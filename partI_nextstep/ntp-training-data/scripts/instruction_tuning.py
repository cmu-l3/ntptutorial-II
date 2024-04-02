import glob
import os
import argparse
import subprocess
import json
import tiktoken
import random
import time
from pathlib import Path
from tqdm import tqdm
from concurrent.futures import ProcessPoolExecutor, as_completed

enc = tiktoken.encoding_for_model("gpt-4")

JSONL_DIRS = {
    'training_data': 'TacticPrediction',
}

def prompt_fn(x, prompt_type, truncation):
    if prompt_type == 'state_tactic':
        return prompt_state_tactic(x)
    elif prompt_type == 'context_state_tactic':
        return prompt_context_state_tactic(x, truncation)


def prompt_state_tactic(x):
    inp = """/- You are proving a theorem in Lean 4.
You are given the following information:
- The current proof state, inside [STATE]...[/STATE]

Your task is to generate the next tactic in the proof.
Put the next tactic inside [TAC]...[/TAC]
-/
[STATE]
%s
[/STATE]
[TAC]
""" % (x['state'])
    out = """%s\n[/TAC]""" % x['nextTactic']
    return inp, out


def prompt_context_state_tactic(x, truncation):
    if truncation > 0:
        context = x['srcUpToTactic']
        if len(enc.encode(context)) > truncation:
            if random.random() > 0.5:
                context = (
                    enc.decode(enc.encode(context)[:truncation//2]) + 
                    '\n\n /- [LONG FILE TRUNCATED] -/\n\n' + 
                    enc.decode(enc.encode(context)[-truncation//2:])
                )
            else:
                context = enc.decode(enc.encode(context)[-truncation:])
    else:
        context = x['srcUpToTactic']
    inp = """/- You are proving a theorem in Lean 4.
You are given the following information:
- The file contents up to the current tactic, inside [CTX]...[/CTX]
- The current proof state, inside [STATE]...[/STATE]

Your task is to generate the next tactic in the proof.
Put the next tactic inside [TAC]...[/TAC]
-/
[CTX]
%s
[/CTX]
[STATE]
%s
[/STATE]
[TAC]
""" % (context, x['state'])
    out = """%s\n[/TAC]""" % x['nextTactic']
    return inp, out


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--name', default='state_tactic')
    parser.add_argument('--output-base-dir', default='instructions/state_tactic')
    parser.add_argument('--pipeline-output-base-dir', default='Examples')
    parser.add_argument('--prompt', default='state_tactic', nargs='*', choices=['state_tactic', 'context_state_tactic'])
    parser.add_argument('--num-dev-examples', type=int, default=0.025)
    parser.add_argument('--num-eval-dev-files', type=float, default=0.00)
    parser.add_argument('--num-eval-test-files', type=float, default=0.00)
    parser.add_argument('--context-truncation', type=int, default=-1)
    parser.add_argument('--mathlib-only', action='store_true')
    args = parser.parse_args()

    if args.mathlib_only:
        args.output_base_dir += '_mathlib_only'

    Path(args.output_base_dir).mkdir(parents=True, exist_ok=True)

    random.seed(12456)

    from collections import defaultdict
    files = defaultdict(lambda: defaultdict(str))
    projects = glob.glob(os.path.join(args.pipeline_output_base_dir, '*'))

    examples = {
        'train': [],
        'dev': [],
        'test': [],
        'file_split_dev': [],
        'file_split_test': []
    }

    all_split_files = {
        'train_dev_test': [],
        'file_split_dev': [],
        'file_split_test': []
    }

    for project in projects:
        if args.mathlib_only and 'Mathlib' not in project:
            continue
        print(project)

        files_ = glob.glob(os.path.join(project, 'TacticPrediction', '*.jsonl'))
        files_ = [f for f in files_ if len(open(f, 'r').readlines()) > 1]

        random.shuffle(files_)
        n_dev = int(len(files_)*args.num_eval_dev_files)
        n_test = int(len(files_)*args.num_eval_test_files)

        # We split at the file level
        split_files = {
            'train': files_[n_dev+n_test:],
            'file_split_dev': files_[:n_dev],
            'file_split_test': files_[n_dev:n_dev+n_test]
        }

        all_split_files['train_dev_test'].extend(split_files['train']) # will be split into train/dev/test
        all_split_files['file_split_dev'].extend(split_files['file_split_dev'])
        all_split_files['file_split_test'].extend(split_files['file_split_test'])

        for split, files_ in split_files.items():
            for i, f in tqdm(enumerate(files_), total=len(files_)):
                jsons = [json.loads(line) for line in open(f, 'r').readlines()]
                for item in jsons:
                    for prompt_name in args.prompt:
                        prompt, completion = prompt_fn(item, prompt_name, args.context_truncation)
                        examples[split].append({
                            'task': 'tactic_predition',
                            'prompt': prompt,
                            'prompt_name': prompt_name,
                            'completion': completion,
                            'metadata': {
                                'task': 'tactic_prediction',
                                'project': project,
                                'file': f,
                                'declId': item['declId'],
                                'target': item['nextTactic'],
                                'split': split
                            }
                        })

    # Now we add "in-distribution" splits using held-out declarations
    train = examples['train']

    decl_ids = list(set([x['metadata']['declId'] for x in train]))
    random.shuffle(decl_ids)

    n_eval_decls = int(2*(args.num_dev_examples)*len(decl_ids))

    train_decls = set(decl_ids[n_eval_decls:])
    dev_decls = set(decl_ids[:n_eval_decls//2])
    test_decls = set(decl_ids[n_eval_decls//2:n_eval_decls])

    examples['train'] = [
        x for x in train if x['metadata']['declId'] in train_decls
    ]
    examples['dev'] = [
        x for x in train if x['metadata']['declId'] in dev_decls
    ]
    for x in examples['dev']:
        x['metadata']['split'] = 'dev'

    examples['test'] = [
        x for x in train if x['metadata']['declId'] in test_decls
    ]
    for x in examples['test']:
        x['metadata']['split'] = 'test'

    stats = {
        'num_train_decls' : len(train_decls),
        'num_dev_decls' : len(dev_decls),
        'num_test_decls' : len(test_decls),
        'num_dev_file_split_decls': len(set([x['metadata']['declId'] for x in examples['file_split_dev']])),
        'num_test_file_split_decls': len(set([x['metadata']['declId'] for x in examples['file_split_test']])),
    }

    for k, v in examples.items():
        stats['num_%s' % k] = len(v)
    
    for k, v in stats.items():
        print(k, v, sep='\t')

    for split, examples_ in examples.items():
        with open(os.path.join(args.output_base_dir, '%s_%s.jsonl' % (args.name, split)), 'w') as f:
            for example in examples_:
                f.write(json.dumps(example))
                f.write('\n')

    with open(os.path.join(args.output_base_dir, 'stats.json'), 'w') as f:
        json.dump(stats, f)

    for split, files in all_split_files.items():
        with open(os.path.join(args.output_base_dir, '%s_files.json' % split), 'w') as f:
            json.dump(files, f)
    
    print(args.output_base_dir)