from flask import Flask, request, jsonify

import argparse
import transformers
from transformers import StoppingCriteria
import torch

parser = argparse.ArgumentParser()
parser.add_argument('--hf-model', type=str, default='l3lab/ntp-mathlib-context-deepseek-coder-1.3b')
parser.add_argument('--port', type=int, default=5001)
parser.add_argument('--temperature', type=float, default=0.5)
args = parser.parse_args()

print("Loading model...")
model = transformers.AutoModelForCausalLM.from_pretrained(args.hf_model)
if torch.cuda.is_available():
    model.cuda()
model.eval()

tokenizer = transformers.AutoTokenizer.from_pretrained(args.hf_model) 
print("Done.")

class MultiTokenEOSCriteria(transformers.StoppingCriteria):
    """Criteria to stop on the specified multi-token sequence."""
    # From: https://github.com/wellecks/lm-evaluation-harness/blob/master/lm_eval/models/huggingface.py#L482

    def __init__(
        self,
        sequence: str,
        tokenizer: transformers.PreTrainedTokenizer,
        initial_decoder_input_length: int,
        batch_size: int,
    ):
        self.initial_decoder_input_length = initial_decoder_input_length
        self.done_tracker = [False] * batch_size
        self.sequence = sequence
        self.sequence_ids = tokenizer.encode(sequence, add_special_tokens=False)
        self.sequence_id_len = len(self.sequence_ids)
        self.tokenizer = tokenizer

    def __call__(self, input_ids, scores, **kwargs) -> bool:
        # For efficiency, we compare the last n tokens where n is the number of tokens in the stop_sequence
        lookback_ids_batch = input_ids[:, self.initial_decoder_input_length :][
            :, -self.sequence_id_len :
        ]

        lookback_tokens_batch = self.tokenizer.batch_decode(lookback_ids_batch)

        for i, done in enumerate(self.done_tracker):
            if not done:
                self.done_tracker[i] = self.sequence in lookback_tokens_batch[i]
        return False not in self.done_tracker

# From: https://github.com/wellecks/lm-evaluation-harness/blob/master/lm_eval/models/huggingface.py#L482
def stop_sequences_criteria(
    tokenizer: transformers.PreTrainedTokenizer,
    stop_sequences,
    initial_decoder_input_length: int,
    batch_size: int,
) -> transformers.StoppingCriteriaList:
    return transformers.StoppingCriteriaList(
        [
            *[
                MultiTokenEOSCriteria(
                    sequence, tokenizer, initial_decoder_input_length, batch_size
                )
                for sequence in stop_sequences
            ],
        ]
    )

def generate(prompt, temperature, num_samples, stop=['[/TAC]']):
    print(prompt)
    input_ids = tokenizer.encode(prompt, return_tensors='pt').to(model.device)
    stopping_criteria = stop_sequences_criteria(
        tokenizer, stop, input_ids.shape[1],
        batch_size=input_ids.shape[0]*num_samples
    )
    out = model.generate(
        input_ids,
        max_new_tokens=200,
        pad_token_id=tokenizer.eos_token_id,
        return_dict_in_generate=True,
        temperature=temperature,
        do_sample=True,
        output_scores=True,
        num_return_sequences=num_samples,
        stopping_criteria=stopping_criteria
    )
    texts = tokenizer.batch_decode(
        out.sequences[:,input_ids.shape[1]:], 
        skip_special_tokens=True
    )
    return texts


app = Flask(__name__)

@app.route('/', methods=['POST'])
def process_request():
    data = request.get_json()
    prompt = data.get('prompt')
    texts = generate(
        prompt, 
        temperature=data.get('temperature', 0.5), 
        num_samples=data.get('n', 5)
    )

    response = {"choices": [{'text': text} for text in texts], "id": ""}
    print(response)
    return jsonify(response)

if __name__ == '__main__':
    app.run(debug=True, host='0.0.0.0', port=args.port)
