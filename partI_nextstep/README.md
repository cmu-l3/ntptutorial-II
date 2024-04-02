## Part I : Next-step suggestion

Builds a neural next-step suggestion tool, introducing concepts and past work in neural theorem proving along the way.

<img src="./notebooks/images/llmsuggest/llmstep_gif.gif" width="350"/>

#### Notebooks:
| Topic | Notebook | 
|:-----------------------|-------:|
| 0. Intro            | [notebook](./notebooks/I_nextstep_lean__part0_intro.ipynb) |
| 1. Data             | [notebook](./notebooks/I_nextstep_lean__part1_data.ipynb) |
| 2. Learning         | [notebook](./notebooks/I_nextstep_lean__part2_learn.ipynb) |
| 3. Proof Search     | [notebook](./notebooks/I_nextstep_lean__part3_proofsearch.ipynb) |
| 4. Evaluation       | [notebook](./notebooks/I_nextstep_lean__part4_evaluation.ipynb) |
| 5. Context | [notebook](./notebooks/I_nextstep_lean__part5_context.ipynb) |
| 6. `LLMLean` tool        | [notebook](./notebooks/I_nextstep_lean__part6_llmsuggest.ipynb) |

All notebooks are in ([`partI_nextstep/notebooks`](./notebooks)). 

#### Artifacts:
| Name | Huggingface | 
|:-----------------------|-------:|
| Data: mathlib extractions | [l3lab/ntp-mathlib](https://huggingface.co/datasets/l3lab/ntp-mathlib) |
| Data: instructions (state-tactic)  | [l3lab/ntp-mathlib-instruct-st](https://huggingface.co/datasets/l3lab/ntp-mathlib-instruct-st) |
| Data: instructions (+context)  | [l3lab/ntp-mathlib-instruct-ctx](https://huggingface.co/datasets/l3lab/ntp-mathlib-instruct-ctx) |
| Model: state-tactic     | [l3lab/ntp-mathlib-st-deepseek-coder-1.3b](https://huggingface.co/l3lab/ntp-mathlib-st-deepseek-coder-1.3b) |
| Model: +context     | [l3lab/ntp-mathlib-context-deepseek-coder-1.3b](https://huggingface.co/l3lab/ntp-mathlib-context-deepseek-coder-1.3b) |


## Setup

#### Setup Lean in VS Code
To try the interactive tool, you will need VS Code and Lean 4. 

Please follow the [official instructions for installing Lean 4 in VS Code](https://leanprover-community.github.io/install/macos_details.html#installing-and-configuring-an-editor): [Installing and configuring an editor](https://leanprover-community.github.io/install/macos_details.html#installing-and-configuring-an-editor).


#### Setup Lean on the command line

Additionally, to run the notebooks you will need Lean 4 installed on your laptop/server.

On Linux or in a Colab notebook, run this command:
```
# from https://leanprover-community.github.io/install/linux.html
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source $HOME/.elan/env
lake
```

For MacOS see:
```
https://leanprover-community.github.io/install/macos.html
```

### Setup language modeling tools
The notebooks use `pytorch` and Huggingface `transformers` and `datasets`.
The notebooks ran successfully with `transformers==4.39.2` and `datasets==2.18.0`.
