# Neural theorem proving tutorial II

*Neural theorem proving* combines neural language models with formal proof assistants.\
This tutorial introduces two research threads in neural theorem proving via interactive Jupyter notebooks.

This is an updated version of <https://github.com/wellecks/ntptutorial>.

[[slides](https://wellecks.com/data/welleck2024_ntptutorial.pdf)]

## Part I : Next-step suggestion

Builds a neural next-step suggestion tool, introducing concepts and past work in neural theorem proving along the way.

<img src="./partI_nextstep/notebooks/images/llmsuggest/llmstep_gif.gif" width="350"/>

#### Notebooks:
| Topic | Notebook | 
|:-----------------------|-------:|
| 0. Intro            | [notebook](./partI_nextstep/notebooks/I_nextstep_lean__part0_intro.ipynb) |
| 1. Data             | [notebook](./partI_nextstep/notebooks/I_nextstep_lean__part1_data.ipynb) |
| 2. Learning         | [notebook](./partI_nextstep/notebooks/I_nextstep_lean__part2_learn.ipynb) |
| 3. Proof Search     | [notebook](./partI_nextstep/notebooks/I_nextstep_lean__part3_proofsearch.ipynb) |
| 4. Evaluation       | [notebook](./partI_nextstep/notebooks/I_nextstep_lean__part4_evaluation.ipynb) |
| 5. Context | [notebook](./partI_nextstep/notebooks/I_nextstep_lean__part5_context.ipynb) |
| 6. `LLMLean` tool        | [notebook](./partI_nextstep/notebooks/I_nextstep_lean__part6_llmsuggest.ipynb) |

All notebooks are in ([`partI_nextstep/notebooks`](./partI_nextstep/notebooks)). 

#### Artifacts:
| Name | Huggingface | 
|:-----------------------|-------:|
| Data: mathlib extractions | [l3lab/ntp-mathlib](https://huggingface.co/datasets/l3lab/ntp-mathlib) |
| Data: instructions (state-tactic)  | [l3lab/ntp-mathlib-instruct-st](https://huggingface.co/datasets/l3lab/ntp-mathlib-instruct-st) |
| Data: instructions (+context)  | [l3lab/ntp-mathlib-instruct-ctx](https://huggingface.co/datasets/l3lab/ntp-mathlib-instruct-ctx) |
| Model: state-tactic     | [l3lab/ntp-mathlib-st-deepseek-coder-1.3b](https://huggingface.co/l3lab/ntp-mathlib-st-deepseek-coder-1.3b) |
| Model: +context     | [l3lab/ntp-mathlib-context-deepseek-coder-1.3b](https://huggingface.co/l3lab/ntp-mathlib-context-deepseek-coder-1.3b) |


#### Setup:
Please follow the setup instructions in [`partI_nextstep/README.md`](./partI_nextstep/README.md).

## Part II : Language cascades
Chain together language models to guide formal proof search with informal proofs.


#### Notebooks:
| Topic | Notebook | 
|:-----------------------|-------:|
| 1. Language model cascades | [notebook](./partII_dsp/notebooks/II_dsp__part1_intro.ipynb) |
| 2. Draft, Sketch, Prove | [notebook](./partII_dsp/notebooks/II_dsp__part2_dsp.ipynb) |

All notebooks are in ([`partII_dsp/notebooks`](./partII_dsp/notebooks)).

#### Setup:
Please follow the setup instructions in [`partII_dsp/README.md`](./partII_dsp/README.md).


-------
### History

This is an updated version of *A tutorial on neural theorem proving* ([https://github.com/wellecks/ntptutorial](https://github.com/wellecks/ntptutorial)). \
Please see the repository for more details.

#### Citation

Until there is an associated preprint, please cite this repository:
```
@misc{ntptutorial,
  author = {Sean Welleck},
  title = {Neural theorem proving tutorial II},
  year = {2023},
  publisher = {GitHub},
  journal = {GitHub repository},
  howpublished = {\url{https://github.com/cmu-l3/ntptutorial-II}},
}
```
