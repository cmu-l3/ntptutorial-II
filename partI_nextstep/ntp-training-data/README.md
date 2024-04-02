# ntp-training-data

This repository is a modified version of Scott Morrison's [lean-training-data](https://github.com/semorrison/lean-training-data).


We provide a pipeline for extracting training data based on Lean project source code. 


### Running the new tools
To run the full pipeline on all repositories in `configs/config.json`:
```
python scripts/extract_repos.py --cwd {filepath_of_this_repo}
```

On a Macbook Pro (M3 Max, 14 CPU) extraction from Mathlib takes around 2 hours.

## New tools:
### `training_data`

This produces a `.jsonl` file where each line is an example of the following form:
```json
{
   "state": "{tactic state}",
   "nextTactic" : "{pretty-printed next tactic}",
   "srcUpToTactic" : "{source code in the file up to the tactic invocation}",
   "declUpToTactic" : "{source code in the declaration up to the tactic invocation}",
   "decl": "{declaration without proof (e.g., statement of a theorem)}",
   "declId": "{unique identifier of the declaration}"
}
```
### `instruction_tuning.py`

Generate instruction tuning examples from extracted data.


