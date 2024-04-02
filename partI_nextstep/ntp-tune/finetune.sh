export CUDA_VISIBLE_DEVICES=0,1,2,3

TRAIN_FILE=data/state_tactic_mathlib_only_train.jsonl
VALID_FILE=data/state_tactic_mathlib_only_dev.jsonl
MODEL_SIZE="1-3B"
NUM_GPUS=4
BATCH_SIZE_PER_GPU=4
TOTAL_BATCH_SIZE=128
GRADIENT_ACC_STEPS=$(($TOTAL_BATCH_SIZE/$NUM_GPUS/$BATCH_SIZE_PER_GPU))
echo "Training model ${MODEL_SIZE} using $NUM_GPUS GPUs, $BATCH_SIZE_PER_GPU batch size per GPU, $GRADIENT_ACC_STEPS gradient accumulation steps"

accelerate launch \
    --mixed_precision bf16 \
    --num_machines 1 \
    --num_processes $NUM_GPUS \
    --use_deepspeed \
    --deepspeed_config_file ds_configs/stage3_no_offloading_accelerate.conf \
    finetune.py \
    --model_name_or_path deepseek-ai/deepseek-coder-1.3b-base \
    --use_flash_attn \
    --checkpointing_steps 1000 \
    --train_file ${TRAIN_FILE} \
    --valid_file ${VALID_FILE} \
    --max_seq_length 2048 \
    --preprocessing_num_workers 16 \
    --per_device_train_batch_size $BATCH_SIZE_PER_GPU \
    --gradient_accumulation_steps $GRADIENT_ACC_STEPS \
    --learning_rate 1e-6 \
    --lr_scheduler_type linear \
    --warmup_ratio 0.03 \
    --weight_decay 0. \
    --num_train_epochs 2 \
    --output_dir output/state_tactic_mathlib_only/deepseek-coder-1-3b-base/ \
    --with_tracking \
    --report_to tensorboard \
    --logging_steps 1
