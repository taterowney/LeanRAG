#!/bin/bash

#SBATCH --job-name=LeanRAG
#SBATCH --partition=general
#SBATCH --output=logs/LeanRAG.out
#SBATCH --error=logs/LeanRAG.err
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=4
#SBATCH --gres=gpu:A6000:1
#SBATCH --mem=100G
#SBATCH --time=12:00:00

source $HOME/miniconda3/bin/activate LeanRAG
# python3 check_new.py --model-name "o4-mini" --dataset-name "mathlib" --num-samples 32
python RAG_mathlib.py