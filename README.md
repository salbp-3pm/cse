# Compact SAT Encoding for Power Peak Minimization (SALBP-3PM)

This repository contains the artifacts for the paper "Compact SAT Encoding for Power Peak Minimization in Assembly Line Balancing".

**Authors:** Tuyen Van Kieu, Phong Chi Nguyen, Bao Gia Hoang, Khanh Van To

**Affiliation:** Faculty of Information Technology, VNU University of Engineering and Technology, Hanoi, Vietnam

## Short description

The Simple Assembly Line Balancing Problem with Power Peak Minimization (SALBP-3PM) minimizes the maximum instantaneous power (peak) while assigning tasks to workstations and scheduling their start times under precedence and cycle-time constraints. This repository implements a Compact SAT Encoding (CSE) and several optimization variants (Clause-Based iterative SAT, PB-Constraint iterative SAT, Binary MaxSAT, Incremental SAT) described in the paper.

## Repository structure

- `code/` — implementation and scripts used for experiments:
  - `CSE_*.py`, `ORG_*.py`, `ILP_CPLEX.py` — solver implementations and helpers.
  - `data/` — instance files (benchmarks) used in experiments.
  - `results/` — experiment outputs (added to the repository).
- `doc/`, `appendix_*.md`, and other manuscript-related files.

## How to reproduce experiments (quick)

1. Ensure you have a Python 3.8+ environment and required solver binaries (e.g., CaDiCaL, MaxHS, CPLEX) installed and available on `PATH` if used by scripts.
2. From the repository root, run the relevant script under `code/` with appropriate arguments. Examples in `code/README.md` explain usage per script.

Example (pseudo):

```bash
# create virtualenv, install requirements (if needed)
python3 -m venv .venv
source .venv/bin/activate
pip install -r code/requirements.txt  # if exists

# run an experiment script (adapt arguments as needed)
python code/CSE_Eval.py --instances code/data/ --solver cadical --out results/
```

## Results

The `results/` folder contains experiment outputs and CSV tables generated during evaluation. See `code/` for the script that produced them.

## Citation

If you use this work, please cite:

T. V. Kieu, P. C. Nguyen, B. G. Hoang, and K. V. To, "Compact SAT Encoding for Power Peak Minimization in Assembly Line Balancing," (manuscript).

## Notes

- This README was added/updated to reflect the paper metadata and the presence of the `results` folder. If you want a longer README (installation details, exact solver versions, sample outputs, or automated run scripts), tell me what extra details to include and I will update it.
