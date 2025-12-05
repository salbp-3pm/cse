# SALBP-3PM: Simple Assembly Line Balancing Problem with Power Peak Minimization

This repository contains the implementation of Compact SAT encodings for solving the **Simple Assembly Line Balancing Problem with Power Peak Minimization (SALBP-3PM)**.

## Problem Description

The SALBP-3PM aims to assign tasks to workstations in an assembly line while:
- Respecting precedence constraints between tasks
- Balancing cycle time constraints
- **Minimizing the peak power consumption** across all workstations

## Repository Structure

```
.
├── CSE_CB.py          # CSE encoding with Cardinality-Based approach
├── CSE_Eval.py        # CSE encoding with Evaluation approach
├── CSE_INC.py         # CSE encoding with Incremental approach
├── CSE_MaxHS.py       # CSE encoding with MaxHS solver
├── CSE_PB.py          # CSE encoding with Pseudo-Boolean constraints
├── ORG_CB.py          # Original encoding with Cardinality-Based approach
├── ORG_Eval.py        # Original encoding with Evaluation approach
├── ORG_MaxHS.py       # Original encoding with MaxHS solver
├── ILP_CPLEX.py       # Integer Linear Programming using CPLEX
├── data/              # Instance data files (task times, precedence)
├── presedent_graph/   # Precedence graph data
└── task_power/        # Power consumption data for each task
```

## Encodings

### CSE (Cardinality-based Staircase Encoding)
- **CSE_CB.py**: Uses cardinality constraints with sequential counter encoding
- **CSE_Eval.py**: Evaluation-based approach for incremental optimization
- **CSE_INC.py**: Incremental SAT solving approach
- **CSE_MaxHS.py**: Integration with MaxHS MaxSAT solver
- **CSE_PB.py**: Pseudo-Boolean constraint encoding

### ORG (Original Encoding)
- **ORG_CB.py**: Original cardinality-based encoding
- **ORG_Eval.py**: Original evaluation approach
- **ORG_MaxHS.py**: Original encoding with MaxHS solver

### ILP Approach
- **ILP_CPLEX.py**: Integer Linear Programming formulation using IBM CPLEX

## Benchmark Instances

The repository includes standard SALBP benchmark instances:

| Instance | Tasks | Description |
|----------|-------|-------------|
| MERTENS | 7 | Small instance |
| BOWMAN | 8 | Small instance |
| JAESCHKE | 9 | Small instance |
| JACKSON | 11 | Small instance |
| MANSOOR | 11 | Small instance |
| MITCHELL | 21 | Medium instance |
| ROSZIEG | 25 | Medium instance |
| HESKIA | 28 | Medium instance |
| BUXEY | 29 | Medium instance |
| SAWYER | 30 | Medium instance |
| GUNTHER | 35 | Large instance |
| WARNECKE | 58 | Large instance |

## Requirements

- Python 3.8+
- Required packages:
  ```
  pysat
  pandas
  numpy
  tabulate
  ```

For ILP approach:
- IBM CPLEX (with Python API)

## Installation

```bash
# Clone the repository
git clone https://github.com/salbp-3pm/cse.git
cd cse

# Install dependencies
pip install python-sat pandas numpy tabulate
```

## Usage

### Running CSE Encoding

```python
# Edit the instance file in the script
python CSE_Eval.py
```

### Running Original Encoding

```python
python ORG_Eval.py
```

### Running ILP with CPLEX

```python
python ILP_CPLEX.py
```

## Data Format

### Instance Files (*.IN2)
```
<number_of_tasks>
<task_1_time>
<task_2_time>
...
<task_n_time>
<predecessor>,<successor>
...
-1,-1
```

### Power Files (task_power/*.txt)
```
<power_task_1>
<power_task_2>
...
<power_task_n>
```

## Citation

If you use this code in your research, please cite:

```bibtex
@article{salbp3pm2024,
  title={Optimizing Power Peaks in Simple Assembly Line Balancing through Maximum Satisfiability},
  author={[Authors]},
  journal={[Journal]},
  year={2024}
}
```

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Contact

For questions or issues, please open an issue on GitHub or contact the authors.
