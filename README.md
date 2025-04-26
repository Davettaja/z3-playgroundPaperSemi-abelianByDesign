# Z3 Verification Code for Semi-abelian by Desing paper

This repository hosts the Python code (`z3_verification.py`) using the Z3 theorem prover to verify a theorem from the paper:

> Forsman, D. "Semi-abelian by Design: Johnstone Algebras Unifying Implication and Division." (arXiv:XXXX.XXXXX [or link to paper])

Specifically, the script can be used to verify the two main statments in **Theorem 1.14**, which relate the anti-symmetry quasi-identity to an equational form ($(xy)x \approx ((xy)x)y$) and the Cornish condition J ($(xy)x\approx (yx)y$) under the theory of weak relative closure terms.

## Requirements

*   Python 3
*   Z3 SMT solver Python bindings (`pip install z3-solver`)

## Usage

Execute the script directly:
```bash
python z3_verification.py
