# Bounded Prime Gaps: Maynard-Tao / Polymath8b Variational Experiments

Exploratory radial-spline experiments for the Maynard-Tao variational quantity $M_k$, motivated by the search for improved bounded prime gaps.

## Structure

- `scripts/falsification_loop.py`: Exact rational Gram matrices for radial splines, floating-point generalized eigenvalue optimization, and rational verification of a candidate with $M_5 > 2$.
- `lean/MaynardTaoCert.lean`: Proposed Lean 4 / Mathlib definitions and theorem statements. Proofs are unfinished (`sorry`); the file has not been checked by Lean.

The basis atoms are $\mathbf{1}_{P_1\le r}(r-P_1)^a\widetilde m_\lambda(t)$, where $P_1=\sum_i t_i$ and $\widetilde m_\lambda$ sums over ordered, distinct coordinate indices (including multiplicities for repeated exponents). The indicator matters when $a=0$. The knots and matrix entries are rational; only the eigenvalue search uses floating-point arithmetic.

## Reproduced numerical results

| k | Degree 7 polynomial (dim 42) | Boundary-layer splines | Delta |
|---:|---:|---:|---:|
| 5 | 2.00711497 | 2.00711545 (dim 56) | +0.00000047 |
| 10 | 2.54321196 | 2.54324412 (dim 63) | +0.00003215 |
| 20 | 3.09076263 | 3.09124798 (dim 63) | +0.00048534 |

These are numerical estimates for the specified finite basis, not independently certified optimal eigenvalues or a reproduction of a prime-gap sieve surplus.

## Exact certificate

For k=5 the degree-3 basis plus one radial knot at 4/5 gives the exact quotient

`11523414930897362831 / 5753394211180518900 > 2`.

The denominator quadratic form is positive, and the exact surplus v^T(A-2B)v is

`16626508536325031 / 116943750000000000000 > 0`.

The coefficient vector in script basis order is

`[1, 4209/1000, -19829/1000, -7041/1000, -10169/1000, -19111/500, 1353/500, 83/250]`.

This establishes a lower bound for the variational problem, not a new prime-gap theorem. No k=38 or k=39 sieve threshold or distribution hypothesis has been verified here.

## Usage

```bash
python -m pip install numpy scipy
python scripts/falsification_loop.py
```

The script checks the candidate using exact fractions and asserts the strict inequality. Numerical search results may vary slightly across platforms.
