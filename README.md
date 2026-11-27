# Can the 180 sieve reach a prime gap of 178?

The [November 2026 paper by Allahyar and Yianni](https://doi.org/10.5281/zenodo.24430219) gives a conditional bound of 180. Its tuple already has the right geometry for testing 178. This audit reproduces the paper's positive margin, computes the extra mixed pair penalty for its frozen profile, and tests what endpoint de-weighting or a joint upper bound would have to save.

**Result:** The two-pair surplus of the frozen restored weight is strictly negative under the paper's priced sieve functional. Its normalized upper bound is `-0.001788933616`. The calculations below leave open whether a reoptimized profile or a sharper joint prime-count estimate can give a positive restored margin.

## Tuple and detection

The paper's tuple is

```text
0, 6, 14, 20, 24, 26, 30, 36, 42, 44, 50, 54, 62, 66, 72, 80, 84, 86,
92, 96, 104, 110, 114, 120, 126, 132, 134, 140, 146, 150, 152, 156, 162,
164, 170, 174, 176, 180, 182
```

Python verified the following missing residues. Primes above 39 have more residue classes than there are shifts.

| Prime | 2 | 3 | 5 | 7 | 11 | 13 | 17 | 19 | 23 | 29 | 31 | 37 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Missing residue | 1 | 1 | 3 | 4 | 1 | 12 | 5 | 2 | 10 | 3 | 12 | 1 |

The only pairs wider than 178 are `(0,180)` and `(0,182)`. Write $N(n)=\sum_{h\in\mathcal H}\mathbf 1_{\mathbb P}(n+h)$ and $B(n)=\mathbf 1_{\mathbb P}(n)\mathbf 1_{\{n+180\text{ or }n+182\text{ is prime}\}}$. A positive weighted mean of $N-1-B$ detects a short pair. Exactly two primes qualify unless they form one of the two long pairs. Any three primes in the tuple qualify because the two long edges do not form a triangle.

## Reproducing 180

Use the paper's normalization. $F$ is the frozen spline, $G$ is its restriction to the allowed support, $D=F-G$, and $M=\lVert F\rVert^2$. The ordinary-mass units put $\rho=2624989/10^7$ on the single-prime income. The two signed label prices $a_s$ and $b_s$ define

$$
I_i(\Phi)=\frac{1}{10^{14}}\sum_s\bigl(a_s E_{i,s}(\Phi)+b_s U_{i,s}(\Phi)\bigr).
$$

Here $E_{i,s}$ is the squared erasure integral under the paper's fragment measure $\nu^{38}$. $U_{i,s}$ uses the same integral with the multiplier $(0.4999-\bar\xi)^{-1}$. The two-site charge for a pair of shifts $a,b$ is

$$
P_{a,b}(\Phi)=\int\frac{2\rho^2\,|\mathcal E_{a,b}\Phi(r)|^2}
{(0.4999-\bar\xi_{37}(r))^2}\,d\nu^{37}(r).
$$

Theorem 5.4 uses $S_{180}(G)=\rho\sum_i I_i(G)-\lVert G\rVert^2-P_{0,182}(G)$. Theorem 6.1 gives the following exact lower margin in units of $M$.

$$
1.0011666-1-0.001121271547-0.0000443013
=\frac{1027153}{10^{12}}.
$$

The upstream quick replay passed all selected checks, including the stored role enclosures, the terminal arithmetic, the middle-restoration aggregation and the distribution-route inventory. It replays the archived evidence. The external per-cap payload and the full Lean build were outside this replay. Reassembling the archived grid enclosures with the tighter restoration and deletion constants in the release gives a lower margin of at least $0.000027800208M$.

### Retained hypotheses

| Hypothesis | Input |
|---|---|
| A1 | Deligne's normalized rank-three hyper-Kloosterman bound $\lvert \mathrm{Kl}_3\rvert\le3$. |
| A2 | The Fouvry-Kowalski-Michel rank-two Kloosterman correlation bound $8p^{3/2}$, including equal nonzero parameters. |
| A3 | Deligne's rank-four bound $4p^{3/2}$ in the paper's unnormalized form. |
| A4 | The proposed finite-exceptional Type III Fourier estimate for four-cycles of rank-three correlations. The generic case allows only a bounded set of exceptional frequencies. The degenerate case allows a bounded-degree algebraic locus and a separate origin term. The paper reports using A4 on 5,520 of its 21,763 Type III parameter choices. |
| Numerical | The paper's 14 stated bounds for the frozen spline, including the grid forms, debits, and restoration terms. |

The 180 implication and any extension using the same distribution routes are conditional on A4. The route replay checks parameter inequalities and coverage. It does not prove the finite-field estimate.

## Two-pair tests

All margins and charges in this section are divided by $M$.

| Test | Certified normalized result |
|---|---:|
| Published 180 terminal margin | $\ge 0.000001027153$ |
| 178, naive union on the frozen restored weight | $[-0.008702060780,\,-0.001788933616]$ |
| 178, asymmetric site-0 fibre projection | Best lower enclosure $-0.008702060780$ at $\lambda=0$. Every support-preserving perturbation within the radius below still gives a negative score. |
| 178, joint upper bound from the available pair data | The available separate caps give the same certificate. The direct rectangular lift provides no saving over separate lifts. |

### Naive union with the frozen weight

The two pairs have different erasures. The spline distinguishes the sites 0 and 182, while 180 belongs to the 37 symmetric interior sites. For the new pair the computation erases site 0 and one interior site, then retains site 182 and the other 36 interior sites. The contraction expands the erased interior variable out of the symmetric power sums and retains the ordered endpoint coefficients.

The uncut reference grid surplus is in `[-0.006190773947, -0.005968610520]`. For the mixed pair, the continuum charge is in `[0.007201341012, 0.007425839724]` before restriction and `[0.006021806929, 0.008729860989]` after restriction. The control erasure for $(0,182)$ encloses all nine archived exact cap values.

The erasure norm bound $K_2=0.3135$ applies after relabelling the pair. To enclose the restored pair cost, use the paper's grid-to-continuum drift and
$\lvert\sqrt{P(F)}-\sqrt{P(G)}\rvert\le\sqrt{K_2}\,\lVert D\rVert$.
The naive certificate subtracts the new upper charge from the 180 lower margin. For the upper side, the same magnitude estimates in the middle-group Young and Cauchy-Schwarz arguments give $-R/M\le0.001565141652$. The positive part of repricing adds at most $0.001392178531M$. This is checked on every archived label run, multiplying the price difference by the maximum insertion length for its retained class. Together with the upper uncut reference income and the lower mixed charge, these prove the negative upper bound in the table.

### De-weighting the shared endpoint

Let $Q_0$ be the orthogonal projection of $G$ onto functions constant along each allowed site-0 fibre, with zero extension outside the fibre. Test $G_\lambda=G-\lambda Q_0$ for $0\le\lambda\le1$. Both pair penalties and the site-0 income scale exactly by $(1-\lambda)^2$. With $q=\lVert Q_0\rVert^2$, the mass falls by $(2\lambda-\lambda^2)q$.

Let $L$ be the current price operator for the other 38 single-prime incomes, $P=P_{0,180}(G)+P_{0,182}(G)$ and $S_0=\rho I_0(G)$. The change in the two-pair surplus is exactly

$$
(2\lambda-\lambda^2)(q-S_0+P)
-2\lambda\langle Q_0,LG\rangle+\lambda^2\langle Q_0,LQ_0\rangle.
$$

The exact operator bounds put every perturbation of $G$ within $0.000163590609\sqrt M$ in $L^2$ strictly below zero, provided it preserves the paper's support envelope. A conservative optimization over the entire interval $0\le\lambda\le1$ maximizes its lower enclosure at $\lambda=0$. At $\lambda=1/4$ the changes in mass, shared income and both penalties leave an allowance of $0.002618234266M$ for the decrease in the other 38 incomes. Their exact change is the remaining numerical target at that $\lambda$.

The two indicated 38-site contractions and the projection mass would determine the optimum in this family. The published receipts give general operator bounds for them, but do not determine their values. The optimized lower enclosure and the local uncut obstruction therefore have different scopes.

### Joint upper bound

The overlap is the event that all of $n,n+180,n+182$ are prime. Under a contradiction assumption of no gaps of size at most 178 at large scales, that overlap is empty, since the last two primes differ by 2. The two separate upper ceilings are compatible with disjoint events, so inclusion-exclusion alone leaves the sum of those ceilings.

A direct common upper-bound sieve is a different possibility. One simple candidate is a rectangular lift with shared-side length $A$ and equal leaf-side lengths $B$, with $A+2B\le L$ for available divisor radius $L$. If the two prescribed leaf marginals are $U,V$ and have common integral $t$, the minimum square mass on the rectangle is
$(\lVert U\rVert^2+\lVert V\rVert^2)/(AB)-t^2/(AB^2)$.
By Cauchy-Schwarz this is at least $(\lVert U\rVert^2+\lVert V\rVert^2)/(2AB)$. The identity
$(L-B)^2-4B(L-2B)=(L-3B)^2$ shows that this lower bound is at least the cost of the two independent triangular lifts for leaf radii at most $B$. Python checked the rational algebra and the finite detection identity. This comparison leaves open a nonrectangular joint lift.

## Threshold for a positive certificate

With the 180 prices, weight and tighter budget fixed, an added certified charge below $0.000027800208M$ suffices. This is less than $0.319\%$ of the present mixed-pair ceiling. A direct joint charge below $0.001042916734M$ also suffices, irrespective of how it is divided between the two events. If only the single-prime incomes are raised, the frozen-weight upper bound requires a gain of at least $0.001788933616M$. A gain exceeding $0.008702060780M$ would close the conservative certificate.

The restoration threshold is in the normalized mass units of the paper. Translating a reduction in it into additional Type II or Type III exponent range requires recomputing the supported regions and their prices. No stronger distribution hypothesis follows from a failed certificate for one profile.

## Reproduce

Obtain the 180 author's `lean/` and `checks/` directories from the [paper release](https://doi.org/10.5281/zenodo.24430219) or the linked [authors' repository](https://github.com/sahibzada-allahyar/math/tree/main/lean). Run the arithmetic replay using Python 3.10+.

```sh
python prime_gap_178_audit.py /path/to/release --receipt mixed_pair_receipt.json
```

To regenerate the mixed-pair receipt, install the release's numerical dependencies, fetch its pinned 182 dependency with `checks/data/fetch_h1_backend.py`, and install a C++ compiler and 64-bit GMP. Keep the upstream `lean/` and `checks/` layout.

```sh
OPENBLAS_NUM_THREADS=1 python prime_gap_178_audit.py /path/to/release --compute /new/scratch/dir
```

The producer uses outward arithmetic from the upstream numerical implementation. The assembler compares the nine recomputed original-pair cap enclosures with the archived exact controls, then uses Python fractions and directed integer square roots for the final budget. Parts of the radial increment evaluator are adapted from the authors' Apache-2.0 numerical release. See [third-party license](THIRD_PARTY_LICENSE.txt).

## Graph theory note

[Reconstructing the second bit of a graph cut](cut-bit-reconstruction/README.md) includes the theorem, a short proof, and a reproducible Lean formalization.
