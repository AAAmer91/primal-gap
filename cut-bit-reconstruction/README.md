# Reconstructing the second bit of a graph cut

Order the vertices of a finite undirected graph. The second-lowest bit of the
cut size for every contiguous interval determines that bit for every vertex
set. Four neighboring interval measurements recover each coefficient of a
quadratic polynomial that evaluates the bit on arbitrary sets.

## Theorem

Let $G=(V,E)$ be a finite graph on ordered vertices. For $S\subseteq V$, let
$c(S)$ count the edges with exactly one endpoint in $S$. Parallel edges are
counted with multiplicity. A loop crosses no cut. Write

$$
b(S)=\left\lfloor\frac{c(S)}{2}\right\rfloor\bmod 2.
$$

Thus $b(S)=0$ for cut sizes congruent to $0$ or $1$ modulo $4$, and
$b(S)=1$ for residues $2$ and $3$. Label the vertices in order. Write
$I_{a,b}=[a,b]$ for the inclusive interval of vertices, taking it to be
empty when $a>b$. For $a\le b$, define the following sum in
$\mathbb F_2$.

$$
d_{a,b}
=b(I_{a,b})+b(I_{a+1,b})+b(I_{a,b-1})+b(I_{a+1,b-1}).
$$

**Theorem.** For every $S\subseteq V$,

$$
b(S)=\sum_{\substack{a,b\in S\\a\le b}} d_{a,b}
\qquad\text{in }\mathbb F_2.
$$

In particular, two graphs on the same ordered vertex set whose second bits
agree on all interval cuts have the same second bits on all cuts.

## Proof

For any nonnegative integer $c$, writing $c=2r$ or $c=2r+1$ gives
$\binom c2\equiv r\pmod 2$. Put $x_v=\mathbf 1_{v\in S}$. The indicator
that an edge $uv$ crosses the cut is $x_u+x_v$ in $\mathbb F_2$.
Since $b(S)\equiv\binom{c(S)}2\pmod 2$, sum the product of the crossing
indicators over unordered pairs of distinct edge occurrences. This expresses
$b(S)$ as a polynomial of degree at most two in the $x_v$. Using
$x_v^2=x_v$, write it as $\sum_{a\le b}q_{a,b}x_ax_b$, with the diagonal
terms representing the linear terms. The constant term is zero because
$b(\varnothing)=0$.

For $a<b$, take the XOR of the polynomial's values on the interval
$I_{a,b}$, the two intervals obtained by deleting one endpoint at a time,
and the interval obtained by deleting both. A monomial with a vertex outside
$I_{a,b}$ is zero throughout. A monomial missing either endpoint cancels
when that endpoint is deleted. The only surviving monomial is $x_ax_b$,
so $d_{a,b}=q_{a,b}$. When $a=b$, the sum reduces to the singleton
measurement, which gives $q_{a,a}$. Evaluating the resulting polynomial
on $S$ gives the stated formula. $\square$

### Example

Take vertices $0,1,2,3$ and edges $01,02,23$. For the scattered set
$S=\{0,2\}$, the singleton measurements give $d_{0,0}=d_{2,2}=1$.
The four intervals used for $d_{0,2}$ have cut sizes $1,3,1,1$, in the
order in the definition. Their second bits XOR to $1$. The reconstructed
bit is $1+1+1=1$ in $\mathbb F_2$. Directly, the cut crosses edges
$01$ and $23$, so its size is $2$.

### The third bit

Compare a 4-cycle ordered around its perimeter with the edgeless graph on the
same vertices. An interval crosses at most two edges of the cycle, so
$\lfloor c/4\rfloor\bmod2$ is zero for all interval cuts in both graphs.
The set of alternating vertices crosses four edges in the cycle and zero
edges in the edgeless graph. The third bits of that cut differ.

## Lean formalization

[CutBitReconstruction.lean](CutBitReconstruction.lean) represents an edge
list by `List (ℕ × ℕ)` and a vertex set by `Finset ℕ`. Any finite vertex
order can be labeled this way. The code uses half-open intervals `[a,b+1)`,
which avoids natural-number subtraction at the leftmost label. Its double
sum ranges over all ordered endpoint pairs in `S × S`. Terms with `a > b`
are zero because all four half-open intervals are empty.

The Lean proof builds the quadratic function by induction over the edge list.
It uses the carry identity

$$
\operatorname{bit}_1(m+n)=\operatorname{bit}_1(m)+\operatorname{bit}_1(n)
+(m\bmod2)(n\bmod2)
\qquad\text{in }\mathbb F_2.
$$

The product of two vertex indicators is recovered by the interval difference
at its minimum and maximum labels. Linearity then yields the reconstruction
formula for the sum.

| Lean declaration | Statement |
| --- | --- |
| `CutBit.reconstruct_cutBit` | The explicit interval formula recovers the second bit on every finite vertex set. |
| `CutBit.cutBit_eq_of_intervals` | Interval agreement implies agreement on all cuts. |
| `CutBit.thirdCutBit_not_determined` | A 4-cycle and the edgeless graph agree at the third bit on every interval and disagree on `{0, 2}`. |

[CutBitReconstructionChecks.lean](CutBitReconstructionChecks.lean) checks
the worked example and rejects any dependency on `sorryAx` from those three
theorems. The proof file reports their transitive axiom dependencies. Lean
reports `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduce

Install [Elan](https://github.com/leanprover/elan) and run from the repository
root. The toolchain file selects Lean 4.24.0. Lake pins Mathlib and its
transitive dependencies in the checked-in manifest.

```sh
cd cut-bit-reconstruction
lake exe cache get \
  Mathlib.Algebra.BigOperators.Group.Finset.Sigma \
  Mathlib.Data.ZMod.Basic \
  Mathlib.Order.Interval.Finset.Nat \
  Mathlib.Tactic.Ring \
  Mathlib.Util.AssertNoSorry
lake build
```

The cache command fetches precompiled dependencies to speed up the build.
`lake build` compiles both project modules and treats warnings as errors.

## Related work and provenance

The parity-of-pairs argument is a special case of the established relation
between the bits of a Hamming weight and elementary symmetric Boolean
polynomials. See Proposition 2 of Anne Canteaut and Marion Videau, *Symmetric
Boolean Functions*, IEEE Transactions on Information Theory 51(8), 2791-2811
(2005). [DOI](https://doi.org/10.1109/TIT.2005.851743)

This note was developed with AI assistance. A targeted search did not locate
the exact graph-cut reconstruction statement. Publication priority remains
unverified.
