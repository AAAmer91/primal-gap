from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations
from math import comb, factorial, prod

import numpy as np
from scipy.linalg import eigh


@lru_cache(None)
def radial_integral(r1, a1, r2, a2, p):
    if r1 > r2:
        r1, a1, r2, a2 = r2, a2, r1, a1
    return sum(
        comb(a2, j) * (r2 - r1) ** (a2 - j) * r1 ** (p + a1 + j + 1)
        * Fraction(factorial(p) * factorial(a1 + j), factorial(p + a1 + j + 1))
        for j in range(a2 + 1)
    )


@lru_cache(None)
def sym_product(k, lam1, lam2):
    s1, s2 = len(lam1), len(lam2)
    total = Fraction(0)
    for m in range(min(s1, s2) + 1):
        n = s1 + s2 - m
        if n > k:
            continue
        ways = factorial(k) // factorial(k - n)
        for idx1 in combinations(range(s1), m):
            for idx2 in permutations(range(s2), m):
                exps = [lam1[a] + lam2[b] for a, b in zip(idx1, idx2)]
                exps += [lam1[a] for a in range(s1) if a not in idx1]
                exps += [lam2[b] for b in range(s2) if b not in idx2]
                total += Fraction(ways * prod(map(factorial, exps)), factorial(k - 1 + sum(exps)))
    return total


@lru_cache(None)
def marginal(atom):
    r, a, lam = atom
    terms = [(Fraction(1, a + 1), (r, a + 1, lam))]
    for j, d in enumerate(lam):
        terms.append((Fraction(factorial(a) * factorial(d), factorial(a + d + 1)),
                      (r, a + d + 1, lam[:j] + lam[j + 1:])))
    return tuple(terms)


@lru_cache(None)
def gram(k, x, y):
    r1, a1, lam1 = x
    r2, a2, lam2 = y
    return sym_product(k, lam1, lam2) * radial_integral(
        r1, a1, r2, a2, k - 1 + sum(lam1) + sum(lam2))


def matrices(k, basis):
    n = len(basis)
    A = [[Fraction(0) for _ in basis] for _ in basis]
    B = [[Fraction(0) for _ in basis] for _ in basis]
    for i, x in enumerate(basis):
        for j in range(i, n):
            y = basis[j]
            B[i][j] = B[j][i] = gram(k, x, y)
            A[i][j] = A[j][i] = k * sum(
                c * d * gram(k - 1, u, v)
                for c, u in marginal(x) for d, v in marginal(y))
    return A, B


def optimize(A, B):
    a, b = np.array(A, dtype=float), np.array(B, dtype=float)
    scale = 1 / np.sqrt(np.diag(b))
    values, vectors = eigh(a * scale[:, None] * scale[None, :],
                           b * scale[:, None] * scale[None, :])
    return values[-1], vectors[:, -1] * scale


def parts_ge2(m, min_p=2):
    if m == 0:
        yield ()
        return
    for p in range(min_p, m + 1):
        for rest in parts_ge2(m - p, p):
            yield (p,) + rest


def poly_basis(max_deg, max_parts=2, r=Fraction(1)):
    return [(r, deg - m, lam) for deg in range(max_deg + 1)
            for m in range(deg + 1) for lam in parts_ge2(m)
            if len(lam) <= max_parts]


def spline_basis(knots, max_deg_main, max_deg_knot, max_parts=2):
    return poly_basis(max_deg_main, max_parts) + [
        atom for r in knots for atom in poly_basis(max_deg_knot, max_parts, r)]


def exact_rayleigh_verify(A, B, coeffs):
    def quadratic(M):
        return sum(x * y * M[i][j] for i, x in enumerate(coeffs)
                   for j, y in enumerate(coeffs))
    num, den = quadratic(A), quadratic(B)
    assert den > 0
    return num, den, num / den


def main():
    print('=== DEGREE-7 POLYNOMIAL VS BOUNDARY-LAYER SPLINES ===')
    for k in (5, 10, 20):
        base = poly_basis(7)
        knots = sorted({Fraction(round(100 * (1 - c / k)), 100)
                        for c in (1, 2.5, 5) if 0.05 < 1 - c / k < 0.99})
        splines = spline_basis(knots, 7, 3)
        p, _ = optimize(*matrices(k, base))
        s, _ = optimize(*matrices(k, splines))
        print(f'k={k:2d} | Poly ({len(base)}): {p:.8f} | Spline ({len(splines)}): {s:.8f} | Delta: {s-p:+.8f}')

    print('\n=== EXACT RATIONAL CERTIFICATE (k=5) ===')
    basis = poly_basis(3) + [(Fraction(4, 5), 1, ())]
    A, B = matrices(5, basis)
    _, v = optimize(A, B)
    coeffs = [Fraction(round(float(x / v[0]) * 1000), 1000) for x in v]
    num, den, ratio = exact_rayleigh_verify(A, B, coeffs)
    print('Coefficients:', coeffs)
    print('Exact quotient:', ratio)
    print('Exact surplus numerator (A - 2B):', num - 2 * den)
    print(f'M_5(F) = {float(ratio):.10f} > 2? {ratio > 2}')
    assert ratio > 2, 'Candidate did not certify M_5 > 2'


if __name__ == '__main__':
    main()
