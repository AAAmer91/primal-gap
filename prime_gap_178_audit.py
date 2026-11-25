"""Replay exact published bounds and evaluate the two long-pair budget.

Baseline: python prime_gap_178_audit.py /path/to/extracted/release
Receipt:  python prime_gap_178_audit.py /path/to/release --receipt mixed_pair_receipt.json
Rebuild:  python prime_gap_178_audit.py /path/to/release --compute /new/scratch/dir

Use the Allahyar-Yianni November 180 release, including its checks and Lean
sources. Rebuild uses the release's numerical dependencies, its pinned 182
backend (fetch_h1_backend.py), and a C++ compiler with 64-bit GMP. The mixed
erasure extends the public Apache-2.0 numerical code in the 180 release.
Outward arithmetic in the producer follows that release's error budgets.

The exact assembler does not treat a negative lower bound as an upper bound.
"""

from argparse import ArgumentParser
from fractions import Fraction as Q
from hashlib import sha256
from itertools import combinations, product
from math import isqrt, lcm
from pathlib import Path
import json

SHIFTS = (
    0, 6, 14, 20, 24, 26, 30, 36, 42, 44, 50, 54, 62, 66, 72, 80, 84, 86,
    92, 96, 104, 110, 114, 120, 126, 132, 134, 140, 146, 150, 152, 156, 162,
    164, 170, 174, 176, 180, 182,
)
PUBLISHED_MARGIN = Q("0.000001027153")
ANCHOR_RESTORE = Q("0.001121271547")
EXACT_RESTORE_CEILING = Q("0.001120271547")
DELETED_MASS_CEILING = Q("0.000168145444")
K1 = Q(1429497779624109, 131072000000000)
K2 = Q("0.3135")
EPS_BIN = Q("0.000000006159")
EPS_VEC = Q("0.00000185")
RHO = Q("0.2624989")
STEP = Q(1399373467, 172031279104000)
T = RHO * STEP * (130964 + 39)
SINGLE_RAW_CEILING = Q("1.0518")
PAIR_DRIFT = 4 * K2 * EPS_BIN + 2 * K2 * EPS_VEC
SINGLE_DRIFT = 2 * K1 * (EPS_BIN + EPS_VEC)
FORMS_PATH = "checks/data/parallel_quotient_debit.json"
PAIR_PATH = "checks/proof/exact_native_pair.json"
ARCHIVES = {
    FORMS_PATH: "b5dcf5c88a68435798f80103f20425ab268ea240e91d15af307b911a8c5b86d3",
    PAIR_PATH: "9b7b84fb74294d1149acf638c51536f518d50df34d1307f4144f4863e6a3c4c7",
}


def sqrt_bounds(q):
    scale = 10**24
    lower = isqrt(q.numerator * scale**2 // q.denominator)
    return Q(lower, scale), Q(lower + (lower**2 * q.denominator != q.numerator * scale**2), scale)


def ratio(bounds, denominator):
    values = [q / m for q, m in product(bounds, denominator)]
    return min(values), max(values)


def read(path, digest=None):
    raw = path.read_bytes()
    if digest is not None and sha256(raw).hexdigest() != digest:
        raise ValueError(f"Source hash mismatch: {path.name}")
    return json.loads(raw)


def tuple_and_detection():
    assert len(SHIFTS) == len(set(SHIFTS)) == 39
    assert SHIFTS == tuple(sorted(SHIFTS))
    assert (SHIFTS[0], *SHIFTS[-2:]) == (0, 180, 182)
    long_pairs = [(a, b) for a, b in combinations(SHIFTS, 2) if b-a > 178]
    assert long_pairs == [(0, 180), (0, 182)]
    omit = {}
    for p in range(2, 40):
        if all(p % q for q in range(2, isqrt(p) + 1)):
            residues = {shift % p for shift in SHIFTS}
            omit[p] = min(set(range(p)) - residues)
    for a, b, c, interior in product(range(2), range(2), range(2), range(37)):
        n = a + b + c + interior
        union = a * max(b, c)
        assert (n - 1 - union > 0) == (n >= 2 and not (n == 2 and union))
        if a * b * c:
            assert b * c == 1 and 182 - 180 <= 178
    return omit


def baseline(root):
    source = read(root / FORMS_PATH, ARCHIVES[FORMS_PATH])
    exact_pair = read(root / PAIR_PATH, ARCHIVES[PAIR_PATH])
    forms = {
        name: tuple(sum(Q(row["forms"][name][i]) for row in source["receipts"])
                    for i in range(2))
        for name in source["raw_forms"]
    }
    assert forms == {k: tuple(map(Q, v)) for k, v in source["raw_forms"].items()}
    m = forms["full"]
    p = (Q(exact_pair["lower"]), Q(exact_pair["upper"]))
    assert m[0] > Q("94.17312") and p[0] <= p[1]
    core, first, last = (forms[k] for k in ("core", "a", "b"))
    num = (
        37 * core[0] + first[0] + last[0] - p[1],
        37 * core[1] + first[1] + last[1] - p[0],
    )
    n = ratio(num, m)
    all_drift = SINGLE_DRIFT + PAIR_DRIFT
    debit_q = Q(27, 20) * Q("0.000024") + Q(27, 7) * Q("0.01815") * Q("0.00017")
    debit_printed = Q("0.0000443013")
    assert debit_q <= debit_printed
    assert Q("1.0011666") - 1 - ANCHOR_RESTORE - debit_printed == PUBLISHED_MARGIN
    # Use the archived grid enclosures and tighter restoration and mass ceilings.
    debit_tight = (Q(27, 20) * Q("0.000024")
                   + Q(27, 7) * Q("0.01815") * DELETED_MASS_CEILING)
    tight = n[0] - all_drift - 1 - EXACT_RESTORE_CEILING - debit_tight
    assert tight > PUBLISHED_MARGIN
    return m, p, first, n, debit_tight, tight


def physical_pair(grid, mass):
    lo, hi = ratio(grid, mass)
    uncut = max(Q(0), lo - PAIR_DRIFT), hi + PAIR_DRIFT
    loss = sqrt_bounds(K2 * DELETED_MASS_CEILING)[1]
    cut = (max(Q(0), sqrt_bounds(uncut[0])[0] - loss)**2,
           (sqrt_bounds(uncut[1])[1] + loss)**2)
    return uncut, cut


def signed_restoration_bound(root):
    """Repurpose the magnitude-based middle certificates for the reverse bound on R."""
    import re

    path = root / "lean/proof/TrialSlackRows180.lean"
    table = path.read_text().split("def rows :", 1)[1].split("/-- Absolute", 1)[0]
    rows = [tuple(map(int, match)) for match in re.findall(
        r"⟨(\d+), (\d+), (\d+), (\d+), (\d+)⟩", table)]
    assert len(rows) == 22
    assert sum(r[0] for r in rows) == 160362542
    assert sum(r[4] for r in rows) == 1047071290

    unit = 10**12
    abs_cross = sum(2 * sqrt_bounds(Q(m * image, unit**2))[1] for m, image in
                    ((3647432, 1375543), (4135470, 206889941)))
    for mass, pair_image, joint, _young, _cost in rows:
        # Joint bounds come from Young's inequality with positive weights
        # applied to the middle single-site cross terms. They therefore
        # apply to either sign of the deleted probe, whose squares agree.
        abs_cross += Q(joint, unit) + Q("0.6865") * Q(mass, unit)
        abs_cross += 2 * sqrt_bounds(Q(mass * pair_image, unit**2))[1]
    return abs_cross + (1 + SINGLE_RAW_CEILING) * DELETED_MASS_CEILING


def repricing_bound(root, direction=1):
    """Bound a one-sided price change using the retained-index insertion length."""
    assert direction in (-1, 1)
    table = read(root / "lean/proof/frozen_band_tables.json",
                 "785527884ca340d8ca12909f3076b422fddf4922e234cdd3a574f74bc70de6ef")
    ref, current = (read(root / "lean/data" / name) for name in
                    ("h1_multilevel_strip_free.json", "repriced_covers.json"))
    assert ref["scale"] == current["scale"] == 10**14
    assert ref["sector_prices"][170] == current["sector_prices"][170]
    assert len(ref["sector_prices"]) == len(current["sector_prices"]) == 521
    for a, b, c in current["sector_prices"]:
        assert b <= 0 and c == 0 and a + b / Q("0.4999") <= current["scale"]
    assert table["maxIndex"] == sorted(table["maxIndex"], reverse=True)
    assert len(table["maxIndex"]) == len(table["sectorRuns"]) == 44
    tau = RHO * STEP
    assert tau * (max(table["maxIndex"]) + 38) < Q("0.2801")
    upper = Q(0)
    for last, ranges in zip(table["maxIndex"], table["sectorRuns"]):
        start = 0
        for stop, label in ranges:
            lo, hi = max(0, start - 1), min(last, stop - 2)
            if label and lo <= hi:
                a, b, _ = (direction * (new - old) for new, old in zip(
                    current["sector_prices"][label - 1], ref["sector_prices"][label - 1]))
                # Price difference is affine in the reciprocal price, hence
                # maximized at an endpoint. Each insertion has at most
                # last-lo+1 native cells once the retained class is fixed.
                value = max(Q(0), *(Q(a) + b / (Q("0.4999") - tau * (j + 38))
                                     for j in (lo, hi)))
                upper = max(upper, 39 * value / current["scale"] * tau * (last - lo + 1))
            start = stop
    return upper


def decimal(q, digits=12, upper=False):
    scale = 10**digits
    x = q * scale
    i = -((-x.numerator) // x.denominator) if upper else x.numerator // x.denominator
    sign = "-" if i < 0 else ""
    return f"{sign}{abs(i)//scale}.{abs(i)%scale:0{digits}d}"


def summary(root, receipt=None):
    omitted = tuple_and_detection()
    print("tuple:", SHIFTS)
    print("omitted residues:", omitted)
    print("published 180 lower margin / M:", PUBLISHED_MARGIN, decimal(PUBLISHED_MARGIN))
    mass, original, first, old_reference, debit, tight = baseline(root)
    print("tighter 180 lower margin / M:", decimal(tight))
    print("raw reference 180 surplus / M:", [decimal(old_reference[0] - 1),
                                              decimal(old_reference[1] - 1, upper=True)])
    if receipt is None:
        return
    data = read(receipt)
    if not data["complete"]:
        raise ValueError("Mixed-pair output must cover all nine changing caps")
    for key in ("original", "mixed"):
        assert tuple(map(Q, data[key])) == tuple(
            sum(Q(row[key][i]) for row in data["caps"]) for i in range(2))
    control = tuple(map(Q, data["original"]))
    assert control[0] <= original[0] <= original[1] <= control[1]
    exact_rows = {v["cap"]: v for v in read(root / PAIR_PATH, ARCHIVES[PAIR_PATH])["caps"]}
    assert len(exact_rows) == len(data["caps"]) == 9
    assert set(exact_rows) == {v["cap"] for v in data["caps"]}
    for row in data["caps"]:
        cap = exact_rows[row["cap"]]
        left, right = map(Q, row["original"])
        assert left <= Q(cap["lower"]) <= Q(cap["upper"]) <= right

    mixed_grid = tuple(map(Q, data["mixed"]))
    assert 0 < mixed_grid[0] <= mixed_grid[1]
    grid_pair_ratio = ratio(mixed_grid, mass)
    grid_surplus = (old_reference[0] - 1 - grid_pair_ratio[1],
                    old_reference[1] - 1 - grid_pair_ratio[0])
    print("raw 178 reference grid surplus / M:",
          [decimal(grid_surplus[0]), decimal(grid_surplus[1], upper=True)])
    full_drift = SINGLE_DRIFT + 2 * PAIR_DRIFT
    print("uncut continuum reference 178 surplus / M:",
          [decimal(grid_surplus[0] - full_drift),
           decimal(grid_surplus[1] + full_drift, upper=True)])
    mix_f, mix_g = physical_pair(mixed_grid, mass)
    _, orig_g = physical_pair(original, mass)
    print("mixed P(F)/M:", [decimal(mix_f[0]), decimal(mix_f[1], upper=True)])
    print("mixed P(G)/M:", [decimal(mix_g[0]), decimal(mix_g[1], upper=True)])
    print("original P(G)/M:", [decimal(orig_g[0]), decimal(orig_g[1], upper=True)])
    naive_budget = PUBLISHED_MARGIN - mix_g[1]
    naive_tight = tight - mix_g[1]
    print("178 naive replay lower bound / M:", decimal(naive_budget))
    print("178 tighter replay lower bound / M:", decimal(naive_tight))
    loss_reverse = signed_restoration_bound(root)
    reprice_up = repricing_bound(root)
    reprice_down = repricing_bound(root, -1)
    restored_upper = (old_reference[1] + SINGLE_DRIFT + PAIR_DRIFT - 1
                      + loss_reverse + reprice_up - mix_g[0])
    print("reverse restoration loss bound / M:", decimal(loss_reverse, upper=True))
    print("positive repricing bound / M:", decimal(reprice_up, upper=True))
    print("178 restored naive upper bound / M:", decimal(restored_upper, upper=True))
    if restored_upper < 0:
        actual_norm = 2 + reprice_down + 1 + 2 * K2
        restored_radius = -restored_upper / (3 * actual_norm)
        assert 0 < restored_radius < 1
        assert restored_upper + actual_norm * (2 * restored_radius + restored_radius**2) < 0
        print("restored obstruction, relative L2 radius:", decimal(restored_radius))
    print("hypothetical perfect-overlap replay lower bound / M:",
          decimal(tight - max(Q(0), mix_g[1] - orig_g[0])))
    assert sum(v[1] for v in (mix_g, orig_g)) <= 1 - DELETED_MASS_CEILING

    # The perturbation removes a multiple of the conditional average of G
    # over each allowed shared-endpoint fibre. Both long-pair charges and the
    # shared single-site term scale exactly by (1-lambda)^2.
    ref_first = ratio(first, mass)[0] - SINGLE_DRIFT
    distance = sqrt_bounds(DELETED_MASS_CEILING)[1]
    shared_lower = ref_first - Q("0.28") * (2 * distance + DELETED_MASS_CEILING) - debit
    assert shared_lower > 0 and T < 1
    guaranteed_gain = (1 / T - 1) * shared_lower + mix_g[0] + orig_g[0]
    other_norm = 2 + reprice_down
    assert guaranteed_gain < other_norm
    for lam in (Q(0), Q("0.01"), Q("0.05"), Q("0.1"), Q("0.25"), Q("0.5"), Q(1)):
        removed = 2 * lam - lam**2
        allowance = naive_tight + removed * guaranteed_gain
        bound = allowance - (2 * lam + lam**2) * other_norm
        print("endpoint lambda", lam, "certified lower score / M", decimal(bound),
              "other-income debit threshold / M", decimal(allowance))
    print("best of the certified lower bounds: lambda=0")

    # The uncut-grid reference operator is bounded between -2 and 1.0518
    # before subtracting the two positive pair forms and the mass.
    max_norm = 2 + 1 + 2 * K2
    if grid_surplus[1] < 0:
        radius = -grid_surplus[1] / (3 * max_norm)
        assert 0 < radius < 1
        assert grid_surplus[1] + max_norm * (2 * radius + radius**2) < 0
        print("uncut-grid obstruction, relative L2 radius:", decimal(radius))

    for b in (Q(1, 16), Q(1, 8), Q(1, 4), Q(1, 3), Q(7, 16)):
        a = 1 - 2 * b
        assert (1 - b)**2 - 4 * b * a == (1 - 3 * b)**2 >= 0
        assert 1 / (2 * a * b) >= 2 / (1 - b)**2
    print("no certified joint discount from separate pair ceilings and zero overlap lower bound")
    # Exact model check: the common lift equal to 1 on a unit simplex
    # has both fibre marginals (1-y)^2/2. Its cost is the cost of either
    # individual minimum lift, and half the sum of the two costs.
    unit_volume = Q(1, 6)
    one_pair = sum(Q((-1)**j * c, 2 * (j + 1)) for j, c in enumerate((1, 2, 1)))
    assert one_pair == unit_volume
    print("unit triangular control: direct lift, sum of pair costs =", unit_volume, 2 * one_pair)
    print("joint upper charge / M sufficient below", decimal(orig_g[0] + tight))
    print("additional pair multiplier must be below", decimal(tight / mix_g[1]))
    single_income_floor = 1 - DELETED_MASS_CEILING + orig_g[0] + tight
    print("uniform extra-income fraction sufficient above",
          decimal((mix_g[1] - tight) / single_income_floor, upper=True))
    print("common pair multiplier, sufficient threshold:",
          decimal((tight + orig_g[0]) / (orig_g[0] + mix_g[1])))
    max_restoration = old_reference[0] - SINGLE_DRIFT - PAIR_DRIFT - 1 - debit - mix_g[1]
    print("restoration ceiling required with other inputs fixed (in common units):",
          decimal(max_restoration))


def ordered_difference(self, cap_class, a, b, signature, Interval, COUNT, FIELD_BITS, SIGNATURES):
    """Enclose one ordered endpoint-shape coefficient across radial cells."""
    low, high = [0] * COUNT, [0] * COUNT
    exponents = SIGNATURES[signature]
    scale = Q((1 << FIELD_BITS) * 39**(sum(exponents) - len(exponents)), self.table["coeffDen"])
    shape = 3 * a + b
    for span, start, end, current, old, weights in self.spans(cap_class):
        coefficients = [self.coefficient(current, shape, signature, j) -
                        self.coefficient(old, shape, signature, j)
                        for j in range(span - 3, span + 1)]
        if not any(coefficients):
            continue
        f = [scale * sum(z * w for z, w in zip(coefficients, row, strict=True)) for row in weights]
        delta = [f[0], f[1] - f[0], f[2] - 2 * f[1] + f[0], f[3] - 3 * f[2] + 3 * f[1] - f[0]]
        common = lcm(*(z.denominator for z in delta))
        y, first, second, third = [int(z * common) for z in delta]
        for j in range(start, end):
            quotient, remainder = divmod(y, common)
            low[j], high[j] = quotient, quotient + bool(remainder)
            y += first
            first += second
            second += third
    return Interval(low, high)


def setup(args):
    import sys
    import numpy as np

    sys.path[:0] = [str(args.source.resolve() / path) for path in ("checks/data", "lean/proof")]
    import quotient_poly as poly
    from quotient_contract import Integral, Laws, configure, contract, empty, scaled_ball
    from quotient_inputs import STEP, SIGS, cap_cdf, exact_float_bounds, site_fields
    from check_exact_endpoint_pair import COUNT, FIELD_BITS, SIGNATURES, Spline
    from endpoint_pair_arithmetic import Interval
    from fast_fragment_ritz import fiber_splits

    configure(args.library, args.bits)
    spline = Spline(args.source / "lean/proof/frozen_band_tables.json")
    spline.two_roles = lambda cap, a, b, k: ordered_difference(
        spline, cap, a, b, k, Interval, COUNT, FIELD_BITS, SIGNATURES)
    cap_keys = [row["cap"] for row in json.loads(
        (args.source / "lean/data/cap_law_transfer.json").read_text())["bins"]]
    active = [index for index in reversed(range(37)) if spline.changes(index)]
    rho = Q("0.2624989")
    rate, ledger = map(exact_float_bounds, (rho * STEP, Q("0.4999")))
    index = np.arange(COUNT) + 37
    lo = poly.down(ledger[0] - poly.up(index * rate[1]))
    hi = poly.up(ledger[1] - poly.down(index * rate[0]))
    assert np.all(lo > 0)
    inv = (poly.down(1 / hi), poly.up(1 / lo))
    price = poly.split_bounds(poly.positive_product(
        poly.positive_product(inv, inv), exact_float_bounds(2 * (rho / 100)**2)))
    width = exact_float_bounds(100 * STEP)
    profiles = site_fields(stop=COUNT)
    index_of = {signature: index for index, signature in enumerate(SIGS)}
    split = [list(fiber_splits(sig)) for sig in SIGS]
    # Check that repeated factors receive their binomial multiplicity.
    assert sorted(split[index_of[(2, 2)]]) == [((), 4, 1), ((2,), 2, 2), ((2, 2), 0, 1)]
    return poly, Integral, Laws, contract, empty, scaled_ball, COUNT, STEP, SIGS, cap_cdf, spline, cap_keys, active, price, width, profiles, index_of, split


def run_fields(args, cap_index):
    import numpy as np
    import time

    (poly, Integral, Laws, contract, empty, scaled_ball, COUNT, STEP, SIGS, cap_cdf,
     spline, cap_keys, active, price, width, profiles, index_of, split) = setup(args)
    start = time.monotonic()
    cap = cap_keys[cap_index]
    law = Laws(profiles, tuple(x[:COUNT] for x in cap_cdf(cap)), width, 36, SIGS)
    inc = empty((len(SIGS) * 3, COUNT))
    base_inc = empty((len(SIGS), COUNT))
    for k in range(len(SIGS)):
        # Use ordered endpoint coefficients for the mixed erasure.
        # Here we erase slot 0 and one of the 37 interior slots, and
        # retain slot 38, whose shape is indexed by b.
        for b in range(3):
            left = empty((COUNT,))
            for a in range(3):
                bounds = spline.two_roles(cap_index, a, b, k)
                low = np.ldexp(np.asarray(bounds.low, dtype=float), -64)
                high = np.ldexp(np.asarray(bounds.high, dtype=float), -64)
                row = poly.split_bounds((poly.down(low), poly.up(high)))
                zero = np.array([x == y == 0 for x, y in zip(bounds.low, bounds.high)])
                row[0][zero] = 0
                row[1][zero] = 0
                left = poly.ball_add(left, poly.correlated(row, law.ins(("shape", a))))
            base = poly.correlated(left, law.ins(("shape", b)))
            base_inc[0][k], base_inc[1][k] = poly.ball_add(
                (base_inc[0][k], base_inc[1][k]), base)
            for retained, power, multiple in split[k]:
                dest = index_of[retained] * 3 + b
                value = poly.correlated(left, law.ins(("power", power)))
                previous = (inc[0][dest], inc[1][dest])
                inc[0][dest], inc[1][dest] = poly.ball_add(
                    previous, scaled_ball(value, multiple))
    path = args.workdir / f"field-{cap_index}.npz"
    temporary = path.with_suffix(".tmp.npz")
    np.savez(temporary, mixed=inc, original=base_inc)
    temporary.replace(path)
    print(f"finished fields for cap {cap} in {time.monotonic()-start:.1f}s", flush=True)


def run_gram(args, cap_index):
    import numpy as np
    import time

    (poly, Integral, Laws, contract, empty, scaled_ball, COUNT, STEP, SIGS, cap_cdf,
     spline, cap_keys, active, price, width, profiles, index_of, split) = setup(args)
    start = time.monotonic()
    cap = cap_keys[cap_index]
    law = Laws(profiles, tuple(x[:COUNT] for x in cap_cdf(cap)), width, 36, SIGS)
    old = empty((len(SIGS) * 3, COUNT))
    base_old = empty((len(SIGS), COUNT))
    for i in active:
        with np.load(args.workdir / f"field-{i}.npz", allow_pickle=False) as z:
            inc, base_inc = tuple(z["mixed"]), tuple(z["original"])
        if i == cap_index:
            break
        old = poly.ball_add(old, inc)
        base_old = poly.ball_add(base_old, base_inc)
    _, last = spline.state(cap_index)
    indices = np.arange(last + 1, dtype=np.int32)
    step, base_step = Integral(), Integral()
    contract(law, 36, 1, [(step, inc, poly.ball_add(inc, old, 2), price, indices)])
    del inc, old
    contract(law, 37, 0, [(base_step, base_inc,
                          poly.ball_add(base_inc, base_old, 2), price, indices)])
    record = dict(cap=cap, mixed=list(map(str, (step.low, step.high))),
                  original=list(map(str, (base_step.low, base_step.high))))
    path = args.workdir / f"gram-{cap_index}.json"
    temporary = path.with_suffix(".tmp.json")
    temporary.write_text(json.dumps(record) + "\n")
    temporary.replace(path)
    print(f"finished Gram for cap {cap} in {time.monotonic()-start:.1f}s | mixed "
          f"{float(step.low):.12g} | original {float(base_step.low):.12g}", flush=True)



def main():
    from concurrent.futures import ProcessPoolExecutor
    from itertools import repeat
    from subprocess import run

    parser = ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="extracted release containing lean/ and checks/")
    parser.add_argument("--receipt", type=Path, help="directed mixed-pair JSON receipt")
    parser.add_argument("--compute", type=Path, metavar="NEW_DIR",
                        help="recompute receipt in a new directory, then summarize")
    parser.add_argument("--bits", type=int, default=128)
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--resume", action="store_true",
                        help="reuse completed cap files from the same computation")
    args = parser.parse_args()

    if args.resume and not args.compute:
        parser.error("--resume requires --compute")
    if args.compute:
        if args.receipt:
            parser.error("choose --compute or --receipt")
        # Complete the baseline replay before computing the extension.
        omitted = tuple_and_detection()
        assert len(omitted) == 12
        baseline(args.source)
        args.workdir = args.compute.resolve()
        sources = ("lean/proof/frozen_band_tables.json", "lean/data/cap_law_transfer.json",
                   "checks/data/packed_poly.cpp", "checks/data/quotient_poly.py",
                   "checks/data/quotient_contract.py", "checks/data/quotient_inputs.py")
        manifest = dict(bits=args.bits,
                        code=sha256(Path(__file__).read_bytes()).hexdigest(),
                        sources={name: sha256((args.source / name).read_bytes()).hexdigest()
                                 for name in sources})
        manifest_path = args.workdir / "run.json"
        if args.resume:
            if read(manifest_path) != manifest:
                raise ValueError("The workspace belongs to a different computation")
        else:
            args.workdir.mkdir()
            manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
        args.library = args.workdir / "packed.so"
        run(["g++", "-O3", "-ffp-contract=off", "-shared", "-fPIC",
             str(args.source / "checks/data/packed_poly.cpp"), "-lgmp",
             "-o", str(args.library)], check=True)
        active = setup(args)[12]
        with ProcessPoolExecutor(max_workers=args.workers) as pool:
            missing = [i for i in active if not (args.workdir / f"field-{i}.npz").is_file()]
            list(pool.map(run_fields, repeat(args), missing))
        with ProcessPoolExecutor(max_workers=args.workers) as pool:
            missing = [i for i in active if not (args.workdir / f"gram-{i}.json").is_file()]
            list(pool.map(run_gram, repeat(args), missing))
        rows = [json.loads((args.workdir / f"gram-{cap}.json").read_text()) for cap in active]
        totals = {k: [str(sum(Q(row[k][i]) for row in rows)) for i in range(2)]
                  for k in ("original", "mixed")}
        args.receipt = args.workdir / "mixed_pair_receipt.json"
        args.receipt.write_text(json.dumps(dict(complete=True, caps=rows, **totals), indent=2) + "\n")
    summary(args.source, args.receipt)


if __name__ == "__main__":
    main()
