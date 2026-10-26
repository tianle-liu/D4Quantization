"""Check the two polynomial identities on the principal cone.

The moment numerator is reconstructed from spanning trees and connected
unicyclic graphs of K5. The two decompositions into weighted squares and
monomials are expanded and compared in all 2,002 degree-five coefficients.
Only the Python standard library is used.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement, permutations
from math import factorial, prod, lcm
from pathlib import Path
import json
import argparse

if not __debug__:
    raise SystemExit('This verifier must be run without Python -O.')

ROOT = Path(__file__).resolve().parent
EDGES = list(combinations(range(5), 2))
EDGE_INDEX = {e: i for i, e in enumerate(EDGES)}
GROUP = [tuple(EDGE_INDEX[tuple(sorted((p[u], p[v])))] for u, v in EDGES)
         for p in permutations(range(5))]


def exponent(indices):
    out = [0]*10
    for i in indices:
        out[i] += 1
    return tuple(out)


def connected(indices):
    reached = {0}
    while True:
        enlarged = reached | {v for i in indices for u, v in
                              (EDGES[i], EDGES[i][::-1]) if u in reached}
        if enlarged == reached:
            return len(reached) == 5
        reached = enlarged


def cycle_length(indices):
    adjacency = {i: set() for i in range(5)}
    for j in indices:
        u, v = EDGES[j]
        adjacency[u].add(v)
        adjacency[v].add(u)
    while True:
        leaves = [v for v, neighbors in adjacency.items() if len(neighbors) == 1]
        if not leaves:
            return sum(bool(neighbors) for neighbors in adjacency.values())
        for v in leaves:
            if adjacency[v]:
                u = adjacency[v].pop()
                adjacency[u].remove(v)


def reconstruct(source):
    """Build Proposition 2.2's graph formula and compare the saved moments.

    The full verification also computes the moment by zonotope integration.
    """
    D = {exponent(t): F(1) for t in combinations(range(10), 4) if connected(t)}
    DL = defaultdict(F)
    for e, c in D.items():
        for i in range(10):
            z = list(e)
            z[i] += 1
            DL[tuple(z)] += c
    S = defaultdict(F, DL)
    cycle_counts = defaultdict(int)
    for graph in combinations(range(10), 5):
        if connected(graph):
            length = cycle_length(graph)
            S[exponent(graph)] += length-2
            cycle_counts[length] += 1
    assert len(D) == 125 and cycle_counts == {3: 150, 4: 60, 5: 12}
    original = json.loads((source/'c1-moment.json').read_text())
    assert D == {tuple(e): F(c) for e, c in original['D_coefficients']}
    assert dict(S) == {tuple(e): F(c) for e, c in original['S_coefficients']}
    for polynomial in (D, S):
        for e, coefficient in polynomial.items():
            assert all(polynomial.get(act(e, p), F(0)) == coefficient for p in GROUP)
    print('K5 spanning-tree/unicyclic reconstruction: PASS.')
    return D, DL, S


def act(e, p):
    """Apply x_i -> x_{p[i]} to the exponent vector of a monomial."""
    out = [0]*10
    for i, value in enumerate(e):
        out[p[i]] = value
    return tuple(out)


MONOMIALS = [exponent(t) for t in combinations_with_replacement(range(10), 5)]
CANON, SIZES = {}, {}
for e in MONOMIALS:
    if e not in CANON:
        orbit = {act(e, p) for p in GROUP}
        rep = min(orbit)
        SIZES[rep] = len(orbit)
        for z in orbit:
            CANON[z] = rep
assert len(MONOMIALS) == 2002 and len(SIZES) == 35


def verify_certificate(cert, DL, S):
    """Check one identity in Proposition 2.4 in every degree-five monomial.

    The weights are positive, the exponents are nonnegative, and the
    polynomials being squared have integer coefficients. The decomposition
    therefore proves nonnegativity on the nonnegative orthant.
    """
    assert cert['exact_identity']
    k, beta = F(cert['k']), F(cert['beta'])
    expected_counts = {(F(13, 10), F(29, 20000)): (32, 35, 100000),
                       (F(3, 2), F(163, 50000)): (34, 35, 1000000)}
    square_count, remainder_count, denominator = expected_counts[k, beta]
    assert len(cert['squares']) == square_count
    assert len(cert['remainder']) == remainder_count
    assert cert['seed_coefficient_bound'] == 10
    assert cert['common_outer_denominator'] == denominator
    masses = defaultdict(F)
    common_denominator, height, terms = 1, 0, 0
    for square in cert['squares']:
        w = tuple(square['weight_exponent'])
        coefficient = F(square['coefficient'])
        assert coefficient > 0 and len(w) == 10
        assert sum(w) in (1, 3)
        assert denominator % coefficient.denominator == 0
        assert all(isinstance(v, int) and v >= 0 for v in w)
        common_denominator = lcm(common_denominator, coefficient.denominator)
        polynomial = [(tuple(e), F(c)) for e, c in square['polynomial']]
        terms += len(polynomial)
        for e, c in polynomial:
            assert len(e) == 10 and all(isinstance(v, int) and v >= 0 for v in e)
            assert sum(w)+2*sum(e) == 5 and c.denominator == 1
            height = max(height, abs(c.numerator))
        # Sum the coefficients over each monomial orbit. Group averaging
        # divides this sum equally among the distinct orbit members.
        # Ordered pairs of polynomial terms supply both cross terms.
        for e, a in polynomial:
            for f, b in polynomial:
                z = tuple(i+j+h for i, j, h in zip(e, f, w))
                masses[CANON[z]] += coefficient*a*b
    seen_remainders = set()
    for remainder in cert['remainder']:
        e = tuple(remainder['representative'])
        # orbit_total is the coefficient of Av(x^e).
        coefficient = F(remainder['orbit_total'])
        assert CANON[e] == e and coefficient > 0
        assert e not in seen_remainders
        seen_remainders.add(e)
        masses[e] += coefficient
    # Compare all 2002 coefficients, including zeros in either polynomial.
    for e in MONOMIALS:
        l5 = F(factorial(5), prod(factorial(v) for v in e))
        assert masses[CANON[e]]/SIZES[CANON[e]] == S.get(e, 0)-k*DL[e]+beta*l5
    assert height == cert['seed_coefficient_bound'] == 10
    assert common_denominator == cert['common_outer_denominator']
    expected_denominator = {(F(13, 10), F(29, 20000)): 100000,
                            (F(3, 2), F(163, 50000)): 1000000}
    assert common_denominator == expected_denominator[k, beta]
    print(f'C1 k={k}, beta={beta}: PASS; {len(cert["squares"])} square orbits, '
          f'{terms} polynomial terms, maximum integer coefficient {height}, '
          f'common outer denominator {common_denominator}.')



if __name__ == '__main__':
    default_source = ROOT if (ROOT/'c1-moment.json').exists() else ROOT.parents[1]/'d4-cone-paper/d4-certificate'
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=default_source,
                        help='Directory containing c1-moment.json.')
    parser.add_argument('--certificates', type=Path,
                        help='Grouped c1-sos-simplified.json file or its directory.')
    args = parser.parse_args()
    if args.certificates is None:
        args.certificates = args.source/'c1-sos-simplified.json'
        if not args.certificates.exists():
            args.certificates = ROOT.parent/'certificates/c1-sos-simplified.json'
    if args.certificates.is_dir():
        args.certificates /= 'c1-sos-simplified.json'
    D, DL, S = reconstruct(args.source)
    grouped = json.loads(args.certificates.read_text())
    assert grouped['edges'] == [list(e) for e in EDGES]
    assert grouped['orbit_count'] == len(SIZES)
    assert {tuple(e): F(c) for e, c in grouped['D']} == D
    assert {tuple(e): F(c) for e, c in grouped['S']} == dict(S)
    proofs = grouped['proofs']
    assert len(proofs) == 2
    assert {(F(p['k']), F(p['beta'])) for p in proofs} == {
        (F(13, 10), F(29, 20000)), (F(3, 2), F(163, 50000))}
    for proof in proofs:
        verify_certificate(proof, DL, S)
    print('Both C1 polynomial identities: PASS')
