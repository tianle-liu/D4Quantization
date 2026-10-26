"""Check the four polynomial identities on C2 and C3.

Using the supplied moment data, the program verifies the Gram determinant,
permutation groups, invariance, all 2,002 coefficients of each identity,
positivity of the weights, coefficient bounds, and scalar endpoints.
The full verification in verify_d4_global.py first reconstructs the geometry
and moments and also compares them with a boundary-triangulation calculation.

By default, the program reads moment files from its own directory.
Use --source DIR to select another directory.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations_with_replacement, permutations
from math import factorial, prod
from pathlib import Path
import argparse
import json

if not __debug__:
    raise SystemExit('Verification requires assertions: do not use Python -O or -OO.')


def monomials(degree):
    """Enumerate every degree-'degree' monomial in the ten parameters."""
    for indices in combinations_with_replacement(range(10), degree):
        e = [0]*10
        for i in indices:
            e[i] += 1
        yield tuple(e)


def action(e, p):
    """Apply x_i -> x_{p[i]} to the exponent vector of a monomial.

    Arrays use zero-based indices; the manuscript's cycles use positions 1..10.
    """
    out = [0]*10
    for i, c in enumerate(e):
        out[p[i]] = c
    return tuple(out)


def permutation_from_cycles(cycles):
    """Convert disjoint cycles in manuscript positions 1..10 to an array."""
    p = list(range(10))
    used = set()
    for cycle in cycles:
        assert len(cycle) == len(set(cycle)) and len(cycle) >= 2
        assert all(type(i) is int and 1 <= i <= 10 for i in cycle)
        assert not used.intersection(cycle)
        used.update(cycle)
        for i, position in enumerate(cycle):
            p[position-1] = cycle[(i+1) % len(cycle)]-1
    return tuple(p)


def generated_group(generators):
    """Close the displayed generators under composition, from the identity.

    With action x_i -> x_{p[i]}, composing q followed by p gives p[q[i]].
    Since these are permutations of a finite set, this closure is a group.
    """
    identity = tuple(range(10))
    group, pending = {identity}, [identity]
    while pending:
        p = pending.pop()
        for q in generators:
            composed = tuple(p[q[i]] for i in range(10))
            if composed not in group:
                group.add(composed)
                pending.append(composed)
    return group


def polynomial(items, degree):
    """Read a homogeneous polynomial, rejecting duplicate monomials."""
    out = {}
    for exponent, coefficient in items:
        e, c = tuple(exponent), F(coefficient)
        assert len(e) == 10 and all(type(v) is int and v >= 0 for v in e)
        assert sum(e) == degree and e not in out
        out[e] = c
    return {e: c for e, c in out.items() if c}


def multiply(left, right):
    out = defaultdict(F)
    for e, a in left.items():
        for f, b in right.items():
            out[tuple(x+y for x, y in zip(e, f))] += a*b
    return {e: c for e, c in out.items() if c}


def gram_determinant(generators):
    """Expand det(sum_i x_i R_i) directly from the ten Gram generators."""
    entries = [[{} for _ in range(4)] for _ in range(4)]
    for i in range(4):
        for j in range(4):
            for k, matrix in enumerate(generators):
                if matrix[i][j]:
                    e = tuple(int(v == k) for v in range(10))
                    entries[i][j][e] = F(matrix[i][j])
    out = defaultdict(F)
    for p in permutations(range(4)):
        inversions = sum(p[i] > p[j] for i in range(4) for j in range(i+1, 4))
        term = {(0,)*10: F((-1)**inversions)}
        for i, j in enumerate(p):
            term = multiply(term, entries[i][j])
        for e, c in term.items():
            out[e] += c
    return {e: c for e, c in out.items() if c}


def verify_cone(cone, source, certificate_dir):
    """Verify both Proposition 2.4 identities for C2 or C3.

    The input N must first be identified with 60 D M by Proposition 2.3;
    verify_d4_global.py runs that reconstruction before calling this checker.
    """
    data = json.loads((source/f'c{cone}-moment.json').read_text())
    geometry = json.loads((source/f'c{cone}-geometry.json').read_text())
    symmetry = json.loads((source/f'c{cone}-symmetry.json').read_text())
    path = certificate_dir/f'c{cone}-sos-simplified.json'
    cert = json.loads(path.read_text())
    assert cert['cone'] == data['cone'] == geometry['cone'] == symmetry['cone'] == cone
    assert cert['parameter_order'] == data['parameter_order'] == geometry['parameter_order']
    N, D = polynomial(data['N_coefficients'], 5), polynomial(data['D_coefficients'], 4)
    assert D == gram_determinant(geometry['generators'])
    group = list(map(tuple, cert['group']))
    group_set = set(group)
    assert group_set == set(map(tuple, symmetry['group']))
    # Generate the groups specified before Proposition 2.4.
    # These cycle entries use the manuscript's one-based parameter positions.
    cycles = {
        2: [((2, 6), (3, 8), (5, 10)),
            ((2, 3), (4, 5), (6, 9), (7, 8))],
        3: [((2, 10), (4, 8), (5, 9), (6, 7)),
            ((2, 6, 10, 8, 3, 5), (4, 9, 7))],
    }[cone]
    generators = [permutation_from_cycles(c) for c in cycles]
    assert group_set == generated_group(generators)
    assert len(group_set) == len(group) == {2: 12, 3: 36}[cone]
    assert tuple(range(10)) in group_set
    for p in group:
        assert sorted(p) == list(range(10)) and p[0] == 0
        for q in group:
            assert tuple(p[q[i]] for i in range(10)) in group_set
        for poly in (N, D):
            assert {action(e, p): c for e, c in poly.items()} == poly
    E = list(monomials(5))
    assert len(E) == 2002
    canon, sizes = {}, {}
    for e in E:
        if e not in canon:
            orbit = {action(e, p) for p in group}
            rep = min(orbit)
            sizes[rep] = len(orbit)
            for z in orbit:
                canon[z] = rep
    assert len(sizes) == cert['orbit_count'] == {2: 225, 3: 91}[cone]
    Dt = defaultdict(F)
    for e, c in D.items():
        for i in range(10):
            z = list(e)
            z[i] += 1
            Dt[tuple(z)] += c*(1 if i == 0 else F(1, 4))
    t5 = {e: F(factorial(5), prod(factorial(j) for j in e))*F(4**e[0], 4**5)
          for e in E}
    assert all(N.get(e, 0)-20*Dt[e] >= 0 for e in E)
    expected = {F(55, 2): F(21, 2), F(31): F(20)}
    expected_sizes = {
        2: {F(55, 2): (176, 225, 10, 100000), F(31): (217, 222, 4, 100000)},
        3: {F(55, 2): (71, 91, 10, 10000), F(31): (88, 89, 4, 10000)},
    }[cone]
    assert len(cert['proofs']) == 2
    seen = set()
    for proof in cert['proofs']:
        k, beta = F(proof['k']), F(proof['beta'])
        assert k in expected and beta == expected[k] and k not in seen
        seen.add(k)
        assert (len(proof['squares']), len(proof['remainder']),
                proof['seed_coefficient_bound'], proof['common_outer_denominator']) == expected_sizes[k]
        mass = defaultdict(F)
        height = 0
        denominator = proof['common_outer_denominator']
        assert type(denominator) is int and denominator > 0
        for item in proof['squares']:
            weight, coefficient = tuple(item['weight_exponent']), F(item['coefficient'])
            assert len(weight) == 10 and all(type(v) is int and v >= 0 for v in weight)
            assert sum(weight) in (1, 3) and coefficient > 0
            assert denominator % coefficient.denominator == 0
            poly = polynomial(item['polynomial'], (5-sum(weight))//2)
            for c in poly.values():
                assert c.denominator == 1
                height = max(height, abs(c.numerator))
            # Sum the coefficients over each monomial orbit. Group averaging
            # divides this sum equally among the distinct orbit members.
            # Ordered pairs of polynomial terms supply both cross terms.
            for e, a in poly.items():
                for f, b in poly.items():
                    z = tuple(x+y+w for x, y, w in zip(e, f, weight))
                    mass[canon[z]] += coefficient*a*b
        assert height == proof['seed_coefficient_bound']
        for item in proof['remainder']:
            # orbit_total is the coefficient of Av(x^rep).
            rep, coefficient = tuple(item['representative']), F(item['orbit_total'])
            assert canon[rep] == rep and coefficient > 0
            mass[rep] += coefficient
        target = {e: N.get(e, 0)-k*Dt[e]+beta*t5[e] for e in E}
        # This compares every degree-five coefficient, including zero entries.
        assert all(mass[canon[e]]/sizes[canon[e]] == target[e] for e in E)
        print(f'C{cone} k={k} beta={beta}: PASS; '
              f'{len(proof["squares"])} squares + {len(proof["remainder"])} remainders; '
              f'maximum integer coefficient {height}; common outer denominator {denominator}; '
              f'all 2002 coefficients.')
    assert seen == set(expected)
    print(f'C{cone}: Gram determinant, manuscript group, invariance, and N>=20Dt: PASS')


def verify_scalar_endpoints():
    """Check the endpoint inequalities in the C2/C3 scalar comparison.

    The extension between endpoints uses concavity, as proved in the paper.
    """
    assert F(7, 20) < F(10, 13)**4
    tests = [(F(7, 20), F(110), F(21, 2)),
             (F(2, 3), F(110), F(21, 2)),
             (F(2, 3), F(124), F(20)),
             (F(1), F(124), F(20))]
    margins = []
    for d, slope, intercept in tests:
        line = slope*d-intercept
        margin = line**4-104**4*d**5
        assert line > 0 and (margin > 0 if d < 1 else margin == 0)
        margins.append(str(margin))
    print('Three-line scalar comparison: PASS; endpoint differences', ', '.join(margins))


if __name__ == '__main__':
    folder = Path(__file__).resolve().parent
    default_source = folder if (folder/'c2-moment.json').exists() else folder.parents[1]/'d4-cone-paper'/'d4-certificate'
    parser = argparse.ArgumentParser()
    parser.add_argument('--source', type=Path, default=default_source)
    parser.add_argument('--certificates', type=Path, default=folder)
    args = parser.parse_args()
    for cone in (2, 3):
        verify_cone(cone, args.source, args.certificates)
    verify_scalar_endpoints()
    print('All four C2/C3 polynomial identities: PASS')
