#!/usr/bin/env python3
"""Display a polynomial identity and compute one of its coefficients.

Run ``python3 -B verify_d4_global.py`` for the geometric reconstruction
and all coefficient comparisons. Only the Python standard library is used.

Examples:
    python3 -B inspect_certificate.py
    python3 -B inspect_certificate.py --cone 2 --proof 2
    python3 -B inspect_certificate.py --cone 3 --proof 1 --all

Coefficients are stored as Fraction objects; exponents and permutation
indices are integers.
"""

import argparse
import json
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations
from math import factorial, prod
from pathlib import Path


DATA = Path(__file__).resolve().parent / "d4-certificate"
ZERO = Fraction(0)


def read_polynomial(rows):
    """Convert a JSON list of [exponent, coefficient] pairs to a polynomial."""
    return {tuple(exponent): Fraction(coefficient)
            for exponent, coefficient in rows}


def variable_name(parameter):
    """The JSON uses [i, j] for an edge variable and strings for a and b."""
    if isinstance(parameter, str):
        return parameter
    return f"x{parameter[0]}{parameter[1]}"


def monomial(exponent, names):
    factors = []
    for name, power in zip(names, exponent):
        if power:
            factors.append(name if power == 1 else f"{name}^{power}")
    return "*".join(factors) or "1"


def polynomial_text(polynomial, names):
    """Format a polynomial without decimal rounding or redundant factors 1."""
    terms = []
    for exponent, coefficient in sorted(polynomial.items(), reverse=True):
        if not coefficient:
            continue
        magnitude = abs(coefficient)
        term = monomial(exponent, names)
        if term == "1":
            term = str(magnitude)
        elif magnitude != 1:
            term = f"{magnitude}*{term}"
        if not terms:
            terms.append(("-" if coefficient < 0 else "") + term)
        else:
            terms.append((" - " if coefficient < 0 else " + ") + term)
    return "".join(terms) or "0"


def variable_action(exponent, permutation):
    """A permutation sends variable i to variable permutation[i]."""
    result = [0] * len(exponent)
    for index, power in enumerate(exponent):
        result[permutation[index]] = power
    return tuple(result)


def principal_group(edges):
    """The 120 vertex permutations of K5 induce permutations of its edges."""
    edge_index = {edge: index for index, edge in enumerate(edges)}
    return [tuple(edge_index[tuple(sorted((p[i], p[j])))] for i, j in edges)
            for p in permutations(range(5))]


def expand_weighted_square(square):
    """Expand x^w p(x)^2, without its outer positive rational coefficient.

    Ordered pairs supply the factor two in cross terms.
    """
    weight = square["weight_exponent"]
    polynomial = read_polynomial(square["polynomial"])
    expanded = defaultdict(Fraction)
    for left, a in polynomial.items():
        for right, b in polynomial.items():
            exponent = tuple(w + i + j
                             for w, i, j in zip(weight, left, right))
            expanded[exponent] += a * b
    return {exponent: coefficient for exponent, coefficient in expanded.items()
            if coefficient}


def linear_product_coefficient(polynomial, linear, exponent):
    """Return [x^exponent](polynomial * sum_i linear[i] x_i)."""
    result = ZERO
    for index, weight in enumerate(linear):
        if exponent[index]:
            predecessor = list(exponent)
            predecessor[index] -= 1
            result += weight * polynomial.get(tuple(predecessor), ZERO)
    return result


def linear_power_coefficient(linear, exponent):
    """The multinomial formula for [x^exponent](sum_i linear[i] x_i)^5."""
    multiplicity = Fraction(factorial(sum(exponent)),
                            prod(factorial(power) for power in exponent))
    return multiplicity * prod(weight ** power
                               for weight, power in zip(linear, exponent))


def square_text(square, names):
    coefficient = Fraction(square["coefficient"])
    weight = monomial(square["weight_exponent"], names)
    seed = polynomial_text(read_polynomial(square["polynomial"]), names)
    return f"{coefficient} * Av_H({weight} * ({seed})^2)"


def inspect(cone, proof_number, show_all):
    path = DATA / f"c{cone}-sos-simplified.json"
    grouped = json.loads(path.read_text())
    proof = grouped["proofs"][proof_number - 1]
    moment = json.loads((DATA / f"c{cone}-moment.json").read_text())
    if cone == 1:
        parameters = [list(edge) for edge in combinations(range(5), 2)]
        group = principal_group([tuple(edge) for edge in parameters])
        numerator_name, linear_name = "S", "L"
        linear = [Fraction(1)] * 10
    else:
        parameters = grouped["parameter_order"]
        group = [tuple(p) for p in grouped["group"]]
        numerator_name, linear_name = "N", "t"
        linear = [Fraction(1)] + [Fraction(1, 4)] * 9
    names = [variable_name(parameter) for parameter in parameters]
    numerator = read_polynomial(moment[f"{numerator_name}_coefficients"])
    determinant = read_polynomial(moment["D_coefficients"])
    k, beta = Fraction(proof["k"]), Fraction(proof["beta"])

    @lru_cache(maxsize=None)
    def orbit(exponent):
        """Return the orbit of a monomial under the group."""
        return frozenset(variable_action(exponent, p) for p in group)

    print(f"C{cone}, proof {proof_number}: {path.name}")
    print("Coefficient calculation for a polynomial identity.")
    print("Full verification: python3 -B verify_d4_global.py\n")
    print("Variable order: (" + ", ".join(names) + ")")
    if cone == 1:
        print("H = S5 acting on the edges of K5; L is the sum of the variables.")
    else:
        print("H is the permutation group listed in the certificate.")
        print("t = a + (sum of the other nine variables)/4.")
    print(f"|H| = {len(group)}; Av_H(f) = sum_(sigma in H) sigma(f)/|H|.")
    print(f"P = {numerator_name} - ({k})*D*{linear_name}"
          f" + ({beta})*{linear_name}^5")
    print(f"Identity: {len(proof['squares'])} averaged weighted squares"
          f" + {len(proof['remainder'])} averaged monomial remainders.\n")

    first = proof["squares"][0]
    expanded = expand_weighted_square(first)
    outer = Fraction(first["coefficient"])
    print("FIRST WEIGHTED SQUARE")
    print("  " + square_text(first, names))
    print("  Before averaging or multiplying by its outer coefficient:")
    print("  " + polynomial_text(expanded, names))
    print("\n  Each distinct orbit member occurs |H|/|orbit| times in the group sum.")
    print("  Averaging distributes the sum of coefficients over an orbit equally.")
    print("  Sum the coefficients over each orbit before dividing by its size.")
    orbit_labels, masses = {}, defaultdict(Fraction)
    for exponent, coefficient in sorted(expanded.items(), reverse=True):
        members = orbit(exponent)
        representative = min(members)
        label = orbit_labels.setdefault(representative, f"O{len(orbit_labels)+1}")
        masses[representative] += outer * coefficient
        signed_coefficient = ("+" if coefficient >= 0 else "") + str(coefficient)
        print(f"  {signed_coefficient} * {monomial(exponent, names)}: {label},"
              f" size {len(members)}, stabilizer size {len(group)//len(members)},"
              f" weighted coefficient {outer * coefficient}.")
    print("\n  Coefficient sums over the orbits of this first square:")
    for representative, label in orbit_labels.items():
        size = len(orbit(representative))
        print(f"  {label}: sum {masses[representative]};"
              f" coefficient of each orbit member = {masses[representative]/size}.")
    print("  The weighted square is nonnegative on the nonnegative orthant.")
    print()

    # C1 uses the monomial in the written worked example. In the other cones,
    # use the lexicographically greatest monomial of the first square.
    selected = (3, 1, 1, 0, 0, 0, 0, 0, 0, 0) if cone == 1 else max(expanded)
    members = orbit(selected)
    size = len(members)
    print("COEFFICIENT OF P")
    print(f"  Selected monomial: {monomial(selected, names)}")
    print(f"  Exponent vector: {selected}; orbit size: {size}.")
    print("  All square entries are expanded; nonzero contributions are:")
    square_total, nonzero_count = ZERO, 0
    for number, square in enumerate(proof["squares"], start=1):
        expansion = expand_weighted_square(square)
        mass = Fraction(square["coefficient"]) * sum(
            (coefficient for exponent, coefficient in expansion.items()
             if exponent in members), ZERO)
        square_total += mass
        if mass:
            nonzero_count += 1
            print(f"  Square {number:>3}: coefficient sum over orbit {str(mass):>15};"
                  f" coefficient contribution {mass / size}.")
    print(f"  The other {len(proof['squares'])-nonzero_count} square entries"
          " contribute zero to this coefficient.")

    remainder_total = ZERO
    for number, remainder in enumerate(proof["remainder"], start=1):
        if tuple(remainder["representative"]) in members:
            mass = Fraction(remainder["orbit_total"])
            remainder_total += mass
            print(f"  Remainder {number}: coefficient sum over orbit {mass};"
                  f" coefficient contribution {mass / size}.")
    if not remainder_total:
        print("  All remainder entries contribute zero to this coefficient.")
    print(f"  Sum of square coefficients = {square_total / size}.")
    print(f"  Sum of remainder coefficients = {remainder_total / size}.")
    actual = (square_total + remainder_total) / size
    print(f"  Coefficient from the decomposition = {actual}.\n")

    numerator_coefficient = numerator.get(selected, ZERO)
    product_coefficient = linear_product_coefficient(determinant, linear, selected)
    power_coefficient = linear_power_coefficient(linear, selected)
    expected = numerator_coefficient - k * product_coefficient + beta * power_coefficient
    print("  Compute the target coefficient from the moment data:")
    print(f"  [{monomial(selected, names)}] {numerator_name} = {numerator_coefficient}")
    print(f"  [{monomial(selected, names)}] D*{linear_name} = {product_coefficient}")
    print(f"  [{monomial(selected, names)}] {linear_name}^5 = {power_coefficient}")
    print(f"  Target coefficient = {numerator_coefficient} - ({k})*"
          f"({product_coefficient}) + ({beta})*({power_coefficient}) = {expected}.")
    if actual != expected:
        raise SystemExit("MISMATCH: the selected coefficient does not agree.")
    print("  AGREEMENT for this coefficient.\n")

    if show_all:
        print("ALL TERMS ON THE RIGHT SIDE OF THE IDENTITY")
        for number, square in enumerate(proof["squares"], start=1):
            print(f"  Square {number}: {square_text(square, names)}")
        for number, remainder in enumerate(proof["remainder"], start=1):
            coefficient = Fraction(remainder["orbit_total"])
            term = monomial(remainder["representative"], names)
            print(f"  Remainder {number}: {coefficient} * Av_H({term})")
        print()
    else:
        print("Add --all to display every square and remainder as a formula.")
    print("For the geometric reconstruction, group checks, and all 2,002")
    print("coefficient comparisons, run:")
    print("  python3 -B verify_d4_global.py")
    print("See REVIEWING.md for the relation between these checks and the proof.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--cone", type=int, choices=(1, 2, 3), default=1)
    parser.add_argument("--proof", type=int, choices=(1, 2), default=1)
    parser.add_argument("--all", action="store_true", help="print every weighted square and remainder term")
    args = parser.parse_args()
    inspect(args.cone, args.proof, args.all)
