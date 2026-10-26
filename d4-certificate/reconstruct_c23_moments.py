"""Recover the C2 and C3 moment polynomials by vertex integration.

This implements the integration formulas in Section 2.2, Proposition 2.3
(LaTeX label ``prop:d4-reconstructed-moments``). The geometry is read from
``c2-geometry.json`` and ``c3-geometry.json``; the output records D = det Q
and N = 60 D M(Q), together with the checks stated in that proposition.
The triangulation program computes these moments by another formula.

Polynomial coefficients are integers. Rational localization weights use
Fraction and are cleared by a common denominator before expansion. A
monomial is stored as one integer with ten four-bit exponent fields:
    packed(e) = sum(e[i] * 16**i for i in range(10)).
All polynomials computed here have total degree at most nine. Thus each
exponent is less than sixteen, and integer addition of packed keys is
exactly addition of exponent vectors: multiplication causes no carries
between fields. JSON output unpacks these keys into ordinary exponent lists.
"""

from collections import defaultdict
from fractions import Fraction
from math import lcm, prod
from pathlib import Path
import json
import time


DIMENSION = 4
PARAMETER_COUNT = 10
EXPONENT_BITS = 4
EXPONENT_MASK = (1 << EXPONENT_BITS) - 1

# Factors appearing in the displayed integration formulas in Section 2.2.
VOLUME_SERIES_FACTOR = 24       # 4!
MOMENT_SERIES_FACTOR = 720      # 6!
COORDINATE_VOLUME_FACTOR = 16   # dr = det(2Q) dx = 16 D dx
COORDINATE_MOMENT_FACTOR = 64   # M(Q) = contraction / (64 D^2)
MOMENT_NUMERATOR_FACTOR = 60    # N = 60 D M(Q)

# T_ij below stores 720 P times integral_P r_i r_j dr. Consequently,
# J = sum_ij adj(Q)_ij T_ij = 720 P * 64 D^2 M(Q), and
# DN = 60 D^2 M(Q) = J / (768 P).
CONTRACTION_TO_DN_DIVISOR = (
    MOMENT_SERIES_FACTOR * COORDINATE_MOMENT_FACTOR // MOMENT_NUMERATOR_FACTOR
)


def add(*polys):
    """Add sparse polynomials and remove zero coefficients."""
    result = defaultdict(int)
    for polynomial in polys:
        for monomial, coefficient in polynomial.items():
            result[monomial] += coefficient
    return {
        monomial: coefficient
        for monomial, coefficient in result.items()
        if coefficient
    }


def scale(polynomial, factor):
    """Multiply each coefficient by a scalar, dropping zero terms."""
    return {
        monomial: coefficient * factor
        for monomial, coefficient in polynomial.items()
        if coefficient * factor
    }


def mul(left, right):
    """Multiply polynomials by adding the packed exponent vectors."""
    result = defaultdict(int)
    for left_monomial, left_coefficient in left.items():
        for right_monomial, right_coefficient in right.items():
            result[left_monomial + right_monomial] += (
                left_coefficient * right_coefficient
            )
    return {
        monomial: coefficient
        for monomial, coefficient in result.items()
        if coefficient
    }


def power(polynomial, exponent):
    """Return a nonnegative integer power by repeated multiplication."""
    result = {0: 1}
    for _ in range(exponent):
        result = mul(result, polynomial)
    return result


def lin(coefficients):
    """Encode a linear form in the fixed ten-parameter order."""
    return {
        1 << (EXPONENT_BITS * i): coefficient
        for i, coefficient in enumerate(coefficients)
        if coefficient
    }


def determinant(matrix):
    """Expand a polynomial matrix determinant along its first row."""
    size = len(matrix)
    if size == 1:
        return matrix[0][0]
    return add(*(
        scale(
            mul(
                matrix[0][j],
                determinant([row[:j] + row[j + 1:] for row in matrix[1:]]),
            ),
            (-1) ** j,
        )
        for j in range(size)
    ))


def exponents(monomial):
    """Decode a packed key into its ten nonnegative integer exponents."""
    return [
        (monomial >> (EXPONENT_BITS * i)) & EXPONENT_MASK
        for i in range(PARAMETER_COUNT)
    ]


def quotient(numerator, divisor):
    """Perform exact integer-coefficient division by one polynomial.

    The largest packed key orders monomials lexicographically, starting
    with the last parameter. At every step the leading exponent vector
    must be divisible componentwise and the leading coefficient must
    divide exactly. An assertion failure rejects an inexact division;
    the caller also checks the result by multiplying back.
    """
    remainder = numerator.copy()
    result = {}
    leading_monomial = max(divisor)
    leading_exponents = exponents(leading_monomial)
    while remainder:
        monomial = max(remainder)
        monomial_exponents = exponents(monomial)
        assert all(
            a >= b for a, b in zip(monomial_exponents, leading_exponents)
        ), ("nondivisible leading monomial", monomial_exponents, leading_exponents)

        # Componentwise divisibility above makes packed subtraction safe:
        # no exponent field borrows from a neighboring field.
        shift = monomial - leading_monomial
        coefficient, coefficient_remainder = divmod(
            remainder[monomial], divisor[leading_monomial]
        )
        assert not coefficient_remainder
        result[shift] = coefficient
        for divisor_monomial, divisor_coefficient in divisor.items():
            key = divisor_monomial + shift
            remainder[key] = (
                remainder.get(key, 0) - coefficient * divisor_coefficient
            )
            if not remainder[key]:
                del remainder[key]
    return result


def run(cone):
    """Integrate the reconstructed polytope and write c{cone}-moment.json."""
    start = time.time()
    folder = Path(__file__).parent
    data = json.loads((folder / f"c{cone}-geometry.json").read_text())
    records = data["vertices"]
    generators = data["generators"]

    # Build Q, det Q, and adj Q as complete parameter polynomials.
    Q = [
        [
            lin([generator[i][j] for generator in generators])
            for j in range(DIMENSION)
        ]
        for i in range(DIMENSION)
    ]
    D = determinant(Q)
    adj = [
        [
            scale(
                determinant([
                    [Q[a][b] for b in range(DIMENSION) if b != i]
                    for a in range(DIMENSION)
                    if a != j
                ]),
                (-1) ** (i + j),
            )
            for j in range(DIMENSION)
        ]
        for i in range(DIMENSION)
    ]

    # For each vertex, columns u_j of inverse_matrix are B_I^{-1} columns.
    # The paper uses s_j = xi^T u_j, omega = 1 / prod_j s_j, and
    # h_i = sum_j (u_j)_i / s_j. All retained bases have |det B_I| = 1.
    xi = [1, 2, 4, 8]
    prepared = []
    common_denominator = 1
    for record in records:
        assert record["denominator"] == 1
        inverse_matrix = record["inverse_numerator"]
        vertex = record["vertex_numerator"]
        s = [
            sum(xi[i] * inverse_matrix[i][j] for i in range(DIMENSION))
            for j in range(DIMENSION)
        ]
        assert all(s)
        omega = Fraction(1, prod(s))
        h = [
            sum(Fraction(inverse_matrix[i][j], s[j]) for j in range(DIMENSION))
            for i in range(DIMENSION)
        ]
        second_weight = [
            [
                h[i] * h[j]
                + sum(
                    Fraction(
                        inverse_matrix[i][k] * inverse_matrix[j][k], s[k] ** 2
                    )
                    for k in range(DIMENSION)
                )
                for j in range(DIMENSION)
            ]
            for i in range(DIMENSION)
        ]

        # Clear every rational coefficient occurring in the localization
        # formula. Powers of the parameter-linear z and v remain integral.
        coefficients = (
            [omega]
            + [omega * value for value in h]
            + [omega * value for row in second_weight for value in row]
        )
        common_denominator = lcm(
            common_denominator, *(value.denominator for value in coefficients)
        )
        prepared.append((vertex, omega, h, second_weight))
    print("cone", cone, "common denominator", common_denominator, flush=True)

    # Only the upper triangle is needed because the moment tensor is
    # symmetric. Its entries store 720 P times the actual integrals.
    moment_tensor_numerators = {
        (i, j): {} for i in range(DIMENSION) for j in range(i, DIMENSION)
    }
    volume_numerator = {}
    for position, (vertex, omega, h, second_weight) in enumerate(prepared):
        vertex_polynomials = [lin(row) for row in vertex]
        z = lin([
            sum(xi[i] * vertex[i][k] for i in range(DIMENSION))
            for k in range(PARAMETER_COUNT)
        ])
        z4 = power(z, 4)
        z5 = mul(z4, z)
        z6 = mul(z5, z)
        volume_numerator = add(
            volume_numerator, scale(z4, int(common_denominator * omega))
        )

        # Three summands of the paper's formula for integral r_i r_j:
        # 30 z^4 v_i v_j - 6 z^5 (h_i v_j + h_j v_i)
        #     + z^6 (h_i h_j + sum_l (u_l)_i (u_l)_j / s_l^2).
        # Multiplication by P clears the already computed denominators.
        for i, j in moment_tensor_numerators:
            first_term = scale(
                mul(z4, mul(vertex_polynomials[i], vertex_polynomials[j])),
                int(30 * common_denominator * omega),
            )
            linear_term = add(
                scale(
                    vertex_polynomials[j],
                    int(-6 * common_denominator * omega * h[i]),
                ),
                scale(
                    vertex_polynomials[i],
                    int(-6 * common_denominator * omega * h[j]),
                ),
            )
            second_term = mul(z5, linear_term)
            third_term = scale(
                z6, int(common_denominator * omega * second_weight[i][j])
            )
            moment_tensor_numerators[i, j] = add(
                moment_tensor_numerators[i, j], first_term, second_term, third_term
            )
        if (position + 1) % 30 == 0:
            print(
                "cone", cone, "vertices integrated", position + 1,
                "seconds", time.time() - start, flush=True,
            )

    # The original Voronoi region has coordinate volume one. The change
    # r = 2Qx gives vol(P_Q) = 16 D, while vertex localization gives
    # vol(P_Q) = sum omega z^4 / 24. Check every coefficient of this identity.
    assert volume_numerator == scale(
        D, VOLUME_SERIES_FACTOR * COORDINATE_VOLUME_FACTOR * common_denominator
    ), "Voronoi volume mismatch"

    # Contract with adj(Q), counting both symmetric off-diagonal entries.
    # The Jacobian and quadratic-form change yield
    # M(Q) = sum_ij adj(Q)_ij integral r_i r_j / (64 D^2).
    contracted_numerator = add(*(
        scale(mul(polynomial, adj[i][j]), 1 if i == j else 2)
        for (i, j), polynomial in moment_tensor_numerators.items()
    ))
    normalization_divisor = CONTRACTION_TO_DN_DIVISOR * common_denominator
    DN = {
        monomial: coefficient // normalization_divisor
        for monomial, coefficient in contracted_numerator.items()
    }
    assert all(
        coefficient % normalization_divisor == 0
        for coefficient in contracted_numerator.values()
    )
    N = quotient(DN, D)
    assert mul(D, N) == DN

    # The packed key 5 is a^5. At Q = aA, M(A) = 13/30 and det A = 4,
    # hence the coefficient is 60 * 4 * (13/30) = 104.
    assert N.get(5) == 104

    # With t = a + (sum lambda_j)/4, this residual is N - 20 D t.
    # Nonnegative coefficients prove the bound throughout the orthant.
    four_t = lin([4] + [1] * 9)
    residual = add(N, scale(mul(D, four_t), -5))
    assert all(coefficient >= 0 for coefficient in residual.values()), (
        "N >= 20 D t is not coefficientwise positive"
    )

    out = {
        "cone": cone,
        "parameter_order": data["parameter_order"],
        "D_terms": len(D),
        "N_terms": len(N),
        "DN_terms": len(DN),
        "moment_tensor_term_counts": {
            f"{i}{j}": len(polynomial)
            for (i, j), polynomial in moment_tensor_numerators.items()
        },
        "volume_identity_verified": True,
        "exact_polynomial_division_verified": True,
        "first_bound_coefficientwise_verified": True,
        "first_bound_nonzero_terms": len(residual),
        "N_coefficients": [
            [exponents(monomial), coefficient]
            for monomial, coefficient in sorted(N.items())
        ],
        "D_coefficients": [
            [exponents(monomial), coefficient]
            for monomial, coefficient in sorted(D.items())
        ],
        "seconds": time.time() - start,
    }
    (folder / f"c{cone}-moment.json").write_text(json.dumps(out, indent=2) + "\n")
    print(
        json.dumps(
            {
                key: value
                for key, value in out.items()
                if not key.endswith("_coefficients")
            },
            indent=2,
        ),
        flush=True,
    )


if __name__ == "__main__":
    for cone in [2, 3]:
        run(cone)
