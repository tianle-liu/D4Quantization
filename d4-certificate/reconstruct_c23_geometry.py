"""Reconstruct the C2 and C3 Voronoi polytopes using integer arithmetic.

This is the geometry part of Proposition 2.3 in Section 2.2 of the paper
(LaTeX label ``prop:d4-reconstructed-moments``). It writes the facet normals,
linear support functions, and linear vertices used by
``reconstruct_c23_moments.py``. No precomputed geometry is read.

The parameters are a, followed by the allowed edges in lexicographic order,
and finally the extra vector (1, 1, -1, -1) for C3. The matrix is
Q = a A + sum_j lambda_j g_j g_j^T. All geometric conclusions below concern
strictly positive parameters; continuity at positive-definite boundary
forms is addressed in the paper.
"""

from collections import Counter
from itertools import combinations, product
from pathlib import Path
import json
import time


DIMENSION = 4
PARAMETER_COUNT = 10
FACET_COUNT = 30
EXPECTED_VERTEX_COUNT = 120
REFERENCE_BASES_EXAMINED = 27405  # binomial(30, 4)
PARITY_BOX_RADIUS = 2

A = [
    [2, 1, -1, -1],
    [1, 2, -1, -1],
    [-1, -1, 2, 0],
    [-1, -1, 0, 2],
]


def norm(v, matrix):
    """Return the quadratic value v^T matrix v."""
    return sum(
        v[i] * matrix[i][j] * v[j]
        for i in range(DIMENSION)
        for j in range(DIMENSION)
    )


def determinant(matrix):
    """Evaluate the determinant by the signed first-row expansion."""
    size = len(matrix)
    if size == 1:
        return matrix[0][0]

    return sum(
        (-1) ** j
        * matrix[0][j]
        * determinant([row[:j] + row[j + 1:] for row in matrix[1:]])
        for j in range(size)
    )


def adjugate(matrix):
    """Return the transposed cofactor matrix of a four-by-four matrix."""
    return [
        [
            (-1) ** (i + j)
            * determinant([
                [matrix[a][b] for b in range(DIMENSION) if b != i]
                for a in range(DIMENSION)
                if a != j
            ])
            for j in range(DIMENSION)
        ]
        for i in range(DIMENSION)
    ]


def run(cone):
    """Enumerate and certify the geometry, then write c{cone}-geometry.json."""
    start = time.time()

    # In four coordinates, edge ij represents e_i - e_j with e_0 = 0.
    # These are exactly the generators in the paper's cone description.
    edges = []
    edge_vectors = []
    for i, j in combinations(range(5), 2):
        if (i, j) == (1, 2) or (cone == 3 and (i, j) == (3, 4)):
            continue
        edges.append([i, j])
        edge_vectors.append(
            tuple(int(i == k) - int(j == k) for k in range(1, 5))
        )
    if cone == 3:
        edges.append("b")
        edge_vectors.append((1, 1, -1, -1))

    generators = [A] + [
        [[g[i] * g[j] for j in range(DIMENSION)] for i in range(DIMENSION)]
        for g in edge_vectors
    ]

    # A nonzero parity class contributes its unique shortest pair +/-v.
    # The A-minimum is 2 or 4. Since diag(A^{-1}) = (1, 1, 1, 1),
    # Cauchy--Schwarz gives |v_i|^2 <= v^T A v <= 4. Thus the box
    # [-2, 2]^4 contains every candidate of A-length at most 4.
    shortest_vectors = []
    parity_classes = []
    for parity in product(range(2), repeat=DIMENSION):
        if not any(parity):
            continue

        candidates = [
            v
            for v in product(
                range(-PARITY_BOX_RADIUS, PARITY_BOX_RADIUS + 1),
                repeat=DIMENSION,
            )
            if tuple(x % 2 for x in v) == parity and norm(v, A) <= 4
        ]
        minimum = min(norm(v, A) for v in candidates)

        # For each rank-one form, (g^T v)^2 is at least its parity (0 or 1).
        # A pair attaining every generator minimum minimizes Q for every
        # positive parameter choice. Uniqueness of this pair is essential.
        simultaneous_minimizers = [
            v
            for v in candidates
            if norm(v, A) == minimum
            and all(
                sum(x * y for x, y in zip(v, g)) ** 2
                == sum(x * y for x, y in zip(parity, g)) % 2
                for g in edge_vectors
            )
        ]
        assert len(simultaneous_minimizers) == 2 and (
            simultaneous_minimizers[0]
            == tuple(-x for x in simultaneous_minimizers[1])
        )
        shortest_vectors.extend(simultaneous_minimizers)
        parity_classes.append({
            "parity": parity,
            "A_minimum": minimum,
            "vectors": simultaneous_minimizers,
        })

    # This checks the diagonal-inverse identity used for the finite box.
    assert determinant(A) == 4 and all(
        adjugate(A)[i][i] == 4 for i in range(DIMENSION)
    )

    # The paper proves that these shortest parity representatives give
    # all Voronoi facets and that omitted integer-vector inequalities are
    # redundant. In r = 2 Q x coordinates, the inequalities are B r <= b.
    # Each row of support_coefficients stores one linear form v^T Q v.
    facets = sorted(shortest_vectors)
    support_coefficients = [
        [norm(v, generator) for generator in generators]
        for v in facets
    ]
    reference_support = list(map(sum, support_coefficients))

    vertices = []
    invertible_bases = 0
    for basis in combinations(range(FACET_COUNT), DIMENSION):
        basis_matrix = [list(facets[i]) for i in basis]
        denominator = determinant(basis_matrix)
        if not denominator:
            continue
        invertible_bases += 1
        inverse_numerator = adjugate(basis_matrix)

        # Store B_I^{-1} as inverse_numerator / denominator, with a
        # positive denominator so that all slack comparisons preserve sign.
        if denominator < 0:
            denominator = -denominator
            inverse_numerator = [
                [-x for x in row] for row in inverse_numerator
            ]

        reference_vertex_numerator = [
            sum(
                inverse_numerator[i][j] * reference_support[basis[j]]
                for j in range(DIMENSION)
            )
            for i in range(DIMENSION)
        ]
        if any(
            denominator * reference_support[j]
            < sum(
                facets[j][i] * reference_vertex_numerator[i]
                for i in range(DIMENSION)
            )
            for j in range(FACET_COUNT)
        ):
            continue

        # Express each vertex coordinate as a linear form in the ten parameters.
        vertex_numerator = [
            [
                sum(
                    inverse_numerator[i][j]
                    * support_coefficients[basis[j]][k]
                    for j in range(DIMENSION)
                )
                for k in range(PARAMETER_COUNT)
            ]
            for i in range(DIMENSION)
        ]
        for j in range(FACET_COUNT):
            slack = [
                denominator * support_coefficients[j][k]
                - sum(
                    facets[j][i] * vertex_numerator[i][k]
                    for i in range(DIMENSION)
                )
                for k in range(PARAMETER_COUNT)
            ]
            assert min(slack) >= 0, (cone, basis, j, slack)
            assert any(slack) == (j not in basis), "non-simple reference vertex"

        # Nonnegative coefficients make every slack nonnegative throughout
        # the positive orthant. A nonzero slack is strictly positive there,
        # so the active facets remain precisely this four-element basis.
        vertices.append({
            "facets": basis,
            "denominator": denominator,
            "inverse_numerator": inverse_numerator,
            "vertex_numerator": vertex_numerator,
        })

    assert len(vertices) == EXPECTED_VERTEX_COUNT

    # All reference bases were enumerated, and every retained vertex
    # stays simple and feasible throughout the positive orthant.
    # The corresponding normal cones are fixed by the facet normals. Their
    # coverage at the reference point therefore persists for all positive
    # parameters. Section 2.2 gives this normal-cone argument explicitly.
    out = {
        "cone": cone,
        "parameter_order": ["a"] + edges,
        "generators": generators,
        "parity_classes": parity_classes,
        "facets": facets,
        "support_coefficients": support_coefficients,
        "vertices": vertices,
        "reference": [1] * PARAMETER_COUNT,
        "bases_examined": REFERENCE_BASES_EXAMINED,
        "invertible_bases": invertible_bases,
        "vertex_count": len(vertices),
        "vertex_denominators": dict(Counter(v["denominator"] for v in vertices)),
        "all_generator_slacks_nonnegative": True,
        "seconds": time.time() - start,
    }
    Path(__file__).with_name(f"c{cone}-geometry.json").write_text(
        json.dumps(out, indent=2) + "\n"
    )
    summary_fields = [
        "cone",
        "bases_examined",
        "invertible_bases",
        "vertex_count",
        "vertex_denominators",
        "all_generator_slacks_nonnegative",
        "seconds",
    ]
    print(json.dumps({key: out[key] for key in summary_fields}, indent=2), flush=True)


if __name__ == "__main__":
    for cone in [2, 3]:
        run(cone)
