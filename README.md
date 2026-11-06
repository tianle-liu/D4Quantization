# Optimality of the D4 lattice quantizer

Lean 4 formalization of [arXiv:2611.00100v2](https://arxiv.org/abs/2611.00100v2).

The main statements concern actual Euclidean Voronoi cells and their Lebesgue
second moments. The four-dimensional theorem includes the characterization of
equality by similarities of D4. The dimension-dependent lower bound applies to
arbitrary discrete full-rank lattices in dimension at least two.

The project also formalizes the classification of the three secondary domains,
their closed cones and moment formulas, the polynomial inequalities, and the
auxiliary geometric and graph-theoretic statements. The outside integrals at
both cone boundaries are jointly analytic in the tangential and transverse
parameters. The quantization applications in this version are included;
historical claims and descriptions of external applications are outside the
mathematical scope.

The proofs use mathlib and Lean's standard foundational axioms: propositional
extensionality, classical choice, and quotient soundness. No additional
mathematical axioms or admitted proofs are used. Finite certificates are checked
by the ordinary Lean kernel.

## Build

The Lean version and mathlib revision are fixed by `lean-toolchain` and
`lake-manifest.json`. With Lean installed through elan:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build
```

The finite certificate files are part of the proof source and can require
substantial time and memory to compile.

## Main declarations

- `D4.theoremA`: the Gram-matrix form of the four-dimensional optimality theorem.
- `D4.Euclidean.geometricTheoremA`: optimality and equality for actual lattices.
- `D4.FacetGeometry.theoremB`: the dimension-dependent lower bound.
- `D4.FacetGeometry.theoremB_actual_facets`: the bound with the actual facet count.
- `D4.geometricMomentIdentities`: the actual moment formulas on all three closed cones.
- `D4.Delaunay.exactly_three_inclusion_maximal_secondary_domains`: the three secondary domains up to integral basis change.
- `D4.C23Local.path2_outside_joint_analytic` and `path3_outside_joint_analytic`: joint analyticity of the actual outside integrals at the two walls.
- `D4.FacetGeometry.subtractive_dither_independent`: the uniform and independent dither error.
- `D4.Blocks.four_dimensional_block_equality`: the equality case for orthogonal D4 blocks.

## Earlier version

The Python checks and computational data for the first version of the paper
are preserved at the [v1 tag](https://github.com/tianle-liu/D4Quantization/tree/v1).
They are not required by the second version or by this Lean formalization.

## Citation and license

Please cite Tianle Liu, *Optimality of the D4 Lattice Quantizer*,
[arXiv:2611.00100v2](https://arxiv.org/abs/2611.00100v2), 2026.
Citation metadata is provided in [CITATION.cff](CITATION.cff).

The proof source and repository documentation are distributed under the
[MIT License](LICENSE). The paper is distributed separately and is not covered
by this license.
