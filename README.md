# D4 quantization: verification

Programs and polynomial identities for the proof that D4 is the optimal
four-dimensional lattice quantizer. The repository also includes checks
for the circular-cone derivative identity and an eight-dimensional
consequence of the Voronoi-facet bound.

## Reading and running the checks

The [review guide](REVIEWING.md) connects the mathematical statements to the
programs and works through one coefficient of a polynomial identity.
Start with that example, then run the full verification:

```sh
python3 -B inspect_certificate.py
python3 -B verify_d4_global.py
python3 -B verify_cone_bound.py
```

Python 3.9 or later and its standard library are sufficient. Run from this
directory with assertions enabled: do not use `-O` or `-OO`. The D4 program
reconstructs the geometry and moments in a temporary directory.

The D4 verification has five stages: geometric reconstruction, comparison
with the supplied moment polynomials, six polynomial identities, a second
integration by boundary triangulation, and the final scalar inequalities
and identification of D4. Its last line is
`ALL D4 GLOBAL PROOF CHECKS PASSED.` A failed assertion or a nonzero exit
status indicates failure.

## Inspecting an identity

```sh
python3 -B inspect_certificate.py --cone 2 --proof 2
python3 -B inspect_certificate.py --cone 3 --proof 1 --all
```

The inspection program expands one weighted square and checks one coefficient
of the selected identity. `--all` displays every weighted square and remainder
term. The full verification checks all coefficients and reconstructs the
geometric inputs.

## Relation to the proof

The programs check the moment polynomials, six polynomial identities,
and finite comparisons used in the proof. The accompanying manuscript gives
the three-cone reduction, the integration formulas, the scalar inequalities,
and the equality argument. The [review guide](REVIEWING.md) explains this
division and identifies the functions and data used in each computation.

The repository contains the verification programs and data. The manuscript
is distributed separately.

## Citation

If you use this code or these certificates in research that leads to a
publication, please cite the accompanying paper:

Tianle Liu. *The optimal four-dimensional lattice quantizer and bounds from
Voronoi facets*. Preprint, 2026.

Citation metadata is provided in [CITATION.cff](CITATION.cff). This citation
request is not an additional condition of the MIT License.

## License

The verification code, certificates, and accompanying repository documentation
are distributed under the [MIT License](LICENSE). The manuscript is distributed
separately and is not covered by this license.
