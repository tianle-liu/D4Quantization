# Guide to reviewing the computation

This guide describes the computations in Section 2 of the accompanying D4
quantization paper. The table below links each mathematical statement to
its implementation; the worked example explains how to read the polynomial
data.

## 1. Mathematical statements and their checks

Write $D=\det Q$ and let $M(Q)$ be the unnormalized moment in basis
coordinates. The paper uses $S=12DM$ on $C_1$ and $N=60DM$ on $C_2,C_3$.
The normalized second moment is $G(Q)=M(Q)/(4D^{1/4})$.

| Mathematical step | Program and entry point | Finite assertion checked |
| --- | --- | --- |
| Proposition 2.2: principal-cone moment | [`reconstruct_c1.py:main`](d4-certificate/reconstruct_c1.py); [`verify_c1_simplified.py:reconstruct`](d4-certificate/verify_c1_simplified.py) | Integrate the coherent zonotope tiling; compare with the expression for $S$ in terms of spanning trees and unicyclic graphs. |
| Proposition 2.3: other two cones | [`reconstruct_c23_geometry.py:run`](d4-certificate/reconstruct_c23_geometry.py); [`reconstruct_c23_moments.py:run`](d4-certificate/reconstruct_c23_moments.py) | Enumerate parity representatives and vertices; check symbolic slacks; integrate; verify volume, exact division, and $N\ge20Dt$. |
| Proposition 2.4: six polynomial identities | [`verify_c1_simplified.py:verify_certificate`](d4-certificate/verify_c1_simplified.py); [`verify_c23_simplified.py:verify_cone`](d4-certificate/verify_c23_simplified.py) | Expand every identity; check all 2,002 coefficients, the degrees, the signs of the weights, and the averaging groups. |
| Second calculation of the moments | [`rebuild_triangulation.py:rebuild`](d4-certificate/rebuild_triangulation.py); comparison in [`verify_d4_global.py:main`](verify_d4_global.py) | Reconstruct facets and vertices without reading JSON; integrate a boundary triangulation; compare complete moment polynomials. |
| Theorem 2.1: final scalar comparisons | [`verify_d4_global.py:scalar_checks`](verify_d4_global.py) | Check determinant and trace constants, rational interval endpoints, and the basis identifying D4. |

Start with the short wrapper
[`verify_d4_global.py`](verify_d4_global.py), then follow the relevant function.
The geometric reconstruction files contain comments matching the integration
formulas and their normalization factors.

The manuscript supplies the three-cone classification, the integration
formulas, the completeness of the vertex descriptions, continuity at
positive-definite boundary forms, the AM--GM bounds, the reduction of scalar
inequalities to endpoint comparisons, and the equality argument. The programs
perform the algebra and finite enumerations used in those arguments.

## 2. The six identities

On $C_1$, variables follow the edges $01,02,03,04,12,13,14,23,24,34$ of $K_5$,
and $L$ is their sum. On $C_2$, the order is
$a,x_{01},x_{02},x_{03},x_{04},x_{13},x_{14},x_{23},x_{24},x_{34}$;
on $C_3$ the last entry is $b$. In both cases
$t=a+\tfrac14\sum_{j=2}^{10}x_j$.

| Cone / proof | Polynomial $P$ | Weighted square entries | Remainder entries |
| --- | --- | ---: | ---: |
| C1 / 1 | $S-\frac{13}{10}DL+\frac{29}{20000}L^5$ | 32 | 35 |
| C1 / 2 | $S-\frac32DL+\frac{163}{50000}L^5$ | 34 | 35 |
| C2 / 1 | $N-\frac{55}{2}Dt+\frac{21}{2}t^5$ | 176 | 225 |
| C2 / 2 | $N-31Dt+20t^5$ | 217 | 222 |
| C3 / 1 | $N-\frac{55}{2}Dt+\frac{21}{2}t^5$ | 71 | 91 |
| C3 / 2 | $N-31Dt+20t^5$ | 88 | 89 |

Every identity has the form

$$
P=\sum_\nu c_\nu\mathrm{Av}_H(x^{w_\nu}p_\nu^2)
  +\sum_\mu r_\mu\mathrm{Av}_H(x^{e_\mu}),
\qquad \mathrm{Av}_H f=\frac1{|H|}\sum_{\sigma\in H}\sigma f.
$$

Here $c_\nu,r_\mu$ are positive rational numbers, the exponents are
nonnegative integers, and the polynomials $p_\nu$ have integer coefficients.
Every summand is nonnegative on the nonnegative orthant, so the identity
proves $P\ge0$ there. Such a decomposition is called a polynomial
nonnegativity certificate.

## 3. A coefficient calculation

Run `python3 -B inspect_certificate.py` while reading this example.
The first term in C1 / 1 is

$$
\frac{6613}{100000}\mathrm{Av}_{S_5}
  \bigl[x_{01}x_{02}x_{03}(x_{01}-x_{02})^2\bigr].
$$

Before averaging, the polynomial inside brackets is

$$
x_{01}^3x_{02}x_{03}-2x_{01}^2x_{02}^2x_{03}
  +x_{01}x_{02}^3x_{03}.
$$

The first and third monomials belong to the same 60-element orbit; the
middle monomial belongs to a different 60-element orbit. The coefficient
sums over these orbits are $2$ and $-2$, respectively. After multiplication
by $6613/100000$ and averaging, each member of the first orbit has
coefficient $6613/3000000$, and each member of the second has coefficient
$-6613/3000000$. The divisor is the orbit size: every monomial occurs
$|H|/|\mathcal O|$ times in the group sum.

For $m=x_{01}^3x_{02}x_{03}$, the sum of coefficients over its orbit is
$173321/100000$ from the 32 weighted squares and $679/100000$ from the
remainder. Averaging gives

$$
[m]P=\frac{173321}{6000000}+\frac{679}{6000000}
     =\frac{29}{1000}.
$$

On the target side, $[m]S=[m]DL=0$ and
$[m]L^5=5!/(3!1!1!)=20$, giving exactly
$\frac{29}{20000}\cdot20=\frac{29}{1000}$.
The inspection program prints the 13 nonzero contributions from weighted
squares; the other 19 are zero. The full verification applies the same
calculation to all 2,002 degree-five monomials in each of the six identities.

## 4. What to check in the verifier

The essential loop has four operations: expand each $x^wp^2$ with
rational arithmetic; sum the coefficients over each monomial orbit;
add the remainder coefficients; divide by the orbit size and compare
with the target coefficient. Iterating over ordered pairs of terms in $p$
supplies the factor two in the cross terms of $p^2$.

The group on C1 is generated directly from vertex permutations of $K_5$.
On C2/C3, the checker generates the groups from the cycles printed in the
paper and compares them with the supplied lists. It checks closure and
invariance of $D,N$ as well. The corresponding numbers of monomial orbits
are 35, 225, and 91.

The C2/C3 checker reads $N$ from a moment file and recomputes $D$.
The full verification in `verify_d4_global.py` also reconstructs the geometry
and moments, compares every supplied moment coefficient with its
reconstruction, and checks the six identities using the reconstructed data.
This reconstruction identifies the polynomial $N$ with $60DM$.

The triangulation calculation constructs the cone generators directly and
uses a different integration formula. Before comparing the two results,
the wrapper aligns the parameter order and normalization: it puts $a$ first
on C2/C3 and compares the triangulation numerator with $5S$ on C1.
Both calculations use Python and the same cone specification.

## 5. Data files and scope

| Files in `d4-certificate/` | Contents and role |
| --- | --- |
| `c*-sos-simplified.json` | Nonnegativity identities. `weight_exponent` encodes $w$; `polynomial` lists exponent/coefficient pairs for $p$; `coefficient` is $c$; `orbit_total` is $r$, before division by the orbit size. |
| `c*-moment.json` | Determinant and moment coefficients, compared with their reconstructions. |
| `c2-geometry.json`, `c3-geometry.json` | Generators, facets, symbolic vertices and supports; regenerated before the complete check uses them. |
| `c2-symmetry.json`, `c3-symmetry.json` | Permutation groups, checked against the generators in the paper. |

For Section 3, `verify_cone_bound.py` checks the polynomial derivative
identity after clearing denominators and the rational comparisons for the
eight-dimensional bound. The polynomial has degree at most four in one
variable and two in the other; equality on a $5\times3$ grid proves the
identity by interpolation. The circular-cone, pyramid, and lattice-bound
arguments are proved in the paper. The program also prints approximate
values in dimensions 2, 3, 4, and 8 for illustration.

The identity and inequality checks use integers or `Fraction`, so these
comparisons use exact arithmetic. The final table uses floating point.
