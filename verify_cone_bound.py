"""Derivative identity and numerical bounds for circular cones.

Run with Python 3; only the standard library is used. The derivative identity
is checked with integers; the eight-dimensional bound uses fractions.Fraction.
The final table gives approximate values using floating-point arithmetic.
"""

from fractions import Fraction as F
from math import cos, gamma, pi, sin


def arctan_partial(x, n):
    """Taylor polynomial U_n(x), evaluated as a rational number."""
    return sum(((-1) ** j * x ** (2 * j + 1) / (2 * j + 1)
                for j in range(n + 1)), F(0))


def verify_concavity_identity():
    """Verify the all-dimensional derivative numerator by interpolation.

    After multiplication by 2(d+1)^2 the claimed identity is polynomial
    of degree at most 4 in d and at most 2 in s.  Equality on the 5 x 3
    grid therefore proves the identity for all d and s.
    """
    for d in range(5):
        for s in range(3):
            numerator = (
                -2 * (d - 1) * (1 + s) * (d + 1 + (d - 1) * s)
                + ((d - 1) * (d + 1) - (d - 1) * s)
                * (d * (d + 1 + (d - 1) * s)
                   - (d + 2) * (d - 1) * (1 + s))
            )
            assert numerator == -2 * d * (d - 1) * (d + 2) * s
    print("All-dimensional cone-concavity derivative identity: PASS")


def verify_eight_dimensional_bound():
    """Verify a numerical consequence of the facet bound in dimension eight."""
    # Machin's identity: pi = 16 atan(1/5) - 4 atan(1/239).
    # Even Taylor truncations are upper bounds, odd ones lower bounds.
    pi_upper = (16 * arctan_partial(F(1, 5), 14)
                - 4 * arctan_partial(F(1, 239), 3))
    r = F(31324847, 50000000)
    assert 0 < r < 1 < 3
    integral_lower = (F(5, 16) * arctan_partial(r, 35)
                      - r * (33 * r**4 + 40 * r**2 + 15)
                      / (48 * (1 + r**2)**3))
    angle_margin = integral_lower - pi_upper / 1632
    assert angle_margin > 0
    lower_fourth_power = (7 * (1 + F(7, 9) * r**2)**4
                          / (680000 * pi_upper**3 * r**7))
    target = F(7101976, 10**8)
    moment_margin = lower_fourth_power - target**4
    assert moment_margin > 0
    print("Upper bracket for the solid-angle radius: PASS")
    print("Fourth-power comparison with 0.07101976: PASS")
    print("Every eight-dimensional lattice has G(L) > 0.07101976.")
    print("Positive rational comparison margins (shown approximately):")
    print(f"  solid-angle margin: {float(angle_margin):.12e}")
    print(f"  fourth-power margin: {float(moment_margin):.12e}")


def sine_power_integral(n, theta):
    """Integral of sin(t)^n on [0, theta], by the elementary recurrence."""
    if n == 0:
        return theta
    if n == 1:
        return 1 - cos(theta)
    return ((n - 1) * sine_power_integral(n - 2, theta)
            - sin(theta)**(n - 1) * cos(theta)) / n


def numerical_bound(d):
    """Evaluate the facet bound using the cone half-angle."""
    facets = 2 * (2**d - 1)
    sphere_area = 2 * pi**(d / 2) / gamma(d / 2)
    lower_sphere_area = 2 * pi**((d - 1) / 2) / gamma((d - 1) / 2)
    target = sphere_area / (facets * lower_sphere_area)
    left, right = 0.0, pi / 2
    for _ in range(70):
        theta = (left + right) / 2
        if sine_power_integral(d - 2, theta) < target:
            left = theta
        else:
            right = theta
    theta = (left + right) / 2
    # The cone has slant height one, height h, and base radius q.
    h, q = cos(theta), sin(theta)
    ball_volume = pi**((d - 1) / 2) / gamma((d + 1) / 2)
    volume = ball_volume * h * q**(d - 1) / d
    cone_moment = ((h*h + F(d - 1, d + 1) * q*q)
                   / ((d + 2) * volume**(2 / d)))
    return facets**(-2 / d) * cone_moment


def verify():
    verify_concavity_identity()
    verify_eight_dimensional_bound()
    print("Approximate values of the facet bound (floating point):")
    for d in (2, 3, 4, 8):
        print(f"  d={d}: {numerical_bound(d):.12f}")
    hexagonal = 5 / (36 * 3**0.5)
    assert abs(numerical_bound(2) - hexagonal) < 1e-15
    print("Dimension-two normalization agrees with 5/(36 sqrt(3)): PASS")


if __name__ == "__main__":
    verify()
