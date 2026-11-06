import D4.CertificateC1B1
import D4.CertificateC1B2
import D4.CertificateC2B1
import D4.CertificateC2B2
import D4.CertificateC3B1
import D4.CertificateC3B2

/-!
# The six inequalities for the supplied expanded polynomials

These theorems expose the coefficients and normalizations of arXiv v2.
They concern the explicitly supplied polynomial functions. In particular,
they do NOT assert that a polynomial is a Lebesgue moment integral.
-/
noncomputable section
namespace D4.CertifiedPolynomials
open D4.Certificate D4.CertificateMoments

def D1 (x : Nat → ℝ) : ℝ := eval x determinantC1
def D2 (x : Nat → ℝ) : ℝ := eval x determinantC2
def D3 (x : Nat → ℝ) : ℝ := eval x determinantC3
def S (x : Nat → ℝ) : ℝ := eval x momentC1
def N2 (x : Nat → ℝ) : ℝ := eval x momentC2
def N3 (x : Nat → ℝ) : ℝ := eval x momentC3
def L (x : Nat → ℝ) : ℝ := eval x parameterC1
def t2 (x : Nat → ℝ) : ℝ := eval x parameterC2 / 4
def t3 (x : Nat → ℝ) : ℝ := eval x parameterC3 / 4

theorem c1_base (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) :
    D1 x * L x ≤ S x := by
  have h := base_nonnegative_c1 x hx
  rw [← base_identity_C1, ← determinant_product_C1] at h
  simp only [eval_mergeAdd, eval_scale, eval_mul, Int.cast_neg, Int.cast_one, Int.cast_ofNat] at h
  dsimp [D1, L, S]
  linarith only [h]

theorem c2_base (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) :
    20 * D2 x * t2 x ≤ N2 x := by
  have h := base_nonnegative_c2 x hx
  rw [← base_identity_C2, ← determinant_product_C2] at h
  simp only [eval_mergeAdd, eval_scale, eval_mul, Int.cast_neg, Int.cast_ofNat] at h
  dsimp [D2, t2, N2]
  linarith only [h]

theorem c3_base (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) :
    20 * D3 x * t3 x ≤ N3 x := by
  have h := base_nonnegative_c3 x hx
  rw [← base_identity_C3, ← determinant_product_C3] at h
  simp only [eval_mergeAdd, eval_scale, eval_mul, Int.cast_neg, Int.cast_ofNat] at h
  dsimp [D3, t3, N3]
  linarith only [h]

theorem c1_middle (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (4/3 : ℝ) * D1 x * L x - (7/4000 : ℝ) * L x ^ 5 ≤ S x := by
  have h := D4.CertificateC1B1.target_nonnegative x hx
  rw [← D4.CertificateC1B1.target_formula] at h
  simp only [eval_sumFast, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, eval_scale, eval_mul, eval_power, Int.cast_neg,
    Int.cast_ofNat] at h
  dsimp [D1, L, S]
  linarith only [h]

theorem c1_high (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (3/2 : ℝ) * D1 x * L x - (33/10000 : ℝ) * L x ^ 5 ≤ S x := by
  have h := D4.CertificateC1B2.target_nonnegative x hx
  rw [← D4.CertificateC1B2.target_formula] at h
  simp only [eval_sumFast, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, eval_scale, eval_mul, eval_power, Int.cast_neg,
    Int.cast_ofNat] at h
  dsimp [D1, L, S]
  linarith only [h]

theorem c2_middle (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (82/3 : ℝ) * D2 x * t2 x - (41/4 : ℝ) * t2 x ^ 5 ≤ N2 x := by
  have h := D4.CertificateC2B1.target_nonnegative x hx
  rw [← D4.CertificateC2B1.target_formula] at h
  simp only [eval_sumFast, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, eval_scale, eval_mul, eval_power, Int.cast_neg,
    Int.cast_ofNat] at h
  dsimp [D2, t2, N2]
  nlinarith only [h]

theorem c2_high (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) :
    31 * D2 x * t2 x - 20 * t2 x ^ 5 ≤ N2 x := by
  have h := D4.CertificateC2B2.target_nonnegative x hx
  rw [← D4.CertificateC2B2.target_formula] at h
  simp only [eval_sumFast, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, eval_scale, eval_mul, eval_power, Int.cast_neg,
    Int.cast_ofNat] at h
  dsimp [D2, t2, N2]
  nlinarith only [h]

theorem c3_middle (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (82/3 : ℝ) * D3 x * t3 x - (41/4 : ℝ) * t3 x ^ 5 ≤ N3 x := by
  have h := D4.CertificateC3B1.target_nonnegative x hx
  rw [← D4.CertificateC3B1.target_formula] at h
  simp only [eval_sumFast, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, eval_scale, eval_mul, eval_power, Int.cast_neg,
    Int.cast_ofNat] at h
  dsimp [D3, t3, N3]
  nlinarith only [h]

theorem c3_high (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) :
    31 * D3 x * t3 x - 20 * t3 x ^ 5 ≤ N3 x := by
  have h := D4.CertificateC3B2.target_nonnegative x hx
  rw [← D4.CertificateC3B2.target_formula] at h
  simp only [eval_sumFast, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, eval_scale, eval_mul, eval_power, Int.cast_neg,
    Int.cast_ofNat] at h
  dsimp [D3, t3, N3]
  nlinarith only [h]

end D4.CertifiedPolynomials
