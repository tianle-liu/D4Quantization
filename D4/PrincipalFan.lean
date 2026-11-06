import D4.PrincipalSimplexHull
import D4.PrincipalTiling

/-! Affine separators for iterated fans. Their hypotheses are finite vertex
inequalities; they do not assume a triangulation or a moment identity. -/
noncomputable section
open Matrix MeasureTheory Set
namespace D4.Principal
open Analytic

structure AffineSlack where
  normal : Vec
  offset : ℝ

namespace AffineSlack

def eval (s : AffineSlack) (x : Vec) : ℝ := s.offset - dotProduct s.normal x

/-- Eliminate the value at an apex by an affine linear combination. -/
def fan (s t : AffineSlack) (p : Vec) : AffineSlack where
  normal := t.eval p • s.normal - s.eval p • t.normal
  offset := t.eval p * s.offset - s.eval p * t.offset

theorem eval_fan (s t : AffineSlack) (p x : Vec) :
    (s.fan t p).eval x = t.eval p * s.eval x - s.eval p * t.eval x := by
  simp only [fan, eval, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  ring

@[simp] theorem eval_fan_apex (s t : AffineSlack) (p : Vec) :
    (s.fan t p).eval p = 0 := by rw [eval_fan]; ring

theorem eval_fan_on_zero (s t : AffineSlack) (p x : Vec) (hx : t.eval x = 0) :
    (s.fan t p).eval x = t.eval p * s.eval x := by simp only [eval_fan, hx, mul_zero, sub_zero]

theorem eval_fan_common_zero (s t : AffineSlack) (p x : Vec)
    (hs : s.eval x = 0) (ht : t.eval x = 0) : (s.fan t p).eval x = 0 := by
  simp only [eval_fan, hs, ht, mul_zero, sub_self]

theorem eval_fan_nonpos (s t : AffineSlack) (p x : Vec)
    (hp : 0 ≤ s.eval p) (hs : s.eval x = 0) (ht : 0 ≤ t.eval x) :
    (s.fan t p).eval x ≤ 0 := by
  rw [eval_fan, hs, mul_zero, zero_sub]
  exact neg_nonpos.mpr (mul_nonneg hp ht)

theorem eval_fan_nonneg (s t : AffineSlack) (p x : Vec)
    (hp : 0 ≤ t.eval p) (hs : 0 ≤ s.eval x) (ht : t.eval x = 0) :
    0 ≤ (s.fan t p).eval x := by
  rw [eval_fan_on_zero _ _ _ _ ht]
  exact mul_nonneg hp hs

theorem eval_fan_pos (s t : AffineSlack) (p x : Vec)
    (hp : 0 < t.eval p) (hs : 0 < s.eval x) (ht : t.eval x = 0) :
    0 < (s.fan t p).eval x := by
  rw [eval_fan_on_zero _ _ _ _ ht]
  exact mul_pos hp hs

theorem eval_affine_combination (s : AffineSlack) (x y : Vec) {a b : ℝ} (hab : a + b = 1) :
    s.eval (a • x + b • y) = a * s.eval x + b * s.eval y := by
  simp only [eval, dotProduct_add, dotProduct_smul, smul_eq_mul]
  nlinarith [congrArg (fun z => z * s.offset) hab]

theorem convex_nonneg (s : AffineSlack) : Convex ℝ {x | 0 ≤ s.eval x} := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ s.eval (a • x + b • y)
  rw [eval_affine_combination _ _ _ hab]
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

theorem convex_nonpos (s : AffineSlack) : Convex ℝ {x | s.eval x ≤ 0} := by
  intro x hx y hy a b ha hb hab
  change s.eval (a • x + b • y) ≤ 0
  rw [eval_affine_combination _ _ _ hab]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx) (mul_nonpos_of_nonneg_of_nonpos hb hy)

theorem normal_ne_zero_of_separates (s : AffineSlack) (p x : Vec)
    (hp : s.eval p = 0) (hx : 0 < s.eval x) : s.normal ≠ 0 := by
  intro hn
  simp only [eval, hn, zero_dotProduct, sub_zero] at hp hx
  linarith

theorem normal_ne_zero_of_eval_ne (s : AffineSlack) (p x : Vec)
    (hp : s.eval p = 0) (hx : s.eval x ≠ 0) : s.normal ≠ 0 := by
  intro hn
  simp only [eval, hn, zero_dotProduct, sub_zero] at hp hx
  exact hx hp

theorem nonneg_on_simplex (s : AffineSlack) (v : Fin 5 → Vec)
    (hv : ∀ i, 0 ≤ s.eval (v i)) {x : Vec} (hx : x ∈ vertexSimplex v) :
    0 ≤ s.eval x :=
  vertexSimplex_subset_of_vertices s.convex_nonneg v hv hx

theorem nonpos_on_simplex (s : AffineSlack) (v : Fin 5 → Vec)
    (hv : ∀ i, s.eval (v i) ≤ 0) {x : Vec} (hx : x ∈ vertexSimplex v) :
    s.eval x ≤ 0 :=
  vertexSimplex_subset_of_vertices s.convex_nonpos v hv hx

theorem fan_preserves_nonneg (s t : AffineSlack) (p : Vec) (v : Fin 5 → Vec)
    (hp : 0 ≤ t.eval p) (hv : ∀ i, v i = p ∨ t.eval (v i) = 0 ∧ 0 ≤ s.eval (v i)) :
    ∀ i, 0 ≤ (s.fan t p).eval (v i) := by
  intro i
  rcases hv i with h | ⟨ht, hs⟩
  · simp only [h, eval_fan_apex, le_refl]
  · exact eval_fan_nonneg s t p _ hp hs ht

theorem fan_preserves_nonpos (s t : AffineSlack) (p : Vec) (v : Fin 5 → Vec)
    (hp : 0 ≤ t.eval p) (hv : ∀ i, v i = p ∨ t.eval (v i) = 0 ∧ s.eval (v i) ≤ 0) :
    ∀ i, (s.fan t p).eval (v i) ≤ 0 := by
  intro i
  rcases hv i with h | ⟨ht, hs⟩
  · simp only [h, eval_fan_apex, le_refl]
  · rw [eval_fan_on_zero _ _ _ _ ht]
    exact mul_nonpos_of_nonneg_of_nonpos hp hs

theorem fan_normal_ne_zero (s t : AffineSlack) (p x : Vec)
    (hp : 0 < t.eval p) (hs : 0 < s.eval x) (ht : t.eval x = 0) :
    (s.fan t p).normal ≠ 0 :=
  normal_ne_zero_of_separates _ p x (eval_fan_apex s t p) (eval_fan_pos s t p x hp hs ht)

/-- A separating affine functional turns finite vertex checks into a
Lebesgue-null intersection of the genuine simplices. -/
theorem simplex_inter_volume (s : AffineSlack) (v w : Fin 5 → Vec)
    (hn : s.normal ≠ 0) (hv : ∀ i, s.eval (v i) ≤ 0)
    (hw : ∀ i, 0 ≤ s.eval (w i)) :
    volume (vertexSimplex v ∩ vertexSimplex w) = 0 := by
  apply measure_mono_null (t := (affineHyperplane s.normal s.offset : Set Vec)) ?_
    (affineHyperplane_volume hn s.offset)
  intro x hx
  have hle := nonpos_on_simplex s v hv hx.1
  have hge := nonneg_on_simplex s w hw hx.2
  change dotProduct s.normal x = s.offset
  dsimp [eval] at hle hge
  linarith

end AffineSlack
end D4.Principal
