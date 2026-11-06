import D4.AreaTriangleHull
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Supporting-line data imply nondegeneracy and null intersections of
polygon fan triangles. -/
noncomputable section
namespace D4.AreaEnvelope
open Set Matrix MeasureTheory

structure PlaneSlack where
  normal : Plane
  offset : ℝ

namespace PlaneSlack

def eval (s : PlaneSlack) (x : Plane) : ℝ := s.offset-dotProduct s.normal x

def hyperplane (s : PlaneSlack) : AffineSubspace ℝ Plane where
  carrier := {x | dotProduct s.normal x=s.offset}
  smul_vsub_vadd_mem c x y z hx hy hz := by
    change dotProduct s.normal (c • (x-y)+z)=s.offset
    rw [dotProduct_add,dotProduct_smul,dotProduct_sub,hx,hy,hz]
    simp

theorem hyperplane_volume (s : PlaneSlack) (hn : s.normal≠0) :
    volume (s.hyperplane : Set Plane)=0 := by
  apply Measure.addHaar_affineSubspace volume
  intro he
  have h0 : dotProduct s.normal (0:Plane)=s.offset := by
    have h : (0:Plane) ∈ s.hyperplane := by rw [he]; trivial
    exact h
  have hs : dotProduct s.normal s.normal=s.offset := by
    have h : s.normal ∈ s.hyperplane := by rw [he]; trivial
    exact h
  have hz : dotProduct s.normal s.normal=0 := by
    simpa only [dotProduct_zero] using hs.trans h0.symm
  exact hn (dotProduct_self_eq_zero.mp hz)

theorem eval_combination (s : PlaneSlack) (x y : Plane) {a b : ℝ} (h : a+b=1) :
    s.eval (a • x+b • y)=a*s.eval x+b*s.eval y := by
  simp only [eval,dotProduct_add,dotProduct_smul,smul_eq_mul]
  nlinarith [congrArg (fun t => t*s.offset) h]

theorem convex_nonneg (s : PlaneSlack) : Convex ℝ {x | 0 ≤ s.eval x} := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ s.eval (a • x+b • y)
  rw [eval_combination _ _ _ hab]
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

theorem convex_nonpos (s : PlaneSlack) : Convex ℝ {x | s.eval x ≤ 0} := by
  intro x hx y hy a b ha hb hab
  change s.eval (a • x+b • y) ≤ 0
  rw [eval_combination _ _ _ hab]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx)
    (mul_nonpos_of_nonneg_of_nonpos hb hy)

theorem triangle_inter_null (s : PlaneSlack) (a b c d : Plane)
    (hn : s.normal≠0)
    (hz : s.eval 0=0) (ha : 0 ≤ s.eval a) (hb : 0 ≤ s.eval b)
    (hc : s.eval c≤0) (hd : s.eval d≤0) :
    volume (affineTriangle (triangleMatrix a b) 0 ∩
      affineTriangle (triangleMatrix c d) 0)=0 := by
  apply measure_mono_null (t := (s.hyperplane:Set Plane)) ?_ (s.hyperplane_volume hn)
  intro x hx
  rw [affineTriangle_eq_convexHull] at hx
  have h1 : 0 ≤ s.eval x := by
    apply convexHull_min (s := ({0,a,b} : Set Plane)) ?_ s.convex_nonneg hx.1
    intro y hy
    simp only [mem_insert_iff,mem_singleton_iff] at hy
    rcases hy with h | h | h
    · rw [h]; exact hz.ge
    · rw [h]; exact ha
    · rw [h]; exact hb
  have h2 : s.eval x≤0 := by
    apply convexHull_min (s := ({0,c,d} : Set Plane)) ?_ s.convex_nonpos
      (by simpa only [affineTriangle_eq_convexHull] using hx.2)
    intro y hy
    simp only [mem_insert_iff,mem_singleton_iff] at hy
    rcases hy with h | h | h
    · rw [h]; exact hz.le
    · rw [h]; exact hc
    · rw [h]; exact hd
  change dotProduct s.normal x=s.offset
  dsimp [eval] at h1 h2
  linarith

theorem triangle_det_ne_zero (s : PlaneSlack) (a b : Plane)
    (hp : 0<s.offset) (ha : s.eval a=0) (hb : s.eval b=0) (hab : a≠b) :
    (triangleMatrix a b).det≠0 := by
  intro hd
  apply hab
  have ha' : s.normal 0*a 0+s.normal 1*a 1=s.offset := by
    simpa [eval,dotProduct,Fin.sum_univ_succ] using (sub_eq_zero.mp ha).symm
  have hb' : s.normal 0*b 0+s.normal 1*b 1=s.offset := by
    simpa [eval,dotProduct,Fin.sum_univ_succ] using (sub_eq_zero.mp hb).symm
  have hd' : a 0*b 1-a 1*b 0=0 := by
    simpa [triangleMatrix,Matrix.det_fin_two,mul_comm] using hd
  have hh (i : Fin 2) : s.offset*(a i-b i)=0 := by
    fin_cases i
    · change s.offset*(a 0-b 0)=0
      linear_combination (b 0)*ha' - (a 0)*hb' + (s.normal 1)*hd'
    · change s.offset*(a 1-b 1)=0
      linear_combination (b 1)*ha' - (a 1)*hb' - (s.normal 0)*hd'
  ext i
  exact sub_eq_zero.mp ((mul_eq_zero.mp (hh i)).resolve_left hp.ne')

end PlaneSlack
end D4.AreaEnvelope
