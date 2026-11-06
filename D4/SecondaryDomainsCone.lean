import D4.SecondaryDomainsCoordinates
import Mathlib.Analysis.Convex.Basic

/-! The displayed secondary domains are genuine convex cones in the space
of Gram matrices. The strict positive orthant is mapped linearly into that
space; membership is preserved in both directions by every positive dilation. -/
noncomputable section
namespace D4.Delaunay
open Analytic Matrix Set

theorem coneForm_add (i : Fin 3) (w v : Fin 10 → ℝ) :
    coneForm i (w+v)=coneForm i w+coneForm i v := by
  fin_cases i
  · change principalForm (w+v)=principalForm w+principalForm v
    simp only [principalForm, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  · change secondaryForm cone2Vectors ((w+v) 0) (fun k => (w+v) k.succ)=
      secondaryForm cone2Vectors (w 0) (fun k => w k.succ)+
      secondaryForm cone2Vectors (v 0) (fun k => v k.succ)
    simp only [secondaryForm, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  · change secondaryForm cone3Vectors ((w+v) 0) (fun k => (w+v) k.succ)=
      secondaryForm cone3Vectors (w 0) (fun k => w k.succ)+
      secondaryForm cone3Vectors (v 0) (fun k => v k.succ)
    simp only [secondaryForm, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel

theorem coneForm_smul (i : Fin 3) (c : ℝ) (w : Fin 10 → ℝ) :
    coneForm i (c • w)=c • coneForm i w := by
  fin_cases i
  · change principalForm (c • w)=c • principalForm w
    simp only [principalForm, Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum]
  · change secondaryForm cone2Vectors ((c • w) 0) (fun k => (c • w) k.succ)=
      c • secondaryForm cone2Vectors (w 0) (fun k => w k.succ)
    simp only [secondaryForm, Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum,
      smul_add]
  · change secondaryForm cone3Vectors ((c • w) 0) (fun k => (c • w) k.succ)=
      c • secondaryForm cone3Vectors (w 0) (fun k => w k.succ)
    simp only [secondaryForm, Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum,
      smul_add]

def positiveFormCone (i : Fin 3) : Set Gram :=
  {Q | ∃ w : Fin 10 → ℝ, (∀ k, 0 < w k) ∧ Q=coneForm i w}

theorem positiveFormCone_convex (i : Fin 3) : Convex ℝ (positiveFormCone i) := by
  rintro Q ⟨w,hw,rfl⟩ R ⟨v,hv,rfl⟩ a b ha hb hab
  refine ⟨a • w+b • v,?_,?_⟩
  · intro k
    change 0 < a*w k+b*v k
    by_cases h : a=0
    · have hb1 : b=1 := by linarith
      simpa only [h,hb1,zero_mul,one_mul,zero_add] using hv k
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (lt_of_le_of_ne ha (Ne.symm h)) (hw k)) (mul_nonneg hb (hv k).le)
  · rw [coneForm_add,coneForm_smul,coneForm_smul]

theorem positiveFormCone_smul (i : Fin 3) {Q : Gram} (hQ : Q ∈ positiveFormCone i)
    {c : ℝ} (hc : 0 < c) : c • Q ∈ positiveFormCone i := by
  obtain ⟨w,hw,rfl⟩ := hQ
  refine ⟨c • w,?_,(coneForm_smul i c w).symm⟩
  intro k
  exact mul_pos hc (hw k)

theorem positiveFormCone_smul_iff (i : Fin 3) (Q : Gram) {c : ℝ} (hc : 0 < c) :
    c • Q ∈ positiveFormCone i ↔ Q ∈ positiveFormCone i := by
  constructor
  · intro h
    have hh := positiveFormCone_smul i h (inv_pos.mpr hc)
    simpa only [smul_smul,inv_mul_cancel₀ hc.ne',one_smul] using hh
  · exact fun h => positiveFormCone_smul i h hc

end D4.Delaunay
