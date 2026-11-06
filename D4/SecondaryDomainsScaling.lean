import D4.SecondaryDomainsType

/-! Positive rescaling preserves the complete actual Delaunay type. -/
noncomputable section
namespace D4.Delaunay
open Analytic Principal Matrix MeasureTheory Set

def planeScale (a : ℝ) (p : AffineSlack) : AffineSlack :=
  ⟨a • p.normal, a*p.offset⟩

theorem planeScale_eval (a : ℝ) (p : AffineSlack) (x : Vec) :
    (planeScale a p).eval x = a*p.eval x := by
  simp only [planeScale, AffineSlack.eval, smul_dotProduct, smul_eq_mul, mul_sub]

theorem tightPlane_pos_smul {Q : Gram} {F : Finset IntVec} {p : AffineSlack}
    {a : ℝ} (ha : 0 < a) (hp : TightPlane Q F p) :
    TightPlane (a • Q) F (planeScale a p) := by
  constructor
  · intro n
    rw [planeScale_eval, quadratic_smul]
    exact mul_le_mul_of_nonneg_left (hp.1 n) ha.le
  · intro n
    rw [planeScale_eval, quadratic_smul]
    constructor
    · intro h
      exact (hp.2 n).mp (mul_left_cancel₀ ha.ne' h)
    · intro h
      rw [(hp.2 n).mpr h]

theorem delaunayType_pos_smul (Q : Gram) {a : ℝ} (ha : 0 < a) :
    delaunayType (a • Q) = delaunayType Q := by
  ext F
  constructor
  · rintro ⟨⟨p,hp⟩,hv⟩
    have hh := tightPlane_pos_smul (inv_pos.mpr ha) hp
    have hmat : a⁻¹ • (a • Q) = Q := by
      rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
    rw [hmat] at hh
    exact ⟨⟨_,hh⟩,hv⟩
  · rintro ⟨⟨p,hp⟩,hv⟩
    exact ⟨⟨_,tightPlane_pos_smul ha hp⟩,hv⟩

end D4.Delaunay
