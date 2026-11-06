import D4.PrincipalMomentTransform

/-! The dual-coordinate lower envelope and the actual integral over a moving
period parallelepiped, with its precise normalization. -/
noncomputable section
namespace D4.Analytic
open Matrix MeasureTheory Set Principal

def dualMap (Q : Gram) (x : Vec) : Vec := ((2:ℝ) • Q) *ᵥ x
def dualInverse (Q : Gram) (r : Vec) : Vec := ((2:ℝ) • Q)⁻¹ *ᵥ r
def dualSiteCost (Q : Gram) (r : Vec) (z : IntVec) : ℝ :=
  quadratic Q (castVec z)-dotProduct (castVec z) r
def dualNearest (Q : Gram) (r : Vec) : ℝ := nearest Q (dualInverse Q r)
def dualPeriod (Q : Gram) (c : Vec) : Set Vec :=
  (fun x => dualMap Q (c+x)) '' unitCube

theorem dualMatrix_det (Q : Gram) : ((2:ℝ) • Q).det=16*Q.det := by
  rw [Matrix.det_smul]
  norm_num

theorem dualMatrix_det_ne_zero {Q : Gram} (hQ : Q.PosDef) :
    ((2:ℝ) • Q).det ≠ 0 := by
  rw [dualMatrix_det]
  exact mul_ne_zero (by norm_num) hQ.det_pos.ne'

@[simp] theorem dualInverse_dualMap {Q : Gram} (hQ : Q.PosDef) (x : Vec) :
    dualInverse Q (dualMap Q x)=x := by
  rw [dualInverse, dualMap, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (dualMatrix_det_ne_zero hQ)), Matrix.one_mulVec]

@[simp] theorem dualMap_dualInverse {Q : Gram} (hQ : Q.PosDef) (r : Vec) :
    dualMap Q (dualInverse Q r)=r := by
  rw [dualInverse, dualMap, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (dualMatrix_det_ne_zero hQ)), Matrix.one_mulVec]

theorem quadratic_eq_dualSiteCost {Q : Gram} (hQ : Q.IsHermitian)
    (x : Vec) (z : IntVec) :
    quadratic Q (x-castVec z)=quadratic Q x+dualSiteCost Q (dualMap Q x) z := by
  rw [quadratic_sub_vec hQ]
  unfold dualSiteCost dualMap
  rw [Matrix.smul_mulVec_assoc, dotProduct_smul, quadratic_pair_symmetric hQ]
  simp only [smul_eq_mul]
  ring

theorem dual_lower_envelope_at_image {Q : Gram} (hQ : Q.PosDef) (x : Vec) :
    (⨅ z : IntVec, dualSiteCost Q (dualMap Q x) z)=nearest Q x-quadratic Q x := by
  have hb (z : IntVec) : nearest Q x-quadratic Q x ≤ dualSiteCost Q (dualMap Q x) z := by
    have hh := nearest_le hQ.posSemidef x z
    rw [quadratic_eq_dualSiteCost hQ.1] at hh
    linarith
  have hbelow : BddBelow (Set.range (dualSiteCost Q (dualMap Q x))) :=
    ⟨nearest Q x-quadratic Q x, by rintro _ ⟨z,rfl⟩; exact hb z⟩
  obtain ⟨z,hz⟩ := nearest_attained hQ x
  rw [quadratic_eq_dualSiteCost hQ.1] at hz
  apply le_antisymm
  · have hh := ciInf_le hbelow z
    linarith
  · exact le_ciInf hb

theorem dualNearest_lower_envelope {Q : Gram} (hQ : Q.PosDef) (r : Vec) :
    dualNearest Q r=quadratic Q⁻¹ r/4 + ⨅ z : IntVec, dualSiteCost Q r z := by
  have he := dual_lower_envelope_at_image hQ (dualInverse Q r)
  rw [dualMap_dualInverse hQ] at he
  have hq := quadratic_inverse_dual hQ (dualInverse Q r)
  change quadratic Q⁻¹ (dualMap Q (dualInverse Q r)) = _ at hq
  rw [dualMap_dualInverse hQ] at hq
  unfold dualNearest
  rw [he]
  linarith

theorem affineImage_integral (B : Gram) (hB : B.det ≠ 0) (c : Vec)
    (S : Set Vec) (f : Vec → ℝ) :
    (∫ y in (fun x => c+B*ᵥx) '' S, f y)=
      |B.det| * ∫ x in S, f (c+B*ᵥx) := by
  have h := setIntegral_map_equiv (μ := (volume : Measure Vec))
    (affineMeasurableEquiv B hB c) f ((fun x => c+B*ᵥx) '' S)
  change (∫ y in (fun x => c+B*ᵥx) '' S, f y ∂Measure.map (fun x => c+B*ᵥx) volume)=
    (∫ x in (fun x => c+B*ᵥx) ⁻¹' ((fun x => c+B*ᵥx) '' S), f (c+B*ᵥx)) at h
  have hp : (fun x => c+B*ᵥx) ⁻¹' ((fun x => c+B*ᵥx) '' S)=S :=
    (affineMeasurableEquiv B hB c).injective.preimage_image S
  rw [map_affine_volume B hB c, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _)), smul_eq_mul, hp] at h
  calc
    _ = |B.det| * (|B.det|⁻¹ * (∫ y in (fun x => c+B*ᵥx) '' S, f y)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hB), one_mul]
    _ = _ := by rw [h]

theorem nearest_shifted_cube_integral (Q : Gram) (c : Vec) :
    (∫ x in unitCube, nearest Q (c+x))=moment Q := by
  apply integral_nearest_comp_equiv Q (MeasurableEquiv.addLeft c)
    (measurePreserving_add_left volume c) (Equiv.refl IntVec)
  intro z x
  change c+(castVec z+x)=castVec z+(c+x)
  abel

theorem dualPeriod_integral {Q : Gram} (hQ : Q.PosDef) (c : Vec) :
    (15/4:ℝ) * (∫ r in dualPeriod Q c, dualNearest Q r)=60*Q.det*moment Q := by
  have hP : dualPeriod Q c=(fun x => dualMap Q c+((2:ℝ) • Q)*ᵥx) '' unitCube := by
    unfold dualPeriod dualMap
    simp only [Matrix.mulVec_add]
  rw [hP, affineImage_integral _ (dualMatrix_det_ne_zero hQ)]
  have hf (x : Vec) : dualNearest Q (dualMap Q c+((2:ℝ) • Q)*ᵥx)=nearest Q (c+x) := by
    change nearest Q (dualInverse Q (((2:ℝ) • Q)*ᵥc+((2:ℝ) • Q)*ᵥx))=_
    rw [← Matrix.mulVec_add]
    exact congrArg (nearest Q) (dualInverse_dualMap hQ (c+x))
  simp_rw [hf]
  rw [nearest_shifted_cube_integral, dualMatrix_det, abs_of_pos (mul_pos (by norm_num) hQ.det_pos)]
  ring

end D4.Analytic
