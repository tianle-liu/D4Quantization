import D4.AreaAnalytic

/-! Actual moving triangles and analytic polynomial integrals. -/
noncomputable section
namespace D4.AreaEnvelope
open MeasureTheory Set Matrix

abbrev PlaneMatrix := Matrix (Fin 2) (Fin 2) ℝ

def planeLinearEquiv (B : PlaneMatrix) (hB : B.det ≠ 0) : Plane ≃ₗ[ℝ] Plane :=
  { B.mulVecLin with
    invFun := B⁻¹.mulVec
    left_inv := fun x => by
      change B⁻¹ *ᵥ (B *ᵥ x) = x
      rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB),Matrix.one_mulVec]
    right_inv := fun x => by
      change B *ᵥ (B⁻¹ *ᵥ x) = x
      rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB),Matrix.one_mulVec] }

def planeAffineEquiv (B : PlaneMatrix) (hB : B.det ≠ 0) (c : Plane) : Plane ≃ᵐ Plane :=
  (planeLinearEquiv B hB).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.trans
    (MeasurableEquiv.addLeft c)

@[simp] theorem planeAffineEquiv_apply (B : PlaneMatrix) (hB : B.det ≠ 0) (c x : Plane) :
    planeAffineEquiv B hB c x = c+B*ᵥx := rfl

def affineTriangle (B : PlaneMatrix) (c : Plane) : Set Plane :=
  (fun x => c+B*ᵥx) '' Principal.standardSimplex 2 1

theorem affineTriangle_compact (B : PlaneMatrix) (c : Plane) : IsCompact (affineTriangle B c) :=
  (Principal.standardSimplex_compact 2 1).image (by unfold Matrix.mulVec dotProduct; fun_prop)

theorem map_planeAffine_volume (B : PlaneMatrix) (hB : B.det ≠ 0) (c : Plane) :
    Measure.map (fun x => c+B*ᵥx) volume = ENNReal.ofReal |B.det|⁻¹ • volume := by
  change Measure.map ((fun y : Plane => c+y) ∘ Matrix.toLin' B) volume = _
  have hm : Measurable (Matrix.toLin' B) :=
    (planeLinearEquiv B hB).toContinuousLinearEquiv.continuous.measurable
  rw [← Measure.map_map (show Measurable (fun y : Plane => c+y) from measurable_const.add measurable_id) hm,
    Real.map_matrix_volume_pi_eq_smul_volume_pi hB,Measure.map_smul,
    (measurePreserving_add_left (volume : Measure Plane) c).map_eq,abs_inv]

theorem affineTriangle_integral (B : PlaneMatrix) (hB : B.det ≠ 0) (c : Plane) (f : Plane → ℝ) :
    (∫ y in affineTriangle B c, f y) =
      |B.det| * ∫ x in Principal.standardSimplex 2 1, f (c+B*ᵥx) := by
  have h := setIntegral_map_equiv (μ := (volume : Measure Plane))
    (planeAffineEquiv B hB c) f (affineTriangle B c)
  change (∫ y in affineTriangle B c, f y ∂Measure.map (fun x => c+B*ᵥx) volume) =
    (∫ x in (fun x => c+B*ᵥx) ⁻¹' affineTriangle B c, f (c+B*ᵥx)) at h
  have hp : (fun x => c+B*ᵥx) ⁻¹' affineTriangle B c = Principal.standardSimplex 2 1 :=
    (planeAffineEquiv B hB c).injective.preimage_image (Principal.standardSimplex 2 1)
  rw [map_planeAffine_volume B hB c,Measure.restrict_smul,integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _)),smul_eq_mul,hp] at h
  calc
    _ = |B.det| * (|B.det|⁻¹ * (∫ y in affineTriangle B c, f y)) := by
      rw [← mul_assoc,mul_inv_cancel₀ (abs_ne_zero.mpr hB),one_mul]
    _ = _ := by rw [h]

def affineCompose (a : Fin 3 → ℝ) (B : PlaneMatrix) (c : Plane) : Fin 3 → ℝ :=
  ![a 0+a 1*c 0+a 2*c 1,a 1*B 0 0+a 2*B 1 0,a 1*B 0 1+a 2*B 1 1]

theorem affineCompose_eval (a : Fin 3 → ℝ) (B : PlaneMatrix) (c x : Plane) :
    affineEval (affineCompose a B c) x = affineEval a (c+B*ᵥx) := by
  simp [affineEval_eq,affineCompose,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem analyticAt_affineCompose (a : ℝ → Fin 3 → ℝ) (B : ℝ → PlaneMatrix)
    (c : ℝ → Plane) (t₀ : ℝ)
    (ha : ∀ i, AnalyticAt ℝ (fun t => a t i) t₀)
    (hB : ∀ i j, AnalyticAt ℝ (fun t => B t i j) t₀)
    (hc : ∀ i, AnalyticAt ℝ (fun t => c t i) t₀) (i : Fin 3) :
    AnalyticAt ℝ (fun t => affineCompose (a t) (B t) (c t) i) t₀ := by
  fin_cases i
  · exact ((ha 0).add ((ha 1).mul (hc 0))).add ((ha 2).mul (hc 1))
  · exact ((ha 1).mul (hB 0 0)).add ((ha 2).mul (hB 1 0))
  · exact ((ha 1).mul (hB 0 1)).add ((ha 2).mul (hB 1 1))

theorem analyticAt_plane_det (B : ℝ → PlaneMatrix) (t₀ : ℝ)
    (hB : ∀ i j, AnalyticAt ℝ (fun t => B t i j) t₀) :
    AnalyticAt ℝ (fun t => (B t).det) t₀ := by
  simp_rw [Matrix.det_fin_two]
  exact ((hB 0 0).mul (hB 1 1)).sub ((hB 0 1).mul (hB 1 0))

theorem analyticAt_abs_of_ne_zero (f : ℝ → ℝ) (t₀ : ℝ)
    (hf : AnalyticAt ℝ f t₀) (hn : f t₀ ≠ 0) : AnalyticAt ℝ (fun t => |f t|) t₀ := by
  rcases lt_or_gt_of_ne hn with hn | hn
  · apply hf.neg.congr
    filter_upwards [hf.continuousAt.eventually_lt_const hn] with t ht
    exact (abs_of_neg ht).symm
  · apply hf.congr
    filter_upwards [hf.continuousAt.eventually_const_lt hn] with t ht
    exact (abs_of_pos ht).symm

/-- Analytic vertices and affine coefficients imply analyticity of the
actual polynomial integral over their moving nondegenerate triangle. -/
theorem analyticAt_negativeTriangleIntegral (R : ℝ) (u d : ℝ → Fin 3 → ℝ)
    (B : ℝ → PlaneMatrix) (c : ℝ → Plane) (t₀ : ℝ)
    (hu : ∀ i, AnalyticAt ℝ (fun t => u t i) t₀)
    (hd : ∀ i, AnalyticAt ℝ (fun t => d t i) t₀)
    (hB : ∀ i j, AnalyticAt ℝ (fun t => B t i j) t₀)
    (hc : ∀ i, AnalyticAt ℝ (fun t => c t i) t₀) (hdet : (B t₀).det ≠ 0) :
    AnalyticAt ℝ (fun t => ∫ x in affineTriangle (B t) (c t),
      4*R^2*affineEval (u t) x + squareNegativePolynomial R (t-affineEval (d t) x)) t₀ := by
  have hdetA := analyticAt_plane_det B t₀ hB
  have hi := analyticAt_negativeReferenceIntegral (Principal.standardSimplex 2 1)
    (Principal.standardSimplex_compact 2 1) R
    (fun t => affineCompose (u t) (B t) (c t))
    (fun t => affineCompose (d t) (B t) (c t)) t₀
    (analyticAt_affineCompose u B c t₀ hu hB hc)
    (analyticAt_affineCompose d B c t₀ hd hB hc)
  apply ((analyticAt_abs_of_ne_zero _ t₀ hdetA hdet).mul hi).congr
  filter_upwards [hdetA.continuousAt.eventually_ne hdet] with t ht
  rw [affineTriangle_integral (B t) ht]
  simp only [affineCompose_eval]
  rfl

end D4.AreaEnvelope
