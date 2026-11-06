import D4.C23LocalWindow

/-! Exact volume preservation for the affine coordinates and fiber translations. -/
noncomputable section
namespace D4.C23Local
open Matrix MeasureTheory Set Analytic AreaEnvelope

def fiberShear (U : Plane → ℝ) (hU : Continuous U) :
    WindowCoordinates ≃ᵐ WindowCoordinates where
  toFun p := (p.1,(p.2.1+U p.1,p.2.2+U p.1))
  invFun p := (p.1,(p.2.1-U p.1,p.2.2-U p.1))
  left_inv := by intro p; simp
  right_inv := by intro p; simp
  measurable_toFun := by
    change Measurable (fun p : WindowCoordinates => (p.1,(p.2.1+U p.1,p.2.2+U p.1)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : WindowCoordinates => (p.1,(p.2.1-U p.1,p.2.2-U p.1)))
    fun_prop

theorem fiberShear_preserving (U : Plane → ℝ) (hU : Continuous U) :
    MeasurePreserving (fiberShear U hU) volume volume := by
  letI : (volume : Measure (ℝ × ℝ)).IsAddLeftInvariant := by
    rw [Measure.volume_eq_prod]
    infer_instance
  refine (MeasurePreserving.id (volume : Measure Plane)).skew_product
    (g := fun L (p : ℝ × ℝ) => (p.1+U L,p.2+U L)) (by fun_prop) ?_
  apply Filter.Eventually.of_forall
  intro L
  have he : (fun p : ℝ × ℝ => (p.1+U L,p.2+U L)) =
      fun p => (U L,U L)+p := by funext p; ext <;> simp [add_comm]
  change Measure.map (fun p : ℝ × ℝ => (p.1+U L,p.2+U L)) volume=volume
  rw [he]
  exact (measurePreserving_add_left (volume : Measure (ℝ × ℝ)) (U L,U L)).map_eq

def coordinatesEquiv2 (Q : Gram) : Vec ≃ᵐ Vec where
  toFun := coordinates2 Q
  invFun := inverseCoordinates2 Q
  left_inv := inverse_coordinates2 Q
  right_inv := coordinates2_inverse Q
  measurable_toFun := (coordinates2_preserving Q).measurable
  measurable_invFun := by
    apply Continuous.measurable
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun c : Vec => Q 0 0-c 0); fun_prop
    · change Continuous (fun c : Vec => Q 1 1-c 1); fun_prop
    · change Continuous (fun c : Vec => c 2-Q 2 2); fun_prop
    · change Continuous (fun c : Vec => c 3-Q 3 3); fun_prop

def coordinatesEquiv3 (Q : Gram) : Vec ≃ᵐ Vec where
  toFun := coordinates3 Q
  invFun := inverseCoordinates3 Q
  left_inv := inverse_coordinates3 Q
  right_inv := coordinates3_inverse Q
  measurable_toFun := (coordinates3_preserving Q).measurable
  measurable_invFun := by
    apply Continuous.measurable
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun c : Vec => c 2-Q 0 0); fun_prop
    · change Continuous (fun c : Vec => c 3-Q 1 1); fun_prop
    · change Continuous (fun c : Vec => Q 2 2-c 0); fun_prop
    · change Continuous (fun c : Vec => Q 3 3-c 1); fun_prop

def windowEquiv2 (Q : Gram) (U : Plane → ℝ) (hU : Continuous U) :
    WindowCoordinates ≃ᵐ Vec :=
  (fiberShear U hU).trans (splitCoordinates.symm.trans (coordinatesEquiv2 Q).symm)

def windowEquiv3 (Q : Gram) (U : Plane → ℝ) (hU : Continuous U) :
    WindowCoordinates ≃ᵐ Vec :=
  (fiberShear U hU).trans (splitCoordinates.symm.trans (coordinatesEquiv3 Q).symm)

theorem windowEquiv2_apply (Q : Gram) (U : Plane → ℝ) (hU : Continuous U)
    (p : WindowCoordinates) : windowEquiv2 Q U hU p=windowPoint2 Q U p := by
  change inverseCoordinates2 Q (splitCoordinates.symm (fiberShear U hU p)) = _
  rw [splitCoordinates_symm_apply]
  rfl

theorem windowEquiv3_apply (Q : Gram) (U : Plane → ℝ) (hU : Continuous U)
    (p : WindowCoordinates) : windowEquiv3 Q U hU p=windowPoint3 Q U p := by
  change inverseCoordinates3 Q (splitCoordinates.symm (fiberShear U hU p)) = _
  rw [splitCoordinates_symm_apply]
  rfl

theorem windowEquiv2_preserving (Q : Gram) (U : Plane → ℝ) (hU : Continuous U) :
    MeasurePreserving (windowEquiv2 Q U hU) volume volume :=
  ((coordinates2_preserving Q).symm (coordinatesEquiv2 Q)).comp
    ((splitCoordinates_preserving.symm splitCoordinates).comp (fiberShear_preserving U hU))

theorem windowEquiv3_preserving (Q : Gram) (U : Plane → ℝ) (hU : Continuous U) :
    MeasurePreserving (windowEquiv3 Q U hU) volume volume :=
  ((coordinates3_preserving Q).symm (coordinatesEquiv3 Q)).comp
    ((splitCoordinates_preserving.symm splitCoordinates).comp (fiberShear_preserving U hU))

theorem localWindow2_integral (Q : Gram) (U : Plane → ℝ) (hU : Continuous U)
    (K : Set Plane) (R : ℝ) (f : Vec → ℝ) :
    (∫ r in localWindow2 Q U K R,f r)=
      ∫ p in referenceWindow K R,f (windowPoint2 Q U p) := by
  have he : localWindow2 Q U K R=windowEquiv2 Q U hU '' referenceWindow K R := by
    simp only [localWindow2,windowEquiv2_apply]
  rw [he]
  have hi := setIntegral_map_equiv (μ := (volume : Measure WindowCoordinates))
    (windowEquiv2 Q U hU) f (windowEquiv2 Q U hU '' referenceWindow K R)
  rw [(windowEquiv2_preserving Q U hU).map_eq,
    (windowEquiv2 Q U hU).injective.preimage_image] at hi
  simpa only [windowEquiv2_apply] using hi

theorem localWindow3_integral (Q : Gram) (U : Plane → ℝ) (hU : Continuous U)
    (K : Set Plane) (R : ℝ) (f : Vec → ℝ) :
    (∫ r in localWindow3 Q U K R,f r)=
      ∫ p in referenceWindow K R,f (windowPoint3 Q U p) := by
  have he : localWindow3 Q U K R=windowEquiv3 Q U hU '' referenceWindow K R := by
    simp only [localWindow3,windowEquiv3_apply]
  rw [he]
  have hi := setIntegral_map_equiv (μ := (volume : Measure WindowCoordinates))
    (windowEquiv3 Q U hU) f (windowEquiv3 Q U hU '' referenceWindow K R)
  rw [(windowEquiv3_preserving Q U hU).map_eq,
    (windowEquiv3 Q U hU).injective.preimage_image] at hi
  simpa only [windowEquiv3_apply] using hi

end D4.C23Local
