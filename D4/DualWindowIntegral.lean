import D4.PeriodicWindowIntegral
import D4.NearestJointContinuity

/-! The actual dual nearest-point integral of a compact local window equals
its periodic pieces in any translated moving dual period. -/
noncomputable section
namespace D4.Analytic
open Set Matrix MeasureTheory
open scoped Pointwise
attribute [local instance] integerTranslation

theorem dualMap_add (Q : Gram) (x y : Vec) : dualMap Q (x+y)=dualMap Q x+dualMap Q y :=
  Matrix.mulVec_add _ _ _

theorem dualMap_injective {Q : Gram} (hQ : Q.PosDef) : Function.Injective (dualMap Q) := by
  intro x y h
  simpa only [dualInverse_dualMap hQ] using congrArg (dualInverse Q) h

theorem dualMap_image_inverse {Q : Gram} (hQ : Q.PosDef) (W : Set Vec) :
    dualMap Q '' (dualInverse Q '' W)=W := by
  rw [← Set.image_comp]
  simp only [Function.comp_def,dualMap_dualInverse hQ,Set.image_id']

theorem dualMap_image_shiftedCube (Q : Gram) (c : Vec) :
    dualMap Q '' shiftedCube c=dualPeriod Q c := by
  unfold shiftedCube dualPeriod
  ext r
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x-c,hx,congrArg (dualMap Q) (by abel : c+(x-c)=x)⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨c+x,by simpa using hx,rfl⟩

theorem dualMap_image_translated_window {Q : Gram} (hQ : Q.PosDef)
    (W : Set Vec) (n : IntVec) :
    dualMap Q '' (n+ᵥ(dualInverse Q '' W))=dualTranslate Q n W := by
  ext r
  constructor
  · rintro ⟨_,⟨_,⟨w,hw,rfl⟩,rfl⟩,rfl⟩
    refine ⟨w,hw,?_⟩
    change w+dualMap Q (castVec n)=dualMap Q (castVec n+dualInverse Q w)
    rw [dualMap_add,dualMap_dualInverse hQ,add_comm]
  · rintro ⟨w,hw,rfl⟩
    refine ⟨n+ᵥdualInverse Q w,⟨dualInverse Q w,⟨w,hw,rfl⟩,rfl⟩,?_⟩
    change dualMap Q (castVec n+dualInverse Q w)=w+dualMap Q (castVec n)
    rw [dualMap_add,dualMap_dualInverse hQ,add_comm]

theorem dualNearest_image_integral {Q : Gram} (hQ : Q.PosDef) (S : Set Vec) :
    (∫ r in dualMap Q '' S,dualNearest Q r)=
      (16*Q.det)*(∫ x in S,nearest Q x) := by
  have hh := affineImage_integral ((2:ℝ) • Q) (dualMatrix_det_ne_zero hQ) 0 S (dualNearest Q)
  simp only [zero_add] at hh
  change (∫ r in dualMap Q '' S,dualNearest Q r)=_ at hh
  rw [hh,dualMatrix_det,abs_of_pos (mul_pos (by norm_num) hQ.det_pos)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  exact congrArg (nearest Q) (dualInverse_dualMap hQ x)

theorem dualNearest_window_periodization {Q : Gram} (hQ : Q.PosDef)
    (c : Vec) (W : Set Vec) (hW : IsCompact W) :
    (∫ r in W,dualNearest Q r)=
      ∑' n : IntVec,∫ r in dualTranslate Q n W∩dualPeriod Q c,dualNearest Q r := by
  have hwin : IsCompact (dualInverse Q '' W) := hW.image (by unfold dualInverse; fun_prop)
  have h_int := nearest_window_periodization Q c (dualInverse Q '' W)
    ((nearest_continuous_point hQ).continuousOn.integrableOn_compact hwin)
  calc
    (∫ r in W,dualNearest Q r) =
        (16*Q.det)*(∫ x in dualInverse Q '' W,nearest Q x) := by
      rw [← dualNearest_image_integral hQ,dualMap_image_inverse hQ]
    _ = (16*Q.det)*(∑' n : IntVec,
        ∫ x in (n+ᵥ(dualInverse Q '' W))∩shiftedCube c,nearest Q x) := by rw [h_int]
    _ = ∑' n : IntVec,(16*Q.det)*
        (∫ x in (n+ᵥ(dualInverse Q '' W))∩shiftedCube c,nearest Q x) := by rw [tsum_mul_left]
    _ = _ := by
      apply tsum_congr
      intro n
      rw [← dualNearest_image_integral hQ,Set.image_inter (dualMap_injective hQ),
        dualMap_image_translated_window hQ,dualMap_image_shiftedCube]

theorem dualNearest_window_finite_periodization {Q : Gram} (hQ : Q.PosDef)
    (c : Vec) (W : Set Vec) (hW : IsCompact W) (s : Finset IntVec)
    (hs : ∀ n,(dualPeriod Q c∩dualTranslate Q n W).Nonempty → n∈s) :
    (∫ r in W,dualNearest Q r)=
      ∑ n∈s,∫ r in dualTranslate Q n W∩dualPeriod Q c,dualNearest Q r := by
  rw [dualNearest_window_periodization hQ c W hW]
  apply tsum_eq_sum
  intro n hn
  have he : dualTranslate Q n W∩dualPeriod Q c=∅ := by
    apply Set.eq_empty_of_forall_not_mem
    intro x hx
    exact hn (hs n ⟨x,hx.2,hx.1⟩)
  simp only [he,setIntegral_empty]

end D4.Analytic
