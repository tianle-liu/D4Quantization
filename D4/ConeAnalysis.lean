import D4.CircularCone
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.IntermediateValue

/-!
# The actual circular-cone angle integrals

The dimension is a natural number. The positive factor D is the surface
area factor `(d-1) κ_(d-1)` in the geometric application. Both displayed
angle integrands in the paper are defined as genuine real integrals.
-/
noncomputable section
namespace D4.ConeAnalysis
open Set MeasureTheory

def radiusKernel (n : ℕ) (r : ℝ) : ℝ :=
  r ^ (n-2) * (1+r^2) ^ (-(n:ℝ)/2)

def radiusAngle (n : ℕ) (D r : ℝ) : ℝ :=
  D * ∫ t in (0:ℝ)..r, radiusKernel n t

def angle (n : ℕ) (D θ : ℝ) : ℝ :=
  D * ∫ t in (0:ℝ)..θ, Real.sin t ^ (n-2)

theorem continuous_radiusKernel (n : ℕ) : Continuous (radiusKernel n) := by
  unfold radiusKernel
  apply Continuous.mul (by fun_prop)
  exact (by fun_prop : Continuous (fun r : ℝ => 1+r^2)).rpow_const
    (fun r => Or.inl (by positivity))

theorem hasDerivAt_radiusAngle (n : ℕ) (D r : ℝ) :
    HasDerivAt (radiusAngle n D) (D * radiusKernel n r) r := by
  have hc := continuous_radiusKernel n
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_mul D

theorem radiusKernel_pos (n : ℕ) (r : ℝ) (hr : 0 < r) : 0 < radiusKernel n r := by
  unfold radiusKernel
  exact mul_pos (pow_pos hr _) (Real.rpow_pos_of_pos (by positivity) _)

theorem radiusAngle_strictMonoOn (n : ℕ) (D : ℝ) (hD : 0 < D) :
    StrictMonoOn (radiusAngle n D) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
  · intro r hr
    exact (hasDerivAt_radiusAngle n D r).continuousAt.continuousWithinAt
  · intro r hr
    have hr' : 0 < r := by simpa only [interior_Ici, mem_Ioi] using hr
    rw [(hasDerivAt_radiusAngle n D r).deriv]
    exact mul_pos hD (radiusKernel_pos n r hr')

@[simp] theorem radiusAngle_zero (n : ℕ) (D : ℝ) : radiusAngle n D 0 = 0 := by
  simp [radiusAngle]

theorem radiusAngle_pos (n : ℕ) (D r : ℝ) (hD : 0 < D) (hr : 0 < r) :
    0 < radiusAngle n D r := by
  simpa only [radiusAngle_zero] using
    radiusAngle_strictMonoOn n D hD (by simp) hr.le hr

theorem hasDerivAt_angle (n : ℕ) (D θ : ℝ) :
    HasDerivAt (angle n D) (D * Real.sin θ ^ (n-2)) θ := by
  have hc : Continuous (fun t : ℝ => Real.sin t ^ (n-2)) := by fun_prop
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 θ)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_mul D

@[simp] theorem angle_zero (n : ℕ) (D : ℝ) : angle n D 0 = 0 := by
  simp [angle]

theorem angle_strictMonoOn (n : ℕ) (D : ℝ) (hD : 0 < D) :
    StrictMonoOn (angle n D) (Icc 0 (Real.pi/2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) (Real.pi/2))
  · intro θ hθ
    exact (hasDerivAt_angle n D θ).continuousAt.continuousWithinAt
  · intro θ hθ
    have hθ' : θ ∈ Ioo 0 (Real.pi/2) := by
      simpa only [interior_Icc] using hθ
    rw [(hasDerivAt_angle n D θ).deriv]
    exact mul_pos hD (pow_pos (Real.sin_pos_of_pos_of_lt_pi hθ'.1
      (hθ'.2.trans (by linarith [Real.pi_pos]))) _)

theorem angle_endpoint_pos (n : ℕ) (D : ℝ) (hD : 0 < D) :
    0 < angle n D (Real.pi/2) := by
  have hp : (0:ℝ) < Real.pi/2 := by positivity
  simpa only [angle_zero] using angle_strictMonoOn n D hD
    (show 0 ∈ Icc 0 (Real.pi/2) from ⟨le_rfl, hp.le⟩)
    (show Real.pi/2 ∈ Icc 0 (Real.pi/2) from ⟨hp.le, le_rfl⟩) hp

theorem angularKernel_arctan (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    Real.sin (Real.arctan r) ^ (n-2) / (1+r^2) = radiusKernel n r := by
  have hX : 0 < 1+r^2 := by positivity
  have hp : (Real.sqrt (1+r^2)) ^ (n-2) = (1+r^2)^(((n:ℝ)-2)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hX.le,
      Nat.cast_sub hn]
    norm_num
    congr 1
    ring
  have hp' : (Real.sqrt (1+r^2)) ^ (n-2) * (1+r^2) = (1+r^2)^((n:ℝ)/2) := by
    rw [hp, ← Real.rpow_add_one hX.ne']
    congr 1
    ring
  unfold radiusKernel
  rw [Real.sin_arctan, div_pow, div_div, hp',
    show -(n:ℝ)/2 = -((n:ℝ)/2) by ring, Real.rpow_neg hX.le]
  rfl

theorem hasDerivAt_angle_arctan (n : ℕ) (hn : 2 ≤ n) (D r : ℝ) :
    HasDerivAt (fun x => angle n D (Real.arctan x)) (D * radiusKernel n r) r := by
  have H := (hasDerivAt_angle n D (Real.arctan r)).comp r (Real.hasDerivAt_arctan r)
  convert H using 1
  rw [← angularKernel_arctan n hn r]
  ring

/-- The two actual angle integrals in the paper agree. -/
theorem radiusAngle_eq_angle_arctan (n : ℕ) (hn : 2 ≤ n) (D r : ℝ) :
    radiusAngle n D r = angle n D (Real.arctan r) := by
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := r) (fun x hx => hasDerivAt_angle_arctan n hn D x)
    ((continuous_const.mul (continuous_radiusKernel n)).intervalIntegrable 0 r)
  simpa only [radiusAngle, intervalIntegral.integral_const_mul, Real.arctan_zero,
    angle_zero, sub_zero] using H

theorem image_arctan_positive :
    Real.arctan '' Ioi (0:ℝ) = Ioo 0 (Real.pi/2) := by
  ext θ
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨by simpa only [Real.arctan_zero] using Real.arctan_strictMono hr,
      Real.arctan_lt_pi_div_two r⟩
  · intro hθ
    refine ⟨Real.tan θ, Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2, ?_⟩
    exact Real.arctan_tan (by linarith [Real.pi_pos, hθ.1]) hθ.2

theorem angle_image_open (n : ℕ) (D : ℝ) (hD : 0 < D) :
    angle n D '' Ioo 0 (Real.pi/2) = Ioo 0 (angle n D (Real.pi/2)) := by
  have hc : ContinuousOn (angle n D) (Icc 0 (Real.pi/2)) :=
    fun θ hθ => (hasDerivAt_angle n D θ).continuousAt.continuousWithinAt
  have h := Set.Subset.antisymm (angle_strictMonoOn n D hD).image_Ioo_subset
    (intermediate_value_Ioo (by positivity : (0:ℝ) ≤ Real.pi/2) hc)
  simpa only [angle_zero] using h

/-- Positive radii give exactly the open solid-angle interval. -/
theorem radiusAngle_image_positive (n : ℕ) (hn : 2 ≤ n) (D : ℝ) (hD : 0 < D) :
    radiusAngle n D '' Ioi 0 = Ioo 0 (angle n D (Real.pi/2)) := by
  have he : radiusAngle n D = (angle n D) ∘ Real.arctan :=
    funext (radiusAngle_eq_angle_arctan n hn D)
  rw [he, Set.image_comp, image_arctan_positive, angle_image_open n D hD]

end D4.ConeAnalysis
