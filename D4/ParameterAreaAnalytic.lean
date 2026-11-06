import D4.ParameterIntegralAnalytic
import D4.AreaPlaneSwap

/-! Jointly analytic polynomial integrals on moving triangles and trapezoids. -/
noncomputable section
namespace D4.ParameterArea
open Matrix MeasureTheory Set Filter Topology AreaEnvelope
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem integral_affine_pow (K : Set Plane) (hK : IsCompact K)
    (a : P → Fin 3 → ℝ) (p₀ : P) (ha : ∀ i, AnalyticAt ℝ (fun p => a p i) p₀)
    (n : ℕ) : AnalyticAt ℝ (fun p => ∫ x in K, (affineEval (a p) x)^n) p₀ := by
  have hb (i : Fin 3) : ContinuousOn (affineBasis i) K := by
    change ContinuousOn (fun x => affineBasis i x) K
    fin_cases i <;> dsimp [affineBasis] <;> fun_prop
  simp_rw [affineEval,integral_finite_sum_pow K hK affineBasis hb]
  exact Finset.analyticAt_sum _ fun f _ =>
    (Finset.analyticAt_prod _ fun j _ => ha (f j)).mul analyticAt_const

theorem negative_reference (K : Set Plane) (hK : IsCompact K) (R : ℝ)
    (u d : P → Fin 3 → ℝ) (τ : P → ℝ) (p₀ : P)
    (hu : ∀ i, AnalyticAt ℝ (fun p => u p i) p₀)
    (hd : ∀ i, AnalyticAt ℝ (fun p => d p i) p₀)
    (hτ : AnalyticAt ℝ τ p₀) :
    AnalyticAt ℝ (fun p => ∫ x in K, 4*R^2*affineEval (u p) x +
      squareNegativePolynomial R (τ p-affineEval (d p) x)) p₀ := by
  let a : P → Fin 3 → ℝ := fun p => ![τ p-d p 0,-d p 1,-d p 2]
  have he (p : P) (x : Plane) : τ p-affineEval (d p) x=affineEval (a p) x := by
    simp [affineEval_eq,a]
    ring
  simp_rw [he,integral_negativePolynomial K hK]
  have ha (i : Fin 3) : AnalyticAt ℝ (fun p => a p i) p₀ := by
    fin_cases i
    · exact hτ.sub (hd 0)
    · exact (hd 1).neg
    · exact (hd 2).neg
  have hiu := integral_affine_pow K hK u p₀ hu 1
  have hia := integral_affine_pow K hK a p₀ ha 1
  simp only [pow_one] at hiu hia
  exact (analyticAt_const.mul hiu).add
    (((analyticAt_const.add (analyticAt_const.mul hia)).sub
      (analyticAt_const.mul (integral_affine_pow K hK a p₀ ha 2))).add
        ((integral_affine_pow K hK a p₀ ha 3).div analyticAt_const (by norm_num)))

theorem affine_compose (a : P → Fin 3 → ℝ) (B : P → PlaneMatrix)
    (c : P → Plane) (p₀ : P)
    (ha : ∀ i, AnalyticAt ℝ (fun p => a p i) p₀)
    (hB : ∀ i j, AnalyticAt ℝ (fun p => B p i j) p₀)
    (hc : ∀ i, AnalyticAt ℝ (fun p => c p i) p₀) (i : Fin 3) :
    AnalyticAt ℝ (fun p => affineCompose (a p) (B p) (c p) i) p₀ := by
  fin_cases i
  · exact ((ha 0).add ((ha 1).mul (hc 0))).add ((ha 2).mul (hc 1))
  · exact ((ha 1).mul (hB 0 0)).add ((ha 2).mul (hB 1 0))
  · exact ((ha 1).mul (hB 0 1)).add ((ha 2).mul (hB 1 1))

theorem abs_of_ne_zero (f : P → ℝ) (p₀ : P)
    (hf : AnalyticAt ℝ f p₀) (hn : f p₀ ≠ 0) : AnalyticAt ℝ (fun p => |f p|) p₀ := by
  rcases lt_or_gt_of_ne hn with hn | hn
  · apply hf.neg.congr
    filter_upwards [hf.continuousAt.eventually_lt_const hn] with p hp
    exact (abs_of_neg hp).symm
  · apply hf.congr
    filter_upwards [hf.continuousAt.eventually_const_lt hn] with p hp
    exact (abs_of_pos hp).symm

theorem negative_triangle (R : ℝ) (u d : P → Fin 3 → ℝ)
    (B : P → PlaneMatrix) (c : P → Plane) (τ : P → ℝ) (p₀ : P)
    (hu : ∀ i, AnalyticAt ℝ (fun p => u p i) p₀)
    (hd : ∀ i, AnalyticAt ℝ (fun p => d p i) p₀)
    (hB : ∀ i j, AnalyticAt ℝ (fun p => B p i j) p₀)
    (hc : ∀ i, AnalyticAt ℝ (fun p => c p i) p₀)
    (hτ : AnalyticAt ℝ τ p₀) (hdet : (B p₀).det ≠ 0) :
    AnalyticAt ℝ (fun p => ∫ x in affineTriangle (B p) (c p),
      4*R^2*affineEval (u p) x + squareNegativePolynomial R (τ p-affineEval (d p) x)) p₀ := by
  have hdetA := ParameterAnalytic.matrix_det B p₀ hB
  have hi := negative_reference (Principal.standardSimplex 2 1)
    (Principal.standardSimplex_compact 2 1) R
    (fun p => affineCompose (u p) (B p) (c p))
    (fun p => affineCompose (d p) (B p) (c p)) τ p₀
    (affine_compose u B c p₀ hu hB hc) (affine_compose d B c p₀ hd hB hc) hτ
  apply ((abs_of_ne_zero _ p₀ hdetA hdet).mul hi).congr
  filter_upwards [hdetA.continuousAt.eventually_ne hdet] with p hp
  rw [affineTriangle_integral (B p) hp]
  simp only [affineCompose_eval]
  rfl

theorem trapezoid_valid_eventually (T : P → Trapezoid) (p₀ : P)
    (ha : ∀ k,AnalyticAt ℝ (fun p => (T p).coordinate k) p₀) (hT : (T p₀).Valid) :
    ∀ᶠ p in nhds p₀,(T p).Valid := by
  have h1 := (ha 1).continuousAt.eventually_const_lt hT.1
  have h2 := ((ha 4).sub (ha 2)).continuousAt.eventually_const_lt (sub_pos.mpr hT.2.1)
  have h3 := ((ha 5).sub (ha 3)).continuousAt.eventually_const_lt (sub_pos.mpr hT.2.2)
  filter_upwards [h1,h2,h3] with p hp1 hp2 hp3
  exact ⟨hp1,by change 0<(T p).topLeft-(T p).bottomLeft at hp2; linarith,
    by change 0<(T p).topRight-(T p).bottomRight at hp3; linarith⟩

theorem trapezoid_matrix (T : P → Trapezoid) (p₀ : P)
    (ha : ∀ k,AnalyticAt ℝ (fun p => (T p).coordinate k) p₀) (i j k : Fin 2) :
    AnalyticAt ℝ (fun p => (T p).matrix i j k) p₀ := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact ha 1
  · exact ha 1
  · exact (ha 3).sub (ha 2)
  · exact (ha 5).sub (ha 2)
  · exact ha 1
  · exact analyticAt_const
  · exact (ha 5).sub (ha 2)
  · exact (ha 4).sub (ha 2)

theorem trapezoid_origin (T : P → Trapezoid) (p₀ : P)
    (ha : ∀ k,AnalyticAt ℝ (fun p => (T p).coordinate k) p₀) (i : Fin 2) :
    AnalyticAt ℝ (fun p => (T p).origin i) p₀ := by
  fin_cases i
  · exact ha 0
  · exact ha 2

theorem negative_trapezoid (R : ℝ) (u d : P → Fin 3 → ℝ)
    (T : P → Trapezoid) (τ : P → ℝ) (p₀ : P)
    (hu : ∀ i,AnalyticAt ℝ (fun p => u p i) p₀)
    (hd : ∀ i,AnalyticAt ℝ (fun p => d p i) p₀)
    (hT : ∀ k,AnalyticAt ℝ (fun p => (T p).coordinate k) p₀)
    (hτ : AnalyticAt ℝ τ p₀) (hvalid : (T p₀).Valid) :
    AnalyticAt ℝ (fun p => ∫ x in (T p).body,
      4*R^2*affineEval (u p) x+squareNegativePolynomial R (τ p-affineEval (d p) x)) p₀ := by
  have ha (i : Fin 2) := negative_triangle R u d
    (fun p => (T p).matrix i) (fun p => (T p).origin) τ p₀ hu hd
    (trapezoid_matrix T p₀ hT i) (trapezoid_origin T p₀ hT) hτ
    ((T p₀).matrix_det_pos hvalid i).ne'
  apply (Finset.analyticAt_sum Finset.univ fun i _ => ha i).congr
  filter_upwards [trapezoid_valid_eventually T p₀ hT hvalid] with p hp
  apply ((T p).integral_triangles hp _ ?_).symm
  unfold squareNegativePolynomial
  have hcu := affineEval_continuous (u p)
  have hcd := affineEval_continuous (d p)
  exact (by fun_prop : Continuous (fun x =>
    4*R^2*affineEval (u p) x+(-2*R^3+R^2*(τ p-affineEval (d p) x)-
      R*(τ p-affineEval (d p) x)^2+(τ p-affineEval (d p) x)^3/6))).continuousOn

theorem negative_swapped_trapezoid (R : ℝ) (u d : P → Fin 3 → ℝ)
    (T : P → Trapezoid) (τ : P → ℝ) (p₀ : P)
    (hu : ∀ i,AnalyticAt ℝ (fun p => u p i) p₀)
    (hd : ∀ i,AnalyticAt ℝ (fun p => d p i) p₀)
    (hT : ∀ k,AnalyticAt ℝ (fun p => (T p).coordinate k) p₀)
    (hτ : AnalyticAt ℝ τ p₀) (hvalid : (T p₀).Valid) :
    AnalyticAt ℝ (fun p => ∫ x in planeSwap '' (T p).body,
      4*R^2*affineEval (u p) x+squareNegativePolynomial R (τ p-affineEval (d p) x)) p₀ := by
  simp_rw [planeSwap_integral,swapCoefficients_eval]
  apply negative_trapezoid R (fun p => swapCoefficients (u p))
    (fun p => swapCoefficients (d p)) T τ p₀ _ _ hT hτ hvalid
  · intro i
    fin_cases i
    · exact hu 0
    · exact hu 2
    · exact hu 1
  · intro i
    fin_cases i
    · exact hd 0
    · exact hd 2
    · exact hd 1

end D4.ParameterArea
