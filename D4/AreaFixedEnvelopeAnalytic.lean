import D4.AreaAnalytic

/-! The negative branch is analytic even when its fixed spatial functions are
only continuous. The proof expands the actual integral as a finite polynomial. -/
noncomputable section
namespace D4.AreaEnvelope
open Set MeasureTheory

theorem analyticAt_integral_fixed_difference_pow (K : Set Plane) (hK : IsCompact K)
    (d : Plane → ℝ) (hd : ContinuousOn d K) (n : ℕ) (t₀ : ℝ) :
    AnalyticAt ℝ (fun t => ∫ x in K, (t-d x)^n) t₀ := by
  let b : Fin 2 → Plane → ℝ := ![fun _ => 1,d]
  let a : ℝ → Fin 2 → ℝ := fun t => ![t,-1]
  have hb (i : Fin 2) : ContinuousOn (b i) K := by
    fin_cases i
    · exact continuousOn_const
    · exact hd
  have ha (i : Fin 2) : AnalyticAt ℝ (fun t => a t i) t₀ := by
    fin_cases i
    · exact analyticAt_id
    · exact analyticAt_const
  have h := analyticAt_integral_finite_sum_pow K hK b hb a t₀ ha n
  simpa [a,b,Fin.sum_univ_succ,sub_eq_add_neg] using h

theorem integral_negative_fixed (K : Set Plane) (hK : IsCompact K)
    (R : ℝ) (U d : Plane → ℝ) (hU : ContinuousOn U K) (hd : ContinuousOn d K)
    (t : ℝ) :
    (∫ x in K, 4*R^2*U x + squareNegativePolynomial R (t-d x)) =
      4*R^2*(∫ x in K, U x) +
        (-2*R^3*volume.real K + R^2*(∫ x in K, t-d x) -
          R*(∫ x in K, (t-d x)^2) + (∫ x in K, (t-d x)^3)/6) := by
  let coeff : Fin 5 → ℝ := ![4*R^2,-2*R^3,R^2,-R,1/6]
  let basis : Fin 5 → Plane → ℝ :=
    ![U,fun _ => 1,fun x => t-d x,fun x => (t-d x)^2,fun x => (t-d x)^3]
  have hb (i : Fin 5) : IntegrableOn (basis i) K := by
    refine (show ContinuousOn (basis i) K from ?_).integrableOn_compact hK
    fin_cases i
    · exact hU
    · exact continuousOn_const
    · exact continuousOn_const.sub hd
    · exact (continuousOn_const.sub hd).pow 2
    · exact (continuousOn_const.sub hd).pow 3
  have he : (fun x => 4*R^2*U x + squareNegativePolynomial R (t-d x)) =
      fun x => ∑ i, coeff i * basis i x := by
    funext x
    simp [coeff,basis,Fin.sum_univ_succ,squareNegativePolynomial]
    ring
  rw [he,integral_finset_sum Finset.univ (fun i _ => (hb i).const_mul (coeff i))]
  simp only [integral_const_mul]
  norm_num [coeff,basis,Fin.sum_univ_succ,setIntegral_const]
  ring

theorem analyticAt_negativeAreaIntegral_fixed (K : Set Plane) (hK : IsCompact K)
    (R : ℝ) (U d : Plane → ℝ) (hU : ContinuousOn U K) (hd : ContinuousOn d K)
    (t₀ : ℝ) : AnalyticAt ℝ (negativeAreaIntegral K R U d) t₀ := by
  unfold negativeAreaIntegral
  simp_rw [integral_negative_fixed K hK R U d hU hd]
  have h1 := analyticAt_integral_fixed_difference_pow K hK d hd 1 t₀
  simp only [pow_one] at h1
  exact analyticAt_const.mul (analyticAt_const.add
    (((analyticAt_const.add (analyticAt_const.mul h1)).sub
      (analyticAt_const.mul (analyticAt_integral_fixed_difference_pow K hK d hd 2 t₀))).add
        ((analyticAt_integral_fixed_difference_pow K hK d hd 3 t₀).div
          analyticAt_const (by norm_num))))

end D4.AreaEnvelope
