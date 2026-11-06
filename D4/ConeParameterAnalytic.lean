import D4.PrincipalClosedMoment
import D4.PrincipalSecondaryBoundary
import D4.CertificateAnalytic
import Mathlib.Analysis.Analytic.Inverse

/-! Multivariable analyticity on the open parameter cones.  The functions
are the genuine nearest-lattice-point integrals. -/
noncomputable section
namespace D4.ConeParameterAnalytic
open Matrix Analytic Principal Certificate CertificateMoments Filter Set

abbrev Weights := Fin 10 → ℝ

def positiveWeights : Set Weights := {w | ∀ i,0<w i}

theorem positiveWeights_convex : Convex ℝ positiveWeights := by
  simpa [positiveWeights,Set.pi] using
    (convex_pi (𝕜 := ℝ) (s := Set.univ) (t := fun _ : Fin 10 => Ioi (0:ℝ))
      (fun _ _ => convex_Ioi (0:ℝ)))

theorem positiveWeights_connected : IsConnected positiveWeights :=
  ⟨⟨fun _ => 1,fun _ => by norm_num⟩,positiveWeights_convex.isPreconnected⟩

theorem positiveWeights_open : IsOpen positiveWeights := by
  simpa only [positiveWeights,Set.iInter_setOf] using
    (isOpen_iInter_of_finite (fun i : Fin 10 =>
      isOpen_lt (f := fun _ : Weights => (0:ℝ)) continuous_const (continuous_apply i)))

theorem coordinate_analytic (w : Weights) (i : Fin 10) :
    AnalyticAt ℝ (fun x : Weights => x i) w :=
  (ContinuousLinearMap.proj (R := ℝ) i).analyticAt w

theorem extension_analytic (w : Weights) (i : Nat) :
    AnalyticAt ℝ (fun x : Weights => extendWeight x i) w := by
  by_cases hi : i<10
  · simpa only [extendWeight,dif_pos hi] using coordinate_analytic w ⟨i,hi⟩
  · simp only [extendWeight,dif_neg hi]
    exact analyticAt_const

theorem monomial_analytic (w : Weights) (m : Monomial) :
    AnalyticAt ℝ (fun x : Weights => monomial (extendWeight x) m) w := by
  induction m with
  | nil => exact analyticAt_const
  | cons i m ih =>
    simpa only [monomial,List.map_cons,List.prod_cons] using (extension_analytic w i).mul ih

theorem polynomial_analytic (w : Weights) (p : Poly) :
    AnalyticAt ℝ (fun x : Weights => eval (extendWeight x) p) w := by
  induction p with
  | nil => exact analyticAt_const
  | cons s p ih =>
    simpa only [eval_cons] using
      (analyticAt_const.mul (monomial_analytic w s.1)).add ih

theorem determinant_analytic (Q : Weights → Gram) (w : Weights)
    (hQ : ∀ i j,AnalyticAt ℝ (fun x => Q x i j) w) :
    AnalyticAt ℝ (fun x => (Q x).det) w := by
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_sum
  intro σ _
  apply AnalyticAt.mul analyticAt_const
  exact Finset.analyticAt_prod _ (fun i _ => hQ (σ i) i)

theorem principal_entry_analytic (w : Weights) (i j : Fin 4) :
    AnalyticAt ℝ (fun x : Weights => principalForm x i j) w := by
  simp only [principalForm,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  exact Finset.analyticAt_sum _ (fun k _ => (coordinate_analytic w k).mul analyticAt_const)

theorem secondary_entry_analytic (v : Fin 9 → Vec) (w : Weights) (i j : Fin 4) :
    AnalyticAt ℝ (fun x : Weights => secondaryForm v (x 0) (fun k => x k.succ) i j) w := by
  simp only [secondaryForm,Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  exact ((coordinate_analytic w 0).mul analyticAt_const).add
    (Finset.analyticAt_sum _ (fun k _ => (coordinate_analytic w k.succ).mul analyticAt_const))

theorem positive_eventually (w : Weights) (hw : ∀ i,0<w i) :
    ∀ᶠ x in nhds w,∀ i,0<x i := by
  rw [Filter.eventually_all]
  intro i
  exact (continuous_apply i).continuousAt.eventually (Ioi_mem_nhds (hw i))

theorem moment_analytic_of_formula (Q : Weights → Gram) (p : Poly) (k : ℝ)
    (hk : k≠0) (w : Weights) (hw : ∀ i,0<w i)
    (hQ : ∀ i j,AnalyticAt ℝ (fun x => Q x i j) w)
    (hpos : ∀ x : Weights,(∀ i,0<x i) → (Q x).PosDef)
    (hformula : ∀ x : Weights,(∀ i,0<x i) →
      k*(Q x).det*moment (Q x)=eval (extendWeight x) p) :
    AnalyticAt ℝ (fun x : Weights => moment (Q x)) w := by
  have ha := (polynomial_analytic w p).div
    (analyticAt_const.mul (determinant_analytic Q w hQ))
    (mul_ne_zero hk (hpos w hw).det_pos.ne')
  apply ha.congr
  filter_upwards [positive_eventually w hw] with x hx
  exact (eq_div_iff (mul_ne_zero hk (hpos x hx).det_pos.ne')).mpr
    (by simpa only [mul_comm (moment (Q x))] using hformula x hx) |>.symm

theorem principal_moment_analytic (w : Weights) (hw : ∀ i,0<w i) :
    AnalyticAt ℝ (fun x : Weights => moment (principalForm x)) w := by
  apply moment_analytic_of_formula principalForm momentC1 12 (by norm_num) w hw
    (principal_entry_analytic w)
  · exact fun _ hx => principal_posDef_of_pos hx
  · exact fun x hx => principal_moment_identity x (fun i => (hx i).le)
      (principal_posDef_of_pos hx)

end D4.ConeParameterAnalytic
