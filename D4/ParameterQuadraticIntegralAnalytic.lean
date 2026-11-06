import D4.ParameterIntegralAnalytic

/-! Analytic quadratic integrals on a fixed compact reference window.
The spatial coordinates may be continuous piecewise affine functions. -/
noncomputable section
namespace D4.ParameterAnalytic
open Matrix MeasureTheory Set C23Local Analytic

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem integral_affine_product
    (S : Set WindowCoordinates) (hS : IsCompact S)
    (g h : WindowCoordinates → ℝ) (hg : Continuous g) (hh : Continuous h)
    (a b : P → ℝ) (t₀ : P) (ha : AnalyticAt ℝ a t₀) (hb : AnalyticAt ℝ b t₀) :
    AnalyticAt ℝ (fun t => ∫ x in S,(a t+g x)*(b t+h x)) t₀ := by
  have he (t : P) : (∫ x in S,(a t+g x)*(b t+h x)) =
      a t*b t*volume.real S+a t*(∫ x in S,h x)+
        b t*(∫ x in S,g x)+(∫ x in S,g x*h x) := by
    have hp : (fun x => (a t+g x)*(b t+h x)) =
        fun x => ((a t*b t+a t*h x)+b t*g x)+g x*h x := by
      funext x; ring
    rw [hp]
    have hi (f : WindowCoordinates → ℝ) (hf : Continuous f) : IntegrableOn f S :=
      hf.continuousOn.integrableOn_compact hS
    rw [integral_add (hi _ (by fun_prop)) (hi _ (hg.mul hh)),
      integral_add (hi _ (by fun_prop)) (hi _ (by fun_prop)),
      integral_add (hi _ continuous_const) (hi _ (by fun_prop)),
      integral_const_mul,integral_const_mul,setIntegral_const]
    simp only [integral_const_mul,smul_eq_mul]
    ring
  simp_rw [he]
  exact (((ha.mul hb).mul analyticAt_const).add (ha.mul analyticAt_const)).add
    (hb.mul analyticAt_const) |>.add analyticAt_const

theorem integral_quadratic_shift
    (S : Set WindowCoordinates) (hS : IsCompact S)
    (g : WindowCoordinates → Vec) (hg : Continuous g)
    (Q : P → Gram) (a : P → Vec) (t₀ : P)
    (hQ : ∀ i j, AnalyticAt ℝ (fun t => Q t i j) t₀)
    (ha : ∀ i, AnalyticAt ℝ (fun t => a t i) t₀) :
    AnalyticAt ℝ (fun t => ∫ x in S,quadratic (Q t) (a t+g x)) t₀ := by
  have he (t : P) (x : WindowCoordinates) :
      quadratic (Q t) (a t+g x) =
        ∑ i : Fin 4, ∑ j : Fin 4, Q t i j*((a t i+g x i)*(a t j+g x j)) := by
    simp only [quadratic, dotProduct, Matrix.mulVec,Pi.add_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  have hi (t : P) (i j : Fin 4) :
      IntegrableOn (fun x => Q t i j*((a t i+g x i)*(a t j+g x j))) S := by
    refine (show Continuous _ from ?_).continuousOn.integrableOn_compact hS
    fun_prop
  simp_rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi _ i j)),
    integral_finset_sum _ (fun j _ => hi _ _ j),integral_const_mul]
  apply Finset.analyticAt_sum
  intro i _
  apply Finset.analyticAt_sum
  intro j _
  exact (hQ i j).mul (integral_affine_product S hS
    (fun x => g x i) (fun x => g x j) (by fun_prop) (by fun_prop)
    (fun t => a t i) (fun t => a t j) t₀ (ha i) (ha j))

end D4.ParameterAnalytic
