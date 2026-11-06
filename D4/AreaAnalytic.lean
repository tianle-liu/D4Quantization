import D4.AreaIntegral
import D4.PrincipalSimplex
import Mathlib.Analysis.Analytic.Constructions

/-! Analytic dependence of polynomial integrals on analytic coefficients.
The reference region and monomials are fixed; the coefficient integrals
are derived by finite expansion and linearity of Lebesgue integration. -/
noncomputable section
namespace D4.AreaEnvelope
open MeasureTheory Set

theorem integral_finite_sum_pow {ι : Type*} [Fintype ι] (K : Set Plane)
    (hK : IsCompact K) (b : ι → Plane → ℝ) (hb : ∀ i, ContinuousOn (b i) K)
    (a : ι → ℝ) (n : ℕ) :
    (∫ x in K, (∑ i, a i * b i x)^n) =
      ∑ p : Fin n → ι, (∏ j, a (p j)) * ∫ x in K, ∏ j, b (p j) x := by
  classical
  simp_rw [Fintype.sum_pow,Finset.prod_mul_distrib]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro p _
    exact integral_const_mul _ _
  · intro p _
    exact (continuousOn_const.mul (continuousOn_finset_prod _ fun j _ => hb (p j))).integrableOn_compact hK

theorem analyticAt_integral_finite_sum_pow {ι : Type*} [Fintype ι] (K : Set Plane)
    (hK : IsCompact K) (b : ι → Plane → ℝ) (hb : ∀ i, ContinuousOn (b i) K)
    (a : ℝ → ι → ℝ) (t₀ : ℝ) (ha : ∀ i, AnalyticAt ℝ (fun t => a t i) t₀)
    (n : ℕ) : AnalyticAt ℝ (fun t => ∫ x in K, (∑ i, a t i * b i x)^n) t₀ := by
  simp_rw [integral_finite_sum_pow K hK b hb]
  exact Finset.analyticAt_sum _ fun p _ =>
    (Finset.analyticAt_prod _ fun j _ => ha (p j)).mul analyticAt_const

def affineBasis (i : Fin 3) (x : Plane) : ℝ := ![1,x 0,x 1] i

def affineEval (a : Fin 3 → ℝ) (x : Plane) : ℝ := ∑ i, a i * affineBasis i x

theorem affineEval_eq (a : Fin 3 → ℝ) (x : Plane) :
    affineEval a x = a 0 + a 1*x 0 + a 2*x 1 := by
  simp [affineEval,affineBasis,Fin.sum_univ_succ] <;> ring

theorem affineEval_continuous (a : Fin 3 → ℝ) : Continuous (affineEval a) := by
  change Continuous (fun x => affineEval a x)
  simp_rw [affineEval_eq]
  fun_prop

theorem analyticAt_integral_affine_pow (K : Set Plane) (hK : IsCompact K)
    (a : ℝ → Fin 3 → ℝ) (t₀ : ℝ) (ha : ∀ i, AnalyticAt ℝ (fun t => a t i) t₀)
    (n : ℕ) : AnalyticAt ℝ (fun t => ∫ x in K, (affineEval (a t) x)^n) t₀ := by
  apply analyticAt_integral_finite_sum_pow K hK affineBasis _ a t₀ ha n
  intro i
  change ContinuousOn (fun x => affineBasis i x) K
  fin_cases i <;> dsimp [affineBasis] <;> fun_prop

def affineComplement (a : ℝ → Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![t-a t 0,-a t 1,-a t 2]

theorem affineComplement_eval (a : ℝ → Fin 3 → ℝ) (t : ℝ) (x : Plane) :
    affineEval (affineComplement a t) x = t-affineEval (a t) x := by
  simp [affineEval_eq,affineComplement]
  ring

theorem analyticAt_affineComplement (a : ℝ → Fin 3 → ℝ) (t₀ : ℝ)
    (ha : ∀ i, AnalyticAt ℝ (fun t => a t i) t₀) (i : Fin 3) :
    AnalyticAt ℝ (fun t => affineComplement a t i) t₀ := by
  fin_cases i
  · exact analyticAt_id.sub (ha 0)
  · exact (ha 1).neg
  · exact (ha 2).neg

theorem integral_negativePolynomial (K : Set Plane) (hK : IsCompact K) (R : ℝ)
    (u a : Fin 3 → ℝ) :
    (∫ x in K, 4*R^2*affineEval u x + squareNegativePolynomial R (affineEval a x)) =
      4*R^2*(∫ x in K, affineEval u x) +
        (-2*R^3*volume.real K + R^2*(∫ x in K, affineEval a x) -
          R*(∫ x in K, (affineEval a x)^2) + (∫ x in K, (affineEval a x)^3)/6) := by
  let coeff : Fin 5 → ℝ := ![4*R^2,-2*R^3,R^2,-R,1/6]
  let basis : Fin 5 → Plane → ℝ :=
    ![affineEval u,fun _ => 1,affineEval a,fun x => (affineEval a x)^2,fun x => (affineEval a x)^3]
  have hb (i : Fin 5) : IntegrableOn (basis i) K := by
    refine (show Continuous (basis i) from ?_).continuousOn.integrableOn_compact hK
    fin_cases i
    · exact affineEval_continuous u
    · exact continuous_const
    · exact affineEval_continuous a
    · exact (affineEval_continuous a).pow 2
    · exact (affineEval_continuous a).pow 3
  have he : (fun x => 4*R^2*affineEval u x + squareNegativePolynomial R (affineEval a x)) =
      fun x => ∑ i, coeff i * basis i x := by
    funext x
    simp [coeff,basis,Fin.sum_univ_succ,squareNegativePolynomial]
    ring
  rw [he,integral_finset_sum Finset.univ (fun i _ => (hb i).const_mul (coeff i))]
  simp only [integral_const_mul]
  norm_num [coeff,basis,Fin.sum_univ_succ,setIntegral_const]
  ring

theorem analyticAt_negativeReferenceIntegral (K : Set Plane) (hK : IsCompact K) (R : ℝ)
    (u d : ℝ → Fin 3 → ℝ) (t₀ : ℝ)
    (hu : ∀ i, AnalyticAt ℝ (fun t => u t i) t₀)
    (hd : ∀ i, AnalyticAt ℝ (fun t => d t i) t₀) :
    AnalyticAt ℝ (fun t => ∫ x in K, 4*R^2*affineEval (u t) x +
      squareNegativePolynomial R (t-affineEval (d t) x)) t₀ := by
  simp_rw [← affineComplement_eval,integral_negativePolynomial K hK]
  have ha := analyticAt_affineComplement d t₀ hd
  have hiu := analyticAt_integral_affine_pow K hK u t₀ hu 1
  have hia := analyticAt_integral_affine_pow K hK (affineComplement d) t₀ ha 1
  simp only [pow_one] at hiu hia
  exact (analyticAt_const.mul hiu).add
    (((analyticAt_const.add (analyticAt_const.mul hia)).sub
      (analyticAt_const.mul (analyticAt_integral_affine_pow K hK _ t₀ ha 2))).add
        ((analyticAt_integral_affine_pow K hK _ t₀ ha 3).div analyticAt_const (by norm_num)))

end D4.AreaEnvelope
