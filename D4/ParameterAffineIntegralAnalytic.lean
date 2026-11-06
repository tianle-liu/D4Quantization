import D4.ParameterIntegralAnalytic
import D4.PrincipalIntegral

/-! Joint analyticity of true quadratic integrals over affine images of an
arbitrary fixed compact four-dimensional reference domain. -/
noncomputable section
namespace D4.ParameterAnalytic
open Analytic Principal Matrix MeasureTheory Set
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem affineImage_integral (S : Set Vec) (B : Gram) (hB : B.det ≠ 0)
    (c : Vec) (f : Vec → ℝ) :
    (∫ y in (fun x => c+B*ᵥx) '' S,f y)=|B.det| *(∫ x in S,f (c+B*ᵥx)) := by
  have h := setIntegral_map_equiv (μ := (volume : Measure Vec))
    (affineMeasurableEquiv B hB c) f ((fun x => c+B*ᵥx) '' S)
  change (∫ y in (fun x => c+B*ᵥx) '' S,f y ∂Measure.map (fun x => c+B*ᵥx) volume)=
    (∫ x in (fun x => c+B*ᵥx) ⁻¹' ((fun x => c+B*ᵥx) '' S),f (c+B*ᵥx)) at h
  have hp : (fun x => c+B*ᵥx) ⁻¹' ((fun x => c+B*ᵥx) '' S)=S :=
    (affineMeasurableEquiv B hB c).injective.preimage_image S
  rw [map_affine_volume B hB c,Measure.restrict_smul,integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _)),smul_eq_mul,hp] at h
  calc
    _ = |B.det| *(|B.det|⁻¹*(∫ y in (fun x => c+B*ᵥx) '' S,f y)) := by
      rw [← mul_assoc,mul_inv_cancel₀ (abs_ne_zero.mpr hB),one_mul]
    _ = _ := by rw [h]

theorem integral_prod_sum_vec (S : Set Vec) (hS : IsCompact S)
    (m k : ℕ) (a : P → Fin m → Fin k → ℝ)
    (b : Fin m → Fin k → Vec → ℝ) (p₀ : P)
    (ha : ∀ j i, AnalyticAt ℝ (fun p => a p j i) p₀)
    (hb : ∀ j i, Continuous (b j i)) :
    AnalyticAt ℝ (fun p => ∫ x in S,
      ∏ j : Fin m, ∑ i : Fin k, a p j i*b j i x) p₀ := by
  have he (p : P) (x : Vec) :
      (∏ j : Fin m, ∑ i : Fin k, a p j i*b j i x) =
        ∑ f : Fin m → Fin k, (∏ j : Fin m, a p j (f j)) *
          (∏ j : Fin m, b j (f j) x) := by
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro f _
    exact Finset.prod_mul_distrib
  have hb' (f : Fin m → Fin k) : Continuous (fun x => ∏ j : Fin m, b j (f j) x) :=
    continuous_finset_prod _ (fun j _ => hb j (f j))
  have heq (p : P) : (∫ x in S, ∏ j : Fin m, ∑ i : Fin k, a p j i*b j i x)=
      ∑ f : Fin m → Fin k, (∏ j : Fin m, a p j (f j)) *
        (∫ x in S, ∏ j : Fin m, b j (f j) x) := by
    simp_rw [he]
    rw [integral_finset_sum _ (fun f _ =>
      ((hb' f).continuousOn.integrableOn_compact hS).const_mul _)]
    simp only [integral_const_mul]
  simp_rw [heq]
  apply Finset.analyticAt_sum
  intro f _
  exact (Finset.analyticAt_prod _ (fun j _ => ha j (f j))).mul analyticAt_const

private def coordinateCoefficients (B : Gram) (c : Vec) (i : Fin 4) : Fin 5 → ℝ :=
  Fin.cons (c i) (B i)
private def coordinateBasis (x : Vec) : Fin 5 → ℝ := Fin.cons 1 x

private theorem coordinate_expansion (B : Gram) (c x : Vec) (i : Fin 4) :
    c i+(B*ᵥx) i=∑ k : Fin 5,coordinateCoefficients B c i k*coordinateBasis x k := by
  simp only [Fin.sum_univ_succ,coordinateCoefficients,coordinateBasis,Fin.cons_zero,
    Fin.cons_succ,mul_one,Matrix.mulVec,dotProduct]

private theorem integral_coordinate_product (S : Set Vec) (hS : IsCompact S)
    (B : P → Gram) (c : P → Vec) (p₀ : P)
    (hB : ∀ i j,AnalyticAt ℝ (fun p => B p i j) p₀)
    (hc : ∀ i,AnalyticAt ℝ (fun p => c p i) p₀) (i j : Fin 4) :
    AnalyticAt ℝ (fun p => ∫ x in S,
      (c p i+(B p*ᵥx) i)*(c p j+(B p*ᵥx) j)) p₀ := by
  simp_rw [coordinate_expansion]
  have h := integral_prod_sum_vec S hS 2 5
    (fun p k l => coordinateCoefficients (B p) (c p) (![i,j] k) l)
    (fun _ l x => coordinateBasis x l) p₀ ?_ ?_
  · simpa only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using h
  · intro k l
    refine Fin.cases ?_ (fun l => ?_) l
    · exact hc (![i,j] k)
    · exact hB (![i,j] k) l
  · intro k l
    refine Fin.cases ?_ (fun l => ?_) l
    · exact continuous_const
    · exact continuous_apply l

theorem integral_quadratic_affine_reference (S : Set Vec) (hS : IsCompact S)
    (Q B : P → Gram) (c : P → Vec) (p₀ : P)
    (hQ : ∀ i j,AnalyticAt ℝ (fun p => Q p i j) p₀)
    (hB : ∀ i j,AnalyticAt ℝ (fun p => B p i j) p₀)
    (hc : ∀ i,AnalyticAt ℝ (fun p => c p i) p₀) :
    AnalyticAt ℝ (fun p => ∫ x in S,Analytic.quadratic (Q p) (c p+B p*ᵥx)) p₀ := by
  have he (p : P) (x : Vec) : Analytic.quadratic (Q p) (c p+B p*ᵥx)=
      ∑ i : Fin 4,∑ j : Fin 4,Q p i j*((c p i+(B p*ᵥx) i)*(c p j+(B p*ᵥx) j)) := by
    simp only [Analytic.quadratic,dotProduct,Matrix.mulVec,Pi.add_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  have hi (p : P) (i j : Fin 4) :
      IntegrableOn (fun x => Q p i j*((c p i+(B p*ᵥx) i)*(c p j+(B p*ᵥx) j))) S := by
    refine (show Continuous _ from ?_).continuousOn.integrableOn_compact hS
    unfold Matrix.mulVec dotProduct
    fun_prop
  simp_rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi _ i j)),
    integral_finset_sum _ (fun j _ => hi _ _ j),integral_const_mul]
  apply Finset.analyticAt_sum
  intro i _
  apply Finset.analyticAt_sum
  intro j _
  exact (hQ i j).mul (integral_coordinate_product S hS B c p₀ hB hc i j)

theorem integral_affineImage_quadratic (S : Set Vec) (hS : IsCompact S)
    (Q B : P → Gram) (c : P → Vec) (p₀ : P)
    (hQ : ∀ i j,AnalyticAt ℝ (fun p => Q p i j) p₀)
    (hB : ∀ i j,AnalyticAt ℝ (fun p => B p i j) p₀)
    (hc : ∀ i,AnalyticAt ℝ (fun p => c p i) p₀) (hdet : (B p₀).det ≠ 0) :
    AnalyticAt ℝ (fun p => ∫ x in (fun y => c p+B p*ᵥy) '' S,
      Analytic.quadratic (Q p) x) p₀ := by
  have hd := matrix_det B p₀ hB
  have ha : AnalyticAt ℝ (fun p => |(B p).det|) p₀ := by
    rcases lt_or_gt_of_ne hdet with hn|hp
    · apply hd.neg.congr
      filter_upwards [hd.continuousAt.eventually_lt_const hn] with p h
      exact (abs_of_neg h).symm
    · apply hd.congr
      filter_upwards [hd.continuousAt.eventually_const_lt hp] with p h
      exact (abs_of_pos h).symm
  apply (ha.mul (integral_quadratic_affine_reference S hS Q B c p₀ hQ hB hc)).congr
  filter_upwards [hd.continuousAt.eventually_ne hdet] with p hp
  exact (affineImage_integral S (B p) hp (c p) _).symm

end D4.ParameterAnalytic
