import D4.C23LocalTrapezoidsC3
import D4.C23LocalPartitionNullC3

/-! The actual negative local integral for the C₂/C₃ path is analytic on a
fixed rectangular neighborhood. Its seven concrete regions are triangulated. -/
noncomputable section
namespace D4.C23Local
open Set Matrix MeasureTheory Filter Topology AreaEnvelope

def localDistance3 (A B : ℝ) (i : Fin 7) : Fin 3 → ℝ :=
  fun j => -localLower3 i j-localUpper3 A B i j

theorem localDistance3_eval (A B : ℝ) (i : Fin 7) (x : Plane) :
    affineEval (localDistance3 A B i) x=
      -affineEval (localLower3 i) x-affineEval (localUpper3 A B i) x := by
  simp only [affineEval_eq,localDistance3]
  ring

theorem localRegion3_compact (A B η ρ : ℝ) (hA : 0<A) (hB : 0<B)
    (hη : 0<η) (hρ : 0<ρ) (i : Fin 7) : IsCompact (localRegion3 A B η ρ i) := by
  rw [localRegion3_eq_trapezoid A B η ρ hA hB hη hρ i]
  split_ifs
  · apply ((localTrapezoid3 A B η ρ i).compact (localTrapezoid3_valid A B η ρ hA hB hη hρ i)).image
    apply continuous_pi
    intro j
    fin_cases j
    · simpa only [planeSwap_zero] using (continuous_apply 1 : Continuous (fun x : Plane => x 1))
    · simpa only [planeSwap_one] using (continuous_apply 0 : Continuous (fun x : Plane => x 0))
  · exact (localTrapezoid3 A B η ρ i).compact (localTrapezoid3_valid A B η ρ hA hB hη hρ i)

theorem localTrapezoid3_path_analytic (α β η : ℝ) (i : Fin 7) (k : Fin 6) :
    AnalyticAt ℝ (fun t => (localTrapezoid3 (α-t) (β-t) η (η+t) i).coordinate k) 0 := by
  fin_cases i <;> fin_cases k <;>
    dsimp [localTrapezoid3,Trapezoid.coordinate,Trapezoid.ofAffine] <;> fun_prop

theorem localDistance3_path_analytic (α β : ℝ) (i : Fin 7) (j : Fin 3) :
    AnalyticAt ℝ (fun t => localDistance3 (α-t) (β-t) i j) 0 := by
  fin_cases i <;> fin_cases j
  · change AnalyticAt ℝ (fun t : ℝ => -(0:ℝ)-(0:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(0:ℝ)-(0:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(0:ℝ)-(0:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(0:ℝ)-(0:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(1:ℝ)-(0:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(0:ℝ)-(0:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(0:ℝ)-(0:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(0:ℝ)-(0:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(1:ℝ)-(0:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(0:ℝ)-(α-t:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(0:ℝ)-(-1:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(0:ℝ)-(0:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(0:ℝ)-(β-t:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(0:ℝ)-(0:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(0:ℝ)-(-1:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(0:ℝ)-(β-t:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(1:ℝ)-(0:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(0:ℝ)-(-1:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(0:ℝ)-(α-t:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(0:ℝ)-(-1:ℝ)) 0
    fun_prop
  · change AnalyticAt ℝ (fun t : ℝ => -(1:ℝ)-(0:ℝ)) 0
    fun_prop

theorem localRegion3_path_positive (α β η : ℝ) (hα : 0<α) (hβ : 0<β) (hη : 0<η) :
    ∀ᶠ t : ℝ in nhds 0,0<α-t ∧ 0<β-t ∧ 0<η+t := by
  have h1 : ContinuousAt (fun t : ℝ => α-t) 0 := by fun_prop
  have h2 : ContinuousAt (fun t : ℝ => β-t) 0 := by fun_prop
  have h3 : ContinuousAt (fun t : ℝ => η+t) 0 := by fun_prop
  filter_upwards [h1.eventually_const_lt (by simpa using hα),
    h2.eventually_const_lt (by simpa using hβ),h3.eventually_const_lt (by simpa using hη)] with t h1 h2 h3
  exact ⟨h1,h2,h3⟩

theorem localRegion3_path_integral_analytic (α β η R : ℝ)
    (hα : 0<α) (hβ : 0<β) (hη : 0<η) (i : Fin 7) :
    AnalyticAt ℝ (fun t => ∫ x in localRegion3 (α-t) (β-t) η (η+t) i,
      4*R^2*affineEval (localLower3 i) x+
        squareNegativePolynomial R (t-affineEval (localDistance3 (α-t) (β-t) i) x)) 0 := by
  have hv : (localTrapezoid3 (α-0) (β-0) η (η+0) i).Valid :=
    localTrapezoid3_valid _ _ _ _ (by simpa using hα) (by simpa using hβ) hη (by simpa using hη) i
  by_cases hs : localSwap3 i
  · have ha := analyticAt_negativeSwappedTrapezoidIntegral R (fun _ => localLower3 i)
      (fun t => localDistance3 (α-t) (β-t) i)
      (fun t => localTrapezoid3 (α-t) (β-t) η (η+t) i) 0
      (fun _ => analyticAt_const) (localDistance3_path_analytic α β i)
      (localTrapezoid3_path_analytic α β η i) hv
    apply ha.congr
    filter_upwards [localRegion3_path_positive α β η hα hβ hη] with t ht
    rw [localRegion3_eq_trapezoid _ _ _ _ ht.1 ht.2.1 hη ht.2.2 i,if_pos hs]
  · have ha := analyticAt_negativeTrapezoidIntegral R (fun _ => localLower3 i)
      (fun t => localDistance3 (α-t) (β-t) i)
      (fun t => localTrapezoid3 (α-t) (β-t) η (η+t) i) 0
      (fun _ => analyticAt_const) (localDistance3_path_analytic α β i)
      (localTrapezoid3_path_analytic α β η i) hv
    apply ha.congr
    filter_upwards [localRegion3_path_positive α β η hα hβ hη] with t ht
    rw [localRegion3_eq_trapezoid _ _ _ _ ht.1 ht.2.1 hη ht.2.2 i,if_neg hs]

theorem correction3_negative_rectangle_analytic (α β η R : ℝ)
    (hα : 0<α) (hβ : 0<β) (hη : 0<η) :
    AnalyticAt ℝ (fun t => negativeAreaIntegral (localRectangle3 α β η η)
      R lower3 (gap3 (α-t) (β-t)) t) 0 := by
  have ha := Finset.analyticAt_sum Finset.univ fun i _ =>
    localRegion3_path_integral_analytic α β η R hα hβ hη i
  have hconst : AnalyticAt ℝ (fun _ : ℝ => (15/4:ℝ)) 0 := analyticAt_const
  apply (hconst.mul ha).congr
  filter_upwards [localRegion3_path_positive α β η hα hβ hη] with t ht
  have hc : (⋃ i : Fin 7,localRegion3 (α-t) (β-t) η (η+t) i)=localRectangle3 α β η η := by
    rw [localRegion3_cover _ _ _ _ ht.1.le ht.2.1.le hη.le ht.2.2.le]
    have he : (![(α-t)+(η+t),(β-t)+(η+t)] : Plane)=![α+η,β+η] := by
      ext j
      fin_cases j
      · change (α-t)+(η+t)=α+η
        ring
      · change (β-t)+(η+t)=β+η
        ring
    exact congrArg (fun y : Plane => Icc (![-η,-η] : Plane) y) he
  let f := fun x : Plane => 4*R^2*lower3 x+squareNegativePolynomial R (t-gap3 (α-t) (β-t) x)
  have hf : Continuous f := by
    have hu : Continuous lower3 := by unfold lower3 min3; fun_prop
    have hd := gap3_continuous (α-t) (β-t)
    unfold f squareNegativePolynomial
    fun_prop
  have hi : IntegrableOn f (⋃ i : Fin 7,localRegion3 (α-t) (β-t) η (η+t) i) := by
    rw [hc]
    exact hf.continuousOn.integrableOn_compact isCompact_Icc
  change (15/4:ℝ)*(∑ i : Fin 7,_) = negativeAreaIntegral _ _ _ _ _
  unfold negativeAreaIntegral
  congr 1
  rw [← hc,integral_iUnion_ae
    (fun i => (localRegion3_compact _ _ _ _ ht.1 ht.2.1 hη ht.2.2 i).measurableSet.nullMeasurableSet)
    (localRegion3_pairwise_null _ _ _ _ ht.1.le ht.2.1.le) hi,tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  apply setIntegral_congr_fun (localRegion3_compact _ _ _ _ ht.1 ht.2.1 hη ht.2.2 i).measurableSet
  intro x hx
  obtain ⟨hu,hv⟩ := localRegion3_affine _ _ _ _ ht.1.le ht.2.1.le i x hx
  dsimp only [f]
  rw [localDistance3_eval]
  unfold gap3
  rw [hu,hv]

end D4.C23Local
