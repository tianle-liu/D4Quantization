import D4.C23LocalAnalyticC3
import D4.ParameterAreaAnalytic
import Mathlib.Analysis.Analytic.Linear

/-! Joint analyticity of the actual C₂/C₃ local negative integral, including
variation of the tangential parameters and the rectangular neighborhood. -/
noncomputable section
namespace D4.C23Local
open Set Matrix MeasureTheory Filter Topology AreaEnvelope

attribute [local fun_prop] analyticAt_fst analyticAt_snd

abbrev JointTriple := ℝ × ℝ × ℝ

theorem localTrapezoid3_joint_analytic (α β η : ℝ) (i : Fin 7) (k : Fin 6) :
    AnalyticAt ℝ (fun p : JointTriple =>
      (localTrapezoid3 (p.1-p.2.2) (p.2.1-p.2.2) η (η+p.2.2) i).coordinate k)
      (α,β,0) := by
  fin_cases i <;> fin_cases k <;>
    dsimp [localTrapezoid3,Trapezoid.coordinate,Trapezoid.ofAffine] <;> fun_prop

theorem localDistance3_joint_analytic (α β : ℝ) (i : Fin 7) (j : Fin 3) :
    AnalyticAt ℝ (fun p : JointTriple =>
      localDistance3 (p.1-p.2.2) (p.2.1-p.2.2) i j) (α,β,0) := by
  fin_cases i <;> fin_cases j
  · change AnalyticAt ℝ (fun p : JointTriple => -(0:ℝ)-(0:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(0:ℝ)-(0:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(0:ℝ)-(0:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(0:ℝ)-(0:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(1:ℝ)-(0:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(0:ℝ)-(0:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(0:ℝ)-(0:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(0:ℝ)-(0:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(1:ℝ)-(0:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(0:ℝ)-(p.1-p.2.2:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(0:ℝ)-(-1:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(0:ℝ)-(0:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(0:ℝ)-(p.2.1-p.2.2:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(0:ℝ)-(0:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(0:ℝ)-(-1:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(0:ℝ)-(p.2.1-p.2.2:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(1:ℝ)-(0:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(0:ℝ)-(-1:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(0:ℝ)-(p.1-p.2.2:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(0:ℝ)-(-1:ℝ)) (α,β,0)
    fun_prop
  · change AnalyticAt ℝ (fun p : JointTriple => -(1:ℝ)-(0:ℝ)) (α,β,0)
    fun_prop

theorem localRegion3_joint_positive (α β η : ℝ)
    (hα : 0<α) (hβ : 0<β) (hη : 0<η) :
    ∀ᶠ p : JointTriple in nhds (α,β,0),
      0<p.1-p.2.2 ∧ 0<p.2.1-p.2.2 ∧ 0<η+p.2.2 := by
  have h1 : ContinuousAt (fun p : JointTriple => p.1-p.2.2) (α,β,0) := by fun_prop
  have h2 : ContinuousAt (fun p : JointTriple => p.2.1-p.2.2) (α,β,0) := by fun_prop
  have h3 : ContinuousAt (fun p : JointTriple => η+p.2.2) (α,β,0) := by fun_prop
  filter_upwards [h1.eventually_const_lt (by simpa using hα),
    h2.eventually_const_lt (by simpa using hβ),h3.eventually_const_lt (by simpa using hη)]
    with p hp1 hp2 hp3
  exact ⟨hp1,hp2,hp3⟩

theorem localRegion3_joint_integral_analytic (α β η R : ℝ)
    (hα : 0<α) (hβ : 0<β) (hη : 0<η) (i : Fin 7) :
    AnalyticAt ℝ (fun p : JointTriple =>
      ∫ x in localRegion3 (p.1-p.2.2) (p.2.1-p.2.2) η (η+p.2.2) i,
        4*R^2*affineEval (localLower3 i) x + squareNegativePolynomial R
          (p.2.2-affineEval (localDistance3 (p.1-p.2.2) (p.2.1-p.2.2) i) x))
      (α,β,0) := by
  have hv : (localTrapezoid3 (α-0) (β-0) η (η+0) i).Valid :=
    localTrapezoid3_valid _ _ _ _ (by simpa using hα) (by simpa using hβ)
      hη (by simpa using hη) i
  by_cases hs : localSwap3 i
  · have ha := ParameterArea.negative_swapped_trapezoid R (fun _ => localLower3 i)
      (fun p : JointTriple => localDistance3 (p.1-p.2.2) (p.2.1-p.2.2) i)
      (fun p : JointTriple => localTrapezoid3 (p.1-p.2.2) (p.2.1-p.2.2) η (η+p.2.2) i)
      (fun p : JointTriple => p.2.2) (α,β,0) (fun _ => analyticAt_const)
      (localDistance3_joint_analytic α β i) (localTrapezoid3_joint_analytic α β η i)
      (by fun_prop) hv
    apply ha.congr
    filter_upwards [localRegion3_joint_positive α β η hα hβ hη] with p hp
    rw [localRegion3_eq_trapezoid _ _ _ _ hp.1 hp.2.1 hη hp.2.2 i,if_pos hs]
  · have ha := ParameterArea.negative_trapezoid R (fun _ => localLower3 i)
      (fun p : JointTriple => localDistance3 (p.1-p.2.2) (p.2.1-p.2.2) i)
      (fun p : JointTriple => localTrapezoid3 (p.1-p.2.2) (p.2.1-p.2.2) η (η+p.2.2) i)
      (fun p : JointTriple => p.2.2) (α,β,0) (fun _ => analyticAt_const)
      (localDistance3_joint_analytic α β i) (localTrapezoid3_joint_analytic α β η i)
      (by fun_prop) hv
    apply ha.congr
    filter_upwards [localRegion3_joint_positive α β η hα hβ hη] with p hp
    rw [localRegion3_eq_trapezoid _ _ _ _ hp.1 hp.2.1 hη hp.2.2 i,if_neg hs]

theorem correction3_negative_rectangle_joint_analytic (α β η R : ℝ)
    (hα : 0<α) (hβ : 0<β) (hη : 0<η) :
    AnalyticAt ℝ (fun p : JointTriple =>
      negativeAreaIntegral (localRectangle3 p.1 p.2.1 η η) R lower3
        (gap3 (p.1-p.2.2) (p.2.1-p.2.2)) p.2.2) (α,β,0) := by
  have ha := Finset.analyticAt_sum Finset.univ fun i _ =>
    localRegion3_joint_integral_analytic α β η R hα hβ hη i
  have hconst : AnalyticAt ℝ (fun _ : JointTriple => (15/4:ℝ)) (α,β,0) := analyticAt_const
  apply (hconst.mul ha).congr
  filter_upwards [localRegion3_joint_positive α β η hα hβ hη] with p hp
  have hc : (⋃ i : Fin 7,localRegion3 (p.1-p.2.2) (p.2.1-p.2.2) η (η+p.2.2) i)=
      localRectangle3 p.1 p.2.1 η η := by
    rw [localRegion3_cover _ _ _ _ hp.1.le hp.2.1.le hη.le hp.2.2.le]
    have he : (![(p.1-p.2.2)+(η+p.2.2),(p.2.1-p.2.2)+(η+p.2.2)] : Plane)=
        ![p.1+η,p.2.1+η] := by
      ext j
      fin_cases j
      · change (p.1-p.2.2)+(η+p.2.2)=p.1+η
        ring
      · change (p.2.1-p.2.2)+(η+p.2.2)=p.2.1+η
        ring
    exact congrArg (fun y : Plane => Icc (![-η,-η] : Plane) y) he
  let f := fun x : Plane => 4*R^2*lower3 x +
    squareNegativePolynomial R (p.2.2-gap3 (p.1-p.2.2) (p.2.1-p.2.2) x)
  have hf : Continuous f := by
    have hu : Continuous lower3 := by unfold lower3 min3; fun_prop
    have hd := gap3_continuous (p.1-p.2.2) (p.2.1-p.2.2)
    unfold f squareNegativePolynomial
    fun_prop
  have hi : IntegrableOn f
      (⋃ i : Fin 7,localRegion3 (p.1-p.2.2) (p.2.1-p.2.2) η (η+p.2.2) i) := by
    rw [hc]
    exact hf.continuousOn.integrableOn_compact isCompact_Icc
  change (15/4:ℝ)*(∑ i : Fin 7,_) = negativeAreaIntegral _ _ _ _ _
  unfold negativeAreaIntegral
  congr 1
  rw [← hc,integral_iUnion_ae
    (fun i => (localRegion3_compact _ _ _ _ hp.1 hp.2.1 hη hp.2.2 i).measurableSet.nullMeasurableSet)
    (localRegion3_pairwise_null _ _ _ _ hp.1.le hp.2.1.le) hi,tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  apply setIntegral_congr_fun
    (localRegion3_compact _ _ _ _ hp.1 hp.2.1 hη hp.2.2 i).measurableSet
  intro x hx
  obtain ⟨hu,hv⟩ := localRegion3_affine _ _ _ _ hp.1.le hp.2.1.le i x hx
  dsimp only [f]
  rw [localDistance3_eval]
  unfold gap3
  rw [hu,hv]

end D4.C23Local
