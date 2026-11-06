import D4.C23WindowBox
import D4.C23WindowPartition
import D4.C23WindowQuadratic

noncomputable section
namespace D4.C23Local
open Matrix MeasureTheory Set Analytic AreaEnvelope Principal
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem localWindow3_congr_lower (Q : Gram) (U V : Plane→ℝ) (K : Set Plane) (R : ℝ)
    (h : ∀L∈K,U L=V L) : localWindow3 Q U K R=localWindow3 Q V K R := by
  apply Set.image_congr
  intro p hp
  simp only [windowPoint3,fiberCoordinates,h p.1 hp.1]

theorem localWindow3_quadratic_joint_fixed (Q : P→Gram) (p₀ : P)
    (hQ : ∀i j,AnalyticAt ℝ (fun p=>Q p i j) p₀) (hd : (Q p₀).det≠0)
    (U : Plane→ℝ) (hU : Continuous U) (K : Set Plane) (hK : IsCompact K) (R : ℝ) :
    AnalyticAt ℝ (fun p=>∫r in localWindow3 (Q p) U K R,quadratic (Q p)⁻¹ r/4) p₀ := by
  have he (p : P) : (∫r in localWindow3 (Q p) U K R,quadratic (Q p)⁻¹ r/4)=
      (∫x in referenceWindow K R,
        quadratic (Q p)⁻¹ (inverseCoordinates3 (Q p) 0+windowPoint3 0 U x))/4 := by
    rw [localWindow3_integral _ U hU,integral_div]
    congr 1
    apply setIntegral_congr_fun (hK.prod (isCompact_Icc.prod isCompact_Icc)).measurableSet
    intro x _
    exact congrArg (quadratic (Q p)⁻¹) (windowPoint3_shift (Q p) U x)
  simp_rw [he]
  apply AnalyticAt.div _ analyticAt_const (by norm_num : (4:ℝ)≠0)
  apply ParameterAnalytic.integral_quadratic_shift (referenceWindow K R)
    (hK.prod (isCompact_Icc.prod isCompact_Icc)) (windowPoint3 0 U)
    (windowPoint3_continuous 0 hU) (fun p=>(Q p)⁻¹)
    (fun p=>inverseCoordinates3 (Q p) 0) p₀ (ParameterAnalytic.matrix_inv Q p₀ hQ hd)
  intro i
  fin_cases i <;> norm_num [inverseCoordinates3,Fin.reduceFinMk,Matrix.cons_val]
  · exact (hQ 0 0).neg
  · exact (hQ 1 1).neg
  · exact hQ 2 2
  · exact hQ 3 3

theorem localWindow3_quadratic_joint_rectangle (Q : P→Gram) (lo hi : P→Plane)
    (u : Fin 3→ℝ) (R : ℝ) (p₀ : P)
    (hQ : ∀i j,AnalyticAt ℝ (fun p=>Q p i j) p₀)
    (hl : ∀i,AnalyticAt ℝ (fun p=>lo p i) p₀)
    (hh : ∀i,AnalyticAt ℝ (fun p=>hi p i) p₀)
    (hHerm : ∀p,(Q p).IsHermitian) (hd : (Q p₀).det≠0)
    (hlo : ∀i,lo p₀ i<hi p₀ i) (hR : 0<R) :
    AnalyticAt ℝ (fun p=>∫r in localWindow3 (Q p) (rectangleLower u)
      (Icc (lo p) (hi p)) R,quadratic (Q p)⁻¹ r/4) p₀ := by
  have hw (i : Fin 2) : AnalyticAt ℝ (fun p=>(hi p i-lo p i)/2) p₀ :=
    ((hh i).sub (hl i)).div analyticAt_const (by norm_num : (2:ℝ)≠0)
  have hm (i : Fin 2) : AnalyticAt ℝ (fun p=>(hi p i+lo p i)/2) p₀ :=
    ((hh i).add (hl i)).div analyticAt_const (by norm_num : (2:ℝ)≠0)
  have hb : ∀i j,AnalyticAt ℝ (fun p=>rectangleMatrix (lo p) (hi p) R u i j) p₀ := by
    intro i j
    fin_cases i <;> fin_cases j
    all_goals first
      | exact analyticAt_const
      | exact hw 0
      | exact hw 1
      | exact analyticAt_const.mul (hw 0)
      | exact analyticAt_const.mul (hw 1)
  have hc : ∀i,AnalyticAt ℝ (fun p=>rectangleCenter (Q p) (lo p) (hi p) u i) p₀ := by
    intro i
    fin_cases i
    · exact (hm 0).sub (hQ 0 0)
    · exact (hm 1).sub (hQ 1 1)
    · exact (((hQ 2 2).sub analyticAt_const).sub
        (analyticAt_const.mul (hm 0))).sub (analyticAt_const.mul (hm 1))
    · exact (((hQ 3 3).sub analyticAt_const).sub
        (analyticAt_const.mul (hm 0))).sub (analyticAt_const.mul (hm 1))
  have hbd : (rectangleMatrix (lo p₀) (hi p₀) R u).det≠0 := by
    rw [rectangleMatrix_det]
    exact ne_of_gt (div_pos (mul_pos (mul_pos (sub_pos.mpr (hlo 0))
      (sub_pos.mpr (hlo 1))) (sq_pos_of_pos hR)) (by norm_num))
  have ha := ParameterAnalytic.integral_parallelotope_quadratic (fun p=>(Q p)⁻¹)
    (fun p=>rectangleMatrix (lo p) (hi p) R u)
    (fun p=>rectangleCenter (Q p) (lo p) (hi p) u) p₀
    (ParameterAnalytic.matrix_inv Q p₀ hQ hd) hb hc (fun p=>(hHerm p).inv) hbd
  apply (ha.div analyticAt_const (by norm_num : (4:ℝ)≠0)).congr
  have he : ∀ᶠp in nhds p₀,∀i,lo p i<hi p i := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((hl i).continuousAt.sub (hh i).continuousAt).eventually_lt_const
      (show lo p₀ i-hi p₀ i<0 by linarith [hlo i]) |>.mono fun p hp=>by linarith
  filter_upwards [he] with p hp
  rw [localWindow3_rectangle_parallelotope (Q p) (lo p) (hi p) R u hp hR,integral_div]
  rfl

def quadrantLower (i : Fin 2×Fin 2) : Plane→ℝ :=
  if i=(0,0) then lower3 else
    rectangleLower ![0,if i.1=0 then 1 else 0,if i.2=0 then 1 else 0]

theorem quadrant_lower_eq (α β η : ℝ) (i : Fin 2×Fin 2) :
    ∀L∈quadrant α β η i,lower3 L=quadrantLower i L := by
  rintro L ⟨hl,hh⟩
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j
  · rfl
  · have a:=hh 0; have b:=hl 1
    simp [quadrantLo,quadrantHi] at a b
    simp [quadrantLower,lower3,min3,rectangleLower,min_eq_right a,min_eq_left (by linarith : L 0≤L 1)]
  · have a:=hl 0; have b:=hh 1
    simp [quadrantLo,quadrantHi] at a b
    simp [quadrantLower,lower3,min3,rectangleLower,min_eq_right (by linarith : L 1≤L 0),min_eq_right b]
  · have a:=hl 0; have b:=hl 1
    simp [quadrantLo,quadrantHi] at a b
    simp [quadrantLower,lower3,min3,rectangleLower,le_min_iff,a,b]

theorem localWindow3_quadratic_joint_moving (Q : P→Gram) (α β : P→ℝ)
    (η R : ℝ) (p₀ : P)
    (hQ : ∀i j,AnalyticAt ℝ (fun p=>Q p i j) p₀)
    (hα : AnalyticAt ℝ α p₀) (hβ : AnalyticAt ℝ β p₀)
    (hHerm : ∀p,(Q p).IsHermitian) (hd : (Q p₀).det≠0)
    (ha : 0<α p₀) (hb : 0<β p₀) (hη : 0<η) (hR : 0<R) :
    AnalyticAt ℝ (fun p=>∫r in localWindow3 (Q p) lower3
      (localRectangle3 (α p) (β p) η η) R,quadratic (Q p)⁻¹ r/4) p₀ := by
  have hi (i : Fin 2×Fin 2) : AnalyticAt ℝ (fun p=>∫r in
      localWindow3 (Q p) (quadrantLower i) (quadrant (α p) (β p) η i) R,
        quadratic (Q p)⁻¹ r/4) p₀ := by
    by_cases hi : i=(0,0)
    · subst i
      exact localWindow3_quadratic_joint_fixed Q p₀ hQ hd lower3
        (by unfold lower3 min3; fun_prop) (Icc ![-η,-η] ![0,0]) isCompact_Icc R
    · simp only [quadrantLower,if_neg hi,quadrant]
      apply localWindow3_quadratic_joint_rectangle Q (fun _=>quadrantLo η i)
        (fun p=>quadrantHi (α p) (β p) η i) _ R p₀ hQ
      · intro k; exact analyticAt_const
      · intro k
        rcases i with ⟨i,j⟩
        fin_cases k <;> fin_cases i <;> fin_cases j <;>
          simp only [quadrantHi,Matrix.cons_val,Fin.reduceFinMk,ite_true,ite_false]
        all_goals first | exact analyticAt_const | exact hα.add analyticAt_const | exact hβ.add analyticAt_const
      · exact hHerm
      · exact hd
      · intro k
        rcases i with ⟨i,j⟩
        fin_cases k <;> fin_cases i <;> fin_cases j <;>
          simp [quadrantLo,quadrantHi] <;> linarith
      · exact hR
  apply (Finset.analyticAt_sum Finset.univ fun i _=>hi i).congr
  filter_upwards [hα.continuousAt.eventually_const_lt ha,
    hβ.continuousAt.eventually_const_lt hb] with p hpα hpβ
  change _=(∫r in localWindow3 (Q p) lower3 (Icc ![-η,-η] ![α p+η,β p+η]) R,quadratic (Q p)⁻¹ r/4)
  rw [localWindow3_integral_partition (Q p) lower3 (by unfold lower3 min3; fun_prop)
    _ isCompact_Icc (quadrant (α p) (β p) η) (fun _=>isCompact_Icc)
    (quadrant_cover _ _ _ hpα.le hpβ.le hη.le) (quadrant_pairwise_null _ _ _) R
    (fun r=>quadratic (Q p)⁻¹ r/4) (by unfold quadratic; fun_prop)]
  apply Finset.sum_congr rfl
  intro i _
  rw [localWindow3_congr_lower (Q p) lower3 (quadrantLower i) _ R (quadrant_lower_eq _ _ _ i)]

end D4.C23Local
