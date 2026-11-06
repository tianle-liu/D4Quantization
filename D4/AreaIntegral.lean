import D4.AreaLayerCake

/-! Actual square and polygon integrals in the area-integral lemma. -/
noncomputable section
namespace D4.AreaEnvelope
open MeasureTheory Set

abbrev Plane := Fin 2 → ℝ

def areaIntegral (K : Set Plane) (R : ℝ) (U d : Plane → ℝ) (t : ℝ) : ℝ :=
  (15/4 : ℝ) * ∫ x in K, ∫ p in Icc (-R) R ×ˢ Icc (-R) R,
    U x + min (min 0 p.1) (min p.2 (p.1+p.2+t-d x))

def negativeAreaIntegral (K : Set Plane) (R : ℝ) (U d : Plane → ℝ) (t : ℝ) : ℝ :=
  (15/4 : ℝ) * ∫ x in K, 4*R^2*U x + squareNegativePolynomial R (t-d x)

theorem squareIntegral_add_constant (R δ u : ℝ) (hR : 0 ≤ R) :
    (∫ p in Icc (-R) R ×ˢ Icc (-R) R,
      u + min (min 0 p.1) (min p.2 (p.1+p.2+δ))) =
    4*R^2*u + squareEnvelope R δ := by
  have hc : Continuous (fun p : ℝ × ℝ => min (min 0 p.1) (min p.2 (p.1+p.2+δ))) := by fun_prop
  rw [integral_add
    (continuous_const.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)),
    ← squareEnvelope_eq_squareIntegral R δ hR,setIntegral_const]
  congr 1
  change ((volume : Measure (ℝ × ℝ)) (Icc (-R) R ×ˢ Icc (-R) R)).toReal * u = _
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,Measure.prod_prod]
  simp only [Real.volume_Icc,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ R - -R),smul_eq_mul]
  ring

theorem areaIntegral_positivePart (K : Set Plane) (hK : IsCompact K) (R : ℝ) (hR : 0 ≤ R)
    (U d : Plane → ℝ) (hU : ContinuousOn U K) (hd : ContinuousOn d K) (t : ℝ)
    (hb : ∀ x ∈ K, |t-d x| ≤ R) :
    areaIntegral K R U d t - negativeAreaIntegral K R U d t =
      (5/8 : ℝ) * ∫ x in K, (max (t-d x) 0)^3 := by
  let P := fun x => 4*R^2*U x + squareNegativePolynomial R (t-d x)
  let C := fun x => (max (t-d x) 0)^3/6
  have hP : IntegrableOn P K := by
    refine (show ContinuousOn P K from ?_).integrableOn_compact hK
    dsimp [P,squareNegativePolynomial]
    exact ((continuousOn_const.mul hU).add
      (((continuousOn_const.add (continuousOn_const.mul (continuousOn_const.sub hd))).sub
        (continuousOn_const.mul ((continuousOn_const.sub hd).pow 2))).add
          (((continuousOn_const.sub hd).pow 3).div_const 6)))
  have hC : IntegrableOn C K := by
    refine (show ContinuousOn C K from ?_).integrableOn_compact hK
    exact (((continuousOn_const.sub hd).sup continuousOn_const).pow 3).div_const 6
  have he : areaIntegral K R U d t = (15/4 : ℝ) * ∫ x in K, P x + C x := by
    unfold areaIntegral
    congr 1
    apply setIntegral_congr_fun hK.measurableSet
    intro x hx
    dsimp only
    rw [show (fun p : ℝ × ℝ => U x + min (min 0 p.1) (min p.2 (p.1+p.2+t-d x))) =
        (fun p => U x + min (min 0 p.1) (min p.2 (p.1+p.2+(t-d x)))) by
      funext p; congr 3 <;> ring,
      squareIntegral_add_constant R (t-d x) (U x) hR]
    have hh := squareEnvelope_positivePart R (t-d x) (hb x hx)
    dsimp [P,C]
    linarith
  rw [he,integral_add hP hC]
  change (15/4 : ℝ) * ((∫ x in K, P x) + ∫ x in K, (max (t-d x) 0)^3/6) -
    (15/4 : ℝ) * (∫ x in K, P x) = _
  rw [integral_div]
  ring

theorem areaIntegral_eq_negative_of_nonpos (K : Set Plane) (hK : IsCompact K)
    (R : ℝ) (hR : 0 ≤ R) (U d : Plane → ℝ)
    (hU : ContinuousOn U K) (hd : ContinuousOn d K) (hn : ∀ x ∈ K, 0 ≤ d x)
    (t : ℝ) (ht : t ≤ 0) (hb : ∀ x ∈ K, |t-d x| ≤ R) :
    areaIntegral K R U d t = negativeAreaIntegral K R U d t := by
  have he := areaIntegral_positivePart K hK R hR U d hU hd t hb
  have hz : (∫ x in K, (max (t-d x) 0)^3) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [max_eq_right (by linarith [hn x hx])]
    norm_num
  rw [hz,mul_zero] at he
  exact sub_eq_zero.mp he

end D4.AreaEnvelope
