import D4.AreaTriangles
import D4.AreaSublevel

/-! A precise finite-triangulation version of the analytic subdivision
hypothesis in the area-integral lemma. Every cell is an actual affine
triangle; its vertex and affine-function coordinates are analytic. -/
noncomputable section
namespace D4.AreaEnvelope
open MeasureTheory Set

theorem integral_eq_sum_affineTriangles {ι : Type*} [Fintype ι]
    (K : Set Plane) (hK : IsCompact K) (B : ι → PlaneMatrix) (c : ι → Plane)
    (hcover : (⋃ i, affineTriangle (B i) (c i)) = K)
    (hinter : Pairwise fun i j => volume
      (affineTriangle (B i) (c i) ∩ affineTriangle (B j) (c j)) = 0)
    (f : Plane → ℝ) (hf : ContinuousOn f K) :
    (∫ x in K, f x) = ∑ i, ∫ x in affineTriangle (B i) (c i), f x := by
  have hi : IntegrableOn f (⋃ i, affineTriangle (B i) (c i)) := by
    rw [hcover]
    exact hf.integrableOn_compact hK
  rw [← hcover,integral_iUnion_ae
    (fun i => (affineTriangle_compact (B i) (c i)).measurableSet.nullMeasurableSet)
    hinter hi,tsum_fintype]

/-- The geometric contents of a finite analytic triangulation near `t₀`.
Coverage and boundary disjointness are set/measure statements, not any
formula for the integral or any assertion that it is analytic. -/
structure AnalyticTriangulation {ι : Type*} [Fintype ι] (K : Set Plane)
    (U d : ℝ → Plane → ℝ) (t₀ : ℝ) where
  matrix : ι → ℝ → PlaneMatrix
  origin : ι → ℝ → Plane
  upperCoefficients : ι → ℝ → Fin 3 → ℝ
  distanceCoefficients : ι → ℝ → Fin 3 → ℝ
  analytic_matrix : ∀ i j k, AnalyticAt ℝ (fun t => matrix i t j k) t₀
  analytic_origin : ∀ i j, AnalyticAt ℝ (fun t => origin i t j) t₀
  analytic_upper : ∀ i j, AnalyticAt ℝ (fun t => upperCoefficients i t j) t₀
  analytic_distance : ∀ i j, AnalyticAt ℝ (fun t => distanceCoefficients i t j) t₀
  nondegenerate : ∀ i, (matrix i t₀).det ≠ 0
  geometry : ∀ᶠ t in nhds t₀,
    (⋃ i, affineTriangle (matrix i t) (origin i t)) = K ∧
    (Pairwise fun i j => volume
      (affineTriangle (matrix i t) (origin i t) ∩
        affineTriangle (matrix j t) (origin j t)) = 0) ∧
    (∀ i x, x ∈ affineTriangle (matrix i t) (origin i t) →
      U t x = affineEval (upperCoefficients i t) x ∧
      d t x = affineEval (distanceCoefficients i t) x)

theorem analyticAt_negativeAreaIntegral {ι : Type*} [Fintype ι]
    (K : Set Plane) (hK : IsCompact K) (R : ℝ) (U d : ℝ → Plane → ℝ) (t₀ : ℝ)
    (T : AnalyticTriangulation (ι := ι) K U d t₀)
    (hcontinuous : ∀ᶠ t in nhds t₀, ContinuousOn (U t) K ∧ ContinuousOn (d t) K) :
    AnalyticAt ℝ (fun t => negativeAreaIntegral K R (U t) (d t) t) t₀ := by
  have ha (i : ι) := analyticAt_negativeTriangleIntegral R
    (T.upperCoefficients i) (T.distanceCoefficients i) (T.matrix i) (T.origin i) t₀
    (T.analytic_upper i) (T.analytic_distance i) (T.analytic_matrix i)
    (T.analytic_origin i) (T.nondegenerate i)
  have hconst : AnalyticAt ℝ (fun _ : ℝ => (15/4 : ℝ)) t₀ := analyticAt_const
  apply (hconst.mul (Finset.analyticAt_sum Finset.univ fun i _ => ha i)).congr
  filter_upwards [T.geometry,hcontinuous] with t ht hc
  simp only [Pi.mul_apply]
  unfold negativeAreaIntegral
  congr 1
  have hf : ContinuousOn (fun x => 4*R^2*U t x + squareNegativePolynomial R (t-d t x)) K := by
    unfold squareNegativePolynomial
    exact (continuousOn_const.mul hc.1).add
      (((continuousOn_const.add (continuousOn_const.mul (continuousOn_const.sub hc.2))).sub
        (continuousOn_const.mul ((continuousOn_const.sub hc.2).pow 2))).add
          (((continuousOn_const.sub hc.2).pow 3).div_const 6))
  rw [integral_eq_sum_affineTriangles K hK (fun i => T.matrix i t)
    (fun i => T.origin i t) ht.1 ht.2.1 _ hf]
  apply Finset.sum_congr rfl
  intro i _
  apply setIntegral_congr_fun (affineTriangle_compact _ _).measurableSet
  intro x hx
  rcases ht.2.2 i x hx with ⟨hu,hd⟩
  simp only [hu,hd]

/-- The analytic continuation and both actual correction integrals. The
finite triangulation supplies the precise geometric meaning of a fixed
analytic piecewise-affine subdivision. -/
theorem area_integral_lemma {ι : Type*} [Fintype ι]
    (K : Set Plane) (hK : IsCompact K) (R : ℝ) (hR : 0 < R)
    (U d : ℝ → Plane → ℝ)
    (T : AnalyticTriangulation (ι := ι) K U d 0)
    (hdata : ∀ᶠ t in nhds (0 : ℝ), ContinuousOn (U t) K ∧ ContinuousOn (d t) K ∧
      (∀ x ∈ K, 0 ≤ d t x) ∧ (∀ x ∈ K, |t-d t x| ≤ R)) :
    ∃ Iminus : ℝ → ℝ, AnalyticAt ℝ Iminus 0 ∧
      (∀ᶠ t in nhds (0 : ℝ), t < 0 → areaIntegral K R (U t) (d t) t = Iminus t) ∧
      (∀ᶠ t in nhds (0 : ℝ), 0 < t →
        areaIntegral K R (U t) (d t) t - Iminus t =
          (5/8 : ℝ) * ∫ x in K, (max (t-d t x) 0)^3) ∧
      (∀ᶠ t in nhds (0 : ℝ), 0 < t →
        areaIntegral K R (U t) (d t) t - Iminus t =
          (15/8 : ℝ) * ∫ s in Icc 0 t,
            (t-s)^2 * volume.real {x | x ∈ K ∧ d t x ≤ s}) := by
  refine ⟨fun t => negativeAreaIntegral K R (U t) (d t) t,?_,?_,?_,?_⟩
  · apply analyticAt_negativeAreaIntegral K hK R U d 0 T
    filter_upwards [hdata] with t ht
    exact ⟨ht.1,ht.2.1⟩
  · filter_upwards [hdata] with t ht
    intro hneg
    exact areaIntegral_eq_negative_of_nonpos K hK R hR.le (U t) (d t)
      ht.1 ht.2.1 ht.2.2.1 t hneg.le ht.2.2.2
  · filter_upwards [hdata] with t ht
    intro _
    exact areaIntegral_positivePart K hK R hR.le (U t) (d t) ht.1 ht.2.1 t ht.2.2.2
  · filter_upwards [hdata] with t ht
    intro hpos
    exact areaIntegral_sublevel K hK R hR.le (U t) (d t) ht.1 ht.2.1 ht.2.2.1 t hpos.le ht.2.2.2

/-- The source lemma's original nonpositive functions `U,V`, with
`d = -U - V`; nonnegativity of the depth is derived rather than assumed. -/
theorem area_integral_lemma_of_nonpos {ι : Type*} [Fintype ι]
    (K : Set Plane) (hK : IsCompact K) (R : ℝ) (hR : 0 < R)
    (U V : ℝ → Plane → ℝ)
    (T : AnalyticTriangulation (ι := ι) K U (fun t x => -U t x - V t x) 0)
    (hdata : ∀ᶠ t in nhds (0 : ℝ), ContinuousOn (U t) K ∧ ContinuousOn (V t) K ∧
      (∀ x ∈ K, U t x ≤ 0 ∧ V t x ≤ 0) ∧
      (∀ x ∈ K, |t-(-U t x-V t x)| < R)) :
    ∃ Iminus : ℝ → ℝ, AnalyticAt ℝ Iminus 0 ∧
      (∀ᶠ t in nhds (0 : ℝ), t < 0 →
        areaIntegral K R (U t) (fun x => -U t x-V t x) t = Iminus t) ∧
      (∀ᶠ t in nhds (0 : ℝ), 0 < t →
        areaIntegral K R (U t) (fun x => -U t x-V t x) t - Iminus t =
          (5/8 : ℝ) * ∫ x in K, (max (t-(-U t x-V t x)) 0)^3) ∧
      (∀ᶠ t in nhds (0 : ℝ), 0 < t →
        areaIntegral K R (U t) (fun x => -U t x-V t x) t - Iminus t =
          (15/8 : ℝ) * ∫ s in Icc 0 t,
            (t-s)^2 * volume.real {x | x ∈ K ∧ -U t x-V t x ≤ s}) := by
  apply area_integral_lemma K hK R hR U (fun t x => -U t x-V t x) T
  filter_upwards [hdata] with t ht
  refine ⟨ht.1,ht.1.neg.sub ht.2.1,?_,fun x hx => (ht.2.2.2 x hx).le⟩
  intro x hx
  rcases ht.2.2.1 x hx with ⟨hu,hv⟩
  linarith

end D4.AreaEnvelope
