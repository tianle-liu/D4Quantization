import D4.AreaPolygonTranslation
import D4.AreaSubdivision

/-! Polygonal analytic subdivisions yield the analytic triangulation used
in the area-integral lemma. Triangle coverage and null intersections are
proved from the original polygon boundaries and supports. -/
noncomputable section
namespace D4.AreaEnvelope
open Set Matrix MeasureTheory
open scoped Topology

structure AnalyticPolygonSubdivision {ι : Type*} [Fintype ι]
    (κ : ι → Type*) [∀ i,Fintype (κ i)] [∀ i,Nonempty (κ i)]
    (K : Set Plane) (U d : ℝ → Plane → ℝ) (t₀ : ℝ) where
  data : ∀ i,ℝ → PolygonData (κ i)
  upperCoefficients : ι → ℝ → Fin 3 → ℝ
  distanceCoefficients : ι → ℝ → Fin 3 → ℝ
  analytic_start : ∀ i j k,AnalyticAt ℝ (fun t => (data i t).start j k) t₀
  analytic_finish : ∀ i j k,AnalyticAt ℝ (fun t => (data i t).finish j k) t₀
  analytic_upper : ∀ i j,AnalyticAt ℝ (fun t => upperCoefficients i t j) t₀
  analytic_distance : ∀ i j,AnalyticAt ℝ (fun t => distanceCoefficients i t j) t₀
  valid_zero : ∀ i,(data i t₀).Valid
  geometry : ∀ᶠ t in nhds t₀,
    (∀ i,(data i t).Valid) ∧
    (⋃ i,(data i t).body)=K ∧
    (Pairwise fun i j => volume ((data i t).body ∩ (data j t).body)=0) ∧
    (∀ i x,x∈(data i t).body →
      U t x=affineEval (upperCoefficients i t) x ∧
      d t x=affineEval (distanceCoefficients i t) x)

namespace AnalyticPolygonSubdivision
variable {ι : Type*} [Fintype ι] {κ : ι → Type*}
  [∀ i,Fintype (κ i)] [∀ i,Nonempty (κ i)]
  {K : Set Plane} {U d : ℝ → Plane → ℝ} {t₀ : ℝ}

theorem analytic_center (P : AnalyticPolygonSubdivision κ K U d t₀) (i : ι) (k : Fin 2) :
    AnalyticAt ℝ (fun t => (P.data i t).center k) t₀ :=
  analyticAt_vertexMean (fun j t => (P.data i t).start j) t₀ (P.analytic_start i) k

theorem analytic_matrices (P : AnalyticPolygonSubdivision κ K U d t₀)
    (i : ι) (j : κ i) (k l : Fin 2) :
    AnalyticAt ℝ (fun t => (P.data i t).matrices j k l) t₀ := by
  fin_cases k <;> fin_cases l
  · exact (P.analytic_center i 0).neg.add (P.analytic_start i j 0)
  · exact (P.analytic_center i 0).neg.add (P.analytic_finish i j 0)
  · exact (P.analytic_center i 1).neg.add (P.analytic_start i j 1)
  · exact (P.analytic_center i 1).neg.add (P.analytic_finish i j 1)

def triangulation (P : AnalyticPolygonSubdivision κ K U d t₀) :
    AnalyticTriangulation (ι := Sigma κ) K U d t₀ where
  matrix := fun i t => (P.data i.1 t).matrices i.2
  origin := fun i t => (P.data i.1 t).center
  upperCoefficients := fun i => P.upperCoefficients i.1
  distanceCoefficients := fun i => P.distanceCoefficients i.1
  analytic_matrix := fun i => P.analytic_matrices i.1 i.2
  analytic_origin := fun i => P.analytic_center i.1
  analytic_upper := fun i => P.analytic_upper i.1
  analytic_distance := fun i => P.analytic_distance i.1
  nondegenerate := fun i => (P.data i.1 t₀).nondegenerate (P.valid_zero i.1) i.2
  geometry := by
    filter_upwards [P.geometry] with t ht
    have hsub (i : Sigma κ) :
        affineTriangle ((P.data i.1 t).matrices i.2) (P.data i.1 t).center ⊆ (P.data i.1 t).body := by
      rw [← (P.data i.1 t).cover (ht.1 i.1)]
      exact fun x hx => mem_iUnion.mpr ⟨i.2,hx⟩
    refine ⟨?_,?_,?_⟩
    · rw [iUnion_sigma]
      simp_rw [fun i => (P.data i t).cover (ht.1 i)]
      exact ht.2.1
    · intro i j hij
      by_cases he : i.1=j.1
      · rcases i with ⟨i,k⟩
        rcases j with ⟨j,l⟩
        dsimp at he
        subst j
        have hkl : k≠l := fun h => hij (by subst l; rfl)
        exact (P.data i t).pairwise_null (ht.1 i) hkl
      · apply measure_mono_null (inter_subset_inter (hsub i) (hsub j))
        exact ht.2.2.1 he
    · intro i x hx
      exact ht.2.2.2 i.1 x (hsub i hx)

end AnalyticPolygonSubdivision
theorem area_integral_lemma_of_polygons {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i,Fintype (κ i)] [∀ i,Nonempty (κ i)]
    (K : Set Plane) (hK : IsCompact K) (R : ℝ) (hR : 0 < R)
    (U V : ℝ → Plane → ℝ)
    (P : AnalyticPolygonSubdivision κ K U (fun t x => -U t x - V t x) 0)
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
  exact area_integral_lemma_of_nonpos K hK R hR U V P.triangulation hdata

end D4.AreaEnvelope
