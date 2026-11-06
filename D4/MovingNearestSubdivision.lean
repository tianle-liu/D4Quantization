import D4.AnalyticLinearSystems
import D4.NearestJointContinuity

/-! Actual nearest-point integrals on a finite analytic simplex subdivision. -/
noncomputable section
namespace D4.Analytic
open Matrix MeasureTheory Set Principal

structure AnalyticNearestSubdivision {ι : Type*} [Fintype ι]
    (S : ℝ → Set Vec) (Q : ℝ → Gram) (t₀ : ℝ) where
  vertices : ι → ℝ → Fin 5 → Vec
  site : ι → IntVec
  analytic_vertices : ∀ i j k, AnalyticAt ℝ (fun t => vertices i t j k) t₀
  nondegenerate : ∀ i, (simplexMatrix (vertices i t₀)).det ≠ 0
  geometry : ∀ᶠ t in nhds t₀,
    (S t =ᵐ[volume] ⋃ i, vertexSimplex (vertices i t)) ∧
    (Pairwise fun i j => volume
      (vertexSimplex (vertices i t) ∩ vertexSimplex (vertices j t)) = 0) ∧
    (∀ i x, x ∈ vertexSimplex (vertices i t) →
      nearest (Q t) x = quadratic (Q t) (x-castVec (site i)))

/-- The conclusion is analyticity of the integral itself; no integral identity
or analyticity is assumed as part of the subdivision data. -/
theorem analyticAt_nearest_integral_subdivision {ι : Type*} [Fintype ι]
    (S : ℝ → Set Vec) (Q : ℝ → Gram) (t₀ : ℝ)
    (hQ : ∀ i j, AnalyticAt ℝ (fun t => Q t i j) t₀)
    (hpos : ∀ᶠ t in nhds t₀, (Q t).PosDef)
    (T : AnalyticNearestSubdivision (ι := ι) S Q t₀) :
    AnalyticAt ℝ (fun t => ∫ x in S t, nearest (Q t) x) t₀ := by
  have ha (i : ι) := analyticAt_vertexSimplex_quadratic_shift Q (T.vertices i)
    (fun _ => castVec (T.site i)) t₀ hQ (T.analytic_vertices i)
    (fun _ => analyticAt_const) (T.nondegenerate i) (hpos.mono fun _ h => h.1)
  apply (Finset.analyticAt_sum Finset.univ fun i _ => ha i).congr
  filter_upwards [T.geometry,hpos] with t ht hp
  rw [setIntegral_congr_set ht.1]
  have hc := nearest_continuous_point hp
  have hi : IntegrableOn (nearest (Q t)) (⋃ i, vertexSimplex (T.vertices i t)) :=
    hc.continuousOn.integrableOn_compact
      (isCompact_iUnion fun i => vertexSimplex_compact (T.vertices i t))
  rw [integral_iUnion_ae
    (fun i => (vertexSimplex_compact (T.vertices i t)).measurableSet.nullMeasurableSet)
    ht.2.1 hi, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  apply setIntegral_congr_fun (vertexSimplex_compact (T.vertices i t)).measurableSet
  exact fun x hx => (ht.2.2 i x hx).symm

end D4.Analytic
