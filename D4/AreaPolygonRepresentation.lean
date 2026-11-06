import D4.AreaPolygonSubdivision

/-! A full-dimensional vertex/half-plane polygon presentation supplies the
strict vertex inequalities used to construct its barycenter. -/
noncomputable section
namespace D4.AreaEnvelope
open Set Matrix MeasureTheory

namespace PolygonData
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem strict_vertex_of_hull (P : PolygonData ι)
    (hhull : P.body=convexHull ℝ (Set.range P.start))
    (hinter : (interior P.body).Nonempty)
    (hsupport : ∀ i x,x∈P.body → 0≤(P.slack i).eval x)
    (hnormal : ∀ i,(P.slack i).normal≠0) (i : ι) :
    ∃ j,0<(P.slack i).eval (P.start j) := by
  by_contra! h
  have hv (j : ι) : (P.slack i).eval (P.start j)=0 := by
    apply le_antisymm (h j)
    apply hsupport i
    rw [hhull]
    exact subset_convexHull ℝ _ ⟨j,rfl⟩
  have hsub : P.body⊆((P.slack i).hyperplane : Set Plane) := by
    rw [hhull]
    apply convexHull_min ?_ (P.slack i).hyperplane.convex
    rintro x ⟨j,rfl⟩
    change dotProduct (P.slack i).normal (P.start j)=(P.slack i).offset
    exact (sub_eq_zero.mp (hv j)).symm
  have hz : volume P.body=0 := measure_mono_null hsub
    ((P.slack i).hyperplane_volume (hnormal i))
  rw [volume.interior_eq_empty_of_null hz] at hinter
  exact Set.not_nonempty_empty hinter

/-- A conventional full-dimensional convex hull, with its actual boundary
edges and distinct supporting facets, is enough to derive `Valid`. -/
def validOfHull (P : PolygonData ι)
    (hc : IsCompact P.body)
    (hhull : P.body=convexHull ℝ (Set.range P.start))
    (hinter : (interior P.body).Nonempty)
    (hdesc : P.body={x | ∀ i,0≤(P.slack i).eval x})
    (hboundary : frontier P.body=⋃ i,segment ℝ (P.start i) (P.finish i))
    (hnormal : ∀ i,(P.slack i).normal≠0)
    (hstart : ∀ i,(P.slack i).eval (P.start i)=0)
    (hfinish : ∀ i,(P.slack i).eval (P.finish i)=0)
    (hne : ∀ i,P.start i≠P.finish i)
    (hdistinct : ∀ i j,i≠j → ∃ x∈P.body,(P.slack i).eval x=0 ∧ 0<(P.slack j).eval x) :
    P.Valid where
  compact := hc
  convex := hhull ▸ convex_convexHull ℝ _
  description := hdesc
  boundary := hboundary
  start_on := hstart
  finish_on := hfinish
  edge_ne := hne
  strict_vertex := P.strict_vertex_of_hull hhull hinter
    (by intro i x hx; rw [hdesc] at hx; exact hx i) hnormal
  facets_distinct := hdistinct

end PolygonData
end D4.AreaEnvelope
