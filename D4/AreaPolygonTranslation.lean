import D4.AreaPolygonBarycenter

noncomputable section
namespace D4.AreaEnvelope
open Set Matrix MeasureTheory
open scoped Topology

namespace PlaneSlack

def recenter (s : PlaneSlack) (c : Plane) : PlaneSlack := ⟨s.normal,s.eval c⟩

theorem eval_recenter (s : PlaneSlack) (c x : Plane) :
    (s.recenter c).eval (-c+x)=s.eval x := by
  simp only [recenter,eval,dotProduct_add,dotProduct_neg]
  ring

end PlaneSlack

structure PolygonData (ι : Type*) where
  body : Set Plane
  start : ι → Plane
  finish : ι → Plane
  slack : ι → PlaneSlack

namespace PolygonData
variable {ι : Type*} [Fintype ι] [Nonempty ι]

structure Valid (P : PolygonData ι) : Prop where
  compact : IsCompact P.body
  convex : Convex ℝ P.body
  description : P.body={x | ∀ i,0≤(P.slack i).eval x}
  boundary : frontier P.body=⋃ i,segment ℝ (P.start i) (P.finish i)
  start_on : ∀ i,(P.slack i).eval (P.start i)=0
  finish_on : ∀ i,(P.slack i).eval (P.finish i)=0
  edge_ne : ∀ i,P.start i≠P.finish i
  strict_vertex : ∀ i,∃ j,0<(P.slack i).eval (P.start j)
  facets_distinct : ∀ i j,i≠j → ∃ x∈P.body,(P.slack i).eval x=0 ∧ 0<(P.slack j).eval x

def center (P : PolygonData ι) : Plane := vertexMean P.start

theorem start_mem (P : PolygonData ι) (hP : P.Valid) (i : ι) : P.start i∈P.body := by
  apply hP.compact.isClosed.frontier_subset
  rw [hP.boundary]
  exact mem_iUnion.mpr ⟨i,left_mem_segment ℝ _ _⟩

theorem center_strict (P : PolygonData ι) (hP : P.Valid) (i : ι) :
    0<(P.slack i).eval P.center := by
  apply vertexMean_strict _ _ ?_ (hP.strict_vertex i)
  intro j
  have h := P.start_mem hP j
  rw [hP.description] at h
  exact h i

theorem center_interior (P : PolygonData ι) (hP : P.Valid) : P.center∈interior P.body := by
  rw [hP.description]
  apply vertexMean_interior _ _ ?_ hP.strict_vertex
  intro i j
  have h := P.start_mem hP j
  rw [hP.description] at h
  exact h i

def centered (P : PolygonData ι) (hP : P.Valid) : CenteredPolygon ι where
  body := (fun x => -P.center+x) '' P.body
  compact := hP.compact.image (continuous_const.add continuous_id)
  convex := hP.convex.translate (-P.center)
  origin_interior := by
    change 0 ∈ interior ((Homeomorph.addLeft (-P.center)) '' P.body)
    rw [← (Homeomorph.addLeft (-P.center)).image_interior P.body]
    exact ⟨P.center,P.center_interior hP,by simp⟩
  start := fun i => -P.center+P.start i
  finish := fun i => -P.center+P.finish i
  boundary := by
    change frontier ((Homeomorph.addLeft (-P.center)) '' P.body)=_
    rw [← (Homeomorph.addLeft (-P.center)).image_frontier P.body,hP.boundary,image_iUnion]
    simp only [Homeomorph.coe_addLeft,segment_translate_image]
  slack := fun i => (P.slack i).recenter P.center
  offset_pos := P.center_strict hP
  support := by
    intro i x hx
    obtain ⟨y,hy,rfl⟩ := hx
    rw [PlaneSlack.eval_recenter]
    rw [hP.description] at hy
    exact hy i
  start_on := fun i => by rw [PlaneSlack.eval_recenter]; exact hP.start_on i
  finish_on := fun i => by rw [PlaneSlack.eval_recenter]; exact hP.finish_on i
  edge_ne := fun i h => hP.edge_ne i (add_left_cancel h)
  facets_distinct := by
    intro i j hij
    obtain ⟨x,hx,hi,hj⟩ := hP.facets_distinct i j hij
    exact ⟨-P.center+x,⟨x,hx,rfl⟩,by simpa only [PlaneSlack.eval_recenter] using hi,
      by simpa only [PlaneSlack.eval_recenter] using hj⟩

def matrices (P : PolygonData ι) (i : ι) : PlaneMatrix :=
  triangleMatrix (-P.center+P.start i) (-P.center+P.finish i)

theorem affineTriangle_translate (B : PlaneMatrix) (c : Plane) :
    (fun x => c+x) '' affineTriangle B 0=affineTriangle B c := by
  simp only [affineTriangle,image_image,zero_add,Function.comp_def]

theorem cover (P : PolygonData ι) (hP : P.Valid) :
    (⋃ i,affineTriangle (P.matrices i) P.center)=P.body := by
  have h := congrArg (fun S : Set Plane => (fun x => P.center+x) '' S) (P.centered hP).cover
  simpa only [centered,CenteredPolygon.matrices,matrices,image_iUnion,affineTriangle_translate,
    image_image,Function.comp_def,add_neg_cancel_left,Set.image_id'] using h

theorem nondegenerate (P : PolygonData ι) (hP : P.Valid) (i : ι) :
    (P.matrices i).det≠0 := (P.centered hP).nondegenerate i

theorem pairwise_null (P : PolygonData ι) (hP : P.Valid) : Pairwise fun i j =>
    volume (affineTriangle (P.matrices i) P.center ∩ affineTriangle (P.matrices j) P.center)=0 := by
  intro i j hij
  rw [← affineTriangle_translate (P.matrices i) P.center,
    ← affineTriangle_translate (P.matrices j) P.center,
    ← image_inter (add_right_injective P.center)]
  have hm := (measurePreserving_add_left (volume : Measure Plane) P.center).measure_preimage_emb
    (Homeomorph.addLeft P.center).measurableEmbedding
    ((fun x => P.center+x) ''
      (affineTriangle (P.matrices i) 0 ∩ affineTriangle (P.matrices j) 0))
  rw [Set.preimage_image_eq _ (add_right_injective P.center)] at hm
  rw [← hm]
  exact (P.centered hP).pairwise_null hij

end PolygonData
end D4.AreaEnvelope
