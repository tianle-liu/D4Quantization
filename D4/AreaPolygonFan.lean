import D4.AreaPolygonRadial
import D4.AreaPolygonSeparation

/-! Geometric fan triangles for finite supporting-edge descriptions of
nondegenerate convex polygons. -/
noncomputable section
namespace D4.AreaEnvelope
open Set Matrix MeasureTheory

namespace PlaneSlack

def fan (s t : PlaneSlack) : PlaneSlack where
  normal := t.offset • s.normal-s.offset • t.normal
  offset := 0

theorem eval_fan (s t : PlaneSlack) (x : Plane) :
    (s.fan t).eval x=t.offset*s.eval x-s.offset*t.eval x := by
  simp only [fan,eval,sub_dotProduct,smul_dotProduct,smul_eq_mul]
  ring

theorem eval_fan_zero (s t : PlaneSlack) : (s.fan t).eval 0=0 := by
  simp [fan,eval]

theorem fan_normal_ne (s t : PlaneSlack) (x : Plane)
    (hp : 0<s.offset) (hs : s.eval x=0) (ht : 0<t.eval x) :
    (s.fan t).normal≠0 := by
  intro hn
  have h : (s.fan t).eval x=0 := by simp only [eval,hn,zero_dotProduct,sub_zero]; rfl
  rw [eval_fan,hs,mul_zero,zero_sub] at h
  have := mul_pos hp ht
  linarith

end PlaneSlack

/-- Actual polygon data: its boundary edges and supporting lines. No fan
coverage, null-intersection, or integral claim occurs among the fields. -/
structure CenteredPolygon (ι : Type*) [Fintype ι] where
  body : Set Plane
  compact : IsCompact body
  convex : Convex ℝ body
  origin_interior : (0:Plane) ∈ interior body
  start : ι → Plane
  finish : ι → Plane
  boundary : frontier body=⋃ i,segment ℝ (start i) (finish i)
  slack : ι → PlaneSlack
  offset_pos : ∀ i,0<(slack i).offset
  support : ∀ i x,x∈body → 0≤(slack i).eval x
  start_on : ∀ i,(slack i).eval (start i)=0
  finish_on : ∀ i,(slack i).eval (finish i)=0
  edge_ne : ∀ i,start i≠finish i
  facets_distinct : ∀ i j,i≠j → ∃ x∈body,(slack i).eval x=0 ∧ 0<(slack j).eval x

namespace CenteredPolygon
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def matrices (P : CenteredPolygon ι) (i : ι) : PlaneMatrix :=
  triangleMatrix (P.start i) (P.finish i)

theorem cover (P : CenteredPolygon ι) :
    (⋃ i,affineTriangle (P.matrices i) 0)=P.body :=
  polygon_fan_cover P.body P.compact P.convex P.origin_interior P.start P.finish P.boundary

theorem nondegenerate (P : CenteredPolygon ι) (i : ι) : (P.matrices i).det≠0 :=
  (P.slack i).triangle_det_ne_zero _ _ (P.offset_pos i) (P.start_on i) (P.finish_on i) (P.edge_ne i)

theorem start_mem (P : CenteredPolygon ι) (i : ι) : P.start i∈P.body := by
  apply P.compact.isClosed.frontier_subset
  rw [P.boundary]
  exact mem_iUnion.mpr ⟨i,left_mem_segment ℝ _ _⟩

theorem finish_mem (P : CenteredPolygon ι) (i : ι) : P.finish i∈P.body := by
  apply P.compact.isClosed.frontier_subset
  rw [P.boundary]
  exact mem_iUnion.mpr ⟨i,right_mem_segment ℝ _ _⟩

theorem pairwise_null (P : CenteredPolygon ι) : Pairwise fun i j =>
    volume (affineTriangle (P.matrices i) 0 ∩ affineTriangle (P.matrices j) 0)=0 := by
  intro i j hij
  obtain ⟨x,hx,hi,hj⟩ := P.facets_distinct i j hij
  have hn := PlaneSlack.fan_normal_ne (P.slack i) (P.slack j) x (P.offset_pos i) hi hj
  rw [Set.inter_comm]
  apply PlaneSlack.triangle_inter_null ((P.slack i).fan (P.slack j))
    (P.start j) (P.finish j) (P.start i) (P.finish i) hn
    (PlaneSlack.eval_fan_zero _ _)
  · rw [PlaneSlack.eval_fan,P.start_on j,mul_zero,sub_zero]
    exact mul_nonneg (P.offset_pos j).le (P.support i _ (P.start_mem j))
  · rw [PlaneSlack.eval_fan,P.finish_on j,mul_zero,sub_zero]
    exact mul_nonneg (P.offset_pos j).le (P.support i _ (P.finish_mem j))
  · rw [PlaneSlack.eval_fan,P.start_on i,mul_zero,zero_sub]
    exact neg_nonpos.mpr (mul_nonneg (P.offset_pos i).le (P.support j _ (P.start_mem i)))
  · rw [PlaneSlack.eval_fan,P.finish_on i,mul_zero,zero_sub]
    exact neg_nonpos.mpr (mul_nonneg (P.offset_pos i).le (P.support j _ (P.finish_mem i)))

end CenteredPolygon
end D4.AreaEnvelope
