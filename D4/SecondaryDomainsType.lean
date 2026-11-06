import D4.DelaunayTriangulations
import Mathlib.Analysis.Convex.Measure

/-! Actual full-dimensional Delaunay cells, defined by supporting affine planes
 against every integer lattice point. Positive volume is the full-dimensional
 condition for their convex hull; no displayed family is built into this type. -/
noncomputable section
namespace D4.Delaunay
open Analytic Principal Matrix MeasureTheory Set

def latticeHull (F : Finset IntVec) : Set Vec := convexHull ℝ (castVec '' (F : Set IntVec))

def TightPlane (Q : Gram) (F : Finset IntVec) (p : AffineSlack) : Prop :=
  (∀ n : IntVec, p.eval (castVec n) ≤ quadratic Q (castVec n)) ∧
  ∀ n : IntVec, p.eval (castVec n)=quadratic Q (castVec n) ↔ n ∈ F

/-- Full-dimensional empty-sphere cells, represented by their complete finite
 lattice vertex sets. Lower-dimensional cells are recovered as their faces. -/
def delaunayType (Q : Gram) : Set (Finset IntVec) :=
  {F | (∃ p, TightPlane Q F p) ∧ volume (latticeHull F) ≠ 0}

theorem latticeHull_simplexVertices (S : LatticeSimplex) :
    latticeHull (simplexVertices S)=simplexRegion S := by
  rw [latticeHull, simplexRegion, vertexSimplex_eq_convexHull]
  congr 1
  ext x
  simp [simplexVertices, Set.mem_range, Set.mem_image]

theorem exactPlane_tightPlane {Q : Gram} {S : LatticeSimplex} {p : AffineSlack}
    (h : ExactPlane Q S p) : TightPlane Q (simplexVertices S) p := ⟨h.1.1,h.2⟩

theorem tight_supported_common_height {Q : Gram} {F : Finset IntVec}
    {S : LatticeSimplex} {p q : AffineSlack}
    (hp : TightPlane Q F p) (hq : SupportsPlane Q S q)
    {x : Vec} (hx : x ∈ latticeHull F ∩ simplexRegion S) : p.eval x=q.eval x := by
  have h1 : 0 ≤ (planeDifference p q).eval x := by
    apply convexHull_min ?_ (planeDifference p q).convex_nonneg hx.1
    rintro _ ⟨n, hn, rfl⟩
    change 0 ≤ (planeDifference p q).eval (castVec n)
    rw [planeDifference_eval, (hp.2 n).mpr hn]
    exact sub_nonneg.mpr (hq.1 n)
  have h2 : (planeDifference p q).eval x ≤ 0 := by
    apply AffineSlack.nonpos_on_simplex _ _ _ hx.2
    intro i
    rw [planeDifference_eval, hq.2 i]
    exact sub_nonpos.mpr (hp.1 _)
  rw [planeDifference_eval] at h1 h2
  linarith

theorem tightPlane_eq_of_inter_volume_ne_zero {Q : Gram} {F : Finset IntVec}
    {S : LatticeSimplex} {p q : AffineSlack}
    (hp : TightPlane Q F p) (hq : ExactPlane Q S q)
    (hvol : volume (latticeHull F ∩ simplexRegion S) ≠ 0) :
    F=simplexVertices S := by
  have hn : p.normal=q.normal := by
    by_contra h
    apply hvol
    apply measure_mono_null (t := (affineHyperplane (p.normal-q.normal)
      (p.offset-q.offset) : Set Vec))
    · intro x hx
      have he := tight_supported_common_height hp hq.1 hx
      change dotProduct (p.normal-q.normal) x=p.offset-q.offset
      rw [sub_dotProduct]
      simp only [AffineSlack.eval] at he
      linarith
    · exact affineHyperplane_volume (sub_ne_zero.mpr h) _
  have hnonempty : (latticeHull F ∩ simplexRegion S).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, measure_empty] at hvol
    exact hvol rfl
  obtain ⟨x,hx⟩ := hnonempty
  have he := tight_supported_common_height hp hq.1 hx
  have ho : p.offset=q.offset := by
    simp only [AffineSlack.eval,hn] at he
    linarith
  ext n
  rw [← hp.2 n, ← hq.2 n]
  simp only [AffineSlack.eval,hn,ho]

/-- A countable exact supporting triangulation determines the entire actual
 full-dimensional Delaunay type, not merely a subfamily of empty simplices. -/
theorem delaunayType_eq_of_exact_cover {ι : Type*} [Countable ι]
    (Q : Gram) (S : ι → LatticeSimplex) (p : ι → AffineSlack)
    (hexact : ∀ i, ExactPlane Q (S i) (p i))
    (hcover : ∀ x : Vec, ∃ i, x ∈ simplexRegion (S i))
    (hvol : ∀ i, volume (simplexRegion (S i)) ≠ 0) :
    delaunayType Q = {F | ∃ i, F=simplexVertices (S i)} := by
  ext F
  constructor
  · rintro ⟨⟨q,hq⟩,hF⟩
    have hi : ∃ i, volume (latticeHull F ∩ simplexRegion (S i)) ≠ 0 := by
      by_contra! h
      apply hF
      have he : latticeHull F = ⋃ i, latticeHull F ∩ simplexRegion (S i) := by
        ext x
        simp only [mem_iUnion, mem_inter_iff]
        exact ⟨fun hx => let ⟨i,hi⟩ := hcover x; ⟨i,hx,hi⟩,
          fun ⟨i,hx,_⟩ => hx⟩
      rw [he]
      exact measure_iUnion_null h
    obtain ⟨i,hi⟩ := hi
    exact ⟨i,tightPlane_eq_of_inter_volume_ne_zero hq (hexact i) hi⟩
  · rintro ⟨i,rfl⟩
    refine ⟨⟨p i,exactPlane_tightPlane (hexact i)⟩,?_⟩
    rw [latticeHull_simplexVertices]
    exact hvol i

end D4.Delaunay
