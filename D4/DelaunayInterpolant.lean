import D4.DelaunayTriangulations
import Mathlib.Analysis.Convex.Function

/-! The actual periodic Delaunay families admit a globally convex, piecewise
 affine interpolant of the quadratic lattice heights. Supporting planes and
 proved coverage supply the construction, including agreement on boundaries. -/
noncomputable section
namespace D4.Delaunay
open Matrix Analytic Principal Set
open scoped Pointwise
attribute [local instance] integerTranslation

theorem supported_cell_dominates {Q : Gram} {S T : LatticeSimplex}
    {p q : AffineSlack} (hp : SupportsPlane Q S p) (hq : SupportsPlane Q T q)
    {x : Vec} (hx : x ∈ simplexRegion S) : q.eval x ≤ p.eval x := by
  have h : 0 ≤ (planeDifference p q).eval x := by
    apply AffineSlack.nonneg_on_simplex _ _ _ hx
    intro i
    rw [planeDifference_eval,hp.2 i]
    exact sub_nonneg.mpr (hq.1 _)
  rwa [planeDifference_eval,sub_nonneg] at h

theorem exists_convex_interpolant {ι : Type*} (Q : Gram)
    (S : ι → LatticeSimplex) (p : ι → AffineSlack)
    (hs : ∀ i, SupportsPlane Q (S i) (p i))
    (hcover : ∀ x : Vec, ∃ i, x ∈ simplexRegion (S i))
    (hvertices : ∀ n : IntVec, ∃ i j, S i j=n) :
    ∃ f : Vec → ℝ, ConvexOn ℝ univ f ∧
      (∀ i x, x ∈ simplexRegion (S i) → f x=(p i).eval x) ∧
      (∀ n : IntVec, f (castVec n)=quadratic Q (castVec n)) ∧
      (∀ i x, (p i).eval x ≤ f x) := by
  classical
  let index : Vec → ι := fun x => Classical.choose (hcover x)
  have hindex (x : Vec) : x ∈ simplexRegion (S (index x)) :=
    Classical.choose_spec (hcover x)
  let f : Vec → ℝ := fun x => (p (index x)).eval x
  have heq (i : ι) (x : Vec) (hx : x ∈ simplexRegion (S i)) :
      f x=(p i).eval x :=
    supported_common_height (hs (index x)) (hs i) ⟨hindex x,hx⟩
  have hle (i : ι) (x : Vec) : (p i).eval x ≤ f x :=
    supported_cell_dominates (hs (index x)) (hs i) (hindex x)
  refine ⟨f,⟨convex_univ,?_⟩,heq,?_,hle⟩
  · intro x _ y _ a b ha hb hab
    change (p (index (a • x+b • y))).eval (a • x+b • y) ≤ a*f x+b*f y
    rw [AffineSlack.eval_affine_combination _ _ _ hab]
    exact add_le_add (mul_le_mul_of_nonneg_left (hle _ x) ha)
      (mul_le_mul_of_nonneg_left (hle _ y) hb)
  · intro n
    obtain ⟨i,j,hj⟩ := hvertices n
    have hn : castVec n ∈ simplexRegion (S i) := by
      rw [← hj]
      exact vertex_mem_vertexSimplex _ j
    rw [heq i _ hn,← hj]
    exact (hs i).2 j

theorem exists_periodic_convex_interpolant {ι : Type*} [Nonempty ι]
    (Q : Gram) (hQ : Q.IsHermitian) (S : ι → LatticeSimplex)
    (p : ι → AffineSlack) (hs : ∀ i, SupportsPlane Q (S i) (p i))
    (hcover : periodicUnion (fun i => simplexRegion (S i))=univ) :
    ∃ f : Vec → ℝ, ConvexOn ℝ univ f ∧
      (∀ i n x, x ∈ simplexRegion (translateSimplex (S i) n) →
        f x=(translatePlane Q (p i) n).eval x) ∧
      (∀ n : IntVec, f (castVec n)=quadratic Q (castVec n)) ∧
      (∀ i n x, (translatePlane Q (p i) n).eval x ≤ f x) := by
  classical
  have hcov (x : Vec) : ∃ k : ι × IntVec,
      x∈simplexRegion (translateSimplex (S k.1) k.2) := by
    have hx : x ∈ periodicUnion (fun i => simplexRegion (S i)) := by rw [hcover]; trivial
    obtain ⟨k,hk⟩ := mem_iUnion.mp hx
    exact ⟨k,by simpa only [periodicPieces,simplexRegion_periodic] using hk⟩
  have hver (n : IntVec) : ∃ k : ι × IntVec, ∃ j,
      translateSimplex (S k.1) k.2 j=n := by
    let i : ι := Classical.choice inferInstance
    exact ⟨(i,n-S i 0),0,by simp only [translateSimplex]; abel⟩
  obtain ⟨f,hf,hlocal,hinteger,hlower⟩ := exists_convex_interpolant Q
    (fun k : ι × IntVec => translateSimplex (S k.1) k.2)
    (fun k => translatePlane Q (p k.1) k.2)
    (fun k => translatePlane_supported hQ (hs k.1) k.2) hcov hver
  exact ⟨f,hf,fun i n => hlocal (i,n),hinteger,fun i n => hlower (i,n)⟩

theorem cells1_convex_interpolant (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) :
    ∃ f : Vec → ℝ, ConvexOn ℝ univ f ∧
      (∀ i n x, x ∈ simplexRegion (translateSimplex (cells1 i) n) →
        f x=(translatePlane (principalForm w) (cellPlane1 w i) n).eval x) ∧
      (∀ n : IntVec, f (castVec n)=quadratic (principalForm w) (castVec n)) ∧
      (∀ i n x, (translatePlane (principalForm w) (cellPlane1 w i) n).eval x ≤ f x) :=
  exists_periodic_convex_interpolant _ (principal_isHermitian w) _ _
    (fun i => (cellPlane1_exact w hw i).1) cells1_cover

theorem cells2_convex_interpolant (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) :
    ∃ f : Vec → ℝ, ConvexOn ℝ univ f ∧
      (∀ i n x, x ∈ simplexRegion (translateSimplex (cells2 i) n) →
        f x=(translatePlane (secondaryForm cone2Vectors (w 0) (fun j => w j.succ))
          (cellPlane2 w i) n).eval x) ∧
      (∀ n : IntVec, f (castVec n)=quadratic
        (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) (castVec n)) ∧
      (∀ i n x, (translatePlane (secondaryForm cone2Vectors (w 0) (fun j => w j.succ))
        (cellPlane2 w i) n).eval x ≤ f x) :=
  exists_periodic_convex_interpolant _ (secondary_isHermitian _ _ _) _ _
    (fun i => (cellPlane2_exact w hw i).1) cells2_cover

theorem cells3_convex_interpolant (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) :
    ∃ f : Vec → ℝ, ConvexOn ℝ univ f ∧
      (∀ i n x, x ∈ simplexRegion (translateSimplex (cells3 i) n) →
        f x=(translatePlane (secondaryForm cone3Vectors (w 0) (fun j => w j.succ))
          (cellPlane3 w i) n).eval x) ∧
      (∀ n : IntVec, f (castVec n)=quadratic
        (secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) (castVec n)) ∧
      (∀ i n x, (translatePlane (secondaryForm cone3Vectors (w 0) (fun j => w j.succ))
        (cellPlane3 w i) n).eval x ≤ f x) :=
  exists_periodic_convex_interpolant _ (secondary_isHermitian _ _ _) _ _
    (fun i => (cellPlane3_exact w hw i).1) cells3_cover

end D4.Delaunay
