import D4.DelaunaySupport
import D4.DelaunayTranslations
import D4.PrincipalFan

noncomputable section
namespace D4.Delaunay
open Matrix Analytic Principal MeasureTheory Set

def SupportsPlane (Q : Gram) (S : LatticeSimplex) (p : AffineSlack) : Prop :=
  (∀ n : IntVec, p.eval (castVec n) ≤ quadratic Q (castVec n)) ∧
  ∀ i, p.eval (castVec (S i))=quadratic Q (castVec (S i))

def ExactPlane (Q : Gram) (S : LatticeSimplex) (p : AffineSlack) : Prop :=
  SupportsPlane Q S p ∧
    ∀ n : IntVec, p.eval (castVec n)=quadratic Q (castVec n) ↔ n ∈ simplexVertices S

def simplexRegion (S : LatticeSimplex) : Set Vec := vertexSimplex (fun i => castVec (S i))

def planeDifference (p q : AffineSlack) : AffineSlack :=
  ⟨p.normal-q.normal,p.offset-q.offset⟩

theorem planeDifference_eval (p q : AffineSlack) (x : Vec) :
    (planeDifference p q).eval x=p.eval x-q.eval x := by
  simp only [planeDifference, AffineSlack.eval, sub_dotProduct]
  ring

theorem supported_common_height {Q : Gram} {S T : LatticeSimplex} {p q : AffineSlack}
    (hp : SupportsPlane Q S p) (hq : SupportsPlane Q T q) {x : Vec}
    (hx : x ∈ simplexRegion S ∩ simplexRegion T) : p.eval x=q.eval x := by
  have hs : 0 ≤ (planeDifference p q).eval x := by
    apply AffineSlack.nonneg_on_simplex _ _ _ hx.1
    intro i
    rw [planeDifference_eval,hp.2 i]
    exact sub_nonneg.mpr (hq.1 _)
  have ht : (planeDifference p q).eval x ≤ 0 := by
    apply AffineSlack.nonpos_on_simplex _ _ _ hx.2
    intro i
    rw [planeDifference_eval,hq.2 i]
    exact sub_nonpos.mpr (hp.1 _)
  rw [planeDifference_eval] at hs ht
  linarith

theorem supported_equal_normal_offset {Q : Gram} {S T : LatticeSimplex} {p q : AffineSlack}
    (hp : SupportsPlane Q S p) (hq : SupportsPlane Q T q) (h : p.normal=q.normal) :
    p.offset=q.offset := by
  have hs := hq.1 (S 0)
  have ht := hp.1 (T 0)
  rw [← hp.2 0] at hs
  rw [← hq.2 0] at ht
  simp only [AffineSlack.eval,h] at hs ht
  linarith

theorem exact_planes_normal_ne {Q : Gram} {S T : LatticeSimplex} {p q : AffineSlack}
    (hp : ExactPlane Q S p) (hq : ExactPlane Q T q)
    (hST : simplexVertices S ≠ simplexVertices T) : p.normal ≠ q.normal := by
  intro h
  have ho := supported_equal_normal_offset hp.1 hq.1 h
  apply hST
  ext n
  rw [← hp.2 n,← hq.2 n]
  simp only [AffineSlack.eval,h,ho]

theorem exact_simplex_inter_volume {Q : Gram} {S T : LatticeSimplex} {p q : AffineSlack}
    (hp : ExactPlane Q S p) (hq : ExactPlane Q T q)
    (hST : simplexVertices S ≠ simplexVertices T) :
    volume (simplexRegion S ∩ simplexRegion T)=0 := by
  apply measure_mono_null (t := (affineHyperplane (p.normal-q.normal)
    (p.offset-q.offset) : Set Vec))
  · intro x hx
    have he := supported_common_height hp.1 hq.1 hx
    change dotProduct (p.normal-q.normal) x=p.offset-q.offset
    rw [sub_dotProduct]
    simp only [AffineSlack.eval] at he
    linarith
  · exact affineHyperplane_volume (sub_ne_zero.mpr (exact_planes_normal_ne hp hq hST)) _

end D4.Delaunay
