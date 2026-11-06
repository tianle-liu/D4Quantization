import D4.Targets
import D4.KernelCompute

/-! Exact lattice simplices and adjacent-facet certificates for the three cones. -/
namespace D4.Delaunay
open Matrix Analytic

abbrev LatticeSimplex := Fin 5 → IntVec
abbrev IntegerGram := Matrix (Fin 4) (Fin 4) ℤ

def simplexMatrixZ (S : LatticeSimplex) : IntegerGram :=
  fun i j => S j.succ i-S 0 i

def quadraticZ (Q : IntegerGram) (z : IntVec) : ℤ := dotProduct z (Q *ᵥ z)

structure FacetRecord where
  left : Fin 24
  leftFace : Fin 5
  right : Fin 24
  rightFace : Fin 5
  leftAnchor : IntVec
  rightAnchor : IntVec
  barycentric : Fin 5 → ℤ
  lifting : Fin 10 → ℤ

structure FlipRecord where
  index : Fin 24
  old : LatticeSimplex
  replacement : LatticeSimplex
  shift : IntVec
  order : Fin 5 → Fin 5
  newShift : IntVec
  newOrder : Fin 5 → Fin 5

def shiftedLeft (cells : Fin 24 → LatticeSimplex) (p : FacetRecord) : LatticeSimplex :=
  fun i => cells p.left i-p.leftAnchor

def shiftedRight (cells : Fin 24 → LatticeSimplex) (p : FacetRecord) : LatticeSimplex :=
  fun i => cells p.right i-p.rightAnchor

def facetVertices (S : LatticeSimplex) (i : Fin 5) : Finset IntVec :=
  (Finset.univ.erase i).image S

def facetCheck (cells : Fin 24 → LatticeSimplex)
    (generators : Fin 10 → IntegerGram) (p : FacetRecord) : Bool := decide (
  p.left ≠ p.right ∧
  facetVertices (shiftedLeft cells p) p.leftFace =
    facetVertices (shiftedRight cells p) p.rightFace ∧
  (∑ i, p.barycentric i)=1 ∧
  (∑ i, p.barycentric i • shiftedLeft cells p i) = shiftedRight cells p p.rightFace ∧
  p.barycentric p.leftFace = -1 ∧
  ∀ k : Fin 10, p.lifting k =
    quadraticZ (generators k) (shiftedRight cells p p.rightFace)-
      ∑ i, p.barycentric i * quadraticZ (generators k) (shiftedLeft cells p i))

def facetOccurrences (pairs : Fin 60 → FacetRecord) : List (Fin 24 × Fin 5) :=
  (List.finRange 60).flatMap fun i =>
    [(pairs i |>.left,pairs i |>.leftFace),(pairs i |>.right,pairs i |>.rightFace)]

def occurrenceCheck (pairs : Fin 60 → FacetRecord) : Bool := decide (
  (facetOccurrences pairs).Nodup ∧
  (facetOccurrences pairs).toFinset = Finset.univ)

def unimodularCheck (cells : Fin 24 → LatticeSimplex) : Bool :=
  (List.finRange 24).all fun i => decide (
    (simplexMatrixZ (cells i)).det=1 ∨ (simplexMatrixZ (cells i)).det = -1)

def flipCheck (before after : Fin 24 → LatticeSimplex) (p : FlipRecord) : Bool := decide (
  Function.Bijective p.order ∧ Function.Bijective p.newOrder ∧
  (∀ i, before p.index i=p.old (p.order i)+p.shift) ∧
  (∀ i, after p.index i=p.replacement (p.newOrder i)+p.newShift))

end D4.Delaunay
