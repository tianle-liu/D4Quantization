import D4.DelaunayDefs
import D4.PrincipalGeometry

noncomputable section
namespace D4.Delaunay
open Matrix Analytic Principal

def generatedForm (g : Fin 10 → IntegerGram) (w : Fin 10 → ℝ) : Gram :=
  ∑ k, w k • realMatrix (g k)

theorem quadraticZ_cast (Q : IntegerGram) (z : IntVec) :
    quadratic (realMatrix Q) (castVec z)=(quadraticZ Q z:ℝ) := by
  simp [quadratic, quadraticZ, realMatrix, castVec, dotProduct, Matrix.mulVec]

theorem quadratic_generated (g : Fin 10 → IntegerGram) (w : Fin 10 → ℝ) (z : IntVec) :
    quadratic (generatedForm g w) (castVec z)=∑ k, w k*(quadraticZ (g k) z:ℝ) := by
  rw [generatedForm, quadratic_sum]
  simp only [quadratic_smul, quadraticZ_cast]

def liftingDifference (g : Fin 10 → IntegerGram) (w : Fin 10 → ℝ)
    (cells : Fin 24 → LatticeSimplex) (p : FacetRecord) : ℝ :=
  quadratic (generatedForm g w) (castVec (shiftedRight cells p p.rightFace))-
    ∑ i, (p.barycentric i:ℝ)*
      quadratic (generatedForm g w) (castVec (shiftedLeft cells p i))

/-- The checked integer coefficients equal the actual quadratic lifting
difference for every real choice of the cone weights. -/
theorem liftingDifference_eq (g : Fin 10 → IntegerGram) (w : Fin 10 → ℝ)
    (cells : Fin 24 → LatticeSimplex) (p : FacetRecord)
    (hp : facetCheck cells g p=true) :
    liftingDifference g w cells p=∑ k, w k*(p.lifting k:ℝ) := by
  have h := of_decide_eq_true hp
  have hc := h.2.2.2.2.2
  unfold liftingDifference
  simp only [quadratic_generated, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [hc k]
  push_cast
  rw [mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem facetCheck_geometry (cells : Fin 24 → LatticeSimplex)
    (g : Fin 10 → IntegerGram) (p : FacetRecord) (hp : facetCheck cells g p=true) :
    p.left ≠ p.right ∧
    facetVertices (shiftedLeft cells p) p.leftFace=
      facetVertices (shiftedRight cells p) p.rightFace ∧
    (∑ i, p.barycentric i)=1 ∧
    (∑ i, p.barycentric i • shiftedLeft cells p i)=shiftedRight cells p p.rightFace ∧
    p.barycentric p.leftFace = -1 := by
  have h := of_decide_eq_true hp
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩

end D4.Delaunay
