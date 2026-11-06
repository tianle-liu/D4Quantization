import D4.SecondaryDomainsRealization
import D4.SecondaryDomainsOutside
import D4.SecondaryDomainsLifting

/-! A displayed periodic family can be the actual Delaunay type only when all
 its neighbouring-cell liftings, hence all ten coordinates, are strict. -/
noncomputable section
namespace D4.Delaunay
open Analytic Principal Matrix MeasureTheory Set

def slackAffineMap (p : AffineSlack) : Vec →ᵃ[ℝ] ℝ where
  toFun := p.eval
  linear :=
    { toFun := fun x => - dotProduct p.normal x
      map_add' := by intro x y; simp only [dotProduct_add, neg_add_rev]; ring
      map_smul' := by intro a x; simp only [dotProduct_smul, smul_eq_mul, RingHom.id_apply]; ring }
  map_vadd' := by
    intro x v
    change p.offset-dotProduct p.normal (v+x)= -dotProduct p.normal v +
      (p.offset-dotProduct p.normal x)
    rw [dotProduct_add]
    ring

theorem exact_lifting_positive (g : Fin 10 → IntegerGram)
    (cells : Fin 24 → LatticeSimplex) (p : FacetRecord)
    (hp : facetCheck cells g p=true) (w : Fin 10 → ℝ) (L : AffineSlack)
    (hL : ExactPlane (generatedForm g w) (shiftedLeft cells p) L)
    (hout : shiftedRight cells p p.rightFace ∉ simplexVertices (shiftedLeft cells p)) :
    0 < liftingDifference g w cells p := by
  have hstrict : L.eval (castVec (shiftedRight cells p p.rightFace)) <
      quadratic (generatedForm g w) (castVec (shiftedRight cells p p.rightFace)) :=
    lt_of_le_of_ne (hL.1.1 _) (fun h => hout ((hL.2 _).mp h))
  have he := liftingDifference_affine cells g p hp w (slackAffineMap L) hL.1.2
  rw [← liftingDifference_eq g w cells p hp] at he
  rw [← he]
  exact sub_pos.mpr hstrict

theorem exactPlane_of_type {Q : Gram} {S : LatticeSimplex}
    (h : simplexVertices S ∈ delaunayType Q) : ∃ p, ExactPlane Q S p := by
  obtain ⟨⟨p,hp⟩,_⟩ := h
  refine ⟨p,⟨hp.1,?_⟩,hp.2⟩
  intro i
  exact (hp.2 _).mpr (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

theorem shiftedLeft_mem_family (cells : Fin 24 → LatticeSimplex) (p : FacetRecord) :
    simplexVertices (shiftedLeft cells p) ∈ periodicVertexFamily cells := by
  refine ⟨p.left,-p.leftAnchor,?_⟩
  rw [← simplexVertices_translate]
  congr 1

theorem positive_liftings_of_type (g : Fin 10 → IntegerGram)
    (cells : Fin 24 → LatticeSimplex) (facets : Fin 60 → FacetRecord)
    (hvalid : ∀ i, facetCheck cells g (facets i)=true)
    (hout : ∀ i, shiftedRight cells (facets i) (facets i).rightFace ∉
      simplexVertices (shiftedLeft cells (facets i)))
    (w : Fin 10 → ℝ) (h : delaunayType (generatedForm g w)=periodicVertexFamily cells) :
    ∀ i, 0 < liftingDifference g w cells (facets i) := by
  intro i
  have hi := shiftedLeft_mem_family cells (facets i)
  rw [← h] at hi
  obtain ⟨p,hp⟩ := exactPlane_of_type hi
  exact exact_lifting_positive g cells (facets i) (hvalid i) w p hp (hout i)

theorem principal_delaunayType_iff (w : Fin 10 → ℝ) :
    delaunayType (principalForm w)=periodicVertexFamily cells1 ↔ ∀ k, 0 < w k := by
  constructor
  · intro h
    apply (facets1_positive_iff w).mp
    apply positive_liftings_of_type _ _ _ facets1_valid facets1_opposite_outside w
    simpa only [generatedForm1] using h
  · exact positive_principal_delaunayType w

theorem secondary2_delaunayType_iff (w : Fin 10 → ℝ) :
    delaunayType (secondaryForm cone2Vectors (w 0) (fun k => w k.succ))=
      periodicVertexFamily cells2 ↔ ∀ k, 0 < w k := by
  constructor
  · intro h
    apply (facets2_positive_iff w).mp
    apply positive_liftings_of_type _ _ _ facets2_valid facets2_opposite_outside w
    simpa only [generatedForm2] using h
  · exact positive_secondary2_delaunayType w

theorem secondary3_delaunayType_iff (w : Fin 10 → ℝ) :
    delaunayType (secondaryForm cone3Vectors (w 0) (fun k => w k.succ))=
      periodicVertexFamily cells3 ↔ ∀ k, 0 < w k := by
  constructor
  · intro h
    apply (facets3_positive_iff w).mp
    apply positive_liftings_of_type _ _ _ facets3_valid facets3_opposite_outside w
    simpa only [generatedForm3] using h
  · exact positive_secondary3_delaunayType w

end D4.Delaunay
