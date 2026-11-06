import D4.SecondaryDomainsType
import D4.SecondaryTypeInvariantDefs

/-! Positive displayed cones realize their entire periodic Delaunay type. -/
noncomputable section
namespace D4.Delaunay
open Analytic Principal Matrix MeasureTheory Set
attribute [local instance] integerTranslation

theorem simplexVertices_translate (S : LatticeSimplex) (n : IntVec) :
    simplexVertices (translateSimplex S n)=
      (simplexVertices S).image (fun z => z+n) := by
  simp only [simplexVertices, Finset.image_image, Function.comp_def]
  rfl

theorem simplexMatrixZ_translate (S : LatticeSimplex) (n : IntVec) :
    simplexMatrixZ (translateSimplex S n)=simplexMatrixZ S := by
  ext i j
  simp only [simplexMatrixZ, translateSimplex, Pi.add_apply]
  ring

theorem periodic_type_of_exact_planes {m : ℕ} (Q : Gram) (hQ : Q.IsHermitian)
    (cells : Fin m → LatticeSimplex) (planes : Fin m → AffineSlack)
    (hexact : ∀ s, ExactPlane Q (cells s) (planes s))
    (hunimod : ∀ s, (simplexMatrixZ (cells s)).det=1 ∨
      (simplexMatrixZ (cells s)).det = -1)
    (hcover : periodicUnion (fun s => simplexRegion (cells s))=univ) :
    delaunayType Q=periodicVertexFamily cells := by
  rw [delaunayType_eq_of_exact_cover Q
    (fun p : Fin m × IntVec => translateSimplex (cells p.1) p.2)
    (fun p => translatePlane Q (planes p.1) p.2)
    (fun p => translatePlane_exact hQ (hexact p.1) p.2)]
  · ext F
    simp only [mem_setOf_eq, Prod.exists, simplexVertices_translate, periodicVertexFamily]
  · intro x
    have hx : x ∈ periodicUnion (fun s => simplexRegion (cells s)) := by rw [hcover]; trivial
    obtain ⟨p,hp⟩ := mem_iUnion.mp hx
    exact ⟨p,by simpa only [periodicPieces,simplexRegion_periodic] using hp⟩
  · intro p
    rw [unimodular_simplex_volume _ (by rw [simplexMatrixZ_translate]; exact hunimod p.1)]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num))

theorem positive_principal_delaunayType (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) :
    delaunayType (principalForm w)=periodicVertexFamily cells1 :=
  periodic_type_of_exact_planes _ (principal_isHermitian w) _ (cellPlane1 w)
    (cellPlane1_exact w hw) cells1_unimodular cells1_cover

theorem positive_secondary2_delaunayType (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) :
    delaunayType (secondaryForm cone2Vectors (w 0) (fun k => w k.succ))=
      periodicVertexFamily cells2 :=
  periodic_type_of_exact_planes _ (secondary_isHermitian _ _ _) _ (cellPlane2 w)
    (cellPlane2_exact w hw) cells2_unimodular cells2_cover

theorem positive_secondary3_delaunayType (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) :
    delaunayType (secondaryForm cone3Vectors (w 0) (fun k => w k.succ))=
      periodicVertexFamily cells3 :=
  periodic_type_of_exact_planes _ (secondary_isHermitian _ _ _) _ (cellPlane3 w)
    (cellPlane3_exact w hw) cells3_unimodular cells3_cover

end D4.Delaunay
