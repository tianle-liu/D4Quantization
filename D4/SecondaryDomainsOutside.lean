import D4.DelaunayFiniteSemantics
import D4.DelaunayTranslations

/-! The opposite vertex in each actual adjacent-cell record lies outside the
 left simplex's vertex set. These are finite statements about integer sites. -/
namespace D4.Delaunay
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem facets1_opposite_outside : ∀ i : Fin 60,
    shiftedRight cells1 (facets1 i) (facets1 i).rightFace ∉
      simplexVertices (shiftedLeft cells1 (facets1 i)) := by decide +kernel

theorem facets2_opposite_outside : ∀ i : Fin 60,
    shiftedRight cells2 (facets2 i) (facets2 i).rightFace ∉
      simplexVertices (shiftedLeft cells2 (facets2 i)) := by decide +kernel

theorem facets3_opposite_outside : ∀ i : Fin 60,
    shiftedRight cells3 (facets3 i) (facets3 i).rightFace ∉
      simplexVertices (shiftedLeft cells3 (facets3 i)) := by decide +kernel

end D4.Delaunay
