import D4.SecondaryTypeInvariantC1
import D4.SecondaryTypeInvariantC2
import D4.SecondaryTypeInvariantC3

/-! The three actual periodic Delaunay simplex families are pairwise
inequivalent under every additive automorphism of the integer lattice.
The invariant counts neighbors lying in exactly 24 full-dimensional cells;
its three values, 10, 4, and 0, refer to the complete translated families. -/
namespace D4.Delaunay
open Analytic

theorem cells1_cells2_not_equivalent :
    ¬ ∃ e : IntVec ≃+ IntVec, ∀ S,
      S ∈ periodicVertexFamily cells1 ↔ S.image e ∈ periodicVertexFamily cells2 := by
  rintro ⟨e, he⟩
  have h := valenceCount_equiv _ _ e he 24
  rw [cells1_valenceCount_24, cells2_valenceCount_24] at h
  norm_num at h

theorem cells1_cells3_not_equivalent :
    ¬ ∃ e : IntVec ≃+ IntVec, ∀ S,
      S ∈ periodicVertexFamily cells1 ↔ S.image e ∈ periodicVertexFamily cells3 := by
  rintro ⟨e, he⟩
  have h := valenceCount_equiv _ _ e he 24
  rw [cells1_valenceCount_24, cells3_valenceCount_24] at h
  norm_num at h

theorem cells2_cells3_not_equivalent :
    ¬ ∃ e : IntVec ≃+ IntVec, ∀ S,
      S ∈ periodicVertexFamily cells2 ↔ S.image e ∈ periodicVertexFamily cells3 := by
  rintro ⟨e, he⟩
  have h := valenceCount_equiv _ _ e he 24
  rw [cells2_valenceCount_24, cells3_valenceCount_24] at h
  norm_num at h

end D4.Delaunay
