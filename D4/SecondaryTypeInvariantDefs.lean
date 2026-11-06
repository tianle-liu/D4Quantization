import D4.DelaunayTranslations
import Mathlib.SetTheory.Cardinal.Finite

/-! Actual periodic lattice simplex families and an integral-coordinate
invariant: the number of neighbors incident with a prescribed number of
full-dimensional cells. No Euclidean metric or chosen vertex ordering
enters this invariant. -/
noncomputable section
namespace D4.Delaunay
open Analytic

def periodicVertexFamily {m : Nat} (cells : Fin m → LatticeSimplex) : Set (Finset IntVec) :=
  {S | ∃ s n, S = (simplexVertices (cells s)).image (fun z => z+n)}

def edgeValence (F : Set (Finset IntVec)) (z : IntVec) : Nat :=
  Nat.card {S : Finset IntVec // S ∈ F ∧ (0 : IntVec) ∈ S ∧ z ∈ S}

def valenceCount (F : Set (Finset IntVec)) (k : Nat) : Nat :=
  Nat.card {z : IntVec // z ≠ 0 ∧ edgeValence F z = k}

theorem image_mem_equiv (e : IntVec ≃+ IntVec) (S : Finset IntVec) (z : IntVec) :
    e z ∈ S.image e ↔ z ∈ S := by
  constructor
  · rintro h
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
    exact e.injective he ▸ hw
  · intro h
    exact Finset.mem_image.mpr ⟨z,h,rfl⟩

/-- Every additive equivalence of the integer lattice preserves actual
edge valences when it maps the full cell family. In particular this applies
to every element of GL(4, ℤ). -/
theorem edgeValence_equiv (F G : Set (Finset IntVec)) (e : IntVec ≃+ IntVec)
    (h : ∀ S, S ∈ F ↔ S.image e ∈ G) (z : IntVec) :
    edgeValence F z = edgeValence G (e z) := by
  unfold edgeValence
  apply Nat.card_congr
  refine Equiv.subtypeEquiv e.toEquiv.finsetCongr ?_
  intro S
  change (S ∈ F ∧ (0 : IntVec) ∈ S ∧ z ∈ S) ↔
    (S.map e.toEquiv.toEmbedding ∈ G ∧ (0 : IntVec) ∈ S.map e.toEquiv.toEmbedding ∧
      e z ∈ S.map e.toEquiv.toEmbedding)
  have h0 : (0 : IntVec) ∈ S.image e ↔ (0 : IntVec) ∈ S := by
    simpa only [map_zero] using image_mem_equiv e S 0
  have hmap : S.map e.toEquiv.toEmbedding = S.image e := Finset.map_eq_image _ _
  rw [hmap, h0, image_mem_equiv]
  exact and_congr (h S) Iff.rfl

theorem valenceCount_equiv (F G : Set (Finset IntVec)) (e : IntVec ≃+ IntVec)
    (h : ∀ S, S ∈ F ↔ S.image e ∈ G) (k : Nat) :
    valenceCount F k = valenceCount G k := by
  unfold valenceCount
  apply Nat.card_congr
  refine Equiv.subtypeEquiv e.toEquiv ?_
  intro z
  have hz : e z ≠ 0 ↔ z ≠ 0 := by
    constructor
    · intro hne he
      exact hne (by simpa only [he,map_zero])
    · intro hne he
      exact hne (e.injective (by simpa only [map_zero] using he))
  exact and_congr hz.symm (iff_of_eq (congrArg (fun n => n=k) (edgeValence_equiv F G e h z)))

end D4.Delaunay
