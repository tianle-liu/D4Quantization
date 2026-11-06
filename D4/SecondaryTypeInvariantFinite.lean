import D4.SecondaryTypeInvariantDefs

/-! Exact finite enumeration of the star at the integer origin. Finset
deduplication makes this valid for any supplied periodic simplex family,
without assuming unique representatives or distinct listed vertices. -/
noncomputable section
namespace D4.Delaunay
open Analytic

def anchoredVertices {m : Nat} (cells : Fin m → LatticeSimplex) (p : Fin m × Fin 5) :
    Finset IntVec := (simplexVertices (cells p.1)).image (fun z => z-cells p.1 p.2)

def starCells {m : Nat} (cells : Fin m → LatticeSimplex) : Finset (Finset IntVec) :=
  Finset.univ.image (anchoredVertices cells)

def starValence {m : Nat} (cells : Fin m → LatticeSimplex) (z : IntVec) : Nat :=
  ((starCells cells).filter (fun S => z ∈ S)).card

def starNeighbors {m : Nat} (cells : Fin m → LatticeSimplex) : Finset IntVec :=
  ((starCells cells).biUnion (fun S => S)).erase 0

def finiteValenceCount {m : Nat} (cells : Fin m → LatticeSimplex) (k : Nat) : Nat :=
  ((starNeighbors cells).filter (fun z => starValence cells z = k)).card

theorem mem_starCells {m : Nat} (cells : Fin m → LatticeSimplex) (S : Finset IntVec) :
    S ∈ starCells cells ↔ S ∈ periodicVertexFamily cells ∧ (0 : IntVec) ∈ S := by
  constructor
  · intro h
    obtain ⟨⟨s,i⟩,_,rfl⟩ := Finset.mem_image.mp h
    refine ⟨⟨s,-cells s i,?_⟩,?_⟩
    · simp only [anchoredVertices,sub_eq_add_neg]
    · exact Finset.mem_image.mpr ⟨cells s i,
        Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,sub_self _⟩
  · rintro ⟨⟨s,n,hS⟩,h0⟩
    rw [hS] at h0
    obtain ⟨z,hz,hn⟩ := Finset.mem_image.mp h0
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hz
    have hn' : n = -cells s i := by
      calc
        n = -cells s i + (cells s i+n) := by abel
        _ = -cells s i := by rw [hi,hn,add_zero]
    apply Finset.mem_image.mpr
    refine ⟨(s,i),Finset.mem_univ _,?_⟩
    simp only [anchoredVertices,hS,hn',sub_eq_add_neg]

theorem edgeValence_eq_starValence {m : Nat} (cells : Fin m → LatticeSimplex) (z : IntVec) :
    edgeValence (periodicVertexFamily cells) z = starValence cells z := by
  unfold edgeValence starValence
  have hp (S : Finset IntVec) :
      (S ∈ periodicVertexFamily cells ∧ (0 : IntVec) ∈ S ∧ z ∈ S) ↔
        S ∈ (starCells cells).filter (fun T => z ∈ T) := by
    rw [Finset.mem_filter,mem_starCells]
    tauto
  rw [Nat.card_congr (Equiv.subtypeEquivRight hp)]
  exact Nat.card_eq_finsetCard _

theorem starValence_pos_iff {m : Nat} (cells : Fin m → LatticeSimplex) (z : IntVec) :
    0 < starValence cells z ↔ ∃ S ∈ starCells cells, z ∈ S := by
  simp only [starValence,Finset.card_pos,Finset.filter_nonempty_iff]

theorem mem_starNeighbors {m : Nat} (cells : Fin m → LatticeSimplex) (z : IntVec) :
    z ∈ starNeighbors cells ↔ z ≠ 0 ∧ 0 < starValence cells z := by
  simp only [starNeighbors,Finset.mem_erase,Finset.mem_biUnion,starValence_pos_iff]

theorem valenceCount_eq_finiteValenceCount {m : Nat} (cells : Fin m → LatticeSimplex)
    (k : Nat) (hk : 0 < k) :
    valenceCount (periodicVertexFamily cells) k = finiteValenceCount cells k := by
  unfold valenceCount finiteValenceCount
  have hp (z : IntVec) :
      (z ≠ 0 ∧ edgeValence (periodicVertexFamily cells) z = k) ↔
        z ∈ (starNeighbors cells).filter (fun w => starValence cells w = k) := by
    rw [Finset.mem_filter,mem_starNeighbors,edgeValence_eq_starValence]
    constructor
    · rintro ⟨hz,h⟩
      exact ⟨⟨hz,h ▸ hk⟩,h⟩
    · exact fun h => ⟨h.1.1,h.2⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hp)]
  exact Nat.card_eq_finsetCard _

end D4.Delaunay
