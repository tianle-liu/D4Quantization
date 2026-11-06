import D4.VoronoiFacetParity
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card

/-! The sharp universal bound on the number of Voronoi facets. -/
noncomputable section
open Set
open scoped InnerProductSpace
namespace D4.FacetGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {L : Submodule ℤ E} (b : Basis ι ℤ L)

def parityCoordinates (z : L) : ι → ZMod 2 := fun i => (b.repr z i : ZMod 2)

theorem sameParity_of_coordinates_eq {z w : L}
    (h : parityCoordinates b z = parityCoordinates b w) : SameParity L (z:E) (w:E) := by
  have hd (i : ι) : (2 : ℤ) ∣ b.repr z i - b.repr w i := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    rw [Int.cast_sub]
    exact sub_eq_zero.mpr (congrFun h i)
  let u : L := b.equivFun.symm (fun i => (b.repr z i - b.repr w i)/2)
  have he : z-w = (2 : ℤ) • u := by
    apply b.equivFun.injective
    ext i
    rw [map_sub, map_smul]
    change b.repr z i - b.repr w i = 2 * (b.equivFun u i)
    dsimp only [u]
    rw [LinearEquiv.apply_symm_apply, Int.mul_ediv_cancel' (hd i)]
  exact ⟨u, u.property, congrArg (fun x : L => (x:E)) he⟩

theorem facet_parity_ne_zero {z : L} (hz : IsFacetVector L (z:E)) : parityCoordinates b z ≠ 0 := by
  intro h
  apply facet_not_zero_parity hz
  have h0 : parityCoordinates b (0:L) = 0 := by ext i; simp [parityCoordinates]
  exact sameParity_of_coordinates_eq b (h.trans h0.symm)

def facetRepresentative (p : ι → ZMod 2) : L := by
  classical
  exact if h : ∃ z : L, IsFacetVector L (z:E) ∧ parityCoordinates b z = p then Classical.choose h else 0

theorem facetRepresentative_spec {p : ι → ZMod 2}
    (h : ∃ z : L, IsFacetVector L (z:E) ∧ parityCoordinates b z = p) :
    IsFacetVector L (facetRepresentative b p : E) ∧
      parityCoordinates b (facetRepresentative b p) = p := by
  rw [facetRepresentative, dif_pos h]
  exact Classical.choose_spec h

abbrev FacetVectors (L : Submodule ℤ E) := {z : L // IsFacetVector L (z:E)}

def facetEncoding (z : FacetVectors L) : {p : ι → ZMod 2 // p ≠ 0} × Bool := by
  classical
  exact (⟨parityCoordinates b z.val, facet_parity_ne_zero b z.property⟩,
    decide (z.val = facetRepresentative b (parityCoordinates b z.val)))

theorem facetEncoding_injective : Function.Injective (facetEncoding b) := by
  classical
  intro z w he
  have hp : parityCoordinates b z.val = parityCoordinates b w.val :=
    congrArg (fun x : {p : ι → ZMod 2 // p ≠ 0} × Bool => x.1.val) he
  have hs : (z.val = facetRepresentative b (parityCoordinates b z.val)) ↔
      (w.val = facetRepresentative b (parityCoordinates b z.val)) := by
    have hh := congrArg Prod.snd he
    simp only [facetEncoding, ← hp] at hh
    exact decide_eq_decide.mp hh
  have hr := facetRepresentative_spec b
    (show ∃ v : L, IsFacetVector L (v:E) ∧ parityCoordinates b v = parityCoordinates b z.val from
      ⟨z.val, z.property, rfl⟩)
  have hz := facets_sameParity_eq_or_neg hr.1 z.property
    (sameParity_of_coordinates_eq b hr.2)
  have hw := facets_sameParity_eq_or_neg hr.1 w.property
    (sameParity_of_coordinates_eq b (hr.2.trans hp))
  apply Subtype.ext
  by_cases hzr : z.val = facetRepresentative b (parityCoordinates b z.val)
  · exact hzr.trans (hs.mp hzr).symm
  · have hwr := mt hs.mpr hzr
    apply Subtype.ext
    rcases hz with h | h
    · exact False.elim (hzr (Subtype.ext h))
    · rcases hw with h' | h'
      · exact False.elim (hwr (Subtype.ext h'))
      · exact h.trans h'.symm

include b

/-- Finiteness follows from the parity argument; it is not assumed separately. -/
theorem finite_facetVectors : Finite (FacetVectors L) :=
  Finite.of_injective (facetEncoding b) (facetEncoding_injective b)

/-- Every parity class except zero contributes at most one opposite pair. -/
theorem card_facetVectors_le : Nat.card (FacetVectors L) ≤ 2 * (2 ^ Fintype.card ι - 1) := by
  letI := finite_facetVectors b
  letI := Fintype.ofFinite (FacetVectors L)
  have h := Fintype.card_le_of_injective (facetEncoding b) (facetEncoding_injective b)
  rw [Nat.card_eq_fintype_card]
  convert h using 1
  rw [Fintype.card_prod, Fintype.card_subtype_compl]
  simp [Fintype.card_fun, mul_comm]

end D4.FacetGeometry
