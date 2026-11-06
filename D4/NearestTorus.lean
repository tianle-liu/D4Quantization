import D4.Voronoi

/-! A common nearest-site face with fewer than twice as many total sites
has no nontrivial identification under lattice translation. -/
noncomputable section
namespace D4.Analytic
open Matrix Set

theorem quadratic_parallelogram (Q : Gram) (x y : Vec) :
    quadratic Q (x+y) + quadratic Q (x-y) = 2*quadratic Q x + 2*quadratic Q y := by
  simp only [quadratic, Matrix.mulVec_add, Matrix.mulVec_sub,
    add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub]
  ring

private theorem castVec_add (z n : IntVec) : castVec (z+n) = castVec z + castVec n := by
  ext i
  simp [castVec]

theorem common_shifted_nearest_force_zero {Q : Gram} (hQ : Q.PosDef)
    (x : Vec) (s n : IntVec)
    (hx : quadratic Q (x-castVec s) = quadratic Q (x-castVec (s+n)))
    (hy : quadratic Q (x+castVec n-castVec s) =
      quadratic Q (x+castVec n-castVec (s+n))) : n=0 := by
  rw [castVec_add] at hx hy
  have he₁ : x-(castVec s+castVec n) = (x-castVec s)-castVec n := by abel
  have he₂ : x+castVec n-(castVec s+castVec n) = x-castVec s := by abel
  have he₃ : x+castVec n-castVec s = (x-castVec s)+castVec n := by abel
  rw [he₁] at hx
  rw [he₂,he₃] at hy
  have hp := quadratic_parallelogram Q (x-castVec s) (castVec n)
  have hz : quadratic Q (castVec n)=0 := by linarith
  have hv : castVec n=0 := by
    by_contra hn
    have hpos := hQ.2 (castVec n) hn
    change 0 < quadratic Q (castVec n) at hpos
    linarith
  apply castVec_injective
  have hzero : castVec (0 : IntVec) = 0 := by ext i; simp [castVec]
  rw [hzero]
  exact hv

/-- This covers, in particular, a square face with four common sites and at
most six nearest sites at each point. -/
theorem nearest_face_translate_injective {Q : Gram} (hQ : Q.PosDef)
    (F : Set Vec) (S : Finset IntVec)
    (hS : ∀ x ∈ F, ∀ z ∈ S, quadratic Q (x-castVec z) = nearest Q x)
    (hcount : ∀ x ∈ F, ∃ T : Finset IntVec,
      (∀ z : IntVec, quadratic Q (x-castVec z) = nearest Q x → z ∈ T) ∧
      T.card < 2*S.card) :
    ∀ x ∈ F, ∀ n : IntVec, x+castVec n ∈ F → n=0 := by
  classical
  intro x hx n hxn
  obtain ⟨T,hT,hcard⟩ := hcount (x+castVec n) hxn
  have hST : S ⊆ T := fun z hz => hT z (hS _ hxn z hz)
  have hshift : S.image (fun z => z+n) ⊆ T := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    apply hT
    rw [nearest_integer_translate, castVec_add]
    have he : x+castVec n-(castVec w+castVec n) = x-castVec w := by abel
    rw [he]
    exact hS x hx w hw
  have hnot : ¬ Disjoint S (S.image (fun z => z+n)) := by
    intro hd
    have hsub : S ∪ S.image (fun z => z+n) ⊆ T := Finset.union_subset hST hshift
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ (fun a b h => add_right_cancel h)] at hc
    omega
  obtain ⟨z,hz,himage⟩ := Finset.not_disjoint_iff.mp hnot
  obtain ⟨w,hsource,rfl⟩ := Finset.mem_image.mp himage
  apply common_shifted_nearest_force_zero hQ x w n
  · exact (hS x hx w hsource).trans (hS x hx (w+n) hz).symm
  · exact (hS (x+castVec n) hxn w hsource).trans (hS (x+castVec n) hxn (w+n) hz).symm

end D4.Analytic
