import D4.PaperMonomialAction

/-! Burnside's lemma applied to the actual canonical degree-five monomials. -/
noncomputable section
namespace D4.PaperSymmetry
open Certificate PaperStatistics
open scoped BigOperators
attribute [local irreducible] degreeFive

def orbitCount (G : Subgroup Perm) : Nat :=
  Nat.card (MulAction.orbitRel.Quotient G DegreeFiveMonomial)

theorem sum_fixedCount (G : Subgroup Perm) (ps : List Perm)
    (hps : ∀ p, p ∈ ps ↔ p ∈ G) (hd : ps.Nodup) :
    (ps.map fixedCount).sum = orbitCount G * ps.length := by
  classical
  letI : Fintype G := Fintype.ofFinset ps.toFinset
    (fun p => List.mem_toFinset.trans (hps p))
  letI : Fintype (MulAction.orbitRel.Quotient G DegreeFiveMonomial) := Fintype.ofFinite _
  have hc : Fintype.card G=ps.length := by
    calc
      _ = ps.toFinset.card := Fintype.card_ofFinset ps.toFinset
        (fun p => List.mem_toFinset.trans (hps p))
      _ = _ := List.toFinset_card_of_nodup hd
  have hf (p : G) : fixedCount p.1=Fintype.card (MulAction.fixedBy DegreeFiveMonomial p) := by
    exact (fixedCount_eq p.1).trans Nat.card_eq_fintype_card
  calc
    (ps.map fixedCount).sum = ∑ p ∈ ps.toFinset, fixedCount p := (List.sum_toFinset _ hd).symm
    _ = ∑ p : G, fixedCount p.1 :=
      Finset.sum_subtype ps.toFinset (fun p => List.mem_toFinset.trans (hps p)) fixedCount
    _ = ∑ p : G, Fintype.card (MulAction.fixedBy DegreeFiveMonomial p) :=
      Finset.sum_congr rfl (fun p _ => hf p)
    _ = orbitCount G * ps.length := by
      rw [MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group,hc]
      simp only [orbitCount,Nat.card_eq_fintype_card]

end D4.PaperSymmetry
