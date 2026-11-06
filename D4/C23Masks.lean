import D4.C23CellDefs

namespace D4.Secondary

/-- Equality of bounded integer masks is determined by their 120 meaningful bits. -/
theorem mask_eq_of_on_iff {a b : Nat} (ha : a < 2^120) (hb : b < 2^120)
    (h : ∀ r : Fin 120, a.testBit r.val = true ↔ b.testBit r.val = true) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 120
  · exact Bool.eq_iff_iff.mpr (h ⟨i, hi⟩)
  · have hp : 2^120 ≤ 2^i := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi)
    rw [Nat.testBit_lt_two_pow (ha.trans_le hp), Nat.testBit_lt_two_pow (hb.trans_le hp)]

/-- A different pair of finite masks supplies a vertex of their symmetric difference. -/
theorem mask_ne_witness {a b : Nat} (ha : a < 2^120) (hb : b < 2^120) (hne : a ≠ b) :
    ∃ r : Fin 120, (a.testBit r.val = true ∧ b.testBit r.val ≠ true) ∨
      (b.testBit r.val = true ∧ a.testBit r.val ≠ true) := by
  classical
  by_contra h
  apply hne
  apply mask_eq_of_on_iff ha hb
  intro r
  constructor
  · intro hra
    by_contra hrb
    exact h ⟨r, Or.inl ⟨hra, hrb⟩⟩
  · intro hrb
    by_contra hra
    exact h ⟨r, Or.inr ⟨hrb, hra⟩⟩

end D4.Secondary
