import D4.Targets

/-! Exact finite parameter encodings for the cone representations. -/
noncomputable section
namespace D4

def principalParameters (w : Fin 10 → ℝ) (n : Nat) : ℝ :=
  if h : n < 10 then w ⟨n, h⟩ else 0

@[simp] theorem principalParameters_apply (w : Fin 10 → ℝ) (i : Fin 10) :
    principalParameters w i = w i := by simp [principalParameters]

theorem principalParameters_nonneg {w : Fin 10 → ℝ} (hw : ∀ i, 0 ≤ w i) :
    ∀ n, 0 ≤ principalParameters w n := by
  intro n
  unfold principalParameters
  split_ifs <;> first | exact hw _ | exact le_rfl

def secondaryParameters (a : ℝ) (w : Fin 9 → ℝ) (n : Nat) : ℝ :=
  match n with
  | 0 => a
  | n+1 => if h : n < 9 then w ⟨n,h⟩ else 0

@[simp] theorem secondaryParameters_zero (a : ℝ) (w : Fin 9 → ℝ) :
    secondaryParameters a w 0 = a := rfl

@[simp] theorem secondaryParameters_succ (a : ℝ) (w : Fin 9 → ℝ) (i : Fin 9) :
    secondaryParameters a w (i+1) = w i := by simp [secondaryParameters]

theorem secondaryParameters_nonneg {a : ℝ} {w : Fin 9 → ℝ}
    (ha : 0 ≤ a) (hw : ∀ i, 0 ≤ w i) : ∀ n, 0 ≤ secondaryParameters a w n := by
  intro n
  cases n with
  | zero => exact ha
  | succ n =>
    change 0 ≤ (if h : n < 9 then w ⟨n,h⟩ else 0)
    split_ifs <;> first | exact hw _ | exact le_rfl

end D4
