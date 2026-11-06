import D4.PaperSymmetryC1
import D4.PaperSymmetryAction
import Mathlib.GroupTheory.Perm.Sign

namespace D4.PaperSymmetry.C1

theorem invariant_all (f : (Nat → ℝ) → ℝ)
    (hs : ∀ i : Fin 4, ∀ x, f (fun n => x (extend
      (edgeHom (Equiv.swap i.castSucc i.succ)) n)) = f x)
    (p : Equiv.Perm (Fin 5)) (x : Nat → ℝ) :
    f (fun n => x (extend (edgeHom p) n)) = f x := by
  let H := (invariantGroup f).comap edgeHom
  have h : Submonoid.closure (Set.range fun i : Fin 4 =>
      Equiv.swap i.castSucc i.succ) ≤ H.toSubmonoid := by
    apply Submonoid.closure_le.mpr
    rintro g ⟨i,rfl⟩
    exact hs i
  rw [Equiv.Perm.mclosure_swap_castSucc_succ] at h
  exact h (by trivial) x

end D4.PaperSymmetry.C1
