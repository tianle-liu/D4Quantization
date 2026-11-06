import D4.C23VertexSupport
import D4.PrincipalFanCells
import D4.PrincipalSecondaryBoundary
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Nat.Bitwise

noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal

abbrev SecondaryCell := FanCell (Fin 30) (Fin 120)

def cellKey (c : SecondaryCell) : Nat := c.f.val * 900 + c.g.val * 30 + c.h.val

def facetSlack (Q : Gram) (n : IntVec) : AffineSlack where
  normal := castVec n
  offset := quadratic Q (castVec n)

def integerSecondaryGenerator (g : Fin 9 → IntVec) : Fin 10 → Matrix (Fin 4) (Fin 4) ℤ :=
  Fin.cases (gramMatrix ℤ) (fun j i k => g j i * g j k)

def integerSlack (g : Fin 9 → IntVec) (V : Fin 120 → Fin 10 → IntVec)
    (n : IntVec) (r : Fin 120) (k : Fin 10) : ℤ :=
  dotProduct n (integerSecondaryGenerator g k *ᵥ n) - dotProduct n (V r k)

def OnMask (mask : Fin 30 → Nat) (f : Fin 30) (r : Fin 120) : Prop :=
  (mask f).testBit r.val = true
instance (mask : Fin 30 → Nat) (f : Fin 30) (r : Fin 120) : Decidable (OnMask mask f r) :=
  inferInstanceAs (Decidable ((mask f).testBit r.val = true))

theorem integerSecondaryGenerator_cast (g : Fin 9 → IntVec) (k : Fin 10) :
    realMatrix (integerSecondaryGenerator g k) = secondaryGenerator (fun j => castVec (g j)) k := by
  refine Fin.cases ?_ (fun j => ?_) k
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [realMatrix, integerSecondaryGenerator, secondaryGenerator, gramMatrix]
  · ext i l
    simp [realMatrix, integerSecondaryGenerator, secondaryGenerator, rankOne, castVec]

theorem integerSlack_cast (g : Fin 9 → IntVec) (V : Fin 120 → Fin 10 → IntVec)
    (n : IntVec) (r : Fin 120) (k : Fin 10) :
    (integerSlack g V n r k : ℝ) =
      quadratic (secondaryGenerator (fun j => castVec (g j)) k) (castVec n) -
        dotProduct (castVec n) (castVec (V r k)) := by
  rw [← integerSecondaryGenerator_cast]
  simp [integerSlack, quadratic, dotProduct, Matrix.mulVec, castVec, realMatrix,
    Int.cast_sum, Int.cast_mul, Finset.mul_sum]

theorem facetSlack_secondaryVertex (g : Fin 9 → IntVec)
    (V : Fin 120 → Fin 10 → IntVec) (w : Fin 10 → ℝ) (n : IntVec) (r : Fin 120) :
    (facetSlack (secondaryForm (fun j => castVec (g j)) (w 0) (fun j => w j.succ)) n).eval
      (secondaryVertex V w r) = ∑ k, w k * (integerSlack g V n r k : ℝ) := by
  simp only [facetSlack, AffineSlack.eval, secondaryVertex]
  rw [← secondaryGenerator_sum, quadratic_sum]
  simp only [quadratic_smul, integerSlack_cast, mul_sub, Finset.sum_sub_distrib]
  congr 1
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem slack_nonneg_of_coefficients (g : Fin 9 → IntVec)
    (V : Fin 120 → Fin 10 → IntVec) (w : Fin 10 → ℝ) (n : IntVec) (r : Fin 120)
    (hw : ∀ k, 0 ≤ w k) (hc : ∀ k, 0 ≤ integerSlack g V n r k) :
    0 ≤ (facetSlack (secondaryForm (fun j => castVec (g j)) (w 0) (fun j => w j.succ)) n).eval
      (secondaryVertex V w r) := by
  rw [facetSlack_secondaryVertex]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (by exact_mod_cast hc k)

theorem slack_zero_of_coefficients (g : Fin 9 → IntVec)
    (V : Fin 120 → Fin 10 → IntVec) (w : Fin 10 → ℝ) (n : IntVec) (r : Fin 120)
    (hc : ∀ k, integerSlack g V n r k = 0) :
    (facetSlack (secondaryForm (fun j => castVec (g j)) (w 0) (fun j => w j.succ)) n).eval
      (secondaryVertex V w r) = 0 := by
  rw [facetSlack_secondaryVertex]
  simp only [hc, Int.cast_zero, mul_zero, Finset.sum_const_zero]

theorem slack_pos_of_coefficients (g : Fin 9 → IntVec)
    (V : Fin 120 → Fin 10 → IntVec) (w : Fin 10 → ℝ) (n : IntVec) (r : Fin 120)
    (hw : ∀ k, 0 < w k) (hc : ∀ k, 0 ≤ integerSlack g V n r k)
    (j : Fin 10) (hj : 0 < integerSlack g V n r j) :
    0 < (facetSlack (secondaryForm (fun k => castVec (g k)) (w 0) (fun k => w k.succ)) n).eval
      (secondaryVertex V w r) := by
  rw [facetSlack_secondaryVertex]
  apply Finset.sum_pos'
  · intro k _
    exact mul_nonneg (hw k).le (by exact_mod_cast hc k)
  · exact ⟨j, Finset.mem_univ _, mul_pos (hw j) (by exact_mod_cast hj)⟩

end D4.Secondary
