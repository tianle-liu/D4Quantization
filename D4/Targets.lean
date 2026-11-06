import D4.Definitions
import D4.Lattice

/-!
# Geometric statement interfaces

All declarations named `...Target` below are definitions of propositions.
These interfaces are proved in the classification and complete optimality modules;
they are definitions of statements, not additional axioms.
-/
noncomputable section
namespace D4
open Matrix

abbrev RealGram := Matrix (Fin 4) (Fin 4) ℝ
abbrev IntegerMatrix := Matrix (Fin 4) (Fin 4) ℤ

def realMatrix (U : IntegerMatrix) : RealGram := U.map (Int.castRingHom ℝ)

/-- Change of integer basis, with unimodularity expressed by a unit determinant. -/
def IntegralCongruent (Q R : RealGram) : Prop :=
  ∃ U : IntegerMatrix, IsUnit U.det ∧
    R = (realMatrix U).transpose * Q * realMatrix U

/-- Similarity to the displayed D₄ Gram matrix, including an integer basis change. -/
def SimilarD4Gram (Q : RealGram) : Prop :=
  ∃ c : ℝ, 0 < c ∧ IntegralCongruent (c • gramMatrix ℝ) Q

/-- The full Gram-matrix version of Theorem A, including both equality directions.
Proved by `D4.theoremA` in `D4.CompleteTheoremA`. -/
def TheoremATarget : Prop :=
  ∀ Q : RealGram, Q.PosDef →
    Analytic.optimalConstant ≤ Analytic.normalizedMoment Q ∧
    (Analytic.normalizedMoment Q = Analytic.optimalConstant ↔ SimilarD4Gram Q)

/-- The actual moment evaluation on the D₄ ray, proved in `D4.ParityMoment`. -/
def D4MomentTarget : Prop :=
  Analytic.moment (gramMatrix ℝ) = 13 / 30

def cone1Vectors : Fin 10 → Fin 4 → ℝ :=
  ![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1],
    ![1,-1,0,0], ![1,0,-1,0], ![1,0,0,-1],
    ![0,1,-1,0], ![0,1,0,-1], ![0,0,1,-1]]

def principalForm (w : Fin 10 → ℝ) : RealGram :=
  ∑ i, w i • rankOne (cone1Vectors i)

def secondaryForm (v : Fin 9 → Fin 4 → ℝ) (a : ℝ) (w : Fin 9 → ℝ) : RealGram :=
  a • gramMatrix ℝ + ∑ i, w i • rankOne (v i)

def InPrincipalCone (Q : RealGram) : Prop :=
  ∃ w : Fin 10 → ℝ, (∀ i, 0 ≤ w i) ∧ Q = principalForm w

def InSecondaryCone (v : Fin 9 → Fin 4 → ℝ) (Q : RealGram) : Prop :=
  ∃ a : ℝ, ∃ w : Fin 9 → ℝ, 0 ≤ a ∧ (∀ i, 0 ≤ w i) ∧ Q = secondaryForm v a w

def InThreeCones (Q : RealGram) : Prop :=
  InPrincipalCone Q ∨ InSecondaryCone cone2Vectors Q ∨ InSecondaryCone cone3Vectors Q

/-- The closed-cone coverage statement, proved by the integral reduction and
classification modules. -/
def SecondaryConeCoverageTarget : Prop :=
  ∀ Q : RealGram, Q.PosDef → ∃ R : RealGram, IntegralCongruent Q R ∧ InThreeCones R

end D4
