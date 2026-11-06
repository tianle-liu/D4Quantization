import D4.IntegralCongruence
import D4.NearestPoint

/-!
# Definitions for a direct four-dimensional reduction proof

The five standard integer vectors form a superbase: their sum is zero,
and the last four are the standard basis. The energy is the sum of their
five genuine quadratic values. No classification proposition is assumed.
-/

noncomputable section
namespace D4.Classification
open Matrix Analytic

/-- The standard superbase, with the dependent vector at index zero. -/
def superVector : Fin 5 → IntVec :=
  ![![-1,-1,-1,-1], ![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]]

/-- Gram matrix after changing the integer basis by the columns of `U`. -/
def transform (Q : RealGram) (U : IntegerMatrix) : RealGram :=
  (realMatrix U).transpose * Q * realMatrix U

/-- Sum of the five squared lengths in the standard superbase. -/
def energy (Q : RealGram) : ℝ :=
  ∑ i : Fin 5, quadratic Q (castVec (superVector i))

/-- Inner products of the five standard superbase vectors. -/
def superInner (Q : RealGram) (i j : Fin 5) : ℝ :=
  dotProduct (castVec (superVector i)) (Q *ᵥ castVec (superVector j))

/-- The only local inequalities needed below: no two incident inner
products have positive sum. This is a definition, not a classification hypothesis. -/
def PairReduced (Q : RealGram) : Prop :=
  ∀ i j k : Fin 5, i ≠ j → i ≠ k → j ≠ k →
    superInner Q i j + superInner Q i k ≤ 0

/-- Global minimization over the actual unimodular integer basis changes. -/
def EnergyMinimal (Q : RealGram) : Prop :=
  ∀ U : IntegerMatrix, IsUnit U.det → energy Q ≤ energy (transform Q U)

end D4.Classification
