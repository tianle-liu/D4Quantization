import D4.NearestPoint
import D4.ClassificationDefs

/-!
# Discrete energy minimization for integer frames

For a positive-definite form, every bounded-energy family of a fixed finite
number of integer vectors belongs to a finite set. Hence any nonempty class
of integer frames, in particular the class of integer superbases, contains
a global energy minimizer. The constraint set need not be finite.
-/
noncomputable section
open Matrix Set

namespace D4.Classification
open Analytic

def frameEnergy {ι : Type*} [Fintype ι] (Q : Gram) (v : ι → IntVec) : ℝ :=
  ∑ i, quadratic Q (castVec (v i))

theorem finite_integer_quadratic_sublevel {Q : Gram} (hQ : Q.PosDef) (E : ℝ) :
    {z : IntVec | quadratic Q (castVec z) ≤ E}.Finite := by
  simpa only [zero_sub, quadratic, Matrix.mulVec_neg, neg_dotProduct,
    dotProduct_neg, neg_neg] using finite_nearest_sublevel hQ (0 : Vec) E

theorem frameEnergy_nonneg {ι : Type*} [Fintype ι]
    {Q : Gram} (hQ : Q.PosSemidef) (v : ι → IntVec) : 0 ≤ frameEnergy Q v :=
  Finset.sum_nonneg fun i _ => quadratic_nonneg hQ (castVec (v i))

theorem quadratic_le_frameEnergy {ι : Type*} [Fintype ι]
    {Q : Gram} (hQ : Q.PosSemidef) (v : ι → IntVec) (i : ι) :
    quadratic Q (castVec (v i)) ≤ frameEnergy Q v :=
  Finset.single_le_sum (fun j _ => quadratic_nonneg hQ (castVec (v j))) (Finset.mem_univ i)

theorem finite_frameEnergy_sublevel {ι : Type*} [Fintype ι]
    {Q : Gram} (hQ : Q.PosDef) (E : ℝ) :
    {v : ι → IntVec | frameEnergy Q v ≤ E}.Finite := by
  apply (Set.Finite.pi' (fun _ : ι => finite_integer_quadratic_sublevel hQ E)).subset
  intro v hv i
  exact (quadratic_le_frameEnergy hQ.posSemidef v i).trans hv

/-- A genuine global minimum over any nonempty class of integer frames. -/
theorem exists_frameEnergy_minimum {ι : Type*} [Fintype ι]
    {Q : Gram} (hQ : Q.PosDef) (S : Set (ι → IntVec)) (hS : S.Nonempty) :
    ∃ v ∈ S, ∀ w ∈ S, frameEnergy Q v ≤ frameEnergy Q w := by
  obtain ⟨v₀, hv₀⟩ := hS
  let T := {v ∈ S | frameEnergy Q v ≤ frameEnergy Q v₀}
  have hT : T.Finite := (finite_frameEnergy_sublevel hQ (frameEnergy Q v₀)).subset
    (fun _ hv => hv.2)
  obtain ⟨v, hv, hmin⟩ := Set.exists_min_image T (frameEnergy Q) hT ⟨v₀, hv₀, le_rfl⟩
  refine ⟨v, hv.1, ?_⟩
  intro w hw
  by_cases hb : frameEnergy Q w ≤ frameEnergy Q v₀
  · exact hmin w ⟨hw, hb⟩
  · exact hv.2.trans (le_of_lt (lt_of_not_ge hb))

theorem energy_transform_eq_frameEnergy (Q : Gram) (U : IntegerMatrix) :
    energy (transform Q U) = frameEnergy Q (fun i : Fin 5 => U *ᵥ superVector i) := by
  unfold energy frameEnergy transform
  apply Finset.sum_congr rfl
  intro i hi
  rw [quadratic_congruence, castVec_mulVec]

theorem transform_mul (Q : Gram) (U V : IntegerMatrix) :
    transform (transform Q U) V = transform Q (U * V) := by
  simp only [transform, realMatrix_mul, Matrix.transpose_mul, Matrix.mul_assoc]

/-- Every positive-definite form has an integrally congruent representative
whose superbase energy is a genuine global minimum. -/
theorem exists_energyMinimal {Q : Gram} (hQ : Q.PosDef) :
    ∃ R, IntegralCongruent Q R ∧ R.PosDef ∧ EnergyMinimal R := by
  let S : Set (Fin 5 → IntVec) :=
    {v | ∃ U : IntegerMatrix, IsUnit U.det ∧ v = fun i => U *ᵥ superVector i}
  have hS : S.Nonempty := by
    refine ⟨fun i => (1 : IntegerMatrix) *ᵥ superVector i, 1, ?_, rfl⟩
    simp
  obtain ⟨v, ⟨U, hU, rfl⟩, hmin⟩ := exists_frameEnergy_minimum hQ S hS
  refine ⟨transform Q U, ⟨U, hU, rfl⟩, posDef_unimodular_congruence hQ U hU, ?_⟩
  intro V hV
  rw [transform_mul]
  simp only [energy_transform_eq_frameEnergy]
  apply hmin
  refine ⟨U * V, ?_, rfl⟩
  rw [Matrix.det_mul]
  exact hU.mul hV

end D4.Classification
