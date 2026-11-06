import D4.ConeBounds
import D4.IntegralCongruence
import D4.ParameterEncoding
import D4.RayEvaluation
import D4.Classification
import D4.ParityMoment

/-!
# Assembly of Theorem A from classification and geometric moments

The classification and D4 ray integral are proved independently. The modular
assembly takes the three actual integral identities as an explicit argument;
CompleteTheoremA supplies their geometric proofs.
-/
noncomputable section
namespace D4
open Matrix Analytic CertifiedPolynomials

/-- The three actual moment identities on the positive-definite part of each
closed cone. -/
structure GeometricMomentIdentities : Prop where
  principal : ∀ (x : Nat → ℝ), (∀ i, 0 ≤ x i) →
    (principalForm (fun i => x i)).PosDef →
    12 * (principalForm (fun i => x i)).det * moment (principalForm (fun i => x i)) = S x
  secondary2 : ∀ (x : Nat → ℝ), (∀ i, 0 ≤ x i) →
    (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))).PosDef →
    60 * (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))).det *
      moment (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))) = N2 x
  secondary3 : ∀ (x : Nat → ℝ), (∀ i, 0 ≤ x i) →
    (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))).PosDef →
    60 * (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))).det *
      moment (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))) = N3 x

theorem principal_strict_of_geometric_moments (hM : GeometricMomentIdentities)
    {Q : RealGram} (hQ : Q.PosDef) (hcone : InPrincipalCone Q) :
    optimalConstant < normalizedMoment Q := by
  obtain ⟨w, hw, rfl⟩ := hcone
  have hx := principalParameters_nonneg hw
  have hQ' : (principalForm (fun i => principalParameters w i)).PosDef := by simpa using hQ
  simpa using principal_analytic_of_moment_identity (principalParameters w) hx hQ'
    (hM.principal _ hx hQ')

theorem secondary2_conclusion_of_geometric_moments (hM : GeometricMomentIdentities)
    {Q : RealGram} (hQ : Q.PosDef) (hcone : InSecondaryCone cone2Vectors Q) :
    optimalConstant ≤ normalizedMoment Q ∧
    (normalizedMoment Q = optimalConstant → ∃ c : ℝ, 0 < c ∧ Q = c • gramMatrix ℝ) := by
  obtain ⟨a, w, ha, hw, rfl⟩ := hcone
  let x := secondaryParameters a w
  have hx : ∀ i, 0 ≤ x i := secondaryParameters_nonneg ha hw
  have hQ' : (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))).PosDef := by
    simpa [x] using hQ
  have hm := hM.secondary2 x hx hQ'
  constructor
  · simpa [x] using secondary2_analytic_of_moment_identity x hx hQ' hm
  · intro he
    refine ⟨t2 x, t2_pos x hQ', ?_⟩
    have he' : normalizedMoment (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))) =
        optimalConstant := by simpa [x] using he
    simpa [x] using secondary2_analytic_equality x hx hQ' hm he'

theorem secondary3_conclusion_of_geometric_moments (hM : GeometricMomentIdentities)
    {Q : RealGram} (hQ : Q.PosDef) (hcone : InSecondaryCone cone3Vectors Q) :
    optimalConstant ≤ normalizedMoment Q ∧
    (normalizedMoment Q = optimalConstant → ∃ c : ℝ, 0 < c ∧ Q = c • gramMatrix ℝ) := by
  obtain ⟨a, w, ha, hw, rfl⟩ := hcone
  let x := secondaryParameters a w
  have hx : ∀ i, 0 ≤ x i := secondaryParameters_nonneg ha hw
  have hQ' : (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))).PosDef := by
    simpa [x] using hQ
  have hm := hM.secondary3 x hx hQ'
  constructor
  · simpa [x] using secondary3_analytic_of_moment_identity x hx hQ' hm
  · intro he
    refine ⟨t3 x, t3_pos x hQ', ?_⟩
    have he' : normalizedMoment (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))) =
        optimalConstant := by simpa [x] using he
    simpa [x] using secondary3_analytic_equality x hx hQ' hm he'

theorem threeCone_conclusion_of_geometric_moments (hM : GeometricMomentIdentities)
    {Q : RealGram} (hQ : Q.PosDef) (hcone : InThreeCones Q) :
    optimalConstant ≤ normalizedMoment Q ∧
    (normalizedMoment Q = optimalConstant → ∃ c : ℝ, 0 < c ∧ Q = c • gramMatrix ℝ) := by
  rcases hcone with h | h | h
  · have hs := principal_strict_of_geometric_moments hM hQ h
    exact ⟨hs.le, fun he => False.elim (hs.ne' he)⟩
  · exact secondary2_conclusion_of_geometric_moments hM hQ h
  · exact secondary3_conclusion_of_geometric_moments hM hQ h

theorem moment_gramMatrix_of_geometric_moments (hM : GeometricMomentIdentities) :
    moment (gramMatrix ℝ) = 13/30 := by
  have hpos : (secondaryForm cone2Vectors (rayCoordinates 0)
      (fun i => rayCoordinates (i+1))).PosDef := by
    rw [ray_secondaryForm]
    exact gramMatrix_posDef
  apply moment_gramMatrix_of_polynomial_identity
  simpa only [ray_secondaryForm, N2] using hM.secondary2 rayCoordinates rayCoordinates_nonneg hpos

theorem normalizedMoment_gramMatrix_of_geometric_moments (hM : GeometricMomentIdentities) :
    normalizedMoment (gramMatrix ℝ) = optimalConstant := by
  exact normalizedMoment_gramMatrix_of_moment (moment_gramMatrix_of_geometric_moments hM)

/-- General assembly with explicit classification and moment inputs. -/
theorem theoremA_of_coverage_and_moments (hcoverage : SecondaryConeCoverageTarget)
    (hM : GeometricMomentIdentities) : TheoremATarget := by
  intro Q hQ
  obtain ⟨R, hQR, hcone⟩ := hcoverage Q hQ
  have hR := threeCone_conclusion_of_geometric_moments hM (hQR.posDef hQ) hcone
  have hn := normalizedMoment_integralCongruent hQR
  constructor
  · rw [← hn]
    exact hR.1
  · constructor
    · intro he
      obtain ⟨c, hc, hray⟩ := hR.2 (hn.trans he)
      refine ⟨c, hc, ?_⟩
      rw [← hray]
      exact hQR.symm
    · intro hs
      rw [normalizedMoment_similarD4 hs]
      exact Quantizer.normalizedMoment_gramMatrix

/-- Combine the constructed Selling reduction with the three integral identities. -/
theorem theoremA_of_moments (hM : GeometricMomentIdentities) : TheoremATarget :=
  theoremA_of_coverage_and_moments secondaryConeCoverage hM

end D4
