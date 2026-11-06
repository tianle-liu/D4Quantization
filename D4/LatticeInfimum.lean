import D4.GeometricTheoremBCorollaries
import D4.ConeAnalysisCount

noncomputable section
namespace D4.FacetGeometry
open Set MeasureTheory D4.ConeAnalysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Values of the actual normalized moment, over all full-rank Euclidean lattices. -/
def latticeMomentValues : Set ℝ :=
  {g | ∃ L : Submodule ℤ E, ∃ _ : DiscreteTopology L,
    ∃ _ : IsZLattice ℝ L, normalizedCellMoment L = g}

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

theorem latticeMomentValues_mem : normalizedCellMoment L ∈ latticeMomentValues (E := E) :=
  ⟨L,inferInstance,inferInstance,rfl⟩

theorem optimal_lattice_bracket (hd : 2 ≤ Module.finrank ℝ E) :
    dimensionalConeBound (Module.finrank ℝ E) (2*((2:ℕ)^Module.finrank ℝ E-1):ℕ) ≤
      sInf (latticeMomentValues (E := E)) ∧
    sInf (latticeMomentValues (E := E)) ≤ normalizedCellMoment L := by
  have hlow : ∀ g ∈ latticeMomentValues (E := E),
      dimensionalConeBound (Module.finrank ℝ E) (2*((2:ℕ)^Module.finrank ℝ E-1):ℕ) ≤ g := by
    rintro g ⟨L',hD,hZ,rfl⟩
    exact theoremB L' hd
  have hne : (latticeMomentValues (E := E)).Nonempty := ⟨_,latticeMomentValues_mem L⟩
  exact ⟨le_csInf hne hlow, csInf_le ⟨_,hlow⟩ (latticeMomentValues_mem L)⟩

theorem dimensionalConeBound_facet_count_comparison (hd : 2 ≤ Module.finrank ℝ E) :
    dimensionalConeBound (Module.finrank ℝ E) (2*((2:ℕ)^Module.finrank ℝ E-1):ℕ) ≤
      dimensionalConeBound (Module.finrank ℝ E) (Nat.card (FacetVectors L)) := by
  obtain ⟨hm,hu⟩ := dimensionalConeBound_angle_mem L hd (Nat.card (FacetVectors L)) le_rfl
  apply countConeBound_antitone (Module.finrank ℝ E) hd _ _ _ _
    (dimensionBallVolume_pos _)
  · exact mul_pos (by exact_mod_cast (show 0 < Module.finrank ℝ E by omega))
      (dimensionBallVolume_pos _)
  · exact hm
  · exact_mod_cast card_facetVectors_le_finrank (L := L)
  · exact hu

end D4.FacetGeometry
