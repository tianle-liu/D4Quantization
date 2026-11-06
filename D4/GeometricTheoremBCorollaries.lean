import D4.GeometricTheoremB
import D4.ConeAnalysisHexagon
import D4.ConeAnalysisSphereBound

/-! The dimension-two value and the strict improvement over the sphere
bound, for actual full-rank lattices. -/
noncomputable section
namespace D4.FacetGeometry
open Set MeasureTheory D4.ConeAnalysis
attribute [local instance] Classical.propDecidable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

theorem dimensionalConeBound_angle_mem (hd : 2 ≤ Module.finrank ℝ E) (m : ℝ)
    (hm : (Nat.card (FacetVectors L):ℝ) ≤ m) :
    0 < m ∧ ((Module.finrank ℝ E:ℝ)*dimensionBallVolume (Module.finrank ℝ E))/m ∈
      Ioo 0 (angle (Module.finrank ℝ E)
        (((Module.finrank ℝ E:ℝ)-1)*dimensionBallVolume (Module.finrank ℝ E-1)) (Real.pi/2)) := by
  letI : Nontrivial E := Module.finrank_pos_iff.mp (show 0 < Module.finrank ℝ E by omega)
  obtain ⟨T, hmem, hT⟩ := exists_finite_voronoi_halfspaces_full (L:=L)
  let S := T.filter (IsFacetVector L)
  let A := (Module.finrank ℝ E:ℝ)*dimensionBallVolume (Module.finrank ℝ E)
  have hangle : ∑ z ∈ S, facetSolidAngle L z = A := by
    dsimp [A]
    rw [← unitBall_volume_eq_dimension (F:=E)]
    exact sum_selected_facetSolidAngle hmem hT
  have hA : 0 < A := mul_pos (by exact_mod_cast (show 0 < Module.finrank ℝ E by omega))
    (dimensionBallVolume_pos _)
  have hS : S.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty] at hangle
    linarith
  have hcard : (S.card:ℝ) ≤ m :=
    (show (S.card:ℝ) ≤ (Nat.card (FacetVectors L):ℝ) by
      exact_mod_cast selected_facets_card_le hmem).trans hm
  have hcardpos : (0:ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  have hmpos : 0 < m := hcardpos.trans_le hcard
  refine ⟨hmpos, div_pos hA hmpos, ?_⟩
  have havg : A/(S.card:ℝ) < angle (Module.finrank ℝ E)
      (((Module.finrank ℝ E:ℝ)-1)*dimensionBallVolume (Module.finrank ℝ E-1)) (Real.pi/2) := by
    apply (div_lt_iff₀ hcardpos).mpr
    rw [← hangle]
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using
      Finset.sum_lt_sum_of_nonempty hS (fun z hz =>
        (facetSolidAngle_mem_dimension (Finset.mem_filter.mp hz).2 hd).2)
  exact ((div_le_div_iff₀ hmpos hcardpos).mpr
    (mul_le_mul_of_nonneg_left hcard hA.le)).trans_lt havg

theorem dimensionalConeBound_gt_sphere (hd : 2 ≤ Module.finrank ℝ E) (m : ℝ)
    (hm : (Nat.card (FacetVectors L):ℝ) ≤ m) :
    (dimensionBallVolume (Module.finrank ℝ E))^(-2/(Module.finrank ℝ E:ℝ)) /
        ((Module.finrank ℝ E:ℝ)+2) < dimensionalConeBound (Module.finrank ℝ E) m := by
  obtain ⟨hmpos, hu⟩ := dimensionalConeBound_angle_mem L hd m hm
  have hn : (0:ℝ) < Module.finrank ℝ E := by exact_mod_cast (show 0 < Module.finrank ℝ E by omega)
  have hk := dimensionBallVolume_pos (Module.finrank ℝ E)
  have H := facet_bound_gt_sphere (Module.finrank ℝ E) hd
    (dimensionBallVolume (Module.finrank ℝ E-1))
    ((Module.finrank ℝ E:ℝ)*dimensionBallVolume (Module.finrank ℝ E)) m
    (dimensionBallVolume_pos _) (mul_pos hn hk) hmpos hu
  have he : (Module.finrank ℝ E:ℝ) /
      ((Module.finrank ℝ E:ℝ)*dimensionBallVolume (Module.finrank ℝ E)) =
      (dimensionBallVolume (Module.finrank ℝ E))⁻¹ := by field_simp
  rw [he, Real.inv_rpow hk.le, ← Real.rpow_neg hk.le,
    show -(2/(Module.finrank ℝ E:ℝ)) = -2/(Module.finrank ℝ E:ℝ) by ring] at H
  exact H

theorem theoremB_strict_sphere (hd : 2 ≤ Module.finrank ℝ E) :
    (dimensionBallVolume (Module.finrank ℝ E))^(-2/(Module.finrank ℝ E:ℝ)) /
        ((Module.finrank ℝ E:ℝ)+2) < normalizedCellMoment L :=
  (dimensionalConeBound_gt_sphere L hd (Nat.card (FacetVectors L)) le_rfl).trans_le
    (theoremB_actual_facets L hd)

theorem theoremB_two (hd : Module.finrank ℝ E = 2) :
    5/(36*Real.sqrt 3) ≤ normalizedCellMoment L := by
  have H := theoremB L (by omega : 2 ≤ Module.finrank ℝ E)
  rw [hd] at H
  change (2*(2^2-1):ℕ)^(-2/(2:ℝ))*coneNormalizedMoment 2 (dimensionBallVolume (2-1))
    (((2:ℝ)*dimensionBallVolume 2)/(2*(2^2-1):ℕ)) ≤ _ at H
  rwa [dimension_two_bound_value] at H

end D4.FacetGeometry
