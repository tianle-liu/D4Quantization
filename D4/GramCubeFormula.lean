import D4.GramCubeIntegral
import D4.GeometricTheoremB

/-! The Gram-cube formula for the actual normalized Voronoi moment in every
positive dimension, with all integer competitors included. -/
noncomputable section
open Matrix MeasureTheory Set
namespace D4.GramCoordinates

theorem gram_det {n : ℕ} (B : Form n) : (gram B).det = |B.det|^2 := by
  rw [gram, Matrix.det_mul, Matrix.det_transpose, sq_abs]
  ring

/-- Equation (gram-error), for an arbitrary invertible basis matrix. -/
theorem normalizedMoment_gram_cube {n : ℕ} (hn : 0 < n)
    (B : Form n) (hB : B.det ≠ 0) :
    FacetGeometry.normalizedCellMoment (lattice B hB) =
      (∫ x in cube n, gramNearest (gram B) x) /
        ((n:ℝ) * (gram B).det ^ (1/(n:ℝ))) := by
  have hd : (0:ℝ) < |B.det| := abs_pos.mpr hB
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp : (gram B).det ^ (1/(n:ℝ)) = |B.det| ^ (2/(n:ℝ)) := by
    rw [gram_det, ← Real.rpow_natCast |B.det| 2, ← Real.rpow_mul hd.le]
    congr 1
    ring
  have hv : |B.det| ^ (1+2/(n:ℝ)) = |B.det| * |B.det| ^ (2/(n:ℝ)) := by
    rw [Real.rpow_add hd, Real.rpow_one]
  unfold FacetGeometry.normalizedCellMoment ConePerspective.normalizedMoment
  simp only [Point, finrank_euclideanSpace, Fintype.card_fin, measureReal_def]
  rw [voronoi_volume B hB, ENNReal.toReal_ofReal hd.le, voronoi_moment B hB, hp, hv]
  field_simp [hd.ne', hn', (Real.rpow_pos_of_pos hd (2/(n:ℝ))).ne']
  ring

end D4.GramCoordinates
