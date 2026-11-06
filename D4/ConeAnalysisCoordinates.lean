import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Euclidean product coordinates with their actual canonical volume.
This supplies the measure bridge between an orthogonal splitting and
the ordinary product measure used in the cone integrals. -/
noncomputable section
namespace D4.ConeAnalysis
open MeasureTheory

theorem prodLp_volume_preserving {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    [MeasurableSpace (WithLp 2 (E × F))] [BorelSpace (WithLp 2 (E × F))] :
    MeasurePreserving (WithLp.prodContinuousLinearEquiv 2 ℝ E F)
      volume ((volume : Measure E).prod (volume : Measure F)) := by
  let b := stdOrthonormalBasis ℝ E
  let c := stdOrthonormalBasis ℝ F
  refine ⟨(WithLp.prodContinuousLinearEquiv 2 ℝ E F).continuous.measurable, ?_⟩
  rw [← (b.prod c).addHaar_eq_volume, Basis.map_addHaar]
  have he : (b.prod c).toBasis.map (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toLinearEquiv =
      b.toBasis.prod c.toBasis := by
    ext i : 1
    cases i <;> simp [OrthonormalBasis.prod, WithLp.prodContinuousLinearEquiv]
  rw [he, Basis.prod_addHaar, b.addHaar_eq_volume, c.addHaar_eq_volume]

end D4.ConeAnalysis
