import D4.C23LocalCosts
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! The actual four-dimensional changes of coordinates preserve Lebesgue
measure; their determinant-one computation is connected to integration. -/
noncomputable section
namespace D4.C23Local
open Matrix MeasureTheory Analytic

theorem determinant_one_affine_preserving (B : Gram) (hB : B.det=1) (c : Vec) :
    MeasurePreserving (fun r : Vec => c+B*ᵥr) volume volume := by
  have hn : B.det ≠ 0 := by rw [hB]; norm_num
  have hm : Measurable (Matrix.toLin' B) := by
    have hc : Continuous (Matrix.toLin' B) := by
      change Continuous (fun x : Vec => B*ᵥx)
      unfold Matrix.mulVec dotProduct
      fun_prop
    exact hc.measurable
  refine ⟨?_,?_⟩
  · unfold Matrix.mulVec dotProduct
    fun_prop
  · change Measure.map ((fun x : Vec => c+x) ∘ Matrix.toLin' B) volume = volume
    rw [← Measure.map_map (show Measurable (fun x : Vec => c+x) from measurable_const.add measurable_id) hm,
      Real.map_matrix_volume_pi_eq_smul_volume_pi hn,Measure.map_smul,
      (measurePreserving_add_left (volume : Measure Vec) c).map_eq,hB]
    simp

theorem coordinates2_preserving (Q : Gram) :
    MeasurePreserving (coordinates2 Q) volume volume := by
  have he : coordinates2 Q = fun r => ![Q 0 0,Q 1 1,Q 2 2,Q 3 3]+coordinateMatrix2*ᵥr :=
    funext (coordinates2_affine Q)
  rw [he]
  exact determinant_one_affine_preserving coordinateMatrix2 coordinateMatrix2_det _

theorem coordinates3_preserving (Q : Gram) :
    MeasurePreserving (coordinates3 Q) volume volume := by
  have he : coordinates3 Q = fun r => ![Q 2 2,Q 3 3,Q 0 0,Q 1 1]+coordinateMatrix3*ᵥr :=
    funext (coordinates3_affine Q)
  rw [he]
  exact determinant_one_affine_preserving coordinateMatrix3 coordinateMatrix3_det _

end D4.C23Local
