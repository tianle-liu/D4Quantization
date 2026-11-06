import D4.C2CellTensors
import D4.C2MomentUpper
import D4.C2Contraction
import D4.CertificateContinuity
import D4.PrincipalSecondaryBoundary
set_option maxHeartbeats 0
noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal Certificate CertificateMoments

theorem c2_contraction_eval_upper (w : Fin 10 → ℝ) :
    eval (extendWeight w) (sumFast c2ContractionPolys) =
      upperContraction (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).adjugate (c2RealTensor w) := by
  rw [eval_sumFast]
  simp only [c2ContractionPolys,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    eval_scale,Int.cast_ofNat,add_zero]
  rw [c2Contract00_eval, c2Contract01_eval, c2Contract02_eval, c2Contract03_eval, c2Contract11_eval, c2Contract12_eval, c2Contract13_eval, c2Contract22_eval, c2Contract23_eval, c2Contract33_eval]
  have ha00 := C2.adjPoly_eval w 0 0
  change eval (extendWeight w) C2.adj00 = (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).adjugate 0 0 at ha00
  have ht00 := c2Tensor00_eval w
  change eval (extendWeight w) c2Tensor00 = c2RealTensor w 0 0 at ht00
  have ha01 := C2.adjPoly_eval w 0 1
  change eval (extendWeight w) C2.adj01 = (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).adjugate 0 1 at ha01
  have ht01 := c2Tensor01_eval w
  change eval (extendWeight w) c2Tensor01 = c2RealTensor w 0 1 at ht01
  have ha02 := C2.adjPoly_eval w 0 2
  change eval (extendWeight w) C2.adj02 = (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).adjugate 0 2 at ha02
  have ht02 := c2Tensor02_eval w
  change eval (extendWeight w) c2Tensor02 = c2RealTensor w 0 2 at ht02
  have ha03 := C2.adjPoly_eval w 0 3
  change eval (extendWeight w) C2.adj03 = (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).adjugate 0 3 at ha03
  have ht03 := c2Tensor03_eval w
  change eval (extendWeight w) c2Tensor03 = c2RealTensor w 0 3 at ht03
  have ha11 := C2.adjPoly_eval w 1 1
  change eval (extendWeight w) C2.adj11 = (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).adjugate 1 1 at ha11
  have ht11 := c2Tensor11_eval w
  change eval (extendWeight w) c2Tensor11 = c2RealTensor w 1 1 at ht11
  have ha12 := C2.adjPoly_eval w 1 2
  change eval (extendWeight w) C2.adj12 = (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).adjugate 1 2 at ha12
  have ht12 := c2Tensor12_eval w
  change eval (extendWeight w) c2Tensor12 = c2RealTensor w 1 2 at ht12
  have ha13 := C2.adjPoly_eval w 1 3
  change eval (extendWeight w) C2.adj13 = (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).adjugate 1 3 at ha13
  have ht13 := c2Tensor13_eval w
  change eval (extendWeight w) c2Tensor13 = c2RealTensor w 1 3 at ht13
  have ha22 := C2.adjPoly_eval w 2 2
  change eval (extendWeight w) C2.adj22 = (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).adjugate 2 2 at ha22
  have ht22 := c2Tensor22_eval w
  change eval (extendWeight w) c2Tensor22 = c2RealTensor w 2 2 at ht22
  have ha23 := C2.adjPoly_eval w 2 3
  change eval (extendWeight w) C2.adj23 = (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).adjugate 2 3 at ha23
  have ht23 := c2Tensor23_eval w
  change eval (extendWeight w) c2Tensor23 = c2RealTensor w 2 3 at ht23
  have ha33 := C2.adjPoly_eval w 3 3
  change eval (extendWeight w) C2.adj33 = (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).adjugate 3 3 at ha33
  have ht33 := c2Tensor33_eval w
  change eval (extendWeight w) c2Tensor33 = c2RealTensor w 3 3 at ht33
  rw [ha00, ht00, ha01, ht01, ha02, ht02, ha03, ht03, ha11, ht11, ha12, ht12, ha13, ht13, ha22, ht22, ha23, ht23, ha33, ht33]
  unfold upperContraction
  ring

theorem c2_simplex_moment_polynomial (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) :
    simplexMomentNumerator (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) (c2CellVertices w) =
      768 * (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).det * eval (extendWeight w) momentC2 := by
  rw [c2_simplex_moment_upper w hw,← c2_contraction_eval_upper,c2_contraction_check,
    eval_scale,c2MomentProduct_eval,determinantC2_extendWeight_eval]
  simp only [extendWeight_fin,Int.cast_ofNat]
  ring

theorem c2_moment_identity_positive (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) :
    60 * (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).det * moment (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) = eval (extendWeight w) momentC2 := by
  have h := c2_simplex_moment_actual w hw
  rw [c2_simplex_moment_polynomial w hw] at h
  have hD := (secondary_posDef_of_pos cone2Vectors (hw 0) (fun j => (hw j.succ).le)).det_pos
  apply mul_left_cancel₀ (show 768 * (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).det ≠ 0 by exact mul_ne_zero (by norm_num) hD.ne')
  calc
    _ = 46080 * (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).det^2 * moment (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) := by ring
    _ = _ := h.symm

theorem c2_moment_identity (w : Fin 10 → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hQ : (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).PosDef) :
    60 * (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).det * moment (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) = eval (extendWeight w) momentC2 := by
  have h : 12 * (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).det * moment (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) = eval (extendWeight w) momentC2 / 5 := by
    apply secondary_moment_boundary_extension cone2Vectors
      (fun w => eval (extendWeight w) momentC2 / 5)
    · apply Continuous.div_const
      apply eval_continuous
      intro n
      unfold extendWeight
      split_ifs with hn
      · exact continuous_apply (⟨n,hn⟩ : Fin 10)
      · exact continuous_const
    · intro v hv
      have hp := c2_moment_identity_positive v hv
      linarith
    · exact hw
    · exact hQ
  linarith

end D4.Secondary
