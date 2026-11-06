import D4.PrincipalTreeFiniteSemantics
import D4.PrincipalTreeTensor
import D4.PrincipalTreeContraction
import D4.PolynomialDeterminants
import D4.CertificateContinuity
import D4.PrincipalBoundary

noncomputable section
namespace D4.Principal
open Matrix Analytic Certificate CertificateMoments

theorem treeMomentProduct_eval_upper (w : Fin 10 → ℝ) :
    eval (extendWeight w) treeMomentProduct =
      upperContraction (principalForm w).adjugate (treeTensor w) := by
  rw [← contraction_check, eval_sumFast]
  simp only [contractionPolys, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    eval_scale, Int.cast_ofNat, add_zero]
  rw [contract00_eval, contract11_eval, contract22_eval, contract33_eval]
  rw [← contract01_check, ← contract02_check, ← contract03_check, ← contract12_check, ← contract13_check, ← contract23_check]
  simp only [eval_mul, eval_mulMerge]
  have ha00 := adjPoly_eval (extendWeight w) 0 0
  simp only [extendWeight_fin] at ha00
  change eval (extendWeight w) adj00 = (principalForm w).adjugate 0 0 at ha00
  have ht00 := tensorPoly_eval w 0 0
  change eval (extendWeight w) tensor00 = treeTensor w 0 0 at ht00
  have ha01 := adjPoly_eval (extendWeight w) 0 1
  simp only [extendWeight_fin] at ha01
  change eval (extendWeight w) adj01 = (principalForm w).adjugate 0 1 at ha01
  have ht01 := tensorPoly_eval w 0 1
  change eval (extendWeight w) tensor01 = treeTensor w 0 1 at ht01
  have ha02 := adjPoly_eval (extendWeight w) 0 2
  simp only [extendWeight_fin] at ha02
  change eval (extendWeight w) adj02 = (principalForm w).adjugate 0 2 at ha02
  have ht02 := tensorPoly_eval w 0 2
  change eval (extendWeight w) tensor02 = treeTensor w 0 2 at ht02
  have ha03 := adjPoly_eval (extendWeight w) 0 3
  simp only [extendWeight_fin] at ha03
  change eval (extendWeight w) adj03 = (principalForm w).adjugate 0 3 at ha03
  have ht03 := tensorPoly_eval w 0 3
  change eval (extendWeight w) tensor03 = treeTensor w 0 3 at ht03
  have ha11 := adjPoly_eval (extendWeight w) 1 1
  simp only [extendWeight_fin] at ha11
  change eval (extendWeight w) adj11 = (principalForm w).adjugate 1 1 at ha11
  have ht11 := tensorPoly_eval w 1 1
  change eval (extendWeight w) tensor11 = treeTensor w 1 1 at ht11
  have ha12 := adjPoly_eval (extendWeight w) 1 2
  simp only [extendWeight_fin] at ha12
  change eval (extendWeight w) adj12 = (principalForm w).adjugate 1 2 at ha12
  have ht12 := tensorPoly_eval w 1 2
  change eval (extendWeight w) tensor12 = treeTensor w 1 2 at ht12
  have ha13 := adjPoly_eval (extendWeight w) 1 3
  simp only [extendWeight_fin] at ha13
  change eval (extendWeight w) adj13 = (principalForm w).adjugate 1 3 at ha13
  have ht13 := tensorPoly_eval w 1 3
  change eval (extendWeight w) tensor13 = treeTensor w 1 3 at ht13
  have ha22 := adjPoly_eval (extendWeight w) 2 2
  simp only [extendWeight_fin] at ha22
  change eval (extendWeight w) adj22 = (principalForm w).adjugate 2 2 at ha22
  have ht22 := tensorPoly_eval w 2 2
  change eval (extendWeight w) tensor22 = treeTensor w 2 2 at ht22
  have ha23 := adjPoly_eval (extendWeight w) 2 3
  simp only [extendWeight_fin] at ha23
  change eval (extendWeight w) adj23 = (principalForm w).adjugate 2 3 at ha23
  have ht23 := tensorPoly_eval w 2 3
  change eval (extendWeight w) tensor23 = treeTensor w 2 3 at ht23
  have ha33 := adjPoly_eval (extendWeight w) 3 3
  simp only [extendWeight_fin] at ha33
  change eval (extendWeight w) adj33 = (principalForm w).adjugate 3 3 at ha33
  have ht33 := tensorPoly_eval w 3 3
  change eval (extendWeight w) tensor33 = treeTensor w 3 3 at ht33
  rw [ha00, ht00, ha01, ht01, ha02, ht02, ha03, ht03, ha11, ht11, ha12, ht12, ha13, ht13, ha22, ht22, ha23, ht23, ha33, ht33]
  unfold upperContraction
  ring

theorem treeMomentNumerator_eq_polynomial (w : Fin 10 → ℝ) :
    treeMomentNumerator w = (principalForm w).det * eval (extendWeight w) momentC1 := by
  rw [treeMomentNumerator_eq_upper, ← treeMomentProduct_eval_upper,
    treeMomentProduct_eval, determinantC1_eval]
  simp only [extendWeight_fin]

theorem principal_moment_identity_positive (w : Fin 10 → ℝ) (hw : ∀ e, 0 < w e) :
    12*(principalForm w).det * moment (principalForm w) = eval (extendWeight w) momentC1 := by
  have h := treeMomentNumerator_eq_actual w hw
  rw [treeMomentNumerator_eq_polynomial] at h
  apply mul_left_cancel₀ (principal_posDef_of_pos hw).det_pos.ne'
  calc
    (principalForm w).det * (12*(principalForm w).det * moment (principalForm w)) =
        12*(principalForm w).det^2*moment (principalForm w) := by ring
    _ = _ := h.symm

/-- The exact integral formula on the entire positive-definite closed principal cone. -/
theorem principal_moment_identity (w : Fin 10 → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hQ : (principalForm w).PosDef) :
    12*(principalForm w).det * moment (principalForm w) = eval (extendWeight w) momentC1 := by
  apply principal_moment_boundary_extension (fun w => eval (extendWeight w) momentC1)
  · apply eval_continuous
    intro n
    unfold extendWeight
    split_ifs with hn
    · exact continuous_apply (⟨n,hn⟩ : Fin 10)
    · exact continuous_const
  · exact principal_moment_identity_positive
  · exact hw
  · exact hQ

end D4.Principal
