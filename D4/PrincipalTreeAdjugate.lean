import D4.PrincipalTreeWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Principal
open Matrix Analytic Certificate
noncomputable section
private def adj00_0 : Poly := [([1,2,3], 1),([1,2,6], 1),([1,2,8], 1),([1,2,9], 1),([1,3,5], 1),([1,3,7], 1),([1,3,9], 1),([1,5,6], 1),([1,5,8], 1),([1,5,9], 1),([1,6,7], 1),([1,6,9], 1),([1,7,8], 1),([1,7,9], 1),([1,8,9], 1),([2,3,4], 1),([2,3,7], 1),([2,3,8], 1),([2,4,6], 1),([2,4,8], 1),([2,4,9], 1),([2,6,7], 1),([2,6,8], 1),([2,7,8], 1),([2,7,9], 1),([2,8,9], 1),([3,4,5], 1),([3,4,7], 1),([3,4,9], 1),([3,5,7], 1),([3,5,8], 1),([3,7,8], 1)]
private def adj00_1 : Poly := [([3,7,9], 1),([3,8,9], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)]
def adj00 : Poly := List.flatten [adj00_0,adj00_1]
private def adj01_0 : Poly := [([2,3,4], 1),([2,4,6], 1),([2,4,8], 1),([2,4,9], 1),([2,6,8], 1),([3,4,5], 1),([3,4,7], 1),([3,4,9], 1),([3,5,7], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)]
def adj01 : Poly := List.flatten [adj01_0]
private def adj02_0 : Poly := [([1,3,5], 1),([1,5,6], 1),([1,5,8], 1),([1,5,9], 1),([1,6,9], 1),([3,4,5], 1),([3,4,7], 1),([3,5,7], 1),([3,5,8], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)]
def adj02 : Poly := List.flatten [adj02_0]
private def adj03_0 : Poly := [([1,2,6], 1),([1,5,6], 1),([1,5,9], 1),([1,6,7], 1),([1,6,9], 1),([2,4,6], 1),([2,4,8], 1),([2,6,7], 1),([2,6,8], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)]
def adj03 : Poly := List.flatten [adj03_0]
private def adj10_0 : Poly := [([2,3,4], 1),([2,4,6], 1),([2,4,8], 1),([2,4,9], 1),([2,6,8], 1),([3,4,5], 1),([3,4,7], 1),([3,4,9], 1),([3,5,7], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)]
def adj10 : Poly := List.flatten [adj10_0]
private def adj11_0 : Poly := [([0,2,3], 1),([0,2,6], 1),([0,2,8], 1),([0,2,9], 1),([0,3,5], 1),([0,3,7], 1),([0,3,9], 1),([0,5,6], 1),([0,5,8], 1),([0,5,9], 1),([0,6,7], 1),([0,6,9], 1),([0,7,8], 1),([0,7,9], 1),([0,8,9], 1),([2,3,4], 1),([2,3,5], 1),([2,3,6], 1),([2,4,6], 1),([2,4,8], 1),([2,4,9], 1),([2,5,6], 1),([2,5,8], 1),([2,5,9], 1),([2,6,8], 1),([2,6,9], 1),([3,4,5], 1),([3,4,7], 1),([3,4,9], 1),([3,5,6], 1),([3,5,7], 1),([3,5,9], 1)]
private def adj11_1 : Poly := [([3,6,7], 1),([3,6,9], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)]
def adj11 : Poly := List.flatten [adj11_0,adj11_1]
private def adj12_0 : Poly := [([0,3,7], 1),([0,6,7], 1),([0,7,8], 1),([0,7,9], 1),([0,8,9], 1),([3,4,5], 1),([3,4,7], 1),([3,5,7], 1),([3,6,7], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)]
def adj12 : Poly := List.flatten [adj12_0]
private def adj13_0 : Poly := [([0,2,8], 1),([0,5,8], 1),([0,7,8], 1),([0,7,9], 1),([0,8,9], 1),([2,4,6], 1),([2,4,8], 1),([2,5,8], 1),([2,6,8], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)]
def adj13 : Poly := List.flatten [adj13_0]
private def adj20_0 : Poly := [([1,3,5], 1),([1,5,6], 1),([1,5,8], 1),([1,5,9], 1),([1,6,9], 1),([3,4,5], 1),([3,4,7], 1),([3,5,7], 1),([3,5,8], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)]
def adj20 : Poly := List.flatten [adj20_0]
private def adj21_0 : Poly := [([0,3,7], 1),([0,6,7], 1),([0,7,8], 1),([0,7,9], 1),([0,8,9], 1),([3,4,5], 1),([3,4,7], 1),([3,5,7], 1),([3,6,7], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)]
def adj21 : Poly := List.flatten [adj21_0]
private def adj22_0 : Poly := [([0,1,3], 1),([0,1,6], 1),([0,1,8], 1),([0,1,9], 1),([0,3,4], 1),([0,3,7], 1),([0,3,8], 1),([0,4,6], 1),([0,4,8], 1),([0,4,9], 1),([0,6,7], 1),([0,6,8], 1),([0,7,8], 1),([0,7,9], 1),([0,8,9], 1),([1,3,4], 1),([1,3,5], 1),([1,3,6], 1),([1,4,6], 1),([1,4,8], 1),([1,4,9], 1),([1,5,6], 1),([1,5,8], 1),([1,5,9], 1),([1,6,8], 1),([1,6,9], 1),([3,4,5], 1),([3,4,6], 1),([3,4,7], 1),([3,4,8], 1),([3,5,7], 1),([3,5,8], 1)]
private def adj22_1 : Poly := [([3,6,7], 1),([3,6,8], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)]
def adj22 : Poly := List.flatten [adj22_0,adj22_1]
private def adj23_0 : Poly := [([0,1,9], 1),([0,4,9], 1),([0,7,8], 1),([0,7,9], 1),([0,8,9], 1),([1,4,9], 1),([1,5,6], 1),([1,5,9], 1),([1,6,9], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)]
def adj23 : Poly := List.flatten [adj23_0]
private def adj30_0 : Poly := [([1,2,6], 1),([1,5,6], 1),([1,5,9], 1),([1,6,7], 1),([1,6,9], 1),([2,4,6], 1),([2,4,8], 1),([2,6,7], 1),([2,6,8], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)]
def adj30 : Poly := List.flatten [adj30_0]
private def adj31_0 : Poly := [([0,2,8], 1),([0,5,8], 1),([0,7,8], 1),([0,7,9], 1),([0,8,9], 1),([2,4,6], 1),([2,4,8], 1),([2,5,8], 1),([2,6,8], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)]
def adj31 : Poly := List.flatten [adj31_0]
private def adj32_0 : Poly := [([0,1,9], 1),([0,4,9], 1),([0,7,8], 1),([0,7,9], 1),([0,8,9], 1),([1,4,9], 1),([1,5,6], 1),([1,5,9], 1),([1,6,9], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)]
def adj32 : Poly := List.flatten [adj32_0]
private def adj33_0 : Poly := [([0,1,2], 1),([0,1,5], 1),([0,1,7], 1),([0,1,9], 1),([0,2,4], 1),([0,2,7], 1),([0,2,8], 1),([0,4,5], 1),([0,4,7], 1),([0,4,9], 1),([0,5,7], 1),([0,5,8], 1),([0,7,8], 1),([0,7,9], 1),([0,8,9], 1),([1,2,4], 1),([1,2,5], 1),([1,2,6], 1),([1,4,5], 1),([1,4,7], 1),([1,4,9], 1),([1,5,6], 1),([1,5,7], 1),([1,5,9], 1),([1,6,7], 1),([1,6,9], 1),([2,4,5], 1),([2,4,6], 1),([2,4,7], 1),([2,4,8], 1),([2,5,7], 1),([2,5,8], 1)]
private def adj33_1 : Poly := [([2,6,7], 1),([2,6,8], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)]
def adj33 : Poly := List.flatten [adj33_0,adj33_1]
def adjPoly : Fin 4 → Fin 4 → Poly := ![![adj00,adj01,adj02,adj03],![adj10,adj11,adj12,adj13],![adj20,adj21,adj22,adj23],![adj30,adj31,adj32,adj33]]
theorem principal_entries (w : Fin 10 → ℝ) :
    principalForm w = !![w 0+w 4+w 5+w 6, -w 4, -w 5, -w 6;
      -w 4, w 1+w 4+w 7+w 8, -w 7, -w 8;
      -w 5, -w 7, w 2+w 5+w 7+w 9, -w 9;
      -w 6, -w 8, -w 9, w 3+w 6+w 8+w 9] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [principalForm, rankOne, cone1Vectors, Fin.sum_univ_succ] <;>
      dsimp [Fin.succ, Fin.instOfNat, Fin.ofNat'] <;> ring

theorem adj00_eval (x : Nat → ℝ) : eval x adj00 =
      (principalForm (fun e => x e.val)).adjugate 0 0 := by
  change eval x [([1,2,3], 1),([1,2,6], 1),([1,2,8], 1),([1,2,9], 1),([1,3,5], 1),([1,3,7], 1),([1,3,9], 1),([1,5,6], 1),([1,5,8], 1),([1,5,9], 1),([1,6,7], 1),([1,6,9], 1),([1,7,8], 1),([1,7,9], 1),([1,8,9], 1),([2,3,4], 1),([2,3,7], 1),([2,3,8], 1),([2,4,6], 1),([2,4,8], 1),([2,4,9], 1),([2,6,7], 1),([2,6,8], 1),([2,7,8], 1),([2,7,9], 1),([2,8,9], 1),([3,4,5], 1),([3,4,7], 1),([3,4,9], 1),([3,5,7], 1),([3,5,8], 1),([3,7,8], 1),([3,7,9], 1),([3,8,9], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)] = _
  simp only [eval_cons, eval_nil, monomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [principal_entries, Matrix.adjugate_fin_succ_eq_det_submatrix]
  change _ = (-1 : ℝ)^0 * Matrix.det !![x 1+x 4+x 7+x 8,-x 7,-x 8;-x 7,x 2+x 5+x 7+x 9,-x 9;-x 8,-x 9,x 3+x 6+x 8+x 9]
  rw [Matrix.det_fin_three]
  norm_num
  dsimp [Fin.instOfNat, Fin.ofNat', Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  norm_num
  ring
theorem adj01_eval (x : Nat → ℝ) : eval x adj01 =
      (principalForm (fun e => x e.val)).adjugate 0 1 := by
  change eval x [([2,3,4], 1),([2,4,6], 1),([2,4,8], 1),([2,4,9], 1),([2,6,8], 1),([3,4,5], 1),([3,4,7], 1),([3,4,9], 1),([3,5,7], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)] = _
  simp only [eval_cons, eval_nil, monomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [principal_entries, Matrix.adjugate_fin_succ_eq_det_submatrix]
  change _ = (-1 : ℝ)^1 * Matrix.det !![-x 4,-x 5,-x 6;-x 7,x 2+x 5+x 7+x 9,-x 9;-x 8,-x 9,x 3+x 6+x 8+x 9]
  rw [Matrix.det_fin_three]
  norm_num
  dsimp [Fin.instOfNat, Fin.ofNat', Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  norm_num
  ring
theorem adj02_eval (x : Nat → ℝ) : eval x adj02 =
      (principalForm (fun e => x e.val)).adjugate 0 2 := by
  change eval x [([1,3,5], 1),([1,5,6], 1),([1,5,8], 1),([1,5,9], 1),([1,6,9], 1),([3,4,5], 1),([3,4,7], 1),([3,5,7], 1),([3,5,8], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)] = _
  simp only [eval_cons, eval_nil, monomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [principal_entries, Matrix.adjugate_fin_succ_eq_det_submatrix]
  change _ = (-1 : ℝ)^2 * Matrix.det !![-x 4,-x 5,-x 6;x 1+x 4+x 7+x 8,-x 7,-x 8;-x 8,-x 9,x 3+x 6+x 8+x 9]
  rw [Matrix.det_fin_three]
  norm_num
  dsimp [Fin.instOfNat, Fin.ofNat', Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  norm_num
  ring
theorem adj03_eval (x : Nat → ℝ) : eval x adj03 =
      (principalForm (fun e => x e.val)).adjugate 0 3 := by
  change eval x [([1,2,6], 1),([1,5,6], 1),([1,5,9], 1),([1,6,7], 1),([1,6,9], 1),([2,4,6], 1),([2,4,8], 1),([2,6,7], 1),([2,6,8], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)] = _
  simp only [eval_cons, eval_nil, monomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [principal_entries, Matrix.adjugate_fin_succ_eq_det_submatrix]
  change _ = (-1 : ℝ)^3 * Matrix.det !![-x 4,-x 5,-x 6;x 1+x 4+x 7+x 8,-x 7,-x 8;-x 7,x 2+x 5+x 7+x 9,-x 9]
  rw [Matrix.det_fin_three]
  norm_num
  dsimp [Fin.instOfNat, Fin.ofNat', Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  norm_num
  ring
theorem adj10_eval (x : Nat → ℝ) : eval x adj10 =
      (principalForm (fun e => x e.val)).adjugate 1 0 := by
  change eval x [([2,3,4], 1),([2,4,6], 1),([2,4,8], 1),([2,4,9], 1),([2,6,8], 1),([3,4,5], 1),([3,4,7], 1),([3,4,9], 1),([3,5,7], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)] = _
  simp only [eval_cons, eval_nil, monomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [principal_entries, Matrix.adjugate_fin_succ_eq_det_submatrix]
  change _ = (-1 : ℝ)^1 * Matrix.det !![-x 4,-x 7,-x 8;-x 5,x 2+x 5+x 7+x 9,-x 9;-x 6,-x 9,x 3+x 6+x 8+x 9]
  rw [Matrix.det_fin_three]
  norm_num
  dsimp [Fin.instOfNat, Fin.ofNat', Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  norm_num
  ring
theorem adj11_eval (x : Nat → ℝ) : eval x adj11 =
      (principalForm (fun e => x e.val)).adjugate 1 1 := by
  change eval x [([0,2,3], 1),([0,2,6], 1),([0,2,8], 1),([0,2,9], 1),([0,3,5], 1),([0,3,7], 1),([0,3,9], 1),([0,5,6], 1),([0,5,8], 1),([0,5,9], 1),([0,6,7], 1),([0,6,9], 1),([0,7,8], 1),([0,7,9], 1),([0,8,9], 1),([2,3,4], 1),([2,3,5], 1),([2,3,6], 1),([2,4,6], 1),([2,4,8], 1),([2,4,9], 1),([2,5,6], 1),([2,5,8], 1),([2,5,9], 1),([2,6,8], 1),([2,6,9], 1),([3,4,5], 1),([3,4,7], 1),([3,4,9], 1),([3,5,6], 1),([3,5,7], 1),([3,5,9], 1),([3,6,7], 1),([3,6,9], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)] = _
  simp only [eval_cons, eval_nil, monomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [principal_entries, Matrix.adjugate_fin_succ_eq_det_submatrix]
  change _ = (-1 : ℝ)^2 * Matrix.det !![x 0+x 4+x 5+x 6,-x 5,-x 6;-x 5,x 2+x 5+x 7+x 9,-x 9;-x 6,-x 9,x 3+x 6+x 8+x 9]
  rw [Matrix.det_fin_three]
  norm_num
  dsimp [Fin.instOfNat, Fin.ofNat', Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  norm_num
  ring
theorem adj12_eval (x : Nat → ℝ) : eval x adj12 =
      (principalForm (fun e => x e.val)).adjugate 1 2 := by
  change eval x [([0,3,7], 1),([0,6,7], 1),([0,7,8], 1),([0,7,9], 1),([0,8,9], 1),([3,4,5], 1),([3,4,7], 1),([3,5,7], 1),([3,6,7], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)] = _
  simp only [eval_cons, eval_nil, monomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [principal_entries, Matrix.adjugate_fin_succ_eq_det_submatrix]
  change _ = (-1 : ℝ)^3 * Matrix.det !![x 0+x 4+x 5+x 6,-x 5,-x 6;-x 4,-x 7,-x 8;-x 6,-x 9,x 3+x 6+x 8+x 9]
  rw [Matrix.det_fin_three]
  norm_num
  dsimp [Fin.instOfNat, Fin.ofNat', Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  norm_num
  ring
theorem adj13_eval (x : Nat → ℝ) : eval x adj13 =
      (principalForm (fun e => x e.val)).adjugate 1 3 := by
  change eval x [([0,2,8], 1),([0,5,8], 1),([0,7,8], 1),([0,7,9], 1),([0,8,9], 1),([2,4,6], 1),([2,4,8], 1),([2,5,8], 1),([2,6,8], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)] = _
  simp only [eval_cons, eval_nil, monomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [principal_entries, Matrix.adjugate_fin_succ_eq_det_submatrix]
  change _ = (-1 : ℝ)^4 * Matrix.det !![x 0+x 4+x 5+x 6,-x 5,-x 6;-x 4,-x 7,-x 8;-x 5,x 2+x 5+x 7+x 9,-x 9]
  rw [Matrix.det_fin_three]
  norm_num
  dsimp [Fin.instOfNat, Fin.ofNat', Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  norm_num
  ring
theorem adj20_eval (x : Nat → ℝ) : eval x adj20 =
      (principalForm (fun e => x e.val)).adjugate 2 0 := by
  change eval x [([1,3,5], 1),([1,5,6], 1),([1,5,8], 1),([1,5,9], 1),([1,6,9], 1),([3,4,5], 1),([3,4,7], 1),([3,5,7], 1),([3,5,8], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)] = _
  simp only [eval_cons, eval_nil, monomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [principal_entries, Matrix.adjugate_fin_succ_eq_det_submatrix]
  change _ = (-1 : ℝ)^2 * Matrix.det !![-x 4,x 1+x 4+x 7+x 8,-x 8;-x 5,-x 7,-x 9;-x 6,-x 8,x 3+x 6+x 8+x 9]
  rw [Matrix.det_fin_three]
  norm_num
  dsimp [Fin.instOfNat, Fin.ofNat', Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  norm_num
  ring
theorem adj21_eval (x : Nat → ℝ) : eval x adj21 =
      (principalForm (fun e => x e.val)).adjugate 2 1 := by
  change eval x [([0,3,7], 1),([0,6,7], 1),([0,7,8], 1),([0,7,9], 1),([0,8,9], 1),([3,4,5], 1),([3,4,7], 1),([3,5,7], 1),([3,6,7], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)] = _
  simp only [eval_cons, eval_nil, monomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [principal_entries, Matrix.adjugate_fin_succ_eq_det_submatrix]
  change _ = (-1 : ℝ)^3 * Matrix.det !![x 0+x 4+x 5+x 6,-x 4,-x 6;-x 5,-x 7,-x 9;-x 6,-x 8,x 3+x 6+x 8+x 9]
  rw [Matrix.det_fin_three]
  norm_num
  dsimp [Fin.instOfNat, Fin.ofNat', Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  norm_num
  ring
theorem adj22_eval (x : Nat → ℝ) : eval x adj22 =
      (principalForm (fun e => x e.val)).adjugate 2 2 := by
  change eval x [([0,1,3], 1),([0,1,6], 1),([0,1,8], 1),([0,1,9], 1),([0,3,4], 1),([0,3,7], 1),([0,3,8], 1),([0,4,6], 1),([0,4,8], 1),([0,4,9], 1),([0,6,7], 1),([0,6,8], 1),([0,7,8], 1),([0,7,9], 1),([0,8,9], 1),([1,3,4], 1),([1,3,5], 1),([1,3,6], 1),([1,4,6], 1),([1,4,8], 1),([1,4,9], 1),([1,5,6], 1),([1,5,8], 1),([1,5,9], 1),([1,6,8], 1),([1,6,9], 1),([3,4,5], 1),([3,4,6], 1),([3,4,7], 1),([3,4,8], 1),([3,5,7], 1),([3,5,8], 1),([3,6,7], 1),([3,6,8], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)] = _
  simp only [eval_cons, eval_nil, monomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [principal_entries, Matrix.adjugate_fin_succ_eq_det_submatrix]
  change _ = (-1 : ℝ)^4 * Matrix.det !![x 0+x 4+x 5+x 6,-x 4,-x 6;-x 4,x 1+x 4+x 7+x 8,-x 8;-x 6,-x 8,x 3+x 6+x 8+x 9]
  rw [Matrix.det_fin_three]
  norm_num
  dsimp [Fin.instOfNat, Fin.ofNat', Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  norm_num
  ring
theorem adj23_eval (x : Nat → ℝ) : eval x adj23 =
      (principalForm (fun e => x e.val)).adjugate 2 3 := by
  change eval x [([0,1,9], 1),([0,4,9], 1),([0,7,8], 1),([0,7,9], 1),([0,8,9], 1),([1,4,9], 1),([1,5,6], 1),([1,5,9], 1),([1,6,9], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)] = _
  simp only [eval_cons, eval_nil, monomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [principal_entries, Matrix.adjugate_fin_succ_eq_det_submatrix]
  change _ = (-1 : ℝ)^5 * Matrix.det !![x 0+x 4+x 5+x 6,-x 4,-x 6;-x 4,x 1+x 4+x 7+x 8,-x 8;-x 5,-x 7,-x 9]
  rw [Matrix.det_fin_three]
  norm_num
  dsimp [Fin.instOfNat, Fin.ofNat', Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  norm_num
  ring
theorem adj30_eval (x : Nat → ℝ) : eval x adj30 =
      (principalForm (fun e => x e.val)).adjugate 3 0 := by
  change eval x [([1,2,6], 1),([1,5,6], 1),([1,5,9], 1),([1,6,7], 1),([1,6,9], 1),([2,4,6], 1),([2,4,8], 1),([2,6,7], 1),([2,6,8], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)] = _
  simp only [eval_cons, eval_nil, monomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [principal_entries, Matrix.adjugate_fin_succ_eq_det_submatrix]
  change _ = (-1 : ℝ)^3 * Matrix.det !![-x 4,x 1+x 4+x 7+x 8,-x 7;-x 5,-x 7,x 2+x 5+x 7+x 9;-x 6,-x 8,-x 9]
  rw [Matrix.det_fin_three]
  norm_num
  dsimp [Fin.instOfNat, Fin.ofNat', Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  norm_num
  ring
theorem adj31_eval (x : Nat → ℝ) : eval x adj31 =
      (principalForm (fun e => x e.val)).adjugate 3 1 := by
  change eval x [([0,2,8], 1),([0,5,8], 1),([0,7,8], 1),([0,7,9], 1),([0,8,9], 1),([2,4,6], 1),([2,4,8], 1),([2,5,8], 1),([2,6,8], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)] = _
  simp only [eval_cons, eval_nil, monomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [principal_entries, Matrix.adjugate_fin_succ_eq_det_submatrix]
  change _ = (-1 : ℝ)^4 * Matrix.det !![x 0+x 4+x 5+x 6,-x 4,-x 5;-x 5,-x 7,x 2+x 5+x 7+x 9;-x 6,-x 8,-x 9]
  rw [Matrix.det_fin_three]
  norm_num
  dsimp [Fin.instOfNat, Fin.ofNat', Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  norm_num
  ring
theorem adj32_eval (x : Nat → ℝ) : eval x adj32 =
      (principalForm (fun e => x e.val)).adjugate 3 2 := by
  change eval x [([0,1,9], 1),([0,4,9], 1),([0,7,8], 1),([0,7,9], 1),([0,8,9], 1),([1,4,9], 1),([1,5,6], 1),([1,5,9], 1),([1,6,9], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)] = _
  simp only [eval_cons, eval_nil, monomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [principal_entries, Matrix.adjugate_fin_succ_eq_det_submatrix]
  change _ = (-1 : ℝ)^5 * Matrix.det !![x 0+x 4+x 5+x 6,-x 4,-x 5;-x 4,x 1+x 4+x 7+x 8,-x 7;-x 6,-x 8,-x 9]
  rw [Matrix.det_fin_three]
  norm_num
  dsimp [Fin.instOfNat, Fin.ofNat', Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  norm_num
  ring
theorem adj33_eval (x : Nat → ℝ) : eval x adj33 =
      (principalForm (fun e => x e.val)).adjugate 3 3 := by
  change eval x [([0,1,2], 1),([0,1,5], 1),([0,1,7], 1),([0,1,9], 1),([0,2,4], 1),([0,2,7], 1),([0,2,8], 1),([0,4,5], 1),([0,4,7], 1),([0,4,9], 1),([0,5,7], 1),([0,5,8], 1),([0,7,8], 1),([0,7,9], 1),([0,8,9], 1),([1,2,4], 1),([1,2,5], 1),([1,2,6], 1),([1,4,5], 1),([1,4,7], 1),([1,4,9], 1),([1,5,6], 1),([1,5,7], 1),([1,5,9], 1),([1,6,7], 1),([1,6,9], 1),([2,4,5], 1),([2,4,6], 1),([2,4,7], 1),([2,4,8], 1),([2,5,7], 1),([2,5,8], 1),([2,6,7], 1),([2,6,8], 1),([4,5,6], 1),([4,5,8], 1),([4,5,9], 1),([4,6,7], 1),([4,6,9], 1),([4,7,8], 1),([4,7,9], 1),([4,8,9], 1),([5,6,7], 1),([5,6,8], 1),([5,7,8], 1),([5,7,9], 1),([5,8,9], 1),([6,7,8], 1),([6,7,9], 1),([6,8,9], 1)] = _
  simp only [eval_cons, eval_nil, monomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [principal_entries, Matrix.adjugate_fin_succ_eq_det_submatrix]
  change _ = (-1 : ℝ)^6 * Matrix.det !![x 0+x 4+x 5+x 6,-x 4,-x 5;-x 4,x 1+x 4+x 7+x 8,-x 7;-x 5,-x 7,x 2+x 5+x 7+x 9]
  rw [Matrix.det_fin_three]
  norm_num
  dsimp [Fin.instOfNat, Fin.ofNat', Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  norm_num
  ring
theorem adjPoly_eval (x : Nat → ℝ) (i j : Fin 4) :
    eval x (adjPoly i j) = (principalForm (fun e => x e.val)).adjugate i j := by
  fin_cases i <;> fin_cases j
  · exact adj00_eval x
  · exact adj01_eval x
  · exact adj02_eval x
  · exact adj03_eval x
  · exact adj10_eval x
  · exact adj11_eval x
  · exact adj12_eval x
  · exact adj13_eval x
  · exact adj20_eval x
  · exact adj21_eval x
  · exact adj22_eval x
  · exact adj23_eval x
  · exact adj30_eval x
  · exact adj31_eval x
  · exact adj32_eval x
  · exact adj33_eval x
end
end D4.Principal
