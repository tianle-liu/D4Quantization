import D4.C23BoundaryHexagonData
import D4.C23VertexSupport

/-! The C₂/C₃ common square has a genuine rectangular dual face. -/
noncomputable section
namespace D4.C23Local
open Matrix Set Analytic Principal AreaEnvelope Secondary

def boundary3Weights (z : Parameters) : Fin 10 → ℝ :=
  ![z 1,z 2,z 3,z 4,0,z 5,z 6,z 7,z 8,0]

def boundary3Form (z : Parameters) : Gram :=
  z 0 • gramMatrix ℝ+principalForm (boundary3Weights z)

def boundary3Parameters (z : Parameters) : Parameters :=
  ![z 0,z 1,z 2,z 3,z 4,z 5,z 6,z 7,z 8,0]

def rectangle3 (u v : ℝ) : Set Plane := Icc ![0,0] ![2*u,2*v]

def boundary3Point (z : Parameters) (L : Plane) : Vec :=
  ![L 0-boundary3Form z 0 0,L 1-boundary3Form z 1 1,
    boundary3Form z 2 2,boundary3Form z 3 3]

def boundary3Coefficients (z : Parameters) (L : Plane) : Fin 10 → ℝ :=
  ![L 0-z 1,L 1-z 2,z 3,z 4,0,-z 5,-z 6,-z 7,-z 8,0]

theorem boundary3_matrix (z : Parameters) : boundary3Form z =
    !![2*z 0+z 1+z 5+z 6,z 0,-z 0-z 5,-z 0-z 6;
       z 0,2*z 0+z 2+z 7+z 8,-z 0-z 7,-z 0-z 8;
       -z 0-z 5,-z 0-z 7,2*z 0+z 3+z 5+z 7,0;
       -z 0-z 6,-z 0-z 8,0,2*z 0+z 4+z 6+z 8] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [boundary3Form,boundary3Weights,principalForm,rankOne,
      cone1Vectors,gramMatrix,Fin.sum_univ_succ] <;> ring

theorem boundary3_form (z : Parameters) : boundary3Form z = form3 (boundary3Parameters z) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [boundary3Form,boundary3Weights,boundary3Parameters,form3,
      principalForm,secondaryForm,rankOne,cone1Vectors,cone3Vectors,gramMatrix,Fin.sum_univ_succ] <;>
    (try simp only [Fin.reduceFinMk,Fin.reduceSucc,Matrix.cons_val,Fin.isValue]) <;> norm_num <;> ring

end D4.C23Local
