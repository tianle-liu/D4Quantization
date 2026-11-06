import D4.Targets
import D4.Definitions

/-! The local costs and affine coordinates in the two correction calculations.
Every cost is the actual value `Q[n] - n · r` at an integer lattice site. -/
set_option maxHeartbeats 2000000
noncomputable section
namespace D4.C23Local
open Matrix Analytic

abbrev Parameters := Fin 10 → ℝ

def form2 (z : Parameters) : Gram :=
  secondaryForm cone2Vectors (z 0) (fun i => z ⟨i.val+1, by omega⟩)

def form3 (z : Parameters) : Gram :=
  secondaryForm cone3Vectors (z 0) (fun i => z ⟨i.val+1, by omega⟩)

def siteCost (Q : Gram) (r : Vec) (n : IntVec) : ℝ :=
  quadratic Q (castVec n) - dotProduct (castVec n) r

def sites2 : Fin 10 → IntVec :=
  ![![0,0,0,0], ![1,0,0,0], ![0,1,0,0], ![1,1,0,0],
    ![0,0,-1,0], ![0,0,0,-1], ![0,0,-1,-1],
    ![1,1,1,0], ![1,1,0,1], ![1,1,1,1]]

def sites3 : Fin 8 → IntVec :=
  ![![0,0,0,0], ![0,0,1,0], ![0,0,0,1], ![0,0,1,1],
    ![-1,0,0,0], ![0,-1,0,0], ![1,0,1,1], ![0,1,1,1]]

def coordinates2 (Q : Gram) (r : Vec) : Vec :=
  ![Q 0 0-r 0, Q 1 1-r 1, Q 2 2+r 2, Q 3 3+r 3]

def coordinates3 (Q : Gram) (r : Vec) : Vec :=
  ![Q 2 2-r 2, Q 3 3-r 3, Q 0 0+r 0, Q 1 1+r 1]

def costValues2 (z : Parameters) (r : Vec) : Fin 10 → ℝ :=
  let c := coordinates2 (form2 z) r
  let L₃ := c 2+c 3-2*z 9
  ![0, c 0, c 1, c 0+c 1+2*z 0,
    c 2, c 3, L₃,
    c 0+c 1+2*z 0+2*(z 3+z 9)-c 2,
    c 0+c 1+2*z 0+2*(z 4+z 9)-c 3,
    c 0+c 1+2*z 0+2*(z 3+z 4)-L₃]

def costValues3 (Q : Gram) (r : Vec) : Fin 8 → ℝ :=
  let c := coordinates3 Q r
  let t := 2*Q 2 3
  let u := Q 0 0+Q 0 2+Q 0 3+t/2
  let v := Q 1 1+Q 1 2+Q 1 3+t/2
  ![0, c 0, c 1, c 0+c 1+t, c 2, c 3,
    2*u-c 2+c 0+c 1, 2*v-c 3+c 0+c 1]

theorem siteCosts2 (z : Parameters) (r : Vec) (i : Fin 10) :
    siteCost (form2 z) r (sites2 i) = costValues2 z r i := by
  fin_cases i <;>
    norm_num [siteCost, sites2, costValues2, coordinates2, quadratic,
      castVec, form2, secondaryForm, rankOne, cone2Vectors, gramMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.reduceFinMk, Matrix.cons_val] <;> (try simp only [Fin.reduceFinMk, Fin.reduceSucc, Matrix.cons_val, Fin.isValue]) <;> norm_num <;> ring

theorem siteCosts3 (z : Parameters) (r : Vec) (i : Fin 8) :
    siteCost (form3 z) r (sites3 i) = costValues3 (form3 z) r i := by
  fin_cases i <;>
    norm_num [siteCost, sites3, costValues3, coordinates3, quadratic,
      castVec, form3, secondaryForm, rankOne, cone3Vectors, gramMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.reduceFinMk, Matrix.cons_val] <;> (try simp only [Fin.reduceFinMk, Fin.reduceSucc, Matrix.cons_val, Fin.isValue]) <;> norm_num <;> ring

/-- Linear parts of the actual four-dimensional affine coordinate maps. -/
def coordinateMatrix2 : Gram := !![-1,0,0,0; 0,-1,0,0; 0,0,1,0; 0,0,0,1]
def coordinateMatrix3 : Gram := !![0,0,-1,0; 0,0,0,-1; 1,0,0,0; 0,1,0,0]

theorem coordinates2_affine (Q : Gram) (r : Vec) :
    coordinates2 Q r = ![Q 0 0,Q 1 1,Q 2 2,Q 3 3]+coordinateMatrix2*ᵥr := by
  ext i; fin_cases i <;> simp [coordinates2, coordinateMatrix2, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, Fin.reduceFinMk, Matrix.cons_val] <;> (try simp only [Fin.reduceFinMk, Fin.reduceSucc, Matrix.cons_val, Fin.isValue]) <;> norm_num <;> ring

theorem coordinates3_affine (Q : Gram) (r : Vec) :
    coordinates3 Q r = ![Q 2 2,Q 3 3,Q 0 0,Q 1 1]+coordinateMatrix3*ᵥr := by
  ext i; fin_cases i <;> simp [coordinates3, coordinateMatrix3, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, Fin.reduceFinMk, Matrix.cons_val] <;> (try simp only [Fin.reduceFinMk, Fin.reduceSucc, Matrix.cons_val, Fin.isValue]) <;> norm_num <;> ring

theorem coordinateMatrix2_det : coordinateMatrix2.det = 1 := by
  unfold coordinateMatrix2
  rw [Matrix.det_succ_row _ 0]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three]
  all_goals try simp only [Fin.reduceFinMk, Fin.reduceSucc, Matrix.cons_val, Fin.isValue, Fin.succAbove]
  all_goals norm_num

theorem coordinateMatrix3_det : coordinateMatrix3.det = 1 := by
  unfold coordinateMatrix3
  rw [Matrix.det_succ_row _ 0]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three]
  all_goals try simp only [Fin.reduceFinMk, Fin.reduceSucc, Matrix.cons_val, Fin.isValue, Fin.succAbove]
  all_goals change (-1:ℝ)*0*0-(-1)*1*1=1
  all_goals norm_num

/-- The path in the paper, with `z 9` unused: the final coefficient is `b`. -/
def path3 (z : Parameters) (b : ℝ) : Parameters :=
  ![z 0-b,z 1,z 2,z 3-b,z 4+b,z 5+b,z 6,z 7+b,z 8,b]

def theta (z : Parameters) : Parameters :=
  ![z 0+z 9,z 1-z 9,z 2-z 9,z 3,z 4,z 5,z 6,z 7,z 8,-z 9]

theorem form3_eq_form2_theta (z : Parameters) : form3 z = form2 (theta z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [form3, form2, theta, secondaryForm, rankOne, cone2Vectors,
      cone3Vectors, gramMatrix, Fin.sum_univ_succ, Fin.reduceFinMk, Matrix.cons_val] <;> (try simp only [Fin.reduceFinMk, Fin.reduceSucc, Matrix.cons_val, Fin.isValue]) <;> norm_num <;> ring

theorem path3_matrix (z : Parameters) (b : ℝ) :
    form3 (path3 z b) =
      !![2*z 0+z 1+z 5+z 6, z 0, -z 0-z 5-b, -z 0-z 6;
         z 0, 2*z 0+z 2+z 7+z 8, -z 0-z 7-b, -z 0-z 8;
         -z 0-z 5-b, -z 0-z 7-b, 2*z 0+z 3+z 5+z 7, b;
         -z 0-z 6, -z 0-z 8, b, 2*z 0+z 4+z 6+z 8] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [form3, path3, secondaryForm, rankOne, cone3Vectors,
      gramMatrix, Fin.sum_univ_succ, Fin.reduceFinMk, Matrix.cons_val] <;> (try simp only [Fin.reduceFinMk, Fin.reduceSucc, Matrix.cons_val, Fin.isValue]) <;> norm_num <;> ring

theorem path3_fixed_parameters (z : Parameters) (b : ℝ) :
    let Q := form3 (path3 z b)
    2*Q 2 3=2*b ∧ Q 0 0+Q 0 2+Q 0 3+Q 2 3=z 1 ∧
      Q 1 1+Q 1 2+Q 1 3+Q 2 3=z 2 := by
  simp only [path3_matrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.cons_val_fin_one]
  constructor
  · ring
  constructor <;> (try simp only [Fin.reduceFinMk, Fin.reduceSucc, Matrix.cons_val, Fin.isValue]) <;> norm_num <;> ring

theorem path3_positive (z : Parameters) (hz : ∀ i, 0 < z i) (b : ℝ)
    (hb : 0 < b) (hb0 : b < z 0) (hb3 : b < z 3) :
    ∀ i, 0 < path3 z b i := by
  intro i; fin_cases i <;> simp [path3] <;> linarith [hz 0, hz 1, hz 2,
    hz 3, hz 4, hz 5, hz 6, hz 7, hz 8]

theorem theta_path3_positive (z : Parameters) (hz : ∀ i, 0 < z i) (b : ℝ)
    (hb : b < 0) (hb4 : -z 4 < b) (hb5 : -z 5 < b) (hb7 : -z 7 < b) :
    ∀ i, 0 < theta (path3 z b) i := by
  intro i; fin_cases i <;> simp [theta, path3] <;> linarith [hz 0, hz 1, hz 2,
    hz 3, hz 4, hz 5, hz 6, hz 7, hz 8]

end D4.C23Local
