import D4.C23TightGenerators
import D4.C23SublevelGeometry
import D4.PrincipalDualRegion

/-! The C₁/C₂ common square has an actual hexagonal dual face. Support is
proved for all integer competitors by an explicit zonotope representation. -/
noncomputable section
namespace D4.C23Local
open Matrix Set Analytic Principal AreaEnvelope

def boundary2Weights (z : Parameters) : Fin 10 → ℝ :=
  ![z 1,z 2,z 3,z 4,0,z 5,z 6,z 7,z 8,z 9]

def boundary2Form (z : Parameters) : Gram := principalForm (boundary2Weights z)

def boundary2Parameters (z : Parameters) : Parameters :=
  ![0,z 1,z 2,z 3,z 4,z 5,z 6,z 7,z 8,z 9]

def hexagon2 (p q r : ℝ) : Set Plane :=
  {L | 0 ≤ L 0 ∧ L 0 ≤ 2*(p+r) ∧ 0 ≤ L 1 ∧ L 1 ≤ 2*(q+r) ∧
    2*r ≤ L 0+L 1 ∧ L 0+L 1 ≤ 2*(p+q+r)}

def boundary2Point (z : Parameters) (L : Plane) : Vec :=
  ![boundary2Form z 0 0,boundary2Form z 1 1,
    L 0-boundary2Form z 2 2,L 1-boundary2Form z 3 3]

def dualSquareFace (Q : Gram) (i j : Fin 4) : Set Vec :=
  {r | r ∈ dualRegion Q ∧ r i=Q i i ∧ r j=Q j j}

theorem boundary2_matrix (z : Parameters) : boundary2Form z =
    !![z 1+z 5+z 6,0,-z 5,-z 6;
       0,z 2+z 7+z 8,-z 7,-z 8;
       -z 5,-z 7,z 3+z 5+z 7+z 9,-z 9;
       -z 6,-z 8,-z 9,z 4+z 6+z 8+z 9] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [boundary2Form,boundary2Weights,principalForm,rankOne,
      cone1Vectors,Fin.sum_univ_succ] <;> ring

theorem generatorMap_coordinates (t : Fin 10 → ℝ) :
    generatorMap t =
      ![t 0+t 4+t 5+t 6,t 1-t 4+t 7+t 8,
        t 2-t 5-t 7+t 9,t 3-t 6-t 8-t 9] := by
  rw [generatorMap_eq]
  ext i; fin_cases i <;>
    norm_num [cone1Vectors,Fin.sum_univ_succ] <;>
    simp only [Fin.reduceFinMk,Fin.reduceSucc,Matrix.cons_val,Fin.isValue] <;>
    norm_num <;> ring

theorem boundary2_form (z : Parameters) : boundary2Form z = form2 (boundary2Parameters z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundary2Form,boundary2Weights,boundary2Parameters,form2,
      principalForm,secondaryForm,rankOne,cone1Vectors,cone2Vectors,gramMatrix,Fin.sum_univ_succ] <;>
    simp only [Fin.reduceFinMk,Fin.reduceSucc,Matrix.cons_val,Fin.isValue] <;> norm_num <;> ring

theorem hexagon2_gap (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (L : Plane) :
    L ∈ hexagon2 p q r ↔ gap2 p q r L=0 := by
  have hn := gap2_nonneg p q r L
  have he : gap2 p q r L=0 ↔ gap2 p q r L ≤ 0 := ⟨fun h => h.le,fun h => le_antisymm h hn⟩
  rw [he,gap2_le_iff p q r 0 hp hq hr (le_refl 0)]
  simp only [hexagon2,mem_setOf_eq,neg_zero,add_zero,sub_zero]
  constructor
  · rintro ⟨h1,h2,h3,h4,h5,h6⟩
    (repeat' constructor) <;> linarith
  · rintro ⟨h1,h2,h3,h4,h5,h6,_⟩
    exact ⟨h1,h2,h3,h4,h5,h6⟩


end D4.C23Local
