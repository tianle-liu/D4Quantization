import D4.PaperSymmetryCore
import D4.KernelCompute
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.PaperSymmetry.C2
open D4.PaperSymmetry

def g0 : Perm :=
  ⟨![0,5,7,3,9,1,6,2,8,4], ![0,5,7,3,9,1,6,2,8,4], by decide +kernel, by decide +kernel⟩

def g1 : Perm :=
  ⟨![0,2,1,4,3,8,7,6,5,9], ![0,2,1,4,3,8,7,6,5,9], by decide +kernel, by decide +kernel⟩

def p0 : Perm :=
  ⟨![0,1,2,3,4,5,6,7,8,9], ![0,1,2,3,4,5,6,7,8,9], by decide +kernel, by decide +kernel⟩

def p1 : Perm :=
  ⟨![0,1,2,4,3,6,5,8,7,9], ![0,1,2,4,3,6,5,8,7,9], by decide +kernel, by decide +kernel⟩

def p2 : Perm :=
  ⟨![0,2,1,3,4,7,8,5,6,9], ![0,2,1,3,4,7,8,5,6,9], by decide +kernel, by decide +kernel⟩

def p3 : Perm :=
  ⟨![0,2,1,4,3,8,7,6,5,9], ![0,2,1,4,3,8,7,6,5,9], by decide +kernel, by decide +kernel⟩

def p4 : Perm :=
  ⟨![0,5,7,3,9,1,6,2,8,4], ![0,5,7,3,9,1,6,2,8,4], by decide +kernel, by decide +kernel⟩

def p5 : Perm :=
  ⟨![0,5,7,9,3,6,1,8,2,4], ![0,6,8,4,9,1,5,2,7,3], by decide +kernel, by decide +kernel⟩

def p6 : Perm :=
  ⟨![0,6,8,4,9,1,5,2,7,3], ![0,5,7,9,3,6,1,8,2,4], by decide +kernel, by decide +kernel⟩

def p7 : Perm :=
  ⟨![0,6,8,9,4,5,1,7,2,3], ![0,6,8,9,4,5,1,7,2,3], by decide +kernel, by decide +kernel⟩

def p8 : Perm :=
  ⟨![0,7,5,3,9,2,8,1,6,4], ![0,7,5,3,9,2,8,1,6,4], by decide +kernel, by decide +kernel⟩

def p9 : Perm :=
  ⟨![0,7,5,9,3,8,2,6,1,4], ![0,8,6,4,9,2,7,1,5,3], by decide +kernel, by decide +kernel⟩

def p10 : Perm :=
  ⟨![0,8,6,4,9,2,7,1,5,3], ![0,7,5,9,3,8,2,6,1,4], by decide +kernel, by decide +kernel⟩

def p11 : Perm :=
  ⟨![0,8,6,9,4,7,2,5,1,3], ![0,8,6,9,4,7,2,5,1,3], by decide +kernel, by decide +kernel⟩

def elements : List Perm := [p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11]
def generatorWords : List (List Bool) := [[],[false,true,false,true,false],[true,false,true,false,true,false],[true],[false],[true,false,true,false],[false,true,false,true],[true,false,true],[true,false,true,false,true],[false,true],[true,false],[false,true,false]]
theorem words_eq : generatorWords.map (word g0 g1) = elements := by decide +kernel
theorem one_mem : (1 : Perm) ∈ elements := by decide +kernel
theorem mul_mem : ∀ p ∈ elements, ∀ q ∈ elements, p*q ∈ elements := by decide +kernel
theorem inv_mem : ∀ p ∈ elements, p⁻¹ ∈ elements := by decide +kernel
theorem generators_mem : g0 ∈ elements ∧ g1 ∈ elements := by decide +kernel
def subgroup : Subgroup Perm := tableSubgroup elements one_mem mul_mem inv_mem
theorem subgroup_eq_generated : subgroup = Subgroup.closure {g0,g1} := by
  exact tableSubgroup_eq_closure elements one_mem mul_mem inv_mem g0 g1
    generators_mem generatorWords words_eq
theorem order : Nat.card (Subgroup.closure ({g0,g1} : Set Perm)) = 12 := by
  rw [← subgroup_eq_generated]
  rw [show subgroup = tableSubgroup elements one_mem mul_mem inv_mem from rfl, tableSubgroup_card]
  decide +kernel
end D4.PaperSymmetry.C2
