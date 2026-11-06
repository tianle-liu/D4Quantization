import D4.PaperSymmetryCore
import D4.KernelCompute
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.PaperSymmetry.C3
open D4.PaperSymmetry

def g0 : Perm :=
  ⟨![0,9,2,7,8,6,5,3,4,1], ![0,9,2,7,8,6,5,3,4,1], by decide +kernel, by decide +kernel⟩

def g1 : Perm :=
  ⟨![0,5,4,8,1,9,3,2,6,7], ![0,4,7,6,2,1,8,9,3,5], by decide +kernel, by decide +kernel⟩

def p0 : Perm :=
  ⟨![0,1,2,3,4,5,6,7,8,9], ![0,1,2,3,4,5,6,7,8,9], by decide +kernel, by decide +kernel⟩

def p1 : Perm :=
  ⟨![0,1,2,4,3,6,5,8,7,9], ![0,1,2,4,3,6,5,8,7,9], by decide +kernel, by decide +kernel⟩

def p2 : Perm :=
  ⟨![0,1,9,5,6,3,4,8,7,2], ![0,1,9,5,6,3,4,8,7,2], by decide +kernel, by decide +kernel⟩

def p3 : Perm :=
  ⟨![0,1,9,6,5,4,3,7,8,2], ![0,1,9,6,5,4,3,7,8,2], by decide +kernel, by decide +kernel⟩

def p4 : Perm :=
  ⟨![0,2,1,3,4,7,8,5,6,9], ![0,2,1,3,4,7,8,5,6,9], by decide +kernel, by decide +kernel⟩

def p5 : Perm :=
  ⟨![0,2,1,4,3,8,7,6,5,9], ![0,2,1,4,3,8,7,6,5,9], by decide +kernel, by decide +kernel⟩

def p6 : Perm :=
  ⟨![0,2,9,7,8,3,4,6,5,1], ![0,9,1,5,6,8,7,3,4,2], by decide +kernel, by decide +kernel⟩

def p7 : Perm :=
  ⟨![0,2,9,8,7,4,3,5,6,1], ![0,9,1,6,5,7,8,4,3,2], by decide +kernel, by decide +kernel⟩

def p8 : Perm :=
  ⟨![0,3,6,1,7,5,2,4,9,8], ![0,3,6,1,7,5,2,4,9,8], by decide +kernel, by decide +kernel⟩

def p9 : Perm :=
  ⟨![0,3,6,7,1,2,5,9,4,8], ![0,4,5,1,8,6,2,3,9,7], by decide +kernel, by decide +kernel⟩

def p10 : Perm :=
  ⟨![0,3,8,2,5,7,1,4,9,6], ![0,6,3,1,7,4,9,5,2,8], by decide +kernel, by decide +kernel⟩

def p11 : Perm :=
  ⟨![0,3,8,5,2,1,7,9,4,6], ![0,5,4,1,8,3,9,6,2,7], by decide +kernel, by decide +kernel⟩

def p12 : Perm :=
  ⟨![0,4,5,1,8,6,2,3,9,7], ![0,3,6,7,1,2,5,9,4,8], by decide +kernel, by decide +kernel⟩

def p13 : Perm :=
  ⟨![0,4,5,8,1,2,6,9,3,7], ![0,4,5,8,1,2,6,9,3,7], by decide +kernel, by decide +kernel⟩

def p14 : Perm :=
  ⟨![0,4,7,2,6,8,1,3,9,5], ![0,6,3,7,1,9,4,2,5,8], by decide +kernel, by decide +kernel⟩

def p15 : Perm :=
  ⟨![0,4,7,6,2,1,8,9,3,5], ![0,5,4,8,1,9,3,2,6,7], by decide +kernel, by decide +kernel⟩

def p16 : Perm :=
  ⟨![0,5,4,1,8,3,9,6,2,7], ![0,3,8,5,2,1,7,9,4,6], by decide +kernel, by decide +kernel⟩

def p17 : Perm :=
  ⟨![0,5,4,8,1,9,3,2,6,7], ![0,4,7,6,2,1,8,9,3,5], by decide +kernel, by decide +kernel⟩

def p18 : Perm :=
  ⟨![0,5,7,3,9,1,8,2,6,4], ![0,5,7,3,9,1,8,2,6,4], by decide +kernel, by decide +kernel⟩

def p19 : Perm :=
  ⟨![0,5,7,9,3,8,1,6,2,4], ![0,6,8,4,9,1,7,2,5,3], by decide +kernel, by decide +kernel⟩

def p20 : Perm :=
  ⟨![0,6,3,1,7,4,9,5,2,8], ![0,3,8,2,5,7,1,4,9,6], by decide +kernel, by decide +kernel⟩

def p21 : Perm :=
  ⟨![0,6,3,7,1,9,4,2,5,8], ![0,4,7,2,6,8,1,3,9,5], by decide +kernel, by decide +kernel⟩

def p22 : Perm :=
  ⟨![0,6,8,4,9,1,7,2,5,3], ![0,5,7,9,3,8,1,6,2,4], by decide +kernel, by decide +kernel⟩

def p23 : Perm :=
  ⟨![0,6,8,9,4,7,1,5,2,3], ![0,6,8,9,4,7,1,5,2,3], by decide +kernel, by decide +kernel⟩

def p24 : Perm :=
  ⟨![0,7,4,2,6,3,9,8,1,5], ![0,8,3,5,2,9,4,1,7,6], by decide +kernel, by decide +kernel⟩

def p25 : Perm :=
  ⟨![0,7,4,6,2,9,3,1,8,5], ![0,7,4,6,2,9,3,1,8,5], by decide +kernel, by decide +kernel⟩

def p26 : Perm :=
  ⟨![0,7,5,3,9,2,6,1,8,4], ![0,7,5,3,9,2,6,1,8,4], by decide +kernel, by decide +kernel⟩

def p27 : Perm :=
  ⟨![0,7,5,9,3,6,2,8,1,4], ![0,8,6,4,9,2,5,1,7,3], by decide +kernel, by decide +kernel⟩

def p28 : Perm :=
  ⟨![0,8,3,2,5,4,9,7,1,6], ![0,8,3,2,5,4,9,7,1,6], by decide +kernel, by decide +kernel⟩

def p29 : Perm :=
  ⟨![0,8,3,5,2,9,4,1,7,6], ![0,7,4,2,6,3,9,8,1,5], by decide +kernel, by decide +kernel⟩

def p30 : Perm :=
  ⟨![0,8,6,4,9,2,5,1,7,3], ![0,7,5,9,3,6,2,8,1,4], by decide +kernel, by decide +kernel⟩

def p31 : Perm :=
  ⟨![0,8,6,9,4,5,2,7,1,3], ![0,8,6,9,4,5,2,7,1,3], by decide +kernel, by decide +kernel⟩

def p32 : Perm :=
  ⟨![0,9,1,5,6,8,7,3,4,2], ![0,2,9,7,8,3,4,6,5,1], by decide +kernel, by decide +kernel⟩

def p33 : Perm :=
  ⟨![0,9,1,6,5,7,8,4,3,2], ![0,2,9,8,7,4,3,5,6,1], by decide +kernel, by decide +kernel⟩

def p34 : Perm :=
  ⟨![0,9,2,7,8,6,5,3,4,1], ![0,9,2,7,8,6,5,3,4,1], by decide +kernel, by decide +kernel⟩

def p35 : Perm :=
  ⟨![0,9,2,8,7,5,6,4,3,1], ![0,9,2,8,7,5,6,4,3,1], by decide +kernel, by decide +kernel⟩

def elements : List Perm := [p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29,p30,p31,p32,p33,p34,p35]
def generatorWords : List (List Bool) := [[],[true,true,true,false,true,false,true],[false,true,true],[true,false,true,false,true,false],[false,true,false,true,false,true],[true,true,false],[true,false,true,false,true],[false,true,true,false],[true,false,true],[false,true,true,true],[false,true,false],[true,true,true,false,true,false],[true,true,true,false],[false,true,false,true,false],[true,true,false,true,false,true],[true,false,true,true,false],[false,true,true,true,false,true],[true],[true,true,false,true,false,true,false],[true,false,true,true],[true,true,false,true,false],[true,false,true,true,true,false],[false,true],[true,true,true,false,true],[true,false],[false,true,true,true,false,true,false],[true,true,true],[false,true,false,true],[true,false,true,true,true],[true,true,false,true],[true,false,true,false],[false,true,true,true,false],[false,true,false,true,false,true,false],[true,true],[false],[true,true,true,false,true,false,true,false]]
theorem words_eq : generatorWords.map (word g0 g1) = elements := by decide +kernel
theorem one_mem : (1 : Perm) ∈ elements := by decide +kernel
theorem mul_mem : ∀ p ∈ elements, ∀ q ∈ elements, p*q ∈ elements := by decide +kernel
theorem inv_mem : ∀ p ∈ elements, p⁻¹ ∈ elements := by decide +kernel
theorem generators_mem : g0 ∈ elements ∧ g1 ∈ elements := by decide +kernel
def subgroup : Subgroup Perm := tableSubgroup elements one_mem mul_mem inv_mem
theorem subgroup_eq_generated : subgroup = Subgroup.closure {g0,g1} := by
  exact tableSubgroup_eq_closure elements one_mem mul_mem inv_mem g0 g1
    generators_mem generatorWords words_eq
theorem order : Nat.card (Subgroup.closure ({g0,g1} : Set Perm)) = 36 := by
  rw [← subgroup_eq_generated]
  rw [show subgroup = tableSubgroup elements one_mem mul_mem inv_mem from rfl, tableSubgroup_card]
  decide +kernel
end D4.PaperSymmetry.C3
