import D4.DelaunayData

/-! The displayed staircase simplices and the six/four displayed flips. -/
namespace D4.Delaunay
open Matrix Analytic
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def unit (i : Fin 4) : IntVec := Pi.single i 1

def staircase (p : Fin 4 → Fin 4) (v : Fin 5) : IntVec :=
  ∑ i : Fin 4, if i.val < v.val then unit (p i) else 0

def firstLinks : Fin 6 → IntVec × IntVec :=
  let c := unit 0+unit 1
  ![(-unit 2,-unit 2-unit 3), (-unit 3,-unit 2-unit 3),
    (-unit 2,c+unit 3), (-unit 3,c+unit 2),
    (c+unit 2,c+unit 2+unit 3), (c+unit 3,c+unit 2+unit 3)]

def secondLinks : Fin 4 → IntVec × IntVec :=
  let c := unit 2+unit 3
  ![(-unit 1,c+unit 0), (-unit 0,c+unit 1),
    (c+unit 1,c+unit 0), (-unit 0,-unit 1)]

def flipMinus (i j : Fin 4) (V W : IntVec) (side : Bool) : LatticeSimplex :=
  ![0,if side then unit j else unit i,unit i+unit j,V,W]

def flipPlus (i j : Fin 4) (V W : IntVec) (side : Bool) : LatticeSimplex :=
  if side then ![unit i,unit j,unit i+unit j,V,W] else ![0,unit i,unit j,V,W]

theorem staircase_check : (List.finRange 24).all (fun i => decide
    (Function.Bijective (staircasePermutations i) ∧ cells1 i=staircase (staircasePermutations i)))=true := by
  kernel_rfl

theorem first_flip_sources_check : (List.finRange 12).all (fun i =>
    let link := firstLinks ⟨i.val/2,by omega⟩
    let side := decide (i.val%2=1)
    decide ((flips2 i).old=flipMinus 0 1 link.1 link.2 side ∧
      (flips2 i).replacement=flipPlus 0 1 link.1 link.2 side))=true := by kernel_rfl

theorem second_flip_sources_check : (List.finRange 8).all (fun i =>
    let link := secondLinks ⟨i.val/2,by omega⟩
    let side := decide (i.val%2=1)
    decide ((flips3 i).old=flipMinus 2 3 link.1 link.2 side ∧
      (flips3 i).replacement=flipPlus 2 3 link.1 link.2 side))=true := by kernel_rfl

theorem first_flips_check : (List.finRange 12).all
    (fun i => flipCheck cells1 cells2 (flips2 i))=true := by kernel_rfl

theorem second_flips_check : (List.finRange 8).all
    (fun i => flipCheck cells2 cells3 (flips3 i))=true := by kernel_rfl

theorem first_changed_indices_check : ((List.finRange 12).map (fun i => (flips2 i).index)).Nodup := by
  decide +kernel

theorem second_changed_indices_check : ((List.finRange 8).map (fun i => (flips3 i).index)).Nodup := by
  decide +kernel

theorem first_unchanged_check : (List.finRange 24).all (fun i => decide
    (i ∉ (List.finRange 12).map (fun j => (flips2 j).index) → cells2 i=cells1 i))=true := by
  kernel_rfl

theorem second_unchanged_check : (List.finRange 24).all (fun i => decide
    (i ∉ (List.finRange 8).map (fun j => (flips3 j).index) → cells3 i=cells2 i))=true := by
  kernel_rfl

end D4.Delaunay
