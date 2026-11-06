import D4.DelaunayFlipHull
import D4.DelaunaySourceChecks
import D4.DelaunayShift

noncomputable section
namespace D4.Delaunay
open Matrix Analytic Principal Set

theorem cast_flipMinus (i j : Fin 4) (V W : IntVec) (s : Bool) :
    (fun k => castVec (flipMinus i j V W s k))=
      ![castVec 0,castVec (if s then unit j else unit i),castVec (unit i+unit j),castVec V,castVec W] := by
  cases s <;> ext k l <;> fin_cases k <;> simp [flipMinus,castVec]

theorem cast_flipPlus_false (i j : Fin 4) (V W : IntVec) :
    (fun k => castVec (flipPlus i j V W false k))=
      ![castVec 0,castVec (unit i),castVec (unit j),castVec V,castVec W] := by
  ext k l
  fin_cases k <;> simp [flipPlus,castVec]

theorem cast_flipPlus_true (i j : Fin 4) (V W : IntVec) :
    (fun k => castVec (flipPlus i j V W true k))=
      ![castVec (unit i),castVec (unit j),castVec (unit i+unit j),castVec V,castVec W] := by
  ext k l
  fin_cases k <;> simp [flipPlus,castVec]

theorem square_flip_same_region (i j : Fin 4) (V W : IntVec) :
    simplexRegion (flipMinus i j V W false) ∪ simplexRegion (flipMinus i j V W true)=
      simplexRegion (flipPlus i j V W false) ∪ simplexRegion (flipPlus i j V W true) := by
  have hrel : castVec (0 : IntVec)+castVec (unit i+unit j)=castVec (unit i)+castVec (unit j) := by
    rw [castVec_add]
    have hz : castVec (0 : IntVec)=(0:Vec) := by ext k; simp [castVec]
    rw [hz,zero_add]
  have h := quadrilateral_flip_same_region (castVec 0) (castVec (unit i))
    (castVec (unit i+unit j)) (castVec (unit j)) (castVec V) (castVec W) hrel
  have hs : vertexSimplex ![castVec (unit i),castVec (unit i+unit j),castVec (unit j),castVec V,castVec W]=
      vertexSimplex ![castVec (unit i),castVec (unit j),castVec (unit i+unit j),castVec V,castVec W] := by
    rw [vertexSimplex_eq_convexHull,vertexSimplex_eq_convexHull]
    congr 1
    ext x
    simp only [Matrix.range_cons,Matrix.range_empty,Set.union_empty,Set.mem_union,Set.mem_singleton_iff]
    tauto
  simpa only [simplexRegion,cast_flipMinus,cast_flipPlus_false,cast_flipPlus_true,
    Bool.false_eq_true,if_false,if_true,hs] using h

theorem unit_cast (i : Fin 4) : castVec (unit i)=Pi.single i (1:ℝ) := by
  ext j
  simp [castVec,unit,Pi.single_apply]

theorem square_lifting_difference {Q : Gram} (hQ : Q.IsHermitian) (i j : Fin 4) :
    quadratic Q (castVec (unit i+unit j))-quadratic Q (castVec (unit i))-
      quadratic Q (castVec (unit j))=2*Q i j := by
  rw [castVec_add,quadratic_add_vec hQ,unit_cast,unit_cast]
  simp only [Matrix.mulVec_single_one,single_dotProduct,one_mul,Matrix.transpose_apply]
  ring

end D4.Delaunay
