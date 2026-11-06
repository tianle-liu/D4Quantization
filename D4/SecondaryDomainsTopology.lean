import D4.SecondaryDomainsCoordinates
import D4.SecondaryDomainsSpace
import D4.SecondaryDomainsNecessity

/-! The three strict secondary domains in the genuine ten-dimensional
 symmetric-matrix topology. Each is the complete locus of its actual type. -/
noncomputable section
namespace D4.Delaunay
open Analytic Matrix Set

def coneFamily (i : Fin 3) : Set (Finset IntVec) :=
  ![periodicVertexFamily cells1, periodicVertexFamily cells2, periodicVertexFamily cells3] i

def coneSymForm (i : Fin 3) (w : Fin 10 → ℝ) : SymGram :=
  ⟨coneForm i w, coneForm_isSymm i w⟩

def coneHomeomorph (i : Fin 3) : (Fin 10 → ℝ) ≃ₜ SymGram where
  toFun := coneSymForm i
  invFun := fun Q => coneCoordinates i Q.1
  left_inv := coneCoordinates_form i
  right_inv := fun Q => Subtype.ext (coneForm_coordinates i Q.1 Q.2)
  continuous_toFun := (coneForm_continuous i).subtype_mk _
  continuous_invFun := (coneCoordinates_continuous i).comp continuous_subtype_val

def positiveCone (i : Fin 3) : Set SymGram :=
  {Q | ∀ k, 0 < coneCoordinates i Q.1 k}

def typeLocus (T : Set (Finset IntVec)) : Set SymGram :=
  {Q | Q.1.PosDef ∧ delaunayType Q.1=T}

theorem coneType_iff (i : Fin 3) (w : Fin 10 → ℝ) :
    delaunayType (coneForm i w)=coneFamily i ↔ ∀ k, 0 < w k := by
  fin_cases i
  · exact principal_delaunayType_iff w
  · exact secondary2_delaunayType_iff w
  · exact secondary3_delaunayType_iff w

theorem positiveCone_eq_typeLocus (i : Fin 3) : positiveCone i=typeLocus (coneFamily i) := by
  ext Q
  constructor
  · intro h
    have hform := coneForm_coordinates i Q.1 Q.2
    refine ⟨?_,?_⟩
    · rw [← hform]
      exact coneForm_posDef i _ h
    · rw [← hform]
      exact (coneType_iff i _).mpr h
  · intro h
    apply (coneType_iff i (coneCoordinates i Q.1)).mp
    rw [coneForm_coordinates i Q.1 Q.2]
    exact h.2

theorem positiveCone_isOpen (i : Fin 3) : IsOpen (positiveCone i) := by
  have h : positiveCone i=⋂ k : Fin 10, {Q : SymGram | 0 < coneCoordinates i Q.1 k} := by
    ext Q
    simp [positiveCone]
  rw [h]
  apply isOpen_iInter_of_finite
  intro k
  exact isOpen_lt continuous_const
    ((continuous_apply k).comp ((coneCoordinates_continuous i).comp continuous_subtype_val))

theorem positiveCone_nonempty (i : Fin 3) : (positiveCone i).Nonempty := by
  refine ⟨coneSymForm i (fun _ => 1),?_⟩
  change ∀ k, 0 < coneCoordinates i (coneForm i (fun _ => 1)) k
  rw [coneCoordinates_form]
  norm_num

/-- A nonempty open locus of a constant actual full-dimensional Delaunay type,
 maximal among open positive-definite loci of that type. -/
def IsMaximalSecondaryDomain (U : Set SymGram) : Prop :=
  IsOpen U ∧ U.Nonempty ∧ ∃ T : Set (Finset IntVec),
    U ⊆ typeLocus T ∧ ∀ V : Set SymGram, IsOpen V → V ⊆ typeLocus T → V ⊆ U

theorem positiveCone_maximal (i : Fin 3) : IsMaximalSecondaryDomain (positiveCone i) := by
  refine ⟨positiveCone_isOpen i,positiveCone_nonempty i,coneFamily i,?_,?_⟩
  · exact (positiveCone_eq_typeLocus i).subset
  · intro V _ hV
    exact hV.trans (positiveCone_eq_typeLocus i).superset

end D4.Delaunay
