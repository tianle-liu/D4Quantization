import D4.DelaunayMatrices
import D4.DualPeriodMoment

/-! Empty-sphere semantics for lattice simplices.  The comparison is with every
integer lattice point, not a finite selection of competitors. -/
noncomputable section
namespace D4.Delaunay
open Matrix Analytic Secondary

/-- The vertices lie on a sphere whose open interior contains no lattice point. -/
def IsDelaunaySimplex (Q : Gram) (S : LatticeSimplex) : Prop :=
  ∃ x : Vec, ∃ ρ : ℝ,
    (∀ i, quadratic Q (x-castVec (S i))=ρ) ∧
    ∀ n : IntVec, ρ ≤ quadratic Q (x-castVec n)

def SupportsSimplex (Q : Gram) (S : LatticeSimplex) (r : Vec) : Prop :=
  DualSupport Q r ∧ ∀ i, quadratic Q (castVec (S i))=dotProduct (castVec (S i)) r

theorem supportsSimplex_isDelaunay {Q : Gram} (hQ : Q.PosDef)
    (S : LatticeSimplex) (r : Vec) (h : SupportsSimplex Q S r) :
    IsDelaunaySimplex Q S := by
  refine ⟨dualInverse Q r, quadratic Q (dualInverse Q r), ?_, ?_⟩
  · intro i
    rw [quadratic_eq_dualSiteCost hQ.1, dualMap_dualInverse hQ]
    simp only [dualSiteCost, h.2 i, sub_self, add_zero]
  · intro n
    rw [quadratic_eq_dualSiteCost hQ.1, dualMap_dualInverse hQ]
    exact le_add_of_nonneg_right (sub_nonneg.mpr (h.1 n))

theorem supportsSimplex_nearest {Q : Gram} (hQ : Q.PosDef)
    (S : LatticeSimplex) (r : Vec) (h : SupportsSimplex Q S r) (i : Fin 5) :
    nearest Q (dualInverse Q r)=quadratic Q (dualInverse Q r-castVec (S i)) := by
  apply le_antisymm (nearest_le hQ.posSemidef _ _)
  apply le_ciInf
  intro n
  rw [quadratic_eq_dualSiteCost hQ.1, quadratic_eq_dualSiteCost hQ.1,
    dualMap_dualInverse hQ]
  simp only [dualSiteCost, h.2 i, sub_self, add_zero]
  exact le_add_of_nonneg_right (sub_nonneg.mpr (h.1 n))

theorem cast_dotProduct (u v : IntVec) :
    dotProduct (castVec u) (castVec v)=((dotProduct u v : ℤ):ℝ) := by
  simp [dotProduct, castVec]

theorem dotProduct_sum (x : Vec) (v : Fin 10 → Vec) :
    dotProduct x (∑ k, v k)=∑ k, dotProduct x (v k) := by
  simp only [dotProduct,Finset.sum_apply,Finset.mul_sum]
  exact Finset.sum_comm

theorem tight_combination (g : Fin 10 → IntegerGram)
    (v : Fin 10 → IntVec) (w : Fin 10 → ℝ) (S : LatticeSimplex)
    (ht : ∀ k i, quadraticZ (g k) (S i)=dotProduct (S i) (v k)) :
    ∀ i, quadratic (generatedForm g w) (castVec (S i))=
      dotProduct (castVec (S i)) (∑ k, w k • castVec (v k)) := by
  intro i
  rw [quadratic_generated, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [dotProduct_smul, smul_eq_mul, cast_dotProduct, ht]

end D4.Delaunay
