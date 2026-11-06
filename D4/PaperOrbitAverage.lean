import D4.PaperMonomialAction
import D4.PaperCoefficientStatistics
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Perm

/-! A coefficient of a group average is the average of the coefficients on
its actual orbit. The action on coefficient functions is inverse transport. -/
noncomputable section
namespace D4.PaperSymmetry
open scoped BigOperators
attribute [local irreducible] PaperStatistics.degreeFive

section General
variable (G X : Type*) [Group G] [Fintype G] [MulAction G X]
variable (x : X) [Fintype (MulAction.orbit G x)]

theorem sum_group_constant_on_orbit (f : X → ℝ) (y : MulAction.orbit G x) :
    (∑ g : G,f (g • y.1))=∑ g : G,f (g • x) := by
  obtain ⟨h,hh⟩ := y.2
  rw [← hh]
  simp only [← mul_smul]
  exact Function.Bijective.sum_comp (Group.mulRight_bijective h) (fun g => f (g • x))

theorem group_orbit_average (f : X → ℝ) :
    (∑ g : G,f (g • x))/(Fintype.card G : ℝ)=
      (∑ y : MulAction.orbit G x,f y.1)/(Fintype.card (MulAction.orbit G x) : ℝ) := by
  classical
  letI : Nonempty (MulAction.orbit G x) := ⟨⟨x,MulAction.mem_orbit_self x⟩⟩
  have hG : (Fintype.card G : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hO : (Fintype.card (MulAction.orbit G x) : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : (Fintype.card (MulAction.orbit G x) : ℝ)*(∑ g : G,f (g • x))=
      (Fintype.card G : ℝ)*(∑ y : MulAction.orbit G x,f y.1) := by
    calc
      _ = ∑ y : MulAction.orbit G x,∑ g : G,f (g • y.1) := by
        simp only [sum_group_constant_on_orbit G X x f,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _ = ∑ g : G,∑ y : MulAction.orbit G x,f (g • y.1) := Finset.sum_comm
      _ = ∑ _ : G,∑ y : MulAction.orbit G x,f y.1 := by
        apply Finset.sum_congr rfl
        intro g _
        exact Function.Bijective.sum_comp (MulAction.bijective g :
          Function.Bijective (fun y : MulAction.orbit G x => g • y)) (fun y => f y.1)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  apply (div_eq_div_iff hG hO).mpr
  nlinarith [hsum]

theorem group_inverse_orbit_average (f : X → ℝ) :
    (∑ g : G,f (g⁻¹ • x))/(Fintype.card G : ℝ)=
      (∑ y : MulAction.orbit G x,f y.1)/(Fintype.card (MulAction.orbit G x) : ℝ) := by
  have he : (∑ g : G,f (g⁻¹ • x))=∑ g : G,f (g • x) := by
    exact Function.Bijective.sum_comp (Equiv.inv G).bijective (fun g => f (g • x))
  rw [he]
  exact group_orbit_average G X x f
end General

local instance (G : Subgroup Perm) : Fintype G := Fintype.ofFinite G
local instance (G : Subgroup Perm) (m : DegreeFiveMonomial) :
    Fintype (MulAction.orbit G m) := Fintype.ofFinite _

/-- The natural action of a variable permutation on a coefficient function. -/
def coefficientAction (p : Perm) (f : DegreeFiveMonomial → ℝ)
    (m : DegreeFiveMonomial) : ℝ := f (p⁻¹ • m)

def averageCoefficient (G : Subgroup Perm) (f : DegreeFiveMonomial → ℝ)
    (m : DegreeFiveMonomial) : ℝ :=
  (∑ g : G,coefficientAction g.1 f m)/(Fintype.card G : ℝ)

theorem averageCoefficient_eq_orbit (G : Subgroup Perm) (f : DegreeFiveMonomial → ℝ)
    (m : DegreeFiveMonomial) :
    averageCoefficient G f m=
      (∑ n : MulAction.orbit G m,f n.1)/(Fintype.card (MulAction.orbit G m) : ℝ) := by
  exact group_inverse_orbit_average G DegreeFiveMonomial m f

/-- The formula applies to the actual coefficients of any sparse polynomial. -/
theorem polynomial_coefficient_orbit_average (G : Subgroup Perm) (p : Certificate.Poly)
    (m : DegreeFiveMonomial) :
    averageCoefficient G (fun n => (PaperStatistics.coefficient p n.1 : ℝ)) m=
      (∑ n : MulAction.orbit G m,(PaperStatistics.coefficient p n.1.1 : ℝ))/
        (Fintype.card (MulAction.orbit G m) : ℝ) :=
  averageCoefficient_eq_orbit G _ m

end D4.PaperSymmetry
