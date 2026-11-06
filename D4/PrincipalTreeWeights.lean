import D4.PrincipalTreeCertificates
import D4.PolynomialDeterminants

/-! The sum of the 125 actual tile volumes is the actual Gram determinant. -/
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Principal
open Matrix Analytic Certificate
noncomputable section

def treeWeight (w : Fin 10 → ℝ) (t : Fin 125) : ℝ :=
  ∏ j : Fin 4, w (treeEdges t j)

def treeDetTerms : Poly := List.ofFn fun t : Fin 125 =>
  (List.ofFn (fun j : Fin 4 => (treeEdges t j).val), (1 : ℤ))

theorem treeDetTerms_eq : treeDetTerms = CertificateMoments.determinantC1 :=
  by kernel_rfl

def extendWeight (w : Fin 10 → ℝ) (n : Nat) : ℝ :=
  if h : n < 10 then w ⟨n, h⟩ else 0

@[simp] theorem extendWeight_fin (w : Fin 10 → ℝ) (e : Fin 10) :
    extendWeight w e.val = w e := by simp [extendWeight, e.isLt]

theorem treeDetTerms_eval (w : Fin 10 → ℝ) :
    eval (extendWeight w) treeDetTerms = ∑ t, treeWeight w t := by
  simp only [eval, monomial, treeDetTerms, treeWeight, List.map_ofFn,
    List.sum_ofFn, List.prod_ofFn, Function.comp_apply, Int.cast_one, one_mul, extendWeight_fin]

theorem sum_treeWeight (w : Fin 10 → ℝ) :
    (∑ t : Fin 125, treeWeight w t) = (principalForm w).det := by
  rw [← treeDetTerms_eval, treeDetTerms_eq, determinantC1_eval]
  simp only [extendWeight_fin]

end
end D4.Principal
