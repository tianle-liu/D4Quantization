import D4.Certificate
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Real.Lemmas

noncomputable section
namespace D4.Certificate

theorem monomial_continuous {X : Type*} [TopologicalSpace X]
    (x : X → Nat → ℝ) (hx : ∀ i, Continuous fun a => x a i) (m : Monomial) :
    Continuous fun a => monomial (x a) m := by
  induction m with
  | nil => exact continuous_const
  | cons i m ih => simpa only [monomial, List.map_cons, List.prod_cons] using (hx i).mul ih

theorem eval_continuous {X : Type*} [TopologicalSpace X]
    (x : X → Nat → ℝ) (hx : ∀ i, Continuous fun a => x a i) (p : Poly) :
    Continuous fun a => eval (x a) p := by
  induction p with
  | nil => exact continuous_const
  | cons t ts ih =>
    simpa only [eval_cons] using (continuous_const.mul (monomial_continuous x hx t.1)).add ih

end D4.Certificate
