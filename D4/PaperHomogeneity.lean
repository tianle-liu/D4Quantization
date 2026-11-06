import D4.CertificateMomentData
import D4.KernelCompute

/-! The three determinant and moment polynomials have their stated
homogeneous degrees, for arbitrary real inputs and scaling factors. -/
noncomputable section
namespace D4.PaperHomogeneity
open Certificate CertificateMoments

def HomogeneousTerms (d : Nat) (p : Poly) : Prop :=
  ∀ t ∈ p, t.1.length = d

theorem monomial_scaling (c : ℝ) (x : Nat → ℝ) (m : Monomial) :
    monomial (fun i => c*x i) m = c^m.length * monomial x m := by
  induction m with
  | nil => simp [monomial]
  | cons a m ih =>
    change (c*x a)*monomial (fun i => c*x i) m =
      c^(m.length+1)*(x a*monomial x m)
    rw [ih,pow_succ]
    ring

theorem eval_homogeneous (d : Nat) (p : Poly) (hp : HomogeneousTerms d p)
    (c : ℝ) (x : Nat → ℝ) :
    eval (fun i => c*x i) p = c^d * eval x p := by
  induction p with
  | nil => simp
  | cons t p ih =>
    have ht := hp t (List.mem_cons_self)
    have htail : HomogeneousTerms d p := fun s hs => hp s (List.mem_cons_of_mem _ hs)
    rw [eval_cons,eval_cons,monomial_scaling,ht,ih htail]
    ring

private theorem determinantC1_degree_check :
    (determinantC1.all fun t => decide (t.1.length=4)) = true := by
  kernel_rfl

theorem determinantC1_degree : HomogeneousTerms 4 determinantC1 := by
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.mp determinantC1_degree_check t ht)

theorem determinantC1_homogeneous (c : ℝ) (x : Nat → ℝ) :
    eval (fun i => c*x i) determinantC1 = c^4 * eval x determinantC1 :=
  eval_homogeneous 4 determinantC1 determinantC1_degree c x

private theorem determinantC2_degree_check :
    (determinantC2.all fun t => decide (t.1.length=4)) = true := by
  kernel_rfl

theorem determinantC2_degree : HomogeneousTerms 4 determinantC2 := by
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.mp determinantC2_degree_check t ht)

theorem determinantC2_homogeneous (c : ℝ) (x : Nat → ℝ) :
    eval (fun i => c*x i) determinantC2 = c^4 * eval x determinantC2 :=
  eval_homogeneous 4 determinantC2 determinantC2_degree c x

private theorem determinantC3_degree_check :
    (determinantC3.all fun t => decide (t.1.length=4)) = true := by
  kernel_rfl

theorem determinantC3_degree : HomogeneousTerms 4 determinantC3 := by
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.mp determinantC3_degree_check t ht)

theorem determinantC3_homogeneous (c : ℝ) (x : Nat → ℝ) :
    eval (fun i => c*x i) determinantC3 = c^4 * eval x determinantC3 :=
  eval_homogeneous 4 determinantC3 determinantC3_degree c x

private theorem momentC1_degree_check :
    (momentC1.all fun t => decide (t.1.length=5)) = true := by
  kernel_rfl

theorem momentC1_degree : HomogeneousTerms 5 momentC1 := by
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.mp momentC1_degree_check t ht)

theorem momentC1_homogeneous (c : ℝ) (x : Nat → ℝ) :
    eval (fun i => c*x i) momentC1 = c^5 * eval x momentC1 :=
  eval_homogeneous 5 momentC1 momentC1_degree c x

private theorem momentC2_degree_check :
    (momentC2.all fun t => decide (t.1.length=5)) = true := by
  kernel_rfl

theorem momentC2_degree : HomogeneousTerms 5 momentC2 := by
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.mp momentC2_degree_check t ht)

theorem momentC2_homogeneous (c : ℝ) (x : Nat → ℝ) :
    eval (fun i => c*x i) momentC2 = c^5 * eval x momentC2 :=
  eval_homogeneous 5 momentC2 momentC2_degree c x

private theorem momentC3_degree_check :
    (momentC3.all fun t => decide (t.1.length=5)) = true := by
  kernel_rfl

theorem momentC3_degree : HomogeneousTerms 5 momentC3 := by
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.mp momentC3_degree_check t ht)

theorem momentC3_homogeneous (c : ℝ) (x : Nat → ℝ) :
    eval (fun i => c*x i) momentC3 = c^5 * eval x momentC3 :=
  eval_homogeneous 5 momentC3 momentC3_degree c x

end D4.PaperHomogeneity
