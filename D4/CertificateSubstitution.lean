import D4.CertificatePrimitiveProduct

/-! Substitution in the checked sparse polynomial representation. -/
namespace D4.Certificate

def substituteMonomial (σ : Nat → Poly) (m : Monomial) : Poly :=
  List.rec [([], 1)] (fun i _ p => mulMergePrim (σ i) p) m

@[simp] theorem eval_substituteMonomial (x : Nat → ℝ) (σ : Nat → Poly)
    (m : Monomial) :
    eval x (substituteMonomial σ m) = monomial (fun i => eval x (σ i)) m := by
  induction m with
  | nil => simp [substituteMonomial, monomial]
  | cons i m ih =>
    simp only [substituteMonomial, List.rec, eval_mulMergePrim] at *
    rw [ih]
    rfl

def substitute (σ : Nat → Poly) (p : Poly) : Poly :=
  sumFast (mapRec (fun t => scale t.2 (substituteMonomial σ t.1)) p)

@[simp] theorem eval_substitute (x : Nat → ℝ) (σ : Nat → Poly) (p : Poly) :
    eval x (substitute σ p) = eval (fun i => eval x (σ i)) p := by
  rw [substitute, eval_sumFast]
  simp only [mapRec_eq_map, List.map_map, Function.comp_def, eval_scale,
    eval_substituteMonomial]
  rfl

theorem eval_substitute_chunks (x : Nat → ℝ) (σ : Nat → Poly) (ps : List Poly) :
    eval x (sumFast (ps.map (substitute σ))) =
      eval (fun i => eval x (σ i)) ps.flatten := by
  rw [eval_sumFast]
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, List.flatten_cons, eval_append,
      eval_substitute, ih]

end D4.Certificate
