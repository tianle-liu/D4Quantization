import D4.AreaPolygonFan

/-! The arithmetic mean of the vertices supplies an analytic interior
apex; its existence is derived from actual supporting inequalities. -/
noncomputable section
namespace D4.AreaEnvelope
open Set Matrix
open scoped BigOperators Topology

def vertexMean {ι : Type*} [Fintype ι] (v : ι → Plane) : Plane :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ i,v i

theorem eval_vertexMean {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : PlaneSlack) (v : ι → Plane) :
    s.eval (vertexMean v)=(Fintype.card ι : ℝ)⁻¹ * ∑ i,s.eval (v i) := by
  have hn : (Fintype.card ι : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [vertexMean,PlaneSlack.eval,dotProduct_smul,smul_eq_mul,dotProduct,Fin.sum_univ_succ,Finset.sum_apply,
    Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  ring

theorem vertexMean_strict {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : PlaneSlack) (v : ι → Plane)
    (hn : ∀ i,0≤s.eval (v i)) (hp : ∃ i,0<s.eval (v i)) :
    0<s.eval (vertexMean v) := by
  rw [eval_vertexMean]
  have hc : 0<(Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  apply mul_pos (inv_pos.mpr hc)
  apply Finset.sum_pos' (fun i _ => hn i)
  obtain ⟨i,hi⟩ := hp
  exact ⟨i,Finset.mem_univ i,hi⟩

theorem vertexMean_interior {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (s : κ → PlaneSlack) (v : ι → Plane)
    (hn : ∀ j i,0≤(s j).eval (v i)) (hp : ∀ j,∃ i,0<(s j).eval (v i)) :
    vertexMean v ∈ interior {x | ∀ j,0≤(s j).eval x} := by
  let U : Set Plane := {x | ∀ j,0<(s j).eval x}
  have hu : IsOpen U := by
    simp only [U,setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt continuous_const (by unfold PlaneSlack.eval dotProduct; fun_prop)
  have hsub : U⊆{x | ∀ j,0≤(s j).eval x} := fun x hx j => (hx j).le
  apply (interior_mono hsub)
  rw [hu.interior_eq]
  exact fun j => vertexMean_strict (s j) v (hn j) (hp j)

theorem analyticAt_vertexMean {ι : Type*} [Fintype ι]
    (v : ι → ℝ → Plane) (t₀ : ℝ)
    (hv : ∀ i j,AnalyticAt ℝ (fun t => v i t j) t₀) (j : Fin 2) :
    AnalyticAt ℝ (fun t => vertexMean (fun i => v i t) j) t₀ := by
  change AnalyticAt ℝ (fun t => (Fintype.card ι : ℝ)⁻¹ * (∑ i,v i t) j) t₀
  simp only [Finset.sum_apply]
  exact analyticAt_const.mul (Finset.analyticAt_sum _ (fun i _ => hv i j))

end D4.AreaEnvelope
