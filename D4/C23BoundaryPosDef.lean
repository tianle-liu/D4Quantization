import D4.C23BoundaryRectangle
import D4.C23BoundaryHexagonSupport
import D4.PrincipalSecondaryBoundary

noncomputable section
namespace D4.C23Local
open Matrix Set Analytic Principal AreaEnvelope

theorem principal_posDef_of_singletons {w : Fin 10 → ℝ}
    (hw : ∀ e,0≤w e) (hs : ∀ i : Fin 4,0<w (singletonEdge i)) :
    (principalForm w).PosDef := by
  refine ⟨principal_isHermitian w,?_⟩
  intro x hx
  have hn : ∃ i,x i≠0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨i,hi⟩ := hn
  have h : 0<quadratic (principalForm w) x := by
    rw [quadratic_principal]
    apply Finset.sum_pos' (fun e _ => mul_nonneg (hw e) (sq_nonneg _))
    refine ⟨singletonEdge i,Finset.mem_univ _,?_⟩
    rw [singleton_generator_dot]
    exact mul_pos (hs i) (sq_pos_of_ne_zero hi)
  simpa only [quadratic,star_trivial] using h

theorem boundary2_posDef (z : Parameters) (hz : ∀ i,0≤z i)
    (hp : ∀ i : Fin 10,i≠0 → 0<z i) : (boundary2Form z).PosDef := by
  apply principal_posDef_of_singletons (boundary2_weights_nonneg z hz)
  intro i
  fin_cases i
  · exact hp 1 (by decide)
  · exact hp 2 (by decide)
  · exact hp 3 (by decide)
  · exact hp 4 (by decide)

theorem boundary3_posDef (z : Parameters) (hz : ∀ i,0≤z i)
    (hp : ∀ i : Fin 10,i≠9 → 0<z i) : (boundary3Form z).PosDef := by
  rw [boundary3_form]
  unfold form3
  apply secondary_posDef_of_pos cone3Vectors (hp 0 (by decide))
  intro i
  fin_cases i
  · exact hz 1
  · exact hz 2
  · exact hz 3
  · exact hz 4
  · exact hz 5
  · exact hz 6
  · exact hz 7
  · exact hz 8
  · exact le_refl 0

end D4.C23Local
