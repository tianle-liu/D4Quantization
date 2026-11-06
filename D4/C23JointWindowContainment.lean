import D4.C23JointWindowBasic

noncomputable section
namespace D4.C23Local
open Analytic AreaEnvelope Matrix Set

theorem moving_window2_subset (Q : Gram) (z w : Parameters) {η R δ : ℝ}
    (hδ : δ ≤ η/16) (hδR : δ ≤ R/4)
    (hw : ∀ i, |w i-z i|≤δ) :
    localWindow2 Q (lower2 (w 9)) {L | gap2 (w 3) (w 4) (w 9) L≤η/2} (R/2) ⊆
      localWindow2 Q (lower2 (z 9)) {L | gap2 (z 3) (z 4) (z 9) L≤η} R := by
  apply localWindow2_subset_of_shift
  · intro L hL
    have h := gap2_parameter_le (w 3) (w 4) (w 9) (z 3) (z 4) (z 9) L
    have h3 := hw 3
    have h4 := hw 4
    have h9 := hw 9
    change gap2 (z 3) (z 4) (z 9) L≤η
    change gap2 (w 3) (w 4) (w 9) L≤η/2 at hL
    linarith
  · intro L _
    have h := lower2_sub_abs_le (w 9) (z 9) L
    have h9 := hw 9
    linarith

theorem moving_rectangle3_subset (z w : Parameters) {η : ℝ} (hη : 0≤η)
    (h1 : |w 1-z 1|≤η/4) (h2 : |w 2-z 2|≤η/4) :
    localRectangle3 (2*w 1) (2*w 2) (η/2) (η/2) ⊆
      localRectangle3 (2*z 1) (2*z 2) η η := by
  intro L hL
  have h1' := (abs_le.mp h1).2
  have h2' := (abs_le.mp h2).2
  constructor
  · intro i
    have h := hL.1 i
    fin_cases i <;>
      simp only [Fin.reduceFinMk,Matrix.cons_val] at h ⊢ <;> linarith
  · intro i
    have h := hL.2 i
    fin_cases i <;>
      simp only [Fin.reduceFinMk,Matrix.cons_val] at h ⊢ <;> linarith

theorem moving_window3_subset (Q : Gram) (z w : Parameters) {η R : ℝ}
    (hη : 0≤η) (hR : 0≤R)
    (h1 : |w 1-z 1|≤η/4) (h2 : |w 2-z 2|≤η/4) :
    localWindow3 Q lower3 (localRectangle3 (2*w 1) (2*w 2) (η/2) (η/2)) (R/2) ⊆
      localWindow3 Q lower3 (localRectangle3 (2*z 1) (2*z 2) η η) R :=
  localWindow3_subset _ _ _ _ (by linarith) (moving_rectangle3_subset z w hη h1 h2)

end D4.C23Local
