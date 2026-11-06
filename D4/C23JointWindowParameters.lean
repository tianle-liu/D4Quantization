import D4.C23JointWindowBasic

/-! Joint continuity and positive-definite neighborhoods in all ten parameters
 and the transverse variable. -/
noncomputable section
namespace D4.C23Local
open Analytic Matrix Set Filter Topology Principal
attribute [local instance] Matrix.normedAddCommGroup

theorem path2_joint_continuous :
    Continuous (fun p : Parameters × ℝ => path2 p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> first
    | (change Continuous (fun p : Parameters × ℝ => p.2); fun_prop)
    | (change Continuous (fun p : Parameters × ℝ => p.1 _); fun_prop)

theorem path3_joint_continuous :
    Continuous (fun p : Parameters × ℝ => path3 p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> first
    | (change Continuous (fun p : Parameters × ℝ => p.2); fun_prop)
    | (change Continuous (fun p : Parameters × ℝ => p.1 _); fun_prop)
    | (change Continuous (fun p : Parameters × ℝ => p.1 _-p.2); fun_prop)
    | (change Continuous (fun p : Parameters × ℝ => p.1 _+p.2); fun_prop)

theorem form2_continuous : Continuous form2 := by
  unfold form2 secondaryForm
  fun_prop

theorem form3_continuous : Continuous form3 := by
  unfold form3 secondaryForm
  fun_prop

theorem form2_path2_joint_continuous :
    Continuous (fun p : Parameters × ℝ => form2 (path2 p.1 p.2)) :=
  form2_continuous.comp path2_joint_continuous

theorem form3_path3_joint_continuous :
    Continuous (fun p : Parameters × ℝ => form3 (path3 p.1 p.2)) :=
  form3_continuous.comp path3_joint_continuous

theorem path2_posDef_eventually_joint (z : Parameters) (hz : ∀ i,0<z i) :
    ∀ᶠ p : Parameters × ℝ in nhds (z,0), (form2 (path2 p.1 p.2)).PosDef := by
  apply posDef_eventually_of_continuous_parameter _ _
    form2_path2_joint_continuous.continuousAt
  · rw [path2_at_zero]
    exact boundary2_posDef z (fun i => (hz i).le) (fun i _ => hz i)
  · intro p
    exact secondary_isHermitian _ _ _

theorem path3_posDef_eventually_joint (z : Parameters) (hz : ∀ i,0<z i) :
    ∀ᶠ p : Parameters × ℝ in nhds (z,0), (form3 (path3 p.1 p.2)).PosDef := by
  apply posDef_eventually_of_continuous_parameter _ _
    form3_path3_joint_continuous.continuousAt
  · rw [path3_at_zero]
    exact boundary3_posDef z (fun i => (hz i).le) (fun i _ => hz i)
  · intro p
    exact secondary_isHermitian _ _ _

theorem parameters_eventually_close (z : Parameters) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ p : Parameters × ℝ in nhds (z,0), ∀ i, |p.1 i-z i|<δ := by
  rw [Filter.eventually_all]
  intro i
  have hc : Continuous (fun p : Parameters × ℝ => |p.1 i-z i|) := by fun_prop
  exact hc.continuousAt.eventually (Iio_mem_nhds (by simpa using hδ))

theorem parameters_eventually_pos (z : Parameters) (hz : ∀ i,0<z i) :
    ∀ᶠ p : Parameters × ℝ in nhds (z,0), ∀ i, 0<p.1 i := by
  rw [Filter.eventually_all]
  intro i
  have hc : Continuous (fun p : Parameters × ℝ => p.1 i) := by fun_prop
  exact hc.continuousAt.eventually (Ioi_mem_nhds (hz i))

end D4.C23Local
