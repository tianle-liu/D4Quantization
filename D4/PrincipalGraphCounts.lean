import D4.PrincipalGraphBasics
namespace D4.PrincipalGraphs

def countCycleLength (n : ℕ) : ℕ :=
  (fiveEdgeGraphs.filter fun H => (graph H).Connected ∧ (cycleCore H).card=n).card

def countCycleLengthFast (n : ℕ) : ℕ :=
  (fiveEdgeGraphs.filter fun H => NoIsolated H ∧ (cycleCore H).card=n).card

theorem countCycleLength_eq (n : ℕ) : countCycleLength n=countCycleLengthFast n := by
  unfold countCycleLength countCycleLengthFast
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro H hH
  have hc : H.card=5 := by simpa [fiveEdgeGraphs] using hH
  rw [connected_iff_noIsolated hc]

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem triangle_count_fast : countCycleLengthFast 3 = 150 := by kernel_rfl
theorem quadrilateral_count_fast : countCycleLengthFast 4 = 60 := by kernel_rfl
theorem pentagon_count_fast : countCycleLengthFast 5 = 12 := by kernel_rfl

theorem triangle_count : countCycleLength 3 = 150 := by rw [countCycleLength_eq,triangle_count_fast]
theorem quadrilateral_count : countCycleLength 4 = 60 := by rw [countCycleLength_eq,quadrilateral_count_fast]
theorem pentagon_count : countCycleLength 5 = 12 := by rw [countCycleLength_eq,pentagon_count_fast]

end D4.PrincipalGraphs
