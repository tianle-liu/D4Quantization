import D4.C23BoundaryHexagonData
noncomputable section
namespace D4.C23Local
open Matrix Set Analytic Principal AreaEnvelope
set_option maxHeartbeats 200000

theorem boundary2_coefficients_exist (z : Parameters)
    (hz : ∀ i, 0 ≤ z i) (L : Plane) (hL : L ∈ hexagon2 (z 3) (z 4) (z 9)) :
    ∃ t : Fin 10 → ℝ, t ∈ Icc (-(boundary2Weights z)) (boundary2Weights z) ∧
      t=![z 1,z 2,
        L 0-z 3-z 9-max (-z 9) (max (L 0-2*z 3-z 9) (z 9-L 1)),
        L 1-z 4-z 9+max (-z 9) (max (L 0-2*z 3-z 9) (z 9-L 1)),
        0,z 5,z 6,z 7,z 8,max (-z 9) (max (L 0-2*z 3-z 9) (z 9-L 1))] := by
  rcases hL with ⟨h1,h2,h3,h4,h5,h6⟩
  let k := max (-z 9) (max (L 0-2*z 3-z 9) (z 9-L 1))
  have hk0 : -z 9 ≤ k := le_max_left _ _
  have hk1 : L 0-2*z 3-z 9 ≤ k := le_trans (le_max_left _ _) (le_max_right _ _)
  have hk2 : z 9-L 1 ≤ k := le_trans (le_max_right _ _) (le_max_right _ _)
  have hk3 : k ≤ z 9 := by dsimp [k]; exact max_le (by linarith [hz 9]) (max_le (by linarith [hz 9]) (by linarith [hz 9]))
  have hk4 : k ≤ L 0-z 9 := by dsimp [k]; exact max_le (by linarith [hz 3]) (max_le (by linarith [hz 3]) (by linarith [hz 3]))
  have hk5 : k ≤ 2*z 4+z 9-L 1 := by dsimp [k]; exact max_le (by linarith [hz 4]) (max_le (by linarith [hz 4]) (by linarith [hz 4]))
  let t : Fin 10 → ℝ :=
    ![z 1,z 2,L 0-z 3-z 9-k,L 1-z 4-z 9+k,0,z 5,z 6,z 7,z 8,k]
  refine ⟨t,?_,rfl⟩
  · constructor
    · intro i
      fin_cases i
      · change -(z 1) ≤ z 1; linarith only [hz 1]
      · change -(z 2) ≤ z 2; linarith only [hz 2]
      · change -(z 3) ≤ L 0-z 3-z 9-k; linarith only [hk4]
      · change -(z 4) ≤ L 1-z 4-z 9+k; linarith only [hk2]
      · change -(0:ℝ) ≤ 0; norm_num
      · change -(z 5) ≤ z 5; linarith only [hz 5]
      · change -(z 6) ≤ z 6; linarith only [hz 6]
      · change -(z 7) ≤ z 7; linarith only [hz 7]
      · change -(z 8) ≤ z 8; linarith only [hz 8]
      · exact hk0
    · intro i
      fin_cases i
      · exact le_refl _
      · exact le_refl _
      · change L 0-z 3-z 9-k ≤ z 3; linarith only [hk1]
      · change L 1-z 4-z 9+k ≤ z 4; linarith only [hk5]
      · exact le_refl _
      · exact le_refl _
      · exact le_refl _
      · exact le_refl _
      · exact le_refl _
      · exact hk3

end D4.C23Local
