import D4.C23WindowLocalizationBasic
import D4.C23BoundaryEmbedding2
import D4.C23BoundaryHexagon

noncomputable section
namespace D4.C23Local
open Matrix Set Filter Topology Analytic Principal AreaEnvelope
attribute [local instance] Matrix.normedAddCommGroup

theorem boundary2_localWindow_sites (z : Parameters) (hz : ∀ i,0≤z i)
    (hp : ∀ i : Fin 10,i≠0 → 0<z i) :
    ∃ η R ε : ℝ,0<η ∧ 0<R ∧ η<R/4 ∧ 0<ε ∧
      ∀ Q : Gram,Q.PosDef → ‖Q-boundary2Form z‖<ε →
        let W := localWindow2 Q (lower2 (z 9)) {L | gap2 (z 3) (z 4) (z 9) L≤η} R
        (∀ r∈W,∀ n : IntVec,quadratic Q (dualInverse Q r-castVec n)=dualNearest Q r →
            n∈Finset.univ.image sites2) ∧
        (∀ r∈W,∀ n : IntVec,r+dualMap Q (castVec n)∈W → n=0) := by
  have hQ := boundary2_posDef z hz hp
  apply windows_nearest_sites (fun Q => windowPoint2 Q (lower2 (z 9)))
    (windowPoint2_joint_continuous (by unfold lower2 min4; fun_prop))
    (gap2 (z 3) (z 4) (z 9)) (gap2_continuous _ _ _) (gap2_nonneg _ _ _)
    (gap2_sublevel_compact _ _ _ 1 (hz 3) (hz 4) (hz 9) (by norm_num))
    (boundary2Form z) hQ (dualSquareFace (boundary2Form z) 0 1)
    (dualSquareFace_compact hQ 0 1) (fun _ h => h.1) (Finset.univ.image sites2)
  · intro r hr n hn
    rw [boundary2_dual_face z hz] at hr
    obtain ⟨L,hL,rfl⟩ := hr
    obtain ⟨i,hi⟩ := boundary2_zero_cost_sites z hz hp L hL n hn
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi.symm⟩
  · exact boundary2_translate_injective z hz hp
  · intro L hL
    have hhex := (hexagon2_gap (z 3) (z 4) (z 9) (hz 3) (hz 4) (hz 9) L).mpr hL
    have hU : lower2 (z 9) L=0 := by
      have hlow : lower2 (z 9) L≤0 := min_le_left _ _
      have hupp : upper2 (z 3) (z 4) (z 9) L≤0 := min_le_left _ _
      change -lower2 (z 9) L-upper2 (z 3) (z 4) (z 9) L=0 at hL
      linarith
    have he : windowPoint2 (boundary2Form z) (lower2 (z 9)) (L,(0,0))=boundary2Point z L := by
      ext i; fin_cases i <;>
        simp only [windowPoint2,inverseCoordinates2,fiberCoordinates,boundary2Point,
          Fin.reduceFinMk,Matrix.cons_val,hU] <;> ring
    rw [he]
    exact ⟨boundary2_point_support z hz L hhex,rfl,rfl⟩


end D4.C23Local
