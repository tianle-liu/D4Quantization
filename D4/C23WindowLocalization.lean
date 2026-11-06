import D4.C23WindowLocalization2
import D4.C23WindowLocalizationBasic
import D4.C23BoundaryGap
import D4.C23SmallWindows
import D4.C23BoundaryHexagon
import D4.C23BoundaryRectangleSites
import D4.C23BoundaryEmbedding
import D4.C23LocalRectangleCorrection

noncomputable section
namespace D4.C23Local
open Matrix Set Filter Topology Analytic Principal AreaEnvelope
attribute [local instance] Matrix.normedAddCommGroup

theorem boundary3_localWindow_sites (z : Parameters) (hz : ∀ i,0≤z i)
    (hp : ∀ i : Fin 10,i≠9 → 0<z i) :
    ∃ η R ε : ℝ,0<η ∧ 0<R ∧ η<R/4 ∧ 0<ε ∧
      ∀ Q : Gram,Q.PosDef → ‖Q-boundary3Form z‖<ε →
        let W := localWindow3 Q lower3 {L | gap3 (2*z 1) (2*z 2) L≤η} R
        (∀ r∈W,∀ n : IntVec,quadratic Q (dualInverse Q r-castVec n)=dualNearest Q r →
            n∈Finset.univ.image sites3) ∧
        (∀ r∈W,∀ n : IntVec,r+dualMap Q (castVec n)∈W → n=0) := by
  have hQ := boundary3_posDef z hz hp
  apply windows_nearest_sites (fun Q => windowPoint3 Q lower3)
    (windowPoint3_joint_continuous (by unfold lower3 min3; fun_prop))
    (gap3 (2*z 1) (2*z 2)) (gap3_continuous _ _) (gap3_nonneg _ _)
    (gap3_sublevel_compact _ _ 1 (mul_nonneg (by norm_num) (hz 1)) (mul_nonneg (by norm_num) (hz 2)) (by norm_num))
    (boundary3Form z) hQ (dualSquareFace (boundary3Form z) 2 3)
    (dualSquareFace_compact hQ 2 3) (fun _ h => h.1) (Finset.univ.image sites3)
  · intro r hr n hn
    rw [boundary3_dual_face z hz] at hr
    obtain ⟨L,hL,rfl⟩ := hr
    obtain ⟨i,hi⟩ := boundary3_zero_cost_sites z hz hp L hL n hn
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi.symm⟩
  · exact boundary3_translate_injective z hz hp
  · intro L hL
    have hb := (gap3_le_iff (2*z 1) (2*z 2) 0 (mul_nonneg (by norm_num) (hz 1)) (mul_nonneg (by norm_num) (hz 2)) (le_refl 0) L).mp hL.le
    rcases hb with ⟨h0,h1,h2,h3,_,_⟩
    have hrect : L∈rectangle3 (z 1) (z 2) := by
      constructor <;> intro i <;> fin_cases i <;>
        simp only [Fin.reduceFinMk,Matrix.cons_val] <;> linarith
    have hU : lower3 L=0 := by
      have hlow : lower3 L≤0 := min_le_left _ _
      have hupp : upper3 (2*z 1) (2*z 2) L≤0 := min_le_left _ _
      change -lower3 L-upper3 (2*z 1) (2*z 2) L=0 at hL
      linarith
    have he : windowPoint3 (boundary3Form z) lower3 (L,(0,0))=boundary3Point z L := by
      ext i; fin_cases i <;>
        simp only [windowPoint3,inverseCoordinates3,fiberCoordinates,boundary3Point,
          Fin.reduceFinMk,Matrix.cons_val,hU] <;> ring
    rw [he]
    exact ⟨boundary3_point_support z hz L hrect,rfl,rfl⟩

theorem boundary3_rectangleWindow_sites (z : Parameters) (hz : ∀ i,0≤z i)
    (hp : ∀ i : Fin 10,i≠9 → 0<z i) :
    ∃ η R ε : ℝ,0<η ∧ 0<R ∧ η<R/4 ∧ 0<ε ∧
      ∀ Q : Gram,Q.PosDef → ‖Q-boundary3Form z‖<ε →
        let W := localWindow3 Q lower3 (localRectangle3 (2*z 1) (2*z 2) η η) R
        (∀ r∈W,∀ n : IntVec,quadratic Q (dualInverse Q r-castVec n)=dualNearest Q r →
            n∈Finset.univ.image sites3) ∧
        (∀ r∈W,∀ n : IntVec,r+dualMap Q (castVec n)∈W → n=0) := by
  obtain ⟨η,R,ε,hη,hR,hηR,hε,h⟩ := boundary3_localWindow_sites z hz hp
  refine ⟨η/2,R,ε,by positivity,hR,by linarith,hε,?_⟩
  intro Q hQ hclose
  obtain ⟨hcomplete,hembed⟩ := h Q hQ hclose
  have hK : localRectangle3 (2*z 1) (2*z 2) (η/2) (η/2) ⊆
      {L | gap3 (2*z 1) (2*z 2) L≤η} := by
    intro L hL
    have hg := gap3_on_localRectangle (2*z 1) (2*z 2) (η/2) 0
      (by positivity) (by linarith) L hL
    simpa only [sub_zero,add_zero,show 2*(η/2)=η by ring] using hg
  have hW : localWindow3 Q lower3 (localRectangle3 (2*z 1) (2*z 2) (η/2) (η/2)) R ⊆
      localWindow3 Q lower3 {L | gap3 (2*z 1) (2*z 2) L≤η} R := by
    apply Set.image_mono
    intro p hp
    exact ⟨hK hp.1,hp.2⟩
  exact ⟨fun r hr n hn => hcomplete r (hW hr) n hn,
    fun r hr n hn => hembed r (hW hr) n (hW hn)⟩

end D4.C23Local
