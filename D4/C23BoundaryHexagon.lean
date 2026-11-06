import D4.C23BoundaryHexagonSupport
noncomputable section
namespace D4.C23Local
open Matrix Set Analytic Principal AreaEnvelope

theorem boundary2_coordinates (z : Parameters) (L : Plane) :
    coordinates2 (boundary2Form z) (boundary2Point z L)=(![0,0,L 0,L 1] : Vec) := by
  ext i; fin_cases i <;>
    simp only [coordinates2,boundary2Point,Fin.reduceFinMk,Matrix.cons_val] <;> ring

theorem boundary2_point_costs (z : Parameters) (L : Plane) (i : Fin 10) :
    siteCost (boundary2Form z) (boundary2Point z L) (sites2 i) =
      (![0,0,0,0,L 0,L 1,L 0+L 1-2*z 9,
        2*(z 3+z 9)-L 0,2*(z 4+z 9)-L 1,2*(z 3+z 4+z 9)-L 0-L 1] : Fin 10 → ℝ) i := by
  rw [boundary2_form,siteCosts2]
  unfold costValues2
  rw [← boundary2_form,boundary2_coordinates]
  fin_cases i <;>
    simp only [boundary2Parameters,Fin.reduceFinMk,Matrix.cons_val] <;> ring

theorem boundary2_support_iff_hexagon (z : Parameters) (hz : ∀ i, 0 ≤ z i) (L : Plane) :
    boundary2Point z L ∈ dualRegion (boundary2Form z) ↔ L ∈ hexagon2 (z 3) (z 4) (z 9) := by
  refine ⟨?_,boundary2_point_support z hz L⟩
  intro h
  have hc (i : Fin 10) : 0 ≤ siteCost (boundary2Form z) (boundary2Point z L) (sites2 i) :=
    sub_nonneg.mpr (h (sites2 i))
  simp_rw [boundary2_point_costs] at hc
  have h4 := hc 4
  have h5 := hc 5
  have h6 := hc 6
  have h7 := hc 7
  have h8 := hc 8
  have h9 := hc 9
  simp only [Fin.reduceFinMk,Matrix.cons_val] at h4 h5 h6 h7 h8 h9
  change 0 ≤ L 0 ∧ L 0 ≤ 2*(z 3+z 9) ∧ 0 ≤ L 1 ∧ L 1 ≤ 2*(z 4+z 9) ∧
    2*z 9 ≤ L 0+L 1 ∧ L 0+L 1 ≤ 2*(z 3+z 4+z 9)
  (repeat' constructor) <;> linarith

theorem boundary2_dual_face (z : Parameters) (hz : ∀ i, 0 ≤ z i) :
    dualSquareFace (boundary2Form z) 0 1 =
      boundary2Point z '' hexagon2 (z 3) (z 4) (z 9) := by
  ext r
  constructor
  · rintro ⟨hr,h0,h1⟩
    let L : Plane := ![boundary2Form z 2 2+r 2,boundary2Form z 3 3+r 3]
    have he : boundary2Point z L=r := by
      ext i; fin_cases i <;> simp [boundary2Point,L,h0,h1]
    refine ⟨L,?_,he⟩
    apply (boundary2_support_iff_hexagon z hz L).mp
    rwa [he]
  · rintro ⟨L,hL,rfl⟩
    exact ⟨boundary2_point_support z hz L hL,by simp [boundary2Point],by simp [boundary2Point]⟩

theorem boundary2_zero_cost_sites (z : Parameters) (hz : ∀ i, 0 ≤ z i)
    (hp : ∀ i : Fin 10, i ≠ 0 → 0 < z i)
    (L : Plane) (hL : L ∈ hexagon2 (z 3) (z 4) (z 9))
    (n : IntVec) (hn : siteCost (boundary2Form z) (boundary2Point z L) n=0) :
    ∃ i : Fin 10, n=sites2 i := by
  obtain ⟨t,ht,he,h0,h1,h5,h6,h7,h8⟩ := boundary2_point_representation z hz L hL
  have hn' : siteCost (principalForm (boundary2Weights z)) (generatorMap t) n=0 := by
    exact congrArg (fun r => siteCost (boundary2Form z) r n) he ▸ hn
  have hw := boundary2_weights_nonneg z hz
  have ha := tight_generator _ t hw ht n hn' 0 (hp 1 (by decide)) h0
  have hb := tight_generator _ t hw ht n hn' 1 (hp 2 (by decide)) h1
  have hc := tight_generator _ t hw ht n hn' 5 (hp 5 (by decide)) h5
  have hd := tight_generator _ t hw ht n hn' 6 (hp 6 (by decide)) h6
  have he' := tight_generator _ t hw ht n hn' 7 (hp 7 (by decide)) h7
  have hf := tight_generator _ t hw ht n hn' 8 (hp 8 (by decide)) h8
  norm_num [integerGenerators,Fin.sum_univ_succ] at ha hb hc hd he' hf
  simp only [Matrix.cons_val,Fin.reduceSucc,Fin.reduceFinMk] at ha hb hc hd he' hf
  norm_num at ha hb hc hd he' hf
  exact six_generator_sites n ha hb hc hd he' hf

end D4.C23Local
