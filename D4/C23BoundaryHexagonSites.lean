import D4.C23BoundaryHexagon

/-! The complete nearest-site list over the first closed dual face and the
pointwise bound of six sites, including vertices and edges of that face. -/
noncomputable section
namespace D4.C23Local
open Matrix Set Analytic Principal AreaEnvelope

def linkCosts2 (p q r : ℝ) (L : Plane) : Fin 6 → ℝ :=
  ![L 0,L 1,L 0+L 1-2*r,2*(p+r)-L 0,2*(q+r)-L 1,
    2*(p+q+r)-L 0-L 1]

def links2 : Fin 6 → IntVec := ![sites2 4,sites2 5,sites2 6,sites2 7,sites2 8,sites2 9]
def square2 : Fin 4 → IntVec := ![sites2 0,sites2 1,sites2 2,sites2 3]

theorem boundary2_link_cost (z : Parameters) (L : Plane) (i : Fin 6) :
    siteCost (boundary2Form z) (boundary2Point z L) (links2 i) = linkCosts2 (z 3) (z 4) (z 9) L i := by
  fin_cases i <;> simp only [links2,Fin.reduceFinMk,Matrix.cons_val,boundary2_point_costs,linkCosts2]

theorem three_link_costs_not_zero (p q r : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) (L : Plane) (i j k : Fin 6)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : linkCosts2 p q r L i=0) (hj : linkCosts2 p q r L j=0) (hk : linkCosts2 p q r L k=0) : False := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at hij hik hjk
  all_goals simp only [linkCosts2,Fin.reduceFinMk,Matrix.cons_val] at hi hj hk
  all_goals linarith

theorem zero_linkCosts2_card (p q r : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) (L : Plane) :
    (Finset.univ.filter (fun i => linkCosts2 p q r L i=0)).card ≤ 2 := by
  classical
  by_contra h
  obtain ⟨i,j,k,hi,hj,hk,hij,hik,hjk⟩ := Finset.two_lt_card_iff.mp (lt_of_not_ge h)
  exact three_link_costs_not_zero p q r hp hq hr L i j k hij hik hjk
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2

theorem boundary2_at_most_six (z : Parameters) (hz : ∀ i, 0 ≤ z i)
    (hp : ∀ i : Fin 10, i ≠ 0 → 0 < z i)
    (L : Plane) (hL : L ∈ hexagon2 (z 3) (z 4) (z 9)) :
    ∃ T : Finset IntVec, T.card ≤ 6 ∧
      ∀ n : IntVec, siteCost (boundary2Form z) (boundary2Point z L) n=0 → n ∈ T := by
  classical
  let C := Finset.univ.filter (fun i => linkCosts2 (z 3) (z 4) (z 9) L i=0)
  let S := Finset.univ.image square2
  let T := S ∪ C.image links2
  have hc : C.card ≤ 2 := zero_linkCosts2_card _ _ _ (hp 3 (by decide))
    (hp 4 (by decide)) (hp 9 (by decide)) L
  have hs : S.card ≤ 4 := by
    exact (Finset.card_image_le).trans (by simp)
  refine ⟨T,?_,?_⟩
  · have ht := Finset.card_union_le S (C.image links2)
    have hci := Finset.card_image_le (s := C) (f := links2)
    dsimp [T]
    omega
  · intro n hn
    obtain ⟨i,rfl⟩ := boundary2_zero_cost_sites z hz hp L hL n hn
    have hS (j : Fin 4) : square2 j ∈ T := Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
    have hC (j : Fin 6) (hj : siteCost (boundary2Form z) (boundary2Point z L) (links2 j)=0) : links2 j ∈ T := by
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
      rwa [boundary2_link_cost] at hj
    fin_cases i
    · exact hS 0
    · exact hS 1
    · exact hS 2
    · exact hS 3
    · exact hC 0 hn
    · exact hC 1 hn
    · exact hC 2 hn
    · exact hC 3 hn
    · exact hC 4 hn
    · exact hC 5 hn

theorem boundary2_each_site_attained (z : Parameters) (hz : ∀ i, 0 ≤ z i)
    (i : Fin 10) : ∃ L ∈ hexagon2 (z 3) (z 4) (z 9),
      siteCost (boundary2Form z) (boundary2Point z L) (sites2 i)=0 := by
  let witness : Fin 10 → Plane :=
    ![![0,2*z 9],![0,2*z 9],![0,2*z 9],![0,2*z 9],![0,2*z 9],
      ![2*z 9,0],![0,2*z 9],![2*(z 3+z 9),0],
      ![0,2*(z 4+z 9)],![2*(z 3+z 9),2*z 4]]
  refine ⟨witness i,?_,?_⟩
  · fin_cases i <;> simp only [witness,hexagon2,mem_setOf_eq,Fin.reduceFinMk,Matrix.cons_val]
    all_goals (repeat' constructor) <;> linarith only [hz 3,hz 4,hz 9]
  · rw [boundary2_point_costs]
    fin_cases i <;> simp only [witness,Fin.reduceFinMk,Matrix.cons_val] <;> ring

theorem boundary2_all_sites_exact (z : Parameters) (hz : ∀ i, 0 ≤ z i)
    (hp : ∀ i : Fin 10, i ≠ 0 → 0 < z i) (n : IntVec) :
    (∃ L ∈ hexagon2 (z 3) (z 4) (z 9),
      siteCost (boundary2Form z) (boundary2Point z L) n=0) ↔ n∈Set.range sites2 := by
  constructor
  · rintro ⟨L,hL,hn⟩
    obtain ⟨i,hi⟩ := boundary2_zero_cost_sites z hz hp L hL n hn
    exact ⟨i,hi.symm⟩
  · rintro ⟨i,rfl⟩
    exact boundary2_each_site_attained z hz i

end D4.C23Local
