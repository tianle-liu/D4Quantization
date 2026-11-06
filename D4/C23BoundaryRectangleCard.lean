import D4.C23BoundaryRectangleSites

/-! The complete nearest-site list over the second closed dual face and the
pointwise bound of six sites, including vertices and edges of that face. -/
noncomputable section
namespace D4.C23Local
open Matrix Set Analytic Principal AreaEnvelope

def linkCosts3 (u v : ℝ) (L : Plane) : Fin 4 → ℝ :=
  ![L 0,L 1,2*u-L 0,2*v-L 1]

def links3 : Fin 4 → IntVec := ![sites3 4,sites3 5,sites3 6,sites3 7]
def square3 : Fin 4 → IntVec := ![sites3 0,sites3 1,sites3 2,sites3 3]

theorem boundary3_link_cost (z : Parameters) (L : Plane) (i : Fin 4) :
    siteCost (boundary3Form z) (boundary3Point z L) (links3 i) = linkCosts3 (z 1) (z 2) L i := by
  fin_cases i <;> simp only [links3,Fin.reduceFinMk,Matrix.cons_val,boundary3_point_costs,linkCosts3]

theorem three_rectangle_link_costs_not_zero (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (L : Plane) (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : linkCosts3 u v L i=0) (hj : linkCosts3 u v L j=0) (hk : linkCosts3 u v L k=0) : False := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at hij hik hjk
  all_goals simp only [linkCosts3,Fin.reduceFinMk,Matrix.cons_val] at hi hj hk
  all_goals linarith

theorem zero_linkCosts3_card (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (L : Plane) :
    (Finset.univ.filter (fun i => linkCosts3 u v L i=0)).card ≤ 2 := by
  classical
  by_contra h
  obtain ⟨i,j,k,hi,hj,hk,hij,hik,hjk⟩ := Finset.two_lt_card_iff.mp (lt_of_not_ge h)
  exact three_rectangle_link_costs_not_zero u v hu hv L i j k hij hik hjk
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2

theorem boundary3_at_most_six (z : Parameters) (hz : ∀ i, 0 ≤ z i)
    (hp : ∀ i : Fin 10, i ≠ 9 → 0 < z i)
    (L : Plane) (hL : L ∈ rectangle3 (z 1) (z 2)) :
    ∃ T : Finset IntVec, T.card ≤ 6 ∧
      ∀ n : IntVec, siteCost (boundary3Form z) (boundary3Point z L) n=0 → n ∈ T := by
  classical
  let C := Finset.univ.filter (fun i => linkCosts3 (z 1) (z 2) L i=0)
  let S := Finset.univ.image square3
  let T := S ∪ C.image links3
  have hc : C.card ≤ 2 := zero_linkCosts3_card _ _ (hp 1 (by decide)) (hp 2 (by decide)) L
  have hs : S.card ≤ 4 := by
    exact (Finset.card_image_le).trans (by simp)
  refine ⟨T,?_,?_⟩
  · have ht := Finset.card_union_le S (C.image links3)
    have hci := Finset.card_image_le (s := C) (f := links3)
    dsimp [T]
    omega
  · intro n hn
    obtain ⟨i,rfl⟩ := boundary3_zero_cost_sites z hz hp L hL n hn
    have hS (j : Fin 4) : square3 j ∈ T := Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
    have hC (j : Fin 4) (hj : siteCost (boundary3Form z) (boundary3Point z L) (links3 j)=0) : links3 j ∈ T := by
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
      rwa [boundary3_link_cost] at hj
    fin_cases i
    · exact hS 0
    · exact hS 1
    · exact hS 2
    · exact hS 3
    · exact hC 0 hn
    · exact hC 1 hn
    · exact hC 2 hn
    · exact hC 3 hn

theorem boundary3_each_site_attained (z : Parameters) (hz : ∀ i, 0 ≤ z i)
    (i : Fin 8) : ∃ L ∈ rectangle3 (z 1) (z 2),
      siteCost (boundary3Form z) (boundary3Point z L) (sites3 i)=0 := by
  let witness : Fin 8 → Plane :=
    ![![0,0],![0,0],![0,0],![0,0],![0,0],![0,0],![2*z 1,0],![0,2*z 2]]
  refine ⟨witness i,?_,?_⟩
  · constructor <;> intro j <;> fin_cases i <;> fin_cases j <;>
      simp only [witness,Fin.reduceFinMk,Matrix.cons_val] <;> linarith only [hz 1,hz 2]
  · rw [boundary3_point_costs]
    fin_cases i <;> simp only [witness,Fin.reduceFinMk,Matrix.cons_val] <;> ring

theorem boundary3_all_sites_exact (z : Parameters) (hz : ∀ i, 0 ≤ z i)
    (hp : ∀ i : Fin 10, i ≠ 9 → 0 < z i) (n : IntVec) :
    (∃ L ∈ rectangle3 (z 1) (z 2),
      siteCost (boundary3Form z) (boundary3Point z L) n=0) ↔ n∈Set.range sites3 := by
  constructor
  · rintro ⟨L,hL,hn⟩
    obtain ⟨i,hi⟩ := boundary3_zero_cost_sites z hz hp L hL n hn
    exact ⟨i,hi.symm⟩
  · rintro ⟨i,rfl⟩
    exact boundary3_each_site_attained z hz i

end D4.C23Local
