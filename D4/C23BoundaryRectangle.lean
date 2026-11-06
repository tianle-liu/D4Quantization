import D4.C23BoundaryRectangleData
noncomputable section
namespace D4.C23Local
open Matrix Set Analytic Principal AreaEnvelope Secondary

theorem boundary3_point_representation (z : Parameters) (L : Plane) :
    boundary3Point z L = z 0 • (![-2,-2,2,2] : Vec)+generatorMap (boundary3Coefficients z L) := by
  have hcoords := generatorMap_coordinates (boundary3Coefficients z L)
  refine Eq.trans ?_ (congrArg (fun v : Vec => z 0 • (![-2,-2,2,2] : Vec)+v) hcoords.symm)
  unfold boundary3Point
  rw [boundary3_matrix]
  ext i; fin_cases i <;>
    simp only [boundary3Coefficients,Fin.reduceFinMk,Matrix.cons_val,Matrix.of_apply,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul] <;> ring

theorem boundary3_weights_nonneg (z : Parameters) (hz : ∀ i, 0 ≤ z i) :
    ∀ e, 0 ≤ boundary3Weights z e := by
  intro e
  fin_cases e
  · exact hz 1
  · exact hz 2
  · exact hz 3
  · exact hz 4
  · exact le_refl 0
  · exact hz 5
  · exact hz 6
  · exact hz 7
  · exact hz 8
  · exact le_refl 0

theorem boundary3_coefficients_mem (z : Parameters) (hz : ∀ i, 0 ≤ z i)
    (L : Plane) (hL : L ∈ rectangle3 (z 1) (z 2)) :
    boundary3Coefficients z L ∈ Icc (-(boundary3Weights z)) (boundary3Weights z) := by
  have h0 := hL.1 0
  have h1 := hL.2 0
  have h2 := hL.1 1
  have h3 := hL.2 1
  simp only [rectangle3,Matrix.cons_val] at h0 h1 h2 h3
  constructor <;> intro e <;> fin_cases e <;>
    simp only [boundary3Coefficients,boundary3Weights,Pi.neg_apply,Fin.reduceFinMk,Matrix.cons_val] <;>
    linarith [hz 1,hz 2,hz 3,hz 4,hz 5,hz 6,hz 7,hz 8]

theorem boundary3_A_support : (![-2,-2,2,2] : Vec) ∈ dualRegion (gramMatrix ℝ) := by
  have h := d4_vertex_support 2
  have he : castVec (d4DualVertex 2)=(![-2,-2,2,2] : Vec) := by
    ext i; fin_cases i <;> norm_num [castVec,d4DualVertex] <;>
      (try simp only [Matrix.cons_val,Fin.reduceFinMk]) <;> norm_num
  rw [he] at h
  exact h

theorem siteCost_sum (Q P : Gram) (r s : Vec) (a : ℝ) (n : IntVec) :
    siteCost (a • Q+P) (a • r+s) n = a*siteCost Q r n+siteCost P s n := by
  simp only [siteCost,quadratic,Matrix.add_mulVec,Matrix.smul_mulVec_assoc,
    dotProduct_add,dotProduct_smul,smul_eq_mul]
  ring

theorem boundary3_point_support (z : Parameters) (hz : ∀ i, 0 ≤ z i)
    (L : Plane) (hL : L ∈ rectangle3 (z 1) (z 2)) :
    boundary3Point z L ∈ dualRegion (boundary3Form z) := by
  intro n
  have hA : 0 ≤ siteCost (gramMatrix ℝ) (![-2,-2,2,2] : Vec) n :=
    sub_nonneg.mpr (boundary3_A_support n)
  have hP : 0 ≤ siteCost (principalForm (boundary3Weights z))
      (generatorMap (boundary3Coefficients z L)) n := sub_nonneg.mpr
    (zonotope_integer_support (boundary3_weights_nonneg z hz)
      ⟨boundary3Coefficients z L,boundary3_coefficients_mem z hz L hL,rfl⟩ n)
  have hcost : 0 ≤ siteCost (boundary3Form z) (boundary3Point z L) n := by
    rw [boundary3_point_representation,boundary3Form,siteCost_sum]
    exact add_nonneg (mul_nonneg (hz 0) hA) hP
  exact sub_nonneg.mp hcost

theorem boundary3_coordinates (z : Parameters) (L : Plane) :
    coordinates3 (boundary3Form z) (boundary3Point z L)=(![0,0,L 0,L 1] : Vec) := by
  ext i; fin_cases i <;>
    simp only [coordinates3,boundary3Point,Fin.reduceFinMk,Matrix.cons_val] <;> ring

theorem boundary3_point_costs (z : Parameters) (L : Plane) (i : Fin 8) :
    siteCost (boundary3Form z) (boundary3Point z L) (sites3 i) =
      (![0,0,0,0,L 0,L 1,2*z 1-L 0,2*z 2-L 1] : Fin 8 → ℝ) i := by
  rw [boundary3_form,siteCosts3]
  unfold costValues3
  rw [← boundary3_form,boundary3_coordinates,boundary3_matrix]
  fin_cases i <;>
    simp only [Fin.reduceFinMk,Matrix.cons_val,Matrix.of_apply] <;> ring

theorem boundary3_support_iff_rectangle (z : Parameters) (hz : ∀ i, 0 ≤ z i) (L : Plane) :
    boundary3Point z L ∈ dualRegion (boundary3Form z) ↔ L ∈ rectangle3 (z 1) (z 2) := by
  refine ⟨?_,boundary3_point_support z hz L⟩
  intro h
  have hc (i : Fin 8) : 0 ≤ siteCost (boundary3Form z) (boundary3Point z L) (sites3 i) :=
    sub_nonneg.mpr (h (sites3 i))
  simp_rw [boundary3_point_costs] at hc
  have h4 := hc 4
  have h5 := hc 5
  have h6 := hc 6
  have h7 := hc 7
  simp only [Matrix.cons_val] at h4 h5 h6 h7
  constructor <;> intro i <;> fin_cases i <;>
    simp only [Fin.reduceFinMk,Matrix.cons_val] <;> linarith

theorem boundary3_dual_face (z : Parameters) (hz : ∀ i, 0 ≤ z i) :
    dualSquareFace (boundary3Form z) 2 3 = boundary3Point z '' rectangle3 (z 1) (z 2) := by
  ext r
  constructor
  · rintro ⟨hr,h2,h3⟩
    let L : Plane := ![boundary3Form z 0 0+r 0,boundary3Form z 1 1+r 1]
    have he : boundary3Point z L=r := by
      ext i; fin_cases i <;> simp [boundary3Point,L,h2,h3]
    refine ⟨L,?_,he⟩
    apply (boundary3_support_iff_rectangle z hz L).mp
    rwa [he]
  · rintro ⟨L,hL,rfl⟩
    exact ⟨boundary3_point_support z hz L hL,by simp [boundary3Point],by simp [boundary3Point]⟩

end D4.C23Local
