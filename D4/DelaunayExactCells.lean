import D4.DelaunayCells

import D4.DelaunayPacking

import D4.DelaunayExactC1B0

import D4.DelaunayExactC1B1

import D4.DelaunayExactC1B2

import D4.DelaunayExactC1B3

import D4.DelaunayExactC1B4

import D4.DelaunayExactC1B5

import D4.DelaunayExactC2B0

import D4.DelaunayExactC2B1

import D4.DelaunayExactC2B2

import D4.DelaunayExactC2B3

import D4.DelaunayExactC2B4

import D4.DelaunayExactC2B5

import D4.DelaunayExactC3B0

import D4.DelaunayExactC3B1

import D4.DelaunayExactC3B2

import D4.DelaunayExactC3B3

import D4.DelaunayExactC3B4

import D4.DelaunayExactC3B5

noncomputable section

namespace D4.Delaunay

open Matrix Analytic Secondary Principal

set_option maxHeartbeats 0

theorem exact_cells1_check (s : Fin 24) (b : Fin 4 → Bool)
    (h : ∀ k, quadraticZ (generators1 k) (cubeSite (cellSigns1 s) b)=
      dotProduct (cubeSite (cellSigns1 s) b) ((principalNormals s) k)) :
    ∃ j : Fin 5, cubeSite (cellSigns1 s) b=cells1 s j := by
  have hindices : List.finRange 24 = [0, 1, 2, 3] ++ [4, 5, 6, 7] ++ [8, 9, 10, 11] ++ [12, 13, 14, 15] ++ [16, 17, 18, 19] ++ [20, 21, 22, 23] := by kernel_rfl
  have hm : s ∈ ([0, 1, 2, 3] ++ [4, 5, 6, 7] ++ [8, 9, 10, 11] ++ [12, 13, 14, 15] ++ [16, 17, 18, 19] ++ [20, 21, 22, 23] : List (Fin 24)) := by
    rw [← hindices]
    exact List.mem_finRange s
  simp only [List.mem_append] at hm
  rcases hm with (((((h0 | h1) | h2) | h3) | h4) | h5)
  · exact of_decide_eq_true (List.all_eq_true.mp exact_cells1_0_check s h0) b h
  · exact of_decide_eq_true (List.all_eq_true.mp exact_cells1_1_check s h1) b h
  · exact of_decide_eq_true (List.all_eq_true.mp exact_cells1_2_check s h2) b h
  · exact of_decide_eq_true (List.all_eq_true.mp exact_cells1_3_check s h3) b h
  · exact of_decide_eq_true (List.all_eq_true.mp exact_cells1_4_check s h4) b h
  · exact of_decide_eq_true (List.all_eq_true.mp exact_cells1_5_check s h5) b h

theorem cells1_exact_sites (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k)
    (s : Fin 24) (n : IntVec) :
    quadratic (principalForm w) (castVec n)=dotProduct (castVec n) (∑ k, w k • castVec ((principalNormals s) k)) ↔
      n ∈ simplexVertices (cells1 s) := by
  have hs : ∀ k, DualSupport (realMatrix (generators1 k)) (castVec ((principalNormals s) k)) := by
    apply component_support
    intro w hw
    simpa only [generatedForm1,secondaryVertex] using (cells1_supported w hw s).1
  constructor
  · intro h
    rw [← generatedForm1] at h
    have ht := (tight_sum_iff generators1 (principalNormals s) hs w hw n).mp h
    obtain ⟨j,hj⟩ := integer_tight_sites generators1 (principalNormals s) (cells1 s)
      (cellSigns1 s) principalUnitIndex (unit_generators1_check s) (exact_cells1_check s) n ht
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj.symm⟩
  · intro h
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
    exact (cells1_supported w (fun k => (hw k).le) s).2 j


def cellPlane1 (w : Fin 10 → ℝ) (s : Fin 24) : AffineSlack :=
  ⟨-(∑ k, w k • castVec ((principalNormals s) k)),0⟩

theorem cellPlane1_exact (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) (s : Fin 24) :
    ExactPlane (principalForm w) (cells1 s) (cellPlane1 w s) := by
  have he (x : Vec) : (cellPlane1 w s).eval x=dotProduct x (∑ k, w k • castVec ((principalNormals s) k)) := by
    simp [cellPlane1,AffineSlack.eval,dotProduct_comm]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro n
    rw [he]
    exact (cells1_supported w (fun k => (hw k).le) s).1 n
  · intro i
    rw [he]
    exact ((cells1_supported w (fun k => (hw k).le) s).2 i).symm
  · intro n
    rw [he,eq_comm]
    exact cells1_exact_sites w hw s n


theorem exact_cells2_check (s : Fin 24) (b : Fin 4 → Bool)
    (h : ∀ k, quadraticZ (generators2 k) (cubeSite (cellSigns2 s) b)=
      dotProduct (cubeSite (cellSigns2 s) b) ((c2VertexCoefficients (cellVertexIndex2 s)) k)) :
    ∃ j : Fin 5, cubeSite (cellSigns2 s) b=cells2 s j := by
  have hindices : List.finRange 24 = [0, 1, 2, 3] ++ [4, 5, 6, 7] ++ [8, 9, 10, 11] ++ [12, 13, 14, 15] ++ [16, 17, 18, 19] ++ [20, 21, 22, 23] := by kernel_rfl
  have hm : s ∈ ([0, 1, 2, 3] ++ [4, 5, 6, 7] ++ [8, 9, 10, 11] ++ [12, 13, 14, 15] ++ [16, 17, 18, 19] ++ [20, 21, 22, 23] : List (Fin 24)) := by
    rw [← hindices]
    exact List.mem_finRange s
  simp only [List.mem_append] at hm
  rcases hm with (((((h0 | h1) | h2) | h3) | h4) | h5)
  · exact of_decide_eq_true (List.all_eq_true.mp exact_cells2_0_check s h0) b h
  · exact of_decide_eq_true (List.all_eq_true.mp exact_cells2_1_check s h1) b h
  · exact of_decide_eq_true (List.all_eq_true.mp exact_cells2_2_check s h2) b h
  · exact of_decide_eq_true (List.all_eq_true.mp exact_cells2_3_check s h3) b h
  · exact of_decide_eq_true (List.all_eq_true.mp exact_cells2_4_check s h4) b h
  · exact of_decide_eq_true (List.all_eq_true.mp exact_cells2_5_check s h5) b h

theorem cells2_exact_sites (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k)
    (s : Fin 24) (n : IntVec) :
    quadratic (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) (castVec n)=dotProduct (castVec n) (∑ k, w k • castVec ((c2VertexCoefficients (cellVertexIndex2 s)) k)) ↔
      n ∈ simplexVertices (cells2 s) := by
  have hs : ∀ k, DualSupport (realMatrix (generators2 k)) (castVec ((c2VertexCoefficients (cellVertexIndex2 s)) k)) := by
    apply component_support
    intro w hw
    simpa only [generatedForm2,secondaryVertex] using (cells2_supported w hw s).1
  constructor
  · intro h
    rw [← generatedForm2] at h
    have ht := (tight_sum_iff generators2 (c2VertexCoefficients (cellVertexIndex2 s)) hs w hw n).mp h
    obtain ⟨j,hj⟩ := integer_tight_sites generators2 (c2VertexCoefficients (cellVertexIndex2 s)) (cells2 s)
      (cellSigns2 s) secondaryUnitIndex (unit_generators2_check s) (exact_cells2_check s) n ht
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj.symm⟩
  · intro h
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
    exact (cells2_supported w (fun k => (hw k).le) s).2 j


def cellPlane2 (w : Fin 10 → ℝ) (s : Fin 24) : AffineSlack :=
  ⟨-(∑ k, w k • castVec ((c2VertexCoefficients (cellVertexIndex2 s)) k)),0⟩

theorem cellPlane2_exact (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) (s : Fin 24) :
    ExactPlane (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) (cells2 s) (cellPlane2 w s) := by
  have he (x : Vec) : (cellPlane2 w s).eval x=dotProduct x (∑ k, w k • castVec ((c2VertexCoefficients (cellVertexIndex2 s)) k)) := by
    simp [cellPlane2,AffineSlack.eval,dotProduct_comm]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro n
    rw [he]
    exact (cells2_supported w (fun k => (hw k).le) s).1 n
  · intro i
    rw [he]
    exact ((cells2_supported w (fun k => (hw k).le) s).2 i).symm
  · intro n
    rw [he,eq_comm]
    exact cells2_exact_sites w hw s n


theorem exact_cells3_check (s : Fin 24) (b : Fin 4 → Bool)
    (h : ∀ k, quadraticZ (generators3 k) (cubeSite (cellSigns3 s) b)=
      dotProduct (cubeSite (cellSigns3 s) b) ((c3VertexCoefficients (cellVertexIndex3 s)) k)) :
    ∃ j : Fin 5, cubeSite (cellSigns3 s) b=cells3 s j := by
  have hindices : List.finRange 24 = [0, 1, 2, 3] ++ [4, 5, 6, 7] ++ [8, 9, 10, 11] ++ [12, 13, 14, 15] ++ [16, 17, 18, 19] ++ [20, 21, 22, 23] := by kernel_rfl
  have hm : s ∈ ([0, 1, 2, 3] ++ [4, 5, 6, 7] ++ [8, 9, 10, 11] ++ [12, 13, 14, 15] ++ [16, 17, 18, 19] ++ [20, 21, 22, 23] : List (Fin 24)) := by
    rw [← hindices]
    exact List.mem_finRange s
  simp only [List.mem_append] at hm
  rcases hm with (((((h0 | h1) | h2) | h3) | h4) | h5)
  · exact of_decide_eq_true (List.all_eq_true.mp exact_cells3_0_check s h0) b h
  · exact of_decide_eq_true (List.all_eq_true.mp exact_cells3_1_check s h1) b h
  · exact of_decide_eq_true (List.all_eq_true.mp exact_cells3_2_check s h2) b h
  · exact of_decide_eq_true (List.all_eq_true.mp exact_cells3_3_check s h3) b h
  · exact of_decide_eq_true (List.all_eq_true.mp exact_cells3_4_check s h4) b h
  · exact of_decide_eq_true (List.all_eq_true.mp exact_cells3_5_check s h5) b h

theorem cells3_exact_sites (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k)
    (s : Fin 24) (n : IntVec) :
    quadratic (secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) (castVec n)=dotProduct (castVec n) (∑ k, w k • castVec ((c3VertexCoefficients (cellVertexIndex3 s)) k)) ↔
      n ∈ simplexVertices (cells3 s) := by
  have hs : ∀ k, DualSupport (realMatrix (generators3 k)) (castVec ((c3VertexCoefficients (cellVertexIndex3 s)) k)) := by
    apply component_support
    intro w hw
    simpa only [generatedForm3,secondaryVertex] using (cells3_supported w hw s).1
  constructor
  · intro h
    rw [← generatedForm3] at h
    have ht := (tight_sum_iff generators3 (c3VertexCoefficients (cellVertexIndex3 s)) hs w hw n).mp h
    obtain ⟨j,hj⟩ := integer_tight_sites generators3 (c3VertexCoefficients (cellVertexIndex3 s)) (cells3 s)
      (cellSigns3 s) secondaryUnitIndex (unit_generators3_check s) (exact_cells3_check s) n ht
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj.symm⟩
  · intro h
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
    exact (cells3_supported w (fun k => (hw k).le) s).2 j


def cellPlane3 (w : Fin 10 → ℝ) (s : Fin 24) : AffineSlack :=
  ⟨-(∑ k, w k • castVec ((c3VertexCoefficients (cellVertexIndex3 s)) k)),0⟩

theorem cellPlane3_exact (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) (s : Fin 24) :
    ExactPlane (secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) (cells3 s) (cellPlane3 w s) := by
  have he (x : Vec) : (cellPlane3 w s).eval x=dotProduct x (∑ k, w k • castVec ((c3VertexCoefficients (cellVertexIndex3 s)) k)) := by
    simp [cellPlane3,AffineSlack.eval,dotProduct_comm]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro n
    rw [he]
    exact (cells3_supported w (fun k => (hw k).le) s).1 n
  · intro i
    rw [he]
    exact ((cells3_supported w (fun k => (hw k).le) s).2 i).symm
  · intro n
    rw [he,eq_comm]
    exact cells3_exact_sites w hw s n


end D4.Delaunay
