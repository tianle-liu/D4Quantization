import D4.DelaunaySemantics
import Mathlib.LinearAlgebra.AffineSpace.Combination

noncomputable section
namespace D4.Delaunay
open Matrix Analytic

theorem facet_affine_interpolation (cells : Fin 24 → LatticeSimplex)
    (g : Fin 10 → IntegerGram) (p : FacetRecord) (hp : facetCheck cells g p=true)
    (L : Vec →ᵃ[ℝ] ℝ) :
    L (castVec (shiftedRight cells p p.rightFace))=
      ∑ i, (p.barycentric i:ℝ)*L (castVec (shiftedLeft cells p i)) := by
  have h := facetCheck_geometry cells g p hp
  have hs : (∑ i, (p.barycentric i:ℝ))=1 := by exact_mod_cast h.2.2.1
  have hv : (∑ i, (p.barycentric i:ℝ) • castVec (shiftedLeft cells p i))=
      castVec (shiftedRight cells p p.rightFace) := by
    ext j
    have hj := congrFun h.2.2.2.1 j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hj
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, castVec]
    exact_mod_cast hj
  have hm := Finset.map_affineCombination (s := Finset.univ)
    (fun i => castVec (shiftedLeft cells p i)) (fun i => (p.barycentric i:ℝ)) hs L
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hs,
    Finset.affineCombination_eq_linear_combination _ _ _ hs, hv] at hm
  simpa only [Function.comp_apply, smul_eq_mul] using hm

theorem liftingDifference_affine (cells : Fin 24 → LatticeSimplex)
    (g : Fin 10 → IntegerGram) (p : FacetRecord) (hp : facetCheck cells g p=true)
    (w : Fin 10 → ℝ) (L : Vec →ᵃ[ℝ] ℝ)
    (hL : ∀ i, L (castVec (shiftedLeft cells p i))=
      quadratic (generatedForm g w) (castVec (shiftedLeft cells p i))) :
    quadratic (generatedForm g w) (castVec (shiftedRight cells p p.rightFace))-
      L (castVec (shiftedRight cells p p.rightFace))=
      ∑ k, w k*(p.lifting k:ℝ) := by
  rw [facet_affine_interpolation cells g p hp L]
  simp_rw [hL]
  exact liftingDifference_eq g w cells p hp

end D4.Delaunay
