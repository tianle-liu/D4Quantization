import D4.SecondaryDomainsType
import D4.DualPeriodMoment

/-! Supporting planes are exactly empty spheres with the full set of lattice sites. -/
noncomputable section
namespace D4.Delaunay
open Analytic Principal Matrix MeasureTheory Set

theorem delaunayType_iff_empty_sphere {Q : Gram} (hQ : Q.PosDef)
    (F : Finset IntVec) :
    F ∈ delaunayType Q ↔
      (∃ x : Vec, ∃ ρ : ℝ,
        (∀ n : IntVec, ρ ≤ quadratic Q (x-castVec n)) ∧
        (∀ n : IntVec, quadratic Q (x-castVec n)=ρ ↔ n∈F)) ∧
      volume (latticeHull F) ≠ 0 := by
  constructor
  · rintro ⟨⟨p,hp⟩,hv⟩
    let x := dualInverse Q (-p.normal)
    have he (n : IntVec) : quadratic Q (x-castVec n) =
        quadratic Q x+quadratic Q (castVec n)+dotProduct p.normal (castVec n) := by
      rw [quadratic_eq_dualSiteCost hQ.1]
      change quadratic Q x+dualSiteCost Q (dualMap Q (dualInverse Q (-p.normal))) n = _
      rw [dualMap_dualInverse hQ]
      simp only [dualSiteCost,dotProduct_neg,sub_neg_eq_add,dotProduct_comm]
      ring
    refine ⟨⟨x,quadratic Q x+p.offset,?_,?_⟩,hv⟩
    · intro n
      have hl := hp.1 n
      rw [AffineSlack.eval] at hl
      rw [he]
      linarith
    · intro n
      rw [he]
      constructor
      · intro hn
        apply (hp.2 n).mp
        rw [AffineSlack.eval]
        linarith
      · intro hn
        have ht := (hp.2 n).mpr hn
        rw [AffineSlack.eval] at ht
        linarith
  · rintro ⟨⟨x,ρ,hl,ht⟩,hv⟩
    let p : AffineSlack := ⟨-dualMap Q x,ρ-quadratic Q x⟩
    have he (n : IntVec) : p.eval (castVec n) =
        ρ-quadratic Q x+dotProduct (castVec n) (dualMap Q x) := by
      simp only [p,AffineSlack.eval,neg_dotProduct,dotProduct_neg,sub_neg_eq_add,dotProduct_comm]
    refine ⟨⟨p,?_,?_⟩,hv⟩
    · intro n
      have hh := hl n
      rw [quadratic_eq_dualSiteCost hQ.1,dualSiteCost] at hh
      rw [he]
      linarith
    · intro n
      rw [he]
      constructor
      · intro hn
        apply (ht n).mp
        rw [quadratic_eq_dualSiteCost hQ.1,dualSiteCost]
        linarith
      · intro hn
        have hh := (ht n).mpr hn
        rw [quadratic_eq_dualSiteCost hQ.1,dualSiteCost] at hh
        linarith

theorem latticeHull_nonzero_volume_nonempty {F : Finset IntVec}
    (hv : volume (latticeHull F) ≠ 0) : F.Nonempty := by
  by_contra h
  have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp h
  simp [he,latticeHull] at hv

theorem empty_sphere_radius_nonneg {Q : Gram} (hQ : Q.PosDef)
    {F : Finset IntVec} {x : Vec} {ρ : ℝ}
    (ht : ∀ n : IntVec, quadratic Q (x-castVec n)=ρ ↔ n∈F)
    (hv : volume (latticeHull F) ≠ 0) : 0 ≤ ρ := by
  obtain ⟨n,hn⟩ := latticeHull_nonzero_volume_nonempty hv
  rw [← (ht n).mpr hn]
  simpa only [quadratic,star_trivial] using hQ.posSemidef.2 (x-castVec n)

theorem finite_sphere_sites {Q : Gram} (hQ : Q.PosDef) (x : Vec) (ρ : ℝ) :
    {n : IntVec | quadratic Q (x-castVec n)=ρ}.Finite := by
  apply (finite_nearest_sublevel hQ x ρ).subset
  intro n hn
  exact hn.le

end D4.Delaunay
