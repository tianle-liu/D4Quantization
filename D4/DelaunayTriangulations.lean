import D4.DelaunayExactCells
import D4.DelaunayTranslationChecks
import D4.DelaunayVolumes
import D4.DelaunayPeriodicPacking
import D4.PeriodicPackingCover
import D4.PrincipalSecondaryBoundary

/-! The three displayed periodic families really cover four-dimensional space,
have disjoint interiors, and consist of Delaunay simplices in their open cones. -/
noncomputable section
namespace D4.Delaunay
open Matrix Analytic Principal MeasureTheory Set
open scoped Pointwise
attribute [local instance] integerTranslation

 theorem isDelaunaySimplex_translate {Q : Gram} {S : LatticeSimplex}
    (h : IsDelaunaySimplex Q S) (n : IntVec) :
    IsDelaunaySimplex Q (translateSimplex S n) := by
  obtain ⟨x,ρ,hv,hn⟩ := h
  refine ⟨x+castVec n,ρ,?_,?_⟩
  · intro i
    have he : x+castVec n-castVec (S i+n)=x-castVec (S i) := by rw [castVec_add]; abel
    simpa only [translateSimplex,he] using hv i
  · intro z
    have he : x+castVec n-castVec z=x-castVec (z-n) := by
      ext i
      simp only [Pi.add_apply,Pi.sub_apply,castVec,Int.cast_sub]
      ring
    rw [he]
    exact hn (z-n)

 theorem interiors_disjoint_of_null {S T : Set Vec} (h : volume (S ∩ T)=0) :
    Disjoint (interior S) (interior T) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hp : 0 < volume (interior S ∩ interior T) :=
    (isOpen_interior.inter isOpen_interior).measure_pos volume ⟨x,hx,hy⟩
  have hz : volume (interior S ∩ interior T)=0 :=
    measure_mono_null (inter_subset_inter interior_subset interior_subset) h
  rw [hz] at hp
  exact (lt_irrefl _ hp)

theorem cells1_periodic_packing :
    Pairwise fun p q : Fin 24 × IntVec => AEDisjoint volume
      (periodicPieces (fun s => simplexRegion (cells1 s)) p)
      (periodicPieces (fun s => simplexRegion (cells1 s)) q) :=
  exact_periodic_packing cells1 (principalForm (fun _ => 1)) (principal_isHermitian (fun _ => 1))
    (cellPlane1 (fun _ => 1)) (cellPlane1_exact _ (by intro k; norm_num))
    cells1_translation_unique

theorem cells1_cover : periodicUnion (fun s => simplexRegion (cells1 s))=univ :=
  periodic_packing_cover _ (fun s => vertexSimplex_compact _)
    cells1_periodic_packing cells1_total_volume

theorem cells1_disjoint_interiors (p q : Fin 24 × IntVec) (hpq : p≠q) :
    Disjoint (interior (periodicPieces (fun s => simplexRegion (cells1 s)) p))
      (interior (periodicPieces (fun s => simplexRegion (cells1 s)) q)) :=
  interiors_disjoint_of_null (cells1_periodic_packing hpq)

theorem cells1_all_delaunay (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k)
    (s : Fin 24) (n : IntVec) :
    IsDelaunaySimplex (principalForm w) (translateSimplex (cells1 s) n) :=
  isDelaunaySimplex_translate (cells1_delaunay w (fun k => (hw k).le) (principal_posDef_of_pos hw) s) n

theorem cells2_periodic_packing :
    Pairwise fun p q : Fin 24 × IntVec => AEDisjoint volume
      (periodicPieces (fun s => simplexRegion (cells2 s)) p)
      (periodicPieces (fun s => simplexRegion (cells2 s)) q) :=
  exact_periodic_packing cells2 (secondaryForm cone2Vectors 1 (fun _ => 1)) (secondary_isHermitian cone2Vectors 1 (fun _ => 1))
    (cellPlane2 (fun _ => 1)) (cellPlane2_exact _ (by intro k; norm_num))
    cells2_translation_unique

theorem cells2_cover : periodicUnion (fun s => simplexRegion (cells2 s))=univ :=
  periodic_packing_cover _ (fun s => vertexSimplex_compact _)
    cells2_periodic_packing cells2_total_volume

theorem cells2_disjoint_interiors (p q : Fin 24 × IntVec) (hpq : p≠q) :
    Disjoint (interior (periodicPieces (fun s => simplexRegion (cells2 s)) p))
      (interior (periodicPieces (fun s => simplexRegion (cells2 s)) q)) :=
  interiors_disjoint_of_null (cells2_periodic_packing hpq)

theorem cells2_all_delaunay (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k)
    (s : Fin 24) (n : IntVec) :
    IsDelaunaySimplex (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) (translateSimplex (cells2 s) n) :=
  isDelaunaySimplex_translate (cells2_delaunay w (fun k => (hw k).le) (secondary_posDef_of_pos cone2Vectors (hw 0) (fun j => (hw j.succ).le)) s) n

theorem cells3_periodic_packing :
    Pairwise fun p q : Fin 24 × IntVec => AEDisjoint volume
      (periodicPieces (fun s => simplexRegion (cells3 s)) p)
      (periodicPieces (fun s => simplexRegion (cells3 s)) q) :=
  exact_periodic_packing cells3 (secondaryForm cone3Vectors 1 (fun _ => 1)) (secondary_isHermitian cone3Vectors 1 (fun _ => 1))
    (cellPlane3 (fun _ => 1)) (cellPlane3_exact _ (by intro k; norm_num))
    cells3_translation_unique

theorem cells3_cover : periodicUnion (fun s => simplexRegion (cells3 s))=univ :=
  periodic_packing_cover _ (fun s => vertexSimplex_compact _)
    cells3_periodic_packing cells3_total_volume

theorem cells3_disjoint_interiors (p q : Fin 24 × IntVec) (hpq : p≠q) :
    Disjoint (interior (periodicPieces (fun s => simplexRegion (cells3 s)) p))
      (interior (periodicPieces (fun s => simplexRegion (cells3 s)) q)) :=
  interiors_disjoint_of_null (cells3_periodic_packing hpq)

theorem cells3_all_delaunay (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k)
    (s : Fin 24) (n : IntVec) :
    IsDelaunaySimplex (secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) (translateSimplex (cells3 s) n) :=
  isDelaunaySimplex_translate (cells3_delaunay w (fun k => (hw k).le) (secondary_posDef_of_pos cone3Vectors (hw 0) (fun j => (hw j.succ).le)) s) n

end D4.Delaunay
