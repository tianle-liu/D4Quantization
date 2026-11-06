import D4.DelaunayShift
import D4.PeriodicPacking

noncomputable section
namespace D4.Delaunay
open Matrix Analytic Principal MeasureTheory Set
open scoped Pointwise
attribute [local instance] integerTranslation

theorem translated_simplex_vertices_unique {m : ℕ} (cells : Fin m → LatticeSimplex)
    (hunique : ∀ s t n,
      (simplexVertices (cells s)).image (fun z => z+n)=simplexVertices (cells t) →
      s=t ∧ n=0) (s t : Fin m) (n k : IntVec)
    (h : simplexVertices (translateSimplex (cells s) n)=
      simplexVertices (translateSimplex (cells t) k)) : s=t ∧ n=k := by
  classical
  have hh := congrArg (fun F : Finset IntVec => F.image (fun z => z-k)) h
  have he : (simplexVertices (cells s)).image (fun z => z+(n-k))=simplexVertices (cells t) := by
    simpa [simplexVertices,translateSimplex,Finset.image_image,Function.comp_def,add_sub_assoc] using hh
  obtain ⟨hst,hn⟩ := hunique s t (n-k) he
  exact ⟨hst,sub_eq_zero.mp hn⟩

theorem simplexRegion_periodic (S : LatticeSimplex) (n : IntVec) :
    n+ᵥsimplexRegion S=simplexRegion (translateSimplex S n) := by
  rw [simplexRegion_translate]
  ext x
  simp only [Set.mem_vadd_set,Set.mem_image]
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y,hy,by rw [integer_vadd,add_comm]⟩
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y,hy,by rw [integer_vadd,add_comm]⟩

theorem exact_periodic_packing {m : ℕ} (cells : Fin m → LatticeSimplex)
    (Q : Gram) (hQ : Q.IsHermitian) (planes : Fin m → AffineSlack)
    (hp : ∀ s, ExactPlane Q (cells s) (planes s))
    (hunique : ∀ s t n,
      (simplexVertices (cells s)).image (fun z => z+n)=simplexVertices (cells t) →
      s=t ∧ n=0) :
    Pairwise fun p q : Fin m × IntVec => AEDisjoint volume
      (periodicPieces (fun s => simplexRegion (cells s)) p)
      (periodicPieces (fun s => simplexRegion (cells s)) q) := by
  intro p q hpq
  change volume ((p.2+ᵥsimplexRegion (cells p.1)) ∩ (q.2+ᵥsimplexRegion (cells q.1)))=0
  rw [simplexRegion_periodic,simplexRegion_periodic]
  apply exact_simplex_inter_volume (translatePlane_exact hQ (hp p.1) p.2)
    (translatePlane_exact hQ (hp q.1) q.2)
  intro h
  have he := translated_simplex_vertices_unique cells hunique p.1 q.1 p.2 q.2 h
  exact hpq (Prod.ext he.1 he.2)

end D4.Delaunay
