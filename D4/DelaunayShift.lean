import D4.DelaunayPacking

noncomputable section
namespace D4.Delaunay
open Matrix Analytic Principal MeasureTheory Set

def translateSimplex (S : LatticeSimplex) (n : IntVec) : LatticeSimplex := fun i => S i+n

def translatePlane (Q : Gram) (p : AffineSlack) (n : IntVec) : AffineSlack :=
  ⟨p.normal-(2:ℝ) • (Q *ᵥ castVec n),
    p.offset+dotProduct p.normal (castVec n)-quadratic Q (castVec n)⟩

theorem castVec_add (m n : IntVec) : castVec (m+n)=castVec m+castVec n := by
  ext i
  simp [castVec]

theorem translatePlane_eval {Q : Gram} (hQ : Q.IsHermitian)
    (p : AffineSlack) (n m : IntVec) :
    (translatePlane Q p n).eval (castVec (m+n))=
      p.eval (castVec m)+quadratic Q (castVec (m+n))-quadratic Q (castVec m) := by
  rw [castVec_add,quadratic_add_vec hQ]
  simp only [translatePlane, AffineSlack.eval, sub_dotProduct, smul_dotProduct,
    dotProduct_add, smul_eq_mul]
  rw [dotProduct_comm (Q *ᵥ castVec n) (castVec m),
    dotProduct_comm (Q *ᵥ castVec n) (castVec n)]
  unfold quadratic
  ring

theorem translatePlane_supported {Q : Gram} (hQ : Q.IsHermitian)
    {S : LatticeSimplex} {p : AffineSlack} (hp : SupportsPlane Q S p) (n : IntVec) :
    SupportsPlane Q (translateSimplex S n) (translatePlane Q p n) := by
  constructor
  · intro z
    have he : (z-n)+n=z := sub_add_cancel z n
    have h := translatePlane_eval hQ p n (z-n)
    rw [he] at h
    rw [h]
    linarith [hp.1 (z-n)]
  · intro i
    change (translatePlane Q p n).eval (castVec (S i+n))=quadratic Q (castVec (S i+n))
    rw [translatePlane_eval hQ,hp.2 i]
    ring

theorem translatePlane_exact {Q : Gram} (hQ : Q.IsHermitian)
    {S : LatticeSimplex} {p : AffineSlack} (hp : ExactPlane Q S p) (n : IntVec) :
    ExactPlane Q (translateSimplex S n) (translatePlane Q p n) := by
  refine ⟨translatePlane_supported hQ hp.1 n,?_⟩
  intro z
  have he : (z-n)+n=z := sub_add_cancel z n
  have h := translatePlane_eval hQ p n (z-n)
  rw [he] at h
  have hf : (translatePlane Q p n).eval (castVec z)=quadratic Q (castVec z) ↔
      p.eval (castVec (z-n))=quadratic Q (castVec (z-n)) := by rw [h]; constructor <;> intro h <;> linarith
  rw [hf,hp.2]
  simp only [simplexVertices,Finset.mem_image,Finset.mem_univ,true_and,translateSimplex]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i,by rw [hi,sub_add_cancel]⟩
  · rintro ⟨i,hi⟩
    exact ⟨i,by rw [← hi,add_sub_cancel_right]⟩

theorem simplexRegion_translate (S : LatticeSimplex) (n : IntVec) :
    simplexRegion (translateSimplex S n)=(fun x => x+castVec n) '' simplexRegion S := by
  ext x
  simp only [simplexRegion, vertexSimplex, affineSimplex, Set.mem_image,translateSimplex]
  constructor
  · rintro ⟨t,ht,rfl⟩
    refine ⟨castVec (S 0)+simplexMatrix (fun i => castVec (S i))*ᵥt,⟨t,ht,rfl⟩,?_⟩
    simp only [castVec_add]
    have hm : simplexMatrix (fun i => castVec (S i)+castVec n)=
        simplexMatrix (fun i => castVec (S i)) := by ext i j; simp [simplexMatrix]
    rw [hm]
    abel
  · rintro ⟨y,⟨t,ht,rfl⟩,rfl⟩
    refine ⟨t,ht,?_⟩
    simp only [castVec_add]
    have hm : simplexMatrix (fun i => castVec (S i)+castVec n)=
        simplexMatrix (fun i => castVec (S i)) := by ext i j; simp [simplexMatrix]
    rw [hm]
    abel

end D4.Delaunay
