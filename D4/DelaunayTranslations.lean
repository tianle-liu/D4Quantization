import D4.DelaunayDefs

namespace D4.Delaunay
open Matrix Analytic

def height (v : IntVec) : ℤ := 1000*v 0+100*v 1+10*v 2+v 3

def simplexVertices (S : LatticeSimplex) : Finset IntVec := Finset.univ.image S

theorem height_add (x y : IntVec) : height (x+y)=height x+height y := by
  simp only [height,Pi.add_apply]
  ring

theorem height_zero : height (0 : IntVec)=0 := by simp [height]

theorem no_translation_repetitions {m : ℕ} (cells : Fin m → LatticeSimplex)
    (h0 : ∀ s, cells s 0=0)
    (hh : ∀ s i, 0 ≤ height (cells s i) ∧ (height (cells s i)=0 → cells s i=0))
    (hd : Function.Injective (fun s => simplexVertices (cells s)))
    (s t : Fin m) (n : IntVec)
    (he : (simplexVertices (cells s)).image (fun z => z+n)=simplexVertices (cells t)) :
    s=t ∧ n=0 := by
  classical
  have hn : n ∈ simplexVertices (cells t) := by
    rw [← he]
    exact Finset.mem_image.mpr ⟨0,Finset.mem_image.mpr ⟨0,Finset.mem_univ _,h0 s⟩,zero_add n⟩
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hn
  have hnpos : 0 ≤ height n := hj ▸ (hh t j).1
  have hz : (0 : IntVec) ∈ (simplexVertices (cells s)).image (fun z => z+n) := by
    rw [he]
    exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,h0 t⟩
  obtain ⟨z,hz,hzn⟩ := Finset.mem_image.mp hz
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hz
  have hsum : height z+height n=0 := by rw [← height_add,hzn,height_zero]
  have hzz : 0 ≤ height z := hi ▸ (hh s i).1
  have hnzero : height n=0 := by omega
  have hn0 : n=0 := by
    rw [← hj]
    exact (hh t j).2 (hj ▸ hnzero)
  refine ⟨hd ?_,hn0⟩
  simpa [hn0] using he

end D4.Delaunay
