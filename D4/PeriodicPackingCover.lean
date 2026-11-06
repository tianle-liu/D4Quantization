import D4.PeriodicPacking
import D4.IntegerEmbeddedNeighborhood

/-! Compact periodic packings of total fundamental volume have no holes.
The conclusion is pointwise coverage, not merely almost-everywhere coverage. -/
noncomputable section
namespace D4.Analytic
open Set MeasureTheory
open scoped Pointwise
attribute [local instance] integerTranslation

def periodicUnion {ι : Type*} (W : ι → Set Vec) : Set Vec :=
  ⋃ p : ι×IntVec,periodicPieces W p

theorem periodicUnion_eq_add {ι : Type*} (W : ι → Set Vec) :
    periodicUnion W=Set.range castVec+(⋃ i,W i) := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨i,n⟩,y,hy,rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨castVec n,⟨n,rfl⟩,y,Set.mem_iUnion.mpr ⟨i,hy⟩,rfl⟩
  · rintro ⟨_,⟨n,rfl⟩,y,hy,rfl⟩
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hy
    exact Set.mem_iUnion.mpr ⟨(i,n),y,hi,rfl⟩

theorem periodicUnion_closed {ι : Type*} [Finite ι]
    (W : ι → Set Vec) (hW : ∀ i,IsCompact (W i)) : IsClosed (periodicUnion W) := by
  rw [periodicUnion_eq_add]
  exact castVec_isClosedEmbedding.isClosed_range.add_right_of_isCompact (isCompact_iUnion hW)

theorem periodicUnion_translate {ι : Type*} (W : ι → Set Vec) (n : IntVec) :
    n+ᵥperiodicUnion W=periodicUnion W := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨⟨i,m⟩,z,hz,rfl⟩ := Set.mem_iUnion.mp hy
    refine Set.mem_iUnion.mpr ⟨(i,n+m),z,hz,?_⟩
    exact add_vadd n m z
  · intro hx
    obtain ⟨⟨i,m⟩,y,hy,rfl⟩ := Set.mem_iUnion.mp hx
    refine ⟨(-n+m)+ᵥy,Set.mem_iUnion.mpr ⟨(i,-n+m),y,hy,rfl⟩,?_⟩
    change n+ᵥ((-n+m)+ᵥy)=m+ᵥy
    rw [← add_vadd]
    simp

theorem periodicUnion_compl_translate {ι : Type*} (W : ι → Set Vec) (n : IntVec) :
    n+ᵥ(periodicUnion W)ᶜ=(periodicUnion W)ᶜ := by
  rw [Set.vadd_set_compl,periodicUnion_translate]

theorem periodic_packing_cover {ι : Type*} [Fintype ι]
    (W : ι → Set Vec) (hW : ∀ i,IsCompact (W i))
    (hd : Pairwise fun p q : ι×IntVec => AEDisjoint volume (periodicPieces W p) (periodicPieces W q))
    (hv : ∑ i,volume (W i)=1) : periodicUnion W=Set.univ := by
  have hclosed := periodicUnion_closed W hW
  have hvol : volume (unitCube∩periodicUnion W)=1 := by
    rw [periodicUnion,periodic_packing_volume W (fun i => (hW i).measurableSet) hd,hv]
  have hzero : volume (unitCube∩(periodicUnion W)ᶜ)=0 := by
    have he : unitCube∩(periodicUnion W)ᶜ=unitCube\(unitCube∩periodicUnion W) := by
      ext x; simp only [mem_inter_iff,mem_compl_iff,mem_diff]; tauto
    rw [he,measure_diff inter_subset_left
      ((show MeasurableSet unitCube from isCompact_Icc.measurableSet).inter hclosed.measurableSet).nullMeasurableSet
      (by rw [hvol]; exact ENNReal.one_ne_top),unitCube_volume,hvol,tsub_self]
  have hall : volume (periodicUnion W)ᶜ=0 := by
    rw [window_volume_periodization]
    simp_rw [periodicUnion_compl_translate,hzero]
    exact tsum_zero
  have he := (hclosed.isOpen_compl.measure_eq_zero_iff volume).mp hall
  apply Set.eq_univ_of_forall
  intro x
  by_contra hx
  have : x∈(periodicUnion W)ᶜ := hx
  rw [he] at this
  exact this

end D4.Analytic
