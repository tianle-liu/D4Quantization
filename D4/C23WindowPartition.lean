import D4.C23WindowMeasure
import D4.C23LocalPartitionNullC3

noncomputable section
namespace D4.C23Local
open Matrix MeasureTheory Set Analytic AreaEnvelope

theorem referenceWindow_inter_null (K L : Set Plane) (R : ℝ)
    (h : volume (K∩L)=0) : volume (referenceWindow K R∩referenceWindow L R)=0 := by
  have he : referenceWindow K R∩referenceWindow L R =
      (K∩L) ×ˢ (Icc (-R) R ×ˢ Icc (-R) R) := by
    ext x; simp [referenceWindow]; tauto
  rw [he,Measure.volume_eq_prod,Measure.prod_prod,h,zero_mul]

theorem localWindow3_integral_partition {ι : Type*} [Fintype ι]
    (Q : Gram) (U : Plane→ℝ) (hU : Continuous U)
    (K : Set Plane) (hK : IsCompact K) (Ks : ι→Set Plane)
    (hKs : ∀i,IsCompact (Ks i)) (hc : (⋃i,Ks i)=K)
    (hn : Pairwise fun i j=>volume (Ks i∩Ks j)=0) (R : ℝ)
    (f : Vec→ℝ) (hf : Continuous f) :
    (∫r in localWindow3 Q U K R,f r)=∑i,∫r in localWindow3 Q U (Ks i) R,f r := by
  simp_rw [localWindow3_integral Q U hU]
  have hc' : (⋃i,referenceWindow (Ks i) R)=referenceWindow K R := by
    ext x; simp only [Set.mem_iUnion,referenceWindow,Set.mem_prod]
    rw [←hc]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi,hs⟩; exact ⟨⟨i,hi⟩,hs⟩
    · rintro ⟨⟨i,hi⟩,hs⟩; exact ⟨i,hi,hs⟩
  rw [←hc',integral_iUnion_ae,tsum_fintype]
  · intro i
    exact ((hKs i).prod (isCompact_Icc.prod isCompact_Icc)).measurableSet.nullMeasurableSet
  · intro i j hij; exact referenceWindow_inter_null _ _ R (hn hij)
  · rw [hc']
    exact (hf.comp (windowPoint3_continuous Q hU)).continuousOn.integrableOn_compact
      (hK.prod (isCompact_Icc.prod isCompact_Icc))

def quadrantLo (η : ℝ) (i : Fin 2×Fin 2) : Plane :=
  ![if i.1=0 then -η else 0,if i.2=0 then -η else 0]

def quadrantHi (α β η : ℝ) (i : Fin 2×Fin 2) : Plane :=
  ![if i.1=0 then 0 else α+η,if i.2=0 then 0 else β+η]

def quadrant (α β η : ℝ) (i : Fin 2×Fin 2) : Set Plane :=
  Icc (quadrantLo η i) (quadrantHi α β η i)

theorem quadrant_cover (α β η : ℝ) (hα : 0≤α) (hβ : 0≤β) (hη : 0≤η) :
    (⋃i,quadrant α β η i)=localRectangle3 α β η η := by
  ext L
  simp only [Set.mem_iUnion,quadrant,Set.mem_Icc,localRectangle3]
  constructor
  · rintro ⟨⟨i,j⟩,hl,hh⟩
    have a:=hl 0; have b:=hl 1; have c:=hh 0; have d:=hh 1
    constructor <;> intro k <;> fin_cases k <;>
      fin_cases i <;> fin_cases j <;>
      simp [quadrantLo,quadrantHi] at a b c d ⊢ <;> linarith
  · intro h
    by_cases h0 : L 0≤0 <;> by_cases h1 : L 1≤0
    · refine ⟨(0,0),?_,?_⟩ <;> intro k <;> fin_cases k <;>
        simp [quadrantLo,quadrantHi] <;> first | exact h0 | exact h1 | exact h.1 0 | exact h.1 1
    · refine ⟨(0,1),?_,?_⟩ <;> intro k <;> fin_cases k <;>
        simp [quadrantLo,quadrantHi] <;> first | exact h0 | exact (le_of_not_ge h1) | exact h.1 0 | exact h.2 1
    · refine ⟨(1,0),?_,?_⟩ <;> intro k <;> fin_cases k <;>
        simp [quadrantLo,quadrantHi] <;> first | exact h1 | exact (le_of_not_ge h0) | exact h.1 1 | exact h.2 0
    · refine ⟨(1,1),?_,?_⟩ <;> intro k <;> fin_cases k <;>
        simp [quadrantLo,quadrantHi] <;> first | exact (le_of_not_ge h0) | exact (le_of_not_ge h1) | exact h.2 0 | exact h.2 1

theorem plane_coordinate_zero_null (k : Fin 2) : volume {L : Plane | L k=0}=0 := by
  have h := affineEquality_volume (a:=![0,if k=0 then 1 else 0,if k=1 then 1 else 0])
    (b:=![0,0,0]) (by
      fin_cases k
      · left; change (1:ℝ)≠0; norm_num
      · right; change (1:ℝ)≠0; norm_num)
  convert h using 2
  ext L
  fin_cases k <;> simp [affineEval_eq]

theorem quadrant_pairwise_null (α β η : ℝ) :
    Pairwise fun i j:Fin 2×Fin 2=>volume (quadrant α β η i∩quadrant α β η j)=0 := by
  rintro ⟨i₀,i₁⟩ ⟨j₀,j₁⟩ hij
  have hi : i₀≠j₀ ∨ i₁≠j₁ := by contrapose! hij; exact Prod.ext hij.1 hij.2
  rcases hi with hi|hi
  · apply measure_mono_null (t:={L:Plane|L 0=0}) ?_ (plane_coordinate_zero_null 0)
    intro L h
    have h1:=h.1; have h2:=h.2
    fin_cases i₀ <;> fin_cases j₀ <;> simp at hi
    all_goals
      change L 0=0
      change _≤L ∧ L≤_ at h1 h2
      have a:=h1.1 0; have b:=h1.2 0; have c:=h2.1 0; have d:=h2.2 0
      simp [quadrantLo,quadrantHi] at a b c d
      linarith
  · apply measure_mono_null (t:={L:Plane|L 1=0}) ?_ (plane_coordinate_zero_null 1)
    intro L h
    have h1:=h.1; have h2:=h.2
    fin_cases i₁ <;> fin_cases j₁ <;> simp at hi
    all_goals
      change L 1=0
      change _≤L ∧ L≤_ at h1 h2
      have a:=h1.1 1; have b:=h1.2 1; have c:=h2.1 1; have d:=h2.2 1
      simp [quadrantLo,quadrantHi] at a b c d
      linarith

end D4.C23Local
