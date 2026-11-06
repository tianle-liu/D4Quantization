import D4.PeriodicLocalization
import D4.IntegerEmbeddedNeighborhood

/-! A compact dual face that embeds at one positive-definite form has a
single embedded neighborhood for all sufficiently nearby forms. -/
noncomputable section
namespace D4.Analytic
open Set Matrix Metric
attribute [local instance] Matrix.normedAddCommGroup

def dualHomeomorph (Q : Gram) (hQ : Q.PosDef) : Vec ≃ₜ Vec :=
  (Euclidean.coordinateEquiv ((2:ℝ) • Q) (dualMatrix_det_ne_zero hQ)).toContinuousLinearEquiv.toHomeomorph

theorem norm_dualMap_le (R : Gram) (x : Vec) : ‖dualMap R x‖≤8*‖R‖*‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  unfold dualMap
  rw [Matrix.smul_mulVec_assoc]
  change |2*dotProduct (R i) x|≤_
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have h := abs_dotProduct_le_sup (R i) x
  have hi := norm_le_pi_norm R i
  nlinarith [norm_nonneg x]

theorem dualMap_sub_matrix (R Q : Gram) (x : Vec) :
    dualMap R x-dualMap Q x=dualMap (R-Q) x := by
  simp only [dualMap,smul_sub,Matrix.sub_mulVec]

theorem compact_dual_embedded_neighborhood {Q : Gram} (hQ : Q.PosDef)
    (F : Set Vec) (hF : IsCompact F)
    (hinj : ∀ x∈F,∀ n : IntVec,x+dualMap Q (castVec n)∈F → n=0) :
    ∃ ε : ℝ,0<ε ∧ ∃ U : Set Vec,IsOpen U ∧ F⊆U ∧
      ∀ R : Gram,‖R-Q‖<ε → ∀ x∈U,∀ n : IntVec,
        x+dualMap R (castVec n)∈U → n=0 := by
  classical
  let D : Set Vec := (fun p : Vec×Vec => p.2-p.1) '' (F×ˢF)
  have hD : IsCompact D := (hF.prod hF).image (by fun_prop)
  have hZ : IsClosed (dualMap Q '' (castVec '' ({0}ᶜ : Set IntVec))) :=
    (dualHomeomorph Q hQ).isClosedMap _ nonzero_integer_points_closed
  have hdis : Disjoint D (dualMap Q '' (castVec '' ({0}ᶜ : Set IntVec))) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩ ⟨_,⟨n,hn,rfl⟩,he⟩
    have hxn : x+dualMap Q (castVec n)∈F := by
      have hh : x+dualMap Q (castVec n)=y := by rw [he]; dsimp; abel
      rwa [hh]
    exact hn (by simp [hinj x hx n hxn])
  obtain ⟨r,hr,hsep⟩ := EMetric.exists_pos_forall_lt_edist hD hZ hdis
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have hdist (f g : Vec) (hf : f∈F) (hg : g∈F) (n : IntVec) (hn : n≠0) :
      (r:ℝ)<‖g-f-dualMap Q (castVec n)‖ := by
    have h := hsep (g-f) ⟨(f,g),⟨hf,hg⟩,rfl⟩
      (dualMap Q (castVec n)) ⟨castVec n,⟨n,by simpa,rfl⟩,rfl⟩
    rw [edist_dist,← ENNReal.ofReal_coe_nnreal] at h
    have hh := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (NNReal.coe_nonneg r)).mp h
    simpa only [dist_eq_norm] using hh
  obtain ⟨B,hB,hbound⟩ := hF.isBounded.subset_closedBall_lt 0 (0:Vec)
  obtain ⟨ε₀,k,hε₀,hk,hcoerce⟩ := nearby_quadratic_coercive hQ
  let ρ : ℝ := min ((r:ℝ)/8) 1
  have hρ : 0<ρ := lt_min (by positivity) zero_lt_one
  let M : ℝ := 4*(B+1)/k
  have hM : 0<M := by dsimp [M]; positivity
  let ε : ℝ := min ε₀ ((r:ℝ)/(32*M))
  have hε : 0<ε := lt_min hε₀ (by positivity)
  let U : Set Vec := ⋃ f∈F,ball f ρ
  have hU : IsOpen U := isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
  have hFU : F⊆U := fun f hf => mem_iUnion.mpr ⟨f,mem_iUnion.mpr ⟨hf,by simpa using hρ⟩⟩
  refine ⟨ε,hε,U,hU,hFU,?_⟩
  intro R hR x hx n hxn
  by_contra hn
  obtain ⟨f,hf,hxf⟩ := mem_iUnion₂.mp hx
  obtain ⟨g,hg,hxng⟩ := mem_iUnion₂.mp hxn
  have hxf' : ‖x-f‖<ρ := hxf
  have hxng' : ‖g-(x+dualMap R (castVec n))‖<ρ := by
    simpa only [mem_ball,dist_eq_norm,norm_sub_rev] using hxng
  have hfB : ‖f‖≤B := by simpa only [mem_closedBall,dist_zero_right] using hbound hf
  have hgB : ‖g‖≤B := by simpa only [mem_closedBall,dist_zero_right] using hbound hg
  have hxB : ‖x‖≤B+1 := by
    have hh := norm_add_le (x-f) f
    rw [sub_add_cancel] at hh
    have hhρ : ρ≤1 := min_le_right _ _
    linarith
  have hynB : ‖x+dualMap R (castVec n)‖≤B+1 := by
    have hh := norm_add_le (x+dualMap R (castVec n)-g) g
    rw [sub_add_cancel] at hh
    rw [norm_sub_rev] at hh
    have hhρ : ρ≤1 := min_le_right _ _
    linarith
  have hnB : ‖castVec n‖≤M := by
    have hu : ‖dualMap R (castVec n)‖≤B+1+(B+1) := by
      have he : dualMap R (castVec n)=(x+dualMap R (castVec n))-x := by abel
      rw [he]
      exact (norm_sub_le _ _).trans (add_le_add hynB hxB)
    have hh := norm_le_of_dualMap_bound R hk
      (hcoerce R (hR.trans_le (min_le_left _ _))) (castVec n) hu
    rw [abs_of_pos (by linarith : 0<B+1+(B+1))] at hh
    dsimp [M]
    convert hh using 1 <;> ring
  have hchange : ‖dualMap R (castVec n)-dualMap Q (castVec n)‖<(r:ℝ)/4 := by
    rw [dualMap_sub_matrix]
    have hd := norm_dualMap_le (R-Q) (castVec n)
    have he : ‖R-Q‖<(r:ℝ)/(32*M) := hR.trans_le (min_le_right _ _)
    have hmul := (lt_div_iff₀ (by positivity : 0<32*M)).mp he
    nlinarith [norm_nonneg (R-Q)]
  have he : g-f-dualMap Q (castVec n)=
      (g-(x+dualMap R (castVec n)))+(x-f)+
        (dualMap R (castVec n)-dualMap Q (castVec n)) := by abel
  have hb := (norm_add_le ((g-(x+dualMap R (castVec n)))+(x-f))
    (dualMap R (castVec n)-dualMap Q (castVec n))).trans
      (add_le_add_right (norm_add_le _ _) _)
  rw [← he] at hb
  have hhρ : ρ≤(r:ℝ)/8 := min_le_left _ _
  have hlow := hdist f g hf hg n hn
  linarith

end D4.Analytic
