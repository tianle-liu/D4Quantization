import D4.ConeAnalysisCoordinates
import D4.GeometricTheoremBCorollaries
import Mathlib.LinearAlgebra.Basis.Fin

/-! An actual full-rank triangular lattice and its regular-hexagon cell. -/
noncomputable section
namespace D4.Hexagonal
open Set MeasureTheory D4.FacetGeometry
open scoped InnerProductSpace
abbrev Point := WithLp 2 (ℝ × ℝ)
instance : MeasurableSpace Point := borel Point
instance : BorelSpace Point := ⟨rfl⟩

private theorem sqrt_three_pos : 0 < Real.sqrt 3 := by positivity
private theorem sqrt_three_sq : (Real.sqrt 3)^2 = 3 := by norm_num

def point (x y : ℝ) : Point := (WithLp.equiv 2 (ℝ × ℝ)).symm (x,y)
@[simp] theorem point_fst (x y : ℝ) : (point x y).fst = x := rfl
@[simp] theorem point_snd (x y : ℝ) : (point x y).snd = y := rfl

def basisEquiv : (ℝ × ℝ) ≃ₗ[ℝ] Point where
  toFun p := point (p.1+p.2/2) (Real.sqrt 3/2*p.2)
  invFun p := (p.fst-p.snd/Real.sqrt 3, 2*p.snd/Real.sqrt 3)
  left_inv p := by
    apply Prod.ext <;> dsimp [point] <;> field_simp [sqrt_three_pos.ne'] <;> ring
  right_inv p := by
    apply (WithLp.equiv 2 (ℝ × ℝ)).injective
    apply Prod.ext <;> dsimp [point] <;> field_simp [sqrt_three_pos.ne'] <;> ring
  map_add' p q := by
    apply (WithLp.equiv 2 (ℝ × ℝ)).injective
    apply Prod.ext <;> dsimp [point] <;> ring
  map_smul' r p := by
    apply (WithLp.equiv 2 (ℝ × ℝ)).injective
    apply Prod.ext <;> dsimp [point] <;> ring

def latticeBasis : Basis (Fin 2) ℝ Point := (Basis.finTwoProd ℝ).map basisEquiv

def lattice : Submodule ℤ Point := Submodule.span ℤ (Set.range latticeBasis)
instance : DiscreteTopology lattice := by unfold lattice; infer_instance
instance : IsZLattice ℝ lattice := by unfold lattice; infer_instance

def integerPoint (m n : ℤ) : Point := basisEquiv (m,n)

theorem latticeBasis_repr_integerPoint (m n : ℤ) :
    ⇑(latticeBasis.repr (integerPoint m n)) = ![(m:ℝ),(n:ℝ)] := by
  simp [latticeBasis, integerPoint, Basis.map_repr, Basis.coe_finTwoProd_repr]

theorem integerPoint_mem (m n : ℤ) : integerPoint m n ∈ lattice := by
  apply (latticeBasis.mem_span_iff_repr_mem ℤ _).mpr
  intro i
  rw [latticeBasis_repr_integerPoint]
  fin_cases i
  · exact ⟨m, rfl⟩
  · exact ⟨n, rfl⟩

theorem mem_lattice_iff (x : Point) : x ∈ lattice ↔ ∃ m n : ℤ, integerPoint m n=x := by
  constructor
  · intro hx
    have hr := (latticeBasis.mem_span_iff_repr_mem ℤ x).mp hx
    obtain ⟨m, hm⟩ := hr 0
    obtain ⟨n, hn⟩ := hr 1
    refine ⟨m,n,latticeBasis.repr.injective ?_⟩
    ext i
    change latticeBasis.repr (integerPoint m n) i = latticeBasis.repr x i
    rw [latticeBasis_repr_integerPoint]
    fin_cases i
    · exact hm
    · exact hn
  · rintro ⟨m,n,rfl⟩
    exact integerPoint_mem m n

theorem norm_sq (p : Point) : ‖p‖^2 = p.fst^2+p.snd^2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs]

theorem inner_formula (p q : Point) : ⟪p,q⟫_ℝ = p.fst*q.fst+p.snd*q.snd := by
  simp [WithLp.prod_inner_apply, real_inner_comm, mul_comm]

theorem integerPoint_norm_sq (m n : ℤ) : ‖integerPoint m n‖^2 = ((m^2+m*n+n^2 : ℤ) : ℝ) := by
  rw [norm_sq]
  change ((m:ℝ)+(n:ℝ)/2)^2+(Real.sqrt 3/2*(n:ℝ))^2 = _
  push_cast
  nlinarith [sqrt_three_sq]

theorem small_norm_coordinates {m n : ℤ} (h : m^2+m*n+n^2 < 3) :
    (-1 ≤ m ∧ m ≤ 1) ∧ (-1 ≤ n ∧ n ≤ 1) := by
  have h1 : 3*m^2 ≤ 4*(m^2+m*n+n^2) := by nlinarith [sq_nonneg (m+2*n)]
  have h2 : 3*n^2 ≤ 4*(m^2+m*n+n^2) := by nlinarith [sq_nonneg (2*m+n)]
  have hm : -1 ≤ m ∧ m ≤ 1 := by
    constructor <;> by_contra hn
    · have : m ≤ -2 := by omega
      nlinarith
    · have : 2 ≤ m := by omega
      nlinarith
  have hn : -1 ≤ n ∧ n ≤ 1 := by
    constructor <;> by_contra hn
    · have : n ≤ -2 := by omega
      nlinarith
    · have : 2 ≤ n := by omega
      nlinarith
  exact ⟨hm,hn⟩

theorem nonroot_norm_gap {m n : ℤ} (h0 : m ≠ 0 ∨ n ≠ 0) (hr : m^2+m*n+n^2 ≠ 1) :
    3 ≤ m^2+m*n+n^2 := by
  by_contra h
  obtain ⟨hm,hn⟩ := small_norm_coordinates (by omega : m^2+m*n+n^2 < 3)
  rcases hm with ⟨hm1,hm2⟩
  rcases hn with ⟨hn1,hn2⟩
  interval_cases m <;> interval_cases n <;> norm_num at h0 hr h ⊢

def hexagon : Set Point := {p | |p.fst| ≤ 1/2 ∧ |p.snd| ≤ (1-|p.fst|)/Real.sqrt 3}

theorem hexagon_norm_sq_le {p : Point} (hp : p ∈ hexagon) : ‖p‖^2 ≤ 1/3 := by
  have ha : 0 ≤ 1-|p.fst| := by linarith [hp.1]
  have hb : Real.sqrt 3*|p.snd| ≤ 1-|p.fst| := by
    simpa only [mul_comm] using (le_div_iff₀ sqrt_three_pos).mp hp.2
  have hb2 := (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt 3*|p.snd|) ha).mpr hb
  rw [mul_pow, sqrt_three_sq, sq_abs] at hb2
  rw [norm_sq]
  have hc := mul_nonneg (abs_nonneg p.fst) (by linarith [hp.1] : 0 ≤ 1/2-|p.fst|)
  nlinarith [sq_abs p.fst]

theorem hexagon_root_inner {p : Point} (hp : p ∈ hexagon) {m n : ℤ}
    (hr : m^2+m*n+n^2=1) : 2*⟪p,integerPoint m n⟫_ℝ ≤ 1 := by
  have hb : |p.fst|+Real.sqrt 3*|p.snd| ≤ 1 := by
    have h := (le_div_iff₀ sqrt_three_pos).mp hp.2
    nlinarith
  have hy := mul_le_mul_of_nonneg_left (le_abs_self p.snd) sqrt_three_pos.le
  have hy' := mul_le_mul_of_nonneg_left (neg_le_abs p.snd) sqrt_three_pos.le
  have hx := le_abs_self p.fst
  have hx' := neg_le_abs p.fst
  obtain ⟨hm,hn⟩ := small_norm_coordinates (by omega : m^2+m*n+n^2 < 3)
  rw [inner_formula]
  change 2*(p.fst*((m:ℝ)+(n:ℝ)/2)+p.snd*(Real.sqrt 3/2*(n:ℝ))) ≤ 1
  rcases hm with ⟨hm1,hm2⟩
  rcases hn with ⟨hn1,hn2⟩
  interval_cases m <;> interval_cases n <;> norm_num at hr ⊢ <;> nlinarith [hp.1]


theorem voronoi_eq_hexagon : voronoi lattice = hexagon := by
  ext p
  constructor
  · intro hp
    have H (m n : ℤ) := (mem_voronoi_iff lattice p).mp hp (integerPoint m n) (integerPoint_mem m n)
    have H' (m n : ℤ) : 2*(p.fst*((m:ℝ)+(n:ℝ)/2)+p.snd*(Real.sqrt 3/2*(n:ℝ))) ≤
        ((m^2+m*n+n^2 : ℤ):ℝ) := by
      simpa only [integerPoint_norm_sq, inner_formula] using H m n
    have h1 := H' 1 0
    have h2 := H' (-1) 0
    have h3 := H' 0 1
    have h4 := H' 1 (-1)
    have h5 := H' (-1) 1
    have h6 := H' 0 (-1)
    norm_num at h1 h2 h3 h4 h5 h6
    refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
    apply (le_div_iff₀ sqrt_three_pos).mpr
    rcases le_total 0 p.fst with hx | hx <;> rcases le_total 0 p.snd with hy | hy
    · rw [abs_of_nonneg hx, abs_of_nonneg hy]; nlinarith
    · rw [abs_of_nonneg hx, abs_of_nonpos hy]; nlinarith
    · rw [abs_of_nonpos hx, abs_of_nonneg hy]; nlinarith
    · rw [abs_of_nonpos hx, abs_of_nonpos hy]; nlinarith
  · intro hp
    rw [mem_voronoi_iff]
    intro z hz
    obtain ⟨m,n,rfl⟩ := (mem_lattice_iff z).mp hz
    by_cases h0 : m=0 ∧ n=0
    · rcases h0 with ⟨rfl,rfl⟩
      simp [integerPoint, basisEquiv, point]
    by_cases hr : m^2+m*n+n^2=1
    · rw [integerPoint_norm_sq, hr]
      exact_mod_cast hexagon_root_inner hp hr
    · have hg : (3:ℝ) ≤ ‖integerPoint m n‖^2 := by
        rw [integerPoint_norm_sq]
        exact_mod_cast nonroot_norm_gap (by tauto : m ≠ 0 ∨ n ≠ 0) hr
      have hn := hexagon_norm_sq_le hp
      have hc : 2*‖p‖ ≤ ‖integerPoint m n‖ := by nlinarith [norm_nonneg p, norm_nonneg (integerPoint m n)]
      have hm := mul_le_mul_of_nonneg_right hc (norm_nonneg (integerPoint m n))
      have hi := real_inner_le_norm p (integerPoint m n)
      nlinarith

theorem dimension_two : Module.finrank ℝ Point = 2 := by
  simpa using Module.finrank_eq_card_basis latticeBasis

end D4.Hexagonal
