import D4.PrincipalFan

/-! Three-level fan simplices have pairwise null intersections. This is a
generic theorem about affine supporting inequalities and finite incidence
data; no assertion that the cells cover a polytope is assumed. -/
noncomputable section
open Matrix MeasureTheory Set
namespace D4.Principal
open Analytic

structure FanCell (F K : Type*) where
  f : F
  g : F
  h : F
  p : K
  q : K
  u : K
  v : K
  deriving DecidableEq

def fanCellVertices {F K : Type*} (V : K → Vec) (c : FanCell F K) : Fin 5 → Vec :=
  ![0, V c.p, V c.q, V c.u, V c.v]

abbrev cellVertices {F K : Type*} (V : K → Vec) (c : FanCell F K) : Fin 5 → Vec :=
  fanCellVertices V c

theorem fanCellVertices_forall {F K : Type*} (V : K → Vec) (c : FanCell F K)
    (P : Vec → Prop) (h0 : P 0) (hp : P (V c.p)) (hq : P (V c.q))
    (hu : P (V c.u)) (hv : P (V c.v)) : ∀ i, P (fanCellVertices V c i) := by
  intro i
  fin_cases i <;> assumption

structure FanCellGeometry {F K : Type*} (s : F → AffineSlack) (V : K → Vec)
    (c : FanCell F K) : Prop where
  f_p : (s c.f).eval (V c.p) = 0
  f_q : (s c.f).eval (V c.q) = 0
  f_u : (s c.f).eval (V c.u) = 0
  f_v : (s c.f).eval (V c.v) = 0
  g_p_pos : 0 < (s c.g).eval (V c.p)
  g_q : (s c.g).eval (V c.q) = 0
  g_u : (s c.g).eval (V c.u) = 0
  g_v : (s c.g).eval (V c.v) = 0
  h_q_pos : 0 < (s c.h).eval (V c.q)
  h_u : (s c.h).eval (V c.u) = 0
  h_v : (s c.h).eval (V c.v) = 0

namespace AffineSlack

theorem eval_fan_nonpos_on_zero (s t : AffineSlack) (p x : Vec)
    (hp : 0 ≤ t.eval p) (ht : t.eval x = 0) (hs : s.eval x ≤ 0) :
    (s.fan t p).eval x ≤ 0 := by
  rw [eval_fan_on_zero _ _ _ _ ht]
  exact mul_nonpos_of_nonneg_of_nonpos hp hs

theorem eval_fan_ne_on_zero (s t : AffineSlack) (p x : Vec)
    (hp : t.eval p ≠ 0) (ht : t.eval x = 0) (hs : s.eval x ≠ 0) :
    (s.fan t p).eval x ≠ 0 := by
  rw [eval_fan_on_zero _ _ _ _ ht]
  exact mul_ne_zero hp hs

theorem eval_fan_ne_of_faces (s t : AffineSlack) (p x : Vec)
    (hs : 0 < s.eval p) (ht : 0 < t.eval p)
    (hx : (s.eval x = 0 ∧ 0 < t.eval x) ∨ (t.eval x = 0 ∧ 0 < s.eval x)) :
    (s.fan t p).eval x ≠ 0 := by
  rcases hx with ⟨hz, hpos⟩ | ⟨hz, hpos⟩
  · rw [eval_fan, hz, mul_zero, zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero hs.ne' hpos.ne')
  · rw [eval_fan, hz, mul_zero, sub_zero]
    exact mul_ne_zero ht.ne' hpos.ne'

theorem lift_cell_nonpos {F K : Type*} (s t : AffineSlack) (V : K → Vec) (c : FanCell F K)
    (ht : 0 ≤ t.eval 0)
    (hp0 : t.eval (V c.p) = 0) (hq0 : t.eval (V c.q) = 0)
    (hu0 : t.eval (V c.u) = 0) (hv0 : t.eval (V c.v) = 0)
    (hp : s.eval (V c.p) ≤ 0) (hq : s.eval (V c.q) ≤ 0)
    (hu : s.eval (V c.u) ≤ 0) (hv : s.eval (V c.v) ≤ 0) :
    ∀ i, (s.fan t 0).eval (fanCellVertices V c i) ≤ 0 := by
  apply fanCellVertices_forall V c (fun x => (s.fan t 0).eval x ≤ 0)
  · simp
  · exact eval_fan_nonpos_on_zero s t 0 _ ht hp0 hp
  · exact eval_fan_nonpos_on_zero s t 0 _ ht hq0 hq
  · exact eval_fan_nonpos_on_zero s t 0 _ ht hu0 hu
  · exact eval_fan_nonpos_on_zero s t 0 _ ht hv0 hv

theorem lift_cell_nonneg {F K : Type*} (s t : AffineSlack) (V : K → Vec) (c : FanCell F K)
    (ht : 0 ≤ t.eval 0)
    (hp0 : t.eval (V c.p) = 0) (hq0 : t.eval (V c.q) = 0)
    (hu0 : t.eval (V c.u) = 0) (hv0 : t.eval (V c.v) = 0)
    (hp : 0 ≤ s.eval (V c.p)) (hq : 0 ≤ s.eval (V c.q))
    (hu : 0 ≤ s.eval (V c.u)) (hv : 0 ≤ s.eval (V c.v)) :
    ∀ i, 0 ≤ (s.fan t 0).eval (fanCellVertices V c i) := by
  apply fanCellVertices_forall V c (fun x => 0 ≤ (s.fan t 0).eval x)
  · simp
  · exact eval_fan_nonneg s t 0 _ ht hp hp0
  · exact eval_fan_nonneg s t 0 _ ht hq hq0
  · exact eval_fan_nonneg s t 0 _ ht hu hu0
  · exact eval_fan_nonneg s t 0 _ ht hv hv0

end AffineSlack

theorem fanCells_levelOne_null {F K : Type*} (s : F → AffineSlack) (V : K → Vec)
    (c d : FanCell F K) (hc : FanCellGeometry s V c) (hd : FanCellGeometry s V d)
    (hall : ∀ f k, 0 ≤ (s f).eval (V k)) (h0 : ∀ f, 0 < (s f).eval 0)
    (hwitness : ∃ r, ((s c.f).eval (V r) = 0 ∧ 0 < (s d.f).eval (V r)) ∨
      ((s d.f).eval (V r) = 0 ∧ 0 < (s c.f).eval (V r))) :
    volume (vertexSimplex (cellVertices V c) ∩ vertexSimplex (cellVertices V d)) = 0 := by
  let S := (s c.f).fan (s d.f) 0
  obtain ⟨r, hr⟩ := hwitness
  have hn : S.normal ≠ 0 := AffineSlack.normal_ne_zero_of_eval_ne S 0 (V r)
    (AffineSlack.eval_fan_apex _ _ _) (AffineSlack.eval_fan_ne_of_faces _ _ _ _ (h0 _) (h0 _) hr)
  apply AffineSlack.simplex_inter_volume S _ _ hn
  · apply fanCellVertices_forall V c (fun x => S.eval x ≤ 0)
    · exact (AffineSlack.eval_fan_apex _ _ _).le
    · exact AffineSlack.eval_fan_nonpos _ _ _ _ (h0 _).le hc.f_p (hall _ _)
    · exact AffineSlack.eval_fan_nonpos _ _ _ _ (h0 _).le hc.f_q (hall _ _)
    · exact AffineSlack.eval_fan_nonpos _ _ _ _ (h0 _).le hc.f_u (hall _ _)
    · exact AffineSlack.eval_fan_nonpos _ _ _ _ (h0 _).le hc.f_v (hall _ _)
  · apply fanCellVertices_forall V d (fun x => 0 ≤ S.eval x)
    · exact (AffineSlack.eval_fan_apex _ _ _).ge
    · exact AffineSlack.eval_fan_nonneg _ _ _ _ (h0 _).le (hall _ _) hd.f_p
    · exact AffineSlack.eval_fan_nonneg _ _ _ _ (h0 _).le (hall _ _) hd.f_q
    · exact AffineSlack.eval_fan_nonneg _ _ _ _ (h0 _).le (hall _ _) hd.f_u
    · exact AffineSlack.eval_fan_nonneg _ _ _ _ (h0 _).le (hall _ _) hd.f_v

theorem fanCells_levelTwo_null {F K : Type*} (s : F → AffineSlack) (V : K → Vec)
    (c d : FanCell F K) (hc : FanCellGeometry s V c) (hd : FanCellGeometry s V d)
    (hall : ∀ f k, 0 ≤ (s f).eval (V k)) (h0 : ∀ f, 0 < (s f).eval 0)
    (hf : c.f = d.f) (hp : c.p = d.p)
    (hwitness : ∃ r, (s c.f).eval (V r) = 0 ∧
      (((s c.g).eval (V r) = 0 ∧ 0 < (s d.g).eval (V r)) ∨
        ((s d.g).eval (V r) = 0 ∧ 0 < (s c.g).eval (V r)))) :
    volume (vertexSimplex (cellVertices V c) ∩ vertexSimplex (cellVertices V d)) = 0 := by
  let S := (s c.g).fan (s d.g) (V c.p)
  let T := S.fan (s c.f) 0
  have hdp : 0 < (s d.g).eval (V c.p) := by rw [hp]; exact hd.g_p_pos
  have hSp : S.eval (V c.p) = 0 := AffineSlack.eval_fan_apex _ _ _
  have hSdp : S.eval (V d.p) = 0 := by rw [← hp]; exact hSp
  obtain ⟨r, hrf, hr⟩ := hwitness
  have hSr : S.eval (V r) ≠ 0 :=
    AffineSlack.eval_fan_ne_of_faces _ _ _ _ hc.g_p_pos hdp hr
  have hTr : T.eval (V r) ≠ 0 :=
    AffineSlack.eval_fan_ne_on_zero S (s c.f) 0 _ (h0 _).ne' hrf hSr
  have hn : T.normal ≠ 0 := AffineSlack.normal_ne_zero_of_eval_ne T 0 (V r)
    (AffineSlack.eval_fan_apex _ _ _) hTr
  apply AffineSlack.simplex_inter_volume T _ _ hn
  · apply AffineSlack.lift_cell_nonpos S (s c.f) V c (h0 _).le hc.f_p hc.f_q hc.f_u hc.f_v
    · exact hSp.le
    · exact AffineSlack.eval_fan_nonpos _ _ _ _ hc.g_p_pos.le hc.g_q (hall _ _)
    · exact AffineSlack.eval_fan_nonpos _ _ _ _ hc.g_p_pos.le hc.g_u (hall _ _)
    · exact AffineSlack.eval_fan_nonpos _ _ _ _ hc.g_p_pos.le hc.g_v (hall _ _)
  · apply AffineSlack.lift_cell_nonneg S (s c.f) V d (h0 _).le
      (by simpa only [hf] using hd.f_p) (by simpa only [hf] using hd.f_q)
      (by simpa only [hf] using hd.f_u) (by simpa only [hf] using hd.f_v)
    · exact hSdp.ge
    · exact AffineSlack.eval_fan_nonneg _ _ _ _ hdp.le (hall _ _) hd.g_q
    · exact AffineSlack.eval_fan_nonneg _ _ _ _ hdp.le (hall _ _) hd.g_u
    · exact AffineSlack.eval_fan_nonneg _ _ _ _ hdp.le (hall _ _) hd.g_v

theorem fanCells_levelThree_null {F K : Type*} (s : F → AffineSlack) (V : K → Vec)
    (c d : FanCell F K) (hc : FanCellGeometry s V c) (hd : FanCellGeometry s V d)
    (hall : ∀ f k, 0 ≤ (s f).eval (V k)) (h0 : ∀ f, 0 < (s f).eval 0)
    (hf : c.f = d.f) (hg : c.g = d.g) (hp : c.p = d.p) (hq : c.q = d.q)
    (hwitness : ∃ r, (s c.f).eval (V r) = 0 ∧ (s c.g).eval (V r) = 0 ∧
      (((s c.h).eval (V r) = 0 ∧ 0 < (s d.h).eval (V r)) ∨
        ((s d.h).eval (V r) = 0 ∧ 0 < (s c.h).eval (V r)))) :
    volume (vertexSimplex (cellVertices V c) ∩ vertexSimplex (cellVertices V d)) = 0 := by
  let S := (s c.h).fan (s d.h) (V c.q)
  let T := S.fan (s c.g) (V c.p)
  let U := T.fan (s c.f) 0
  have hdq : 0 < (s d.h).eval (V c.q) := by rw [hq]; exact hd.h_q_pos
  have hSq : S.eval (V c.q) = 0 := AffineSlack.eval_fan_apex _ _ _
  have hTp : T.eval (V c.p) = 0 := AffineSlack.eval_fan_apex _ _ _
  have hTdp : T.eval (V d.p) = 0 := by rw [← hp]; exact hTp
  have hTq : T.eval (V c.q) = 0 := by
    rw [AffineSlack.eval_fan_on_zero S (s c.g) (V c.p) _ hc.g_q, hSq, mul_zero]
  have hTdq : T.eval (V d.q) = 0 := by rw [← hq]; exact hTq
  obtain ⟨r, hrf, hrg, hr⟩ := hwitness
  have hSr : S.eval (V r) ≠ 0 :=
    AffineSlack.eval_fan_ne_of_faces _ _ _ _ hc.h_q_pos hdq hr
  have hTr : T.eval (V r) ≠ 0 :=
    AffineSlack.eval_fan_ne_on_zero S (s c.g) (V c.p) _ hc.g_p_pos.ne' hrg hSr
  have hUr : U.eval (V r) ≠ 0 :=
    AffineSlack.eval_fan_ne_on_zero T (s c.f) 0 _ (h0 _).ne' hrf hTr
  have hn : U.normal ≠ 0 := AffineSlack.normal_ne_zero_of_eval_ne U 0 (V r)
    (AffineSlack.eval_fan_apex _ _ _) hUr
  apply AffineSlack.simplex_inter_volume U _ _ hn
  · apply AffineSlack.lift_cell_nonpos T (s c.f) V c (h0 _).le hc.f_p hc.f_q hc.f_u hc.f_v
    · exact hTp.le
    · exact hTq.le
    · apply AffineSlack.eval_fan_nonpos_on_zero S (s c.g) (V c.p) _ hc.g_p_pos.le hc.g_u
      exact AffineSlack.eval_fan_nonpos _ _ _ _ hc.h_q_pos.le hc.h_u (hall _ _)
    · apply AffineSlack.eval_fan_nonpos_on_zero S (s c.g) (V c.p) _ hc.g_p_pos.le hc.g_v
      exact AffineSlack.eval_fan_nonpos _ _ _ _ hc.h_q_pos.le hc.h_v (hall _ _)
  · apply AffineSlack.lift_cell_nonneg T (s c.f) V d (h0 _).le
      (by simpa only [hf] using hd.f_p) (by simpa only [hf] using hd.f_q)
      (by simpa only [hf] using hd.f_u) (by simpa only [hf] using hd.f_v)
    · exact hTdp.ge
    · exact hTdq.ge
    · apply AffineSlack.eval_fan_nonneg S (s c.g) (V c.p) _ hc.g_p_pos.le _
        (by simpa only [hg] using hd.g_u)
      exact AffineSlack.eval_fan_nonneg _ _ _ _ hdq.le (hall _ _) hd.h_u
    · apply AffineSlack.eval_fan_nonneg S (s c.g) (V c.p) _ hc.g_p_pos.le _
        (by simpa only [hg] using hd.g_v)
      exact AffineSlack.eval_fan_nonneg _ _ _ _ hdq.le (hall _ _) hd.h_v

/-- Finite incidence and face-distinction witnesses imply pairwise null
intersections, without presupposing any global fan decomposition. -/
theorem fanCells_pairwise_null {I F K : Type*} (s : F → AffineSlack) (V : K → Vec)
    (c : I → FanCell F K)
    (hall : ∀ f k, 0 ≤ (s f).eval (V k)) (h0 : ∀ f, 0 < (s f).eval 0)
    (hgeom : ∀ i, FanCellGeometry s V (c i))
    (hp : ∀ i j, (c i).f = (c j).f → (c i).p = (c j).p)
    (hq : ∀ i j, (c i).f = (c j).f → (c i).g = (c j).g → (c i).q = (c j).q)
    (hinj : ∀ i j, (c i).f = (c j).f → (c i).g = (c j).g → (c i).h = (c j).h → i = j)
    (hface : ∀ i j, (c i).f ≠ (c j).f → ∃ r,
      (((s (c i).f).eval (V r) = 0 ∧ 0 < (s (c j).f).eval (V r)) ∨
        ((s (c j).f).eval (V r) = 0 ∧ 0 < (s (c i).f).eval (V r))))
    (hface2 : ∀ i j, (c i).f = (c j).f → (c i).g ≠ (c j).g → ∃ r,
      (s (c i).f).eval (V r) = 0 ∧
      (((s (c i).g).eval (V r) = 0 ∧ 0 < (s (c j).g).eval (V r)) ∨
        ((s (c j).g).eval (V r) = 0 ∧ 0 < (s (c i).g).eval (V r))))
    (hface3 : ∀ i j, (c i).f = (c j).f → (c i).g = (c j).g → (c i).h ≠ (c j).h → ∃ r,
      (s (c i).f).eval (V r) = 0 ∧ (s (c i).g).eval (V r) = 0 ∧
      (((s (c i).h).eval (V r) = 0 ∧ 0 < (s (c j).h).eval (V r)) ∨
        ((s (c j).h).eval (V r) = 0 ∧ 0 < (s (c i).h).eval (V r)))) :
    Pairwise fun i j => volume (vertexSimplex (cellVertices V (c i)) ∩
      vertexSimplex (cellVertices V (c j))) = 0 := by
  classical
  intro i j hij
  by_cases hf : (c i).f = (c j).f
  · by_cases hg : (c i).g = (c j).g
    · have hh : (c i).h ≠ (c j).h := fun h => hij (hinj i j hf hg h)
      exact fanCells_levelThree_null s V (c i) (c j) (hgeom i) (hgeom j) hall h0 hf hg
        (hp i j hf) (hq i j hf hg) (hface3 i j hf hg hh)
    · exact fanCells_levelTwo_null s V (c i) (c j) (hgeom i) (hgeom j) hall h0 hf
        (hp i j hf) (hface2 i j hf hg)
  · exact fanCells_levelOne_null s V (c i) (c j) (hgeom i) (hgeom j) hall h0 (hface i j hf)

end D4.Principal
