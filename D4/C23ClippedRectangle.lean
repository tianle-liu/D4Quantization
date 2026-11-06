import D4.C23SublevelGeometry
import D4.AreaSquareEnvelope

/-! Actual Lebesgue area of a rectangle with four disjoint corner cuts. -/
noncomputable section
namespace D4.C23Local
open Set MeasureTheory

def clipLower (W c d x : ℝ) := max 0 (max (c-x) (x-W+d))
def clipUpper (W H c d x : ℝ) := min H (min (W+H-c-x) (x+H-d))

theorem clippedRectangle_slices_iff (W H c d : ℝ) (z : ℝ × ℝ) :
    z ∈ clippedRectangle W H c d ↔
      z.1 ∈ Icc 0 W ∧ z.2 ∈ Icc (clipLower W c d z.1) (clipUpper W H c d z.1) := by
  simp only [clippedRectangle,mem_setOf_eq,mem_Icc,clipLower,clipUpper,
    max_le_iff,le_min_iff]
  constructor
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
    (repeat' constructor) <;> linarith
  · rintro ⟨⟨h1,h2⟩,⟨h3,h5,h7⟩,h4,h6,h8⟩
    (repeat' constructor) <;> linarith

theorem clippedRectangle_compact (W H c d : ℝ) :
    IsCompact (clippedRectangle W H c d) := by
  have hc : IsClosed (clippedRectangle W H c d) := by
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_const).inter
      ((isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_snd continuous_const).inter
      ((isClosed_le continuous_const (continuous_fst.add continuous_snd)).inter
      ((isClosed_le (continuous_fst.add continuous_snd) continuous_const).inter
      ((isClosed_le (continuous_fst.sub continuous_snd) continuous_const).inter
        (isClosed_le (continuous_snd.sub continuous_fst) continuous_const)))))))
  exact (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hc
    (show clippedRectangle W H c d ⊆ Icc 0 W ×ˢ Icc 0 H from
      fun _ h => ⟨⟨h.1,h.2.1⟩,⟨h.2.2.1,h.2.2.2.1⟩⟩)

theorem clipLower_le_upper (W H c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hW : c+d ≤ W) (hH : c+d ≤ H) (x : ℝ) (hx : x ∈ Icc 0 W) :
    clipLower W c d x ≤ clipUpper W H c d x := by
  simp only [clipLower,clipUpper,max_le_iff,le_min_iff]
  (repeat' constructor) <;> linarith [hx.1,hx.2]

private theorem max_pair (a b : ℝ) (h : a+b ≤ 0) :
    max 0 (max a b) = max a 0+max b 0 := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · simp [max_eq_right ha,max_eq_right hb,max_eq_left (max_le ha hb)]
  · rw [max_eq_right ha,max_eq_left hb,max_eq_right (le_max_of_le_right hb),
      max_eq_right (by linarith : a ≤ b)]; ring
  · rw [max_eq_left ha,max_eq_right hb,max_eq_right (le_max_of_le_left ha),
      max_eq_left (by linarith : b ≤ a)]; ring
  · have ha0 : a=0 := by linarith
    have hb0 : b=0 := by linarith
    simp [ha0,hb0]

private theorem min_pair (H a b : ℝ) (h : a+b ≤ 0) :
    min H (min (H-a) (H-b)) = H-(max a 0+max b 0) := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [max_eq_right ha,max_eq_right hb,min_eq_left (le_min (by linarith) (by linarith))]
    ring
  · rw [max_eq_right ha,max_eq_left hb,min_eq_right (by linarith : H-b ≤ H-a),
      min_eq_right (by linarith : H-b ≤ H)]; ring
  · rw [max_eq_left ha,max_eq_right hb,min_eq_left (by linarith : H-a ≤ H-b),
      min_eq_right (by linarith : H-a ≤ H)]; ring
  · have ha0 : a=0 := by linarith
    have hb0 : b=0 := by linarith
    simp [ha0,hb0]

theorem clip_width (W H c d x : ℝ) (hW : c+d ≤ W) :
    clipUpper W H c d x-clipLower W c d x =
      H-max (x-W+c) 0-max (d-x) 0-max (c-x) 0-max (x-W+d) 0 := by
  have h₁ := max_pair (c-x) (x-W+d) (by linarith : c-x+(x-W+d) ≤ 0)
  have h₂ := min_pair H (x-W+c) (d-x) (by linarith : x-W+c+(d-x) ≤ 0)
  have he₁ : W+H-c-x=H-(x-W+c) := by ring
  have he₂ : x+H-d=H-(d-x) := by ring
  rw [clipLower,clipUpper,he₁,he₂,h₁,h₂]
  ring

theorem clippedRectangle_slices (W H c d : ℝ) (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
    (∫ p in clippedRectangle W H c d, f p ∂((volume : Measure ℝ).prod volume)) =
      ∫ x in Icc 0 W, ∫ y in Icc (clipLower W c d x) (clipUpper W H c d x), f (x,y) := by
  have hm := (clippedRectangle_compact W H c d).measurableSet
  have hi : IntegrableOn f (clippedRectangle W H c d) ((volume : Measure ℝ).prod volume) :=
    hf.continuousOn.integrableOn_compact (clippedRectangle_compact W H c d)
  rw [← integral_indicator hm,integral_prod _ (hi.integrable_indicator hm),
    ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ Icc 0 W
    · rw [indicator_of_mem hx,← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        by_cases hy : y ∈ Icc (clipLower W c d x) (clipUpper W H c d x)
        · have hp : (x,y) ∈ clippedRectangle W H c d :=
            (clippedRectangle_slices_iff W H c d (x,y)).mpr ⟨hx,hy⟩
          simp only [indicator_of_mem hp,indicator_of_mem hy]
        · have hp : (x,y) ∉ clippedRectangle W H c d :=
            fun h => hy ((clippedRectangle_slices_iff W H c d (x,y)).mp h).2
          simp only [indicator_of_not_mem hp,indicator_of_not_mem hy]
    · rw [indicator_of_not_mem hx]
      apply integral_eq_zero_of_ae
      exact Filter.Eventually.of_forall fun y => indicator_of_not_mem
        (show (x,y) ∉ clippedRectangle W H c d from
          fun h => hx ((clippedRectangle_slices_iff W H c d (x,y)).mp h).1) f

theorem integral_left_hinge (W a : ℝ) (ha : 0 ≤ a) (haW : a ≤ W) :
    (∫ x in (0:ℝ)..W, max (a-x) 0) = a^2/2 := by
  have hc : Continuous (fun x : ℝ => max (a-x) 0) := by fun_prop
  have h₁ : (∫ x in (0:ℝ)..a, max (a-x) 0) = ∫ x in (0:ℝ)..a, a-x := by
    apply intervalIntegral.integral_congr
    intro x hx; rw [uIcc_of_le ha] at hx
    exact max_eq_left (by linarith [hx.2])
  have h₂ : (∫ x in a..W, max (a-x) 0) = 0 := by
    calc
      _ = ∫ _x in a..W, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le haW] at hx
        exact max_eq_right (by linarith [hx.1])
      _ = 0 := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a W),h₁,h₂,
    intervalIntegral.integral_sub (f := fun _ : ℝ => a) (g := fun x : ℝ => x) intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
    intervalIntegral.integral_const,integral_id]
  simp only [smul_eq_mul]
  ring

theorem integral_right_hinge (W a : ℝ) (ha : 0 ≤ a) (haW : a ≤ W) :
    (∫ x in (0:ℝ)..W, max (x-W+a) 0) = a^2/2 := by
  have hc : Continuous (fun x : ℝ => max (x-W+a) 0) := by fun_prop
  have h₁ : (∫ x in (0:ℝ)..(W-a), max (x-W+a) 0) = 0 := by
    calc
      _ = ∫ _x in (0:ℝ)..(W-a), (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by linarith : (0:ℝ) ≤ W-a)] at hx
        exact max_eq_right (by linarith [hx.2])
      _ = 0 := by simp
  have h₂ : (∫ x in (W-a)..W, max (x-W+a) 0) =
      ∫ x in (W-a)..W, x+(a-W) := by
    apply intervalIntegral.integral_congr
    intro x hx; rw [uIcc_of_le (by linarith : W-a ≤ W)] at hx
    dsimp only
    rw [max_eq_left (by linarith [hx.1] : 0 ≤ x-W+a)]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (W-a)) (hc.intervalIntegrable (W-a) W),h₁,h₂,
    intervalIntegral.integral_add (f := fun x : ℝ => x) (g := fun _ : ℝ => a-W) (continuous_id.intervalIntegrable _ _) intervalIntegrable_const,
    integral_id,intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem clippedRectangle_area (W H c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hW : c+d ≤ W) (hH : c+d ≤ H) :
    volume.real (clippedRectangle W H c d) = W*H-c^2-d^2 := by
  have hW0 : 0 ≤ W := by linarith
  have he : volume.real (clippedRectangle W H c d) =
      ∫ p in clippedRectangle W H c d, (1:ℝ) ∂((volume : Measure ℝ).prod volume) := by
    simp [MeasureTheory.Measure.volume_eq_prod]
  rw [he,clippedRectangle_slices W H c d (fun _ => 1) continuous_const]
  have hv : (∫ x in Icc 0 W, ∫ y in Icc (clipLower W c d x) (clipUpper W H c d x), (1:ℝ)) =
      ∫ x in Icc 0 W, H-max (x-W+c) 0-max (d-x) 0-max (c-x) 0-max (x-W+d) 0 := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    dsimp only
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le
      (clipLower_le_upper W H c d hc hd hW hH x hx),intervalIntegral.integral_const]
    simp only [smul_eq_mul,mul_one]
    exact clip_width W H c d x hW
  rw [hv,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hW0]
  have h₁ : IntervalIntegrable (fun x : ℝ => max (x-W+c) 0) volume 0 W := (by fun_prop : Continuous _).intervalIntegrable _ _
  have h₂ : IntervalIntegrable (fun x : ℝ => max (d-x) 0) volume 0 W := (by fun_prop : Continuous _).intervalIntegrable _ _
  have h₃ : IntervalIntegrable (fun x : ℝ => max (c-x) 0) volume 0 W := (by fun_prop : Continuous _).intervalIntegrable _ _
  have h₄ : IntervalIntegrable (fun x : ℝ => max (x-W+d) 0) volume 0 W := (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (((intervalIntegrable_const.sub h₁).sub h₂).sub h₃) h₄,
    intervalIntegral.integral_sub ((intervalIntegrable_const.sub h₁).sub h₂) h₃,
    intervalIntegral.integral_sub (intervalIntegrable_const.sub h₁) h₂,
    intervalIntegral.integral_sub intervalIntegrable_const h₁,
    intervalIntegral.integral_const,integral_right_hinge W c hc (by linarith),
    integral_left_hinge W d hd (by linarith),integral_left_hinge W c hc (by linarith),
    integral_right_hinge W d hd (by linarith)]
  simp only [smul_eq_mul]
  ring

end D4.C23Local
