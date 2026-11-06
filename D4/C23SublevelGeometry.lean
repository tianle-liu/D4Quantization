import D4.AreaSublevel

/-! Actual sublevel sets of the local minimum gaps. -/
noncomputable section
namespace D4.C23Local
open Set AreaEnvelope

def min3 (a b c : ℝ) := min a (min b c)
def min4 (a b c d : ℝ) := min a (min b (min c d))

def lower2 (r : ℝ) (L : Plane) := min4 0 (L 0) (L 1) (L 0+L 1-2*r)
def upper2 (p q r : ℝ) (L : Plane) :=
  min4 0 (2*(p+r)-L 0) (2*(q+r)-L 1) (2*(p+q)-(L 0+L 1-2*r))
def gap2 (p q r : ℝ) (L : Plane) := -lower2 r L-upper2 p q r L

def lower3 (L : Plane) := min3 0 (L 0) (L 1)
def upper3 (A B : ℝ) (L : Plane) := min3 0 (A-L 0) (B-L 1)
def gap3 (A B : ℝ) (L : Plane) := -lower3 L-upper3 A B L

private theorem le_min_add_iff (a b c d : ℝ) :
    c ≤ min a b+d ↔ c ≤ a+d ∧ c ≤ b+d := by
  constructor
  · intro h; constructor <;> linarith [min_le_left a b, min_le_right a b]
  · rintro ⟨h₁,h₂⟩
    have h : c-d ≤ min a b := le_min (by linarith) (by linarith)
    linarith

private theorem le_add_min_iff (a b c d : ℝ) :
    c ≤ d+min a b ↔ c ≤ d+a ∧ c ≤ d+b := by
  simpa only [add_comm d] using le_min_add_iff a b c d

theorem gap2_nonneg (p q r : ℝ) (L : Plane) : 0 ≤ gap2 p q r L := by
  have h₁ : lower2 r L ≤ 0 := min_le_left _ _
  have h₂ : upper2 p q r L ≤ 0 := min_le_left _ _
  dsimp [gap2]; linarith

theorem gap3_nonneg (A B : ℝ) (L : Plane) : 0 ≤ gap3 A B L := by
  have h₁ : lower3 L ≤ 0 := min_le_left _ _
  have h₂ : upper3 A B L ≤ 0 := min_le_left _ _
  dsimp [gap3]; linarith

theorem gap2_continuous (p q r : ℝ) : Continuous (gap2 p q r) := by
  unfold gap2 lower2 upper2 min4
  fun_prop

theorem gap3_continuous (A B : ℝ) : Continuous (gap3 A B) := by
  unfold gap3 lower3 upper3 min3
  fun_prop

/-- All sixteen pair inequalities are reduced to the eight displayed
halfspaces. The other eight follow from nonnegative parameters. -/
theorem gap2_le_iff (p q r s : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (L : Plane) :
    gap2 p q r L ≤ s ↔
      -s ≤ L 0 ∧ L 0 ≤ 2*(p+r)+s ∧
      -s ≤ L 1 ∧ L 1 ≤ 2*(q+r)+s ∧
      2*r-s ≤ L 0+L 1 ∧ L 0+L 1 ≤ 2*(p+q+r)+s ∧
      L 0-L 1 ≤ 2*(p+r)+s ∧ L 1-L 0 ≤ 2*(q+r)+s := by
  have he : gap2 p q r L ≤ s ↔ -s ≤ lower2 r L+upper2 p q r L := by
    unfold gap2; constructor <;> intro h <;> linarith
  rw [he]
  simp only [lower2,upper2,min4,le_min_add_iff,le_add_min_iff]
  constructor
  · rintro ⟨⟨h00,h01,h02,h03⟩,⟨h10,h11,h12,h13⟩,
      ⟨h20,h21,h22,h23⟩,⟨h30,h31,h32,h33⟩⟩
    (repeat' constructor) <;> linarith
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
    (repeat' constructor) <;> linarith

/-- The analogous nine pair inequalities reduce to six halfspaces. -/
theorem gap3_le_iff (A B s : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : 0 ≤ s) (L : Plane) :
    gap3 A B L ≤ s ↔
      -s ≤ L 0 ∧ L 0 ≤ A+s ∧ -s ≤ L 1 ∧ L 1 ≤ B+s ∧
      L 0-L 1 ≤ A+s ∧ L 1-L 0 ≤ B+s := by
  have he : gap3 A B L ≤ s ↔ -s ≤ lower3 L+upper3 A B L := by
    unfold gap3; constructor <;> intro h <;> linarith
  rw [he]
  simp only [lower3,upper3,min3,le_min_add_iff,le_add_min_iff]
  constructor
  · rintro ⟨⟨h00,h01,h02⟩,⟨h10,h11,h12⟩,⟨h20,h21,h22⟩⟩
    (repeat' constructor) <;> linarith
  · rintro ⟨h1,h2,h3,h4,h5,h6⟩
    (repeat' constructor) <;> linarith

/-- A rectangle with four corner cuts, including cuts of zero size. -/
def clippedRectangle (W H c d : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ W ∧ 0 ≤ z.2 ∧ z.2 ≤ H ∧
    c ≤ z.1+z.2 ∧ z.1+z.2 ≤ W+H-c ∧
    z.1-z.2 ≤ W-d ∧ z.2-z.1 ≤ H-d}

theorem gap2_sublevel_translation (p q r s : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (L : Plane) :
    gap2 p q r L ≤ s ↔
      (L 0+s,L 1+s) ∈ clippedRectangle (2*(p+r+s)) (2*(q+r+s)) (2*r+s) s := by
  rw [gap2_le_iff p q r s hp hq hr hs]
  simp only [clippedRectangle,mem_setOf_eq]
  constructor <;> rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ <;>
    (repeat' constructor) <;> linarith

theorem gap3_sublevel_translation (A B s : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : 0 ≤ s) (L : Plane) :
    gap3 A B L ≤ s ↔
      (L 0+s,L 1+s) ∈ clippedRectangle (A+2*s) (B+2*s) 0 s := by
  rw [gap3_le_iff A B s hA hB hs]
  simp only [clippedRectangle,mem_setOf_eq]
  constructor
  · rintro ⟨h1,h2,h3,h4,h5,h6⟩
    (repeat' constructor) <;> linarith
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
    (repeat' constructor) <;> linarith


/-- Uniform control of the moving C₃ gap on a fixed compact neighborhood. -/
theorem gap3_shift_bounds (A B t : ℝ) (ht : 0 ≤ t) (L : Plane) :
    gap3 A B L ≤ gap3 (A-t) (B-t) L ∧
      gap3 (A-t) (B-t) L ≤ gap3 A B L+t := by
  have h0 : upper3 A B L ≤ 0 := min_le_left _ _
  have h1 : upper3 A B L ≤ A-L 0 := le_trans (min_le_right _ _) (min_le_left _ _)
  have h2 : upper3 A B L ≤ B-L 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  have k0 : upper3 (A-t) (B-t) L ≤ 0 := min_le_left _ _
  have k1 : upper3 (A-t) (B-t) L ≤ A-t-L 0 := le_trans (min_le_right _ _) (min_le_left _ _)
  have k2 : upper3 (A-t) (B-t) L ≤ B-t-L 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hle : upper3 (A-t) (B-t) L ≤ upper3 A B L := by
    change upper3 (A-t) (B-t) L ≤ min 0 (min (A-L 0) (B-L 1))
    exact le_min k0 (le_min (by linarith) (by linarith))
  have hge : upper3 A B L-t ≤ upper3 (A-t) (B-t) L := by
    change upper3 A B L-t ≤ min 0 (min (A-t-L 0) (B-t-L 1))
    exact le_min (by linarith) (le_min (by linarith) (by linarith))
  unfold gap3
  constructor <;> linarith

theorem minimum_square_recenter (U V x y t : ℝ) :
    min4 U x y (x+y+t+V) =
      U+min4 0 (x-U) (y-U) ((x-U)+(y-U)+t-(-U-V)) := by
  simp only [min4,add_min]
  congr 1
  · ring
  congr 1
  · ring
  congr 1 <;> ring

end D4.C23Local
