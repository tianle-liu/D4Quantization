import D4.AreaTrapezoidGeometry

noncomputable section
namespace D4.AreaEnvelope
open Set Matrix

def Trapezoid.ofAffine (l w b₀ b₁ t₀ t₁ : ℝ) : Trapezoid :=
  ⟨l,w,b₀+b₁*l,b₀+b₁*(l+w),t₀+t₁*l,t₀+t₁*(l+w)⟩

theorem Trapezoid.ofAffine_body (l w b₀ b₁ t₀ t₁ : ℝ) (hw : 0<w) (x : Plane) :
    x∈(ofAffine l w b₀ b₁ t₀ t₁).body ↔
      l≤x 0 ∧ x 0≤l+w ∧ b₀+b₁*x 0≤x 1 ∧ x 1≤t₀+t₁*x 0 := by
  let s := (x 0-l)/w
  have hs : w*s=x 0-l := by dsimp [s]; field_simp
  have h0 : 0≤s ↔ l≤x 0 := by
    dsimp [s]
    rw [le_div_iff₀ hw]
    constructor <;> intro h <;> linarith
  have h1 : s≤1 ↔ x 0≤l+w := by
    dsimp [s]
    rw [div_le_iff₀ hw]
    constructor <;> intro h <;> linarith
  have he (a b : ℝ) : a+b*l+(a+b*(l+w)-(a+b*l))*s=a+b*x 0 := by
    calc
      _ = a+b*l+b*(w*s) := by ring
      _ = _ := by rw [hs]; ring
  change (0≤s ∧ s≤1 ∧ b₀+b₁*l+(b₀+b₁*(l+w)-(b₀+b₁*l))*s≤x 1 ∧
    x 1≤t₀+t₁*l+(t₀+t₁*(l+w)-(t₀+t₁*l))*s) ↔ _
  rw [h0,h1,he,he]

end D4.AreaEnvelope
