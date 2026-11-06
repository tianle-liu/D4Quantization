import D4.CertificateSubstitution

/-! Exact substitutions in the compact secondary-cone moment formulas. -/
namespace D4.CompactMoments
open Certificate
def z2Substitution : Nat → Poly
  | 0 => [([0], 1),([1], 1)]
  | 1 => [([0], 1),([2], 1)]
  | 2 => [([3], 1)]
  | 3 => [([4], 1)]
  | 4 => [([0], -1)]
  | 5 => [([0], 1),([5], 1)]
  | 6 => [([0], 1),([6], 1)]
  | 7 => [([0], 1),([7], 1)]
  | 8 => [([0], 1),([8], 1)]
  | 9 => [([9], 1)]
  | i => [([i], 1)]

def thetaSubstitution : Nat → Poly
  | 0 => [([0], 1),([9], 1)]
  | 1 => [([1], 1),([9], -1)]
  | 2 => [([2], 1),([9], -1)]
  | 3 => [([3], 1)]
  | 4 => [([4], 1)]
  | 5 => [([5], 1)]
  | 6 => [([6], 1)]
  | 7 => [([7], 1)]
  | 8 => [([8], 1)]
  | 9 => [([9], -1)]
  | i => [([i], 1)]

def z2 (x : Nat → ℝ) (i : Nat) : ℝ := eval x (z2Substitution i)
def theta (x : Nat → ℝ) (i : Nat) : ℝ := eval x (thetaSubstitution i)

end D4.CompactMoments
