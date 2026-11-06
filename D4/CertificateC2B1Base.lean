import D4.CertificateC2B1Data
import D4.KernelCompute
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace D4.CertificateC2B1
open D4.Certificate

theorem factors_generate_group : D4.CertificateSort.sort (fun g h => key g ≤ key h) factoredGroup = group := by kernel_rfl

theorem weights_nonnegative : rowsNonnegative rows = true := by kernel_rfl

theorem expand_rows : sumFast (rows.map Row.expand) = unsym := by kernel_rfl

theorem unsym_nonnegative (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x unsym := by
  rw [← expand_rows, eval_sumFast_eq_sum]
  exact rows_nonneg x hx rows weights_nonnegative

end D4.CertificateC2B1
