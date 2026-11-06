import D4.C3CellDetCheck0
import D4.C3CellDetCheck1
import D4.C3CellDetCheck2
import D4.C3CellDetCheck3
import D4.C3CellDetCheck4
import D4.C3CellDetCheck5
import D4.C3CellDetCheck6
import D4.C3CellDetCheck7
import D4.C3CellDetCheck8
import D4.C3CellDetCheck9
import D4.C3CellDetCheck10
import D4.C3CellDetCheck11
import D4.C3CellDetCheck12
import D4.C3CellDetCheck13
import D4.C3CellDetCheck14
import D4.C3CellDetCheck15
import D4.C3CellDetCheck16
import D4.C3CellDetCheck17
import D4.C3CellDetCheck18
import D4.C3CellDetCheck19
import D4.C3CellDetCheck20
import D4.C3CellDetCheck21
import D4.C3CellDetCheck22
import D4.C3CellDetCheck23
import D4.C3CellDetCheck24
import D4.C3CellDetCheck25
import D4.C3CellDetCheck26
import D4.C3CellDetCheck27
import D4.C3CellDetCheck28
import D4.C3CellDetCheck29
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3_support_rows : ∀ i : Fin 582,
    (integerSupportRows c3FacetNormal (c3Cell i) (c3DetCoordinate i)).det = c3DetSign i ∧
    (c3DetSign i)^2 = 1 ∧
    (∀ j, 0 ≤ c3DetSign i * (c3VertexCoefficients (c3Cell i).v j (c3DetCoordinate i) -
      c3VertexCoefficients (c3Cell i).u j (c3DetCoordinate i))) ∧
    (∃ j, 0 < c3DetSign i * (c3VertexCoefficients (c3Cell i).v j (c3DetCoordinate i) -
      c3VertexCoefficients (c3Cell i).u j (c3DetCoordinate i))) := by
  intro t
  have ht := t.isLt
  have hb : t.val / 20 < 30 := by omega
  interval_cases hblock : t.val / 20
  · have hr : t.val % 20 < 20 := by omega
    have hi : 0 + t.val % 20 < 582 := by omega
    have he : (⟨0 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_0 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 20 + t.val % 20 < 582 := by omega
    have he : (⟨20 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_1 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 40 + t.val % 20 < 582 := by omega
    have he : (⟨40 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_2 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 60 + t.val % 20 < 582 := by omega
    have he : (⟨60 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_3 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 80 + t.val % 20 < 582 := by omega
    have he : (⟨80 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_4 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 100 + t.val % 20 < 582 := by omega
    have he : (⟨100 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_5 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 120 + t.val % 20 < 582 := by omega
    have he : (⟨120 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_6 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 140 + t.val % 20 < 582 := by omega
    have he : (⟨140 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_7 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 160 + t.val % 20 < 582 := by omega
    have he : (⟨160 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_8 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 180 + t.val % 20 < 582 := by omega
    have he : (⟨180 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_9 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 200 + t.val % 20 < 582 := by omega
    have he : (⟨200 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_10 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 220 + t.val % 20 < 582 := by omega
    have he : (⟨220 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_11 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 240 + t.val % 20 < 582 := by omega
    have he : (⟨240 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_12 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 260 + t.val % 20 < 582 := by omega
    have he : (⟨260 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_13 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 280 + t.val % 20 < 582 := by omega
    have he : (⟨280 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_14 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 300 + t.val % 20 < 582 := by omega
    have he : (⟨300 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_15 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 320 + t.val % 20 < 582 := by omega
    have he : (⟨320 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_16 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 340 + t.val % 20 < 582 := by omega
    have he : (⟨340 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_17 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 360 + t.val % 20 < 582 := by omega
    have he : (⟨360 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_18 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 380 + t.val % 20 < 582 := by omega
    have he : (⟨380 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_19 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 400 + t.val % 20 < 582 := by omega
    have he : (⟨400 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_20 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 420 + t.val % 20 < 582 := by omega
    have he : (⟨420 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_21 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 440 + t.val % 20 < 582 := by omega
    have he : (⟨440 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_22 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 460 + t.val % 20 < 582 := by omega
    have he : (⟨460 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_23 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 480 + t.val % 20 < 582 := by omega
    have he : (⟨480 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_24 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 500 + t.val % 20 < 582 := by omega
    have he : (⟨500 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_25 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 520 + t.val % 20 < 582 := by omega
    have he : (⟨520 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_26 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 540 + t.val % 20 < 582 := by omega
    have he : (⟨540 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_27 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 560 + t.val % 20 < 582 := by omega
    have he : (⟨560 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_28 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 2 := by omega
    have hi : 580 + t.val % 20 < 582 := by omega
    have he : (⟨580 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_support_rows_29 ⟨t.val % 20,hr⟩)

theorem c3_det_polynomial : ∀ i : Fin 582,
    cellFactorProduct c3IntegerGenerators c3VertexCoefficients c3FacetNormal
      (c3Cell i) (c3DetCoordinate i) (c3DetSign i) = c3CellDetPoly i := by
  intro t
  have ht := t.isLt
  have hb : t.val / 20 < 30 := by omega
  interval_cases hblock : t.val / 20
  · have hr : t.val % 20 < 20 := by omega
    have hi : 0 + t.val % 20 < 582 := by omega
    have he : (⟨0 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_0 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 20 + t.val % 20 < 582 := by omega
    have he : (⟨20 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_1 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 40 + t.val % 20 < 582 := by omega
    have he : (⟨40 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_2 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 60 + t.val % 20 < 582 := by omega
    have he : (⟨60 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_3 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 80 + t.val % 20 < 582 := by omega
    have he : (⟨80 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_4 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 100 + t.val % 20 < 582 := by omega
    have he : (⟨100 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_5 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 120 + t.val % 20 < 582 := by omega
    have he : (⟨120 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_6 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 140 + t.val % 20 < 582 := by omega
    have he : (⟨140 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_7 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 160 + t.val % 20 < 582 := by omega
    have he : (⟨160 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_8 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 180 + t.val % 20 < 582 := by omega
    have he : (⟨180 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_9 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 200 + t.val % 20 < 582 := by omega
    have he : (⟨200 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_10 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 220 + t.val % 20 < 582 := by omega
    have he : (⟨220 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_11 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 240 + t.val % 20 < 582 := by omega
    have he : (⟨240 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_12 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 260 + t.val % 20 < 582 := by omega
    have he : (⟨260 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_13 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 280 + t.val % 20 < 582 := by omega
    have he : (⟨280 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_14 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 300 + t.val % 20 < 582 := by omega
    have he : (⟨300 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_15 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 320 + t.val % 20 < 582 := by omega
    have he : (⟨320 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_16 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 340 + t.val % 20 < 582 := by omega
    have he : (⟨340 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_17 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 360 + t.val % 20 < 582 := by omega
    have he : (⟨360 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_18 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 380 + t.val % 20 < 582 := by omega
    have he : (⟨380 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_19 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 400 + t.val % 20 < 582 := by omega
    have he : (⟨400 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_20 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 420 + t.val % 20 < 582 := by omega
    have he : (⟨420 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_21 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 440 + t.val % 20 < 582 := by omega
    have he : (⟨440 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_22 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 460 + t.val % 20 < 582 := by omega
    have he : (⟨460 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_23 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 480 + t.val % 20 < 582 := by omega
    have he : (⟨480 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_24 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 500 + t.val % 20 < 582 := by omega
    have he : (⟨500 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_25 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 520 + t.val % 20 < 582 := by omega
    have he : (⟨520 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_26 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 540 + t.val % 20 < 582 := by omega
    have he : (⟨540 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_27 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 560 + t.val % 20 < 582 := by omega
    have he : (⟨560 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_28 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 2 := by omega
    have hi : 580 + t.val % 20 < 582 := by omega
    have he : (⟨580 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_det_polynomial_29 ⟨t.val % 20,hr⟩)

end D4.Secondary
