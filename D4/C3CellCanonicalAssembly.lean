import D4.C3CellCanonical0
import D4.C3CellCanonical1
import D4.C3CellCanonical2
import D4.C3CellCanonical3
import D4.C3CellCanonical4
import D4.C3CellCanonical5
import D4.C3CellCanonical6
import D4.C3CellCanonical7
import D4.C3CellCanonical8
import D4.C3CellCanonical9
import D4.C3CellCanonical10
import D4.C3CellCanonical11
import D4.C3CellCanonical12
import D4.C3CellCanonical13
import D4.C3CellCanonical14
import D4.C3CellCanonical15
import D4.C3CellCanonical16
import D4.C3CellCanonical17
import D4.C3CellCanonical18
import D4.C3CellCanonical19
import D4.C3CellCanonical20
import D4.C3CellCanonical21
import D4.C3CellCanonical22
import D4.C3CellCanonical23
import D4.C3CellCanonical24
import D4.C3CellCanonical25
import D4.C3CellCanonical26
import D4.C3CellCanonical27
import D4.C3CellCanonical28
import D4.C3CellCanonical29
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal MeasureTheory
theorem c3_face_canonical : ∀ t g,
    c3FacetMask (c3Cell t).f &&& c3FacetMask g =
      c3FacetMask (c3Cell t).f &&& c3FacetMask (c3Cell t).g → (c3Cell t).g ≤ g  := by
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
    simpa only [he] using (c3_face_canonical_0 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 20 + t.val % 20 < 582 := by omega
    have he : (⟨20 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_1 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 40 + t.val % 20 < 582 := by omega
    have he : (⟨40 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_2 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 60 + t.val % 20 < 582 := by omega
    have he : (⟨60 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_3 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 80 + t.val % 20 < 582 := by omega
    have he : (⟨80 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_4 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 100 + t.val % 20 < 582 := by omega
    have he : (⟨100 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_5 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 120 + t.val % 20 < 582 := by omega
    have he : (⟨120 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_6 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 140 + t.val % 20 < 582 := by omega
    have he : (⟨140 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_7 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 160 + t.val % 20 < 582 := by omega
    have he : (⟨160 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_8 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 180 + t.val % 20 < 582 := by omega
    have he : (⟨180 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_9 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 200 + t.val % 20 < 582 := by omega
    have he : (⟨200 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_10 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 220 + t.val % 20 < 582 := by omega
    have he : (⟨220 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_11 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 240 + t.val % 20 < 582 := by omega
    have he : (⟨240 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_12 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 260 + t.val % 20 < 582 := by omega
    have he : (⟨260 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_13 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 280 + t.val % 20 < 582 := by omega
    have he : (⟨280 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_14 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 300 + t.val % 20 < 582 := by omega
    have he : (⟨300 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_15 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 320 + t.val % 20 < 582 := by omega
    have he : (⟨320 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_16 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 340 + t.val % 20 < 582 := by omega
    have he : (⟨340 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_17 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 360 + t.val % 20 < 582 := by omega
    have he : (⟨360 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_18 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 380 + t.val % 20 < 582 := by omega
    have he : (⟨380 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_19 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 400 + t.val % 20 < 582 := by omega
    have he : (⟨400 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_20 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 420 + t.val % 20 < 582 := by omega
    have he : (⟨420 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_21 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 440 + t.val % 20 < 582 := by omega
    have he : (⟨440 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_22 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 460 + t.val % 20 < 582 := by omega
    have he : (⟨460 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_23 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 480 + t.val % 20 < 582 := by omega
    have he : (⟨480 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_24 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 500 + t.val % 20 < 582 := by omega
    have he : (⟨500 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_25 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 520 + t.val % 20 < 582 := by omega
    have he : (⟨520 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_26 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 540 + t.val % 20 < 582 := by omega
    have he : (⟨540 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_27 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 560 + t.val % 20 < 582 := by omega
    have he : (⟨560 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_28 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 2 := by omega
    have hi : 580 + t.val % 20 < 582 := by omega
    have he : (⟨580 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_face_canonical_29 ⟨t.val % 20,hr⟩)
theorem c3_edge_canonical : ∀ t h,
    c3FacetMask (c3Cell t).f &&& c3FacetMask (c3Cell t).g &&& c3FacetMask h =
      c3FacetMask (c3Cell t).f &&& c3FacetMask (c3Cell t).g &&& c3FacetMask (c3Cell t).h →
        (c3Cell t).h ≤ h  := by
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
    simpa only [he] using (c3_edge_canonical_0 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 20 + t.val % 20 < 582 := by omega
    have he : (⟨20 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_1 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 40 + t.val % 20 < 582 := by omega
    have he : (⟨40 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_2 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 60 + t.val % 20 < 582 := by omega
    have he : (⟨60 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_3 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 80 + t.val % 20 < 582 := by omega
    have he : (⟨80 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_4 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 100 + t.val % 20 < 582 := by omega
    have he : (⟨100 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_5 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 120 + t.val % 20 < 582 := by omega
    have he : (⟨120 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_6 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 140 + t.val % 20 < 582 := by omega
    have he : (⟨140 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_7 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 160 + t.val % 20 < 582 := by omega
    have he : (⟨160 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_8 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 180 + t.val % 20 < 582 := by omega
    have he : (⟨180 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_9 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 200 + t.val % 20 < 582 := by omega
    have he : (⟨200 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_10 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 220 + t.val % 20 < 582 := by omega
    have he : (⟨220 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_11 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 240 + t.val % 20 < 582 := by omega
    have he : (⟨240 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_12 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 260 + t.val % 20 < 582 := by omega
    have he : (⟨260 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_13 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 280 + t.val % 20 < 582 := by omega
    have he : (⟨280 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_14 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 300 + t.val % 20 < 582 := by omega
    have he : (⟨300 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_15 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 320 + t.val % 20 < 582 := by omega
    have he : (⟨320 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_16 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 340 + t.val % 20 < 582 := by omega
    have he : (⟨340 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_17 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 360 + t.val % 20 < 582 := by omega
    have he : (⟨360 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_18 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 380 + t.val % 20 < 582 := by omega
    have he : (⟨380 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_19 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 400 + t.val % 20 < 582 := by omega
    have he : (⟨400 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_20 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 420 + t.val % 20 < 582 := by omega
    have he : (⟨420 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_21 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 440 + t.val % 20 < 582 := by omega
    have he : (⟨440 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_22 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 460 + t.val % 20 < 582 := by omega
    have he : (⟨460 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_23 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 480 + t.val % 20 < 582 := by omega
    have he : (⟨480 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_24 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 500 + t.val % 20 < 582 := by omega
    have he : (⟨500 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_25 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 520 + t.val % 20 < 582 := by omega
    have he : (⟨520 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_26 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 540 + t.val % 20 < 582 := by omega
    have he : (⟨540 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_27 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 20 := by omega
    have hi : 560 + t.val % 20 < 582 := by omega
    have he : (⟨560 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_28 ⟨t.val % 20,hr⟩)
  · have hr : t.val % 20 < 2 := by omega
    have hi : 580 + t.val % 20 < 582 := by omega
    have he : (⟨580 + t.val % 20, hi⟩ : Fin 582) = t := by
      apply Fin.ext
      dsimp
      omega
    simpa only [he] using (c3_edge_canonical_29 ⟨t.val % 20,hr⟩)
end D4.Secondary
