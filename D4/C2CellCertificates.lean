import D4.C2CellIncidence
import D4.C23CellRealization
import D4.PrincipalDualRegion
import D4.C2CellCanonical0
import D4.C2CellCanonical1
import D4.C2CellCanonical2
import D4.C2CellCanonical3
import D4.C2CellCanonical4
import D4.C2CellCanonical5
import D4.C2CellCanonical6
import D4.C2CellCanonical7
import D4.C2CellCanonical8
import D4.C2CellCanonical9
import D4.C2CellCanonical10
import D4.C2CellCanonical11
import D4.C2CellCanonical12
import D4.C2CellCanonical13
import D4.C2CellCanonical14
import D4.C2CellCanonical15
import D4.C2CellCanonical16
import D4.C2CellCanonical17
import D4.C2CellCanonical18
import D4.C2CellCanonical19
import D4.C2CellCanonical20
import D4.C2CellCanonical21
import D4.C2CellCanonical22
import D4.C2CellCanonical23
import D4.C2CellCanonical24
import D4.C2CellCanonical25
import D4.C2CellCanonical26
import D4.C2CellCanonical27
import D4.C2CellCanonical28
import D4.C2FacetSlack00
import D4.C2FacetSlack01
import D4.C2FacetSlack02
import D4.C2FacetSlack03
import D4.C2FacetSlack04
import D4.C2FacetSlack05
import D4.C2FacetSlack06
import D4.C2FacetSlack07
import D4.C2FacetSlack08
import D4.C2FacetSlack09
import D4.C2FacetSlack10
import D4.C2FacetSlack11
import D4.C2FacetSlack12
import D4.C2FacetSlack13
import D4.C2FacetSlack14
import D4.C2FacetSlack15
import D4.C2FacetSlack16
import D4.C2FacetSlack17
import D4.C2FacetSlack18
import D4.C2FacetSlack19
import D4.C2FacetSlack20
import D4.C2FacetSlack21
import D4.C2FacetSlack22
import D4.C2FacetSlack23
import D4.C2FacetSlack24
import D4.C2FacetSlack25
import D4.C2FacetSlack26
import D4.C2FacetSlack27
import D4.C2FacetSlack28
import D4.C2FacetSlack29
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal MeasureTheory
theorem c2_face_canonical : ∀ t g,
    c2FacetMask (c2Cell t).f &&& c2FacetMask g =
      c2FacetMask (c2Cell t).f &&& c2FacetMask (c2Cell t).g → (c2Cell t).g ≤ g := by
  intro t
  fin_cases t
  · exact c2_face_canonical_0 ⟨0,by decide⟩
  · exact c2_face_canonical_0 ⟨1,by decide⟩
  · exact c2_face_canonical_0 ⟨2,by decide⟩
  · exact c2_face_canonical_0 ⟨3,by decide⟩
  · exact c2_face_canonical_0 ⟨4,by decide⟩
  · exact c2_face_canonical_0 ⟨5,by decide⟩
  · exact c2_face_canonical_0 ⟨6,by decide⟩
  · exact c2_face_canonical_0 ⟨7,by decide⟩
  · exact c2_face_canonical_0 ⟨8,by decide⟩
  · exact c2_face_canonical_0 ⟨9,by decide⟩
  · exact c2_face_canonical_0 ⟨10,by decide⟩
  · exact c2_face_canonical_0 ⟨11,by decide⟩
  · exact c2_face_canonical_0 ⟨12,by decide⟩
  · exact c2_face_canonical_0 ⟨13,by decide⟩
  · exact c2_face_canonical_0 ⟨14,by decide⟩
  · exact c2_face_canonical_0 ⟨15,by decide⟩
  · exact c2_face_canonical_0 ⟨16,by decide⟩
  · exact c2_face_canonical_0 ⟨17,by decide⟩
  · exact c2_face_canonical_0 ⟨18,by decide⟩
  · exact c2_face_canonical_0 ⟨19,by decide⟩
  · exact c2_face_canonical_1 ⟨0,by decide⟩
  · exact c2_face_canonical_1 ⟨1,by decide⟩
  · exact c2_face_canonical_1 ⟨2,by decide⟩
  · exact c2_face_canonical_1 ⟨3,by decide⟩
  · exact c2_face_canonical_1 ⟨4,by decide⟩
  · exact c2_face_canonical_1 ⟨5,by decide⟩
  · exact c2_face_canonical_1 ⟨6,by decide⟩
  · exact c2_face_canonical_1 ⟨7,by decide⟩
  · exact c2_face_canonical_1 ⟨8,by decide⟩
  · exact c2_face_canonical_1 ⟨9,by decide⟩
  · exact c2_face_canonical_1 ⟨10,by decide⟩
  · exact c2_face_canonical_1 ⟨11,by decide⟩
  · exact c2_face_canonical_1 ⟨12,by decide⟩
  · exact c2_face_canonical_1 ⟨13,by decide⟩
  · exact c2_face_canonical_1 ⟨14,by decide⟩
  · exact c2_face_canonical_1 ⟨15,by decide⟩
  · exact c2_face_canonical_1 ⟨16,by decide⟩
  · exact c2_face_canonical_1 ⟨17,by decide⟩
  · exact c2_face_canonical_1 ⟨18,by decide⟩
  · exact c2_face_canonical_1 ⟨19,by decide⟩
  · exact c2_face_canonical_2 ⟨0,by decide⟩
  · exact c2_face_canonical_2 ⟨1,by decide⟩
  · exact c2_face_canonical_2 ⟨2,by decide⟩
  · exact c2_face_canonical_2 ⟨3,by decide⟩
  · exact c2_face_canonical_2 ⟨4,by decide⟩
  · exact c2_face_canonical_2 ⟨5,by decide⟩
  · exact c2_face_canonical_2 ⟨6,by decide⟩
  · exact c2_face_canonical_2 ⟨7,by decide⟩
  · exact c2_face_canonical_2 ⟨8,by decide⟩
  · exact c2_face_canonical_2 ⟨9,by decide⟩
  · exact c2_face_canonical_2 ⟨10,by decide⟩
  · exact c2_face_canonical_2 ⟨11,by decide⟩
  · exact c2_face_canonical_2 ⟨12,by decide⟩
  · exact c2_face_canonical_2 ⟨13,by decide⟩
  · exact c2_face_canonical_2 ⟨14,by decide⟩
  · exact c2_face_canonical_2 ⟨15,by decide⟩
  · exact c2_face_canonical_2 ⟨16,by decide⟩
  · exact c2_face_canonical_2 ⟨17,by decide⟩
  · exact c2_face_canonical_2 ⟨18,by decide⟩
  · exact c2_face_canonical_2 ⟨19,by decide⟩
  · exact c2_face_canonical_3 ⟨0,by decide⟩
  · exact c2_face_canonical_3 ⟨1,by decide⟩
  · exact c2_face_canonical_3 ⟨2,by decide⟩
  · exact c2_face_canonical_3 ⟨3,by decide⟩
  · exact c2_face_canonical_3 ⟨4,by decide⟩
  · exact c2_face_canonical_3 ⟨5,by decide⟩
  · exact c2_face_canonical_3 ⟨6,by decide⟩
  · exact c2_face_canonical_3 ⟨7,by decide⟩
  · exact c2_face_canonical_3 ⟨8,by decide⟩
  · exact c2_face_canonical_3 ⟨9,by decide⟩
  · exact c2_face_canonical_3 ⟨10,by decide⟩
  · exact c2_face_canonical_3 ⟨11,by decide⟩
  · exact c2_face_canonical_3 ⟨12,by decide⟩
  · exact c2_face_canonical_3 ⟨13,by decide⟩
  · exact c2_face_canonical_3 ⟨14,by decide⟩
  · exact c2_face_canonical_3 ⟨15,by decide⟩
  · exact c2_face_canonical_3 ⟨16,by decide⟩
  · exact c2_face_canonical_3 ⟨17,by decide⟩
  · exact c2_face_canonical_3 ⟨18,by decide⟩
  · exact c2_face_canonical_3 ⟨19,by decide⟩
  · exact c2_face_canonical_4 ⟨0,by decide⟩
  · exact c2_face_canonical_4 ⟨1,by decide⟩
  · exact c2_face_canonical_4 ⟨2,by decide⟩
  · exact c2_face_canonical_4 ⟨3,by decide⟩
  · exact c2_face_canonical_4 ⟨4,by decide⟩
  · exact c2_face_canonical_4 ⟨5,by decide⟩
  · exact c2_face_canonical_4 ⟨6,by decide⟩
  · exact c2_face_canonical_4 ⟨7,by decide⟩
  · exact c2_face_canonical_4 ⟨8,by decide⟩
  · exact c2_face_canonical_4 ⟨9,by decide⟩
  · exact c2_face_canonical_4 ⟨10,by decide⟩
  · exact c2_face_canonical_4 ⟨11,by decide⟩
  · exact c2_face_canonical_4 ⟨12,by decide⟩
  · exact c2_face_canonical_4 ⟨13,by decide⟩
  · exact c2_face_canonical_4 ⟨14,by decide⟩
  · exact c2_face_canonical_4 ⟨15,by decide⟩
  · exact c2_face_canonical_4 ⟨16,by decide⟩
  · exact c2_face_canonical_4 ⟨17,by decide⟩
  · exact c2_face_canonical_4 ⟨18,by decide⟩
  · exact c2_face_canonical_4 ⟨19,by decide⟩
  · exact c2_face_canonical_5 ⟨0,by decide⟩
  · exact c2_face_canonical_5 ⟨1,by decide⟩
  · exact c2_face_canonical_5 ⟨2,by decide⟩
  · exact c2_face_canonical_5 ⟨3,by decide⟩
  · exact c2_face_canonical_5 ⟨4,by decide⟩
  · exact c2_face_canonical_5 ⟨5,by decide⟩
  · exact c2_face_canonical_5 ⟨6,by decide⟩
  · exact c2_face_canonical_5 ⟨7,by decide⟩
  · exact c2_face_canonical_5 ⟨8,by decide⟩
  · exact c2_face_canonical_5 ⟨9,by decide⟩
  · exact c2_face_canonical_5 ⟨10,by decide⟩
  · exact c2_face_canonical_5 ⟨11,by decide⟩
  · exact c2_face_canonical_5 ⟨12,by decide⟩
  · exact c2_face_canonical_5 ⟨13,by decide⟩
  · exact c2_face_canonical_5 ⟨14,by decide⟩
  · exact c2_face_canonical_5 ⟨15,by decide⟩
  · exact c2_face_canonical_5 ⟨16,by decide⟩
  · exact c2_face_canonical_5 ⟨17,by decide⟩
  · exact c2_face_canonical_5 ⟨18,by decide⟩
  · exact c2_face_canonical_5 ⟨19,by decide⟩
  · exact c2_face_canonical_6 ⟨0,by decide⟩
  · exact c2_face_canonical_6 ⟨1,by decide⟩
  · exact c2_face_canonical_6 ⟨2,by decide⟩
  · exact c2_face_canonical_6 ⟨3,by decide⟩
  · exact c2_face_canonical_6 ⟨4,by decide⟩
  · exact c2_face_canonical_6 ⟨5,by decide⟩
  · exact c2_face_canonical_6 ⟨6,by decide⟩
  · exact c2_face_canonical_6 ⟨7,by decide⟩
  · exact c2_face_canonical_6 ⟨8,by decide⟩
  · exact c2_face_canonical_6 ⟨9,by decide⟩
  · exact c2_face_canonical_6 ⟨10,by decide⟩
  · exact c2_face_canonical_6 ⟨11,by decide⟩
  · exact c2_face_canonical_6 ⟨12,by decide⟩
  · exact c2_face_canonical_6 ⟨13,by decide⟩
  · exact c2_face_canonical_6 ⟨14,by decide⟩
  · exact c2_face_canonical_6 ⟨15,by decide⟩
  · exact c2_face_canonical_6 ⟨16,by decide⟩
  · exact c2_face_canonical_6 ⟨17,by decide⟩
  · exact c2_face_canonical_6 ⟨18,by decide⟩
  · exact c2_face_canonical_6 ⟨19,by decide⟩
  · exact c2_face_canonical_7 ⟨0,by decide⟩
  · exact c2_face_canonical_7 ⟨1,by decide⟩
  · exact c2_face_canonical_7 ⟨2,by decide⟩
  · exact c2_face_canonical_7 ⟨3,by decide⟩
  · exact c2_face_canonical_7 ⟨4,by decide⟩
  · exact c2_face_canonical_7 ⟨5,by decide⟩
  · exact c2_face_canonical_7 ⟨6,by decide⟩
  · exact c2_face_canonical_7 ⟨7,by decide⟩
  · exact c2_face_canonical_7 ⟨8,by decide⟩
  · exact c2_face_canonical_7 ⟨9,by decide⟩
  · exact c2_face_canonical_7 ⟨10,by decide⟩
  · exact c2_face_canonical_7 ⟨11,by decide⟩
  · exact c2_face_canonical_7 ⟨12,by decide⟩
  · exact c2_face_canonical_7 ⟨13,by decide⟩
  · exact c2_face_canonical_7 ⟨14,by decide⟩
  · exact c2_face_canonical_7 ⟨15,by decide⟩
  · exact c2_face_canonical_7 ⟨16,by decide⟩
  · exact c2_face_canonical_7 ⟨17,by decide⟩
  · exact c2_face_canonical_7 ⟨18,by decide⟩
  · exact c2_face_canonical_7 ⟨19,by decide⟩
  · exact c2_face_canonical_8 ⟨0,by decide⟩
  · exact c2_face_canonical_8 ⟨1,by decide⟩
  · exact c2_face_canonical_8 ⟨2,by decide⟩
  · exact c2_face_canonical_8 ⟨3,by decide⟩
  · exact c2_face_canonical_8 ⟨4,by decide⟩
  · exact c2_face_canonical_8 ⟨5,by decide⟩
  · exact c2_face_canonical_8 ⟨6,by decide⟩
  · exact c2_face_canonical_8 ⟨7,by decide⟩
  · exact c2_face_canonical_8 ⟨8,by decide⟩
  · exact c2_face_canonical_8 ⟨9,by decide⟩
  · exact c2_face_canonical_8 ⟨10,by decide⟩
  · exact c2_face_canonical_8 ⟨11,by decide⟩
  · exact c2_face_canonical_8 ⟨12,by decide⟩
  · exact c2_face_canonical_8 ⟨13,by decide⟩
  · exact c2_face_canonical_8 ⟨14,by decide⟩
  · exact c2_face_canonical_8 ⟨15,by decide⟩
  · exact c2_face_canonical_8 ⟨16,by decide⟩
  · exact c2_face_canonical_8 ⟨17,by decide⟩
  · exact c2_face_canonical_8 ⟨18,by decide⟩
  · exact c2_face_canonical_8 ⟨19,by decide⟩
  · exact c2_face_canonical_9 ⟨0,by decide⟩
  · exact c2_face_canonical_9 ⟨1,by decide⟩
  · exact c2_face_canonical_9 ⟨2,by decide⟩
  · exact c2_face_canonical_9 ⟨3,by decide⟩
  · exact c2_face_canonical_9 ⟨4,by decide⟩
  · exact c2_face_canonical_9 ⟨5,by decide⟩
  · exact c2_face_canonical_9 ⟨6,by decide⟩
  · exact c2_face_canonical_9 ⟨7,by decide⟩
  · exact c2_face_canonical_9 ⟨8,by decide⟩
  · exact c2_face_canonical_9 ⟨9,by decide⟩
  · exact c2_face_canonical_9 ⟨10,by decide⟩
  · exact c2_face_canonical_9 ⟨11,by decide⟩
  · exact c2_face_canonical_9 ⟨12,by decide⟩
  · exact c2_face_canonical_9 ⟨13,by decide⟩
  · exact c2_face_canonical_9 ⟨14,by decide⟩
  · exact c2_face_canonical_9 ⟨15,by decide⟩
  · exact c2_face_canonical_9 ⟨16,by decide⟩
  · exact c2_face_canonical_9 ⟨17,by decide⟩
  · exact c2_face_canonical_9 ⟨18,by decide⟩
  · exact c2_face_canonical_9 ⟨19,by decide⟩
  · exact c2_face_canonical_10 ⟨0,by decide⟩
  · exact c2_face_canonical_10 ⟨1,by decide⟩
  · exact c2_face_canonical_10 ⟨2,by decide⟩
  · exact c2_face_canonical_10 ⟨3,by decide⟩
  · exact c2_face_canonical_10 ⟨4,by decide⟩
  · exact c2_face_canonical_10 ⟨5,by decide⟩
  · exact c2_face_canonical_10 ⟨6,by decide⟩
  · exact c2_face_canonical_10 ⟨7,by decide⟩
  · exact c2_face_canonical_10 ⟨8,by decide⟩
  · exact c2_face_canonical_10 ⟨9,by decide⟩
  · exact c2_face_canonical_10 ⟨10,by decide⟩
  · exact c2_face_canonical_10 ⟨11,by decide⟩
  · exact c2_face_canonical_10 ⟨12,by decide⟩
  · exact c2_face_canonical_10 ⟨13,by decide⟩
  · exact c2_face_canonical_10 ⟨14,by decide⟩
  · exact c2_face_canonical_10 ⟨15,by decide⟩
  · exact c2_face_canonical_10 ⟨16,by decide⟩
  · exact c2_face_canonical_10 ⟨17,by decide⟩
  · exact c2_face_canonical_10 ⟨18,by decide⟩
  · exact c2_face_canonical_10 ⟨19,by decide⟩
  · exact c2_face_canonical_11 ⟨0,by decide⟩
  · exact c2_face_canonical_11 ⟨1,by decide⟩
  · exact c2_face_canonical_11 ⟨2,by decide⟩
  · exact c2_face_canonical_11 ⟨3,by decide⟩
  · exact c2_face_canonical_11 ⟨4,by decide⟩
  · exact c2_face_canonical_11 ⟨5,by decide⟩
  · exact c2_face_canonical_11 ⟨6,by decide⟩
  · exact c2_face_canonical_11 ⟨7,by decide⟩
  · exact c2_face_canonical_11 ⟨8,by decide⟩
  · exact c2_face_canonical_11 ⟨9,by decide⟩
  · exact c2_face_canonical_11 ⟨10,by decide⟩
  · exact c2_face_canonical_11 ⟨11,by decide⟩
  · exact c2_face_canonical_11 ⟨12,by decide⟩
  · exact c2_face_canonical_11 ⟨13,by decide⟩
  · exact c2_face_canonical_11 ⟨14,by decide⟩
  · exact c2_face_canonical_11 ⟨15,by decide⟩
  · exact c2_face_canonical_11 ⟨16,by decide⟩
  · exact c2_face_canonical_11 ⟨17,by decide⟩
  · exact c2_face_canonical_11 ⟨18,by decide⟩
  · exact c2_face_canonical_11 ⟨19,by decide⟩
  · exact c2_face_canonical_12 ⟨0,by decide⟩
  · exact c2_face_canonical_12 ⟨1,by decide⟩
  · exact c2_face_canonical_12 ⟨2,by decide⟩
  · exact c2_face_canonical_12 ⟨3,by decide⟩
  · exact c2_face_canonical_12 ⟨4,by decide⟩
  · exact c2_face_canonical_12 ⟨5,by decide⟩
  · exact c2_face_canonical_12 ⟨6,by decide⟩
  · exact c2_face_canonical_12 ⟨7,by decide⟩
  · exact c2_face_canonical_12 ⟨8,by decide⟩
  · exact c2_face_canonical_12 ⟨9,by decide⟩
  · exact c2_face_canonical_12 ⟨10,by decide⟩
  · exact c2_face_canonical_12 ⟨11,by decide⟩
  · exact c2_face_canonical_12 ⟨12,by decide⟩
  · exact c2_face_canonical_12 ⟨13,by decide⟩
  · exact c2_face_canonical_12 ⟨14,by decide⟩
  · exact c2_face_canonical_12 ⟨15,by decide⟩
  · exact c2_face_canonical_12 ⟨16,by decide⟩
  · exact c2_face_canonical_12 ⟨17,by decide⟩
  · exact c2_face_canonical_12 ⟨18,by decide⟩
  · exact c2_face_canonical_12 ⟨19,by decide⟩
  · exact c2_face_canonical_13 ⟨0,by decide⟩
  · exact c2_face_canonical_13 ⟨1,by decide⟩
  · exact c2_face_canonical_13 ⟨2,by decide⟩
  · exact c2_face_canonical_13 ⟨3,by decide⟩
  · exact c2_face_canonical_13 ⟨4,by decide⟩
  · exact c2_face_canonical_13 ⟨5,by decide⟩
  · exact c2_face_canonical_13 ⟨6,by decide⟩
  · exact c2_face_canonical_13 ⟨7,by decide⟩
  · exact c2_face_canonical_13 ⟨8,by decide⟩
  · exact c2_face_canonical_13 ⟨9,by decide⟩
  · exact c2_face_canonical_13 ⟨10,by decide⟩
  · exact c2_face_canonical_13 ⟨11,by decide⟩
  · exact c2_face_canonical_13 ⟨12,by decide⟩
  · exact c2_face_canonical_13 ⟨13,by decide⟩
  · exact c2_face_canonical_13 ⟨14,by decide⟩
  · exact c2_face_canonical_13 ⟨15,by decide⟩
  · exact c2_face_canonical_13 ⟨16,by decide⟩
  · exact c2_face_canonical_13 ⟨17,by decide⟩
  · exact c2_face_canonical_13 ⟨18,by decide⟩
  · exact c2_face_canonical_13 ⟨19,by decide⟩
  · exact c2_face_canonical_14 ⟨0,by decide⟩
  · exact c2_face_canonical_14 ⟨1,by decide⟩
  · exact c2_face_canonical_14 ⟨2,by decide⟩
  · exact c2_face_canonical_14 ⟨3,by decide⟩
  · exact c2_face_canonical_14 ⟨4,by decide⟩
  · exact c2_face_canonical_14 ⟨5,by decide⟩
  · exact c2_face_canonical_14 ⟨6,by decide⟩
  · exact c2_face_canonical_14 ⟨7,by decide⟩
  · exact c2_face_canonical_14 ⟨8,by decide⟩
  · exact c2_face_canonical_14 ⟨9,by decide⟩
  · exact c2_face_canonical_14 ⟨10,by decide⟩
  · exact c2_face_canonical_14 ⟨11,by decide⟩
  · exact c2_face_canonical_14 ⟨12,by decide⟩
  · exact c2_face_canonical_14 ⟨13,by decide⟩
  · exact c2_face_canonical_14 ⟨14,by decide⟩
  · exact c2_face_canonical_14 ⟨15,by decide⟩
  · exact c2_face_canonical_14 ⟨16,by decide⟩
  · exact c2_face_canonical_14 ⟨17,by decide⟩
  · exact c2_face_canonical_14 ⟨18,by decide⟩
  · exact c2_face_canonical_14 ⟨19,by decide⟩
  · exact c2_face_canonical_15 ⟨0,by decide⟩
  · exact c2_face_canonical_15 ⟨1,by decide⟩
  · exact c2_face_canonical_15 ⟨2,by decide⟩
  · exact c2_face_canonical_15 ⟨3,by decide⟩
  · exact c2_face_canonical_15 ⟨4,by decide⟩
  · exact c2_face_canonical_15 ⟨5,by decide⟩
  · exact c2_face_canonical_15 ⟨6,by decide⟩
  · exact c2_face_canonical_15 ⟨7,by decide⟩
  · exact c2_face_canonical_15 ⟨8,by decide⟩
  · exact c2_face_canonical_15 ⟨9,by decide⟩
  · exact c2_face_canonical_15 ⟨10,by decide⟩
  · exact c2_face_canonical_15 ⟨11,by decide⟩
  · exact c2_face_canonical_15 ⟨12,by decide⟩
  · exact c2_face_canonical_15 ⟨13,by decide⟩
  · exact c2_face_canonical_15 ⟨14,by decide⟩
  · exact c2_face_canonical_15 ⟨15,by decide⟩
  · exact c2_face_canonical_15 ⟨16,by decide⟩
  · exact c2_face_canonical_15 ⟨17,by decide⟩
  · exact c2_face_canonical_15 ⟨18,by decide⟩
  · exact c2_face_canonical_15 ⟨19,by decide⟩
  · exact c2_face_canonical_16 ⟨0,by decide⟩
  · exact c2_face_canonical_16 ⟨1,by decide⟩
  · exact c2_face_canonical_16 ⟨2,by decide⟩
  · exact c2_face_canonical_16 ⟨3,by decide⟩
  · exact c2_face_canonical_16 ⟨4,by decide⟩
  · exact c2_face_canonical_16 ⟨5,by decide⟩
  · exact c2_face_canonical_16 ⟨6,by decide⟩
  · exact c2_face_canonical_16 ⟨7,by decide⟩
  · exact c2_face_canonical_16 ⟨8,by decide⟩
  · exact c2_face_canonical_16 ⟨9,by decide⟩
  · exact c2_face_canonical_16 ⟨10,by decide⟩
  · exact c2_face_canonical_16 ⟨11,by decide⟩
  · exact c2_face_canonical_16 ⟨12,by decide⟩
  · exact c2_face_canonical_16 ⟨13,by decide⟩
  · exact c2_face_canonical_16 ⟨14,by decide⟩
  · exact c2_face_canonical_16 ⟨15,by decide⟩
  · exact c2_face_canonical_16 ⟨16,by decide⟩
  · exact c2_face_canonical_16 ⟨17,by decide⟩
  · exact c2_face_canonical_16 ⟨18,by decide⟩
  · exact c2_face_canonical_16 ⟨19,by decide⟩
  · exact c2_face_canonical_17 ⟨0,by decide⟩
  · exact c2_face_canonical_17 ⟨1,by decide⟩
  · exact c2_face_canonical_17 ⟨2,by decide⟩
  · exact c2_face_canonical_17 ⟨3,by decide⟩
  · exact c2_face_canonical_17 ⟨4,by decide⟩
  · exact c2_face_canonical_17 ⟨5,by decide⟩
  · exact c2_face_canonical_17 ⟨6,by decide⟩
  · exact c2_face_canonical_17 ⟨7,by decide⟩
  · exact c2_face_canonical_17 ⟨8,by decide⟩
  · exact c2_face_canonical_17 ⟨9,by decide⟩
  · exact c2_face_canonical_17 ⟨10,by decide⟩
  · exact c2_face_canonical_17 ⟨11,by decide⟩
  · exact c2_face_canonical_17 ⟨12,by decide⟩
  · exact c2_face_canonical_17 ⟨13,by decide⟩
  · exact c2_face_canonical_17 ⟨14,by decide⟩
  · exact c2_face_canonical_17 ⟨15,by decide⟩
  · exact c2_face_canonical_17 ⟨16,by decide⟩
  · exact c2_face_canonical_17 ⟨17,by decide⟩
  · exact c2_face_canonical_17 ⟨18,by decide⟩
  · exact c2_face_canonical_17 ⟨19,by decide⟩
  · exact c2_face_canonical_18 ⟨0,by decide⟩
  · exact c2_face_canonical_18 ⟨1,by decide⟩
  · exact c2_face_canonical_18 ⟨2,by decide⟩
  · exact c2_face_canonical_18 ⟨3,by decide⟩
  · exact c2_face_canonical_18 ⟨4,by decide⟩
  · exact c2_face_canonical_18 ⟨5,by decide⟩
  · exact c2_face_canonical_18 ⟨6,by decide⟩
  · exact c2_face_canonical_18 ⟨7,by decide⟩
  · exact c2_face_canonical_18 ⟨8,by decide⟩
  · exact c2_face_canonical_18 ⟨9,by decide⟩
  · exact c2_face_canonical_18 ⟨10,by decide⟩
  · exact c2_face_canonical_18 ⟨11,by decide⟩
  · exact c2_face_canonical_18 ⟨12,by decide⟩
  · exact c2_face_canonical_18 ⟨13,by decide⟩
  · exact c2_face_canonical_18 ⟨14,by decide⟩
  · exact c2_face_canonical_18 ⟨15,by decide⟩
  · exact c2_face_canonical_18 ⟨16,by decide⟩
  · exact c2_face_canonical_18 ⟨17,by decide⟩
  · exact c2_face_canonical_18 ⟨18,by decide⟩
  · exact c2_face_canonical_18 ⟨19,by decide⟩
  · exact c2_face_canonical_19 ⟨0,by decide⟩
  · exact c2_face_canonical_19 ⟨1,by decide⟩
  · exact c2_face_canonical_19 ⟨2,by decide⟩
  · exact c2_face_canonical_19 ⟨3,by decide⟩
  · exact c2_face_canonical_19 ⟨4,by decide⟩
  · exact c2_face_canonical_19 ⟨5,by decide⟩
  · exact c2_face_canonical_19 ⟨6,by decide⟩
  · exact c2_face_canonical_19 ⟨7,by decide⟩
  · exact c2_face_canonical_19 ⟨8,by decide⟩
  · exact c2_face_canonical_19 ⟨9,by decide⟩
  · exact c2_face_canonical_19 ⟨10,by decide⟩
  · exact c2_face_canonical_19 ⟨11,by decide⟩
  · exact c2_face_canonical_19 ⟨12,by decide⟩
  · exact c2_face_canonical_19 ⟨13,by decide⟩
  · exact c2_face_canonical_19 ⟨14,by decide⟩
  · exact c2_face_canonical_19 ⟨15,by decide⟩
  · exact c2_face_canonical_19 ⟨16,by decide⟩
  · exact c2_face_canonical_19 ⟨17,by decide⟩
  · exact c2_face_canonical_19 ⟨18,by decide⟩
  · exact c2_face_canonical_19 ⟨19,by decide⟩
  · exact c2_face_canonical_20 ⟨0,by decide⟩
  · exact c2_face_canonical_20 ⟨1,by decide⟩
  · exact c2_face_canonical_20 ⟨2,by decide⟩
  · exact c2_face_canonical_20 ⟨3,by decide⟩
  · exact c2_face_canonical_20 ⟨4,by decide⟩
  · exact c2_face_canonical_20 ⟨5,by decide⟩
  · exact c2_face_canonical_20 ⟨6,by decide⟩
  · exact c2_face_canonical_20 ⟨7,by decide⟩
  · exact c2_face_canonical_20 ⟨8,by decide⟩
  · exact c2_face_canonical_20 ⟨9,by decide⟩
  · exact c2_face_canonical_20 ⟨10,by decide⟩
  · exact c2_face_canonical_20 ⟨11,by decide⟩
  · exact c2_face_canonical_20 ⟨12,by decide⟩
  · exact c2_face_canonical_20 ⟨13,by decide⟩
  · exact c2_face_canonical_20 ⟨14,by decide⟩
  · exact c2_face_canonical_20 ⟨15,by decide⟩
  · exact c2_face_canonical_20 ⟨16,by decide⟩
  · exact c2_face_canonical_20 ⟨17,by decide⟩
  · exact c2_face_canonical_20 ⟨18,by decide⟩
  · exact c2_face_canonical_20 ⟨19,by decide⟩
  · exact c2_face_canonical_21 ⟨0,by decide⟩
  · exact c2_face_canonical_21 ⟨1,by decide⟩
  · exact c2_face_canonical_21 ⟨2,by decide⟩
  · exact c2_face_canonical_21 ⟨3,by decide⟩
  · exact c2_face_canonical_21 ⟨4,by decide⟩
  · exact c2_face_canonical_21 ⟨5,by decide⟩
  · exact c2_face_canonical_21 ⟨6,by decide⟩
  · exact c2_face_canonical_21 ⟨7,by decide⟩
  · exact c2_face_canonical_21 ⟨8,by decide⟩
  · exact c2_face_canonical_21 ⟨9,by decide⟩
  · exact c2_face_canonical_21 ⟨10,by decide⟩
  · exact c2_face_canonical_21 ⟨11,by decide⟩
  · exact c2_face_canonical_21 ⟨12,by decide⟩
  · exact c2_face_canonical_21 ⟨13,by decide⟩
  · exact c2_face_canonical_21 ⟨14,by decide⟩
  · exact c2_face_canonical_21 ⟨15,by decide⟩
  · exact c2_face_canonical_21 ⟨16,by decide⟩
  · exact c2_face_canonical_21 ⟨17,by decide⟩
  · exact c2_face_canonical_21 ⟨18,by decide⟩
  · exact c2_face_canonical_21 ⟨19,by decide⟩
  · exact c2_face_canonical_22 ⟨0,by decide⟩
  · exact c2_face_canonical_22 ⟨1,by decide⟩
  · exact c2_face_canonical_22 ⟨2,by decide⟩
  · exact c2_face_canonical_22 ⟨3,by decide⟩
  · exact c2_face_canonical_22 ⟨4,by decide⟩
  · exact c2_face_canonical_22 ⟨5,by decide⟩
  · exact c2_face_canonical_22 ⟨6,by decide⟩
  · exact c2_face_canonical_22 ⟨7,by decide⟩
  · exact c2_face_canonical_22 ⟨8,by decide⟩
  · exact c2_face_canonical_22 ⟨9,by decide⟩
  · exact c2_face_canonical_22 ⟨10,by decide⟩
  · exact c2_face_canonical_22 ⟨11,by decide⟩
  · exact c2_face_canonical_22 ⟨12,by decide⟩
  · exact c2_face_canonical_22 ⟨13,by decide⟩
  · exact c2_face_canonical_22 ⟨14,by decide⟩
  · exact c2_face_canonical_22 ⟨15,by decide⟩
  · exact c2_face_canonical_22 ⟨16,by decide⟩
  · exact c2_face_canonical_22 ⟨17,by decide⟩
  · exact c2_face_canonical_22 ⟨18,by decide⟩
  · exact c2_face_canonical_22 ⟨19,by decide⟩
  · exact c2_face_canonical_23 ⟨0,by decide⟩
  · exact c2_face_canonical_23 ⟨1,by decide⟩
  · exact c2_face_canonical_23 ⟨2,by decide⟩
  · exact c2_face_canonical_23 ⟨3,by decide⟩
  · exact c2_face_canonical_23 ⟨4,by decide⟩
  · exact c2_face_canonical_23 ⟨5,by decide⟩
  · exact c2_face_canonical_23 ⟨6,by decide⟩
  · exact c2_face_canonical_23 ⟨7,by decide⟩
  · exact c2_face_canonical_23 ⟨8,by decide⟩
  · exact c2_face_canonical_23 ⟨9,by decide⟩
  · exact c2_face_canonical_23 ⟨10,by decide⟩
  · exact c2_face_canonical_23 ⟨11,by decide⟩
  · exact c2_face_canonical_23 ⟨12,by decide⟩
  · exact c2_face_canonical_23 ⟨13,by decide⟩
  · exact c2_face_canonical_23 ⟨14,by decide⟩
  · exact c2_face_canonical_23 ⟨15,by decide⟩
  · exact c2_face_canonical_23 ⟨16,by decide⟩
  · exact c2_face_canonical_23 ⟨17,by decide⟩
  · exact c2_face_canonical_23 ⟨18,by decide⟩
  · exact c2_face_canonical_23 ⟨19,by decide⟩
  · exact c2_face_canonical_24 ⟨0,by decide⟩
  · exact c2_face_canonical_24 ⟨1,by decide⟩
  · exact c2_face_canonical_24 ⟨2,by decide⟩
  · exact c2_face_canonical_24 ⟨3,by decide⟩
  · exact c2_face_canonical_24 ⟨4,by decide⟩
  · exact c2_face_canonical_24 ⟨5,by decide⟩
  · exact c2_face_canonical_24 ⟨6,by decide⟩
  · exact c2_face_canonical_24 ⟨7,by decide⟩
  · exact c2_face_canonical_24 ⟨8,by decide⟩
  · exact c2_face_canonical_24 ⟨9,by decide⟩
  · exact c2_face_canonical_24 ⟨10,by decide⟩
  · exact c2_face_canonical_24 ⟨11,by decide⟩
  · exact c2_face_canonical_24 ⟨12,by decide⟩
  · exact c2_face_canonical_24 ⟨13,by decide⟩
  · exact c2_face_canonical_24 ⟨14,by decide⟩
  · exact c2_face_canonical_24 ⟨15,by decide⟩
  · exact c2_face_canonical_24 ⟨16,by decide⟩
  · exact c2_face_canonical_24 ⟨17,by decide⟩
  · exact c2_face_canonical_24 ⟨18,by decide⟩
  · exact c2_face_canonical_24 ⟨19,by decide⟩
  · exact c2_face_canonical_25 ⟨0,by decide⟩
  · exact c2_face_canonical_25 ⟨1,by decide⟩
  · exact c2_face_canonical_25 ⟨2,by decide⟩
  · exact c2_face_canonical_25 ⟨3,by decide⟩
  · exact c2_face_canonical_25 ⟨4,by decide⟩
  · exact c2_face_canonical_25 ⟨5,by decide⟩
  · exact c2_face_canonical_25 ⟨6,by decide⟩
  · exact c2_face_canonical_25 ⟨7,by decide⟩
  · exact c2_face_canonical_25 ⟨8,by decide⟩
  · exact c2_face_canonical_25 ⟨9,by decide⟩
  · exact c2_face_canonical_25 ⟨10,by decide⟩
  · exact c2_face_canonical_25 ⟨11,by decide⟩
  · exact c2_face_canonical_25 ⟨12,by decide⟩
  · exact c2_face_canonical_25 ⟨13,by decide⟩
  · exact c2_face_canonical_25 ⟨14,by decide⟩
  · exact c2_face_canonical_25 ⟨15,by decide⟩
  · exact c2_face_canonical_25 ⟨16,by decide⟩
  · exact c2_face_canonical_25 ⟨17,by decide⟩
  · exact c2_face_canonical_25 ⟨18,by decide⟩
  · exact c2_face_canonical_25 ⟨19,by decide⟩
  · exact c2_face_canonical_26 ⟨0,by decide⟩
  · exact c2_face_canonical_26 ⟨1,by decide⟩
  · exact c2_face_canonical_26 ⟨2,by decide⟩
  · exact c2_face_canonical_26 ⟨3,by decide⟩
  · exact c2_face_canonical_26 ⟨4,by decide⟩
  · exact c2_face_canonical_26 ⟨5,by decide⟩
  · exact c2_face_canonical_26 ⟨6,by decide⟩
  · exact c2_face_canonical_26 ⟨7,by decide⟩
  · exact c2_face_canonical_26 ⟨8,by decide⟩
  · exact c2_face_canonical_26 ⟨9,by decide⟩
  · exact c2_face_canonical_26 ⟨10,by decide⟩
  · exact c2_face_canonical_26 ⟨11,by decide⟩
  · exact c2_face_canonical_26 ⟨12,by decide⟩
  · exact c2_face_canonical_26 ⟨13,by decide⟩
  · exact c2_face_canonical_26 ⟨14,by decide⟩
  · exact c2_face_canonical_26 ⟨15,by decide⟩
  · exact c2_face_canonical_26 ⟨16,by decide⟩
  · exact c2_face_canonical_26 ⟨17,by decide⟩
  · exact c2_face_canonical_26 ⟨18,by decide⟩
  · exact c2_face_canonical_26 ⟨19,by decide⟩
  · exact c2_face_canonical_27 ⟨0,by decide⟩
  · exact c2_face_canonical_27 ⟨1,by decide⟩
  · exact c2_face_canonical_27 ⟨2,by decide⟩
  · exact c2_face_canonical_27 ⟨3,by decide⟩
  · exact c2_face_canonical_27 ⟨4,by decide⟩
  · exact c2_face_canonical_27 ⟨5,by decide⟩
  · exact c2_face_canonical_27 ⟨6,by decide⟩
  · exact c2_face_canonical_27 ⟨7,by decide⟩
  · exact c2_face_canonical_27 ⟨8,by decide⟩
  · exact c2_face_canonical_27 ⟨9,by decide⟩
  · exact c2_face_canonical_27 ⟨10,by decide⟩
  · exact c2_face_canonical_27 ⟨11,by decide⟩
  · exact c2_face_canonical_27 ⟨12,by decide⟩
  · exact c2_face_canonical_27 ⟨13,by decide⟩
  · exact c2_face_canonical_27 ⟨14,by decide⟩
  · exact c2_face_canonical_27 ⟨15,by decide⟩
  · exact c2_face_canonical_27 ⟨16,by decide⟩
  · exact c2_face_canonical_27 ⟨17,by decide⟩
  · exact c2_face_canonical_27 ⟨18,by decide⟩
  · exact c2_face_canonical_27 ⟨19,by decide⟩
  · exact c2_face_canonical_28 ⟨0,by decide⟩
  · exact c2_face_canonical_28 ⟨1,by decide⟩
  · exact c2_face_canonical_28 ⟨2,by decide⟩
  · exact c2_face_canonical_28 ⟨3,by decide⟩
  · exact c2_face_canonical_28 ⟨4,by decide⟩
  · exact c2_face_canonical_28 ⟨5,by decide⟩
  · exact c2_face_canonical_28 ⟨6,by decide⟩
  · exact c2_face_canonical_28 ⟨7,by decide⟩
  · exact c2_face_canonical_28 ⟨8,by decide⟩
  · exact c2_face_canonical_28 ⟨9,by decide⟩
  · exact c2_face_canonical_28 ⟨10,by decide⟩
  · exact c2_face_canonical_28 ⟨11,by decide⟩
  · exact c2_face_canonical_28 ⟨12,by decide⟩
  · exact c2_face_canonical_28 ⟨13,by decide⟩
  · exact c2_face_canonical_28 ⟨14,by decide⟩
  · exact c2_face_canonical_28 ⟨15,by decide⟩
  · exact c2_face_canonical_28 ⟨16,by decide⟩
  · exact c2_face_canonical_28 ⟨17,by decide⟩
  · exact c2_face_canonical_28 ⟨18,by decide⟩
  · exact c2_face_canonical_28 ⟨19,by decide⟩
theorem c2_edge_canonical : ∀ t h,
    c2FacetMask (c2Cell t).f &&& c2FacetMask (c2Cell t).g &&& c2FacetMask h =
      c2FacetMask (c2Cell t).f &&& c2FacetMask (c2Cell t).g &&& c2FacetMask (c2Cell t).h →
        (c2Cell t).h ≤ h := by
  intro t
  fin_cases t
  · exact c2_edge_canonical_0 ⟨0,by decide⟩
  · exact c2_edge_canonical_0 ⟨1,by decide⟩
  · exact c2_edge_canonical_0 ⟨2,by decide⟩
  · exact c2_edge_canonical_0 ⟨3,by decide⟩
  · exact c2_edge_canonical_0 ⟨4,by decide⟩
  · exact c2_edge_canonical_0 ⟨5,by decide⟩
  · exact c2_edge_canonical_0 ⟨6,by decide⟩
  · exact c2_edge_canonical_0 ⟨7,by decide⟩
  · exact c2_edge_canonical_0 ⟨8,by decide⟩
  · exact c2_edge_canonical_0 ⟨9,by decide⟩
  · exact c2_edge_canonical_0 ⟨10,by decide⟩
  · exact c2_edge_canonical_0 ⟨11,by decide⟩
  · exact c2_edge_canonical_0 ⟨12,by decide⟩
  · exact c2_edge_canonical_0 ⟨13,by decide⟩
  · exact c2_edge_canonical_0 ⟨14,by decide⟩
  · exact c2_edge_canonical_0 ⟨15,by decide⟩
  · exact c2_edge_canonical_0 ⟨16,by decide⟩
  · exact c2_edge_canonical_0 ⟨17,by decide⟩
  · exact c2_edge_canonical_0 ⟨18,by decide⟩
  · exact c2_edge_canonical_0 ⟨19,by decide⟩
  · exact c2_edge_canonical_1 ⟨0,by decide⟩
  · exact c2_edge_canonical_1 ⟨1,by decide⟩
  · exact c2_edge_canonical_1 ⟨2,by decide⟩
  · exact c2_edge_canonical_1 ⟨3,by decide⟩
  · exact c2_edge_canonical_1 ⟨4,by decide⟩
  · exact c2_edge_canonical_1 ⟨5,by decide⟩
  · exact c2_edge_canonical_1 ⟨6,by decide⟩
  · exact c2_edge_canonical_1 ⟨7,by decide⟩
  · exact c2_edge_canonical_1 ⟨8,by decide⟩
  · exact c2_edge_canonical_1 ⟨9,by decide⟩
  · exact c2_edge_canonical_1 ⟨10,by decide⟩
  · exact c2_edge_canonical_1 ⟨11,by decide⟩
  · exact c2_edge_canonical_1 ⟨12,by decide⟩
  · exact c2_edge_canonical_1 ⟨13,by decide⟩
  · exact c2_edge_canonical_1 ⟨14,by decide⟩
  · exact c2_edge_canonical_1 ⟨15,by decide⟩
  · exact c2_edge_canonical_1 ⟨16,by decide⟩
  · exact c2_edge_canonical_1 ⟨17,by decide⟩
  · exact c2_edge_canonical_1 ⟨18,by decide⟩
  · exact c2_edge_canonical_1 ⟨19,by decide⟩
  · exact c2_edge_canonical_2 ⟨0,by decide⟩
  · exact c2_edge_canonical_2 ⟨1,by decide⟩
  · exact c2_edge_canonical_2 ⟨2,by decide⟩
  · exact c2_edge_canonical_2 ⟨3,by decide⟩
  · exact c2_edge_canonical_2 ⟨4,by decide⟩
  · exact c2_edge_canonical_2 ⟨5,by decide⟩
  · exact c2_edge_canonical_2 ⟨6,by decide⟩
  · exact c2_edge_canonical_2 ⟨7,by decide⟩
  · exact c2_edge_canonical_2 ⟨8,by decide⟩
  · exact c2_edge_canonical_2 ⟨9,by decide⟩
  · exact c2_edge_canonical_2 ⟨10,by decide⟩
  · exact c2_edge_canonical_2 ⟨11,by decide⟩
  · exact c2_edge_canonical_2 ⟨12,by decide⟩
  · exact c2_edge_canonical_2 ⟨13,by decide⟩
  · exact c2_edge_canonical_2 ⟨14,by decide⟩
  · exact c2_edge_canonical_2 ⟨15,by decide⟩
  · exact c2_edge_canonical_2 ⟨16,by decide⟩
  · exact c2_edge_canonical_2 ⟨17,by decide⟩
  · exact c2_edge_canonical_2 ⟨18,by decide⟩
  · exact c2_edge_canonical_2 ⟨19,by decide⟩
  · exact c2_edge_canonical_3 ⟨0,by decide⟩
  · exact c2_edge_canonical_3 ⟨1,by decide⟩
  · exact c2_edge_canonical_3 ⟨2,by decide⟩
  · exact c2_edge_canonical_3 ⟨3,by decide⟩
  · exact c2_edge_canonical_3 ⟨4,by decide⟩
  · exact c2_edge_canonical_3 ⟨5,by decide⟩
  · exact c2_edge_canonical_3 ⟨6,by decide⟩
  · exact c2_edge_canonical_3 ⟨7,by decide⟩
  · exact c2_edge_canonical_3 ⟨8,by decide⟩
  · exact c2_edge_canonical_3 ⟨9,by decide⟩
  · exact c2_edge_canonical_3 ⟨10,by decide⟩
  · exact c2_edge_canonical_3 ⟨11,by decide⟩
  · exact c2_edge_canonical_3 ⟨12,by decide⟩
  · exact c2_edge_canonical_3 ⟨13,by decide⟩
  · exact c2_edge_canonical_3 ⟨14,by decide⟩
  · exact c2_edge_canonical_3 ⟨15,by decide⟩
  · exact c2_edge_canonical_3 ⟨16,by decide⟩
  · exact c2_edge_canonical_3 ⟨17,by decide⟩
  · exact c2_edge_canonical_3 ⟨18,by decide⟩
  · exact c2_edge_canonical_3 ⟨19,by decide⟩
  · exact c2_edge_canonical_4 ⟨0,by decide⟩
  · exact c2_edge_canonical_4 ⟨1,by decide⟩
  · exact c2_edge_canonical_4 ⟨2,by decide⟩
  · exact c2_edge_canonical_4 ⟨3,by decide⟩
  · exact c2_edge_canonical_4 ⟨4,by decide⟩
  · exact c2_edge_canonical_4 ⟨5,by decide⟩
  · exact c2_edge_canonical_4 ⟨6,by decide⟩
  · exact c2_edge_canonical_4 ⟨7,by decide⟩
  · exact c2_edge_canonical_4 ⟨8,by decide⟩
  · exact c2_edge_canonical_4 ⟨9,by decide⟩
  · exact c2_edge_canonical_4 ⟨10,by decide⟩
  · exact c2_edge_canonical_4 ⟨11,by decide⟩
  · exact c2_edge_canonical_4 ⟨12,by decide⟩
  · exact c2_edge_canonical_4 ⟨13,by decide⟩
  · exact c2_edge_canonical_4 ⟨14,by decide⟩
  · exact c2_edge_canonical_4 ⟨15,by decide⟩
  · exact c2_edge_canonical_4 ⟨16,by decide⟩
  · exact c2_edge_canonical_4 ⟨17,by decide⟩
  · exact c2_edge_canonical_4 ⟨18,by decide⟩
  · exact c2_edge_canonical_4 ⟨19,by decide⟩
  · exact c2_edge_canonical_5 ⟨0,by decide⟩
  · exact c2_edge_canonical_5 ⟨1,by decide⟩
  · exact c2_edge_canonical_5 ⟨2,by decide⟩
  · exact c2_edge_canonical_5 ⟨3,by decide⟩
  · exact c2_edge_canonical_5 ⟨4,by decide⟩
  · exact c2_edge_canonical_5 ⟨5,by decide⟩
  · exact c2_edge_canonical_5 ⟨6,by decide⟩
  · exact c2_edge_canonical_5 ⟨7,by decide⟩
  · exact c2_edge_canonical_5 ⟨8,by decide⟩
  · exact c2_edge_canonical_5 ⟨9,by decide⟩
  · exact c2_edge_canonical_5 ⟨10,by decide⟩
  · exact c2_edge_canonical_5 ⟨11,by decide⟩
  · exact c2_edge_canonical_5 ⟨12,by decide⟩
  · exact c2_edge_canonical_5 ⟨13,by decide⟩
  · exact c2_edge_canonical_5 ⟨14,by decide⟩
  · exact c2_edge_canonical_5 ⟨15,by decide⟩
  · exact c2_edge_canonical_5 ⟨16,by decide⟩
  · exact c2_edge_canonical_5 ⟨17,by decide⟩
  · exact c2_edge_canonical_5 ⟨18,by decide⟩
  · exact c2_edge_canonical_5 ⟨19,by decide⟩
  · exact c2_edge_canonical_6 ⟨0,by decide⟩
  · exact c2_edge_canonical_6 ⟨1,by decide⟩
  · exact c2_edge_canonical_6 ⟨2,by decide⟩
  · exact c2_edge_canonical_6 ⟨3,by decide⟩
  · exact c2_edge_canonical_6 ⟨4,by decide⟩
  · exact c2_edge_canonical_6 ⟨5,by decide⟩
  · exact c2_edge_canonical_6 ⟨6,by decide⟩
  · exact c2_edge_canonical_6 ⟨7,by decide⟩
  · exact c2_edge_canonical_6 ⟨8,by decide⟩
  · exact c2_edge_canonical_6 ⟨9,by decide⟩
  · exact c2_edge_canonical_6 ⟨10,by decide⟩
  · exact c2_edge_canonical_6 ⟨11,by decide⟩
  · exact c2_edge_canonical_6 ⟨12,by decide⟩
  · exact c2_edge_canonical_6 ⟨13,by decide⟩
  · exact c2_edge_canonical_6 ⟨14,by decide⟩
  · exact c2_edge_canonical_6 ⟨15,by decide⟩
  · exact c2_edge_canonical_6 ⟨16,by decide⟩
  · exact c2_edge_canonical_6 ⟨17,by decide⟩
  · exact c2_edge_canonical_6 ⟨18,by decide⟩
  · exact c2_edge_canonical_6 ⟨19,by decide⟩
  · exact c2_edge_canonical_7 ⟨0,by decide⟩
  · exact c2_edge_canonical_7 ⟨1,by decide⟩
  · exact c2_edge_canonical_7 ⟨2,by decide⟩
  · exact c2_edge_canonical_7 ⟨3,by decide⟩
  · exact c2_edge_canonical_7 ⟨4,by decide⟩
  · exact c2_edge_canonical_7 ⟨5,by decide⟩
  · exact c2_edge_canonical_7 ⟨6,by decide⟩
  · exact c2_edge_canonical_7 ⟨7,by decide⟩
  · exact c2_edge_canonical_7 ⟨8,by decide⟩
  · exact c2_edge_canonical_7 ⟨9,by decide⟩
  · exact c2_edge_canonical_7 ⟨10,by decide⟩
  · exact c2_edge_canonical_7 ⟨11,by decide⟩
  · exact c2_edge_canonical_7 ⟨12,by decide⟩
  · exact c2_edge_canonical_7 ⟨13,by decide⟩
  · exact c2_edge_canonical_7 ⟨14,by decide⟩
  · exact c2_edge_canonical_7 ⟨15,by decide⟩
  · exact c2_edge_canonical_7 ⟨16,by decide⟩
  · exact c2_edge_canonical_7 ⟨17,by decide⟩
  · exact c2_edge_canonical_7 ⟨18,by decide⟩
  · exact c2_edge_canonical_7 ⟨19,by decide⟩
  · exact c2_edge_canonical_8 ⟨0,by decide⟩
  · exact c2_edge_canonical_8 ⟨1,by decide⟩
  · exact c2_edge_canonical_8 ⟨2,by decide⟩
  · exact c2_edge_canonical_8 ⟨3,by decide⟩
  · exact c2_edge_canonical_8 ⟨4,by decide⟩
  · exact c2_edge_canonical_8 ⟨5,by decide⟩
  · exact c2_edge_canonical_8 ⟨6,by decide⟩
  · exact c2_edge_canonical_8 ⟨7,by decide⟩
  · exact c2_edge_canonical_8 ⟨8,by decide⟩
  · exact c2_edge_canonical_8 ⟨9,by decide⟩
  · exact c2_edge_canonical_8 ⟨10,by decide⟩
  · exact c2_edge_canonical_8 ⟨11,by decide⟩
  · exact c2_edge_canonical_8 ⟨12,by decide⟩
  · exact c2_edge_canonical_8 ⟨13,by decide⟩
  · exact c2_edge_canonical_8 ⟨14,by decide⟩
  · exact c2_edge_canonical_8 ⟨15,by decide⟩
  · exact c2_edge_canonical_8 ⟨16,by decide⟩
  · exact c2_edge_canonical_8 ⟨17,by decide⟩
  · exact c2_edge_canonical_8 ⟨18,by decide⟩
  · exact c2_edge_canonical_8 ⟨19,by decide⟩
  · exact c2_edge_canonical_9 ⟨0,by decide⟩
  · exact c2_edge_canonical_9 ⟨1,by decide⟩
  · exact c2_edge_canonical_9 ⟨2,by decide⟩
  · exact c2_edge_canonical_9 ⟨3,by decide⟩
  · exact c2_edge_canonical_9 ⟨4,by decide⟩
  · exact c2_edge_canonical_9 ⟨5,by decide⟩
  · exact c2_edge_canonical_9 ⟨6,by decide⟩
  · exact c2_edge_canonical_9 ⟨7,by decide⟩
  · exact c2_edge_canonical_9 ⟨8,by decide⟩
  · exact c2_edge_canonical_9 ⟨9,by decide⟩
  · exact c2_edge_canonical_9 ⟨10,by decide⟩
  · exact c2_edge_canonical_9 ⟨11,by decide⟩
  · exact c2_edge_canonical_9 ⟨12,by decide⟩
  · exact c2_edge_canonical_9 ⟨13,by decide⟩
  · exact c2_edge_canonical_9 ⟨14,by decide⟩
  · exact c2_edge_canonical_9 ⟨15,by decide⟩
  · exact c2_edge_canonical_9 ⟨16,by decide⟩
  · exact c2_edge_canonical_9 ⟨17,by decide⟩
  · exact c2_edge_canonical_9 ⟨18,by decide⟩
  · exact c2_edge_canonical_9 ⟨19,by decide⟩
  · exact c2_edge_canonical_10 ⟨0,by decide⟩
  · exact c2_edge_canonical_10 ⟨1,by decide⟩
  · exact c2_edge_canonical_10 ⟨2,by decide⟩
  · exact c2_edge_canonical_10 ⟨3,by decide⟩
  · exact c2_edge_canonical_10 ⟨4,by decide⟩
  · exact c2_edge_canonical_10 ⟨5,by decide⟩
  · exact c2_edge_canonical_10 ⟨6,by decide⟩
  · exact c2_edge_canonical_10 ⟨7,by decide⟩
  · exact c2_edge_canonical_10 ⟨8,by decide⟩
  · exact c2_edge_canonical_10 ⟨9,by decide⟩
  · exact c2_edge_canonical_10 ⟨10,by decide⟩
  · exact c2_edge_canonical_10 ⟨11,by decide⟩
  · exact c2_edge_canonical_10 ⟨12,by decide⟩
  · exact c2_edge_canonical_10 ⟨13,by decide⟩
  · exact c2_edge_canonical_10 ⟨14,by decide⟩
  · exact c2_edge_canonical_10 ⟨15,by decide⟩
  · exact c2_edge_canonical_10 ⟨16,by decide⟩
  · exact c2_edge_canonical_10 ⟨17,by decide⟩
  · exact c2_edge_canonical_10 ⟨18,by decide⟩
  · exact c2_edge_canonical_10 ⟨19,by decide⟩
  · exact c2_edge_canonical_11 ⟨0,by decide⟩
  · exact c2_edge_canonical_11 ⟨1,by decide⟩
  · exact c2_edge_canonical_11 ⟨2,by decide⟩
  · exact c2_edge_canonical_11 ⟨3,by decide⟩
  · exact c2_edge_canonical_11 ⟨4,by decide⟩
  · exact c2_edge_canonical_11 ⟨5,by decide⟩
  · exact c2_edge_canonical_11 ⟨6,by decide⟩
  · exact c2_edge_canonical_11 ⟨7,by decide⟩
  · exact c2_edge_canonical_11 ⟨8,by decide⟩
  · exact c2_edge_canonical_11 ⟨9,by decide⟩
  · exact c2_edge_canonical_11 ⟨10,by decide⟩
  · exact c2_edge_canonical_11 ⟨11,by decide⟩
  · exact c2_edge_canonical_11 ⟨12,by decide⟩
  · exact c2_edge_canonical_11 ⟨13,by decide⟩
  · exact c2_edge_canonical_11 ⟨14,by decide⟩
  · exact c2_edge_canonical_11 ⟨15,by decide⟩
  · exact c2_edge_canonical_11 ⟨16,by decide⟩
  · exact c2_edge_canonical_11 ⟨17,by decide⟩
  · exact c2_edge_canonical_11 ⟨18,by decide⟩
  · exact c2_edge_canonical_11 ⟨19,by decide⟩
  · exact c2_edge_canonical_12 ⟨0,by decide⟩
  · exact c2_edge_canonical_12 ⟨1,by decide⟩
  · exact c2_edge_canonical_12 ⟨2,by decide⟩
  · exact c2_edge_canonical_12 ⟨3,by decide⟩
  · exact c2_edge_canonical_12 ⟨4,by decide⟩
  · exact c2_edge_canonical_12 ⟨5,by decide⟩
  · exact c2_edge_canonical_12 ⟨6,by decide⟩
  · exact c2_edge_canonical_12 ⟨7,by decide⟩
  · exact c2_edge_canonical_12 ⟨8,by decide⟩
  · exact c2_edge_canonical_12 ⟨9,by decide⟩
  · exact c2_edge_canonical_12 ⟨10,by decide⟩
  · exact c2_edge_canonical_12 ⟨11,by decide⟩
  · exact c2_edge_canonical_12 ⟨12,by decide⟩
  · exact c2_edge_canonical_12 ⟨13,by decide⟩
  · exact c2_edge_canonical_12 ⟨14,by decide⟩
  · exact c2_edge_canonical_12 ⟨15,by decide⟩
  · exact c2_edge_canonical_12 ⟨16,by decide⟩
  · exact c2_edge_canonical_12 ⟨17,by decide⟩
  · exact c2_edge_canonical_12 ⟨18,by decide⟩
  · exact c2_edge_canonical_12 ⟨19,by decide⟩
  · exact c2_edge_canonical_13 ⟨0,by decide⟩
  · exact c2_edge_canonical_13 ⟨1,by decide⟩
  · exact c2_edge_canonical_13 ⟨2,by decide⟩
  · exact c2_edge_canonical_13 ⟨3,by decide⟩
  · exact c2_edge_canonical_13 ⟨4,by decide⟩
  · exact c2_edge_canonical_13 ⟨5,by decide⟩
  · exact c2_edge_canonical_13 ⟨6,by decide⟩
  · exact c2_edge_canonical_13 ⟨7,by decide⟩
  · exact c2_edge_canonical_13 ⟨8,by decide⟩
  · exact c2_edge_canonical_13 ⟨9,by decide⟩
  · exact c2_edge_canonical_13 ⟨10,by decide⟩
  · exact c2_edge_canonical_13 ⟨11,by decide⟩
  · exact c2_edge_canonical_13 ⟨12,by decide⟩
  · exact c2_edge_canonical_13 ⟨13,by decide⟩
  · exact c2_edge_canonical_13 ⟨14,by decide⟩
  · exact c2_edge_canonical_13 ⟨15,by decide⟩
  · exact c2_edge_canonical_13 ⟨16,by decide⟩
  · exact c2_edge_canonical_13 ⟨17,by decide⟩
  · exact c2_edge_canonical_13 ⟨18,by decide⟩
  · exact c2_edge_canonical_13 ⟨19,by decide⟩
  · exact c2_edge_canonical_14 ⟨0,by decide⟩
  · exact c2_edge_canonical_14 ⟨1,by decide⟩
  · exact c2_edge_canonical_14 ⟨2,by decide⟩
  · exact c2_edge_canonical_14 ⟨3,by decide⟩
  · exact c2_edge_canonical_14 ⟨4,by decide⟩
  · exact c2_edge_canonical_14 ⟨5,by decide⟩
  · exact c2_edge_canonical_14 ⟨6,by decide⟩
  · exact c2_edge_canonical_14 ⟨7,by decide⟩
  · exact c2_edge_canonical_14 ⟨8,by decide⟩
  · exact c2_edge_canonical_14 ⟨9,by decide⟩
  · exact c2_edge_canonical_14 ⟨10,by decide⟩
  · exact c2_edge_canonical_14 ⟨11,by decide⟩
  · exact c2_edge_canonical_14 ⟨12,by decide⟩
  · exact c2_edge_canonical_14 ⟨13,by decide⟩
  · exact c2_edge_canonical_14 ⟨14,by decide⟩
  · exact c2_edge_canonical_14 ⟨15,by decide⟩
  · exact c2_edge_canonical_14 ⟨16,by decide⟩
  · exact c2_edge_canonical_14 ⟨17,by decide⟩
  · exact c2_edge_canonical_14 ⟨18,by decide⟩
  · exact c2_edge_canonical_14 ⟨19,by decide⟩
  · exact c2_edge_canonical_15 ⟨0,by decide⟩
  · exact c2_edge_canonical_15 ⟨1,by decide⟩
  · exact c2_edge_canonical_15 ⟨2,by decide⟩
  · exact c2_edge_canonical_15 ⟨3,by decide⟩
  · exact c2_edge_canonical_15 ⟨4,by decide⟩
  · exact c2_edge_canonical_15 ⟨5,by decide⟩
  · exact c2_edge_canonical_15 ⟨6,by decide⟩
  · exact c2_edge_canonical_15 ⟨7,by decide⟩
  · exact c2_edge_canonical_15 ⟨8,by decide⟩
  · exact c2_edge_canonical_15 ⟨9,by decide⟩
  · exact c2_edge_canonical_15 ⟨10,by decide⟩
  · exact c2_edge_canonical_15 ⟨11,by decide⟩
  · exact c2_edge_canonical_15 ⟨12,by decide⟩
  · exact c2_edge_canonical_15 ⟨13,by decide⟩
  · exact c2_edge_canonical_15 ⟨14,by decide⟩
  · exact c2_edge_canonical_15 ⟨15,by decide⟩
  · exact c2_edge_canonical_15 ⟨16,by decide⟩
  · exact c2_edge_canonical_15 ⟨17,by decide⟩
  · exact c2_edge_canonical_15 ⟨18,by decide⟩
  · exact c2_edge_canonical_15 ⟨19,by decide⟩
  · exact c2_edge_canonical_16 ⟨0,by decide⟩
  · exact c2_edge_canonical_16 ⟨1,by decide⟩
  · exact c2_edge_canonical_16 ⟨2,by decide⟩
  · exact c2_edge_canonical_16 ⟨3,by decide⟩
  · exact c2_edge_canonical_16 ⟨4,by decide⟩
  · exact c2_edge_canonical_16 ⟨5,by decide⟩
  · exact c2_edge_canonical_16 ⟨6,by decide⟩
  · exact c2_edge_canonical_16 ⟨7,by decide⟩
  · exact c2_edge_canonical_16 ⟨8,by decide⟩
  · exact c2_edge_canonical_16 ⟨9,by decide⟩
  · exact c2_edge_canonical_16 ⟨10,by decide⟩
  · exact c2_edge_canonical_16 ⟨11,by decide⟩
  · exact c2_edge_canonical_16 ⟨12,by decide⟩
  · exact c2_edge_canonical_16 ⟨13,by decide⟩
  · exact c2_edge_canonical_16 ⟨14,by decide⟩
  · exact c2_edge_canonical_16 ⟨15,by decide⟩
  · exact c2_edge_canonical_16 ⟨16,by decide⟩
  · exact c2_edge_canonical_16 ⟨17,by decide⟩
  · exact c2_edge_canonical_16 ⟨18,by decide⟩
  · exact c2_edge_canonical_16 ⟨19,by decide⟩
  · exact c2_edge_canonical_17 ⟨0,by decide⟩
  · exact c2_edge_canonical_17 ⟨1,by decide⟩
  · exact c2_edge_canonical_17 ⟨2,by decide⟩
  · exact c2_edge_canonical_17 ⟨3,by decide⟩
  · exact c2_edge_canonical_17 ⟨4,by decide⟩
  · exact c2_edge_canonical_17 ⟨5,by decide⟩
  · exact c2_edge_canonical_17 ⟨6,by decide⟩
  · exact c2_edge_canonical_17 ⟨7,by decide⟩
  · exact c2_edge_canonical_17 ⟨8,by decide⟩
  · exact c2_edge_canonical_17 ⟨9,by decide⟩
  · exact c2_edge_canonical_17 ⟨10,by decide⟩
  · exact c2_edge_canonical_17 ⟨11,by decide⟩
  · exact c2_edge_canonical_17 ⟨12,by decide⟩
  · exact c2_edge_canonical_17 ⟨13,by decide⟩
  · exact c2_edge_canonical_17 ⟨14,by decide⟩
  · exact c2_edge_canonical_17 ⟨15,by decide⟩
  · exact c2_edge_canonical_17 ⟨16,by decide⟩
  · exact c2_edge_canonical_17 ⟨17,by decide⟩
  · exact c2_edge_canonical_17 ⟨18,by decide⟩
  · exact c2_edge_canonical_17 ⟨19,by decide⟩
  · exact c2_edge_canonical_18 ⟨0,by decide⟩
  · exact c2_edge_canonical_18 ⟨1,by decide⟩
  · exact c2_edge_canonical_18 ⟨2,by decide⟩
  · exact c2_edge_canonical_18 ⟨3,by decide⟩
  · exact c2_edge_canonical_18 ⟨4,by decide⟩
  · exact c2_edge_canonical_18 ⟨5,by decide⟩
  · exact c2_edge_canonical_18 ⟨6,by decide⟩
  · exact c2_edge_canonical_18 ⟨7,by decide⟩
  · exact c2_edge_canonical_18 ⟨8,by decide⟩
  · exact c2_edge_canonical_18 ⟨9,by decide⟩
  · exact c2_edge_canonical_18 ⟨10,by decide⟩
  · exact c2_edge_canonical_18 ⟨11,by decide⟩
  · exact c2_edge_canonical_18 ⟨12,by decide⟩
  · exact c2_edge_canonical_18 ⟨13,by decide⟩
  · exact c2_edge_canonical_18 ⟨14,by decide⟩
  · exact c2_edge_canonical_18 ⟨15,by decide⟩
  · exact c2_edge_canonical_18 ⟨16,by decide⟩
  · exact c2_edge_canonical_18 ⟨17,by decide⟩
  · exact c2_edge_canonical_18 ⟨18,by decide⟩
  · exact c2_edge_canonical_18 ⟨19,by decide⟩
  · exact c2_edge_canonical_19 ⟨0,by decide⟩
  · exact c2_edge_canonical_19 ⟨1,by decide⟩
  · exact c2_edge_canonical_19 ⟨2,by decide⟩
  · exact c2_edge_canonical_19 ⟨3,by decide⟩
  · exact c2_edge_canonical_19 ⟨4,by decide⟩
  · exact c2_edge_canonical_19 ⟨5,by decide⟩
  · exact c2_edge_canonical_19 ⟨6,by decide⟩
  · exact c2_edge_canonical_19 ⟨7,by decide⟩
  · exact c2_edge_canonical_19 ⟨8,by decide⟩
  · exact c2_edge_canonical_19 ⟨9,by decide⟩
  · exact c2_edge_canonical_19 ⟨10,by decide⟩
  · exact c2_edge_canonical_19 ⟨11,by decide⟩
  · exact c2_edge_canonical_19 ⟨12,by decide⟩
  · exact c2_edge_canonical_19 ⟨13,by decide⟩
  · exact c2_edge_canonical_19 ⟨14,by decide⟩
  · exact c2_edge_canonical_19 ⟨15,by decide⟩
  · exact c2_edge_canonical_19 ⟨16,by decide⟩
  · exact c2_edge_canonical_19 ⟨17,by decide⟩
  · exact c2_edge_canonical_19 ⟨18,by decide⟩
  · exact c2_edge_canonical_19 ⟨19,by decide⟩
  · exact c2_edge_canonical_20 ⟨0,by decide⟩
  · exact c2_edge_canonical_20 ⟨1,by decide⟩
  · exact c2_edge_canonical_20 ⟨2,by decide⟩
  · exact c2_edge_canonical_20 ⟨3,by decide⟩
  · exact c2_edge_canonical_20 ⟨4,by decide⟩
  · exact c2_edge_canonical_20 ⟨5,by decide⟩
  · exact c2_edge_canonical_20 ⟨6,by decide⟩
  · exact c2_edge_canonical_20 ⟨7,by decide⟩
  · exact c2_edge_canonical_20 ⟨8,by decide⟩
  · exact c2_edge_canonical_20 ⟨9,by decide⟩
  · exact c2_edge_canonical_20 ⟨10,by decide⟩
  · exact c2_edge_canonical_20 ⟨11,by decide⟩
  · exact c2_edge_canonical_20 ⟨12,by decide⟩
  · exact c2_edge_canonical_20 ⟨13,by decide⟩
  · exact c2_edge_canonical_20 ⟨14,by decide⟩
  · exact c2_edge_canonical_20 ⟨15,by decide⟩
  · exact c2_edge_canonical_20 ⟨16,by decide⟩
  · exact c2_edge_canonical_20 ⟨17,by decide⟩
  · exact c2_edge_canonical_20 ⟨18,by decide⟩
  · exact c2_edge_canonical_20 ⟨19,by decide⟩
  · exact c2_edge_canonical_21 ⟨0,by decide⟩
  · exact c2_edge_canonical_21 ⟨1,by decide⟩
  · exact c2_edge_canonical_21 ⟨2,by decide⟩
  · exact c2_edge_canonical_21 ⟨3,by decide⟩
  · exact c2_edge_canonical_21 ⟨4,by decide⟩
  · exact c2_edge_canonical_21 ⟨5,by decide⟩
  · exact c2_edge_canonical_21 ⟨6,by decide⟩
  · exact c2_edge_canonical_21 ⟨7,by decide⟩
  · exact c2_edge_canonical_21 ⟨8,by decide⟩
  · exact c2_edge_canonical_21 ⟨9,by decide⟩
  · exact c2_edge_canonical_21 ⟨10,by decide⟩
  · exact c2_edge_canonical_21 ⟨11,by decide⟩
  · exact c2_edge_canonical_21 ⟨12,by decide⟩
  · exact c2_edge_canonical_21 ⟨13,by decide⟩
  · exact c2_edge_canonical_21 ⟨14,by decide⟩
  · exact c2_edge_canonical_21 ⟨15,by decide⟩
  · exact c2_edge_canonical_21 ⟨16,by decide⟩
  · exact c2_edge_canonical_21 ⟨17,by decide⟩
  · exact c2_edge_canonical_21 ⟨18,by decide⟩
  · exact c2_edge_canonical_21 ⟨19,by decide⟩
  · exact c2_edge_canonical_22 ⟨0,by decide⟩
  · exact c2_edge_canonical_22 ⟨1,by decide⟩
  · exact c2_edge_canonical_22 ⟨2,by decide⟩
  · exact c2_edge_canonical_22 ⟨3,by decide⟩
  · exact c2_edge_canonical_22 ⟨4,by decide⟩
  · exact c2_edge_canonical_22 ⟨5,by decide⟩
  · exact c2_edge_canonical_22 ⟨6,by decide⟩
  · exact c2_edge_canonical_22 ⟨7,by decide⟩
  · exact c2_edge_canonical_22 ⟨8,by decide⟩
  · exact c2_edge_canonical_22 ⟨9,by decide⟩
  · exact c2_edge_canonical_22 ⟨10,by decide⟩
  · exact c2_edge_canonical_22 ⟨11,by decide⟩
  · exact c2_edge_canonical_22 ⟨12,by decide⟩
  · exact c2_edge_canonical_22 ⟨13,by decide⟩
  · exact c2_edge_canonical_22 ⟨14,by decide⟩
  · exact c2_edge_canonical_22 ⟨15,by decide⟩
  · exact c2_edge_canonical_22 ⟨16,by decide⟩
  · exact c2_edge_canonical_22 ⟨17,by decide⟩
  · exact c2_edge_canonical_22 ⟨18,by decide⟩
  · exact c2_edge_canonical_22 ⟨19,by decide⟩
  · exact c2_edge_canonical_23 ⟨0,by decide⟩
  · exact c2_edge_canonical_23 ⟨1,by decide⟩
  · exact c2_edge_canonical_23 ⟨2,by decide⟩
  · exact c2_edge_canonical_23 ⟨3,by decide⟩
  · exact c2_edge_canonical_23 ⟨4,by decide⟩
  · exact c2_edge_canonical_23 ⟨5,by decide⟩
  · exact c2_edge_canonical_23 ⟨6,by decide⟩
  · exact c2_edge_canonical_23 ⟨7,by decide⟩
  · exact c2_edge_canonical_23 ⟨8,by decide⟩
  · exact c2_edge_canonical_23 ⟨9,by decide⟩
  · exact c2_edge_canonical_23 ⟨10,by decide⟩
  · exact c2_edge_canonical_23 ⟨11,by decide⟩
  · exact c2_edge_canonical_23 ⟨12,by decide⟩
  · exact c2_edge_canonical_23 ⟨13,by decide⟩
  · exact c2_edge_canonical_23 ⟨14,by decide⟩
  · exact c2_edge_canonical_23 ⟨15,by decide⟩
  · exact c2_edge_canonical_23 ⟨16,by decide⟩
  · exact c2_edge_canonical_23 ⟨17,by decide⟩
  · exact c2_edge_canonical_23 ⟨18,by decide⟩
  · exact c2_edge_canonical_23 ⟨19,by decide⟩
  · exact c2_edge_canonical_24 ⟨0,by decide⟩
  · exact c2_edge_canonical_24 ⟨1,by decide⟩
  · exact c2_edge_canonical_24 ⟨2,by decide⟩
  · exact c2_edge_canonical_24 ⟨3,by decide⟩
  · exact c2_edge_canonical_24 ⟨4,by decide⟩
  · exact c2_edge_canonical_24 ⟨5,by decide⟩
  · exact c2_edge_canonical_24 ⟨6,by decide⟩
  · exact c2_edge_canonical_24 ⟨7,by decide⟩
  · exact c2_edge_canonical_24 ⟨8,by decide⟩
  · exact c2_edge_canonical_24 ⟨9,by decide⟩
  · exact c2_edge_canonical_24 ⟨10,by decide⟩
  · exact c2_edge_canonical_24 ⟨11,by decide⟩
  · exact c2_edge_canonical_24 ⟨12,by decide⟩
  · exact c2_edge_canonical_24 ⟨13,by decide⟩
  · exact c2_edge_canonical_24 ⟨14,by decide⟩
  · exact c2_edge_canonical_24 ⟨15,by decide⟩
  · exact c2_edge_canonical_24 ⟨16,by decide⟩
  · exact c2_edge_canonical_24 ⟨17,by decide⟩
  · exact c2_edge_canonical_24 ⟨18,by decide⟩
  · exact c2_edge_canonical_24 ⟨19,by decide⟩
  · exact c2_edge_canonical_25 ⟨0,by decide⟩
  · exact c2_edge_canonical_25 ⟨1,by decide⟩
  · exact c2_edge_canonical_25 ⟨2,by decide⟩
  · exact c2_edge_canonical_25 ⟨3,by decide⟩
  · exact c2_edge_canonical_25 ⟨4,by decide⟩
  · exact c2_edge_canonical_25 ⟨5,by decide⟩
  · exact c2_edge_canonical_25 ⟨6,by decide⟩
  · exact c2_edge_canonical_25 ⟨7,by decide⟩
  · exact c2_edge_canonical_25 ⟨8,by decide⟩
  · exact c2_edge_canonical_25 ⟨9,by decide⟩
  · exact c2_edge_canonical_25 ⟨10,by decide⟩
  · exact c2_edge_canonical_25 ⟨11,by decide⟩
  · exact c2_edge_canonical_25 ⟨12,by decide⟩
  · exact c2_edge_canonical_25 ⟨13,by decide⟩
  · exact c2_edge_canonical_25 ⟨14,by decide⟩
  · exact c2_edge_canonical_25 ⟨15,by decide⟩
  · exact c2_edge_canonical_25 ⟨16,by decide⟩
  · exact c2_edge_canonical_25 ⟨17,by decide⟩
  · exact c2_edge_canonical_25 ⟨18,by decide⟩
  · exact c2_edge_canonical_25 ⟨19,by decide⟩
  · exact c2_edge_canonical_26 ⟨0,by decide⟩
  · exact c2_edge_canonical_26 ⟨1,by decide⟩
  · exact c2_edge_canonical_26 ⟨2,by decide⟩
  · exact c2_edge_canonical_26 ⟨3,by decide⟩
  · exact c2_edge_canonical_26 ⟨4,by decide⟩
  · exact c2_edge_canonical_26 ⟨5,by decide⟩
  · exact c2_edge_canonical_26 ⟨6,by decide⟩
  · exact c2_edge_canonical_26 ⟨7,by decide⟩
  · exact c2_edge_canonical_26 ⟨8,by decide⟩
  · exact c2_edge_canonical_26 ⟨9,by decide⟩
  · exact c2_edge_canonical_26 ⟨10,by decide⟩
  · exact c2_edge_canonical_26 ⟨11,by decide⟩
  · exact c2_edge_canonical_26 ⟨12,by decide⟩
  · exact c2_edge_canonical_26 ⟨13,by decide⟩
  · exact c2_edge_canonical_26 ⟨14,by decide⟩
  · exact c2_edge_canonical_26 ⟨15,by decide⟩
  · exact c2_edge_canonical_26 ⟨16,by decide⟩
  · exact c2_edge_canonical_26 ⟨17,by decide⟩
  · exact c2_edge_canonical_26 ⟨18,by decide⟩
  · exact c2_edge_canonical_26 ⟨19,by decide⟩
  · exact c2_edge_canonical_27 ⟨0,by decide⟩
  · exact c2_edge_canonical_27 ⟨1,by decide⟩
  · exact c2_edge_canonical_27 ⟨2,by decide⟩
  · exact c2_edge_canonical_27 ⟨3,by decide⟩
  · exact c2_edge_canonical_27 ⟨4,by decide⟩
  · exact c2_edge_canonical_27 ⟨5,by decide⟩
  · exact c2_edge_canonical_27 ⟨6,by decide⟩
  · exact c2_edge_canonical_27 ⟨7,by decide⟩
  · exact c2_edge_canonical_27 ⟨8,by decide⟩
  · exact c2_edge_canonical_27 ⟨9,by decide⟩
  · exact c2_edge_canonical_27 ⟨10,by decide⟩
  · exact c2_edge_canonical_27 ⟨11,by decide⟩
  · exact c2_edge_canonical_27 ⟨12,by decide⟩
  · exact c2_edge_canonical_27 ⟨13,by decide⟩
  · exact c2_edge_canonical_27 ⟨14,by decide⟩
  · exact c2_edge_canonical_27 ⟨15,by decide⟩
  · exact c2_edge_canonical_27 ⟨16,by decide⟩
  · exact c2_edge_canonical_27 ⟨17,by decide⟩
  · exact c2_edge_canonical_27 ⟨18,by decide⟩
  · exact c2_edge_canonical_27 ⟨19,by decide⟩
  · exact c2_edge_canonical_28 ⟨0,by decide⟩
  · exact c2_edge_canonical_28 ⟨1,by decide⟩
  · exact c2_edge_canonical_28 ⟨2,by decide⟩
  · exact c2_edge_canonical_28 ⟨3,by decide⟩
  · exact c2_edge_canonical_28 ⟨4,by decide⟩
  · exact c2_edge_canonical_28 ⟨5,by decide⟩
  · exact c2_edge_canonical_28 ⟨6,by decide⟩
  · exact c2_edge_canonical_28 ⟨7,by decide⟩
  · exact c2_edge_canonical_28 ⟨8,by decide⟩
  · exact c2_edge_canonical_28 ⟨9,by decide⟩
  · exact c2_edge_canonical_28 ⟨10,by decide⟩
  · exact c2_edge_canonical_28 ⟨11,by decide⟩
  · exact c2_edge_canonical_28 ⟨12,by decide⟩
  · exact c2_edge_canonical_28 ⟨13,by decide⟩
  · exact c2_edge_canonical_28 ⟨14,by decide⟩
  · exact c2_edge_canonical_28 ⟨15,by decide⟩
  · exact c2_edge_canonical_28 ⟨16,by decide⟩
  · exact c2_edge_canonical_28 ⟨17,by decide⟩
  · exact c2_edge_canonical_28 ⟨18,by decide⟩
  · exact c2_edge_canonical_28 ⟨19,by decide⟩
theorem c2_slack_incidence : ∀ f r,
    (OnMask c2FacetMask f r → ∀ k,
      integerSlack c2IntegerGenerators c2VertexCoefficients (c2FacetNormal f) r k = 0) ∧
    (¬OnMask c2FacetMask f r →
      0 < integerSlack c2IntegerGenerators c2VertexCoefficients (c2FacetNormal f) r
        (c2SlackWitness f r)) := by
  intro f
  fin_cases f
  · exact c2_slack_incidence_0
  · exact c2_slack_incidence_1
  · exact c2_slack_incidence_2
  · exact c2_slack_incidence_3
  · exact c2_slack_incidence_4
  · exact c2_slack_incidence_5
  · exact c2_slack_incidence_6
  · exact c2_slack_incidence_7
  · exact c2_slack_incidence_8
  · exact c2_slack_incidence_9
  · exact c2_slack_incidence_10
  · exact c2_slack_incidence_11
  · exact c2_slack_incidence_12
  · exact c2_slack_incidence_13
  · exact c2_slack_incidence_14
  · exact c2_slack_incidence_15
  · exact c2_slack_incidence_16
  · exact c2_slack_incidence_17
  · exact c2_slack_incidence_18
  · exact c2_slack_incidence_19
  · exact c2_slack_incidence_20
  · exact c2_slack_incidence_21
  · exact c2_slack_incidence_22
  · exact c2_slack_incidence_23
  · exact c2_slack_incidence_24
  · exact c2_slack_incidence_25
  · exact c2_slack_incidence_26
  · exact c2_slack_incidence_27
  · exact c2_slack_incidence_28
  · exact c2_slack_incidence_29
def c2Slack (w : Fin 10 → ℝ) (f : Fin 30) : AffineSlack :=
  facetSlack (secondaryForm (fun j => castVec (c2IntegerGenerators j))
    (w 0) (fun j => w j.succ)) (c2FacetNormal f)

def c2CellVertices (w : Fin 10 → ℝ) (t : Fin 580) : Fin 5 → Vec :=
  cellVertices (secondaryVertex c2VertexCoefficients w) (c2Cell t)

theorem c2_slack_geometry (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) (f r) :
    (OnMask c2FacetMask f r → (c2Slack w f).eval (secondaryVertex c2VertexCoefficients w r) = 0) ∧
    (¬OnMask c2FacetMask f r → 0 < (c2Slack w f).eval (secondaryVertex c2VertexCoefficients w r)) := by
  constructor
  · intro h
    exact slack_zero_of_coefficients _ _ _ _ _ ((c2_slack_incidence f r).1 h)
  · intro h
    exact slack_pos_of_coefficients _ _ _ _ _ hw (c2_integerSlack_nonneg _ r)
      (c2SlackWitness f r) ((c2_slack_incidence f r).2 h)

theorem c2_cell_geometry (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) (t : Fin 580) :
    FanCellGeometry (c2Slack w) (secondaryVertex c2VertexCoefficients w) (c2Cell t) :=
  fanCellGeometry_of_mask c2FacetMask _ _ _ (c2_slack_geometry w hw) (c2_cell_incidence t)

theorem c2_cells_pairwise_null (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) :
    Pairwise fun i j => volume (vertexSimplex (c2CellVertices w i) ∩
      vertexSimplex (c2CellVertices w j)) = 0 := by
  apply cells_pairwise_null c2Cell c2FacetMask c2FacetApex c2FaceApex
    (c2Slack w) (secondaryVertex c2VertexCoefficients w)
    c2_facet_masks_bounded c2_facet_masks_injective
    (Fin.strictMono_iff_lt_succ.mpr c2_cell_keys_increasing).injective
    c2_cell_apices c2_cell_incidence c2_face_canonical c2_edge_canonical
    (c2_slack_geometry w hw)
  intro f
  exact facetSlack_origin_pos
    (secondary_posDef_of_pos _ (hw 0) (fun j => (hw j.succ).le)) _
    (c2_facet_normals_ne_zero f)

theorem c2_cells_support (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) (t : Fin 580) :
    ∀ j, c2CellVertices w t j ∈
      dualRegion (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) := by
  apply fanCellVertices_forall (secondaryVertex c2VertexCoefficients w) (c2Cell t)
  · intro z
    simp only [dotProduct_zero]
    have hQ := secondary_posDef_of_pos cone2Vectors (hw 0) (fun j => (hw j.succ).le)
    by_cases hz : castVec z = 0
    · simp [hz,quadratic]
    · exact le_of_lt (by simpa only [quadratic,star_trivial] using hQ.2 (castVec z) hz)
  all_goals exact c2_vertex_support w (fun k => (hw k).le) _

end D4.Secondary
