import D4.C3CellCanonicalAssembly
import D4.C3CellIncidence
import D4.C23CellRealization
import D4.PrincipalDualRegion
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
import D4.C3FacetSlack00
import D4.C3FacetSlack01
import D4.C3FacetSlack02
import D4.C3FacetSlack03
import D4.C3FacetSlack04
import D4.C3FacetSlack05
import D4.C3FacetSlack06
import D4.C3FacetSlack07
import D4.C3FacetSlack08
import D4.C3FacetSlack09
import D4.C3FacetSlack10
import D4.C3FacetSlack11
import D4.C3FacetSlack12
import D4.C3FacetSlack13
import D4.C3FacetSlack14
import D4.C3FacetSlack15
import D4.C3FacetSlack16
import D4.C3FacetSlack17
import D4.C3FacetSlack18
import D4.C3FacetSlack19
import D4.C3FacetSlack20
import D4.C3FacetSlack21
import D4.C3FacetSlack22
import D4.C3FacetSlack23
import D4.C3FacetSlack24
import D4.C3FacetSlack25
import D4.C3FacetSlack26
import D4.C3FacetSlack27
import D4.C3FacetSlack28
import D4.C3FacetSlack29
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal MeasureTheory
theorem c3_slack_incidence : ∀ f r,
    (OnMask c3FacetMask f r → ∀ k,
      integerSlack c3IntegerGenerators c3VertexCoefficients (c3FacetNormal f) r k = 0) ∧
    (¬OnMask c3FacetMask f r →
      0 < integerSlack c3IntegerGenerators c3VertexCoefficients (c3FacetNormal f) r
        (c3SlackWitness f r)) := by
  intro f
  fin_cases f
  · exact c3_slack_incidence_0
  · exact c3_slack_incidence_1
  · exact c3_slack_incidence_2
  · exact c3_slack_incidence_3
  · exact c3_slack_incidence_4
  · exact c3_slack_incidence_5
  · exact c3_slack_incidence_6
  · exact c3_slack_incidence_7
  · exact c3_slack_incidence_8
  · exact c3_slack_incidence_9
  · exact c3_slack_incidence_10
  · exact c3_slack_incidence_11
  · exact c3_slack_incidence_12
  · exact c3_slack_incidence_13
  · exact c3_slack_incidence_14
  · exact c3_slack_incidence_15
  · exact c3_slack_incidence_16
  · exact c3_slack_incidence_17
  · exact c3_slack_incidence_18
  · exact c3_slack_incidence_19
  · exact c3_slack_incidence_20
  · exact c3_slack_incidence_21
  · exact c3_slack_incidence_22
  · exact c3_slack_incidence_23
  · exact c3_slack_incidence_24
  · exact c3_slack_incidence_25
  · exact c3_slack_incidence_26
  · exact c3_slack_incidence_27
  · exact c3_slack_incidence_28
  · exact c3_slack_incidence_29
def c3Slack (w : Fin 10 → ℝ) (f : Fin 30) : AffineSlack :=
  facetSlack (secondaryForm (fun j => castVec (c3IntegerGenerators j))
    (w 0) (fun j => w j.succ)) (c3FacetNormal f)

def c3CellVertices (w : Fin 10 → ℝ) (t : Fin 582) : Fin 5 → Vec :=
  cellVertices (secondaryVertex c3VertexCoefficients w) (c3Cell t)

theorem c3_slack_geometry (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) (f r) :
    (OnMask c3FacetMask f r → (c3Slack w f).eval (secondaryVertex c3VertexCoefficients w r) = 0) ∧
    (¬OnMask c3FacetMask f r → 0 < (c3Slack w f).eval (secondaryVertex c3VertexCoefficients w r)) := by
  constructor
  · intro h
    exact slack_zero_of_coefficients _ _ _ _ _ ((c3_slack_incidence f r).1 h)
  · intro h
    exact slack_pos_of_coefficients _ _ _ _ _ hw (c3_integerSlack_nonneg _ r)
      (c3SlackWitness f r) ((c3_slack_incidence f r).2 h)

theorem c3_cell_geometry (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) (t : Fin 582) :
    FanCellGeometry (c3Slack w) (secondaryVertex c3VertexCoefficients w) (c3Cell t) :=
  fanCellGeometry_of_mask c3FacetMask _ _ _ (c3_slack_geometry w hw) (c3_cell_incidence t)

theorem c3_cells_pairwise_null (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) :
    Pairwise fun i j => volume (vertexSimplex (c3CellVertices w i) ∩
      vertexSimplex (c3CellVertices w j)) = 0 := by
  apply cells_pairwise_null c3Cell c3FacetMask c3FacetApex c3FaceApex
    (c3Slack w) (secondaryVertex c3VertexCoefficients w)
    c3_facet_masks_bounded c3_facet_masks_injective
    (Fin.strictMono_iff_lt_succ.mpr c3_cell_keys_increasing).injective
    c3_cell_apices c3_cell_incidence c3_face_canonical c3_edge_canonical
    (c3_slack_geometry w hw)
  intro f
  exact facetSlack_origin_pos
    (secondary_posDef_of_pos _ (hw 0) (fun j => (hw j.succ).le)) _
    (c3_facet_normals_ne_zero f)

theorem c3_cells_support (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) (t : Fin 582) :
    ∀ j, c3CellVertices w t j ∈
      dualRegion (secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) := by
  apply fanCellVertices_forall (secondaryVertex c3VertexCoefficients w) (c3Cell t)
  · intro z
    simp only [dotProduct_zero]
    have hQ := secondary_posDef_of_pos cone3Vectors (hw 0) (fun j => (hw j.succ).le)
    by_cases hz : castVec z = 0
    · simp [hz,quadratic]
    · exact le_of_lt (by simpa only [quadratic,star_trivial] using hQ.2 (castVec z) hz)
  all_goals exact c3_vertex_support w (fun k => (hw k).le) _

end D4.Secondary
