import D4.PrincipalGraphFourDefs

namespace D4.PrincipalGraphs
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem four_finite_check : fourEdgeList.all fourCheck = true := by kernel_rfl

theorem treeEdgeSets_card : (Finset.univ.image treeEdgeSet).card = 125 := by kernel_rfl

end D4.PrincipalGraphs
