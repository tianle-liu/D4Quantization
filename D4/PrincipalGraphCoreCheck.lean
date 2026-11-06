import D4.PrincipalGraphCoreDefs
namespace D4.PrincipalGraphs
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem core_finite_check : fiveEdgeList.all coreCheck = true := by kernel_rfl

end D4.PrincipalGraphs
