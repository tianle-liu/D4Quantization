import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup65_det_check : c2TensorGroup65.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 86)) = true := by kernel_rfl
private def c2GroupHessian65_00Chunk0 : Poly := [([0,0], 104),([0,1], 160),([0,5], 160),([0,6], 48),([1,1], 80),([1,5], 160),([5,5], 80),([6,6], 24)]
def c2GroupHessian65_00 : Poly := List.flatten [c2GroupHessian65_00Chunk0]
theorem c2GroupHessian65_00_check : sumFast (c2TensorGroup65.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian65_00 := by kernel_rfl
private def c2GroupHessian65_01Chunk0 : Poly := [([0,0], 16),([0,2], 8),([0,6], 16),([0,7], -4),([0,8], -80),([1,8], -80),([2,6], 8),([5,8], -80),([6,7], -4)]
def c2GroupHessian65_01 : Poly := List.flatten [c2GroupHessian65_01Chunk0]
theorem c2GroupHessian65_01_check : sumFast (c2TensorGroup65.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian65_01 := by kernel_rfl
private def c2GroupHessian65_02Chunk0 : Poly := [([0,0], -88),([0,1], -80),([0,3], 8),([0,5], -160),([0,6], -8),([0,7], 4),([0,9], -80),([1,5], -80),([1,9], -80),([3,6], 8),([5,5], -80),([5,9], -80),([6,7], 4)]
def c2GroupHessian65_02 : Poly := List.flatten [c2GroupHessian65_02Chunk0]
theorem c2GroupHessian65_02_check : sumFast (c2TensorGroup65.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian65_02 := by kernel_rfl
private def c2GroupHessian65_03Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,4], 80),([0,5], 80),([0,6], -48),([0,8], 80),([0,9], 80),([1,4], 80),([1,8], 80),([1,9], 80),([4,5], 80),([5,8], 80),([5,9], 80),([6,6], -24)]
def c2GroupHessian65_03 : Poly := List.flatten [c2GroupHessian65_03Chunk0]
theorem c2GroupHessian65_03_check : sumFast (c2TensorGroup65.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian65_03 := by kernel_rfl
private def c2GroupHessian65_11Chunk0 : Poly := [([0,0], 32),([0,2], 32),([0,7], 32),([2,2], 24),([2,7], -8),([7,7], 32),([8,8], 80)]
def c2GroupHessian65_11 : Poly := List.flatten [c2GroupHessian65_11Chunk0]
theorem c2GroupHessian65_11_check : sumFast (c2TensorGroup65.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian65_11 := by kernel_rfl
private def c2GroupHessian65_12Chunk0 : Poly := [([0,0], -16),([0,2], 8),([0,3], 16),([0,7], -36),([0,8], 80),([2,3], 24),([2,7], 4),([3,7], -4),([5,8], 80),([7,7], -32),([8,9], 80)]
def c2GroupHessian65_12 : Poly := List.flatten [c2GroupHessian65_12Chunk0]
theorem c2GroupHessian65_12_check : sumFast (c2TensorGroup65.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian65_12 := by kernel_rfl
private def c2GroupHessian65_13Chunk0 : Poly := [([0,0], -16),([0,2], -8),([0,6], -16),([0,7], 4),([0,8], -80),([2,6], -8),([4,8], -80),([6,7], 4),([8,8], -80),([8,9], -80)]
def c2GroupHessian65_13 : Poly := List.flatten [c2GroupHessian65_13Chunk0]
theorem c2GroupHessian65_13_check : sumFast (c2TensorGroup65.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian65_13 := by kernel_rfl
private def c2GroupHessian65_22Chunk0 : Poly := [([0,0], 104),([0,3], 16),([0,5], 160),([0,7], 40),([0,9], 160),([3,3], 24),([3,7], 8),([5,5], 80),([5,9], 160),([7,7], 32),([9,9], 80)]
def c2GroupHessian65_22 : Poly := List.flatten [c2GroupHessian65_22Chunk0]
theorem c2GroupHessian65_22_check : sumFast (c2TensorGroup65.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian65_22 := by kernel_rfl
private def c2GroupHessian65_23Chunk0 : Poly := [([0,0], -72),([0,3], -8),([0,4], -80),([0,5], -80),([0,6], 8),([0,7], -4),([0,8], -80),([0,9], -160),([3,6], -8),([4,5], -80),([4,9], -80),([5,8], -80),([5,9], -80),([6,7], -4),([8,9], -80),([9,9], -80)]
def c2GroupHessian65_23 : Poly := List.flatten [c2GroupHessian65_23Chunk0]
theorem c2GroupHessian65_23_check : sumFast (c2TensorGroup65.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian65_23 := by kernel_rfl
private def c2GroupHessian65_33Chunk0 : Poly := [([0,0], 104),([0,4], 160),([0,6], 48),([0,8], 160),([0,9], 160),([4,4], 80),([4,8], 160),([4,9], 160),([6,6], 24),([8,8], 80),([8,9], 160),([9,9], 80)]
def c2GroupHessian65_33 : Poly := List.flatten [c2GroupHessian65_33Chunk0]
theorem c2GroupHessian65_33_check : sumFast (c2TensorGroup65.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian65_33 := by kernel_rfl
end D4.Secondary
