import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup180_det_check : c2TensorGroup180.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 226)) = true := by kernel_rfl
private def c2GroupHessian180_00Chunk0 : Poly := [([0,0], 112),([0,1], 64),([0,5], -8),([0,6], 64),([1,1], 32),([1,5], -8),([1,6], 64),([5,5], 24),([5,6], -8),([6,6], 32)]
def c2GroupHessian180_00 : Poly := List.flatten [c2GroupHessian180_00Chunk0]
theorem c2GroupHessian180_00_check : sumFast (c2TensorGroup180.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian180_00 := by kernel_rfl
private def c2GroupHessian180_01Chunk0 : Poly := [([0,0], 160),([0,2], 80),([0,7], 80),([0,8], 80)]
def c2GroupHessian180_01 : Poly := List.flatten [c2GroupHessian180_01Chunk0]
theorem c2GroupHessian180_01_check : sumFast (c2TensorGroup180.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian180_01 := by kernel_rfl
private def c2GroupHessian180_02Chunk0 : Poly := [([0,0], -48),([0,1], 32),([0,3], 32),([0,6], 32),([0,7], -80),([0,9], 32),([1,3], 32),([1,5], 4),([1,9], 32),([3,5], -4),([3,6], 32),([5,5], -24),([5,6], 4),([5,9], -4),([6,9], 32)]
def c2GroupHessian180_02 : Poly := List.flatten [c2GroupHessian180_02Chunk0]
theorem c2GroupHessian180_02_check : sumFast (c2TensorGroup180.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian180_02 := by kernel_rfl
private def c2GroupHessian180_03Chunk0 : Poly := [([0,0], -112),([0,1], -32),([0,4], -4),([0,5], 4),([0,6], -64),([0,8], -80),([0,9], -32),([1,4], -4),([1,6], -32),([1,9], -32),([4,5], 8),([4,6], -4),([5,6], 4),([5,9], 4),([6,6], -32),([6,9], -32)]
def c2GroupHessian180_03 : Poly := List.flatten [c2GroupHessian180_03Chunk0]
theorem c2GroupHessian180_03_check : sumFast (c2TensorGroup180.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian180_03 := by kernel_rfl
private def c2GroupHessian180_11Chunk0 : Poly := [([0,0], 320),([0,2], 320),([0,7], 320),([0,8], 320),([2,2], 80),([2,7], 160),([2,8], 160),([7,7], 80),([7,8], 160),([8,8], 80)]
def c2GroupHessian180_11 : Poly := List.flatten [c2GroupHessian180_11Chunk0]
theorem c2GroupHessian180_11_check : sumFast (c2TensorGroup180.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian180_11 := by kernel_rfl
private def c2GroupHessian180_12Chunk0 : Poly := [([0,0], -160),([0,2], -80),([0,7], -240),([0,8], -80),([2,7], -80),([7,7], -80),([7,8], -80)]
def c2GroupHessian180_12 : Poly := List.flatten [c2GroupHessian180_12Chunk0]
theorem c2GroupHessian180_12_check : sumFast (c2TensorGroup180.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian180_12 := by kernel_rfl
private def c2GroupHessian180_13Chunk0 : Poly := [([0,0], -160),([0,2], -80),([0,7], -80),([0,8], -240),([2,8], -80),([7,8], -80),([8,8], -80)]
def c2GroupHessian180_13 : Poly := List.flatten [c2GroupHessian180_13Chunk0]
theorem c2GroupHessian180_13_check : sumFast (c2TensorGroup180.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian180_13 := by kernel_rfl
private def c2GroupHessian180_22Chunk0 : Poly := [([0,0], 112),([0,3], 64),([0,5], 8),([0,7], 160),([0,9], 64),([3,3], 32),([3,5], 8),([3,9], 64),([5,5], 24),([5,9], 8),([7,7], 80),([9,9], 32)]
def c2GroupHessian180_22 : Poly := List.flatten [c2GroupHessian180_22Chunk0]
theorem c2GroupHessian180_22_check : sumFast (c2TensorGroup180.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian180_22 := by kernel_rfl
private def c2GroupHessian180_23Chunk0 : Poly := [([0,0], 48),([0,3], -32),([0,4], -4),([0,5], -4),([0,6], -32),([0,7], 80),([0,8], 80),([0,9], -64),([3,4], -4),([3,6], -32),([3,9], -32),([4,5], -8),([4,9], -4),([5,6], -4),([5,9], -4),([6,9], -32),([7,8], 80),([9,9], -32)]
def c2GroupHessian180_23 : Poly := List.flatten [c2GroupHessian180_23Chunk0]
theorem c2GroupHessian180_23_check : sumFast (c2TensorGroup180.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian180_23 := by kernel_rfl
private def c2GroupHessian180_33Chunk0 : Poly := [([0,0], 112),([0,4], 8),([0,6], 64),([0,8], 160),([0,9], 64),([4,4], 24),([4,6], 8),([4,9], 8),([6,6], 32),([6,9], 64),([8,8], 80),([9,9], 32)]
def c2GroupHessian180_33 : Poly := List.flatten [c2GroupHessian180_33Chunk0]
theorem c2GroupHessian180_33_check : sumFast (c2TensorGroup180.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian180_33 := by kernel_rfl
end D4.Secondary
