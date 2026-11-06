import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup94_det_check : c2TensorGroup94.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 123)) = true := by kernel_rfl
private def c2GroupHessian94_00Chunk0 : Poly := [([0,0], 320),([0,1], 320),([0,5], 320),([0,6], 320),([1,1], 80),([1,5], 160),([1,6], 160),([5,5], 80),([5,6], 160),([6,6], 80)]
def c2GroupHessian94_00 : Poly := List.flatten [c2GroupHessian94_00Chunk0]
theorem c2GroupHessian94_00_check : sumFast (c2TensorGroup94.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian94_00 := by kernel_rfl
private def c2GroupHessian94_01Chunk0 : Poly := [([0,0], 160),([0,1], 80),([0,5], 80),([0,6], 80)]
def c2GroupHessian94_01 : Poly := List.flatten [c2GroupHessian94_01Chunk0]
theorem c2GroupHessian94_01_check : sumFast (c2TensorGroup94.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian94_01 := by kernel_rfl
private def c2GroupHessian94_02Chunk0 : Poly := [([0,0], -160),([0,1], -80),([0,5], -240),([0,6], -80),([1,5], -80),([5,5], -80),([5,6], -80)]
def c2GroupHessian94_02 : Poly := List.flatten [c2GroupHessian94_02Chunk0]
theorem c2GroupHessian94_02_check : sumFast (c2TensorGroup94.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian94_02 := by kernel_rfl
private def c2GroupHessian94_03Chunk0 : Poly := [([0,0], -160),([0,1], -80),([0,5], -80),([0,6], -240),([1,6], -80),([5,6], -80),([6,6], -80)]
def c2GroupHessian94_03 : Poly := List.flatten [c2GroupHessian94_03Chunk0]
theorem c2GroupHessian94_03_check : sumFast (c2TensorGroup94.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian94_03 := by kernel_rfl
private def c2GroupHessian94_11Chunk0 : Poly := [([0,0], 112),([0,2], 64),([0,7], -8),([0,8], 64),([2,2], 32),([2,7], -8),([2,8], 64),([7,7], 24),([7,8], -8),([8,8], 32)]
def c2GroupHessian94_11 : Poly := List.flatten [c2GroupHessian94_11Chunk0]
theorem c2GroupHessian94_11_check : sumFast (c2TensorGroup94.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian94_11 := by kernel_rfl
private def c2GroupHessian94_12Chunk0 : Poly := [([0,0], -48),([0,2], 32),([0,3], 32),([0,5], -80),([0,8], 32),([0,9], 32),([2,3], 32),([2,7], 4),([2,9], 32),([3,7], -4),([3,8], 32),([7,7], -24),([7,8], 4),([7,9], -4),([8,9], 32)]
def c2GroupHessian94_12 : Poly := List.flatten [c2GroupHessian94_12Chunk0]
theorem c2GroupHessian94_12_check : sumFast (c2TensorGroup94.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian94_12 := by kernel_rfl
private def c2GroupHessian94_13Chunk0 : Poly := [([0,0], -112),([0,2], -32),([0,4], -4),([0,6], -80),([0,7], 4),([0,8], -64),([0,9], -32),([2,4], -4),([2,8], -32),([2,9], -32),([4,7], 8),([4,8], -4),([7,8], 4),([7,9], 4),([8,8], -32),([8,9], -32)]
def c2GroupHessian94_13 : Poly := List.flatten [c2GroupHessian94_13Chunk0]
theorem c2GroupHessian94_13_check : sumFast (c2TensorGroup94.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian94_13 := by kernel_rfl
private def c2GroupHessian94_22Chunk0 : Poly := [([0,0], 112),([0,3], 64),([0,5], 160),([0,7], 8),([0,9], 64),([3,3], 32),([3,7], 8),([3,9], 64),([5,5], 80),([7,7], 24),([7,9], 8),([9,9], 32)]
def c2GroupHessian94_22 : Poly := List.flatten [c2GroupHessian94_22Chunk0]
theorem c2GroupHessian94_22_check : sumFast (c2TensorGroup94.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian94_22 := by kernel_rfl
private def c2GroupHessian94_23Chunk0 : Poly := [([0,0], 48),([0,3], -32),([0,4], -4),([0,5], 80),([0,6], 80),([0,7], -4),([0,8], -32),([0,9], -64),([3,4], -4),([3,8], -32),([3,9], -32),([4,7], -8),([4,9], -4),([5,6], 80),([7,8], -4),([7,9], -4),([8,9], -32),([9,9], -32)]
def c2GroupHessian94_23 : Poly := List.flatten [c2GroupHessian94_23Chunk0]
theorem c2GroupHessian94_23_check : sumFast (c2TensorGroup94.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian94_23 := by kernel_rfl
private def c2GroupHessian94_33Chunk0 : Poly := [([0,0], 112),([0,4], 8),([0,6], 160),([0,8], 64),([0,9], 64),([4,4], 24),([4,8], 8),([4,9], 8),([6,6], 80),([8,8], 32),([8,9], 64),([9,9], 32)]
def c2GroupHessian94_33 : Poly := List.flatten [c2GroupHessian94_33Chunk0]
theorem c2GroupHessian94_33_check : sumFast (c2TensorGroup94.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian94_33 := by kernel_rfl
end D4.Secondary
