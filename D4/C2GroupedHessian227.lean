import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup227_det_check : c2TensorGroup227.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 288)) = true := by kernel_rfl
private def c2GroupHessian227_00Chunk0 : Poly := [([0,0], 112),([0,1], 64),([0,5], -8),([0,6], 160),([1,1], 32),([1,5], -8),([5,5], 24),([6,6], 80)]
def c2GroupHessian227_00 : Poly := List.flatten [c2GroupHessian227_00Chunk0]
theorem c2GroupHessian227_00_check : sumFast (c2TensorGroup227.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian227_00 := by kernel_rfl
private def c2GroupHessian227_01Chunk0 : Poly := [([0,0], 112),([0,1], 32),([0,2], 32),([0,5], -4),([0,6], 80),([0,7], -4),([0,8], 80),([1,2], 32),([1,7], -4),([2,5], -4),([5,7], 8),([6,8], 80)]
def c2GroupHessian227_01 : Poly := List.flatten [c2GroupHessian227_01Chunk0]
theorem c2GroupHessian227_01_check : sumFast (c2TensorGroup227.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian227_01 := by kernel_rfl
private def c2GroupHessian227_02Chunk0 : Poly := [([0,3], 32),([0,5], 4),([0,7], 4),([0,9], 80),([1,3], 32),([1,5], 4),([1,7], 4),([3,5], -4),([5,5], -24),([5,7], -8),([6,9], 80)]
def c2GroupHessian227_02 : Poly := List.flatten [c2GroupHessian227_02Chunk0]
theorem c2GroupHessian227_02_check : sumFast (c2TensorGroup227.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian227_02 := by kernel_rfl
private def c2GroupHessian227_03Chunk0 : Poly := [([0,0], -160),([0,4], -80),([0,6], -240),([0,8], -80),([0,9], -80),([4,6], -80),([6,6], -80),([6,8], -80),([6,9], -80)]
def c2GroupHessian227_03 : Poly := List.flatten [c2GroupHessian227_03Chunk0]
theorem c2GroupHessian227_03_check : sumFast (c2TensorGroup227.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian227_03 := by kernel_rfl
private def c2GroupHessian227_11Chunk0 : Poly := [([0,0], 112),([0,2], 64),([0,7], -8),([0,8], 160),([2,2], 32),([2,7], -8),([7,7], 24),([8,8], 80)]
def c2GroupHessian227_11 : Poly := List.flatten [c2GroupHessian227_11Chunk0]
theorem c2GroupHessian227_11_check : sumFast (c2TensorGroup227.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian227_11 := by kernel_rfl
private def c2GroupHessian227_12Chunk0 : Poly := [([0,3], 32),([0,5], 4),([0,7], 4),([0,9], 80),([2,3], 32),([2,5], 4),([2,7], 4),([3,7], -4),([5,7], -8),([7,7], -24),([8,9], 80)]
def c2GroupHessian227_12 : Poly := List.flatten [c2GroupHessian227_12Chunk0]
theorem c2GroupHessian227_12_check : sumFast (c2TensorGroup227.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian227_12 := by kernel_rfl
private def c2GroupHessian227_13Chunk0 : Poly := [([0,0], -160),([0,4], -80),([0,6], -80),([0,8], -240),([0,9], -80),([4,8], -80),([6,8], -80),([8,8], -80),([8,9], -80)]
def c2GroupHessian227_13 : Poly := List.flatten [c2GroupHessian227_13Chunk0]
theorem c2GroupHessian227_13_check : sumFast (c2TensorGroup227.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian227_13 := by kernel_rfl
private def c2GroupHessian227_22Chunk0 : Poly := [([3,3], 32),([3,5], 8),([3,7], 8),([5,5], 24),([5,7], 16),([7,7], 24),([9,9], 80)]
def c2GroupHessian227_22 : Poly := List.flatten [c2GroupHessian227_22Chunk0]
theorem c2GroupHessian227_22_check : sumFast (c2TensorGroup227.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian227_22 := by kernel_rfl
private def c2GroupHessian227_23Chunk0 : Poly := [([0,9], -160),([4,9], -80),([6,9], -80),([8,9], -80),([9,9], -80)]
def c2GroupHessian227_23 : Poly := List.flatten [c2GroupHessian227_23Chunk0]
theorem c2GroupHessian227_23_check : sumFast (c2TensorGroup227.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian227_23 := by kernel_rfl
private def c2GroupHessian227_33Chunk0 : Poly := [([0,0], 320),([0,4], 320),([0,6], 320),([0,8], 320),([0,9], 320),([4,4], 80),([4,6], 160),([4,8], 160),([4,9], 160),([6,6], 80),([6,8], 160),([6,9], 160),([8,8], 80),([8,9], 160),([9,9], 80)]
def c2GroupHessian227_33 : Poly := List.flatten [c2GroupHessian227_33Chunk0]
theorem c2GroupHessian227_33_check : sumFast (c2TensorGroup227.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian227_33 := by kernel_rfl
end D4.Secondary
