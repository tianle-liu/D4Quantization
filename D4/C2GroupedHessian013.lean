import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup13_det_check : c2TensorGroup13.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 15)) = true := by kernel_rfl
private def c2GroupHessian13_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 32),([0,6], 32),([1,1], 40),([5,5], 16),([5,6], 32),([6,6], 16)]
def c2GroupHessian13_00 : Poly := List.flatten [c2GroupHessian13_00Chunk0]
theorem c2GroupHessian13_00_check : sumFast (c2TensorGroup13.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian13_00 := by kernel_rfl
private def c2GroupHessian13_01Chunk0 : Poly := [([0,0], 44),([0,1], 40),([0,2], 40),([0,5], 4),([0,6], 4),([0,7], -8),([0,8], 4),([1,2], 40),([5,7], -8),([5,8], 4),([6,7], -8),([6,8], 4)]
def c2GroupHessian13_01 : Poly := List.flatten [c2GroupHessian13_01Chunk0]
theorem c2GroupHessian13_01_check : sumFast (c2TensorGroup13.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian13_01 := by kernel_rfl
private def c2GroupHessian13_02Chunk0 : Poly := [([0,3], 40),([0,5], -16),([0,7], 8),([0,9], 4),([1,3], 40),([5,5], -16),([5,6], -16),([5,7], 8),([5,9], 4),([6,7], 8),([6,9], 4)]
def c2GroupHessian13_02 : Poly := List.flatten [c2GroupHessian13_02Chunk0]
theorem c2GroupHessian13_02_check : sumFast (c2TensorGroup13.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian13_02 := by kernel_rfl
private def c2GroupHessian13_03Chunk0 : Poly := [([0,0], -20),([0,4], 40),([0,5], -20),([0,6], -36),([0,8], -4),([0,9], -4),([1,4], 40),([5,6], -16),([5,8], -4),([5,9], -4),([6,6], -16),([6,8], -4),([6,9], -4)]
def c2GroupHessian13_03 : Poly := List.flatten [c2GroupHessian13_03Chunk0]
theorem c2GroupHessian13_03_check : sumFast (c2TensorGroup13.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian13_03 := by kernel_rfl
private def c2GroupHessian13_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 8),([0,8], 16),([2,2], 40),([7,7], 16),([7,8], 8),([8,8], 8)]
def c2GroupHessian13_11 : Poly := List.flatten [c2GroupHessian13_11Chunk0]
theorem c2GroupHessian13_11_check : sumFast (c2TensorGroup13.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian13_11 := by kernel_rfl
private def c2GroupHessian13_12Chunk0 : Poly := [([0,3], 40),([0,5], -4),([0,7], -4),([0,9], 8),([2,3], 40),([5,7], 8),([5,8], -4),([7,7], -16),([7,8], -4),([7,9], 4),([8,9], 8)]
def c2GroupHessian13_12 : Poly := List.flatten [c2GroupHessian13_12Chunk0]
theorem c2GroupHessian13_12_check : sumFast (c2TensorGroup13.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian13_12 := by kernel_rfl
private def c2GroupHessian13_13Chunk0 : Poly := [([0,0], -12),([0,4], 40),([0,6], -4),([0,7], 4),([0,8], -20),([0,9], -8),([2,4], 40),([6,7], 8),([6,8], -4),([7,8], -4),([7,9], -4),([8,8], -8),([8,9], -8)]
def c2GroupHessian13_13 : Poly := List.flatten [c2GroupHessian13_13Chunk0]
theorem c2GroupHessian13_13_check : sumFast (c2TensorGroup13.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian13_13 := by kernel_rfl
private def c2GroupHessian13_22Chunk0 : Poly := [([3,3], 40),([5,5], 16),([5,7], -16),([5,9], -8),([7,7], 16),([7,9], -8),([9,9], 8)]
def c2GroupHessian13_22 : Poly := List.flatten [c2GroupHessian13_22Chunk0]
theorem c2GroupHessian13_22_check : sumFast (c2TensorGroup13.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian13_22 := by kernel_rfl
private def c2GroupHessian13_23Chunk0 : Poly := [([0,5], 20),([0,7], -4),([0,9], -12),([3,4], 40),([5,6], 16),([5,8], 4),([5,9], 4),([6,7], -8),([6,9], -4),([7,8], 4),([7,9], 4),([8,9], -8),([9,9], -8)]
def c2GroupHessian13_23 : Poly := List.flatten [c2GroupHessian13_23Chunk0]
theorem c2GroupHessian13_23_check : sumFast (c2TensorGroup13.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian13_23 := by kernel_rfl
private def c2GroupHessian13_33Chunk0 : Poly := [([0,0], 32),([0,6], 40),([0,8], 24),([0,9], 24),([4,4], 40),([6,6], 16),([6,8], 8),([6,9], 8),([8,8], 8),([8,9], 16),([9,9], 8)]
def c2GroupHessian13_33 : Poly := List.flatten [c2GroupHessian13_33Chunk0]
theorem c2GroupHessian13_33_check : sumFast (c2TensorGroup13.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian13_33 := by kernel_rfl
end D4.Secondary
