import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup98_det_check : c2TensorGroup98.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 128)) = true := by kernel_rfl
private def c2GroupHessian98_00Chunk0 : Poly := [([0,0], 160),([0,1], 160),([0,5], 160),([0,6], 160),([1,1], 40),([1,5], 80),([1,6], 80),([5,5], 40),([5,6], 80),([6,6], 40)]
def c2GroupHessian98_00 : Poly := List.flatten [c2GroupHessian98_00Chunk0]
theorem c2GroupHessian98_00_check : sumFast (c2TensorGroup98.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian98_00 := by kernel_rfl
private def c2GroupHessian98_01Chunk0 : Poly := [([0,0], 80),([0,1], 40),([0,5], 40),([0,6], 40)]
def c2GroupHessian98_01 : Poly := List.flatten [c2GroupHessian98_01Chunk0]
theorem c2GroupHessian98_01_check : sumFast (c2TensorGroup98.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian98_01 := by kernel_rfl
private def c2GroupHessian98_02Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -120),([0,6], -40),([1,5], -40),([5,5], -40),([5,6], -40)]
def c2GroupHessian98_02 : Poly := List.flatten [c2GroupHessian98_02Chunk0]
theorem c2GroupHessian98_02_check : sumFast (c2TensorGroup98.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian98_02 := by kernel_rfl
private def c2GroupHessian98_03Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -40),([0,6], -120),([1,6], -40),([5,6], -40),([6,6], -40)]
def c2GroupHessian98_03 : Poly := List.flatten [c2GroupHessian98_03Chunk0]
theorem c2GroupHessian98_03_check : sumFast (c2TensorGroup98.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian98_03 := by kernel_rfl
private def c2GroupHessian98_11Chunk0 : Poly := [([0,0], 48),([0,2], 8),([0,7], 8),([0,8], 16),([2,2], 16),([2,7], -16),([2,8], 8),([7,7], 16),([7,8], 8),([8,8], 8)]
def c2GroupHessian98_11 : Poly := List.flatten [c2GroupHessian98_11Chunk0]
theorem c2GroupHessian98_11_check : sumFast (c2TensorGroup98.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian98_11 := by kernel_rfl
private def c2GroupHessian98_12Chunk0 : Poly := [([0,0], -36),([0,2], 16),([0,3], 4),([0,5], -40),([0,7], -12),([0,8], 4),([0,9], 8),([2,3], 16),([2,7], 8),([2,9], 4),([3,7], -8),([3,8], 4),([7,7], -16),([7,8], -4),([7,9], 4),([8,9], 8)]
def c2GroupHessian98_12 : Poly := List.flatten [c2GroupHessian98_12Chunk0]
theorem c2GroupHessian98_12_check : sumFast (c2TensorGroup98.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian98_12 := by kernel_rfl
private def c2GroupHessian98_13Chunk0 : Poly := [([0,0], -48),([0,2], -4),([0,4], 4),([0,6], -40),([0,7], -4),([0,8], -16),([0,9], -8),([2,4], 16),([2,8], -4),([2,9], -4),([4,7], -8),([4,8], 4),([7,8], -4),([7,9], -4),([8,8], -8),([8,9], -8)]
def c2GroupHessian98_13 : Poly := List.flatten [c2GroupHessian98_13Chunk0]
theorem c2GroupHessian98_13_check : sumFast (c2TensorGroup98.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian98_13 := by kernel_rfl
private def c2GroupHessian98_22Chunk0 : Poly := [([0,0], 56),([0,3], 32),([0,5], 80),([0,7], 16),([0,9], 8),([3,3], 16),([3,7], 16),([3,9], 8),([5,5], 40),([7,7], 16),([7,9], -8),([9,9], 8)]
def c2GroupHessian98_22 : Poly := List.flatten [c2GroupHessian98_22Chunk0]
theorem c2GroupHessian98_22_check : sumFast (c2TensorGroup98.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian98_22 := by kernel_rfl
private def c2GroupHessian98_23Chunk0 : Poly := [([0,0], 36),([0,3], -4),([0,4], 16),([0,5], 40),([0,6], 40),([0,7], 4),([0,8], -4),([0,9], -12),([3,4], 16),([3,8], -4),([3,9], -4),([4,7], 8),([4,9], 4),([5,6], 40),([7,8], 4),([7,9], 4),([8,9], -8),([9,9], -8)]
def c2GroupHessian98_23 : Poly := List.flatten [c2GroupHessian98_23Chunk0]
theorem c2GroupHessian98_23_check : sumFast (c2TensorGroup98.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian98_23 := by kernel_rfl
private def c2GroupHessian98_33Chunk0 : Poly := [([0,0], 48),([0,4], -8),([0,6], 80),([0,8], 16),([0,9], 16),([4,4], 16),([4,8], -8),([4,9], -8),([6,6], 40),([8,8], 8),([8,9], 16),([9,9], 8)]
def c2GroupHessian98_33 : Poly := List.flatten [c2GroupHessian98_33Chunk0]
theorem c2GroupHessian98_33_check : sumFast (c2TensorGroup98.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian98_33 := by kernel_rfl
end D4.Secondary
