import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup3_det_check : c2TensorGroup3.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 4)) = true := by kernel_rfl
private def c2GroupHessian3_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 16),([0,6], 8),([1,1], 40),([5,5], 8),([5,6], 8),([6,6], 16)]
def c2GroupHessian3_00 : Poly := List.flatten [c2GroupHessian3_00Chunk0]
theorem c2GroupHessian3_00_check : sumFast (c2TensorGroup3.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian3_00 := by kernel_rfl
private def c2GroupHessian3_01Chunk0 : Poly := [([0,0], 44),([0,1], 40),([0,2], 40),([0,5], 4),([0,6], -8),([0,7], 4),([0,8], 4),([1,2], 40),([5,7], 4),([5,8], 4),([6,7], -8),([6,8], -8)]
def c2GroupHessian3_01 : Poly := List.flatten [c2GroupHessian3_01Chunk0]
theorem c2GroupHessian3_01_check : sumFast (c2TensorGroup3.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian3_01 := by kernel_rfl
private def c2GroupHessian3_02Chunk0 : Poly := [([0,0], -8),([0,3], 40),([0,5], -16),([0,6], 16),([0,7], -4),([1,3], 40),([5,5], -8),([5,6], -4),([5,7], -4),([6,7], 8),([6,9], 20)]
def c2GroupHessian3_02 : Poly := List.flatten [c2GroupHessian3_02Chunk0]
theorem c2GroupHessian3_02_check : sumFast (c2TensorGroup3.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian3_02 := by kernel_rfl
private def c2GroupHessian3_03Chunk0 : Poly := [([0,0], -4),([0,4], 40),([0,5], -4),([0,6], -16),([0,8], -4),([1,4], 40),([5,6], -4),([5,8], -4),([6,6], -16),([6,8], 8),([6,9], -20)]
def c2GroupHessian3_03 : Poly := List.flatten [c2GroupHessian3_03Chunk0]
theorem c2GroupHessian3_03_check : sumFast (c2TensorGroup3.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian3_03 := by kernel_rfl
private def c2GroupHessian3_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 32),([0,8], 32),([2,2], 40),([7,7], 16),([7,8], 32),([8,8], 16)]
def c2GroupHessian3_11 : Poly := List.flatten [c2GroupHessian3_11Chunk0]
theorem c2GroupHessian3_11_check : sumFast (c2TensorGroup3.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian3_11 := by kernel_rfl
private def c2GroupHessian3_12Chunk0 : Poly := [([0,0], -24),([0,3], 40),([0,5], -4),([0,7], -40),([0,8], -24),([0,9], -20),([2,3], 40),([5,7], -4),([5,8], -4),([7,7], -16),([7,8], -16),([7,9], -20),([8,9], -20)]
def c2GroupHessian3_12 : Poly := List.flatten [c2GroupHessian3_12Chunk0]
theorem c2GroupHessian3_12_check : sumFast (c2TensorGroup3.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian3_12 := by kernel_rfl
private def c2GroupHessian3_13Chunk0 : Poly := [([0,0], 4),([0,4], 40),([0,6], 8),([0,7], 4),([0,8], -12),([0,9], 20),([2,4], 40),([6,7], 8),([6,8], 8),([7,8], -16),([7,9], 20),([8,8], -16),([8,9], 20)]
def c2GroupHessian3_13 : Poly := List.flatten [c2GroupHessian3_13Chunk0]
theorem c2GroupHessian3_13_check : sumFast (c2TensorGroup3.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian3_13 := by kernel_rfl
private def c2GroupHessian3_22Chunk0 : Poly := [([0,0], 48),([0,5], 16),([0,7], 48),([0,9], 80),([3,3], 40),([5,5], 8),([5,7], 8),([7,7], 16),([7,9], 40),([9,9], 40)]
def c2GroupHessian3_22 : Poly := List.flatten [c2GroupHessian3_22Chunk0]
theorem c2GroupHessian3_22_check : sumFast (c2TensorGroup3.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian3_22 := by kernel_rfl
private def c2GroupHessian3_23Chunk0 : Poly := [([0,0], -16),([0,5], 4),([0,6], -16),([0,7], -4),([0,8], 24),([0,9], -60),([3,4], 40),([5,6], 4),([5,8], 4),([6,7], -8),([6,9], -20),([7,8], 16),([7,9], -20),([8,9], 20),([9,9], -40)]
def c2GroupHessian3_23 : Poly := List.flatten [c2GroupHessian3_23Chunk0]
theorem c2GroupHessian3_23_check : sumFast (c2TensorGroup3.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian3_23 := by kernel_rfl
private def c2GroupHessian3_33Chunk0 : Poly := [([0,0], 16),([0,6], 24),([0,8], -8),([0,9], 40),([4,4], 40),([6,6], 16),([6,8], -16),([6,9], 40),([8,8], 16),([8,9], -40),([9,9], 40)]
def c2GroupHessian3_33 : Poly := List.flatten [c2GroupHessian3_33Chunk0]
theorem c2GroupHessian3_33_check : sumFast (c2TensorGroup3.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian3_33 := by kernel_rfl
end D4.Secondary
