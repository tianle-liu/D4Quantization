import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup5_det_check : c2TensorGroup5.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 6)) = true := by kernel_rfl
private def c2GroupHessian5_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 32),([0,6], 40),([1,1], 40),([5,5], 16),([5,6], 40),([6,6], 40)]
def c2GroupHessian5_00 : Poly := List.flatten [c2GroupHessian5_00Chunk0]
theorem c2GroupHessian5_00_check : sumFast (c2TensorGroup5.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian5_00 := by kernel_rfl
private def c2GroupHessian5_01Chunk0 : Poly := [([0,0], 44),([0,1], 40),([0,2], 40),([0,5], 4),([0,7], -8),([0,8], 4),([1,2], 40),([5,7], -8),([5,8], 4),([6,7], -20)]
def c2GroupHessian5_01 : Poly := List.flatten [c2GroupHessian5_01Chunk0]
theorem c2GroupHessian5_01_check : sumFast (c2TensorGroup5.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian5_01 := by kernel_rfl
private def c2GroupHessian5_02Chunk0 : Poly := [([0,0], 4),([0,3], 40),([0,5], -12),([0,6], 20),([0,7], 8),([0,9], 20),([1,3], 40),([5,5], -16),([5,6], -20),([5,7], 8),([5,9], 20),([6,7], 20),([6,9], 40)]
def c2GroupHessian5_02 : Poly := List.flatten [c2GroupHessian5_02Chunk0]
theorem c2GroupHessian5_02_check : sumFast (c2TensorGroup5.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian5_02 := by kernel_rfl
private def c2GroupHessian5_03Chunk0 : Poly := [([0,0], -24),([0,4], 40),([0,5], -24),([0,6], -60),([0,8], -4),([0,9], -20),([1,4], 40),([5,6], -20),([5,8], -4),([5,9], -20),([6,6], -40),([6,9], -40)]
def c2GroupHessian5_03 : Poly := List.flatten [c2GroupHessian5_03Chunk0]
theorem c2GroupHessian5_03_check : sumFast (c2TensorGroup5.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian5_03 := by kernel_rfl
private def c2GroupHessian5_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 8),([0,8], 16),([2,2], 40),([7,7], 16),([7,8], 8),([8,8], 8)]
def c2GroupHessian5_11 : Poly := List.flatten [c2GroupHessian5_11Chunk0]
theorem c2GroupHessian5_11_check : sumFast (c2TensorGroup5.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian5_11 := by kernel_rfl
private def c2GroupHessian5_12Chunk0 : Poly := [([0,0], -4),([0,3], 40),([0,5], -4),([0,7], -16),([0,8], -4),([2,3], 40),([5,7], 8),([5,8], -4),([7,7], -16),([7,8], -4),([7,9], -20)]
def c2GroupHessian5_12 : Poly := List.flatten [c2GroupHessian5_12Chunk0]
theorem c2GroupHessian5_12_check : sumFast (c2TensorGroup5.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian5_12 := by kernel_rfl
private def c2GroupHessian5_13Chunk0 : Poly := [([0,0], -8),([0,4], 40),([0,7], 16),([0,8], -16),([2,4], 40),([6,7], 20),([7,8], -4),([7,9], 20),([8,8], -8)]
def c2GroupHessian5_13 : Poly := List.flatten [c2GroupHessian5_13Chunk0]
theorem c2GroupHessian5_13_check : sumFast (c2TensorGroup5.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian5_13 := by kernel_rfl
private def c2GroupHessian5_22Chunk0 : Poly := [([0,0], 16),([0,5], -8),([0,7], 24),([0,9], 40),([3,3], 40),([5,5], 16),([5,7], -16),([5,9], -40),([7,7], 16),([7,9], 40),([9,9], 40)]
def c2GroupHessian5_22 : Poly := List.flatten [c2GroupHessian5_22Chunk0]
theorem c2GroupHessian5_22_check : sumFast (c2TensorGroup5.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian5_22 := by kernel_rfl
private def c2GroupHessian5_23Chunk0 : Poly := [([0,0], -16),([0,5], 24),([0,6], -20),([0,7], -16),([0,8], 4),([0,9], -60),([3,4], 40),([5,6], 20),([5,8], 4),([5,9], 20),([6,7], -20),([6,9], -40),([7,8], 4),([7,9], -20),([9,9], -40)]
def c2GroupHessian5_23 : Poly := List.flatten [c2GroupHessian5_23Chunk0]
theorem c2GroupHessian5_23_check : sumFast (c2TensorGroup5.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian5_23 := by kernel_rfl
private def c2GroupHessian5_33Chunk0 : Poly := [([0,0], 48),([0,6], 80),([0,8], 16),([0,9], 80),([4,4], 40),([6,6], 40),([6,9], 80),([8,8], 8),([9,9], 40)]
def c2GroupHessian5_33 : Poly := List.flatten [c2GroupHessian5_33Chunk0]
theorem c2GroupHessian5_33_check : sumFast (c2TensorGroup5.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian5_33 := by kernel_rfl
end D4.Secondary
