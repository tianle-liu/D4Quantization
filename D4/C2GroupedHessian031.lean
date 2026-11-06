import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup31_det_check : c2TensorGroup31.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 48)) = true := by kernel_rfl
private def c2GroupHessian31_00Chunk0 : Poly := [([0,0], 32),([0,5], 40),([0,6], 24),([1,1], 40),([5,5], 16),([5,6], 8),([6,6], 8)]
def c2GroupHessian31_00 : Poly := List.flatten [c2GroupHessian31_00Chunk0]
theorem c2GroupHessian31_00_check : sumFast (c2TensorGroup31.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian31_00 := by kernel_rfl
private def c2GroupHessian31_01Chunk0 : Poly := [([0,0], 12),([0,1], -40),([0,2], -4),([0,5], 4),([0,6], 8),([1,7], -40),([1,8], -40),([2,5], -8),([2,6], 4)]
def c2GroupHessian31_01 : Poly := List.flatten [c2GroupHessian31_01Chunk0]
theorem c2GroupHessian31_01_check : sumFast (c2TensorGroup31.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian31_01 := by kernel_rfl
private def c2GroupHessian31_02Chunk0 : Poly := [([0,0], -20),([0,1], 40),([0,5], -36),([0,6], -4),([0,9], -20),([1,3], 40),([1,7], 40),([5,5], -16),([5,6], -4),([5,9], -20)]
def c2GroupHessian31_02 : Poly := List.flatten [c2GroupHessian31_02Chunk0]
theorem c2GroupHessian31_02_check : sumFast (c2TensorGroup31.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian31_02 := by kernel_rfl
private def c2GroupHessian31_03Chunk0 : Poly := [([0,0], -12),([0,1], 40),([0,5], -4),([0,6], -20),([0,9], 20),([1,4], 40),([1,8], 40),([5,6], -4),([5,9], 20),([6,6], -8)]
def c2GroupHessian31_03 : Poly := List.flatten [c2GroupHessian31_03Chunk0]
theorem c2GroupHessian31_03_check : sumFast (c2TensorGroup31.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian31_03 := by kernel_rfl
private def c2GroupHessian31_11Chunk0 : Poly := [([0,0], 48),([0,2], 8),([0,7], 80),([0,8], 80),([2,2], 16),([7,7], 40),([7,8], 80),([8,8], 40)]
def c2GroupHessian31_11 : Poly := List.flatten [c2GroupHessian31_11Chunk0]
theorem c2GroupHessian31_11_check : sumFast (c2TensorGroup31.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian31_11 := by kernel_rfl
private def c2GroupHessian31_12Chunk0 : Poly := [([0,0], -44),([0,2], 8),([0,3], -40),([0,5], -4),([0,7], -80),([0,8], -40),([2,5], 8),([2,9], 20),([3,7], -40),([3,8], -40),([7,7], -40),([7,8], -40)]
def c2GroupHessian31_12 : Poly := List.flatten [c2GroupHessian31_12Chunk0]
theorem c2GroupHessian31_12_check : sumFast (c2TensorGroup31.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian31_12 := by kernel_rfl
private def c2GroupHessian31_13Chunk0 : Poly := [([0,0], -48),([0,2], -4),([0,4], -40),([0,6], -8),([0,7], -40),([0,8], -80),([2,6], -4),([2,9], -20),([4,7], -40),([4,8], -40),([7,8], -40),([8,8], -40)]
def c2GroupHessian31_13 : Poly := List.flatten [c2GroupHessian31_13Chunk0]
theorem c2GroupHessian31_13_check : sumFast (c2TensorGroup31.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian31_13 := by kernel_rfl
private def c2GroupHessian31_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 32),([0,7], 80),([0,9], 40),([3,3], 40),([3,7], 80),([5,5], 16),([5,9], 40),([7,7], 40),([9,9], 40)]
def c2GroupHessian31_22 : Poly := List.flatten [c2GroupHessian31_22Chunk0]
theorem c2GroupHessian31_22_check : sumFast (c2TensorGroup31.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian31_22 := by kernel_rfl
private def c2GroupHessian31_23Chunk0 : Poly := [([0,0], 44),([0,3], 40),([0,4], 40),([0,5], 4),([0,6], 4),([0,7], 40),([0,8], 40),([0,9], -20),([3,4], 40),([3,8], 40),([4,7], 40),([5,6], 4),([5,9], -20),([7,8], 40),([9,9], -40)]
def c2GroupHessian31_23 : Poly := List.flatten [c2GroupHessian31_23Chunk0]
theorem c2GroupHessian31_23_check : sumFast (c2TensorGroup31.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian31_23 := by kernel_rfl
private def c2GroupHessian31_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 16),([0,8], 80),([4,4], 40),([4,8], 80),([6,6], 8),([8,8], 40),([9,9], 40)]
def c2GroupHessian31_33 : Poly := List.flatten [c2GroupHessian31_33Chunk0]
theorem c2GroupHessian31_33_check : sumFast (c2TensorGroup31.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian31_33 := by kernel_rfl
end D4.Secondary
