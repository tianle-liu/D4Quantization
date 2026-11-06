import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup108_det_check : c2TensorGroup108.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 140)) = true := by kernel_rfl
private def c2GroupHessian108_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 80),([0,6], 80),([1,1], 40),([1,5], 80),([1,6], 80),([5,5], 40),([5,6], 80),([6,6], 40)]
def c2GroupHessian108_00 : Poly := List.flatten [c2GroupHessian108_00Chunk0]
theorem c2GroupHessian108_00_check : sumFast (c2TensorGroup108.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian108_00 := by kernel_rfl
private def c2GroupHessian108_01Chunk0 : Poly := [([0,0], -24),([0,1], -40),([0,2], -40),([0,5], -40),([0,6], -40),([0,7], -40),([0,8], -40),([1,2], -40),([1,7], -40),([1,8], -40),([2,5], -40),([2,6], -40),([5,7], -40),([5,8], -40),([6,7], -40),([6,8], -40)]
def c2GroupHessian108_01 : Poly := List.flatten [c2GroupHessian108_01Chunk0]
theorem c2GroupHessian108_01_check : sumFast (c2TensorGroup108.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian108_01 := by kernel_rfl
private def c2GroupHessian108_02Chunk0 : Poly := [([0,0], -12),([0,3], -8),([0,5], -40),([0,7], 40),([0,9], 4),([1,5], -40),([1,7], 40),([5,5], -40),([5,6], -40),([5,7], 40),([6,7], 40)]
def c2GroupHessian108_02 : Poly := List.flatten [c2GroupHessian108_02Chunk0]
theorem c2GroupHessian108_02_check : sumFast (c2TensorGroup108.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian108_02 := by kernel_rfl
private def c2GroupHessian108_03Chunk0 : Poly := [([0,0], -12),([0,4], -8),([0,6], -40),([0,8], 40),([0,9], -4),([1,6], -40),([1,8], 40),([5,6], -40),([5,8], 40),([6,6], -40),([6,8], 40)]
def c2GroupHessian108_03 : Poly := List.flatten [c2GroupHessian108_03Chunk0]
theorem c2GroupHessian108_03_check : sumFast (c2TensorGroup108.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian108_03 := by kernel_rfl
private def c2GroupHessian108_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 80),([0,8], 80),([2,2], 40),([2,7], 80),([2,8], 80),([7,7], 40),([7,8], 80),([8,8], 40)]
def c2GroupHessian108_11 : Poly := List.flatten [c2GroupHessian108_11Chunk0]
theorem c2GroupHessian108_11_check : sumFast (c2TensorGroup108.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian108_11 := by kernel_rfl
private def c2GroupHessian108_12Chunk0 : Poly := [([0,0], -12),([0,3], -8),([0,5], 40),([0,7], -40),([0,9], 4),([2,5], 40),([2,7], -40),([5,7], 40),([5,8], 40),([7,7], -40),([7,8], -40)]
def c2GroupHessian108_12 : Poly := List.flatten [c2GroupHessian108_12Chunk0]
theorem c2GroupHessian108_12_check : sumFast (c2TensorGroup108.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian108_12 := by kernel_rfl
private def c2GroupHessian108_13Chunk0 : Poly := [([0,0], -12),([0,4], -8),([0,6], 40),([0,8], -40),([0,9], -4),([2,6], 40),([2,8], -40),([6,7], 40),([6,8], 40),([7,8], -40),([8,8], -40)]
def c2GroupHessian108_13 : Poly := List.flatten [c2GroupHessian108_13Chunk0]
theorem c2GroupHessian108_13_check : sumFast (c2TensorGroup108.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian108_13 := by kernel_rfl
private def c2GroupHessian108_22Chunk0 : Poly := [([0,0], 16),([0,3], 24),([0,9], 8),([3,3], 16),([3,9], 8),([5,5], 40),([5,7], -80),([7,7], 40),([9,9], 8)]
def c2GroupHessian108_22 : Poly := List.flatten [c2GroupHessian108_22Chunk0]
theorem c2GroupHessian108_22_check : sumFast (c2TensorGroup108.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian108_22 := by kernel_rfl
private def c2GroupHessian108_23Chunk0 : Poly := [([0,0], 8),([0,3], 12),([0,4], 12),([0,9], -8),([3,4], 16),([3,9], -4),([4,9], 4),([5,6], 40),([5,8], -40),([6,7], -40),([7,8], 40),([9,9], -8)]
def c2GroupHessian108_23 : Poly := List.flatten [c2GroupHessian108_23Chunk0]
theorem c2GroupHessian108_23_check : sumFast (c2TensorGroup108.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian108_23 := by kernel_rfl
private def c2GroupHessian108_33Chunk0 : Poly := [([0,0], 16),([0,4], 24),([0,9], 8),([4,4], 16),([4,9], -8),([6,6], 40),([6,8], -80),([8,8], 40),([9,9], 8)]
def c2GroupHessian108_33 : Poly := List.flatten [c2GroupHessian108_33Chunk0]
theorem c2GroupHessian108_33_check : sumFast (c2TensorGroup108.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian108_33 := by kernel_rfl
end D4.Secondary
