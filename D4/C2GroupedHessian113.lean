import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup113_det_check : c2TensorGroup113.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 145)) = true := by kernel_rfl
private def c2GroupHessian113_00Chunk0 : Poly := [([0,0], 48),([0,1], 16),([0,5], 80),([0,6], 80),([1,1], 8),([5,5], 40),([5,6], 80),([6,6], 40)]
def c2GroupHessian113_00 : Poly := List.flatten [c2GroupHessian113_00Chunk0]
theorem c2GroupHessian113_00_check : sumFast (c2TensorGroup113.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian113_00 := by kernel_rfl
private def c2GroupHessian113_01Chunk0 : Poly := [([0,0], 8),([0,1], 8),([0,2], -40),([0,8], 4),([1,8], 4),([2,5], -40),([2,6], -40)]
def c2GroupHessian113_01 : Poly := List.flatten [c2GroupHessian113_01Chunk0]
theorem c2GroupHessian113_01_check : sumFast (c2TensorGroup113.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian113_01 := by kernel_rfl
private def c2GroupHessian113_02Chunk0 : Poly := [([0,0], -40),([0,3], -40),([0,5], -80),([0,6], -40),([0,9], 4),([1,9], 4),([3,5], -40),([3,6], -40),([5,5], -40),([5,6], -40)]
def c2GroupHessian113_02 : Poly := List.flatten [c2GroupHessian113_02Chunk0]
theorem c2GroupHessian113_02_check : sumFast (c2TensorGroup113.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian113_02 := by kernel_rfl
private def c2GroupHessian113_03Chunk0 : Poly := [([0,0], -48),([0,1], -8),([0,4], -40),([0,5], -40),([0,6], -80),([0,8], -4),([0,9], -4),([1,8], -4),([1,9], -4),([4,5], -40),([4,6], -40),([5,6], -40),([6,6], -40)]
def c2GroupHessian113_03 : Poly := List.flatten [c2GroupHessian113_03Chunk0]
theorem c2GroupHessian113_03_check : sumFast (c2TensorGroup113.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian113_03 := by kernel_rfl
private def c2GroupHessian113_11Chunk0 : Poly := [([0,0], 48),([0,7], 80),([0,8], 48),([2,2], 40),([7,7], 40),([7,8], 40),([8,8], 16)]
def c2GroupHessian113_11 : Poly := List.flatten [c2GroupHessian113_11Chunk0]
theorem c2GroupHessian113_11_check : sumFast (c2TensorGroup113.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian113_11 := by kernel_rfl
private def c2GroupHessian113_12Chunk0 : Poly := [([0,0], -40),([0,2], 40),([0,7], -80),([0,8], -20),([0,9], -16),([2,3], 40),([2,5], 40),([7,7], -40),([7,8], -20),([7,9], -20),([8,9], -8)]
def c2GroupHessian113_12 : Poly := List.flatten [c2GroupHessian113_12Chunk0]
theorem c2GroupHessian113_12_check : sumFast (c2TensorGroup113.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian113_12 := by kernel_rfl
private def c2GroupHessian113_13Chunk0 : Poly := [([0,0], -8),([0,2], 40),([0,8], -28),([0,9], 16),([2,4], 40),([2,6], 40),([7,8], -20),([7,9], 20),([8,8], -16),([8,9], 8)]
def c2GroupHessian113_13 : Poly := List.flatten [c2GroupHessian113_13Chunk0]
theorem c2GroupHessian113_13_check : sumFast (c2TensorGroup113.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian113_13 := by kernel_rfl
private def c2GroupHessian113_22Chunk0 : Poly := [([0,0], 80),([0,3], 80),([0,5], 80),([0,7], 80),([0,9], 40),([3,3], 40),([3,5], 80),([5,5], 40),([7,7], 40),([7,9], 40),([9,9], 16)]
def c2GroupHessian113_22 : Poly := List.flatten [c2GroupHessian113_22Chunk0]
theorem c2GroupHessian113_22_check : sumFast (c2TensorGroup113.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian113_22 := by kernel_rfl
private def c2GroupHessian113_23Chunk0 : Poly := [([0,0], 40),([0,3], 40),([0,4], 40),([0,5], 40),([0,6], 40),([0,8], 20),([0,9], -24),([3,4], 40),([3,6], 40),([4,5], 40),([5,6], 40),([7,8], 20),([7,9], -20),([8,9], 8),([9,9], -16)]
def c2GroupHessian113_23 : Poly := List.flatten [c2GroupHessian113_23Chunk0]
theorem c2GroupHessian113_23_check : sumFast (c2TensorGroup113.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian113_23 := by kernel_rfl
private def c2GroupHessian113_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 80),([0,8], 8),([0,9], 8),([4,4], 40),([4,6], 80),([6,6], 40),([8,8], 16),([8,9], -16),([9,9], 16)]
def c2GroupHessian113_33 : Poly := List.flatten [c2GroupHessian113_33Chunk0]
theorem c2GroupHessian113_33_check : sumFast (c2TensorGroup113.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian113_33 := by kernel_rfl
end D4.Secondary
