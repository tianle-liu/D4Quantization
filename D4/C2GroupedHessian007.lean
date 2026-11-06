import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup7_det_check : c2TensorGroup7.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 8)) = true := by kernel_rfl
private def c2GroupHessian7_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 16),([1,1], 40),([5,5], 8),([6,6], 40)]
def c2GroupHessian7_00 : Poly := List.flatten [c2GroupHessian7_00Chunk0]
theorem c2GroupHessian7_00_check : sumFast (c2TensorGroup7.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian7_00 := by kernel_rfl
private def c2GroupHessian7_01Chunk0 : Poly := [([0,0], 48),([0,1], 40),([0,2], 40),([0,5], 8),([0,7], 4),([0,8], 4),([1,2], 40),([5,7], 4),([5,8], 4),([6,7], -20),([6,8], 20)]
def c2GroupHessian7_01 : Poly := List.flatten [c2GroupHessian7_01Chunk0]
theorem c2GroupHessian7_01_check : sumFast (c2TensorGroup7.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian7_01 := by kernel_rfl
private def c2GroupHessian7_02Chunk0 : Poly := [([0,0], -8),([0,3], 40),([0,5], -16),([0,6], 40),([0,7], -4),([1,3], 40),([5,5], -8),([5,7], -4),([6,7], 20),([6,9], 40)]
def c2GroupHessian7_02 : Poly := List.flatten [c2GroupHessian7_02Chunk0]
theorem c2GroupHessian7_02_check : sumFast (c2TensorGroup7.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian7_02 := by kernel_rfl
private def c2GroupHessian7_03Chunk0 : Poly := [([0,0], -8),([0,4], 40),([0,5], -8),([0,6], -40),([0,8], -4),([1,4], 40),([5,8], -4),([6,6], -40),([6,8], -20),([6,9], -40)]
def c2GroupHessian7_03 : Poly := List.flatten [c2GroupHessian7_03Chunk0]
theorem c2GroupHessian7_03_check : sumFast (c2TensorGroup7.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian7_03 := by kernel_rfl
private def c2GroupHessian7_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 8),([0,8], 8),([2,2], 40),([7,7], 16),([7,8], -16),([8,8], 16)]
def c2GroupHessian7_11 : Poly := List.flatten [c2GroupHessian7_11Chunk0]
theorem c2GroupHessian7_11_check : sumFast (c2TensorGroup7.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian7_11 := by kernel_rfl
private def c2GroupHessian7_12Chunk0 : Poly := [([0,0], -8),([0,3], 40),([0,5], -8),([0,7], -28),([0,8], 16),([2,3], 40),([5,7], -4),([5,8], -4),([7,7], -16),([7,8], 8),([7,9], -20),([8,9], 20)]
def c2GroupHessian7_12 : Poly := List.flatten [c2GroupHessian7_12Chunk0]
theorem c2GroupHessian7_12_check : sumFast (c2TensorGroup7.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian7_12 := by kernel_rfl
private def c2GroupHessian7_13Chunk0 : Poly := [([0,0], -8),([0,4], 40),([0,7], 16),([0,8], -28),([2,4], 40),([6,7], 20),([6,8], -20),([7,8], 8),([7,9], 20),([8,8], -16),([8,9], -20)]
def c2GroupHessian7_13 : Poly := List.flatten [c2GroupHessian7_13Chunk0]
theorem c2GroupHessian7_13_check : sumFast (c2TensorGroup7.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian7_13 := by kernel_rfl
private def c2GroupHessian7_22Chunk0 : Poly := [([0,0], 48),([0,5], 16),([0,7], 48),([0,9], 80),([3,3], 40),([5,5], 8),([5,7], 8),([7,7], 16),([7,9], 40),([9,9], 40)]
def c2GroupHessian7_22 : Poly := List.flatten [c2GroupHessian7_22Chunk0]
theorem c2GroupHessian7_22_check : sumFast (c2TensorGroup7.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian7_22 := by kernel_rfl
private def c2GroupHessian7_23Chunk0 : Poly := [([0,0], -32),([0,5], 8),([0,6], -40),([0,7], -16),([0,8], -16),([0,9], -80),([3,4], 40),([5,8], 4),([6,7], -20),([6,9], -40),([7,8], -8),([7,9], -20),([8,9], -20),([9,9], -40)]
def c2GroupHessian7_23 : Poly := List.flatten [c2GroupHessian7_23Chunk0]
theorem c2GroupHessian7_23_check : sumFast (c2TensorGroup7.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian7_23 := by kernel_rfl
private def c2GroupHessian7_33Chunk0 : Poly := [([0,0], 48),([0,6], 80),([0,8], 48),([0,9], 80),([4,4], 40),([6,6], 40),([6,8], 40),([6,9], 80),([8,8], 16),([8,9], 40),([9,9], 40)]
def c2GroupHessian7_33 : Poly := List.flatten [c2GroupHessian7_33Chunk0]
theorem c2GroupHessian7_33_check : sumFast (c2TensorGroup7.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian7_33 := by kernel_rfl
end D4.Secondary
