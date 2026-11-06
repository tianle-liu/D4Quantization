import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup134_det_check : c2TensorGroup134.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 170)) = true := by kernel_rfl
private def c2GroupHessian134_00Chunk0 : Poly := [([0,0], 48),([0,1], 48),([0,6], 80),([1,1], 16),([1,6], 40),([5,5], 40),([6,6], 40)]
def c2GroupHessian134_00 : Poly := List.flatten [c2GroupHessian134_00Chunk0]
theorem c2GroupHessian134_00_check : sumFast (c2TensorGroup134.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian134_00 := by kernel_rfl
private def c2GroupHessian134_01Chunk0 : Poly := [([0,0], 8),([0,1], 4),([0,5], -40),([0,7], 8),([1,7], 4),([2,5], -40),([5,8], -40)]
def c2GroupHessian134_01 : Poly := List.flatten [c2GroupHessian134_01Chunk0]
theorem c2GroupHessian134_01_check : sumFast (c2TensorGroup134.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian134_01 := by kernel_rfl
private def c2GroupHessian134_02Chunk0 : Poly := [([0,0], -8),([0,1], -4),([0,5], -40),([0,7], -8),([1,7], -4),([3,5], -40),([5,5], -40),([5,9], -40)]
def c2GroupHessian134_02 : Poly := List.flatten [c2GroupHessian134_02Chunk0]
theorem c2GroupHessian134_02_check : sumFast (c2TensorGroup134.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian134_02 := by kernel_rfl
private def c2GroupHessian134_03Chunk0 : Poly := [([0,0], -40),([0,1], -20),([0,4], -16),([0,5], 40),([0,6], -80),([1,4], -8),([1,6], -20),([4,6], -20),([5,8], 40),([5,9], 40),([6,6], -40)]
def c2GroupHessian134_03 : Poly := List.flatten [c2GroupHessian134_03Chunk0]
theorem c2GroupHessian134_03_check : sumFast (c2TensorGroup134.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian134_03 := by kernel_rfl
private def c2GroupHessian134_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 16),([0,8], 80),([2,2], 40),([2,8], 80),([7,7], 8),([8,8], 40)]
def c2GroupHessian134_11 : Poly := List.flatten [c2GroupHessian134_11Chunk0]
theorem c2GroupHessian134_11_check : sumFast (c2TensorGroup134.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian134_11 := by kernel_rfl
private def c2GroupHessian134_12Chunk0 : Poly := [([0,0], 32),([0,2], 40),([0,3], 40),([0,5], 40),([0,7], -16),([0,8], 40),([0,9], 40),([2,3], 40),([2,5], 40),([2,9], 40),([3,8], 40),([5,8], 40),([7,7], -8),([8,9], 40)]
def c2GroupHessian134_12 : Poly := List.flatten [c2GroupHessian134_12Chunk0]
theorem c2GroupHessian134_12_check : sumFast (c2TensorGroup134.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian134_12 := by kernel_rfl
private def c2GroupHessian134_13Chunk0 : Poly := [([0,0], -40),([0,2], -40),([0,4], 4),([0,8], -80),([0,9], -40),([2,8], -40),([2,9], -40),([4,7], 4),([8,8], -40),([8,9], -40)]
def c2GroupHessian134_13 : Poly := List.flatten [c2GroupHessian134_13Chunk0]
theorem c2GroupHessian134_13_check : sumFast (c2TensorGroup134.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian134_13 := by kernel_rfl
private def c2GroupHessian134_22Chunk0 : Poly := [([0,0], 48),([0,3], 80),([0,5], 80),([0,7], 16),([0,9], 80),([3,3], 40),([3,5], 80),([3,9], 80),([5,5], 40),([5,9], 80),([7,7], 8),([9,9], 40)]
def c2GroupHessian134_22 : Poly := List.flatten [c2GroupHessian134_22Chunk0]
theorem c2GroupHessian134_22_check : sumFast (c2TensorGroup134.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian134_22 := by kernel_rfl
private def c2GroupHessian134_23Chunk0 : Poly := [([0,0], -40),([0,3], -40),([0,4], -4),([0,5], -40),([0,8], -40),([0,9], -80),([3,8], -40),([3,9], -40),([4,7], -4),([5,8], -40),([5,9], -40),([8,9], -40),([9,9], -40)]
def c2GroupHessian134_23 : Poly := List.flatten [c2GroupHessian134_23Chunk0]
theorem c2GroupHessian134_23_check : sumFast (c2TensorGroup134.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian134_23 := by kernel_rfl
private def c2GroupHessian134_33Chunk0 : Poly := [([0,0], 80),([0,4], 40),([0,6], 80),([0,8], 80),([0,9], 80),([4,4], 16),([4,6], 40),([6,6], 40),([8,8], 40),([8,9], 80),([9,9], 40)]
def c2GroupHessian134_33 : Poly := List.flatten [c2GroupHessian134_33Chunk0]
theorem c2GroupHessian134_33_check : sumFast (c2TensorGroup134.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian134_33 := by kernel_rfl
end D4.Secondary
