import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup64_det_check : c2TensorGroup64.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 85)) = true := by kernel_rfl
private def c2GroupHessian64_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 80),([0,6], 32),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 16)]
def c2GroupHessian64_00 : Poly := List.flatten [c2GroupHessian64_00Chunk0]
theorem c2GroupHessian64_00_check : sumFast (c2TensorGroup64.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian64_00 := by kernel_rfl
private def c2GroupHessian64_01Chunk0 : Poly := [([0,0], 20),([0,2], 4),([0,6], 20),([0,7], 4),([0,8], -40),([1,8], -40),([2,6], 4),([5,8], -40),([6,7], 4)]
def c2GroupHessian64_01 : Poly := List.flatten [c2GroupHessian64_01Chunk0]
theorem c2GroupHessian64_01_check : sumFast (c2TensorGroup64.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian64_01 := by kernel_rfl
private def c2GroupHessian64_02Chunk0 : Poly := [([0,0], -56),([0,1], -40),([0,3], -8),([0,5], -80),([0,6], -16),([0,7], -4),([0,9], -40),([1,5], -40),([1,9], -40),([3,6], -8),([5,5], -40),([5,9], -40),([6,7], -4)]
def c2GroupHessian64_02 : Poly := List.flatten [c2GroupHessian64_02Chunk0]
theorem c2GroupHessian64_02_check : sumFast (c2TensorGroup64.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian64_02 := by kernel_rfl
private def c2GroupHessian64_03Chunk0 : Poly := [([0,0], 24),([0,1], 40),([0,4], 40),([0,5], 40),([0,6], -32),([0,8], 40),([0,9], 40),([1,4], 40),([1,8], 40),([1,9], 40),([4,5], 40),([5,8], 40),([5,9], 40),([6,6], -16)]
def c2GroupHessian64_03 : Poly := List.flatten [c2GroupHessian64_03Chunk0]
theorem c2GroupHessian64_03_check : sumFast (c2TensorGroup64.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian64_03 := by kernel_rfl
private def c2GroupHessian64_11Chunk0 : Poly := [([0,0], 32),([0,2], 24),([0,7], 24),([2,2], 8),([2,7], 16),([7,7], 8),([8,8], 40)]
def c2GroupHessian64_11 : Poly := List.flatten [c2GroupHessian64_11Chunk0]
theorem c2GroupHessian64_11_check : sumFast (c2TensorGroup64.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian64_11 := by kernel_rfl
private def c2GroupHessian64_12Chunk0 : Poly := [([0,0], -20),([0,2], -4),([0,3], -4),([0,7], -16),([0,8], 40),([2,3], 4),([2,7], -8),([3,7], 4),([5,8], 40),([7,7], -8),([8,9], 40)]
def c2GroupHessian64_12 : Poly := List.flatten [c2GroupHessian64_12Chunk0]
theorem c2GroupHessian64_12_check : sumFast (c2TensorGroup64.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian64_12 := by kernel_rfl
private def c2GroupHessian64_13Chunk0 : Poly := [([0,0], -20),([0,2], -4),([0,6], -20),([0,7], -4),([0,8], -40),([2,6], -4),([4,8], -40),([6,7], -4),([8,8], -40),([8,9], -40)]
def c2GroupHessian64_13 : Poly := List.flatten [c2GroupHessian64_13Chunk0]
theorem c2GroupHessian64_13_check : sumFast (c2TensorGroup64.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian64_13 := by kernel_rfl
private def c2GroupHessian64_22Chunk0 : Poly := [([0,0], 56),([0,3], 16),([0,5], 80),([0,7], 8),([0,9], 80),([3,3], 16),([3,7], -8),([5,5], 40),([5,9], 80),([7,7], 8),([9,9], 40)]
def c2GroupHessian64_22 : Poly := List.flatten [c2GroupHessian64_22Chunk0]
theorem c2GroupHessian64_22_check : sumFast (c2TensorGroup64.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian64_22 := by kernel_rfl
private def c2GroupHessian64_23Chunk0 : Poly := [([0,0], -24),([0,3], 8),([0,4], -40),([0,5], -40),([0,6], 16),([0,7], 4),([0,8], -40),([0,9], -80),([3,6], 8),([4,5], -40),([4,9], -40),([5,8], -40),([5,9], -40),([6,7], 4),([8,9], -40),([9,9], -40)]
def c2GroupHessian64_23 : Poly := List.flatten [c2GroupHessian64_23Chunk0]
theorem c2GroupHessian64_23_check : sumFast (c2TensorGroup64.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian64_23 := by kernel_rfl
private def c2GroupHessian64_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 32),([0,8], 80),([0,9], 80),([4,4], 40),([4,8], 80),([4,9], 80),([6,6], 16),([8,8], 40),([8,9], 80),([9,9], 40)]
def c2GroupHessian64_33 : Poly := List.flatten [c2GroupHessian64_33Chunk0]
theorem c2GroupHessian64_33_check : sumFast (c2TensorGroup64.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian64_33 := by kernel_rfl
end D4.Secondary
