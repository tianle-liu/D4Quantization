import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup147_det_check : c2TensorGroup147.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 185)) = true := by kernel_rfl
private def c2GroupHessian147_00Chunk0 : Poly := [([0,0], 16),([0,1], 24),([0,5], 40),([1,1], 16),([1,5], 40),([5,5], 40),([6,6], 40)]
def c2GroupHessian147_00 : Poly := List.flatten [c2GroupHessian147_00Chunk0]
theorem c2GroupHessian147_00_check : sumFast (c2TensorGroup147.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian147_00 := by kernel_rfl
private def c2GroupHessian147_01Chunk0 : Poly := [([0,0], -4),([0,1], -8),([0,5], -20),([0,6], -40),([0,8], -4),([1,8], -8),([2,6], -40),([5,8], -20),([6,7], -40)]
def c2GroupHessian147_01 : Poly := List.flatten [c2GroupHessian147_01Chunk0]
theorem c2GroupHessian147_01_check : sumFast (c2TensorGroup147.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian147_01 := by kernel_rfl
private def c2GroupHessian147_02Chunk0 : Poly := [([0,0], -12),([0,1], -8),([0,3], 4),([0,5], -40),([0,6], 40),([1,3], 4),([1,5], -20),([5,5], -40),([6,7], 40),([6,9], 40)]
def c2GroupHessian147_02 : Poly := List.flatten [c2GroupHessian147_02Chunk0]
theorem c2GroupHessian147_02_check : sumFast (c2TensorGroup147.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian147_02 := by kernel_rfl
private def c2GroupHessian147_03Chunk0 : Poly := [([0,0], 4),([0,1], 8),([0,5], 20),([0,6], -40),([0,8], 4),([1,8], 8),([4,6], -40),([5,8], 20),([6,6], -40),([6,9], -40)]
def c2GroupHessian147_03 : Poly := List.flatten [c2GroupHessian147_03Chunk0]
theorem c2GroupHessian147_03_check : sumFast (c2TensorGroup147.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian147_03 := by kernel_rfl
private def c2GroupHessian147_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 80),([0,8], 32),([2,2], 40),([2,7], 80),([7,7], 40),([8,8], 16)]
def c2GroupHessian147_11 : Poly := List.flatten [c2GroupHessian147_11Chunk0]
theorem c2GroupHessian147_11_check : sumFast (c2TensorGroup147.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian147_11 := by kernel_rfl
private def c2GroupHessian147_12Chunk0 : Poly := [([0,0], -32),([0,2], -40),([0,3], 4),([0,5], 20),([0,7], -80),([0,8], 8),([0,9], -40),([2,7], -40),([2,9], -40),([3,8], 4),([5,8], 20),([7,7], -40),([7,9], -40)]
def c2GroupHessian147_12 : Poly := List.flatten [c2GroupHessian147_12Chunk0]
theorem c2GroupHessian147_12_check : sumFast (c2TensorGroup147.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian147_12 := by kernel_rfl
private def c2GroupHessian147_13Chunk0 : Poly := [([0,0], 24),([0,2], 40),([0,4], 40),([0,6], 40),([0,7], 40),([0,8], -32),([0,9], 40),([2,4], 40),([2,6], 40),([2,9], 40),([4,7], 40),([6,7], 40),([7,9], 40),([8,8], -16)]
def c2GroupHessian147_13 : Poly := List.flatten [c2GroupHessian147_13Chunk0]
theorem c2GroupHessian147_13_check : sumFast (c2TensorGroup147.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian147_13 := by kernel_rfl
private def c2GroupHessian147_22Chunk0 : Poly := [([0,0], 56),([0,3], 8),([0,5], 40),([0,7], 80),([0,9], 80),([3,3], 8),([5,5], 40),([7,7], 40),([7,9], 80),([9,9], 40)]
def c2GroupHessian147_22 : Poly := List.flatten [c2GroupHessian147_22Chunk0]
theorem c2GroupHessian147_22_check : sumFast (c2TensorGroup147.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian147_22 := by kernel_rfl
private def c2GroupHessian147_23Chunk0 : Poly := [([0,0], -48),([0,3], -4),([0,4], -40),([0,5], -20),([0,6], -40),([0,7], -40),([0,8], -8),([0,9], -80),([3,8], -4),([4,7], -40),([4,9], -40),([5,8], -20),([6,7], -40),([6,9], -40),([7,9], -40),([9,9], -40)]
def c2GroupHessian147_23 : Poly := List.flatten [c2GroupHessian147_23Chunk0]
theorem c2GroupHessian147_23_check : sumFast (c2TensorGroup147.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian147_23 := by kernel_rfl
private def c2GroupHessian147_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 80),([0,8], 32),([0,9], 80),([4,4], 40),([4,6], 80),([4,9], 80),([6,6], 40),([6,9], 80),([8,8], 16),([9,9], 40)]
def c2GroupHessian147_33 : Poly := List.flatten [c2GroupHessian147_33Chunk0]
theorem c2GroupHessian147_33_check : sumFast (c2TensorGroup147.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian147_33 := by kernel_rfl
end D4.Secondary
