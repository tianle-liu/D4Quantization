import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup132_det_check : c2TensorGroup132.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 167)) = true := by kernel_rfl
private def c2GroupHessian132_00Chunk0 : Poly := [([0,0], 32),([0,1], 24),([0,6], 24),([1,1], 8),([1,6], 16),([5,5], 40),([6,6], 8)]
def c2GroupHessian132_00 : Poly := List.flatten [c2GroupHessian132_00Chunk0]
theorem c2GroupHessian132_00_check : sumFast (c2TensorGroup132.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian132_00 := by kernel_rfl
private def c2GroupHessian132_01Chunk0 : Poly := [([0,0], 20),([0,1], 4),([0,5], -40),([0,6], 4),([0,7], 20),([1,7], 4),([2,5], -40),([5,8], -40),([6,7], 4)]
def c2GroupHessian132_01 : Poly := List.flatten [c2GroupHessian132_01Chunk0]
theorem c2GroupHessian132_01_check : sumFast (c2TensorGroup132.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian132_01 := by kernel_rfl
private def c2GroupHessian132_02Chunk0 : Poly := [([0,0], -20),([0,1], -4),([0,5], -40),([0,6], -4),([0,7], -20),([1,7], -4),([3,5], -40),([5,5], -40),([5,9], -40),([6,7], -4)]
def c2GroupHessian132_02 : Poly := List.flatten [c2GroupHessian132_02Chunk0]
theorem c2GroupHessian132_02_check : sumFast (c2TensorGroup132.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian132_02 := by kernel_rfl
private def c2GroupHessian132_03Chunk0 : Poly := [([0,0], -20),([0,1], -4),([0,4], -4),([0,5], 40),([0,6], -16),([1,4], 4),([1,6], -8),([4,6], 4),([5,8], 40),([5,9], 40),([6,6], -8)]
def c2GroupHessian132_03 : Poly := List.flatten [c2GroupHessian132_03Chunk0]
theorem c2GroupHessian132_03_check : sumFast (c2TensorGroup132.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian132_03 := by kernel_rfl
private def c2GroupHessian132_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 32),([0,8], 80),([2,2], 40),([2,8], 80),([7,7], 16),([8,8], 40)]
def c2GroupHessian132_11 : Poly := List.flatten [c2GroupHessian132_11Chunk0]
theorem c2GroupHessian132_11_check : sumFast (c2TensorGroup132.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian132_11 := by kernel_rfl
private def c2GroupHessian132_12Chunk0 : Poly := [([0,0], 24),([0,2], 40),([0,3], 40),([0,5], 40),([0,7], -32),([0,8], 40),([0,9], 40),([2,3], 40),([2,5], 40),([2,9], 40),([3,8], 40),([5,8], 40),([7,7], -16),([8,9], 40)]
def c2GroupHessian132_12 : Poly := List.flatten [c2GroupHessian132_12Chunk0]
theorem c2GroupHessian132_12_check : sumFast (c2TensorGroup132.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian132_12 := by kernel_rfl
private def c2GroupHessian132_13Chunk0 : Poly := [([0,0], -56),([0,2], -40),([0,4], -8),([0,6], -4),([0,7], -16),([0,8], -80),([0,9], -40),([2,8], -40),([2,9], -40),([4,7], -8),([6,7], -4),([8,8], -40),([8,9], -40)]
def c2GroupHessian132_13 : Poly := List.flatten [c2GroupHessian132_13Chunk0]
theorem c2GroupHessian132_13_check : sumFast (c2TensorGroup132.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian132_13 := by kernel_rfl
private def c2GroupHessian132_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 80),([0,7], 32),([0,9], 80),([3,3], 40),([3,5], 80),([3,9], 80),([5,5], 40),([5,9], 80),([7,7], 16),([9,9], 40)]
def c2GroupHessian132_22 : Poly := List.flatten [c2GroupHessian132_22Chunk0]
theorem c2GroupHessian132_22_check : sumFast (c2TensorGroup132.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian132_22 := by kernel_rfl
private def c2GroupHessian132_23Chunk0 : Poly := [([0,0], -24),([0,3], -40),([0,4], 8),([0,5], -40),([0,6], 4),([0,7], 16),([0,8], -40),([0,9], -80),([3,8], -40),([3,9], -40),([4,7], 8),([5,8], -40),([5,9], -40),([6,7], 4),([8,9], -40),([9,9], -40)]
def c2GroupHessian132_23 : Poly := List.flatten [c2GroupHessian132_23Chunk0]
theorem c2GroupHessian132_23_check : sumFast (c2TensorGroup132.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian132_23 := by kernel_rfl
private def c2GroupHessian132_33Chunk0 : Poly := [([0,0], 56),([0,4], 16),([0,6], 8),([0,8], 80),([0,9], 80),([4,4], 16),([4,6], -8),([6,6], 8),([8,8], 40),([8,9], 80),([9,9], 40)]
def c2GroupHessian132_33 : Poly := List.flatten [c2GroupHessian132_33Chunk0]
theorem c2GroupHessian132_33_check : sumFast (c2TensorGroup132.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian132_33 := by kernel_rfl
end D4.Secondary
