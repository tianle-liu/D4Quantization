import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup28_det_check : c2TensorGroup28.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 44)) = true := by kernel_rfl
private def c2GroupHessian28_00Chunk0 : Poly := [([0,0], 16),([0,5], 16),([0,6], 16),([1,1], 40),([5,5], 16),([5,6], 32),([6,6], 16)]
def c2GroupHessian28_00 : Poly := List.flatten [c2GroupHessian28_00Chunk0]
theorem c2GroupHessian28_00_check : sumFast (c2TensorGroup28.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian28_00 := by kernel_rfl
private def c2GroupHessian28_01Chunk0 : Poly := [([0,0], 8),([0,1], -40),([0,5], -8),([0,6], -8),([1,7], -40),([1,8], -40),([2,5], -20),([2,6], -20)]
def c2GroupHessian28_01 : Poly := List.flatten [c2GroupHessian28_01Chunk0]
theorem c2GroupHessian28_01_check : sumFast (c2TensorGroup28.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian28_01 := by kernel_rfl
private def c2GroupHessian28_02Chunk0 : Poly := [([0,0], -8),([0,1], 40),([0,5], -12),([0,6], -4),([0,9], 8),([1,3], 40),([1,7], 40),([5,5], -16),([5,6], -16),([5,9], 4),([6,9], 4)]
def c2GroupHessian28_02 : Poly := List.flatten [c2GroupHessian28_02Chunk0]
theorem c2GroupHessian28_02_check : sumFast (c2TensorGroup28.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian28_02 := by kernel_rfl
private def c2GroupHessian28_03Chunk0 : Poly := [([0,0], -8),([0,1], 40),([0,5], -4),([0,6], -12),([0,9], -8),([1,4], 40),([1,8], 40),([5,6], -16),([5,9], -4),([6,6], -16),([6,9], -4)]
def c2GroupHessian28_03 : Poly := List.flatten [c2GroupHessian28_03Chunk0]
theorem c2GroupHessian28_03_check : sumFast (c2TensorGroup28.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian28_03 := by kernel_rfl
private def c2GroupHessian28_11Chunk0 : Poly := [([0,0], 56),([0,2], 40),([0,7], 80),([0,8], 80),([2,2], 40),([7,7], 40),([7,8], 80),([8,8], 40)]
def c2GroupHessian28_11 : Poly := List.flatten [c2GroupHessian28_11Chunk0]
theorem c2GroupHessian28_11_check : sumFast (c2TensorGroup28.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian28_11 := by kernel_rfl
private def c2GroupHessian28_12Chunk0 : Poly := [([0,0], -44),([0,3], -40),([0,5], 8),([0,7], -80),([0,8], -40),([0,9], 4),([2,5], 20),([3,7], -40),([3,8], -40),([7,7], -40),([7,8], -40)]
def c2GroupHessian28_12 : Poly := List.flatten [c2GroupHessian28_12Chunk0]
theorem c2GroupHessian28_12_check : sumFast (c2TensorGroup28.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian28_12 := by kernel_rfl
private def c2GroupHessian28_13Chunk0 : Poly := [([0,0], -44),([0,4], -40),([0,6], 8),([0,7], -40),([0,8], -80),([0,9], -4),([2,6], 20),([4,7], -40),([4,8], -40),([7,8], -40),([8,8], -40)]
def c2GroupHessian28_13 : Poly := List.flatten [c2GroupHessian28_13Chunk0]
theorem c2GroupHessian28_13_check : sumFast (c2TensorGroup28.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian28_13 := by kernel_rfl
private def c2GroupHessian28_22Chunk0 : Poly := [([0,0], 48),([0,3], 80),([0,5], 8),([0,7], 80),([3,3], 40),([3,7], 80),([5,5], 16),([5,9], -8),([7,7], 40),([9,9], 8)]
def c2GroupHessian28_22 : Poly := List.flatten [c2GroupHessian28_22Chunk0]
theorem c2GroupHessian28_22_check : sumFast (c2TensorGroup28.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian28_22 := by kernel_rfl
private def c2GroupHessian28_23Chunk0 : Poly := [([0,0], 40),([0,3], 40),([0,4], 40),([0,5], 4),([0,6], 4),([0,7], 40),([0,8], 40),([0,9], -8),([3,4], 40),([3,8], 40),([4,7], 40),([5,6], 16),([5,9], 4),([6,9], -4),([7,8], 40),([9,9], -8)]
def c2GroupHessian28_23 : Poly := List.flatten [c2GroupHessian28_23Chunk0]
theorem c2GroupHessian28_23_check : sumFast (c2TensorGroup28.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian28_23 := by kernel_rfl
private def c2GroupHessian28_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 8),([0,8], 80),([0,9], 16),([4,4], 40),([4,8], 80),([6,6], 16),([6,9], 8),([8,8], 40),([9,9], 8)]
def c2GroupHessian28_33 : Poly := List.flatten [c2GroupHessian28_33Chunk0]
theorem c2GroupHessian28_33_check : sumFast (c2TensorGroup28.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian28_33 := by kernel_rfl
end D4.Secondary
