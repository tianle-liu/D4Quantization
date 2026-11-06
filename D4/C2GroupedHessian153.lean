import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup153_det_check : c2TensorGroup153.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 192)) = true := by kernel_rfl
private def c2GroupHessian153_00Chunk0 : Poly := [([0,0], 16),([0,1], 16),([0,5], 16),([1,1], 16),([1,5], 32),([5,5], 16),([6,6], 40)]
def c2GroupHessian153_00 : Poly := List.flatten [c2GroupHessian153_00Chunk0]
theorem c2GroupHessian153_00_check : sumFast (c2TensorGroup153.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian153_00 := by kernel_rfl
private def c2GroupHessian153_01Chunk0 : Poly := [([0,0], 8),([0,1], -8),([0,5], -8),([0,6], -40),([1,8], -20),([2,6], -40),([5,8], -20),([6,7], -40)]
def c2GroupHessian153_01 : Poly := List.flatten [c2GroupHessian153_01Chunk0]
theorem c2GroupHessian153_01_check : sumFast (c2TensorGroup153.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian153_01 := by kernel_rfl
private def c2GroupHessian153_02Chunk0 : Poly := [([0,0], -8),([0,1], -4),([0,3], 8),([0,5], -12),([0,6], 40),([1,3], 4),([1,5], -16),([3,5], 4),([5,5], -16),([6,7], 40),([6,9], 40)]
def c2GroupHessian153_02 : Poly := List.flatten [c2GroupHessian153_02Chunk0]
theorem c2GroupHessian153_02_check : sumFast (c2TensorGroup153.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian153_02 := by kernel_rfl
private def c2GroupHessian153_03Chunk0 : Poly := [([0,0], -8),([0,1], 8),([0,5], 8),([0,6], -40),([1,8], 20),([4,6], -40),([5,8], 20),([6,6], -40),([6,9], -40)]
def c2GroupHessian153_03 : Poly := List.flatten [c2GroupHessian153_03Chunk0]
theorem c2GroupHessian153_03_check : sumFast (c2TensorGroup153.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian153_03 := by kernel_rfl
private def c2GroupHessian153_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 80),([0,8], 40),([2,2], 40),([2,7], 80),([7,7], 40),([8,8], 40)]
def c2GroupHessian153_11 : Poly := List.flatten [c2GroupHessian153_11Chunk0]
theorem c2GroupHessian153_11_check : sumFast (c2TensorGroup153.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian153_11 := by kernel_rfl
private def c2GroupHessian153_12Chunk0 : Poly := [([0,0], -44),([0,2], -40),([0,3], 4),([0,5], 8),([0,7], -80),([0,9], -40),([2,7], -40),([2,9], -40),([5,8], 20),([7,7], -40),([7,9], -40)]
def c2GroupHessian153_12 : Poly := List.flatten [c2GroupHessian153_12Chunk0]
theorem c2GroupHessian153_12_check : sumFast (c2TensorGroup153.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian153_12 := by kernel_rfl
private def c2GroupHessian153_13Chunk0 : Poly := [([0,0], 24),([0,2], 40),([0,4], 40),([0,6], 40),([0,7], 40),([0,8], -40),([0,9], 40),([2,4], 40),([2,6], 40),([2,9], 40),([4,7], 40),([6,7], 40),([7,9], 40),([8,8], -40)]
def c2GroupHessian153_13 : Poly := List.flatten [c2GroupHessian153_13Chunk0]
theorem c2GroupHessian153_13_check : sumFast (c2TensorGroup153.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian153_13 := by kernel_rfl
private def c2GroupHessian153_22Chunk0 : Poly := [([0,0], 48),([0,5], 8),([0,7], 80),([0,9], 80),([3,3], 8),([3,5], -8),([5,5], 16),([7,7], 40),([7,9], 80),([9,9], 40)]
def c2GroupHessian153_22 : Poly := List.flatten [c2GroupHessian153_22Chunk0]
theorem c2GroupHessian153_22_check : sumFast (c2TensorGroup153.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian153_22 := by kernel_rfl
private def c2GroupHessian153_23Chunk0 : Poly := [([0,0], -36),([0,3], -4),([0,4], -40),([0,5], -8),([0,6], -40),([0,7], -40),([0,9], -80),([4,7], -40),([4,9], -40),([5,8], -20),([6,7], -40),([6,9], -40),([7,9], -40),([9,9], -40)]
def c2GroupHessian153_23 : Poly := List.flatten [c2GroupHessian153_23Chunk0]
theorem c2GroupHessian153_23_check : sumFast (c2TensorGroup153.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian153_23 := by kernel_rfl
private def c2GroupHessian153_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 80),([0,8], 40),([0,9], 80),([4,4], 40),([4,6], 80),([4,9], 80),([6,6], 40),([6,9], 80),([8,8], 40),([9,9], 40)]
def c2GroupHessian153_33 : Poly := List.flatten [c2GroupHessian153_33Chunk0]
theorem c2GroupHessian153_33_check : sumFast (c2TensorGroup153.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian153_33 := by kernel_rfl
end D4.Secondary
