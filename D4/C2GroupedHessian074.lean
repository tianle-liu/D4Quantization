import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup74_det_check : c2TensorGroup74.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 100)) = true := by kernel_rfl
private def c2GroupHessian74_00Chunk0 : Poly := [([0,0], 160),([0,1], 160),([0,5], 160),([0,6], 160),([1,1], 40),([1,5], 80),([1,6], 80),([5,5], 40),([5,6], 80),([6,6], 40)]
def c2GroupHessian74_00 : Poly := List.flatten [c2GroupHessian74_00Chunk0]
theorem c2GroupHessian74_00_check : sumFast (c2TensorGroup74.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian74_00 := by kernel_rfl
private def c2GroupHessian74_01Chunk0 : Poly := [([0,0], 80),([0,1], 40),([0,5], 40),([0,6], 40)]
def c2GroupHessian74_01 : Poly := List.flatten [c2GroupHessian74_01Chunk0]
theorem c2GroupHessian74_01_check : sumFast (c2TensorGroup74.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian74_01 := by kernel_rfl
private def c2GroupHessian74_02Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -120),([0,6], -40),([1,5], -40),([5,5], -40),([5,6], -40)]
def c2GroupHessian74_02 : Poly := List.flatten [c2GroupHessian74_02Chunk0]
theorem c2GroupHessian74_02_check : sumFast (c2TensorGroup74.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian74_02 := by kernel_rfl
private def c2GroupHessian74_03Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -40),([0,6], -120),([1,6], -40),([5,6], -40),([6,6], -40)]
def c2GroupHessian74_03 : Poly := List.flatten [c2GroupHessian74_03Chunk0]
theorem c2GroupHessian74_03_check : sumFast (c2TensorGroup74.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian74_03 := by kernel_rfl
private def c2GroupHessian74_11Chunk0 : Poly := [([0,0], 48),([0,2], 16),([0,7], 8),([0,8], 16),([2,2], 8),([2,7], 8),([2,8], 16),([7,7], 16),([7,8], 8),([8,8], 8)]
def c2GroupHessian74_11 : Poly := List.flatten [c2GroupHessian74_11Chunk0]
theorem c2GroupHessian74_11_check : sumFast (c2TensorGroup74.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian74_11 := by kernel_rfl
private def c2GroupHessian74_12Chunk0 : Poly := [([0,0], -40),([0,5], -40),([0,7], -24),([2,7], -4),([3,7], -20),([7,7], -16),([7,8], -4),([7,9], -20)]
def c2GroupHessian74_12 : Poly := List.flatten [c2GroupHessian74_12Chunk0]
theorem c2GroupHessian74_12_check : sumFast (c2TensorGroup74.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian74_12 := by kernel_rfl
private def c2GroupHessian74_13Chunk0 : Poly := [([0,0], -44),([0,2], -4),([0,4], 4),([0,6], -40),([0,7], 8),([0,8], -12),([2,4], 4),([2,8], -8),([4,7], -8),([4,8], 4),([7,8], -4),([7,9], 20),([8,8], -8)]
def c2GroupHessian74_13 : Poly := List.flatten [c2GroupHessian74_13Chunk0]
theorem c2GroupHessian74_13_check : sumFast (c2TensorGroup74.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian74_13 := by kernel_rfl
private def c2GroupHessian74_22Chunk0 : Poly := [([0,0], 80),([0,3], 80),([0,5], 80),([0,7], 40),([0,9], 80),([3,3], 40),([3,7], 40),([3,9], 80),([5,5], 40),([7,7], 16),([7,9], 40),([9,9], 40)]
def c2GroupHessian74_22 : Poly := List.flatten [c2GroupHessian74_22Chunk0]
theorem c2GroupHessian74_22_check : sumFast (c2TensorGroup74.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian74_22 := by kernel_rfl
private def c2GroupHessian74_23Chunk0 : Poly := [([0,0], 20),([0,3], -20),([0,4], 20),([0,5], 40),([0,6], 40),([0,7], -8),([0,9], -60),([3,4], 20),([3,9], -40),([4,7], 8),([4,9], 20),([5,6], 40),([7,8], 4),([7,9], -20),([9,9], -40)]
def c2GroupHessian74_23 : Poly := List.flatten [c2GroupHessian74_23Chunk0]
theorem c2GroupHessian74_23_check : sumFast (c2TensorGroup74.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian74_23 := by kernel_rfl
private def c2GroupHessian74_33Chunk0 : Poly := [([0,0], 56),([0,4], -16),([0,6], 80),([0,8], 8),([0,9], 40),([4,4], 16),([4,8], -8),([4,9], -40),([6,6], 40),([8,8], 8),([9,9], 40)]
def c2GroupHessian74_33 : Poly := List.flatten [c2GroupHessian74_33Chunk0]
theorem c2GroupHessian74_33_check : sumFast (c2TensorGroup74.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian74_33 := by kernel_rfl
end D4.Secondary
