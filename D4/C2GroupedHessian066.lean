import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup66_det_check : c2TensorGroup66.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 88)) = true := by kernel_rfl
private def c2GroupHessian66_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 80),([0,6], 16),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 8)]
def c2GroupHessian66_00 : Poly := List.flatten [c2GroupHessian66_00Chunk0]
theorem c2GroupHessian66_00_check : sumFast (c2TensorGroup66.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian66_00 := by kernel_rfl
private def c2GroupHessian66_01Chunk0 : Poly := [([0,0], 8),([0,2], 4),([0,6], 8),([0,8], -40),([1,8], -40),([2,6], 4),([5,8], -40)]
def c2GroupHessian66_01 : Poly := List.flatten [c2GroupHessian66_01Chunk0]
theorem c2GroupHessian66_01_check : sumFast (c2TensorGroup66.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian66_01 := by kernel_rfl
private def c2GroupHessian66_02Chunk0 : Poly := [([0,0], -40),([0,1], -40),([0,3], 4),([0,5], -80),([0,9], -40),([1,5], -40),([1,9], -40),([3,6], 4),([5,5], -40),([5,9], -40)]
def c2GroupHessian66_02 : Poly := List.flatten [c2GroupHessian66_02Chunk0]
theorem c2GroupHessian66_02_check : sumFast (c2TensorGroup66.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian66_02 := by kernel_rfl
private def c2GroupHessian66_03Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,4], 40),([0,5], 40),([0,6], -16),([0,8], 40),([0,9], 40),([1,4], 40),([1,8], 40),([1,9], 40),([4,5], 40),([5,8], 40),([5,9], 40),([6,6], -8)]
def c2GroupHessian66_03 : Poly := List.flatten [c2GroupHessian66_03Chunk0]
theorem c2GroupHessian66_03_check : sumFast (c2TensorGroup66.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian66_03 := by kernel_rfl
private def c2GroupHessian66_11Chunk0 : Poly := [([0,0], 48),([0,2], 48),([0,7], 80),([2,2], 16),([2,7], 40),([7,7], 40),([8,8], 40)]
def c2GroupHessian66_11 : Poly := List.flatten [c2GroupHessian66_11Chunk0]
theorem c2GroupHessian66_11_check : sumFast (c2TensorGroup66.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian66_11 := by kernel_rfl
private def c2GroupHessian66_12Chunk0 : Poly := [([0,0], -40),([0,2], -20),([0,3], -16),([0,7], -80),([0,8], 40),([2,3], -8),([2,7], -20),([3,7], -20),([5,8], 40),([7,7], -40),([8,9], 40)]
def c2GroupHessian66_12 : Poly := List.flatten [c2GroupHessian66_12Chunk0]
theorem c2GroupHessian66_12_check : sumFast (c2TensorGroup66.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian66_12 := by kernel_rfl
private def c2GroupHessian66_13Chunk0 : Poly := [([0,0], -8),([0,2], -4),([0,6], -8),([0,8], -40),([2,6], -4),([4,8], -40),([8,8], -40),([8,9], -40)]
def c2GroupHessian66_13 : Poly := List.flatten [c2GroupHessian66_13Chunk0]
theorem c2GroupHessian66_13_check : sumFast (c2TensorGroup66.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian66_13 := by kernel_rfl
private def c2GroupHessian66_22Chunk0 : Poly := [([0,0], 80),([0,3], 40),([0,5], 80),([0,7], 80),([0,9], 80),([3,3], 16),([3,7], 40),([5,5], 40),([5,9], 80),([7,7], 40),([9,9], 40)]
def c2GroupHessian66_22 : Poly := List.flatten [c2GroupHessian66_22Chunk0]
theorem c2GroupHessian66_22_check : sumFast (c2TensorGroup66.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian66_22 := by kernel_rfl
private def c2GroupHessian66_23Chunk0 : Poly := [([0,0], -40),([0,3], -4),([0,4], -40),([0,5], -40),([0,8], -40),([0,9], -80),([3,6], -4),([4,5], -40),([4,9], -40),([5,8], -40),([5,9], -40),([8,9], -40),([9,9], -40)]
def c2GroupHessian66_23 : Poly := List.flatten [c2GroupHessian66_23Chunk0]
theorem c2GroupHessian66_23_check : sumFast (c2TensorGroup66.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian66_23 := by kernel_rfl
private def c2GroupHessian66_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 16),([0,8], 80),([0,9], 80),([4,4], 40),([4,8], 80),([4,9], 80),([6,6], 8),([8,8], 40),([8,9], 80),([9,9], 40)]
def c2GroupHessian66_33 : Poly := List.flatten [c2GroupHessian66_33Chunk0]
theorem c2GroupHessian66_33_check : sumFast (c2TensorGroup66.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian66_33 := by kernel_rfl
end D4.Secondary
