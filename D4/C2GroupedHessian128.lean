import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup128_det_check : c2TensorGroup128.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 163)) = true := by kernel_rfl
private def c2GroupHessian128_00Chunk0 : Poly := [([0,0], 16),([0,1], 16),([0,6], 16),([1,1], 8),([1,6], 8),([5,5], 40),([6,6], 16)]
def c2GroupHessian128_00 : Poly := List.flatten [c2GroupHessian128_00Chunk0]
theorem c2GroupHessian128_00_check : sumFast (c2TensorGroup128.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian128_00 := by kernel_rfl
private def c2GroupHessian128_01Chunk0 : Poly := [([0,0], 8),([0,1], 4),([0,5], -40),([0,6], -8),([2,5], -40),([5,8], -40),([6,7], -20)]
def c2GroupHessian128_01 : Poly := List.flatten [c2GroupHessian128_01Chunk0]
theorem c2GroupHessian128_01_check : sumFast (c2TensorGroup128.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian128_01 := by kernel_rfl
private def c2GroupHessian128_02Chunk0 : Poly := [([0,0], -8),([0,1], -4),([0,5], -40),([0,6], 8),([3,5], -40),([5,5], -40),([5,9], -40),([6,7], 20)]
def c2GroupHessian128_02 : Poly := List.flatten [c2GroupHessian128_02Chunk0]
theorem c2GroupHessian128_02_check : sumFast (c2TensorGroup128.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian128_02 := by kernel_rfl
private def c2GroupHessian128_03Chunk0 : Poly := [([0,0], -8),([0,1], -4),([0,5], 40),([0,6], -24),([1,6], -4),([4,6], -20),([5,8], 40),([5,9], 40),([6,6], -16)]
def c2GroupHessian128_03 : Poly := List.flatten [c2GroupHessian128_03Chunk0]
theorem c2GroupHessian128_03_check : sumFast (c2TensorGroup128.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian128_03 := by kernel_rfl
private def c2GroupHessian128_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 40),([0,8], 80),([2,2], 40),([2,8], 80),([7,7], 40),([8,8], 40)]
def c2GroupHessian128_11 : Poly := List.flatten [c2GroupHessian128_11Chunk0]
theorem c2GroupHessian128_11_check : sumFast (c2TensorGroup128.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian128_11 := by kernel_rfl
private def c2GroupHessian128_12Chunk0 : Poly := [([0,0], 24),([0,2], 40),([0,3], 40),([0,5], 40),([0,7], -40),([0,8], 40),([0,9], 40),([2,3], 40),([2,5], 40),([2,9], 40),([3,8], 40),([5,8], 40),([7,7], -40),([8,9], 40)]
def c2GroupHessian128_12 : Poly := List.flatten [c2GroupHessian128_12Chunk0]
theorem c2GroupHessian128_12_check : sumFast (c2TensorGroup128.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian128_12 := by kernel_rfl
private def c2GroupHessian128_13Chunk0 : Poly := [([0,0], -32),([0,2], -40),([0,4], 20),([0,6], 8),([0,7], 20),([0,8], -80),([0,9], -40),([2,8], -40),([2,9], -40),([4,7], 40),([6,7], 20),([8,8], -40),([8,9], -40)]
def c2GroupHessian128_13 : Poly := List.flatten [c2GroupHessian128_13Chunk0]
theorem c2GroupHessian128_13_check : sumFast (c2TensorGroup128.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian128_13 := by kernel_rfl
private def c2GroupHessian128_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 80),([0,7], 40),([0,9], 80),([3,3], 40),([3,5], 80),([3,9], 80),([5,5], 40),([5,9], 80),([7,7], 40),([9,9], 40)]
def c2GroupHessian128_22 : Poly := List.flatten [c2GroupHessian128_22Chunk0]
theorem c2GroupHessian128_22_check : sumFast (c2TensorGroup128.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian128_22 := by kernel_rfl
private def c2GroupHessian128_23Chunk0 : Poly := [([0,0], -48),([0,3], -40),([0,4], -20),([0,5], -40),([0,6], -8),([0,7], -20),([0,8], -40),([0,9], -80),([3,8], -40),([3,9], -40),([4,7], -40),([5,8], -40),([5,9], -40),([6,7], -20),([8,9], -40),([9,9], -40)]
def c2GroupHessian128_23 : Poly := List.flatten [c2GroupHessian128_23Chunk0]
theorem c2GroupHessian128_23_check : sumFast (c2TensorGroup128.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian128_23 := by kernel_rfl
private def c2GroupHessian128_33Chunk0 : Poly := [([0,0], 56),([0,4], 40),([0,6], 32),([0,8], 80),([0,9], 80),([4,4], 40),([4,6], 40),([6,6], 16),([8,8], 40),([8,9], 80),([9,9], 40)]
def c2GroupHessian128_33 : Poly := List.flatten [c2GroupHessian128_33Chunk0]
theorem c2GroupHessian128_33_check : sumFast (c2TensorGroup128.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian128_33 := by kernel_rfl
end D4.Secondary
