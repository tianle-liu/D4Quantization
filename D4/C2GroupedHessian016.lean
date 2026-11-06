import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup16_det_check : c2TensorGroup16.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 19)) = true := by kernel_rfl
private def c2GroupHessian16_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 40),([0,6], -16),([1,1], 40),([5,5], 40),([5,6], -40),([6,6], 16)]
def c2GroupHessian16_00 : Poly := List.flatten [c2GroupHessian16_00Chunk0]
theorem c2GroupHessian16_00_check : sumFast (c2TensorGroup16.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian16_00 := by kernel_rfl
private def c2GroupHessian16_01Chunk0 : Poly := [([0,0], 56),([0,1], 40),([0,2], 40),([0,5], 20),([0,6], -8),([0,7], 20),([0,8], 4),([1,2], 40),([5,7], 40),([6,7], -20),([6,8], 4)]
def c2GroupHessian16_01 : Poly := List.flatten [c2GroupHessian16_01Chunk0]
theorem c2GroupHessian16_01_check : sumFast (c2TensorGroup16.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian16_01 := by kernel_rfl
private def c2GroupHessian16_02Chunk0 : Poly := [([0,0], -24),([0,3], 40),([0,5], -60),([0,6], 24),([0,7], -20),([0,9], -8),([1,3], 40),([5,5], -40),([5,6], 20),([5,7], -40),([5,9], -20),([6,7], 20),([6,9], 16)]
def c2GroupHessian16_02 : Poly := List.flatten [c2GroupHessian16_02Chunk0]
theorem c2GroupHessian16_02_check : sumFast (c2TensorGroup16.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian16_02 := by kernel_rfl
private def c2GroupHessian16_03Chunk0 : Poly := [([0,0], -8),([0,4], 40),([0,8], -4),([0,9], 8),([1,4], 40),([5,6], 20),([5,9], 20),([6,6], -16),([6,8], -4),([6,9], -16)]
def c2GroupHessian16_03 : Poly := List.flatten [c2GroupHessian16_03Chunk0]
theorem c2GroupHessian16_03_check : sumFast (c2TensorGroup16.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian16_03 := by kernel_rfl
private def c2GroupHessian16_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 40),([0,8], 8),([2,2], 40),([7,7], 40),([8,8], 8)]
def c2GroupHessian16_11 : Poly := List.flatten [c2GroupHessian16_11Chunk0]
theorem c2GroupHessian16_11_check : sumFast (c2TensorGroup16.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian16_11 := by kernel_rfl
private def c2GroupHessian16_12Chunk0 : Poly := [([0,0], -24),([0,3], 40),([0,5], -20),([0,7], -60),([0,9], -8),([2,3], 40),([5,7], -40),([7,7], -40),([7,9], -20),([8,9], 4)]
def c2GroupHessian16_12 : Poly := List.flatten [c2GroupHessian16_12Chunk0]
theorem c2GroupHessian16_12_check : sumFast (c2TensorGroup16.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian16_12 := by kernel_rfl
private def c2GroupHessian16_13Chunk0 : Poly := [([0,0], -8),([0,4], 40),([0,6], 8),([0,8], -12),([0,9], 8),([2,4], 40),([6,7], 20),([6,8], -4),([7,9], 20),([8,8], -8),([8,9], -4)]
def c2GroupHessian16_13 : Poly := List.flatten [c2GroupHessian16_13Chunk0]
theorem c2GroupHessian16_13_check : sumFast (c2TensorGroup16.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian16_13 := by kernel_rfl
private def c2GroupHessian16_22Chunk0 : Poly := [([0,0], 48),([0,5], 80),([0,7], 80),([0,9], 48),([3,3], 40),([5,5], 40),([5,7], 80),([5,9], 40),([7,7], 40),([7,9], 40),([9,9], 16)]
def c2GroupHessian16_22 : Poly := List.flatten [c2GroupHessian16_22Chunk0]
theorem c2GroupHessian16_22_check : sumFast (c2TensorGroup16.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian16_22 := by kernel_rfl
private def c2GroupHessian16_23Chunk0 : Poly := [([0,6], -24),([0,9], -32),([3,4], 40),([5,6], -20),([5,9], -20),([6,7], -20),([6,9], -16),([7,9], -20),([8,9], -4),([9,9], -16)]
def c2GroupHessian16_23 : Poly := List.flatten [c2GroupHessian16_23Chunk0]
theorem c2GroupHessian16_23_check : sumFast (c2TensorGroup16.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian16_23 := by kernel_rfl
private def c2GroupHessian16_33Chunk0 : Poly := [([0,0], 16),([0,6], 16),([0,8], 16),([0,9], 16),([4,4], 40),([6,6], 16),([6,8], 8),([6,9], 32),([8,8], 8),([8,9], 8),([9,9], 16)]
def c2GroupHessian16_33 : Poly := List.flatten [c2GroupHessian16_33Chunk0]
theorem c2GroupHessian16_33_check : sumFast (c2TensorGroup16.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian16_33 := by kernel_rfl
end D4.Secondary
