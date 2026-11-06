import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup10_det_check : c2TensorGroup10.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 11)) = true := by kernel_rfl
private def c2GroupHessian10_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,6], 16),([1,1], 40),([5,5], 40),([6,6], 8)]
def c2GroupHessian10_00 : Poly := List.flatten [c2GroupHessian10_00Chunk0]
theorem c2GroupHessian10_00_check : sumFast (c2TensorGroup10.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian10_00 := by kernel_rfl
private def c2GroupHessian10_01Chunk0 : Poly := [([0,0], 48),([0,1], 40),([0,2], 40),([0,6], 8),([0,7], 4),([0,8], 4),([1,2], 40),([5,7], 20),([5,8], -20),([6,7], 4),([6,8], 4)]
def c2GroupHessian10_01 : Poly := List.flatten [c2GroupHessian10_01Chunk0]
theorem c2GroupHessian10_01_check : sumFast (c2TensorGroup10.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian10_01 := by kernel_rfl
private def c2GroupHessian10_02Chunk0 : Poly := [([0,0], -4),([0,3], 40),([0,5], -20),([0,6], -4),([0,7], -4),([0,9], 4),([1,3], 40),([5,5], -40),([5,7], -20),([5,9], -20),([6,7], -4),([6,9], 4)]
def c2GroupHessian10_02 : Poly := List.flatten [c2GroupHessian10_02Chunk0]
theorem c2GroupHessian10_02_check : sumFast (c2TensorGroup10.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian10_02 := by kernel_rfl
private def c2GroupHessian10_03Chunk0 : Poly := [([0,0], -12),([0,4], 40),([0,5], 20),([0,6], -20),([0,8], -4),([0,9], -4),([1,4], 40),([5,8], 20),([5,9], 20),([6,6], -8),([6,8], -4),([6,9], -4)]
def c2GroupHessian10_03 : Poly := List.flatten [c2GroupHessian10_03Chunk0]
theorem c2GroupHessian10_03_check : sumFast (c2TensorGroup10.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian10_03 := by kernel_rfl
private def c2GroupHessian10_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 8),([0,8], 8),([2,2], 40),([7,7], 16),([7,8], -16),([8,8], 16)]
def c2GroupHessian10_11 : Poly := List.flatten [c2GroupHessian10_11Chunk0]
theorem c2GroupHessian10_11_check : sumFast (c2TensorGroup10.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian10_11 := by kernel_rfl
private def c2GroupHessian10_12Chunk0 : Poly := [([0,0], -4),([0,3], 40),([0,7], -16),([0,8], 12),([0,9], 4),([2,3], 40),([5,7], -20),([5,8], 20),([7,7], -16),([7,8], 8),([7,9], -8),([8,9], 16)]
def c2GroupHessian10_12 : Poly := List.flatten [c2GroupHessian10_12Chunk0]
theorem c2GroupHessian10_12_check : sumFast (c2TensorGroup10.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian10_12 := by kernel_rfl
private def c2GroupHessian10_13Chunk0 : Poly := [([0,0], -12),([0,4], 40),([0,6], -8),([0,7], 4),([0,8], -24),([0,9], -4),([2,4], 40),([6,7], -4),([6,8], -4),([7,8], 8),([7,9], 8),([8,8], -16),([8,9], -16)]
def c2GroupHessian10_13 : Poly := List.flatten [c2GroupHessian10_13Chunk0]
theorem c2GroupHessian10_13_check : sumFast (c2TensorGroup10.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian10_13 := by kernel_rfl
private def c2GroupHessian10_22Chunk0 : Poly := [([0,0], 16),([0,5], 40),([0,7], 24),([0,9], 24),([3,3], 40),([5,5], 40),([5,7], 40),([5,9], 40),([7,7], 16),([7,9], 16),([9,9], 16)]
def c2GroupHessian10_22 : Poly := List.flatten [c2GroupHessian10_22Chunk0]
theorem c2GroupHessian10_22_check : sumFast (c2TensorGroup10.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian10_22 := by kernel_rfl
private def c2GroupHessian10_23Chunk0 : Poly := [([0,0], -8),([0,5], -20),([0,6], 4),([0,7], -4),([0,8], -12),([0,9], -32),([3,4], 40),([5,8], -20),([5,9], -20),([6,7], 4),([6,9], -4),([7,8], -8),([7,9], -8),([8,9], -16),([9,9], -16)]
def c2GroupHessian10_23 : Poly := List.flatten [c2GroupHessian10_23Chunk0]
theorem c2GroupHessian10_23_check : sumFast (c2TensorGroup10.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian10_23 := by kernel_rfl
private def c2GroupHessian10_33Chunk0 : Poly := [([0,0], 32),([0,6], 24),([0,8], 40),([0,9], 40),([4,4], 40),([6,6], 8),([6,8], 8),([6,9], 8),([8,8], 16),([8,9], 32),([9,9], 16)]
def c2GroupHessian10_33 : Poly := List.flatten [c2GroupHessian10_33Chunk0]
theorem c2GroupHessian10_33_check : sumFast (c2TensorGroup10.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian10_33 := by kernel_rfl
end D4.Secondary
