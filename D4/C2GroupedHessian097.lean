import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup97_det_check : c2TensorGroup97.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 127)) = true := by kernel_rfl
private def c2GroupHessian97_00Chunk0 : Poly := [([0,0], 160),([0,1], 160),([0,5], 160),([0,6], 160),([1,1], 40),([1,5], 80),([1,6], 80),([5,5], 40),([5,6], 80),([6,6], 40)]
def c2GroupHessian97_00 : Poly := List.flatten [c2GroupHessian97_00Chunk0]
theorem c2GroupHessian97_00_check : sumFast (c2TensorGroup97.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian97_00 := by kernel_rfl
private def c2GroupHessian97_01Chunk0 : Poly := [([0,0], 80),([0,1], 40),([0,5], 40),([0,6], 40)]
def c2GroupHessian97_01 : Poly := List.flatten [c2GroupHessian97_01Chunk0]
theorem c2GroupHessian97_01_check : sumFast (c2TensorGroup97.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian97_01 := by kernel_rfl
private def c2GroupHessian97_02Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -120),([0,6], -40),([1,5], -40),([5,5], -40),([5,6], -40)]
def c2GroupHessian97_02 : Poly := List.flatten [c2GroupHessian97_02Chunk0]
theorem c2GroupHessian97_02_check : sumFast (c2TensorGroup97.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian97_02 := by kernel_rfl
private def c2GroupHessian97_03Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -40),([0,6], -120),([1,6], -40),([5,6], -40),([6,6], -40)]
def c2GroupHessian97_03 : Poly := List.flatten [c2GroupHessian97_03Chunk0]
theorem c2GroupHessian97_03_check : sumFast (c2TensorGroup97.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian97_03 := by kernel_rfl
private def c2GroupHessian97_11Chunk0 : Poly := [([0,0], 48),([0,2], 8),([0,7], 16),([0,8], 8),([2,2], 16),([2,7], 8),([2,8], -16),([7,7], 8),([7,8], 8),([8,8], 16)]
def c2GroupHessian97_11 : Poly := List.flatten [c2GroupHessian97_11Chunk0]
theorem c2GroupHessian97_11_check : sumFast (c2TensorGroup97.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian97_11 := by kernel_rfl
private def c2GroupHessian97_12Chunk0 : Poly := [([0,0], -44),([0,2], -8),([0,3], 4),([0,5], -40),([0,7], -12),([0,8], 8),([2,3], 16),([2,7], -4),([2,9], -20),([3,7], 4),([3,8], -8),([7,7], -8),([7,8], -4),([8,9], 20)]
def c2GroupHessian97_12 : Poly := List.flatten [c2GroupHessian97_12Chunk0]
theorem c2GroupHessian97_12_check : sumFast (c2TensorGroup97.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian97_12 := by kernel_rfl
private def c2GroupHessian97_13Chunk0 : Poly := [([0,0], -40),([0,2], 20),([0,4], 4),([0,6], -40),([0,8], -24),([2,4], 16),([2,8], 8),([2,9], 20),([4,7], 4),([4,8], -8),([7,8], -4),([8,8], -16),([8,9], -20)]
def c2GroupHessian97_13 : Poly := List.flatten [c2GroupHessian97_13Chunk0]
theorem c2GroupHessian97_13_check : sumFast (c2TensorGroup97.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian97_13 := by kernel_rfl
private def c2GroupHessian97_22Chunk0 : Poly := [([0,0], 56),([0,3], -16),([0,5], 80),([0,7], 8),([0,9], 40),([3,3], 16),([3,7], -8),([3,9], -40),([5,5], 40),([7,7], 8),([9,9], 40)]
def c2GroupHessian97_22 : Poly := List.flatten [c2GroupHessian97_22Chunk0]
theorem c2GroupHessian97_22_check : sumFast (c2TensorGroup97.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian97_22 := by kernel_rfl
private def c2GroupHessian97_23Chunk0 : Poly := [([0,0], 20),([0,3], 20),([0,4], -8),([0,5], 40),([0,6], 40),([0,8], -8),([0,9], -60),([3,4], 16),([3,8], 8),([3,9], 20),([4,7], -4),([4,9], -20),([5,6], 40),([7,8], 4),([8,9], -20),([9,9], -40)]
def c2GroupHessian97_23 : Poly := List.flatten [c2GroupHessian97_23Chunk0]
theorem c2GroupHessian97_23_check : sumFast (c2TensorGroup97.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian97_23 := by kernel_rfl
private def c2GroupHessian97_33Chunk0 : Poly := [([0,0], 80),([0,4], 40),([0,6], 80),([0,8], 40),([0,9], 80),([4,4], 16),([4,8], 16),([4,9], 40),([6,6], 40),([8,8], 16),([8,9], 40),([9,9], 40)]
def c2GroupHessian97_33 : Poly := List.flatten [c2GroupHessian97_33Chunk0]
theorem c2GroupHessian97_33_check : sumFast (c2TensorGroup97.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian97_33 := by kernel_rfl
end D4.Secondary
