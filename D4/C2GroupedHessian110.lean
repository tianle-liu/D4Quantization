import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup110_det_check : c2TensorGroup110.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 142)) = true := by kernel_rfl
private def c2GroupHessian110_00Chunk0 : Poly := [([0,0], 56),([0,1], 40),([0,5], 80),([0,6], 80),([1,1], 40),([5,5], 40),([5,6], 80),([6,6], 40)]
def c2GroupHessian110_00 : Poly := List.flatten [c2GroupHessian110_00Chunk0]
theorem c2GroupHessian110_00_check : sumFast (c2TensorGroup110.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian110_00 := by kernel_rfl
private def c2GroupHessian110_01Chunk0 : Poly := [([0,0], 8),([0,2], -40),([0,7], -8),([0,8], -8),([1,7], -20),([1,8], -20),([2,5], -40),([2,6], -40)]
def c2GroupHessian110_01 : Poly := List.flatten [c2GroupHessian110_01Chunk0]
theorem c2GroupHessian110_01_check : sumFast (c2TensorGroup110.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian110_01 := by kernel_rfl
private def c2GroupHessian110_02Chunk0 : Poly := [([0,0], -44),([0,3], -40),([0,5], -80),([0,6], -40),([0,7], 8),([0,9], 4),([1,7], 20),([3,5], -40),([3,6], -40),([5,5], -40),([5,6], -40)]
def c2GroupHessian110_02 : Poly := List.flatten [c2GroupHessian110_02Chunk0]
theorem c2GroupHessian110_02_check : sumFast (c2TensorGroup110.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian110_02 := by kernel_rfl
private def c2GroupHessian110_03Chunk0 : Poly := [([0,0], -44),([0,4], -40),([0,5], -40),([0,6], -80),([0,8], 8),([0,9], -4),([1,8], 20),([4,5], -40),([4,6], -40),([5,6], -40),([6,6], -40)]
def c2GroupHessian110_03 : Poly := List.flatten [c2GroupHessian110_03Chunk0]
theorem c2GroupHessian110_03_check : sumFast (c2TensorGroup110.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian110_03 := by kernel_rfl
private def c2GroupHessian110_11Chunk0 : Poly := [([0,0], 16),([0,7], 16),([0,8], 16),([2,2], 40),([7,7], 16),([7,8], 32),([8,8], 16)]
def c2GroupHessian110_11 : Poly := List.flatten [c2GroupHessian110_11Chunk0]
theorem c2GroupHessian110_11_check : sumFast (c2TensorGroup110.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian110_11 := by kernel_rfl
private def c2GroupHessian110_12Chunk0 : Poly := [([0,0], -8),([0,2], 40),([0,7], -12),([0,8], -4),([0,9], 8),([2,3], 40),([2,5], 40),([7,7], -16),([7,8], -16),([7,9], 4),([8,9], 4)]
def c2GroupHessian110_12 : Poly := List.flatten [c2GroupHessian110_12Chunk0]
theorem c2GroupHessian110_12_check : sumFast (c2TensorGroup110.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian110_12 := by kernel_rfl
private def c2GroupHessian110_13Chunk0 : Poly := [([0,0], -8),([0,2], 40),([0,7], -4),([0,8], -12),([0,9], -8),([2,4], 40),([2,6], 40),([7,8], -16),([7,9], -4),([8,8], -16),([8,9], -4)]
def c2GroupHessian110_13 : Poly := List.flatten [c2GroupHessian110_13Chunk0]
theorem c2GroupHessian110_13_check : sumFast (c2TensorGroup110.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian110_13 := by kernel_rfl
private def c2GroupHessian110_22Chunk0 : Poly := [([0,0], 48),([0,3], 80),([0,5], 80),([0,7], 8),([3,3], 40),([3,5], 80),([5,5], 40),([7,7], 16),([7,9], -8),([9,9], 8)]
def c2GroupHessian110_22 : Poly := List.flatten [c2GroupHessian110_22Chunk0]
theorem c2GroupHessian110_22_check : sumFast (c2TensorGroup110.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian110_22 := by kernel_rfl
private def c2GroupHessian110_23Chunk0 : Poly := [([0,0], 40),([0,3], 40),([0,4], 40),([0,5], 40),([0,6], 40),([0,7], 4),([0,8], 4),([0,9], -8),([3,4], 40),([3,6], 40),([4,5], 40),([5,6], 40),([7,8], 16),([7,9], 4),([8,9], -4),([9,9], -8)]
def c2GroupHessian110_23 : Poly := List.flatten [c2GroupHessian110_23Chunk0]
theorem c2GroupHessian110_23_check : sumFast (c2TensorGroup110.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian110_23 := by kernel_rfl
private def c2GroupHessian110_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 80),([0,8], 8),([0,9], 16),([4,4], 40),([4,6], 80),([6,6], 40),([8,8], 16),([8,9], 8),([9,9], 8)]
def c2GroupHessian110_33 : Poly := List.flatten [c2GroupHessian110_33Chunk0]
theorem c2GroupHessian110_33_check : sumFast (c2TensorGroup110.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian110_33 := by kernel_rfl
end D4.Secondary
