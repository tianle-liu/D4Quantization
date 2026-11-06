import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup36_det_check : c2TensorGroup36.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 53)) = true := by kernel_rfl
private def c2GroupHessian36_00Chunk0 : Poly := [([0,0], 16),([0,5], 40),([0,6], 24),([1,1], 40),([5,5], 40),([5,6], 40),([6,6], 16)]
def c2GroupHessian36_00 : Poly := List.flatten [c2GroupHessian36_00Chunk0]
theorem c2GroupHessian36_00_check : sumFast (c2TensorGroup36.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian36_00 := by kernel_rfl
private def c2GroupHessian36_01Chunk0 : Poly := [([0,0], -4),([0,1], -40),([0,2], -4),([0,5], -20),([0,6], -8),([1,7], -40),([1,8], -40),([2,5], -20),([2,6], -8)]
def c2GroupHessian36_01 : Poly := List.flatten [c2GroupHessian36_01Chunk0]
theorem c2GroupHessian36_01_check : sumFast (c2TensorGroup36.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian36_01 := by kernel_rfl
private def c2GroupHessian36_02Chunk0 : Poly := [([0,0], -12),([0,1], 40),([0,5], -40),([0,6], -8),([0,9], 4),([1,3], 40),([1,7], 40),([5,5], -40),([5,6], -20),([6,9], 4)]
def c2GroupHessian36_02 : Poly := List.flatten [c2GroupHessian36_02Chunk0]
theorem c2GroupHessian36_02_check : sumFast (c2TensorGroup36.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian36_02 := by kernel_rfl
private def c2GroupHessian36_03Chunk0 : Poly := [([0,0], -4),([0,1], 40),([0,6], -16),([0,9], -4),([1,4], 40),([1,8], 40),([5,6], -20),([6,6], -16),([6,9], -4)]
def c2GroupHessian36_03 : Poly := List.flatten [c2GroupHessian36_03Chunk0]
theorem c2GroupHessian36_03_check : sumFast (c2TensorGroup36.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian36_03 := by kernel_rfl
private def c2GroupHessian36_11Chunk0 : Poly := [([0,0], 56),([0,2], 32),([0,7], 80),([0,8], 80),([2,2], 16),([7,7], 40),([7,8], 80),([8,8], 40)]
def c2GroupHessian36_11 : Poly := List.flatten [c2GroupHessian36_11Chunk0]
theorem c2GroupHessian36_11_check : sumFast (c2TensorGroup36.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian36_11 := by kernel_rfl
private def c2GroupHessian36_12Chunk0 : Poly := [([0,0], -32),([0,2], 8),([0,3], -40),([0,5], 20),([0,7], -80),([0,8], -40),([0,9], 4),([2,5], 20),([2,9], 4),([3,7], -40),([3,8], -40),([7,7], -40),([7,8], -40)]
def c2GroupHessian36_12 : Poly := List.flatten [c2GroupHessian36_12Chunk0]
theorem c2GroupHessian36_12_check : sumFast (c2TensorGroup36.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian36_12 := by kernel_rfl
private def c2GroupHessian36_13Chunk0 : Poly := [([0,0], -44),([0,2], -4),([0,4], -40),([0,6], 8),([0,7], -40),([0,8], -80),([0,9], -4),([2,6], 8),([2,9], -4),([4,7], -40),([4,8], -40),([7,8], -40),([8,8], -40)]
def c2GroupHessian36_13 : Poly := List.flatten [c2GroupHessian36_13Chunk0]
theorem c2GroupHessian36_13_check : sumFast (c2TensorGroup36.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian36_13 := by kernel_rfl
private def c2GroupHessian36_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 40),([0,7], 80),([0,9], 8),([3,3], 40),([3,7], 80),([5,5], 40),([7,7], 40),([9,9], 8)]
def c2GroupHessian36_22 : Poly := List.flatten [c2GroupHessian36_22Chunk0]
theorem c2GroupHessian36_22_check : sumFast (c2TensorGroup36.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian36_22 := by kernel_rfl
private def c2GroupHessian36_23Chunk0 : Poly := [([0,0], 36),([0,3], 40),([0,4], 40),([0,6], 8),([0,7], 40),([0,8], 40),([0,9], -12),([3,4], 40),([3,8], 40),([4,7], 40),([5,6], 20),([6,9], -4),([7,8], 40),([9,9], -8)]
def c2GroupHessian36_23 : Poly := List.flatten [c2GroupHessian36_23Chunk0]
theorem c2GroupHessian36_23_check : sumFast (c2TensorGroup36.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian36_23 := by kernel_rfl
private def c2GroupHessian36_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 8),([0,8], 80),([0,9], 16),([4,4], 40),([4,8], 80),([6,6], 16),([6,9], 8),([8,8], 40),([9,9], 8)]
def c2GroupHessian36_33 : Poly := List.flatten [c2GroupHessian36_33Chunk0]
theorem c2GroupHessian36_33_check : sumFast (c2TensorGroup36.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian36_33 := by kernel_rfl
end D4.Secondary
