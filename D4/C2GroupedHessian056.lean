import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup56_det_check : c2TensorGroup56.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 77)) = true := by kernel_rfl
private def c2GroupHessian56_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 80),([0,6], 16),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 8)]
def c2GroupHessian56_00 : Poly := List.flatten [c2GroupHessian56_00Chunk0]
theorem c2GroupHessian56_00_check : sumFast (c2TensorGroup56.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian56_00 := by kernel_rfl
private def c2GroupHessian56_01Chunk0 : Poly := [([0,0], 8),([0,2], 4),([0,6], 8),([0,7], 4),([0,8], -40),([1,8], -40),([2,6], 4),([5,8], -40),([6,7], 4)]
def c2GroupHessian56_01 : Poly := List.flatten [c2GroupHessian56_01Chunk0]
theorem c2GroupHessian56_01_check : sumFast (c2TensorGroup56.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian56_01 := by kernel_rfl
private def c2GroupHessian56_02Chunk0 : Poly := [([0,0], -44),([0,1], -40),([0,5], -80),([0,6], -4),([0,7], -4),([0,9], -40),([1,5], -40),([1,9], -40),([5,5], -40),([5,9], -40),([6,7], -4)]
def c2GroupHessian56_02 : Poly := List.flatten [c2GroupHessian56_02Chunk0]
theorem c2GroupHessian56_02_check : sumFast (c2TensorGroup56.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian56_02 := by kernel_rfl
private def c2GroupHessian56_03Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,4], 40),([0,5], 40),([0,6], -16),([0,8], 40),([0,9], 40),([1,4], 40),([1,8], 40),([1,9], 40),([4,5], 40),([5,8], 40),([5,9], 40),([6,6], -8)]
def c2GroupHessian56_03 : Poly := List.flatten [c2GroupHessian56_03Chunk0]
theorem c2GroupHessian56_03_check : sumFast (c2TensorGroup56.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian56_03 := by kernel_rfl
private def c2GroupHessian56_11Chunk0 : Poly := [([0,0], 16),([0,2], 16),([0,7], 16),([2,2], 16),([2,7], -16),([7,7], 16),([8,8], 40)]
def c2GroupHessian56_11 : Poly := List.flatten [c2GroupHessian56_11Chunk0]
theorem c2GroupHessian56_11_check : sumFast (c2TensorGroup56.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian56_11 := by kernel_rfl
private def c2GroupHessian56_12Chunk0 : Poly := [([0,0], -8),([0,2], 8),([0,7], -24),([0,8], 40),([2,3], 20),([2,7], 8),([3,7], -20),([5,8], 40),([7,7], -16),([8,9], 40)]
def c2GroupHessian56_12 : Poly := List.flatten [c2GroupHessian56_12Chunk0]
theorem c2GroupHessian56_12_check : sumFast (c2TensorGroup56.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian56_12 := by kernel_rfl
private def c2GroupHessian56_13Chunk0 : Poly := [([0,0], -8),([0,2], -4),([0,6], -8),([0,7], -4),([0,8], -40),([2,6], -4),([4,8], -40),([6,7], -4),([8,8], -40),([8,9], -40)]
def c2GroupHessian56_13 : Poly := List.flatten [c2GroupHessian56_13Chunk0]
theorem c2GroupHessian56_13_check : sumFast (c2TensorGroup56.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian56_13 := by kernel_rfl
private def c2GroupHessian56_22Chunk0 : Poly := [([0,0], 56),([0,3], 40),([0,5], 80),([0,7], 32),([0,9], 80),([3,3], 40),([3,7], 40),([5,5], 40),([5,9], 80),([7,7], 16),([9,9], 40)]
def c2GroupHessian56_22 : Poly := List.flatten [c2GroupHessian56_22Chunk0]
theorem c2GroupHessian56_22_check : sumFast (c2TensorGroup56.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian56_22 := by kernel_rfl
private def c2GroupHessian56_23Chunk0 : Poly := [([0,0], -36),([0,4], -40),([0,5], -40),([0,6], 4),([0,7], 4),([0,8], -40),([0,9], -80),([4,5], -40),([4,9], -40),([5,8], -40),([5,9], -40),([6,7], 4),([8,9], -40),([9,9], -40)]
def c2GroupHessian56_23 : Poly := List.flatten [c2GroupHessian56_23Chunk0]
theorem c2GroupHessian56_23_check : sumFast (c2TensorGroup56.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian56_23 := by kernel_rfl
private def c2GroupHessian56_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 16),([0,8], 80),([0,9], 80),([4,4], 40),([4,8], 80),([4,9], 80),([6,6], 8),([8,8], 40),([8,9], 80),([9,9], 40)]
def c2GroupHessian56_33 : Poly := List.flatten [c2GroupHessian56_33Chunk0]
theorem c2GroupHessian56_33_check : sumFast (c2TensorGroup56.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian56_33 := by kernel_rfl
end D4.Secondary
