import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup195_det_check : c2TensorGroup195.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 250)) = true := by kernel_rfl
private def c2GroupHessian195_00Chunk0 : Poly := [([0,0], 104),([0,1], 48),([0,5], 160),([0,6], 48),([1,1], 24),([1,6], 48),([5,5], 80),([6,6], 24)]
def c2GroupHessian195_00 : Poly := List.flatten [c2GroupHessian195_00Chunk0]
theorem c2GroupHessian195_00_check : sumFast (c2TensorGroup195.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian195_00 := by kernel_rfl
private def c2GroupHessian195_01Chunk0 : Poly := [([0,0], 88),([0,1], 8),([0,2], 8),([0,5], 80),([0,6], 8),([0,7], 80),([0,8], 8),([1,2], 8),([1,8], 8),([2,6], 8),([5,7], 80),([6,8], 8)]
def c2GroupHessian195_01 : Poly := List.flatten [c2GroupHessian195_01Chunk0]
theorem c2GroupHessian195_01_check : sumFast (c2TensorGroup195.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian195_01 := by kernel_rfl
private def c2GroupHessian195_02Chunk0 : Poly := [([0,0], -160),([0,3], -80),([0,5], -240),([0,7], -80),([0,9], -80),([3,5], -80),([5,5], -80),([5,7], -80),([5,9], -80)]
def c2GroupHessian195_02 : Poly := List.flatten [c2GroupHessian195_02Chunk0]
theorem c2GroupHessian195_02_check : sumFast (c2TensorGroup195.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian195_02 := by kernel_rfl
private def c2GroupHessian195_03Chunk0 : Poly := [([0,0], -16),([0,1], -16),([0,4], -4),([0,6], -40),([0,8], -8),([0,9], 80),([1,4], -4),([1,6], -24),([1,8], -8),([4,6], -4),([5,9], 80),([6,6], -24),([6,8], -8)]
def c2GroupHessian195_03 : Poly := List.flatten [c2GroupHessian195_03Chunk0]
theorem c2GroupHessian195_03_check : sumFast (c2TensorGroup195.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian195_03 := by kernel_rfl
private def c2GroupHessian195_11Chunk0 : Poly := [([0,0], 104),([0,2], 48),([0,7], 160),([0,8], 48),([2,2], 24),([2,8], 48),([7,7], 80),([8,8], 24)]
def c2GroupHessian195_11 : Poly := List.flatten [c2GroupHessian195_11Chunk0]
theorem c2GroupHessian195_11_check : sumFast (c2TensorGroup195.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian195_11 := by kernel_rfl
private def c2GroupHessian195_12Chunk0 : Poly := [([0,0], -160),([0,3], -80),([0,5], -80),([0,7], -240),([0,9], -80),([3,7], -80),([5,7], -80),([7,7], -80),([7,9], -80)]
def c2GroupHessian195_12 : Poly := List.flatten [c2GroupHessian195_12Chunk0]
theorem c2GroupHessian195_12_check : sumFast (c2TensorGroup195.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian195_12 := by kernel_rfl
private def c2GroupHessian195_13Chunk0 : Poly := [([0,0], -16),([0,2], -16),([0,4], -4),([0,6], -8),([0,8], -40),([0,9], 80),([2,4], -4),([2,6], -8),([2,8], -24),([4,8], -4),([6,8], -8),([7,9], 80),([8,8], -24)]
def c2GroupHessian195_13 : Poly := List.flatten [c2GroupHessian195_13Chunk0]
theorem c2GroupHessian195_13_check : sumFast (c2TensorGroup195.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian195_13 := by kernel_rfl
private def c2GroupHessian195_22Chunk0 : Poly := [([0,0], 320),([0,3], 320),([0,5], 320),([0,7], 320),([0,9], 320),([3,3], 80),([3,5], 160),([3,7], 160),([3,9], 160),([5,5], 80),([5,7], 160),([5,9], 160),([7,7], 80),([7,9], 160),([9,9], 80)]
def c2GroupHessian195_22 : Poly := List.flatten [c2GroupHessian195_22Chunk0]
theorem c2GroupHessian195_22_check : sumFast (c2TensorGroup195.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian195_22 := by kernel_rfl
private def c2GroupHessian195_23Chunk0 : Poly := [([0,9], -160),([3,9], -80),([5,9], -80),([7,9], -80),([9,9], -80)]
def c2GroupHessian195_23 : Poly := List.flatten [c2GroupHessian195_23Chunk0]
theorem c2GroupHessian195_23_check : sumFast (c2TensorGroup195.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian195_23 := by kernel_rfl
private def c2GroupHessian195_33Chunk0 : Poly := [([0,0], 32),([0,4], 48),([0,6], 32),([0,8], 32),([4,4], 32),([4,6], 8),([4,8], 8),([6,6], 24),([6,8], 16),([8,8], 24),([9,9], 80)]
def c2GroupHessian195_33 : Poly := List.flatten [c2GroupHessian195_33Chunk0]
theorem c2GroupHessian195_33_check : sumFast (c2TensorGroup195.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian195_33 := by kernel_rfl
end D4.Secondary
