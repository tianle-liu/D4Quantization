import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup120_det_check : c2TensorGroup120.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 153)) = true := by kernel_rfl
private def c2GroupHessian120_00Chunk0 : Poly := [([0,0], 104),([0,1], 48),([0,5], 160),([0,6], 160),([1,1], 24),([5,5], 80),([5,6], 160),([6,6], 80)]
def c2GroupHessian120_00 : Poly := List.flatten [c2GroupHessian120_00Chunk0]
theorem c2GroupHessian120_00_check : sumFast (c2TensorGroup120.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian120_00 := by kernel_rfl
private def c2GroupHessian120_01Chunk0 : Poly := [([0,0], 16),([0,1], 16),([0,2], -80),([0,7], -4),([0,8], 8),([1,7], -4),([1,8], 8),([2,5], -80),([2,6], -80)]
def c2GroupHessian120_01 : Poly := List.flatten [c2GroupHessian120_01Chunk0]
theorem c2GroupHessian120_01_check : sumFast (c2TensorGroup120.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian120_01 := by kernel_rfl
private def c2GroupHessian120_02Chunk0 : Poly := [([0,0], -88),([0,1], -8),([0,3], -80),([0,5], -160),([0,6], -80),([0,7], 4),([0,9], 8),([1,7], 4),([1,9], 8),([3,5], -80),([3,6], -80),([5,5], -80),([5,6], -80)]
def c2GroupHessian120_02 : Poly := List.flatten [c2GroupHessian120_02Chunk0]
theorem c2GroupHessian120_02_check : sumFast (c2TensorGroup120.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian120_02 := by kernel_rfl
private def c2GroupHessian120_03Chunk0 : Poly := [([0,0], -88),([0,1], -8),([0,4], -80),([0,5], -80),([0,6], -160),([0,8], -8),([0,9], -8),([1,8], -8),([1,9], -8),([4,5], -80),([4,6], -80),([5,6], -80),([6,6], -80)]
def c2GroupHessian120_03 : Poly := List.flatten [c2GroupHessian120_03Chunk0]
theorem c2GroupHessian120_03_check : sumFast (c2TensorGroup120.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian120_03 := by kernel_rfl
private def c2GroupHessian120_11Chunk0 : Poly := [([0,0], 32),([0,7], 32),([0,8], 32),([2,2], 80),([7,7], 32),([7,8], -8),([8,8], 24)]
def c2GroupHessian120_11 : Poly := List.flatten [c2GroupHessian120_11Chunk0]
theorem c2GroupHessian120_11_check : sumFast (c2TensorGroup120.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian120_11 := by kernel_rfl
private def c2GroupHessian120_12Chunk0 : Poly := [([0,0], -16),([0,2], 80),([0,7], -36),([0,8], 8),([0,9], 16),([2,3], 80),([2,5], 80),([7,7], -32),([7,8], 4),([7,9], -4),([8,9], 24)]
def c2GroupHessian120_12 : Poly := List.flatten [c2GroupHessian120_12Chunk0]
theorem c2GroupHessian120_12_check : sumFast (c2TensorGroup120.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian120_12 := by kernel_rfl
private def c2GroupHessian120_13Chunk0 : Poly := [([0,0], -16),([0,2], 80),([0,7], 4),([0,8], -40),([0,9], -16),([2,4], 80),([2,6], 80),([7,8], 4),([7,9], 4),([8,8], -24),([8,9], -24)]
def c2GroupHessian120_13 : Poly := List.flatten [c2GroupHessian120_13Chunk0]
theorem c2GroupHessian120_13_check : sumFast (c2TensorGroup120.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian120_13 := by kernel_rfl
private def c2GroupHessian120_22Chunk0 : Poly := [([0,0], 104),([0,3], 160),([0,5], 160),([0,7], 40),([0,9], 16),([3,3], 80),([3,5], 160),([5,5], 80),([7,7], 32),([7,9], 8),([9,9], 24)]
def c2GroupHessian120_22 : Poly := List.flatten [c2GroupHessian120_22Chunk0]
theorem c2GroupHessian120_22_check : sumFast (c2TensorGroup120.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian120_22 := by kernel_rfl
private def c2GroupHessian120_23Chunk0 : Poly := [([0,0], 72),([0,3], 80),([0,4], 80),([0,5], 80),([0,6], 80),([0,7], -4),([0,8], -8),([0,9], -32),([3,4], 80),([3,6], 80),([4,5], 80),([5,6], 80),([7,8], -4),([7,9], -4),([8,9], -24),([9,9], -24)]
def c2GroupHessian120_23 : Poly := List.flatten [c2GroupHessian120_23Chunk0]
theorem c2GroupHessian120_23_check : sumFast (c2TensorGroup120.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian120_23 := by kernel_rfl
private def c2GroupHessian120_33Chunk0 : Poly := [([0,0], 104),([0,4], 160),([0,6], 160),([0,8], 48),([0,9], 48),([4,4], 80),([4,6], 160),([6,6], 80),([8,8], 24),([8,9], 48),([9,9], 24)]
def c2GroupHessian120_33 : Poly := List.flatten [c2GroupHessian120_33Chunk0]
theorem c2GroupHessian120_33_check : sumFast (c2TensorGroup120.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian120_33 := by kernel_rfl
end D4.Secondary
