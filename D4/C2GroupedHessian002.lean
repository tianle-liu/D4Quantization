import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup2_det_check : c2TensorGroup2.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 3)) = true := by kernel_rfl
private def c2GroupHessian2_00Chunk0 : Poly := [([0,0], 104),([0,1], 160),([0,5], 48),([0,6], 48),([1,1], 80),([5,5], 24),([5,6], 48),([6,6], 24)]
def c2GroupHessian2_00 : Poly := List.flatten [c2GroupHessian2_00Chunk0]
theorem c2GroupHessian2_00_check : sumFast (c2TensorGroup2.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian2_00 := by kernel_rfl
private def c2GroupHessian2_01Chunk0 : Poly := [([0,0], 88),([0,1], 80),([0,2], 80),([0,5], 8),([0,6], 8),([0,7], 8),([0,8], 8),([1,2], 80),([5,7], 8),([5,8], 8),([6,7], 8),([6,8], 8)]
def c2GroupHessian2_01 : Poly := List.flatten [c2GroupHessian2_01Chunk0]
theorem c2GroupHessian2_01_check : sumFast (c2TensorGroup2.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian2_01 := by kernel_rfl
private def c2GroupHessian2_02Chunk0 : Poly := [([0,0], -16),([0,3], 80),([0,5], -40),([0,6], -16),([0,7], -8),([0,9], -4),([1,3], 80),([5,5], -24),([5,6], -24),([5,7], -8),([5,9], -4),([6,7], -8),([6,9], -4)]
def c2GroupHessian2_02 : Poly := List.flatten [c2GroupHessian2_02Chunk0]
theorem c2GroupHessian2_02_check : sumFast (c2TensorGroup2.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian2_02 := by kernel_rfl
private def c2GroupHessian2_03Chunk0 : Poly := [([0,0], -16),([0,4], 80),([0,5], -16),([0,6], -40),([0,8], -8),([0,9], 4),([1,4], 80),([5,6], -24),([5,8], -8),([5,9], 4),([6,6], -24),([6,8], -8),([6,9], 4)]
def c2GroupHessian2_03 : Poly := List.flatten [c2GroupHessian2_03Chunk0]
theorem c2GroupHessian2_03_check : sumFast (c2TensorGroup2.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian2_03 := by kernel_rfl
private def c2GroupHessian2_11Chunk0 : Poly := [([0,0], 104),([0,2], 160),([0,7], 48),([0,8], 48),([2,2], 80),([7,7], 24),([7,8], 48),([8,8], 24)]
def c2GroupHessian2_11 : Poly := List.flatten [c2GroupHessian2_11Chunk0]
theorem c2GroupHessian2_11_check : sumFast (c2TensorGroup2.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian2_11 := by kernel_rfl
private def c2GroupHessian2_12Chunk0 : Poly := [([0,0], -16),([0,3], 80),([0,5], -8),([0,7], -40),([0,8], -16),([0,9], -4),([2,3], 80),([5,7], -8),([5,8], -8),([7,7], -24),([7,8], -24),([7,9], -4),([8,9], -4)]
def c2GroupHessian2_12 : Poly := List.flatten [c2GroupHessian2_12Chunk0]
theorem c2GroupHessian2_12_check : sumFast (c2TensorGroup2.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian2_12 := by kernel_rfl
private def c2GroupHessian2_13Chunk0 : Poly := [([0,0], -16),([0,4], 80),([0,6], -8),([0,7], -16),([0,8], -40),([0,9], 4),([2,4], 80),([6,7], -8),([6,8], -8),([7,8], -24),([7,9], 4),([8,8], -24),([8,9], 4)]
def c2GroupHessian2_13 : Poly := List.flatten [c2GroupHessian2_13Chunk0]
theorem c2GroupHessian2_13_check : sumFast (c2TensorGroup2.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian2_13 := by kernel_rfl
private def c2GroupHessian2_22Chunk0 : Poly := [([0,0], 32),([0,5], 32),([0,7], 32),([0,9], 48),([3,3], 80),([5,5], 24),([5,7], 16),([5,9], 8),([7,7], 24),([7,9], 8),([9,9], 32)]
def c2GroupHessian2_22 : Poly := List.flatten [c2GroupHessian2_22Chunk0]
theorem c2GroupHessian2_22_check : sumFast (c2TensorGroup2.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian2_22 := by kernel_rfl
private def c2GroupHessian2_23Chunk0 : Poly := [([0,5], 16),([0,6], 16),([0,7], 16),([0,8], 16),([0,9], -40),([3,4], 80),([5,6], 24),([5,8], 8),([5,9], -4),([6,7], 8),([6,9], 4),([7,8], 24),([7,9], -4),([8,9], 4),([9,9], -32)]
def c2GroupHessian2_23 : Poly := List.flatten [c2GroupHessian2_23Chunk0]
theorem c2GroupHessian2_23_check : sumFast (c2TensorGroup2.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian2_23 := by kernel_rfl
private def c2GroupHessian2_33Chunk0 : Poly := [([0,0], 32),([0,6], 32),([0,8], 32),([0,9], 32),([4,4], 80),([6,6], 24),([6,8], 16),([6,9], -8),([8,8], 24),([8,9], -8),([9,9], 32)]
def c2GroupHessian2_33 : Poly := List.flatten [c2GroupHessian2_33Chunk0]
theorem c2GroupHessian2_33_check : sumFast (c2TensorGroup2.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian2_33 := by kernel_rfl
end D4.Secondary
