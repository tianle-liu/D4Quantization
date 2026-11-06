import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup52_det_check : c2TensorGroup52.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 71)) = true := by kernel_rfl
private def c2GroupHessian52_00Chunk0 : Poly := [([0,0], 112),([0,1], 160),([0,5], -8),([0,6], 160),([1,1], 80),([1,6], 160),([5,5], 24),([6,6], 80)]
def c2GroupHessian52_00 : Poly := List.flatten [c2GroupHessian52_00Chunk0]
theorem c2GroupHessian52_00_check : sumFast (c2TensorGroup52.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian52_00 := by kernel_rfl
private def c2GroupHessian52_01Chunk0 : Poly := [([0,0], 64),([0,2], 32),([0,5], -8),([0,7], -80),([0,8], 32),([1,7], -80),([2,5], -4),([5,8], -4),([6,7], -80)]
def c2GroupHessian52_01 : Poly := List.flatten [c2GroupHessian52_01Chunk0]
theorem c2GroupHessian52_01_check : sumFast (c2TensorGroup52.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian52_01 := by kernel_rfl
private def c2GroupHessian52_02Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,3], 80),([0,5], 8),([0,6], 80),([0,7], 80),([0,9], 80),([1,3], 80),([1,7], 80),([1,9], 80),([3,6], 80),([5,5], -24),([6,7], 80),([6,9], 80)]
def c2GroupHessian52_02 : Poly := List.flatten [c2GroupHessian52_02Chunk0]
theorem c2GroupHessian52_02_check : sumFast (c2TensorGroup52.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian52_02 := by kernel_rfl
private def c2GroupHessian52_03Chunk0 : Poly := [([0,0], -112),([0,1], -80),([0,4], -4),([0,5], 4),([0,6], -160),([0,8], -32),([0,9], -80),([1,6], -80),([1,9], -80),([4,5], 8),([5,8], 4),([6,6], -80),([6,9], -80)]
def c2GroupHessian52_03 : Poly := List.flatten [c2GroupHessian52_03Chunk0]
theorem c2GroupHessian52_03_check : sumFast (c2TensorGroup52.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian52_03 := by kernel_rfl
private def c2GroupHessian52_11Chunk0 : Poly := [([0,0], 128),([0,2], 128),([0,8], 128),([2,2], 32),([2,8], 64),([7,7], 80),([8,8], 32)]
def c2GroupHessian52_11 : Poly := List.flatten [c2GroupHessian52_11Chunk0]
theorem c2GroupHessian52_11_check : sumFast (c2TensorGroup52.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian52_11 := by kernel_rfl
private def c2GroupHessian52_12Chunk0 : Poly := [([0,0], -64),([0,2], -32),([0,5], 8),([0,7], -80),([0,8], -32),([2,5], 4),([3,7], -80),([5,8], 4),([7,7], -80),([7,9], -80)]
def c2GroupHessian52_12 : Poly := List.flatten [c2GroupHessian52_12Chunk0]
theorem c2GroupHessian52_12_check : sumFast (c2TensorGroup52.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian52_12 := by kernel_rfl
private def c2GroupHessian52_13Chunk0 : Poly := [([0,0], -64),([0,2], -32),([0,4], -8),([0,7], 80),([0,8], -96),([2,4], -4),([2,8], -32),([4,8], -4),([6,7], 80),([7,9], 80),([8,8], -32)]
def c2GroupHessian52_13 : Poly := List.flatten [c2GroupHessian52_13Chunk0]
theorem c2GroupHessian52_13_check : sumFast (c2TensorGroup52.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian52_13 := by kernel_rfl
private def c2GroupHessian52_22Chunk0 : Poly := [([0,0], 112),([0,3], 160),([0,5], -8),([0,7], 160),([0,9], 160),([3,3], 80),([3,7], 160),([3,9], 160),([5,5], 24),([7,7], 80),([7,9], 160),([9,9], 80)]
def c2GroupHessian52_22 : Poly := List.flatten [c2GroupHessian52_22Chunk0]
theorem c2GroupHessian52_22_check : sumFast (c2TensorGroup52.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian52_22 := by kernel_rfl
private def c2GroupHessian52_23Chunk0 : Poly := [([0,0], -48),([0,3], -80),([0,4], 4),([0,5], -4),([0,6], -80),([0,7], -80),([0,8], 32),([0,9], -160),([3,6], -80),([3,9], -80),([4,5], -8),([5,8], -4),([6,7], -80),([6,9], -80),([7,9], -80),([9,9], -80)]
def c2GroupHessian52_23 : Poly := List.flatten [c2GroupHessian52_23Chunk0]
theorem c2GroupHessian52_23_check : sumFast (c2TensorGroup52.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian52_23 := by kernel_rfl
private def c2GroupHessian52_33Chunk0 : Poly := [([0,0], 112),([0,4], 8),([0,6], 160),([0,8], 64),([0,9], 160),([4,4], 24),([4,8], 8),([6,6], 80),([6,9], 160),([8,8], 32),([9,9], 80)]
def c2GroupHessian52_33 : Poly := List.flatten [c2GroupHessian52_33Chunk0]
theorem c2GroupHessian52_33_check : sumFast (c2TensorGroup52.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian52_33 := by kernel_rfl
end D4.Secondary
