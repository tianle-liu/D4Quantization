import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup206_det_check : c2TensorGroup206.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 262)) = true := by kernel_rfl
private def c2GroupHessian206_00Chunk0 : Poly := [([0,0], 112),([0,1], 64),([0,5], 160),([0,6], -8),([1,1], 32),([1,6], -8),([5,5], 80),([6,6], 24)]
def c2GroupHessian206_00 : Poly := List.flatten [c2GroupHessian206_00Chunk0]
theorem c2GroupHessian206_00_check : sumFast (c2TensorGroup206.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian206_00 := by kernel_rfl
private def c2GroupHessian206_01Chunk0 : Poly := [([0,0], 112),([0,1], 32),([0,2], 32),([0,5], 80),([0,6], -4),([0,7], 80),([0,8], -4),([1,2], 32),([1,8], -4),([2,6], -4),([5,7], 80),([6,8], 8)]
def c2GroupHessian206_01 : Poly := List.flatten [c2GroupHessian206_01Chunk0]
theorem c2GroupHessian206_01_check : sumFast (c2TensorGroup206.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian206_01 := by kernel_rfl
private def c2GroupHessian206_02Chunk0 : Poly := [([0,0], -160),([0,3], -80),([0,5], -240),([0,7], -80),([0,9], -80),([3,5], -80),([5,5], -80),([5,7], -80),([5,9], -80)]
def c2GroupHessian206_02 : Poly := List.flatten [c2GroupHessian206_02Chunk0]
theorem c2GroupHessian206_02_check : sumFast (c2TensorGroup206.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian206_02 := by kernel_rfl
private def c2GroupHessian206_03Chunk0 : Poly := [([0,4], 32),([0,6], 4),([0,8], 4),([0,9], 80),([1,4], 32),([1,6], 4),([1,8], 4),([4,6], -4),([5,9], 80),([6,6], -24),([6,8], -8)]
def c2GroupHessian206_03 : Poly := List.flatten [c2GroupHessian206_03Chunk0]
theorem c2GroupHessian206_03_check : sumFast (c2TensorGroup206.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian206_03 := by kernel_rfl
private def c2GroupHessian206_11Chunk0 : Poly := [([0,0], 112),([0,2], 64),([0,7], 160),([0,8], -8),([2,2], 32),([2,8], -8),([7,7], 80),([8,8], 24)]
def c2GroupHessian206_11 : Poly := List.flatten [c2GroupHessian206_11Chunk0]
theorem c2GroupHessian206_11_check : sumFast (c2TensorGroup206.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian206_11 := by kernel_rfl
private def c2GroupHessian206_12Chunk0 : Poly := [([0,0], -160),([0,3], -80),([0,5], -80),([0,7], -240),([0,9], -80),([3,7], -80),([5,7], -80),([7,7], -80),([7,9], -80)]
def c2GroupHessian206_12 : Poly := List.flatten [c2GroupHessian206_12Chunk0]
theorem c2GroupHessian206_12_check : sumFast (c2TensorGroup206.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian206_12 := by kernel_rfl
private def c2GroupHessian206_13Chunk0 : Poly := [([0,4], 32),([0,6], 4),([0,8], 4),([0,9], 80),([2,4], 32),([2,6], 4),([2,8], 4),([4,8], -4),([6,8], -8),([7,9], 80),([8,8], -24)]
def c2GroupHessian206_13 : Poly := List.flatten [c2GroupHessian206_13Chunk0]
theorem c2GroupHessian206_13_check : sumFast (c2TensorGroup206.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian206_13 := by kernel_rfl
private def c2GroupHessian206_22Chunk0 : Poly := [([0,0], 320),([0,3], 320),([0,5], 320),([0,7], 320),([0,9], 320),([3,3], 80),([3,5], 160),([3,7], 160),([3,9], 160),([5,5], 80),([5,7], 160),([5,9], 160),([7,7], 80),([7,9], 160),([9,9], 80)]
def c2GroupHessian206_22 : Poly := List.flatten [c2GroupHessian206_22Chunk0]
theorem c2GroupHessian206_22_check : sumFast (c2TensorGroup206.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian206_22 := by kernel_rfl
private def c2GroupHessian206_23Chunk0 : Poly := [([0,9], -160),([3,9], -80),([5,9], -80),([7,9], -80),([9,9], -80)]
def c2GroupHessian206_23 : Poly := List.flatten [c2GroupHessian206_23Chunk0]
theorem c2GroupHessian206_23_check : sumFast (c2TensorGroup206.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian206_23 := by kernel_rfl
private def c2GroupHessian206_33Chunk0 : Poly := [([4,4], 32),([4,6], 8),([4,8], 8),([6,6], 24),([6,8], 16),([8,8], 24),([9,9], 80)]
def c2GroupHessian206_33 : Poly := List.flatten [c2GroupHessian206_33Chunk0]
theorem c2GroupHessian206_33_check : sumFast (c2TensorGroup206.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian206_33 := by kernel_rfl
end D4.Secondary
