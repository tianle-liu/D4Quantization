import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup119_det_check : c2TensorGroup119.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 152)) = true := by kernel_rfl
private def c2GroupHessian119_00Chunk0 : Poly := [([0,0], 48),([0,1], 8),([0,5], 80),([0,6], 80),([1,1], 16),([5,5], 40),([5,6], 80),([6,6], 40)]
def c2GroupHessian119_00 : Poly := List.flatten [c2GroupHessian119_00Chunk0]
theorem c2GroupHessian119_00_check : sumFast (c2TensorGroup119.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian119_00 := by kernel_rfl
private def c2GroupHessian119_01Chunk0 : Poly := [([0,0], 12),([0,1], -4),([0,2], -40),([0,7], 8),([0,8], 4),([1,7], 4),([1,8], -8),([2,5], -40),([2,6], -40)]
def c2GroupHessian119_01 : Poly := List.flatten [c2GroupHessian119_01Chunk0]
theorem c2GroupHessian119_01_check : sumFast (c2TensorGroup119.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian119_01 := by kernel_rfl
private def c2GroupHessian119_02Chunk0 : Poly := [([0,0], -48),([0,1], -4),([0,3], -40),([0,5], -80),([0,6], -40),([0,7], -8),([0,9], 4),([1,7], -4),([1,9], -8),([3,5], -40),([3,6], -40),([5,5], -40),([5,6], -40)]
def c2GroupHessian119_02 : Poly := List.flatten [c2GroupHessian119_02Chunk0]
theorem c2GroupHessian119_02_check : sumFast (c2TensorGroup119.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian119_02 := by kernel_rfl
private def c2GroupHessian119_03Chunk0 : Poly := [([0,0], -44),([0,1], 8),([0,4], -40),([0,5], -40),([0,6], -80),([0,8], -4),([0,9], -4),([1,8], 8),([1,9], 8),([4,5], -40),([4,6], -40),([5,6], -40),([6,6], -40)]
def c2GroupHessian119_03 : Poly := List.flatten [c2GroupHessian119_03Chunk0]
theorem c2GroupHessian119_03_check : sumFast (c2TensorGroup119.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian119_03 := by kernel_rfl
private def c2GroupHessian119_11Chunk0 : Poly := [([0,0], 32),([0,7], 24),([0,8], 40),([2,2], 40),([7,7], 8),([7,8], 8),([8,8], 16)]
def c2GroupHessian119_11 : Poly := List.flatten [c2GroupHessian119_11Chunk0]
theorem c2GroupHessian119_11_check : sumFast (c2TensorGroup119.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian119_11 := by kernel_rfl
private def c2GroupHessian119_12Chunk0 : Poly := [([0,0], -12),([0,2], 40),([0,7], -20),([0,8], -4),([0,9], 20),([2,3], 40),([2,5], 40),([7,7], -8),([7,8], -4),([7,9], 4),([8,9], 16)]
def c2GroupHessian119_12 : Poly := List.flatten [c2GroupHessian119_12Chunk0]
theorem c2GroupHessian119_12_check : sumFast (c2TensorGroup119.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian119_12 := by kernel_rfl
private def c2GroupHessian119_13Chunk0 : Poly := [([0,0], -20),([0,2], 40),([0,7], -4),([0,8], -36),([0,9], -20),([2,4], 40),([2,6], 40),([7,8], -4),([7,9], -4),([8,8], -16),([8,9], -16)]
def c2GroupHessian119_13 : Poly := List.flatten [c2GroupHessian119_13Chunk0]
theorem c2GroupHessian119_13_check : sumFast (c2TensorGroup119.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian119_13 := by kernel_rfl
private def c2GroupHessian119_22Chunk0 : Poly := [([0,0], 48),([0,3], 80),([0,5], 80),([0,7], 16),([0,9], -8),([3,3], 40),([3,5], 80),([5,5], 40),([7,7], 8),([7,9], -8),([9,9], 16)]
def c2GroupHessian119_22 : Poly := List.flatten [c2GroupHessian119_22Chunk0]
theorem c2GroupHessian119_22_check : sumFast (c2TensorGroup119.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian119_22 := by kernel_rfl
private def c2GroupHessian119_23Chunk0 : Poly := [([0,0], 44),([0,3], 40),([0,4], 40),([0,5], 40),([0,6], 40),([0,7], 4),([0,8], 4),([0,9], -12),([3,4], 40),([3,6], 40),([4,5], 40),([5,6], 40),([7,8], 4),([7,9], 4),([8,9], -16),([9,9], -16)]
def c2GroupHessian119_23 : Poly := List.flatten [c2GroupHessian119_23Chunk0]
theorem c2GroupHessian119_23_check : sumFast (c2TensorGroup119.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian119_23 := by kernel_rfl
private def c2GroupHessian119_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 80),([0,8], 32),([0,9], 32),([4,4], 40),([4,6], 80),([6,6], 40),([8,8], 16),([8,9], 32),([9,9], 16)]
def c2GroupHessian119_33 : Poly := List.flatten [c2GroupHessian119_33Chunk0]
theorem c2GroupHessian119_33_check : sumFast (c2TensorGroup119.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian119_33 := by kernel_rfl
end D4.Secondary
