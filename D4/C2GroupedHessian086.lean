import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup86_det_check : c2TensorGroup86.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 113)) = true := by kernel_rfl
private def c2GroupHessian86_00Chunk0 : Poly := [([0,0], 160),([0,1], 160),([0,5], 160),([0,6], 160),([1,1], 40),([1,5], 80),([1,6], 80),([5,5], 40),([5,6], 80),([6,6], 40)]
def c2GroupHessian86_00 : Poly := List.flatten [c2GroupHessian86_00Chunk0]
theorem c2GroupHessian86_00_check : sumFast (c2TensorGroup86.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian86_00 := by kernel_rfl
private def c2GroupHessian86_01Chunk0 : Poly := [([0,0], 80),([0,1], 40),([0,5], 40),([0,6], 40)]
def c2GroupHessian86_01 : Poly := List.flatten [c2GroupHessian86_01Chunk0]
theorem c2GroupHessian86_01_check : sumFast (c2TensorGroup86.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian86_01 := by kernel_rfl
private def c2GroupHessian86_02Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -120),([0,6], -40),([1,5], -40),([5,5], -40),([5,6], -40)]
def c2GroupHessian86_02 : Poly := List.flatten [c2GroupHessian86_02Chunk0]
theorem c2GroupHessian86_02_check : sumFast (c2TensorGroup86.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian86_02 := by kernel_rfl
private def c2GroupHessian86_03Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -40),([0,6], -120),([1,6], -40),([5,6], -40),([6,6], -40)]
def c2GroupHessian86_03 : Poly := List.flatten [c2GroupHessian86_03Chunk0]
theorem c2GroupHessian86_03_check : sumFast (c2TensorGroup86.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian86_03 := by kernel_rfl
private def c2GroupHessian86_11Chunk0 : Poly := [([0,0], 48),([0,2], 16),([0,7], 16),([2,2], 8),([2,7], 16),([7,7], 8),([8,8], 40)]
def c2GroupHessian86_11 : Poly := List.flatten [c2GroupHessian86_11Chunk0]
theorem c2GroupHessian86_11_check : sumFast (c2TensorGroup86.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian86_11 := by kernel_rfl
private def c2GroupHessian86_12Chunk0 : Poly := [([0,0], -40),([0,3], 4),([0,5], -40),([0,7], -8),([0,8], 40),([2,3], 4),([2,7], -8),([3,7], 4),([3,8], 20),([7,7], -8),([8,9], 40)]
def c2GroupHessian86_12 : Poly := List.flatten [c2GroupHessian86_12Chunk0]
theorem c2GroupHessian86_12_check : sumFast (c2TensorGroup86.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian86_12 := by kernel_rfl
private def c2GroupHessian86_13Chunk0 : Poly := [([0,0], -40),([0,4], 4),([0,6], -40),([0,8], -40),([2,4], 4),([4,7], 4),([4,8], -20),([8,8], -40),([8,9], -40)]
def c2GroupHessian86_13 : Poly := List.flatten [c2GroupHessian86_13Chunk0]
theorem c2GroupHessian86_13_check : sumFast (c2TensorGroup86.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian86_13 := by kernel_rfl
private def c2GroupHessian86_22Chunk0 : Poly := [([0,0], 80),([0,3], 40),([0,5], 80),([0,9], 80),([3,3], 16),([3,7], -8),([3,9], 40),([5,5], 40),([7,7], 8),([9,9], 40)]
def c2GroupHessian86_22 : Poly := List.flatten [c2GroupHessian86_22Chunk0]
theorem c2GroupHessian86_22_check : sumFast (c2TensorGroup86.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian86_22 := by kernel_rfl
private def c2GroupHessian86_23Chunk0 : Poly := [([0,3], -20),([0,4], -20),([0,5], 40),([0,6], 40),([0,8], -40),([0,9], -80),([3,4], -8),([3,8], -20),([3,9], -20),([4,7], -4),([4,9], -20),([5,6], 40),([8,9], -40),([9,9], -40)]
def c2GroupHessian86_23 : Poly := List.flatten [c2GroupHessian86_23Chunk0]
theorem c2GroupHessian86_23_check : sumFast (c2TensorGroup86.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian86_23 := by kernel_rfl
private def c2GroupHessian86_33Chunk0 : Poly := [([0,0], 80),([0,4], 40),([0,6], 80),([0,8], 80),([0,9], 80),([4,4], 16),([4,8], 40),([4,9], 40),([6,6], 40),([8,8], 40),([8,9], 80),([9,9], 40)]
def c2GroupHessian86_33 : Poly := List.flatten [c2GroupHessian86_33Chunk0]
theorem c2GroupHessian86_33_check : sumFast (c2TensorGroup86.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian86_33 := by kernel_rfl
end D4.Secondary
