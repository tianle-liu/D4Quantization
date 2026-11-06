import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup1_det_check : c2TensorGroup1.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 2)) = true := by kernel_rfl
private def c2GroupHessian1_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 40),([0,6], 32),([1,1], 40),([5,5], 40),([5,6], 40),([6,6], 16)]
def c2GroupHessian1_00 : Poly := List.flatten [c2GroupHessian1_00Chunk0]
theorem c2GroupHessian1_00_check : sumFast (c2TensorGroup1.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian1_00 := by kernel_rfl
private def c2GroupHessian1_01Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,2], 40),([0,5], -20),([0,6], -8),([0,7], -8),([0,8], -8),([1,2], 40),([5,7], -20),([5,8], -20),([6,7], -8),([6,8], -8)]
def c2GroupHessian1_01 : Poly := List.flatten [c2GroupHessian1_01Chunk0]
theorem c2GroupHessian1_01_check : sumFast (c2TensorGroup1.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian1_01 := by kernel_rfl
private def c2GroupHessian1_02Chunk0 : Poly := [([0,3], 40),([0,5], -20),([0,7], 8),([0,9], 4),([1,3], 40),([5,5], -40),([5,6], -20),([5,7], 20),([6,7], 8),([6,9], 4)]
def c2GroupHessian1_02 : Poly := List.flatten [c2GroupHessian1_02Chunk0]
theorem c2GroupHessian1_02_check : sumFast (c2TensorGroup1.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian1_02 := by kernel_rfl
private def c2GroupHessian1_03Chunk0 : Poly := [([0,0], -8),([0,4], 40),([0,6], -24),([0,8], 8),([0,9], -4),([1,4], 40),([5,6], -20),([5,8], 20),([6,6], -16),([6,8], 8),([6,9], -4)]
def c2GroupHessian1_03 : Poly := List.flatten [c2GroupHessian1_03Chunk0]
theorem c2GroupHessian1_03_check : sumFast (c2TensorGroup1.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian1_03 := by kernel_rfl
private def c2GroupHessian1_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 32),([0,8], 32),([2,2], 40),([7,7], 16),([7,8], 32),([8,8], 16)]
def c2GroupHessian1_11 : Poly := List.flatten [c2GroupHessian1_11Chunk0]
theorem c2GroupHessian1_11_check : sumFast (c2TensorGroup1.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian1_11 := by kernel_rfl
private def c2GroupHessian1_12Chunk0 : Poly := [([0,3], 40),([0,5], 20),([0,7], -16),([0,9], 4),([2,3], 40),([5,7], 20),([5,8], 20),([7,7], -16),([7,8], -16),([7,9], 4),([8,9], 4)]
def c2GroupHessian1_12 : Poly := List.flatten [c2GroupHessian1_12Chunk0]
theorem c2GroupHessian1_12_check : sumFast (c2TensorGroup1.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian1_12 := by kernel_rfl
private def c2GroupHessian1_13Chunk0 : Poly := [([0,0], -8),([0,4], 40),([0,6], 8),([0,7], -8),([0,8], -24),([0,9], -4),([2,4], 40),([6,7], 8),([6,8], 8),([7,8], -16),([7,9], -4),([8,8], -16),([8,9], -4)]
def c2GroupHessian1_13 : Poly := List.flatten [c2GroupHessian1_13Chunk0]
theorem c2GroupHessian1_13_check : sumFast (c2TensorGroup1.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian1_13 := by kernel_rfl
private def c2GroupHessian1_22Chunk0 : Poly := [([3,3], 40),([5,5], 40),([5,7], -40),([7,7], 16),([7,9], -8),([9,9], 8)]
def c2GroupHessian1_22 : Poly := List.flatten [c2GroupHessian1_22Chunk0]
theorem c2GroupHessian1_22_check : sumFast (c2TensorGroup1.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian1_22 := by kernel_rfl
private def c2GroupHessian1_23Chunk0 : Poly := [([0,7], 8),([0,9], -8),([3,4], 40),([5,6], 20),([5,8], -20),([6,7], -8),([6,9], -4),([7,8], 16),([7,9], 4),([8,9], -4),([9,9], -8)]
def c2GroupHessian1_23 : Poly := List.flatten [c2GroupHessian1_23Chunk0]
theorem c2GroupHessian1_23_check : sumFast (c2TensorGroup1.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian1_23 := by kernel_rfl
private def c2GroupHessian1_33Chunk0 : Poly := [([0,0], 16),([0,6], 16),([0,8], 16),([0,9], 16),([4,4], 40),([6,6], 16),([6,8], -16),([6,9], 8),([8,8], 16),([8,9], 8),([9,9], 8)]
def c2GroupHessian1_33 : Poly := List.flatten [c2GroupHessian1_33Chunk0]
theorem c2GroupHessian1_33_check : sumFast (c2TensorGroup1.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian1_33 := by kernel_rfl
end D4.Secondary
