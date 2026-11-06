import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup188_det_check : c2TensorGroup188.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 240)) = true := by kernel_rfl
private def c2GroupHessian188_00Chunk0 : Poly := [([0,0], 56),([0,1], 40),([0,5], 80),([0,6], 32),([1,1], 40),([1,6], 40),([5,5], 40),([6,6], 16)]
def c2GroupHessian188_00 : Poly := List.flatten [c2GroupHessian188_00Chunk0]
theorem c2GroupHessian188_00_check : sumFast (c2TensorGroup188.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian188_00 := by kernel_rfl
private def c2GroupHessian188_01Chunk0 : Poly := [([0,0], 44),([0,2], 4),([0,5], 40),([0,6], 4),([0,7], 40),([0,8], -8),([1,8], -20),([2,6], 4),([5,7], 40),([6,8], -8)]
def c2GroupHessian188_01 : Poly := List.flatten [c2GroupHessian188_01Chunk0]
theorem c2GroupHessian188_01_check : sumFast (c2TensorGroup188.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian188_01 := by kernel_rfl
private def c2GroupHessian188_02Chunk0 : Poly := [([0,0], -80),([0,3], -40),([0,5], -120),([0,7], -40),([0,9], -40),([3,5], -40),([5,5], -40),([5,7], -40),([5,9], -40)]
def c2GroupHessian188_02 : Poly := List.flatten [c2GroupHessian188_02Chunk0]
theorem c2GroupHessian188_02_check : sumFast (c2TensorGroup188.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian188_02 := by kernel_rfl
private def c2GroupHessian188_03Chunk0 : Poly := [([0,0], 4),([0,1], 20),([0,4], 20),([0,6], -12),([0,8], 8),([0,9], 40),([1,4], 40),([1,6], -20),([1,8], 20),([4,6], 20),([5,9], 40),([6,6], -16),([6,8], 8)]
def c2GroupHessian188_03 : Poly := List.flatten [c2GroupHessian188_03Chunk0]
theorem c2GroupHessian188_03_check : sumFast (c2TensorGroup188.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian188_03 := by kernel_rfl
private def c2GroupHessian188_11Chunk0 : Poly := [([0,0], 48),([0,2], 16),([0,7], 80),([0,8], 8),([2,2], 8),([2,8], 8),([7,7], 40),([8,8], 16)]
def c2GroupHessian188_11 : Poly := List.flatten [c2GroupHessian188_11Chunk0]
theorem c2GroupHessian188_11_check : sumFast (c2TensorGroup188.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian188_11 := by kernel_rfl
private def c2GroupHessian188_12Chunk0 : Poly := [([0,0], -80),([0,3], -40),([0,5], -40),([0,7], -120),([0,9], -40),([3,7], -40),([5,7], -40),([7,7], -40),([7,9], -40)]
def c2GroupHessian188_12 : Poly := List.flatten [c2GroupHessian188_12Chunk0]
theorem c2GroupHessian188_12_check : sumFast (c2TensorGroup188.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian188_12 := by kernel_rfl
private def c2GroupHessian188_13Chunk0 : Poly := [([0,0], -4),([0,2], -4),([0,6], -4),([0,8], -16),([0,9], 40),([2,6], -4),([2,8], -4),([4,8], -20),([6,8], 8),([7,9], 40),([8,8], -16)]
def c2GroupHessian188_13 : Poly := List.flatten [c2GroupHessian188_13Chunk0]
theorem c2GroupHessian188_13_check : sumFast (c2TensorGroup188.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian188_13 := by kernel_rfl
private def c2GroupHessian188_22Chunk0 : Poly := [([0,0], 160),([0,3], 160),([0,5], 160),([0,7], 160),([0,9], 160),([3,3], 40),([3,5], 80),([3,7], 80),([3,9], 80),([5,5], 40),([5,7], 80),([5,9], 80),([7,7], 40),([7,9], 80),([9,9], 40)]
def c2GroupHessian188_22 : Poly := List.flatten [c2GroupHessian188_22Chunk0]
theorem c2GroupHessian188_22_check : sumFast (c2TensorGroup188.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian188_22 := by kernel_rfl
private def c2GroupHessian188_23Chunk0 : Poly := [([0,9], -80),([3,9], -40),([5,9], -40),([7,9], -40),([9,9], -40)]
def c2GroupHessian188_23 : Poly := List.flatten [c2GroupHessian188_23Chunk0]
theorem c2GroupHessian188_23_check : sumFast (c2TensorGroup188.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian188_23 := by kernel_rfl
private def c2GroupHessian188_33Chunk0 : Poly := [([0,0], 16),([0,4], 40),([0,6], -8),([0,8], 24),([4,4], 40),([4,6], -40),([4,8], 40),([6,6], 16),([6,8], -16),([8,8], 16),([9,9], 40)]
def c2GroupHessian188_33 : Poly := List.flatten [c2GroupHessian188_33Chunk0]
theorem c2GroupHessian188_33_check : sumFast (c2TensorGroup188.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian188_33 := by kernel_rfl
end D4.Secondary
