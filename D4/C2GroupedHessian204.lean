import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup204_det_check : c2TensorGroup204.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 260)) = true := by kernel_rfl
private def c2GroupHessian204_00Chunk0 : Poly := [([0,0], 48),([0,1], 8),([0,5], 80),([0,6], 16),([1,1], 16),([1,6], 8),([5,5], 40),([6,6], 8)]
def c2GroupHessian204_00 : Poly := List.flatten [c2GroupHessian204_00Chunk0]
theorem c2GroupHessian204_00_check : sumFast (c2TensorGroup204.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian204_00 := by kernel_rfl
private def c2GroupHessian204_01Chunk0 : Poly := [([0,0], 44),([0,1], -8),([0,2], 4),([0,5], 40),([0,6], 4),([0,7], 40),([1,2], -8),([1,8], -20),([2,6], 4),([5,7], 40)]
def c2GroupHessian204_01 : Poly := List.flatten [c2GroupHessian204_01Chunk0]
theorem c2GroupHessian204_01_check : sumFast (c2TensorGroup204.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian204_01 := by kernel_rfl
private def c2GroupHessian204_02Chunk0 : Poly := [([0,0], -80),([0,3], -40),([0,5], -120),([0,7], -40),([0,9], -40),([3,5], -40),([5,5], -40),([5,7], -40),([5,9], -40)]
def c2GroupHessian204_02 : Poly := List.flatten [c2GroupHessian204_02Chunk0]
theorem c2GroupHessian204_02_check : sumFast (c2TensorGroup204.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian204_02 := by kernel_rfl
private def c2GroupHessian204_03Chunk0 : Poly := [([0,0], -4),([0,1], 12),([0,4], 4),([0,6], -12),([0,9], 40),([1,4], 16),([1,6], -4),([1,8], 20),([4,6], 4),([5,9], 40),([6,6], -8)]
def c2GroupHessian204_03 : Poly := List.flatten [c2GroupHessian204_03Chunk0]
theorem c2GroupHessian204_03_check : sumFast (c2TensorGroup204.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian204_03 := by kernel_rfl
private def c2GroupHessian204_11Chunk0 : Poly := [([0,0], 56),([0,2], 32),([0,7], 80),([0,8], 40),([2,2], 16),([2,8], 40),([7,7], 40),([8,8], 40)]
def c2GroupHessian204_11 : Poly := List.flatten [c2GroupHessian204_11Chunk0]
theorem c2GroupHessian204_11_check : sumFast (c2TensorGroup204.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian204_11 := by kernel_rfl
private def c2GroupHessian204_12Chunk0 : Poly := [([0,0], -80),([0,3], -40),([0,5], -40),([0,7], -120),([0,9], -40),([3,7], -40),([5,7], -40),([7,7], -40),([7,9], -40)]
def c2GroupHessian204_12 : Poly := List.flatten [c2GroupHessian204_12Chunk0]
theorem c2GroupHessian204_12_check : sumFast (c2TensorGroup204.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian204_12 := by kernel_rfl
private def c2GroupHessian204_13Chunk0 : Poly := [([0,0], -12),([0,2], -12),([0,4], -8),([0,6], -4),([0,8], -40),([0,9], 40),([2,4], -8),([2,6], -4),([2,8], -20),([4,8], -20),([7,9], 40),([8,8], -40)]
def c2GroupHessian204_13 : Poly := List.flatten [c2GroupHessian204_13Chunk0]
theorem c2GroupHessian204_13_check : sumFast (c2TensorGroup204.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian204_13 := by kernel_rfl
private def c2GroupHessian204_22Chunk0 : Poly := [([0,0], 160),([0,3], 160),([0,5], 160),([0,7], 160),([0,9], 160),([3,3], 40),([3,5], 80),([3,7], 80),([3,9], 80),([5,5], 40),([5,7], 80),([5,9], 80),([7,7], 40),([7,9], 80),([9,9], 40)]
def c2GroupHessian204_22 : Poly := List.flatten [c2GroupHessian204_22Chunk0]
theorem c2GroupHessian204_22_check : sumFast (c2TensorGroup204.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian204_22 := by kernel_rfl
private def c2GroupHessian204_23Chunk0 : Poly := [([0,9], -80),([3,9], -40),([5,9], -40),([7,9], -40),([9,9], -40)]
def c2GroupHessian204_23 : Poly := List.flatten [c2GroupHessian204_23Chunk0]
theorem c2GroupHessian204_23_check : sumFast (c2TensorGroup204.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian204_23 := by kernel_rfl
private def c2GroupHessian204_33Chunk0 : Poly := [([0,0], 16),([0,4], 24),([0,6], 8),([0,8], 40),([4,4], 16),([4,6], -8),([4,8], 40),([6,6], 8),([8,8], 40),([9,9], 40)]
def c2GroupHessian204_33 : Poly := List.flatten [c2GroupHessian204_33Chunk0]
theorem c2GroupHessian204_33_check : sumFast (c2TensorGroup204.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian204_33 := by kernel_rfl
end D4.Secondary
