import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup210_det_check : c2TensorGroup210.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 268)) = true := by kernel_rfl
private def c2GroupHessian210_00Chunk0 : Poly := [([0,0], 48),([0,1], 8),([0,5], 8),([0,6], 80),([1,1], 16),([1,5], -16),([5,5], 16),([6,6], 40)]
def c2GroupHessian210_00 : Poly := List.flatten [c2GroupHessian210_00Chunk0]
theorem c2GroupHessian210_00_check : sumFast (c2TensorGroup210.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian210_00 := by kernel_rfl
private def c2GroupHessian210_01Chunk0 : Poly := [([0,0], 48),([0,1], 4),([0,5], 4),([0,6], 40),([0,7], 8),([0,8], 40),([1,2], 20),([1,7], 4),([2,5], -20),([5,7], 4),([6,8], 40)]
def c2GroupHessian210_01 : Poly := List.flatten [c2GroupHessian210_01Chunk0]
theorem c2GroupHessian210_01_check : sumFast (c2TensorGroup210.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian210_01 := by kernel_rfl
private def c2GroupHessian210_02Chunk0 : Poly := [([0,0], -8),([0,1], 16),([0,5], -28),([0,7], -8),([0,9], 40),([1,3], 20),([1,5], 8),([1,7], -4),([3,5], -20),([5,5], -16),([5,7], -4),([6,9], 40)]
def c2GroupHessian210_02 : Poly := List.flatten [c2GroupHessian210_02Chunk0]
theorem c2GroupHessian210_02_check : sumFast (c2TensorGroup210.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian210_02 := by kernel_rfl
private def c2GroupHessian210_03Chunk0 : Poly := [([0,0], -80),([0,4], -40),([0,6], -120),([0,8], -40),([0,9], -40),([4,6], -40),([6,6], -40),([6,8], -40),([6,9], -40)]
def c2GroupHessian210_03 : Poly := List.flatten [c2GroupHessian210_03Chunk0]
theorem c2GroupHessian210_03_check : sumFast (c2TensorGroup210.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian210_03 := by kernel_rfl
private def c2GroupHessian210_11Chunk0 : Poly := [([0,0], 48),([0,7], 16),([0,8], 80),([2,2], 40),([7,7], 8),([8,8], 40)]
def c2GroupHessian210_11 : Poly := List.flatten [c2GroupHessian210_11Chunk0]
theorem c2GroupHessian210_11_check : sumFast (c2TensorGroup210.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian210_11 := by kernel_rfl
private def c2GroupHessian210_12Chunk0 : Poly := [([0,0], -8),([0,2], 40),([0,5], -4),([0,7], -16),([0,9], 40),([2,3], 40),([2,5], 20),([5,7], -4),([7,7], -8),([8,9], 40)]
def c2GroupHessian210_12 : Poly := List.flatten [c2GroupHessian210_12Chunk0]
theorem c2GroupHessian210_12_check : sumFast (c2TensorGroup210.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian210_12 := by kernel_rfl
private def c2GroupHessian210_13Chunk0 : Poly := [([0,0], -80),([0,4], -40),([0,6], -40),([0,8], -120),([0,9], -40),([4,8], -40),([6,8], -40),([8,8], -40),([8,9], -40)]
def c2GroupHessian210_13 : Poly := List.flatten [c2GroupHessian210_13Chunk0]
theorem c2GroupHessian210_13_check : sumFast (c2TensorGroup210.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian210_13 := by kernel_rfl
private def c2GroupHessian210_22Chunk0 : Poly := [([0,0], 48),([0,3], 80),([0,5], 48),([0,7], 16),([3,3], 40),([3,5], 40),([5,5], 16),([5,7], 8),([7,7], 8),([9,9], 40)]
def c2GroupHessian210_22 : Poly := List.flatten [c2GroupHessian210_22Chunk0]
theorem c2GroupHessian210_22_check : sumFast (c2TensorGroup210.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian210_22 := by kernel_rfl
private def c2GroupHessian210_23Chunk0 : Poly := [([0,9], -80),([4,9], -40),([6,9], -40),([8,9], -40),([9,9], -40)]
def c2GroupHessian210_23 : Poly := List.flatten [c2GroupHessian210_23Chunk0]
theorem c2GroupHessian210_23_check : sumFast (c2TensorGroup210.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian210_23 := by kernel_rfl
private def c2GroupHessian210_33Chunk0 : Poly := [([0,0], 160),([0,4], 160),([0,6], 160),([0,8], 160),([0,9], 160),([4,4], 40),([4,6], 80),([4,8], 80),([4,9], 80),([6,6], 40),([6,8], 80),([6,9], 80),([8,8], 40),([8,9], 80),([9,9], 40)]
def c2GroupHessian210_33 : Poly := List.flatten [c2GroupHessian210_33Chunk0]
theorem c2GroupHessian210_33_check : sumFast (c2TensorGroup210.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian210_33 := by kernel_rfl
end D4.Secondary
