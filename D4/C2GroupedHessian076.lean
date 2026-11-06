import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup76_det_check : c2TensorGroup76.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 102)) = true := by kernel_rfl
private def c2GroupHessian76_00Chunk0 : Poly := [([0,0], 160),([0,1], 160),([0,5], 160),([0,6], 160),([1,1], 40),([1,5], 80),([1,6], 80),([5,5], 40),([5,6], 80),([6,6], 40)]
def c2GroupHessian76_00 : Poly := List.flatten [c2GroupHessian76_00Chunk0]
theorem c2GroupHessian76_00_check : sumFast (c2TensorGroup76.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian76_00 := by kernel_rfl
private def c2GroupHessian76_01Chunk0 : Poly := [([0,0], 80),([0,1], 40),([0,5], 40),([0,6], 40)]
def c2GroupHessian76_01 : Poly := List.flatten [c2GroupHessian76_01Chunk0]
theorem c2GroupHessian76_01_check : sumFast (c2TensorGroup76.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian76_01 := by kernel_rfl
private def c2GroupHessian76_02Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -120),([0,6], -40),([1,5], -40),([5,5], -40),([5,6], -40)]
def c2GroupHessian76_02 : Poly := List.flatten [c2GroupHessian76_02Chunk0]
theorem c2GroupHessian76_02_check : sumFast (c2TensorGroup76.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian76_02 := by kernel_rfl
private def c2GroupHessian76_03Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -40),([0,6], -120),([1,6], -40),([5,6], -40),([6,6], -40)]
def c2GroupHessian76_03 : Poly := List.flatten [c2GroupHessian76_03Chunk0]
theorem c2GroupHessian76_03_check : sumFast (c2TensorGroup76.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian76_03 := by kernel_rfl
private def c2GroupHessian76_11Chunk0 : Poly := [([0,0], 48),([0,2], 16),([0,7], 8),([0,8], 8),([2,2], 8),([2,7], 8),([2,8], 8),([7,7], 16),([7,8], -16),([8,8], 16)]
def c2GroupHessian76_11 : Poly := List.flatten [c2GroupHessian76_11Chunk0]
theorem c2GroupHessian76_11_check : sumFast (c2TensorGroup76.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian76_11 := by kernel_rfl
private def c2GroupHessian76_12Chunk0 : Poly := [([0,0], -40),([0,5], -40),([0,7], -24),([0,8], 20),([2,7], -4),([3,7], -20),([3,8], 20),([7,7], -16),([7,8], 8),([7,9], -20),([8,9], 20)]
def c2GroupHessian76_12 : Poly := List.flatten [c2GroupHessian76_12Chunk0]
theorem c2GroupHessian76_12_check : sumFast (c2TensorGroup76.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian76_12 := by kernel_rfl
private def c2GroupHessian76_13Chunk0 : Poly := [([0,0], -40),([0,4], 8),([0,6], -40),([0,7], 20),([0,8], -24),([2,4], 8),([2,8], -4),([4,7], 4),([4,8], 4),([7,8], 8),([7,9], 20),([8,8], -16),([8,9], -20)]
def c2GroupHessian76_13 : Poly := List.flatten [c2GroupHessian76_13Chunk0]
theorem c2GroupHessian76_13_check : sumFast (c2TensorGroup76.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian76_13 := by kernel_rfl
private def c2GroupHessian76_22Chunk0 : Poly := [([0,0], 80),([0,3], 80),([0,5], 80),([0,7], 40),([0,9], 80),([3,3], 40),([3,7], 40),([3,9], 80),([5,5], 40),([7,7], 16),([7,9], 40),([9,9], 40)]
def c2GroupHessian76_22 : Poly := List.flatten [c2GroupHessian76_22Chunk0]
theorem c2GroupHessian76_22_check : sumFast (c2TensorGroup76.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian76_22 := by kernel_rfl
private def c2GroupHessian76_23Chunk0 : Poly := [([0,3], -40),([0,5], 40),([0,6], 40),([0,7], -20),([0,8], -20),([0,9], -80),([3,8], -20),([3,9], -40),([4,7], -4),([5,6], 40),([7,8], -8),([7,9], -20),([8,9], -20),([9,9], -40)]
def c2GroupHessian76_23 : Poly := List.flatten [c2GroupHessian76_23Chunk0]
theorem c2GroupHessian76_23_check : sumFast (c2TensorGroup76.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian76_23 := by kernel_rfl
private def c2GroupHessian76_33Chunk0 : Poly := [([0,0], 80),([0,6], 80),([0,8], 40),([0,9], 80),([4,4], 8),([4,8], -8),([6,6], 40),([8,8], 16),([8,9], 40),([9,9], 40)]
def c2GroupHessian76_33 : Poly := List.flatten [c2GroupHessian76_33Chunk0]
theorem c2GroupHessian76_33_check : sumFast (c2TensorGroup76.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian76_33 := by kernel_rfl
end D4.Secondary
