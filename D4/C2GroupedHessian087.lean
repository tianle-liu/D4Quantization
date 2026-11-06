import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup87_det_check : c2TensorGroup87.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 114)) = true := by kernel_rfl
private def c2GroupHessian87_00Chunk0 : Poly := [([0,0], 160),([0,1], 160),([0,5], 160),([0,6], 160),([1,1], 40),([1,5], 80),([1,6], 80),([5,5], 40),([5,6], 80),([6,6], 40)]
def c2GroupHessian87_00 : Poly := List.flatten [c2GroupHessian87_00Chunk0]
theorem c2GroupHessian87_00_check : sumFast (c2TensorGroup87.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian87_00 := by kernel_rfl
private def c2GroupHessian87_01Chunk0 : Poly := [([0,0], 80),([0,1], 40),([0,5], 40),([0,6], 40)]
def c2GroupHessian87_01 : Poly := List.flatten [c2GroupHessian87_01Chunk0]
theorem c2GroupHessian87_01_check : sumFast (c2TensorGroup87.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian87_01 := by kernel_rfl
private def c2GroupHessian87_02Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -120),([0,6], -40),([1,5], -40),([5,5], -40),([5,6], -40)]
def c2GroupHessian87_02 : Poly := List.flatten [c2GroupHessian87_02Chunk0]
theorem c2GroupHessian87_02_check : sumFast (c2TensorGroup87.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian87_02 := by kernel_rfl
private def c2GroupHessian87_03Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -40),([0,6], -120),([1,6], -40),([5,6], -40),([6,6], -40)]
def c2GroupHessian87_03 : Poly := List.flatten [c2GroupHessian87_03Chunk0]
theorem c2GroupHessian87_03_check : sumFast (c2TensorGroup87.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian87_03 := by kernel_rfl
private def c2GroupHessian87_11Chunk0 : Poly := [([0,0], 56),([0,2], 8),([0,7], 32),([0,8], 40),([2,2], 8),([2,7], 8),([7,7], 16),([7,8], 40),([8,8], 40)]
def c2GroupHessian87_11 : Poly := List.flatten [c2GroupHessian87_11Chunk0]
theorem c2GroupHessian87_11_check : sumFast (c2TensorGroup87.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian87_11 := by kernel_rfl
private def c2GroupHessian87_12Chunk0 : Poly := [([0,0], -32),([0,2], 4),([0,3], 4),([0,5], -40),([0,7], -8),([0,8], 20),([0,9], 20),([2,3], 8),([2,7], -4),([3,7], 4),([7,7], -16),([7,8], -20),([7,9], 20),([8,9], 40)]
def c2GroupHessian87_12 : Poly := List.flatten [c2GroupHessian87_12Chunk0]
theorem c2GroupHessian87_12_check : sumFast (c2TensorGroup87.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian87_12 := by kernel_rfl
private def c2GroupHessian87_13Chunk0 : Poly := [([0,0], -60),([0,4], -8),([0,6], -40),([0,7], -20),([0,8], -60),([0,9], -20),([2,4], 4),([4,7], -8),([4,8], -20),([7,8], -20),([7,9], -20),([8,8], -40),([8,9], -40)]
def c2GroupHessian87_13 : Poly := List.flatten [c2GroupHessian87_13Chunk0]
theorem c2GroupHessian87_13_check : sumFast (c2TensorGroup87.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian87_13 := by kernel_rfl
private def c2GroupHessian87_22Chunk0 : Poly := [([0,0], 56),([0,3], 8),([0,5], 80),([0,7], -16),([0,9], 40),([3,3], 8),([3,7], -8),([5,5], 40),([7,7], 16),([7,9], -40),([9,9], 40)]
def c2GroupHessian87_22 : Poly := List.flatten [c2GroupHessian87_22Chunk0]
theorem c2GroupHessian87_22_check : sumFast (c2TensorGroup87.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian87_22 := by kernel_rfl
private def c2GroupHessian87_23Chunk0 : Poly := [([0,0], 20),([0,4], -8),([0,5], 40),([0,6], 40),([0,7], 20),([0,8], -20),([0,9], -60),([3,4], 4),([4,7], 8),([4,9], -20),([5,6], 40),([7,8], 20),([7,9], 20),([8,9], -40),([9,9], -40)]
def c2GroupHessian87_23 : Poly := List.flatten [c2GroupHessian87_23Chunk0]
theorem c2GroupHessian87_23_check : sumFast (c2TensorGroup87.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian87_23 := by kernel_rfl
private def c2GroupHessian87_33Chunk0 : Poly := [([0,0], 80),([0,4], 40),([0,6], 80),([0,8], 80),([0,9], 80),([4,4], 16),([4,8], 40),([4,9], 40),([6,6], 40),([8,8], 40),([8,9], 80),([9,9], 40)]
def c2GroupHessian87_33 : Poly := List.flatten [c2GroupHessian87_33Chunk0]
theorem c2GroupHessian87_33_check : sumFast (c2TensorGroup87.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian87_33 := by kernel_rfl
end D4.Secondary
