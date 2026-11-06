import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup69_det_check : c2TensorGroup69.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 92)) = true := by kernel_rfl
private def c2GroupHessian69_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 80),([0,6], 40),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 40)]
def c2GroupHessian69_00 : Poly := List.flatten [c2GroupHessian69_00Chunk0]
theorem c2GroupHessian69_00_check : sumFast (c2TensorGroup69.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian69_00 := by kernel_rfl
private def c2GroupHessian69_01Chunk0 : Poly := [([0,0], 8),([0,2], -8),([0,7], 4),([0,8], -40),([1,8], -40),([2,6], -20),([5,8], -40)]
def c2GroupHessian69_01 : Poly := List.flatten [c2GroupHessian69_01Chunk0]
theorem c2GroupHessian69_01_check : sumFast (c2TensorGroup69.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian69_01 := by kernel_rfl
private def c2GroupHessian69_02Chunk0 : Poly := [([0,0], -56),([0,1], -40),([0,3], -8),([0,5], -80),([0,6], -20),([0,7], -4),([0,9], -40),([1,5], -40),([1,9], -40),([3,6], -20),([5,5], -40),([5,9], -40)]
def c2GroupHessian69_02 : Poly := List.flatten [c2GroupHessian69_02Chunk0]
theorem c2GroupHessian69_02_check : sumFast (c2TensorGroup69.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian69_02 := by kernel_rfl
private def c2GroupHessian69_03Chunk0 : Poly := [([0,0], 24),([0,1], 40),([0,4], 40),([0,5], 40),([0,6], -40),([0,8], 40),([0,9], 40),([1,4], 40),([1,8], 40),([1,9], 40),([4,5], 40),([5,8], 40),([5,9], 40),([6,6], -40)]
def c2GroupHessian69_03 : Poly := List.flatten [c2GroupHessian69_03Chunk0]
theorem c2GroupHessian69_03_check : sumFast (c2TensorGroup69.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian69_03 := by kernel_rfl
private def c2GroupHessian69_11Chunk0 : Poly := [([0,0], 16),([0,2], 16),([0,7], 16),([2,2], 16),([2,7], 8),([7,7], 8),([8,8], 40)]
def c2GroupHessian69_11 : Poly := List.flatten [c2GroupHessian69_11Chunk0]
theorem c2GroupHessian69_11_check : sumFast (c2TensorGroup69.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian69_11 := by kernel_rfl
private def c2GroupHessian69_12Chunk0 : Poly := [([0,0], -8),([0,2], 8),([0,3], 8),([0,7], -12),([0,8], 40),([2,3], 16),([2,7], -4),([3,7], 4),([5,8], 40),([7,7], -8),([8,9], 40)]
def c2GroupHessian69_12 : Poly := List.flatten [c2GroupHessian69_12Chunk0]
theorem c2GroupHessian69_12_check : sumFast (c2TensorGroup69.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian69_12 := by kernel_rfl
private def c2GroupHessian69_13Chunk0 : Poly := [([0,0], -8),([0,2], 8),([0,7], -4),([0,8], -40),([2,6], 20),([4,8], -40),([8,8], -40),([8,9], -40)]
def c2GroupHessian69_13 : Poly := List.flatten [c2GroupHessian69_13Chunk0]
theorem c2GroupHessian69_13_check : sumFast (c2TensorGroup69.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian69_13 := by kernel_rfl
private def c2GroupHessian69_22Chunk0 : Poly := [([0,0], 56),([0,3], 16),([0,5], 80),([0,7], 8),([0,9], 80),([3,3], 16),([3,7], -8),([5,5], 40),([5,9], 80),([7,7], 8),([9,9], 40)]
def c2GroupHessian69_22 : Poly := List.flatten [c2GroupHessian69_22Chunk0]
theorem c2GroupHessian69_22_check : sumFast (c2TensorGroup69.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian69_22 := by kernel_rfl
private def c2GroupHessian69_23Chunk0 : Poly := [([0,0], -24),([0,3], 8),([0,4], -40),([0,5], -40),([0,6], 20),([0,7], 4),([0,8], -40),([0,9], -80),([3,6], 20),([4,5], -40),([4,9], -40),([5,8], -40),([5,9], -40),([8,9], -40),([9,9], -40)]
def c2GroupHessian69_23 : Poly := List.flatten [c2GroupHessian69_23Chunk0]
theorem c2GroupHessian69_23_check : sumFast (c2TensorGroup69.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian69_23 := by kernel_rfl
private def c2GroupHessian69_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 40),([0,8], 80),([0,9], 80),([4,4], 40),([4,8], 80),([4,9], 80),([6,6], 40),([8,8], 40),([8,9], 80),([9,9], 40)]
def c2GroupHessian69_33 : Poly := List.flatten [c2GroupHessian69_33Chunk0]
theorem c2GroupHessian69_33_check : sumFast (c2TensorGroup69.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian69_33 := by kernel_rfl
end D4.Secondary
