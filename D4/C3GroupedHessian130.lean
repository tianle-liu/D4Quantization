import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup130_det_check : c3TensorGroup130.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 170)) = true := by kernel_rfl
private def c3GroupHessian130_00Chunk0 : Poly := [([0,0], 16),([0,1], 16),([0,6], 16),([0,9], 16),([1,1], 16),([1,6], 32),([1,9], 8),([5,5], 40),([6,6], 16),([6,9], 8),([9,9], 8)]
def c3GroupHessian130_00 : Poly := List.flatten [c3GroupHessian130_00Chunk0]
theorem c3GroupHessian130_00_check : sumFast (c3TensorGroup130.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian130_00 := by kernel_rfl
private def c3GroupHessian130_01Chunk0 : Poly := [([0,0], 8),([0,1], -8),([0,5], -40),([0,6], -8),([0,9], 12),([1,7], -20),([1,9], 4),([2,5], -40),([5,8], -40),([6,7], -20),([6,9], 4),([9,9], 8)]
def c3GroupHessian130_01 : Poly := List.flatten [c3GroupHessian130_01Chunk0]
theorem c3GroupHessian130_01_check : sumFast (c3TensorGroup130.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian130_01 := by kernel_rfl
private def c3GroupHessian130_02Chunk0 : Poly := [([0,0], -8),([0,1], 8),([0,5], -40),([0,6], 8),([0,9], -12),([1,7], 20),([1,9], -4),([3,5], -40),([5,5], -40),([6,7], 20),([6,9], -4),([9,9], -8)]
def c3GroupHessian130_02 : Poly := List.flatten [c3GroupHessian130_02Chunk0]
theorem c3GroupHessian130_02_check : sumFast (c3TensorGroup130.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian130_02 := by kernel_rfl
private def c3GroupHessian130_03Chunk0 : Poly := [([0,0], -8),([0,1], -16),([0,5], 40),([0,6], -24),([0,9], -12),([1,4], -20),([1,6], -16),([1,9], -4),([4,6], -20),([5,8], 40),([6,6], -16),([6,9], -8),([9,9], -8)]
def c3GroupHessian130_03 : Poly := List.flatten [c3GroupHessian130_03Chunk0]
theorem c3GroupHessian130_03_check : sumFast (c3TensorGroup130.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian130_03 := by kernel_rfl
private def c3GroupHessian130_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 40),([0,8], 80),([0,9], 8),([2,2], 40),([2,8], 80),([7,7], 40),([8,8], 40),([9,9], 8)]
def c3GroupHessian130_11 : Poly := List.flatten [c3GroupHessian130_11Chunk0]
theorem c3GroupHessian130_11_check : sumFast (c3TensorGroup130.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian130_11 := by kernel_rfl
private def c3GroupHessian130_12Chunk0 : Poly := [([0,0], 24),([0,2], 40),([0,3], 40),([0,5], 40),([0,7], -40),([0,8], 40),([0,9], -8),([2,3], 40),([2,5], 40),([3,8], 40),([5,8], 40),([7,7], -40),([9,9], -8)]
def c3GroupHessian130_12 : Poly := List.flatten [c3GroupHessian130_12Chunk0]
theorem c3GroupHessian130_12_check : sumFast (c3TensorGroup130.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian130_12 := by kernel_rfl
private def c3GroupHessian130_13Chunk0 : Poly := [([0,0], -32),([0,2], -40),([0,4], 20),([0,6], 8),([0,7], 20),([0,8], -80),([0,9], -8),([2,8], -40),([4,7], 40),([6,7], 20),([6,9], -4),([8,8], -40),([9,9], -8)]
def c3GroupHessian130_13 : Poly := List.flatten [c3GroupHessian130_13Chunk0]
theorem c3GroupHessian130_13_check : sumFast (c3TensorGroup130.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian130_13 := by kernel_rfl
private def c3GroupHessian130_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 80),([0,7], 40),([0,9], 8),([3,3], 40),([3,5], 80),([5,5], 40),([7,7], 40),([9,9], 8)]
def c3GroupHessian130_22 : Poly := List.flatten [c3GroupHessian130_22Chunk0]
theorem c3GroupHessian130_22_check : sumFast (c3TensorGroup130.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian130_22 := by kernel_rfl
private def c3GroupHessian130_23Chunk0 : Poly := [([0,0], -48),([0,3], -40),([0,4], -20),([0,5], -40),([0,6], -8),([0,7], -20),([0,8], -40),([0,9], 8),([3,8], -40),([4,7], -40),([5,8], -40),([6,7], -20),([6,9], 4),([9,9], 8)]
def c3GroupHessian130_23 : Poly := List.flatten [c3GroupHessian130_23Chunk0]
theorem c3GroupHessian130_23_check : sumFast (c3TensorGroup130.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian130_23 := by kernel_rfl
private def c3GroupHessian130_33Chunk0 : Poly := [([0,0], 56),([0,4], 40),([0,6], 32),([0,8], 80),([0,9], 8),([4,4], 40),([4,6], 40),([6,6], 16),([6,9], 8),([8,8], 40),([9,9], 8)]
def c3GroupHessian130_33 : Poly := List.flatten [c3GroupHessian130_33Chunk0]
theorem c3GroupHessian130_33_check : sumFast (c3TensorGroup130.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian130_33 := by kernel_rfl
end D4.Secondary
