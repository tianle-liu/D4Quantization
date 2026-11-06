import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup71_det_check : c3TensorGroup71.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 96)) = true := by kernel_rfl
private def c3GroupHessian71_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 80),([0,6], 32),([0,9], 40),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 16),([6,9], 40),([9,9], 40)]
def c3GroupHessian71_00 : Poly := List.flatten [c3GroupHessian71_00Chunk0]
theorem c3GroupHessian71_00_check : sumFast (c3TensorGroup71.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian71_00 := by kernel_rfl
private def c3GroupHessian71_01Chunk0 : Poly := [([0,0], 24),([0,2], 4),([0,6], 24),([0,7], 20),([0,8], -40),([0,9], 60),([1,8], -40),([2,6], 4),([5,8], -40),([6,7], 20),([6,9], 20),([7,9], 40),([9,9], 40)]
def c3GroupHessian71_01 : Poly := List.flatten [c3GroupHessian71_01Chunk0]
theorem c3GroupHessian71_01_check : sumFast (c3TensorGroup71.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian71_01 := by kernel_rfl
private def c3GroupHessian71_02Chunk0 : Poly := [([0,0], -60),([0,1], -40),([0,3], -8),([0,5], -80),([0,6], -20),([0,7], -20),([0,9], -60),([1,5], -40),([3,6], -8),([3,9], -20),([5,5], -40),([6,7], -20),([6,9], -20),([7,9], -40),([9,9], -40)]
def c3GroupHessian71_02 : Poly := List.flatten [c3GroupHessian71_02Chunk0]
theorem c3GroupHessian71_02_check : sumFast (c3TensorGroup71.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian71_02 := by kernel_rfl
private def c3GroupHessian71_03Chunk0 : Poly := [([0,0], 24),([0,1], 40),([0,4], 40),([0,5], 40),([0,6], -32),([0,8], 40),([0,9], -40),([1,4], 40),([1,8], 40),([4,5], 40),([5,8], 40),([6,6], -16),([6,9], -40),([9,9], -40)]
def c3GroupHessian71_03 : Poly := List.flatten [c3GroupHessian71_03Chunk0]
theorem c3GroupHessian71_03_check : sumFast (c3TensorGroup71.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian71_03 := by kernel_rfl
private def c3GroupHessian71_11Chunk0 : Poly := [([0,0], 48),([0,2], 16),([0,7], 80),([0,9], 80),([2,2], 8),([7,7], 40),([7,9], 80),([8,8], 40),([9,9], 40)]
def c3GroupHessian71_11 : Poly := List.flatten [c3GroupHessian71_11Chunk0]
theorem c3GroupHessian71_11_check : sumFast (c3TensorGroup71.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian71_11 := by kernel_rfl
private def c3GroupHessian71_12Chunk0 : Poly := [([0,0], -40),([0,3], -16),([0,7], -80),([0,8], 40),([0,9], -80),([2,3], 4),([3,7], -20),([3,9], -20),([5,8], 40),([7,7], -40),([7,9], -80),([9,9], -40)]
def c3GroupHessian71_12 : Poly := List.flatten [c3GroupHessian71_12Chunk0]
theorem c3GroupHessian71_12_check : sumFast (c3TensorGroup71.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian71_12 := by kernel_rfl
private def c3GroupHessian71_13Chunk0 : Poly := [([0,0], -24),([0,2], -4),([0,6], -24),([0,7], -20),([0,8], -40),([0,9], -60),([2,6], -4),([4,8], -40),([6,7], -20),([6,9], -20),([7,9], -40),([8,8], -40),([9,9], -40)]
def c3GroupHessian71_13 : Poly := List.flatten [c3GroupHessian71_13Chunk0]
theorem c3GroupHessian71_13_check : sumFast (c3TensorGroup71.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian71_13 := by kernel_rfl
private def c3GroupHessian71_22Chunk0 : Poly := [([0,0], 80),([0,3], 40),([0,5], 80),([0,7], 80),([0,9], 80),([3,3], 16),([3,7], 40),([3,9], 40),([5,5], 40),([7,7], 40),([7,9], 80),([9,9], 40)]
def c3GroupHessian71_22 : Poly := List.flatten [c3GroupHessian71_22Chunk0]
theorem c3GroupHessian71_22_check : sumFast (c3TensorGroup71.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian71_22 := by kernel_rfl
private def c3GroupHessian71_23Chunk0 : Poly := [([0,0], -20),([0,3], 8),([0,4], -40),([0,5], -40),([0,6], 20),([0,7], 20),([0,8], -40),([0,9], 60),([3,6], 8),([3,9], 20),([4,5], -40),([5,8], -40),([6,7], 20),([6,9], 20),([7,9], 40),([9,9], 40)]
def c3GroupHessian71_23 : Poly := List.flatten [c3GroupHessian71_23Chunk0]
theorem c3GroupHessian71_23_check : sumFast (c3TensorGroup71.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian71_23 := by kernel_rfl
private def c3GroupHessian71_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 32),([0,8], 80),([0,9], 40),([4,4], 40),([4,8], 80),([6,6], 16),([6,9], 40),([8,8], 40),([9,9], 40)]
def c3GroupHessian71_33 : Poly := List.flatten [c3GroupHessian71_33Chunk0]
theorem c3GroupHessian71_33_check : sumFast (c3TensorGroup71.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian71_33 := by kernel_rfl
end D4.Secondary
