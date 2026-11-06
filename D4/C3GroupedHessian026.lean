import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup26_det_check : c3TensorGroup26.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 40)) = true := by kernel_rfl
private def c3GroupHessian26_00Chunk0 : Poly := [([0,0], 48),([0,5], 80),([0,6], 80),([1,1], 40),([1,9], -80),([5,5], 40),([5,6], 80),([6,6], 40),([9,9], 40)]
def c3GroupHessian26_00 : Poly := List.flatten [c3GroupHessian26_00Chunk0]
theorem c3GroupHessian26_00_check : sumFast (c3TensorGroup26.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian26_00 := by kernel_rfl
private def c3GroupHessian26_01Chunk0 : Poly := [([0,0], 8),([0,1], -40),([0,2], -16),([0,9], 40),([1,7], -40),([1,8], -40),([1,9], -40),([2,5], -20),([2,6], -20),([7,9], 40),([8,9], 40),([9,9], 40)]
def c3GroupHessian26_01 : Poly := List.flatten [c3GroupHessian26_01Chunk0]
theorem c3GroupHessian26_01_check : sumFast (c3TensorGroup26.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian26_01 := by kernel_rfl
private def c3GroupHessian26_02Chunk0 : Poly := [([0,0], -24),([0,1], 40),([0,5], -60),([0,6], -20),([0,9], -40),([1,3], 40),([1,7], 40),([1,9], 40),([3,9], -40),([5,5], -40),([5,6], -40),([7,9], -40),([9,9], -40)]
def c3GroupHessian26_02 : Poly := List.flatten [c3GroupHessian26_02Chunk0]
theorem c3GroupHessian26_02_check : sumFast (c3TensorGroup26.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian26_02 := by kernel_rfl
private def c3GroupHessian26_03Chunk0 : Poly := [([0,0], -24),([0,1], 40),([0,5], -20),([0,6], -60),([0,9], -40),([1,4], 40),([1,8], 40),([1,9], 40),([4,9], -40),([5,6], -40),([6,6], -40),([8,9], -40),([9,9], -40)]
def c3GroupHessian26_03 : Poly := List.flatten [c3GroupHessian26_03Chunk0]
theorem c3GroupHessian26_03_check : sumFast (c3TensorGroup26.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian26_03 := by kernel_rfl
private def c3GroupHessian26_11Chunk0 : Poly := [([0,0], 48),([0,2], 8),([0,7], 80),([0,8], 80),([0,9], 80),([2,2], 16),([7,7], 40),([7,8], 80),([7,9], 80),([8,8], 40),([8,9], 80),([9,9], 40)]
def c3GroupHessian26_11 : Poly := List.flatten [c3GroupHessian26_11Chunk0]
theorem c3GroupHessian26_11_check : sumFast (c3TensorGroup26.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian26_11 := by kernel_rfl
private def c3GroupHessian26_12Chunk0 : Poly := [([0,0], -44),([0,2], 8),([0,3], -40),([0,7], -80),([0,8], -40),([0,9], -80),([2,5], 20),([3,7], -40),([3,8], -40),([3,9], -40),([7,7], -40),([7,8], -40),([7,9], -80),([8,9], -40),([9,9], -40)]
def c3GroupHessian26_12 : Poly := List.flatten [c3GroupHessian26_12Chunk0]
theorem c3GroupHessian26_12_check : sumFast (c3TensorGroup26.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian26_12 := by kernel_rfl
private def c3GroupHessian26_13Chunk0 : Poly := [([0,0], -44),([0,2], 8),([0,4], -40),([0,7], -40),([0,8], -80),([0,9], -80),([2,6], 20),([4,7], -40),([4,8], -40),([4,9], -40),([7,8], -40),([7,9], -40),([8,8], -40),([8,9], -80),([9,9], -40)]
def c3GroupHessian26_13 : Poly := List.flatten [c3GroupHessian26_13Chunk0]
theorem c3GroupHessian26_13_check : sumFast (c3TensorGroup26.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian26_13 := by kernel_rfl
private def c3GroupHessian26_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 40),([0,7], 80),([0,9], 80),([3,3], 40),([3,7], 80),([3,9], 80),([5,5], 40),([7,7], 40),([7,9], 80),([9,9], 40)]
def c3GroupHessian26_22 : Poly := List.flatten [c3GroupHessian26_22Chunk0]
theorem c3GroupHessian26_22_check : sumFast (c3TensorGroup26.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian26_22 := by kernel_rfl
private def c3GroupHessian26_23Chunk0 : Poly := [([0,0], 48),([0,3], 40),([0,4], 40),([0,5], 20),([0,6], 20),([0,7], 40),([0,8], 40),([0,9], 80),([3,4], 40),([3,8], 40),([3,9], 40),([4,7], 40),([4,9], 40),([5,6], 40),([7,8], 40),([7,9], 40),([8,9], 40),([9,9], 40)]
def c3GroupHessian26_23 : Poly := List.flatten [c3GroupHessian26_23Chunk0]
theorem c3GroupHessian26_23_check : sumFast (c3TensorGroup26.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian26_23 := by kernel_rfl
private def c3GroupHessian26_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 40),([0,8], 80),([0,9], 80),([4,4], 40),([4,8], 80),([4,9], 80),([6,6], 40),([8,8], 40),([8,9], 80),([9,9], 40)]
def c3GroupHessian26_33 : Poly := List.flatten [c3GroupHessian26_33Chunk0]
theorem c3GroupHessian26_33_check : sumFast (c3TensorGroup26.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian26_33 := by kernel_rfl
end D4.Secondary
