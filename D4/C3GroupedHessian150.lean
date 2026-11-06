import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup150_det_check : c3TensorGroup150.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 195)) = true := by kernel_rfl
private def c3GroupHessian150_00Chunk0 : Poly := [([0,0], 48),([0,1], 16),([0,5], 80),([0,9], 80),([1,1], 8),([5,5], 40),([5,9], 80),([6,6], 40),([9,9], 40)]
def c3GroupHessian150_00 : Poly := List.flatten [c3GroupHessian150_00Chunk0]
theorem c3GroupHessian150_00_check : sumFast (c3TensorGroup150.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian150_00 := by kernel_rfl
private def c3GroupHessian150_01Chunk0 : Poly := [([0,0], 24),([0,1], 4),([0,5], 20),([0,6], -40),([0,8], 24),([0,9], 60),([1,8], 4),([2,6], -40),([5,8], 20),([5,9], 40),([6,7], -40),([8,9], 20),([9,9], 40)]
def c3GroupHessian150_01 : Poly := List.flatten [c3GroupHessian150_01Chunk0]
theorem c3GroupHessian150_01_check : sumFast (c3TensorGroup150.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian150_01 := by kernel_rfl
private def c3GroupHessian150_02Chunk0 : Poly := [([0,0], -40),([0,3], -16),([0,5], -80),([0,6], 40),([0,9], -80),([1,3], 4),([3,5], -20),([3,9], -20),([5,5], -40),([5,9], -80),([6,7], 40),([9,9], -40)]
def c3GroupHessian150_02 : Poly := List.flatten [c3GroupHessian150_02Chunk0]
theorem c3GroupHessian150_02_check : sumFast (c3TensorGroup150.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian150_02 := by kernel_rfl
private def c3GroupHessian150_03Chunk0 : Poly := [([0,0], -24),([0,1], -4),([0,5], -20),([0,6], -40),([0,8], -24),([0,9], -60),([1,8], -4),([4,6], -40),([5,8], -20),([5,9], -40),([6,6], -40),([8,9], -20),([9,9], -40)]
def c3GroupHessian150_03 : Poly := List.flatten [c3GroupHessian150_03Chunk0]
theorem c3GroupHessian150_03_check : sumFast (c3TensorGroup150.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian150_03 := by kernel_rfl
private def c3GroupHessian150_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 80),([0,8], 32),([0,9], 40),([2,2], 40),([2,7], 80),([7,7], 40),([8,8], 16),([8,9], 40),([9,9], 40)]
def c3GroupHessian150_11 : Poly := List.flatten [c3GroupHessian150_11Chunk0]
theorem c3GroupHessian150_11_check : sumFast (c3TensorGroup150.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian150_11 := by kernel_rfl
private def c3GroupHessian150_12Chunk0 : Poly := [([0,0], -60),([0,2], -40),([0,3], -8),([0,5], -20),([0,7], -80),([0,8], -20),([0,9], -60),([2,7], -40),([3,8], -8),([3,9], -20),([5,8], -20),([5,9], -40),([7,7], -40),([8,9], -20),([9,9], -40)]
def c3GroupHessian150_12 : Poly := List.flatten [c3GroupHessian150_12Chunk0]
theorem c3GroupHessian150_12_check : sumFast (c3TensorGroup150.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian150_12 := by kernel_rfl
private def c3GroupHessian150_13Chunk0 : Poly := [([0,0], 24),([0,2], 40),([0,4], 40),([0,6], 40),([0,7], 40),([0,8], -32),([0,9], -40),([2,4], 40),([2,6], 40),([4,7], 40),([6,7], 40),([8,8], -16),([8,9], -40),([9,9], -40)]
def c3GroupHessian150_13 : Poly := List.flatten [c3GroupHessian150_13Chunk0]
theorem c3GroupHessian150_13_check : sumFast (c3TensorGroup150.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian150_13 := by kernel_rfl
private def c3GroupHessian150_22Chunk0 : Poly := [([0,0], 80),([0,3], 40),([0,5], 80),([0,7], 80),([0,9], 80),([3,3], 16),([3,5], 40),([3,9], 40),([5,5], 40),([5,9], 80),([7,7], 40),([9,9], 40)]
def c3GroupHessian150_22 : Poly := List.flatten [c3GroupHessian150_22Chunk0]
theorem c3GroupHessian150_22_check : sumFast (c3TensorGroup150.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian150_22 := by kernel_rfl
private def c3GroupHessian150_23Chunk0 : Poly := [([0,0], -20),([0,3], 8),([0,4], -40),([0,5], 20),([0,6], -40),([0,7], -40),([0,8], 20),([0,9], 60),([3,8], 8),([3,9], 20),([4,7], -40),([5,8], 20),([5,9], 40),([6,7], -40),([8,9], 20),([9,9], 40)]
def c3GroupHessian150_23 : Poly := List.flatten [c3GroupHessian150_23Chunk0]
theorem c3GroupHessian150_23_check : sumFast (c3TensorGroup150.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian150_23 := by kernel_rfl
private def c3GroupHessian150_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 80),([0,8], 32),([0,9], 40),([4,4], 40),([4,6], 80),([6,6], 40),([8,8], 16),([8,9], 40),([9,9], 40)]
def c3GroupHessian150_33 : Poly := List.flatten [c3GroupHessian150_33Chunk0]
theorem c3GroupHessian150_33_check : sumFast (c3TensorGroup150.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian150_33 := by kernel_rfl
end D4.Secondary
