import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup187_det_check : c3TensorGroup187.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 239)) = true := by kernel_rfl
private def c3GroupHessian187_00Chunk0 : Poly := [([0,0], 160),([0,1], 40),([0,5], 160),([0,6], 160),([0,9], 160),([1,1], 24),([1,6], 40),([5,5], 80),([5,9], 160),([6,6], 80),([9,9], 80)]
def c3GroupHessian187_00 : Poly := List.flatten [c3GroupHessian187_00Chunk0]
theorem c3GroupHessian187_00_check : sumFast (c3TensorGroup187.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian187_00 := by kernel_rfl
private def c3GroupHessian187_01Chunk0 : Poly := [([0,0], 160),([0,1], 20),([0,2], 20),([0,5], 80),([0,6], 80),([0,7], 80),([0,8], 80),([0,9], 160),([1,2], 8),([1,8], 20),([2,6], 20),([5,7], 80),([5,9], 80),([6,8], 80),([7,9], 80),([9,9], 80)]
def c3GroupHessian187_01 : Poly := List.flatten [c3GroupHessian187_01Chunk0]
theorem c3GroupHessian187_01_check : sumFast (c3TensorGroup187.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian187_01 := by kernel_rfl
private def c3GroupHessian187_02Chunk0 : Poly := [([0,0], -160),([0,3], -80),([0,5], -240),([0,7], -80),([0,9], -240),([3,5], -80),([3,9], -80),([5,5], -80),([5,7], -80),([5,9], -160),([7,9], -80),([9,9], -80)]
def c3GroupHessian187_02 : Poly := List.flatten [c3GroupHessian187_02Chunk0]
theorem c3GroupHessian187_02_check : sumFast (c3TensorGroup187.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian187_02 := by kernel_rfl
private def c3GroupHessian187_03Chunk0 : Poly := [([0,0], -120),([0,1], -24),([0,4], -40),([0,6], -200),([0,8], -80),([0,9], -80),([1,4], -4),([1,6], -20),([1,8], -20),([4,6], -40),([5,9], -80),([6,6], -80),([6,8], -80),([9,9], -80)]
def c3GroupHessian187_03 : Poly := List.flatten [c3GroupHessian187_03Chunk0]
theorem c3GroupHessian187_03_check : sumFast (c3TensorGroup187.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian187_03 := by kernel_rfl
private def c3GroupHessian187_11Chunk0 : Poly := [([0,0], 160),([0,2], 40),([0,7], 160),([0,8], 160),([0,9], 160),([2,2], 24),([2,8], 40),([7,7], 80),([7,9], 160),([8,8], 80),([9,9], 80)]
def c3GroupHessian187_11 : Poly := List.flatten [c3GroupHessian187_11Chunk0]
theorem c3GroupHessian187_11_check : sumFast (c3TensorGroup187.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian187_11 := by kernel_rfl
private def c3GroupHessian187_12Chunk0 : Poly := [([0,0], -160),([0,3], -80),([0,5], -80),([0,7], -240),([0,9], -240),([3,7], -80),([3,9], -80),([5,7], -80),([5,9], -80),([7,7], -80),([7,9], -160),([9,9], -80)]
def c3GroupHessian187_12 : Poly := List.flatten [c3GroupHessian187_12Chunk0]
theorem c3GroupHessian187_12_check : sumFast (c3TensorGroup187.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian187_12 := by kernel_rfl
private def c3GroupHessian187_13Chunk0 : Poly := [([0,0], -120),([0,2], -24),([0,4], -40),([0,6], -80),([0,8], -200),([0,9], -80),([2,4], -4),([2,6], -20),([2,8], -20),([4,8], -40),([6,8], -80),([7,9], -80),([8,8], -80),([9,9], -80)]
def c3GroupHessian187_13 : Poly := List.flatten [c3GroupHessian187_13Chunk0]
theorem c3GroupHessian187_13_check : sumFast (c3TensorGroup187.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian187_13 := by kernel_rfl
private def c3GroupHessian187_22Chunk0 : Poly := [([0,0], 320),([0,3], 320),([0,5], 320),([0,7], 320),([0,9], 320),([3,3], 80),([3,5], 160),([3,7], 160),([3,9], 160),([5,5], 80),([5,7], 160),([5,9], 160),([7,7], 80),([7,9], 160),([9,9], 80)]
def c3GroupHessian187_22 : Poly := List.flatten [c3GroupHessian187_22Chunk0]
theorem c3GroupHessian187_22_check : sumFast (c3TensorGroup187.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian187_22 := by kernel_rfl
private def c3GroupHessian187_23Chunk0 : Poly := [([0,9], 160),([3,9], 80),([5,9], 80),([7,9], 80),([9,9], 80)]
def c3GroupHessian187_23 : Poly := List.flatten [c3GroupHessian187_23Chunk0]
theorem c3GroupHessian187_23_check : sumFast (c3TensorGroup187.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian187_23 := by kernel_rfl
private def c3GroupHessian187_33Chunk0 : Poly := [([0,0], 192),([0,4], 144),([0,6], 240),([0,8], 240),([4,4], 32),([4,6], 80),([4,8], 80),([6,6], 80),([6,8], 160),([8,8], 80),([9,9], 80)]
def c3GroupHessian187_33 : Poly := List.flatten [c3GroupHessian187_33Chunk0]
theorem c3GroupHessian187_33_check : sumFast (c3TensorGroup187.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian187_33 := by kernel_rfl
end D4.Secondary
