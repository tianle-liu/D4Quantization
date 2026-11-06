import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup53_det_check : c3TensorGroup53.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 75)) = true := by kernel_rfl
private def c3GroupHessian53_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 16),([0,6], 80),([0,9], 8),([1,1], 40),([1,6], 80),([5,5], 8),([5,9], 8),([6,6], 40),([9,9], 16)]
def c3GroupHessian53_00 : Poly := List.flatten [c3GroupHessian53_00Chunk0]
theorem c3GroupHessian53_00_check : sumFast (c3TensorGroup53.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian53_00 := by kernel_rfl
private def c3GroupHessian53_01Chunk0 : Poly := [([0,0], 4),([0,2], 4),([0,5], 4),([0,7], -40),([0,9], 16),([1,7], -40),([2,5], 4),([2,9], -8),([5,9], 4),([6,7], -40),([8,9], 20),([9,9], 16)]
def c3GroupHessian53_01 : Poly := List.flatten [c3GroupHessian53_01Chunk0]
theorem c3GroupHessian53_01_check : sumFast (c3TensorGroup53.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian53_01 := by kernel_rfl
private def c3GroupHessian53_02Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,3], 40),([0,5], -16),([0,6], 40),([0,7], 40),([0,9], -8),([1,3], 40),([1,7], 40),([3,6], 40),([5,5], -8),([5,9], -8),([6,7], 40),([9,9], -16)]
def c3GroupHessian53_02 : Poly := List.flatten [c3GroupHessian53_02Chunk0]
theorem c3GroupHessian53_02_check : sumFast (c3TensorGroup53.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian53_02 := by kernel_rfl
private def c3GroupHessian53_03Chunk0 : Poly := [([0,0], -40),([0,1], -40),([0,4], 4),([0,6], -80),([0,9], -24),([1,6], -40),([4,5], 4),([4,9], -8),([5,9], -4),([6,6], -40),([8,9], -20),([9,9], -16)]
def c3GroupHessian53_03 : Poly := List.flatten [c3GroupHessian53_03Chunk0]
theorem c3GroupHessian53_03_check : sumFast (c3TensorGroup53.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian53_03 := by kernel_rfl
private def c3GroupHessian53_11Chunk0 : Poly := [([0,0], 16),([0,2], -8),([0,8], 40),([0,9], 24),([2,2], 16),([2,8], -40),([2,9], -16),([7,7], 40),([8,8], 40),([8,9], 40),([9,9], 16)]
def c3GroupHessian53_11 : Poly := List.flatten [c3GroupHessian53_11Chunk0]
theorem c3GroupHessian53_11_check : sumFast (c3TensorGroup53.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian53_11 := by kernel_rfl
private def c3GroupHessian53_12Chunk0 : Poly := [([0,0], -4),([0,2], -4),([0,5], -4),([0,7], -40),([0,9], -16),([2,5], -4),([2,9], 8),([3,7], -40),([5,9], -4),([7,7], -40),([8,9], -20),([9,9], -16)]
def c3GroupHessian53_12 : Poly := List.flatten [c3GroupHessian53_12Chunk0]
theorem c3GroupHessian53_12_check : sumFast (c3TensorGroup53.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian53_12 := by kernel_rfl
private def c3GroupHessian53_13Chunk0 : Poly := [([0,0], -20),([0,2], 20),([0,4], -4),([0,7], 40),([0,8], -60),([0,9], -32),([2,4], 16),([2,8], 20),([2,9], 8),([4,8], -20),([4,9], -8),([6,7], 40),([8,8], -40),([8,9], -40),([9,9], -16)]
def c3GroupHessian53_13 : Poly := List.flatten [c3GroupHessian53_13Chunk0]
theorem c3GroupHessian53_13_check : sumFast (c3TensorGroup53.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian53_13 := by kernel_rfl
private def c3GroupHessian53_22Chunk0 : Poly := [([0,0], 48),([0,3], 80),([0,5], 16),([0,7], 80),([0,9], 8),([3,3], 40),([3,7], 80),([5,5], 8),([5,9], 8),([7,7], 40),([9,9], 16)]
def c3GroupHessian53_22 : Poly := List.flatten [c3GroupHessian53_22Chunk0]
theorem c3GroupHessian53_22_check : sumFast (c3TensorGroup53.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian53_22 := by kernel_rfl
private def c3GroupHessian53_23Chunk0 : Poly := [([0,0], -40),([0,3], -40),([0,4], -4),([0,6], -40),([0,7], -40),([0,9], 24),([3,6], -40),([4,5], -4),([4,9], 8),([5,9], 4),([6,7], -40),([8,9], 20),([9,9], 16)]
def c3GroupHessian53_23 : Poly := List.flatten [c3GroupHessian53_23Chunk0]
theorem c3GroupHessian53_23_check : sumFast (c3TensorGroup53.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian53_23 := by kernel_rfl
private def c3GroupHessian53_33Chunk0 : Poly := [([0,0], 80),([0,4], 40),([0,6], 80),([0,8], 80),([0,9], 40),([4,4], 16),([4,8], 40),([4,9], 16),([6,6], 40),([8,8], 40),([8,9], 40),([9,9], 16)]
def c3GroupHessian53_33 : Poly := List.flatten [c3GroupHessian53_33Chunk0]
theorem c3GroupHessian53_33_check : sumFast (c3TensorGroup53.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian53_33 := by kernel_rfl
end D4.Secondary
