import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup151_det_check : c3TensorGroup151.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 196)) = true := by kernel_rfl
private def c3GroupHessian151_00Chunk0 : Poly := [([0,0], 16),([0,1], 16),([0,5], 16),([0,9], 16),([1,1], 16),([1,5], 32),([1,9], 8),([5,5], 16),([5,9], 8),([6,6], 40),([9,9], 8)]
def c3GroupHessian151_00 : Poly := List.flatten [c3GroupHessian151_00Chunk0]
theorem c3GroupHessian151_00_check : sumFast (c3TensorGroup151.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian151_00 := by kernel_rfl
private def c3GroupHessian151_01Chunk0 : Poly := [([0,0], 8),([0,1], -8),([0,5], -8),([0,6], -40),([0,9], 12),([1,8], -20),([1,9], 4),([2,6], -40),([5,8], -20),([5,9], 4),([6,7], -40),([9,9], 8)]
def c3GroupHessian151_01 : Poly := List.flatten [c3GroupHessian151_01Chunk0]
theorem c3GroupHessian151_01_check : sumFast (c3TensorGroup151.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian151_01 := by kernel_rfl
private def c3GroupHessian151_02Chunk0 : Poly := [([0,0], -8),([0,1], -16),([0,5], -24),([0,6], 40),([0,9], -12),([1,3], -20),([1,5], -16),([1,9], -4),([3,5], -20),([5,5], -16),([5,9], -8),([6,7], 40),([9,9], -8)]
def c3GroupHessian151_02 : Poly := List.flatten [c3GroupHessian151_02Chunk0]
theorem c3GroupHessian151_02_check : sumFast (c3TensorGroup151.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian151_02 := by kernel_rfl
private def c3GroupHessian151_03Chunk0 : Poly := [([0,0], -8),([0,1], 8),([0,5], 8),([0,6], -40),([0,9], -12),([1,8], 20),([1,9], -4),([4,6], -40),([5,8], 20),([5,9], -4),([6,6], -40),([9,9], -8)]
def c3GroupHessian151_03 : Poly := List.flatten [c3GroupHessian151_03Chunk0]
theorem c3GroupHessian151_03_check : sumFast (c3TensorGroup151.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian151_03 := by kernel_rfl
private def c3GroupHessian151_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 80),([0,8], 40),([0,9], 8),([2,2], 40),([2,7], 80),([7,7], 40),([8,8], 40),([9,9], 8)]
def c3GroupHessian151_11 : Poly := List.flatten [c3GroupHessian151_11Chunk0]
theorem c3GroupHessian151_11_check : sumFast (c3TensorGroup151.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian151_11 := by kernel_rfl
private def c3GroupHessian151_12Chunk0 : Poly := [([0,0], -32),([0,2], -40),([0,3], 20),([0,5], 8),([0,7], -80),([0,8], 20),([0,9], -8),([2,7], -40),([3,8], 40),([5,8], 20),([5,9], -4),([7,7], -40),([9,9], -8)]
def c3GroupHessian151_12 : Poly := List.flatten [c3GroupHessian151_12Chunk0]
theorem c3GroupHessian151_12_check : sumFast (c3TensorGroup151.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian151_12 := by kernel_rfl
private def c3GroupHessian151_13Chunk0 : Poly := [([0,0], 24),([0,2], 40),([0,4], 40),([0,6], 40),([0,7], 40),([0,8], -40),([0,9], -8),([2,4], 40),([2,6], 40),([4,7], 40),([6,7], 40),([8,8], -40),([9,9], -8)]
def c3GroupHessian151_13 : Poly := List.flatten [c3GroupHessian151_13Chunk0]
theorem c3GroupHessian151_13_check : sumFast (c3TensorGroup151.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian151_13 := by kernel_rfl
private def c3GroupHessian151_22Chunk0 : Poly := [([0,0], 56),([0,3], 40),([0,5], 32),([0,7], 80),([0,9], 8),([3,3], 40),([3,5], 40),([5,5], 16),([5,9], 8),([7,7], 40),([9,9], 8)]
def c3GroupHessian151_22 : Poly := List.flatten [c3GroupHessian151_22Chunk0]
theorem c3GroupHessian151_22_check : sumFast (c3TensorGroup151.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian151_22 := by kernel_rfl
private def c3GroupHessian151_23Chunk0 : Poly := [([0,0], -48),([0,3], -20),([0,4], -40),([0,5], -8),([0,6], -40),([0,7], -40),([0,8], -20),([0,9], 8),([3,8], -40),([4,7], -40),([5,8], -20),([5,9], 4),([6,7], -40),([9,9], 8)]
def c3GroupHessian151_23 : Poly := List.flatten [c3GroupHessian151_23Chunk0]
theorem c3GroupHessian151_23_check : sumFast (c3TensorGroup151.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian151_23 := by kernel_rfl
private def c3GroupHessian151_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 80),([0,8], 40),([0,9], 8),([4,4], 40),([4,6], 80),([6,6], 40),([8,8], 40),([9,9], 8)]
def c3GroupHessian151_33 : Poly := List.flatten [c3GroupHessian151_33Chunk0]
theorem c3GroupHessian151_33_check : sumFast (c3TensorGroup151.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian151_33 := by kernel_rfl
end D4.Secondary
