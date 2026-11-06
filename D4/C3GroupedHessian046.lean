import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup46_det_check : c3TensorGroup46.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 64)) = true := by kernel_rfl
private def c3GroupHessian46_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 32),([0,6], 80),([0,9], 32),([1,1], 40),([1,6], 80),([5,5], 16),([5,9], 32),([6,6], 40),([9,9], 16)]
def c3GroupHessian46_00 : Poly := List.flatten [c3GroupHessian46_00Chunk0]
theorem c3GroupHessian46_00_check : sumFast (c3TensorGroup46.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian46_00 := by kernel_rfl
private def c3GroupHessian46_01Chunk0 : Poly := [([0,0], 20),([0,2], 4),([0,5], 20),([0,7], -40),([0,8], 4),([0,9], 36),([1,7], -40),([2,5], 4),([2,9], 4),([5,8], 4),([5,9], 16),([6,7], -40),([8,9], 4),([9,9], 16)]
def c3GroupHessian46_01 : Poly := List.flatten [c3GroupHessian46_01Chunk0]
theorem c3GroupHessian46_01_check : sumFast (c3TensorGroup46.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian46_01 := by kernel_rfl
private def c3GroupHessian46_02Chunk0 : Poly := [([0,0], 24),([0,1], 40),([0,3], 40),([0,5], -32),([0,6], 40),([0,7], 40),([0,9], -32),([1,3], 40),([1,7], 40),([3,6], 40),([5,5], -16),([5,9], -32),([6,7], 40),([9,9], -16)]
def c3GroupHessian46_02 : Poly := List.flatten [c3GroupHessian46_02Chunk0]
theorem c3GroupHessian46_02_check : sumFast (c3TensorGroup46.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian46_02 := by kernel_rfl
private def c3GroupHessian46_03Chunk0 : Poly := [([0,0], -56),([0,1], -40),([0,4], -8),([0,5], -16),([0,6], -80),([0,8], -4),([0,9], -32),([1,6], -40),([4,5], -8),([4,9], -8),([5,8], -4),([5,9], -16),([6,6], -40),([8,9], -4),([9,9], -16)]
def c3GroupHessian46_03 : Poly := List.flatten [c3GroupHessian46_03Chunk0]
theorem c3GroupHessian46_03_check : sumFast (c3TensorGroup46.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian46_03 := by kernel_rfl
private def c3GroupHessian46_11Chunk0 : Poly := [([0,0], 32),([0,2], 24),([0,8], 24),([0,9], 40),([2,2], 8),([2,8], 16),([2,9], 8),([7,7], 40),([8,8], 8),([8,9], 8),([9,9], 16)]
def c3GroupHessian46_11 : Poly := List.flatten [c3GroupHessian46_11Chunk0]
theorem c3GroupHessian46_11_check : sumFast (c3TensorGroup46.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian46_11 := by kernel_rfl
private def c3GroupHessian46_12Chunk0 : Poly := [([0,0], -20),([0,2], -4),([0,5], -20),([0,7], -40),([0,8], -4),([0,9], -36),([2,5], -4),([2,9], -4),([3,7], -40),([5,8], -4),([5,9], -16),([7,7], -40),([8,9], -4),([9,9], -16)]
def c3GroupHessian46_12 : Poly := List.flatten [c3GroupHessian46_12Chunk0]
theorem c3GroupHessian46_12_check : sumFast (c3TensorGroup46.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian46_12 := by kernel_rfl
private def c3GroupHessian46_13Chunk0 : Poly := [([0,0], -20),([0,2], -4),([0,4], -4),([0,7], 40),([0,8], -16),([0,9], -36),([2,4], 4),([2,8], -8),([2,9], -4),([4,8], 4),([4,9], -8),([6,7], 40),([8,8], -8),([8,9], -8),([9,9], -16)]
def c3GroupHessian46_13 : Poly := List.flatten [c3GroupHessian46_13Chunk0]
theorem c3GroupHessian46_13_check : sumFast (c3TensorGroup46.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian46_13 := by kernel_rfl
private def c3GroupHessian46_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 32),([0,7], 80),([0,9], 32),([3,3], 40),([3,7], 80),([5,5], 16),([5,9], 32),([7,7], 40),([9,9], 16)]
def c3GroupHessian46_22 : Poly := List.flatten [c3GroupHessian46_22Chunk0]
theorem c3GroupHessian46_22_check : sumFast (c3TensorGroup46.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian46_22 := by kernel_rfl
private def c3GroupHessian46_23Chunk0 : Poly := [([0,0], -24),([0,3], -40),([0,4], 8),([0,5], 16),([0,6], -40),([0,7], -40),([0,8], 4),([0,9], 32),([3,6], -40),([4,5], 8),([4,9], 8),([5,8], 4),([5,9], 16),([6,7], -40),([8,9], 4),([9,9], 16)]
def c3GroupHessian46_23 : Poly := List.flatten [c3GroupHessian46_23Chunk0]
theorem c3GroupHessian46_23_check : sumFast (c3TensorGroup46.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian46_23 := by kernel_rfl
private def c3GroupHessian46_33Chunk0 : Poly := [([0,0], 56),([0,4], 16),([0,6], 80),([0,8], 8),([0,9], 32),([4,4], 16),([4,8], -8),([4,9], 16),([6,6], 40),([8,8], 8),([8,9], 8),([9,9], 16)]
def c3GroupHessian46_33 : Poly := List.flatten [c3GroupHessian46_33Chunk0]
theorem c3GroupHessian46_33_check : sumFast (c3TensorGroup46.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian46_33 := by kernel_rfl
end D4.Secondary
