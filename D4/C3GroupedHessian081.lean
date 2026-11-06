import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup81_det_check : c3TensorGroup81.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 109)) = true := by kernel_rfl
private def c3GroupHessian81_00Chunk0 : Poly := [([0,0], 160),([0,1], 160),([0,5], 160),([0,6], 160),([0,9], 160),([1,1], 40),([1,5], 80),([1,6], 80),([1,9], 80),([5,5], 40),([5,6], 80),([5,9], 80),([6,6], 40),([6,9], 80),([9,9], 40)]
def c3GroupHessian81_00 : Poly := List.flatten [c3GroupHessian81_00Chunk0]
theorem c3GroupHessian81_00_check : sumFast (c3TensorGroup81.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian81_00 := by kernel_rfl
private def c3GroupHessian81_01Chunk0 : Poly := [([0,0], 80),([0,1], 40),([0,5], 40),([0,6], 40),([0,9], 120),([1,9], 40),([5,9], 40),([6,9], 40),([9,9], 40)]
def c3GroupHessian81_01 : Poly := List.flatten [c3GroupHessian81_01Chunk0]
theorem c3GroupHessian81_01_check : sumFast (c3TensorGroup81.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian81_01 := by kernel_rfl
private def c3GroupHessian81_02Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -120),([0,6], -40),([0,9], -120),([1,5], -40),([1,9], -40),([5,5], -40),([5,6], -40),([5,9], -80),([6,9], -40),([9,9], -40)]
def c3GroupHessian81_02 : Poly := List.flatten [c3GroupHessian81_02Chunk0]
theorem c3GroupHessian81_02_check : sumFast (c3TensorGroup81.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian81_02 := by kernel_rfl
private def c3GroupHessian81_03Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -40),([0,6], -120),([0,9], -120),([1,6], -40),([1,9], -40),([5,6], -40),([5,9], -40),([6,6], -40),([6,9], -80),([9,9], -40)]
def c3GroupHessian81_03 : Poly := List.flatten [c3GroupHessian81_03Chunk0]
theorem c3GroupHessian81_03_check : sumFast (c3TensorGroup81.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian81_03 := by kernel_rfl
private def c3GroupHessian81_11Chunk0 : Poly := [([0,0], 48),([0,2], 8),([0,7], 16),([0,8], 8),([0,9], 80),([2,2], 16),([2,7], 8),([2,8], -16),([7,7], 8),([7,8], 8),([8,8], 16),([9,9], 40)]
def c3GroupHessian81_11 : Poly := List.flatten [c3GroupHessian81_11Chunk0]
theorem c3GroupHessian81_11_check : sumFast (c3TensorGroup81.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian81_11 := by kernel_rfl
private def c3GroupHessian81_12Chunk0 : Poly := [([0,0], -44),([0,2], 8),([0,5], -40),([0,7], -12),([0,8], -8),([0,9], -80),([2,3], 20),([2,7], -4),([3,8], -20),([5,9], -40),([7,7], -8),([7,8], -4),([9,9], -40)]
def c3GroupHessian81_12 : Poly := List.flatten [c3GroupHessian81_12Chunk0]
theorem c3GroupHessian81_12_check : sumFast (c3TensorGroup81.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian81_12 := by kernel_rfl
private def c3GroupHessian81_13Chunk0 : Poly := [([0,0], -44),([0,2], 8),([0,6], -40),([0,7], -4),([0,8], -20),([0,9], -80),([2,4], 20),([2,8], 8),([4,8], -20),([6,9], -40),([7,8], -4),([8,8], -16),([9,9], -40)]
def c3GroupHessian81_13 : Poly := List.flatten [c3GroupHessian81_13Chunk0]
theorem c3GroupHessian81_13_check : sumFast (c3TensorGroup81.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian81_13 := by kernel_rfl
private def c3GroupHessian81_22Chunk0 : Poly := [([0,0], 56),([0,3], 40),([0,5], 80),([0,7], 8),([0,9], 80),([3,3], 40),([5,5], 40),([5,9], 80),([7,7], 8),([9,9], 40)]
def c3GroupHessian81_22 : Poly := List.flatten [c3GroupHessian81_22Chunk0]
theorem c3GroupHessian81_22_check : sumFast (c3TensorGroup81.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian81_22 := by kernel_rfl
private def c3GroupHessian81_23Chunk0 : Poly := [([0,0], 48),([0,3], 20),([0,4], 20),([0,5], 40),([0,6], 40),([0,7], 4),([0,8], 8),([0,9], 80),([3,4], 40),([3,8], 20),([5,6], 40),([5,9], 40),([6,9], 40),([7,8], 4),([9,9], 40)]
def c3GroupHessian81_23 : Poly := List.flatten [c3GroupHessian81_23Chunk0]
theorem c3GroupHessian81_23_check : sumFast (c3TensorGroup81.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian81_23 := by kernel_rfl
private def c3GroupHessian81_33Chunk0 : Poly := [([0,0], 56),([0,4], 40),([0,6], 80),([0,8], 32),([0,9], 80),([4,4], 40),([4,8], 40),([6,6], 40),([6,9], 80),([8,8], 16),([9,9], 40)]
def c3GroupHessian81_33 : Poly := List.flatten [c3GroupHessian81_33Chunk0]
theorem c3GroupHessian81_33_check : sumFast (c3TensorGroup81.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian81_33 := by kernel_rfl
end D4.Secondary
