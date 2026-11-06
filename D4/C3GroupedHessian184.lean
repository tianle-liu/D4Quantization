import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup184_det_check : c3TensorGroup184.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 235)) = true := by kernel_rfl
private def c3GroupHessian184_00Chunk0 : Poly := [([0,0], 56),([0,1], 40),([0,5], 80),([0,6], 32),([0,9], 80),([1,1], 40),([1,6], 40),([5,5], 40),([5,9], 80),([6,6], 16),([9,9], 40)]
def c3GroupHessian184_00 : Poly := List.flatten [c3GroupHessian184_00Chunk0]
theorem c3GroupHessian184_00_check : sumFast (c3TensorGroup184.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian184_00 := by kernel_rfl
private def c3GroupHessian184_01Chunk0 : Poly := [([0,0], 44),([0,2], 4),([0,5], 40),([0,6], 4),([0,7], 40),([0,8], -8),([0,9], 80),([1,8], -20),([2,6], 4),([5,7], 40),([5,9], 40),([6,8], -8),([7,9], 40),([9,9], 40)]
def c3GroupHessian184_01 : Poly := List.flatten [c3GroupHessian184_01Chunk0]
theorem c3GroupHessian184_01_check : sumFast (c3TensorGroup184.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian184_01 := by kernel_rfl
private def c3GroupHessian184_02Chunk0 : Poly := [([0,0], -80),([0,3], -40),([0,5], -120),([0,7], -40),([0,9], -120),([3,5], -40),([3,9], -40),([5,5], -40),([5,7], -40),([5,9], -80),([7,9], -40),([9,9], -40)]
def c3GroupHessian184_02 : Poly := List.flatten [c3GroupHessian184_02Chunk0]
theorem c3GroupHessian184_02_check : sumFast (c3TensorGroup184.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian184_02 := by kernel_rfl
private def c3GroupHessian184_03Chunk0 : Poly := [([0,0], 4),([0,1], 20),([0,4], 20),([0,6], -12),([0,8], 8),([0,9], -40),([1,4], 40),([1,6], -20),([1,8], 20),([4,6], 20),([5,9], -40),([6,6], -16),([6,8], 8),([9,9], -40)]
def c3GroupHessian184_03 : Poly := List.flatten [c3GroupHessian184_03Chunk0]
theorem c3GroupHessian184_03_check : sumFast (c3TensorGroup184.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian184_03 := by kernel_rfl
private def c3GroupHessian184_11Chunk0 : Poly := [([0,0], 48),([0,2], 16),([0,7], 80),([0,8], 8),([0,9], 80),([2,2], 8),([2,8], 8),([7,7], 40),([7,9], 80),([8,8], 16),([9,9], 40)]
def c3GroupHessian184_11 : Poly := List.flatten [c3GroupHessian184_11Chunk0]
theorem c3GroupHessian184_11_check : sumFast (c3TensorGroup184.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian184_11 := by kernel_rfl
private def c3GroupHessian184_12Chunk0 : Poly := [([0,0], -80),([0,3], -40),([0,5], -40),([0,7], -120),([0,9], -120),([3,7], -40),([3,9], -40),([5,7], -40),([5,9], -40),([7,7], -40),([7,9], -80),([9,9], -40)]
def c3GroupHessian184_12 : Poly := List.flatten [c3GroupHessian184_12Chunk0]
theorem c3GroupHessian184_12_check : sumFast (c3TensorGroup184.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian184_12 := by kernel_rfl
private def c3GroupHessian184_13Chunk0 : Poly := [([0,0], -4),([0,2], -4),([0,6], -4),([0,8], -16),([0,9], -40),([2,6], -4),([2,8], -4),([4,8], -20),([6,8], 8),([7,9], -40),([8,8], -16),([9,9], -40)]
def c3GroupHessian184_13 : Poly := List.flatten [c3GroupHessian184_13Chunk0]
theorem c3GroupHessian184_13_check : sumFast (c3TensorGroup184.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian184_13 := by kernel_rfl
private def c3GroupHessian184_22Chunk0 : Poly := [([0,0], 160),([0,3], 160),([0,5], 160),([0,7], 160),([0,9], 160),([3,3], 40),([3,5], 80),([3,7], 80),([3,9], 80),([5,5], 40),([5,7], 80),([5,9], 80),([7,7], 40),([7,9], 80),([9,9], 40)]
def c3GroupHessian184_22 : Poly := List.flatten [c3GroupHessian184_22Chunk0]
theorem c3GroupHessian184_22_check : sumFast (c3TensorGroup184.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian184_22 := by kernel_rfl
private def c3GroupHessian184_23Chunk0 : Poly := [([0,9], 80),([3,9], 40),([5,9], 40),([7,9], 40),([9,9], 40)]
def c3GroupHessian184_23 : Poly := List.flatten [c3GroupHessian184_23Chunk0]
theorem c3GroupHessian184_23_check : sumFast (c3TensorGroup184.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian184_23 := by kernel_rfl
private def c3GroupHessian184_33Chunk0 : Poly := [([0,0], 16),([0,4], 40),([0,6], -8),([0,8], 24),([4,4], 40),([4,6], -40),([4,8], 40),([6,6], 16),([6,8], -16),([8,8], 16),([9,9], 40)]
def c3GroupHessian184_33 : Poly := List.flatten [c3GroupHessian184_33Chunk0]
theorem c3GroupHessian184_33_check : sumFast (c3TensorGroup184.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian184_33 := by kernel_rfl
end D4.Secondary
