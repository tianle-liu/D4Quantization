import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup159_det_check : c3TensorGroup159.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 207)) = true := by kernel_rfl
private def c3GroupHessian159_00Chunk0 : Poly := [([0,0], 48),([0,1], 8),([0,5], 8),([0,6], 16),([0,9], 80),([1,1], 16),([1,5], -16),([1,6], 8),([5,5], 16),([5,6], 8),([6,6], 8),([9,9], 40)]
def c3GroupHessian159_00 : Poly := List.flatten [c3GroupHessian159_00Chunk0]
theorem c3GroupHessian159_00_check : sumFast (c3TensorGroup159.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian159_00 := by kernel_rfl
private def c3GroupHessian159_01Chunk0 : Poly := [([0,0], 80),([0,2], 40),([0,7], 40),([0,8], 40),([0,9], 120),([2,9], 40),([7,9], 40),([8,9], 40),([9,9], 40)]
def c3GroupHessian159_01 : Poly := List.flatten [c3GroupHessian159_01Chunk0]
theorem c3GroupHessian159_01_check : sumFast (c3TensorGroup159.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian159_01 := by kernel_rfl
private def c3GroupHessian159_02Chunk0 : Poly := [([0,0], -40),([0,1], 20),([0,5], -24),([0,7], -40),([0,9], -80),([1,3], 20),([1,5], 8),([3,5], -20),([5,5], -16),([5,6], -4),([7,9], -40),([9,9], -40)]
def c3GroupHessian159_02 : Poly := List.flatten [c3GroupHessian159_02Chunk0]
theorem c3GroupHessian159_02_check : sumFast (c3TensorGroup159.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian159_02 := by kernel_rfl
private def c3GroupHessian159_03Chunk0 : Poly := [([0,0], -48),([0,1], -4),([0,5], -4),([0,6], -16),([0,8], -40),([0,9], -80),([1,4], 20),([1,6], -4),([4,5], -20),([5,6], -4),([6,6], -8),([8,9], -40),([9,9], -40)]
def c3GroupHessian159_03 : Poly := List.flatten [c3GroupHessian159_03Chunk0]
theorem c3GroupHessian159_03_check : sumFast (c3TensorGroup159.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian159_03 := by kernel_rfl
private def c3GroupHessian159_11Chunk0 : Poly := [([0,0], 160),([0,2], 160),([0,7], 160),([0,8], 160),([0,9], 160),([2,2], 40),([2,7], 80),([2,8], 80),([2,9], 80),([7,7], 40),([7,8], 80),([7,9], 80),([8,8], 40),([8,9], 80),([9,9], 40)]
def c3GroupHessian159_11 : Poly := List.flatten [c3GroupHessian159_11Chunk0]
theorem c3GroupHessian159_11_check : sumFast (c3TensorGroup159.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian159_11 := by kernel_rfl
private def c3GroupHessian159_12Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -120),([0,8], -40),([0,9], -120),([2,7], -40),([2,9], -40),([7,7], -40),([7,8], -40),([7,9], -80),([8,9], -40),([9,9], -40)]
def c3GroupHessian159_12 : Poly := List.flatten [c3GroupHessian159_12Chunk0]
theorem c3GroupHessian159_12_check : sumFast (c3TensorGroup159.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian159_12 := by kernel_rfl
private def c3GroupHessian159_13Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -40),([0,8], -120),([0,9], -120),([2,8], -40),([2,9], -40),([7,8], -40),([7,9], -40),([8,8], -40),([8,9], -80),([9,9], -40)]
def c3GroupHessian159_13 : Poly := List.flatten [c3GroupHessian159_13Chunk0]
theorem c3GroupHessian159_13_check : sumFast (c3TensorGroup159.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian159_13 := by kernel_rfl
private def c3GroupHessian159_22Chunk0 : Poly := [([0,0], 80),([0,3], 80),([0,5], 40),([0,7], 80),([0,9], 80),([3,3], 40),([3,5], 40),([5,5], 16),([7,7], 40),([7,9], 80),([9,9], 40)]
def c3GroupHessian159_22 : Poly := List.flatten [c3GroupHessian159_22Chunk0]
theorem c3GroupHessian159_22_check : sumFast (c3TensorGroup159.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian159_22 := by kernel_rfl
private def c3GroupHessian159_23Chunk0 : Poly := [([0,0], 40),([0,4], 40),([0,5], 4),([0,7], 40),([0,8], 40),([0,9], 80),([3,4], 40),([4,5], 20),([5,6], 4),([7,8], 40),([7,9], 40),([8,9], 40),([9,9], 40)]
def c3GroupHessian159_23 : Poly := List.flatten [c3GroupHessian159_23Chunk0]
theorem c3GroupHessian159_23_check : sumFast (c3TensorGroup159.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian159_23 := by kernel_rfl
private def c3GroupHessian159_33Chunk0 : Poly := [([0,0], 48),([0,6], 16),([0,8], 80),([0,9], 80),([4,4], 40),([6,6], 8),([8,8], 40),([8,9], 80),([9,9], 40)]
def c3GroupHessian159_33 : Poly := List.flatten [c3GroupHessian159_33Chunk0]
theorem c3GroupHessian159_33_check : sumFast (c3TensorGroup159.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian159_33 := by kernel_rfl
end D4.Secondary
