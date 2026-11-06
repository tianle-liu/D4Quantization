import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup80_det_check : c3TensorGroup80.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 108)) = true := by kernel_rfl
private def c3GroupHessian80_00Chunk0 : Poly := [([0,0], 160),([0,1], 160),([0,5], 160),([0,6], 160),([0,9], 160),([1,1], 40),([1,5], 80),([1,6], 80),([1,9], 80),([5,5], 40),([5,6], 80),([5,9], 80),([6,6], 40),([6,9], 80),([9,9], 40)]
def c3GroupHessian80_00 : Poly := List.flatten [c3GroupHessian80_00Chunk0]
theorem c3GroupHessian80_00_check : sumFast (c3TensorGroup80.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian80_00 := by kernel_rfl
private def c3GroupHessian80_01Chunk0 : Poly := [([0,0], 80),([0,1], 40),([0,5], 40),([0,6], 40),([0,9], 120),([1,9], 40),([5,9], 40),([6,9], 40),([9,9], 40)]
def c3GroupHessian80_01 : Poly := List.flatten [c3GroupHessian80_01Chunk0]
theorem c3GroupHessian80_01_check : sumFast (c3TensorGroup80.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian80_01 := by kernel_rfl
private def c3GroupHessian80_02Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -120),([0,6], -40),([0,9], -120),([1,5], -40),([1,9], -40),([5,5], -40),([5,6], -40),([5,9], -80),([6,9], -40),([9,9], -40)]
def c3GroupHessian80_02 : Poly := List.flatten [c3GroupHessian80_02Chunk0]
theorem c3GroupHessian80_02_check : sumFast (c3TensorGroup80.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian80_02 := by kernel_rfl
private def c3GroupHessian80_03Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -40),([0,6], -120),([0,9], -120),([1,6], -40),([1,9], -40),([5,6], -40),([5,9], -40),([6,6], -40),([6,9], -80),([9,9], -40)]
def c3GroupHessian80_03 : Poly := List.flatten [c3GroupHessian80_03Chunk0]
theorem c3GroupHessian80_03_check : sumFast (c3TensorGroup80.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian80_03 := by kernel_rfl
private def c3GroupHessian80_11Chunk0 : Poly := [([0,0], 48),([0,2], 16),([0,7], 8),([0,8], 8),([0,9], 80),([2,2], 8),([2,7], 8),([2,8], 8),([7,7], 16),([7,8], -16),([8,8], 16),([9,9], 40)]
def c3GroupHessian80_11 : Poly := List.flatten [c3GroupHessian80_11Chunk0]
theorem c3GroupHessian80_11_check : sumFast (c3TensorGroup80.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian80_11 := by kernel_rfl
private def c3GroupHessian80_12Chunk0 : Poly := [([0,0], -40),([0,5], -40),([0,7], -24),([0,8], 20),([0,9], -80),([2,7], -4),([3,7], -20),([3,8], 20),([5,9], -40),([7,7], -16),([7,8], 8),([9,9], -40)]
def c3GroupHessian80_12 : Poly := List.flatten [c3GroupHessian80_12Chunk0]
theorem c3GroupHessian80_12_check : sumFast (c3TensorGroup80.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian80_12 := by kernel_rfl
private def c3GroupHessian80_13Chunk0 : Poly := [([0,0], -40),([0,4], 8),([0,6], -40),([0,7], 20),([0,8], -24),([0,9], -80),([2,4], 8),([2,8], -4),([4,7], 4),([4,8], 4),([6,9], -40),([7,8], 8),([8,8], -16),([9,9], -40)]
def c3GroupHessian80_13 : Poly := List.flatten [c3GroupHessian80_13Chunk0]
theorem c3GroupHessian80_13_check : sumFast (c3TensorGroup80.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian80_13 := by kernel_rfl
private def c3GroupHessian80_22Chunk0 : Poly := [([0,0], 80),([0,3], 80),([0,5], 80),([0,7], 40),([0,9], 80),([3,3], 40),([3,7], 40),([5,5], 40),([5,9], 80),([7,7], 16),([9,9], 40)]
def c3GroupHessian80_22 : Poly := List.flatten [c3GroupHessian80_22Chunk0]
theorem c3GroupHessian80_22_check : sumFast (c3TensorGroup80.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian80_22 := by kernel_rfl
private def c3GroupHessian80_23Chunk0 : Poly := [([0,3], -40),([0,5], 40),([0,6], 40),([0,7], -20),([0,8], -20),([0,9], 80),([3,8], -20),([4,7], -4),([5,6], 40),([5,9], 40),([6,9], 40),([7,8], -8),([9,9], 40)]
def c3GroupHessian80_23 : Poly := List.flatten [c3GroupHessian80_23Chunk0]
theorem c3GroupHessian80_23_check : sumFast (c3TensorGroup80.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian80_23 := by kernel_rfl
private def c3GroupHessian80_33Chunk0 : Poly := [([0,0], 80),([0,6], 80),([0,8], 40),([0,9], 80),([4,4], 8),([4,8], -8),([6,6], 40),([6,9], 80),([8,8], 16),([9,9], 40)]
def c3GroupHessian80_33 : Poly := List.flatten [c3GroupHessian80_33Chunk0]
theorem c3GroupHessian80_33_check : sumFast (c3TensorGroup80.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian80_33 := by kernel_rfl
end D4.Secondary
