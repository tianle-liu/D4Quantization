import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup173_det_check : c3TensorGroup173.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 222)) = true := by kernel_rfl
private def c3GroupHessian173_00Chunk0 : Poly := [([0,0], 56),([0,1], 8),([0,5], 40),([0,6], 32),([0,9], 80),([1,1], 8),([1,6], 8),([5,5], 40),([5,6], 40),([6,6], 16),([9,9], 40)]
def c3GroupHessian173_00 : Poly := List.flatten [c3GroupHessian173_00Chunk0]
theorem c3GroupHessian173_00_check : sumFast (c3TensorGroup173.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian173_00 := by kernel_rfl
private def c3GroupHessian173_01Chunk0 : Poly := [([0,0], 80),([0,2], 40),([0,7], 40),([0,8], 40),([0,9], 120),([2,9], 40),([7,9], 40),([8,9], 40),([9,9], 40)]
def c3GroupHessian173_01 : Poly := List.flatten [c3GroupHessian173_01Chunk0]
theorem c3GroupHessian173_01_check : sumFast (c3TensorGroup173.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian173_01 := by kernel_rfl
private def c3GroupHessian173_02Chunk0 : Poly := [([0,0], -48),([0,1], 4),([0,3], -8),([0,5], -40),([0,6], -8),([0,7], -40),([0,9], -80),([1,3], 4),([3,5], -20),([3,6], -8),([5,5], -40),([5,6], -20),([7,9], -40),([9,9], -40)]
def c3GroupHessian173_02 : Poly := List.flatten [c3GroupHessian173_02Chunk0]
theorem c3GroupHessian173_02_check : sumFast (c3TensorGroup173.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian173_02 := by kernel_rfl
private def c3GroupHessian173_03Chunk0 : Poly := [([0,0], -44),([0,4], 4),([0,6], -20),([0,8], -40),([0,9], -80),([1,4], 8),([1,6], -4),([4,6], 4),([5,6], -20),([6,6], -16),([8,9], -40),([9,9], -40)]
def c3GroupHessian173_03 : Poly := List.flatten [c3GroupHessian173_03Chunk0]
theorem c3GroupHessian173_03_check : sumFast (c3TensorGroup173.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian173_03 := by kernel_rfl
private def c3GroupHessian173_11Chunk0 : Poly := [([0,0], 160),([0,2], 160),([0,7], 160),([0,8], 160),([0,9], 160),([2,2], 40),([2,7], 80),([2,8], 80),([2,9], 80),([7,7], 40),([7,8], 80),([7,9], 80),([8,8], 40),([8,9], 80),([9,9], 40)]
def c3GroupHessian173_11 : Poly := List.flatten [c3GroupHessian173_11Chunk0]
theorem c3GroupHessian173_11_check : sumFast (c3TensorGroup173.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian173_11 := by kernel_rfl
private def c3GroupHessian173_12Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -120),([0,8], -40),([0,9], -120),([2,7], -40),([2,9], -40),([7,7], -40),([7,8], -40),([7,9], -80),([8,9], -40),([9,9], -40)]
def c3GroupHessian173_12 : Poly := List.flatten [c3GroupHessian173_12Chunk0]
theorem c3GroupHessian173_12_check : sumFast (c3TensorGroup173.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian173_12 := by kernel_rfl
private def c3GroupHessian173_13Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -40),([0,8], -120),([0,9], -120),([2,8], -40),([2,9], -40),([7,8], -40),([7,9], -40),([8,8], -40),([8,9], -80),([9,9], -40)]
def c3GroupHessian173_13 : Poly := List.flatten [c3GroupHessian173_13Chunk0]
theorem c3GroupHessian173_13_check : sumFast (c3TensorGroup173.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian173_13 := by kernel_rfl
private def c3GroupHessian173_22Chunk0 : Poly := [([0,0], 56),([0,3], 32),([0,5], 40),([0,7], 80),([0,9], 80),([3,3], 16),([3,5], 40),([5,5], 40),([7,7], 40),([7,9], 80),([9,9], 40)]
def c3GroupHessian173_22 : Poly := List.flatten [c3GroupHessian173_22Chunk0]
theorem c3GroupHessian173_22_check : sumFast (c3TensorGroup173.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian173_22 := by kernel_rfl
private def c3GroupHessian173_23Chunk0 : Poly := [([0,0], 36),([0,3], -4),([0,4], 4),([0,6], 8),([0,7], 40),([0,8], 40),([0,9], 80),([3,4], 4),([3,6], 8),([5,6], 20),([7,8], 40),([7,9], 40),([8,9], 40),([9,9], 40)]
def c3GroupHessian173_23 : Poly := List.flatten [c3GroupHessian173_23Chunk0]
theorem c3GroupHessian173_23_check : sumFast (c3TensorGroup173.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian173_23 := by kernel_rfl
private def c3GroupHessian173_33Chunk0 : Poly := [([0,0], 48),([0,6], 8),([0,8], 80),([0,9], 80),([4,4], 8),([4,6], -8),([6,6], 16),([8,8], 40),([8,9], 80),([9,9], 40)]
def c3GroupHessian173_33 : Poly := List.flatten [c3GroupHessian173_33Chunk0]
theorem c3GroupHessian173_33_check : sumFast (c3TensorGroup173.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian173_33 := by kernel_rfl
end D4.Secondary
