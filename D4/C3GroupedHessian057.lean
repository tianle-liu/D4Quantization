import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup57_det_check : c3TensorGroup57.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 79)) = true := by kernel_rfl
private def c3GroupHessian57_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 80),([0,6], 8),([0,9], 8),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 16),([6,9], -16),([9,9], 16)]
def c3GroupHessian57_00 : Poly := List.flatten [c3GroupHessian57_00Chunk0]
theorem c3GroupHessian57_00_check : sumFast (c3TensorGroup57.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian57_00 := by kernel_rfl
private def c3GroupHessian57_01Chunk0 : Poly := [([0,0], 12),([0,2], 8),([0,6], -4),([0,7], 4),([0,8], -40),([0,9], 24),([1,8], -40),([2,6], 4),([2,9], 4),([5,8], -40),([6,7], -8),([6,9], -8),([7,9], 16),([9,9], 16)]
def c3GroupHessian57_01 : Poly := List.flatten [c3GroupHessian57_01Chunk0]
theorem c3GroupHessian57_01_check : sumFast (c3TensorGroup57.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian57_01 := by kernel_rfl
private def c3GroupHessian57_02Chunk0 : Poly := [([0,0], -44),([0,1], -40),([0,5], -80),([0,6], 8),([0,7], -4),([0,9], -20),([1,5], -40),([3,6], 20),([3,9], -20),([5,5], -40),([6,7], 8),([6,9], 8),([7,9], -16),([9,9], -16)]
def c3GroupHessian57_02 : Poly := List.flatten [c3GroupHessian57_02Chunk0]
theorem c3GroupHessian57_02_check : sumFast (c3TensorGroup57.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian57_02 := by kernel_rfl
private def c3GroupHessian57_03Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,4], 40),([0,5], 40),([0,6], -8),([0,8], 40),([0,9], -8),([1,4], 40),([1,8], 40),([4,5], 40),([5,8], 40),([6,6], -16),([6,9], 16),([9,9], -16)]
def c3GroupHessian57_03 : Poly := List.flatten [c3GroupHessian57_03Chunk0]
theorem c3GroupHessian57_03_check : sumFast (c3TensorGroup57.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian57_03 := by kernel_rfl
private def c3GroupHessian57_11Chunk0 : Poly := [([0,0], 32),([0,2], 24),([0,7], 40),([0,9], 40),([2,2], 8),([2,7], 8),([2,9], 8),([7,7], 16),([7,9], 32),([8,8], 40),([9,9], 16)]
def c3GroupHessian57_11 : Poly := List.flatten [c3GroupHessian57_11Chunk0]
theorem c3GroupHessian57_11_check : sumFast (c3TensorGroup57.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian57_11 := by kernel_rfl
private def c3GroupHessian57_12Chunk0 : Poly := [([0,0], -20),([0,2], -4),([0,3], -20),([0,7], -36),([0,8], 40),([0,9], -36),([2,7], -4),([2,9], -4),([3,7], -20),([3,9], -20),([5,8], 40),([7,7], -16),([7,9], -32),([9,9], -16)]
def c3GroupHessian57_12 : Poly := List.flatten [c3GroupHessian57_12Chunk0]
theorem c3GroupHessian57_12_check : sumFast (c3TensorGroup57.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian57_12 := by kernel_rfl
private def c3GroupHessian57_13Chunk0 : Poly := [([0,0], -12),([0,2], -8),([0,6], 4),([0,7], -4),([0,8], -40),([0,9], -24),([2,6], -4),([2,9], -4),([4,8], -40),([6,7], 8),([6,9], 8),([7,9], -16),([8,8], -40),([9,9], -16)]
def c3GroupHessian57_13 : Poly := List.flatten [c3GroupHessian57_13Chunk0]
theorem c3GroupHessian57_13_check : sumFast (c3TensorGroup57.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian57_13 := by kernel_rfl
private def c3GroupHessian57_22Chunk0 : Poly := [([0,0], 56),([0,3], 40),([0,5], 80),([0,7], 32),([0,9], 32),([3,3], 40),([3,7], 40),([3,9], 40),([5,5], 40),([7,7], 16),([7,9], 32),([9,9], 16)]
def c3GroupHessian57_22 : Poly := List.flatten [c3GroupHessian57_22Chunk0]
theorem c3GroupHessian57_22_check : sumFast (c3TensorGroup57.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian57_22 := by kernel_rfl
private def c3GroupHessian57_23Chunk0 : Poly := [([0,0], -36),([0,4], -40),([0,5], -40),([0,6], -8),([0,7], 4),([0,8], -40),([0,9], 20),([3,6], -20),([3,9], 20),([4,5], -40),([5,8], -40),([6,7], -8),([6,9], -8),([7,9], 16),([9,9], 16)]
def c3GroupHessian57_23 : Poly := List.flatten [c3GroupHessian57_23Chunk0]
theorem c3GroupHessian57_23_check : sumFast (c3TensorGroup57.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian57_23 := by kernel_rfl
private def c3GroupHessian57_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 8),([0,8], 80),([0,9], 8),([4,4], 40),([4,8], 80),([6,6], 16),([6,9], -16),([8,8], 40),([9,9], 16)]
def c3GroupHessian57_33 : Poly := List.flatten [c3GroupHessian57_33Chunk0]
theorem c3GroupHessian57_33_check : sumFast (c3TensorGroup57.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian57_33 := by kernel_rfl
end D4.Secondary
