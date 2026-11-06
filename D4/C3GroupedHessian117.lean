import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup117_det_check : c3TensorGroup117.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 154)) = true := by kernel_rfl
private def c3GroupHessian117_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,6], 80),([0,9], 48),([1,1], 40),([1,6], 80),([1,9], 40),([5,5], 40),([6,6], 40),([6,9], 40),([9,9], 16)]
def c3GroupHessian117_00 : Poly := List.flatten [c3GroupHessian117_00Chunk0]
theorem c3GroupHessian117_00_check : sumFast (c3TensorGroup117.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian117_00 := by kernel_rfl
private def c3GroupHessian117_01Chunk0 : Poly := [([0,0], 8),([0,5], -40),([0,7], -16),([0,9], 28),([1,7], -20),([1,9], 20),([2,5], -40),([5,8], -40),([6,7], -20),([6,9], 20),([7,9], -8),([9,9], 16)]
def c3GroupHessian117_01 : Poly := List.flatten [c3GroupHessian117_01Chunk0]
theorem c3GroupHessian117_01_check : sumFast (c3TensorGroup117.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian117_01 := by kernel_rfl
private def c3GroupHessian117_02Chunk0 : Poly := [([0,0], -8),([0,5], -40),([0,7], 16),([0,9], -28),([1,7], 20),([1,9], -20),([3,5], -40),([5,5], -40),([6,7], 20),([6,9], -20),([7,9], 8),([9,9], -16)]
def c3GroupHessian117_02 : Poly := List.flatten [c3GroupHessian117_02Chunk0]
theorem c3GroupHessian117_02_check : sumFast (c3TensorGroup117.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian117_02 := by kernel_rfl
private def c3GroupHessian117_03Chunk0 : Poly := [([0,0], -40),([0,1], -40),([0,4], 8),([0,5], 40),([0,6], -80),([0,9], -44),([1,6], -40),([1,9], -20),([4,9], 4),([5,8], 40),([6,6], -40),([6,9], -40),([9,9], -16)]
def c3GroupHessian117_03 : Poly := List.flatten [c3GroupHessian117_03Chunk0]
theorem c3GroupHessian117_03_check : sumFast (c3TensorGroup117.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian117_03 := by kernel_rfl
private def c3GroupHessian117_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 8),([0,8], 80),([0,9], 8),([2,2], 40),([2,8], 80),([7,7], 16),([7,9], -16),([8,8], 40),([9,9], 16)]
def c3GroupHessian117_11 : Poly := List.flatten [c3GroupHessian117_11Chunk0]
theorem c3GroupHessian117_11_check : sumFast (c3TensorGroup117.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian117_11 := by kernel_rfl
private def c3GroupHessian117_12Chunk0 : Poly := [([0,0], 32),([0,2], 40),([0,3], 40),([0,5], 40),([0,7], -8),([0,8], 40),([0,9], -8),([2,3], 40),([2,5], 40),([3,8], 40),([5,8], 40),([7,7], -16),([7,9], 16),([9,9], -16)]
def c3GroupHessian117_12 : Poly := List.flatten [c3GroupHessian117_12Chunk0]
theorem c3GroupHessian117_12_check : sumFast (c3TensorGroup117.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian117_12 := by kernel_rfl
private def c3GroupHessian117_13Chunk0 : Poly := [([0,0], -40),([0,2], -40),([0,4], 8),([0,7], 20),([0,8], -80),([0,9], -24),([2,8], -40),([4,7], 4),([4,9], 4),([6,7], 20),([6,9], -20),([7,9], 8),([8,8], -40),([9,9], -16)]
def c3GroupHessian117_13 : Poly := List.flatten [c3GroupHessian117_13Chunk0]
theorem c3GroupHessian117_13_check : sumFast (c3TensorGroup117.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian117_13 := by kernel_rfl
private def c3GroupHessian117_22Chunk0 : Poly := [([0,0], 48),([0,3], 80),([0,5], 80),([0,7], 8),([0,9], 8),([3,3], 40),([3,5], 80),([5,5], 40),([7,7], 16),([7,9], -16),([9,9], 16)]
def c3GroupHessian117_22 : Poly := List.flatten [c3GroupHessian117_22Chunk0]
theorem c3GroupHessian117_22_check : sumFast (c3TensorGroup117.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian117_22 := by kernel_rfl
private def c3GroupHessian117_23Chunk0 : Poly := [([0,0], -40),([0,3], -40),([0,4], -8),([0,5], -40),([0,7], -20),([0,8], -40),([0,9], 24),([3,8], -40),([4,7], -4),([4,9], -4),([5,8], -40),([6,7], -20),([6,9], 20),([7,9], -8),([9,9], 16)]
def c3GroupHessian117_23 : Poly := List.flatten [c3GroupHessian117_23Chunk0]
theorem c3GroupHessian117_23_check : sumFast (c3TensorGroup117.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian117_23 := by kernel_rfl
private def c3GroupHessian117_33Chunk0 : Poly := [([0,0], 80),([0,6], 80),([0,8], 80),([0,9], 40),([4,4], 8),([4,9], -8),([6,6], 40),([6,9], 40),([8,8], 40),([9,9], 16)]
def c3GroupHessian117_33 : Poly := List.flatten [c3GroupHessian117_33Chunk0]
theorem c3GroupHessian117_33_check : sumFast (c3TensorGroup117.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian117_33 := by kernel_rfl
end D4.Secondary
