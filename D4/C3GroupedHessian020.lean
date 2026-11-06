import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup20_det_check : c3TensorGroup20.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 22)) = true := by kernel_rfl
private def c3GroupHessian20_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 16),([0,6], 8),([0,9], 8),([1,1], 40),([5,5], 8),([5,6], 8),([5,9], 8),([6,6], 16),([6,9], -16),([9,9], 16)]
def c3GroupHessian20_00 : Poly := List.flatten [c3GroupHessian20_00Chunk0]
theorem c3GroupHessian20_00_check : sumFast (c3TensorGroup20.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian20_00 := by kernel_rfl
private def c3GroupHessian20_01Chunk0 : Poly := [([0,0], 40),([0,1], 40),([0,2], 40),([0,6], -20),([0,9], 24),([1,2], 40),([5,9], 4),([6,7], -20),([6,8], -20),([6,9], -8),([7,9], 20),([8,9], 20),([9,9], 16)]
def c3GroupHessian20_01 : Poly := List.flatten [c3GroupHessian20_01Chunk0]
theorem c3GroupHessian20_01_check : sumFast (c3TensorGroup20.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian20_01 := by kernel_rfl
private def c3GroupHessian20_02Chunk0 : Poly := [([0,0], -4),([0,3], 40),([0,5], -12),([0,6], 12),([0,9], -16),([1,3], 40),([5,5], -8),([5,6], -4),([5,9], -8),([6,7], 20),([6,9], 8),([7,9], -20),([9,9], -16)]
def c3GroupHessian20_02 : Poly := List.flatten [c3GroupHessian20_02Chunk0]
theorem c3GroupHessian20_02_check : sumFast (c3TensorGroup20.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian20_02 := by kernel_rfl
private def c3GroupHessian20_03Chunk0 : Poly := [([0,0], -4),([0,4], 40),([0,5], -4),([0,9], -16),([1,4], 40),([5,6], -4),([5,9], -4),([6,6], -16),([6,8], 20),([6,9], 16),([8,9], -20),([9,9], -16)]
def c3GroupHessian20_03 : Poly := List.flatten [c3GroupHessian20_03Chunk0]
theorem c3GroupHessian20_03_check : sumFast (c3TensorGroup20.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian20_03 := by kernel_rfl
private def c3GroupHessian20_11Chunk0 : Poly := [([0,0], 80),([0,2], 80),([0,7], 80),([0,8], 80),([0,9], 40),([2,2], 40),([7,7], 40),([7,8], 80),([7,9], 40),([8,8], 40),([8,9], 40),([9,9], 16)]
def c3GroupHessian20_11 : Poly := List.flatten [c3GroupHessian20_11Chunk0]
theorem c3GroupHessian20_11_check : sumFast (c3TensorGroup20.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian20_11 := by kernel_rfl
private def c3GroupHessian20_12Chunk0 : Poly := [([0,0], -20),([0,3], 40),([0,7], -60),([0,8], -20),([0,9], -32),([2,3], 40),([5,9], -4),([7,7], -40),([7,8], -40),([7,9], -40),([8,9], -20),([9,9], -16)]
def c3GroupHessian20_12 : Poly := List.flatten [c3GroupHessian20_12Chunk0]
theorem c3GroupHessian20_12_check : sumFast (c3TensorGroup20.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian20_12 := by kernel_rfl
private def c3GroupHessian20_13Chunk0 : Poly := [([0,0], -20),([0,4], 40),([0,6], 20),([0,7], -20),([0,8], -60),([0,9], -32),([2,4], 40),([6,7], 20),([6,8], 20),([6,9], 8),([7,8], -40),([7,9], -20),([8,8], -40),([8,9], -40),([9,9], -16)]
def c3GroupHessian20_13 : Poly := List.flatten [c3GroupHessian20_13Chunk0]
theorem c3GroupHessian20_13_check : sumFast (c3TensorGroup20.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian20_13 := by kernel_rfl
private def c3GroupHessian20_22Chunk0 : Poly := [([0,0], 16),([0,5], 8),([0,7], 40),([0,9], 24),([3,3], 40),([5,5], 8),([5,9], 8),([7,7], 40),([7,9], 40),([9,9], 16)]
def c3GroupHessian20_22 : Poly := List.flatten [c3GroupHessian20_22Chunk0]
theorem c3GroupHessian20_22_check : sumFast (c3TensorGroup20.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian20_22 := by kernel_rfl
private def c3GroupHessian20_23Chunk0 : Poly := [([0,0], 8),([0,5], 4),([0,6], -12),([0,7], 20),([0,8], 20),([0,9], 24),([3,4], 40),([5,6], 4),([5,9], 4),([6,7], -20),([6,9], -8),([7,8], 40),([7,9], 20),([8,9], 20),([9,9], 16)]
def c3GroupHessian20_23 : Poly := List.flatten [c3GroupHessian20_23Chunk0]
theorem c3GroupHessian20_23_check : sumFast (c3TensorGroup20.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian20_23 := by kernel_rfl
private def c3GroupHessian20_33Chunk0 : Poly := [([0,0], 16),([0,6], -8),([0,8], 40),([0,9], 24),([4,4], 40),([6,6], 16),([6,8], -40),([6,9], -16),([8,8], 40),([8,9], 40),([9,9], 16)]
def c3GroupHessian20_33 : Poly := List.flatten [c3GroupHessian20_33Chunk0]
theorem c3GroupHessian20_33_check : sumFast (c3TensorGroup20.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian20_33 := by kernel_rfl
end D4.Secondary
