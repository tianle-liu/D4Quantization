import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup73_det_check : c3TensorGroup73.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 99)) = true := by kernel_rfl
private def c3GroupHessian73_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 80),([0,6], 40),([0,9], 32),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 40),([6,9], 40),([9,9], 16)]
def c3GroupHessian73_00 : Poly := List.flatten [c3GroupHessian73_00Chunk0]
theorem c3GroupHessian73_00_check : sumFast (c3TensorGroup73.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian73_00 := by kernel_rfl
private def c3GroupHessian73_01Chunk0 : Poly := [([0,0], 8),([0,2], -8),([0,7], 4),([0,8], -40),([0,9], 24),([1,8], -40),([2,6], -20),([2,9], -8),([5,8], -40),([6,9], 20),([7,9], 4),([9,9], 16)]
def c3GroupHessian73_01 : Poly := List.flatten [c3GroupHessian73_01Chunk0]
theorem c3GroupHessian73_01_check : sumFast (c3TensorGroup73.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian73_01 := by kernel_rfl
private def c3GroupHessian73_02Chunk0 : Poly := [([0,0], -56),([0,1], -40),([0,3], -8),([0,5], -80),([0,6], -20),([0,7], -4),([0,9], -32),([1,5], -40),([3,6], -20),([3,9], -8),([5,5], -40),([6,9], -20),([7,9], -4),([9,9], -16)]
def c3GroupHessian73_02 : Poly := List.flatten [c3GroupHessian73_02Chunk0]
theorem c3GroupHessian73_02_check : sumFast (c3TensorGroup73.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian73_02 := by kernel_rfl
private def c3GroupHessian73_03Chunk0 : Poly := [([0,0], 24),([0,1], 40),([0,4], 40),([0,5], 40),([0,6], -40),([0,8], 40),([0,9], -32),([1,4], 40),([1,8], 40),([4,5], 40),([5,8], 40),([6,6], -40),([6,9], -40),([9,9], -16)]
def c3GroupHessian73_03 : Poly := List.flatten [c3GroupHessian73_03Chunk0]
theorem c3GroupHessian73_03_check : sumFast (c3TensorGroup73.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian73_03 := by kernel_rfl
private def c3GroupHessian73_11Chunk0 : Poly := [([0,0], 16),([0,2], 16),([0,7], 16),([0,9], 16),([2,2], 16),([2,7], 8),([2,9], -16),([7,7], 8),([7,9], 8),([8,8], 40),([9,9], 16)]
def c3GroupHessian73_11 : Poly := List.flatten [c3GroupHessian73_11Chunk0]
theorem c3GroupHessian73_11_check : sumFast (c3TensorGroup73.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian73_11 := by kernel_rfl
private def c3GroupHessian73_12Chunk0 : Poly := [([0,0], -8),([0,2], 8),([0,3], 8),([0,7], -12),([0,8], 40),([0,9], -24),([2,3], 16),([2,7], -4),([2,9], 8),([3,7], 4),([3,9], -8),([5,8], 40),([7,7], -8),([7,9], -8),([9,9], -16)]
def c3GroupHessian73_12 : Poly := List.flatten [c3GroupHessian73_12Chunk0]
theorem c3GroupHessian73_12_check : sumFast (c3TensorGroup73.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian73_12 := by kernel_rfl
private def c3GroupHessian73_13Chunk0 : Poly := [([0,0], -8),([0,2], 8),([0,7], -4),([0,8], -40),([0,9], -24),([2,6], 20),([2,9], 8),([4,8], -40),([6,9], -20),([7,9], -4),([8,8], -40),([9,9], -16)]
def c3GroupHessian73_13 : Poly := List.flatten [c3GroupHessian73_13Chunk0]
theorem c3GroupHessian73_13_check : sumFast (c3TensorGroup73.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian73_13 := by kernel_rfl
private def c3GroupHessian73_22Chunk0 : Poly := [([0,0], 56),([0,3], 16),([0,5], 80),([0,7], 8),([0,9], 32),([3,3], 16),([3,7], -8),([3,9], 16),([5,5], 40),([7,7], 8),([7,9], 8),([9,9], 16)]
def c3GroupHessian73_22 : Poly := List.flatten [c3GroupHessian73_22Chunk0]
theorem c3GroupHessian73_22_check : sumFast (c3TensorGroup73.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian73_22 := by kernel_rfl
private def c3GroupHessian73_23Chunk0 : Poly := [([0,0], -24),([0,3], 8),([0,4], -40),([0,5], -40),([0,6], 20),([0,7], 4),([0,8], -40),([0,9], 32),([3,6], 20),([3,9], 8),([4,5], -40),([5,8], -40),([6,9], 20),([7,9], 4),([9,9], 16)]
def c3GroupHessian73_23 : Poly := List.flatten [c3GroupHessian73_23Chunk0]
theorem c3GroupHessian73_23_check : sumFast (c3TensorGroup73.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian73_23 := by kernel_rfl
private def c3GroupHessian73_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 40),([0,8], 80),([0,9], 32),([4,4], 40),([4,8], 80),([6,6], 40),([6,9], 40),([8,8], 40),([9,9], 16)]
def c3GroupHessian73_33 : Poly := List.flatten [c3GroupHessian73_33Chunk0]
theorem c3GroupHessian73_33_check : sumFast (c3TensorGroup73.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian73_33 := by kernel_rfl
end D4.Secondary
