import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup55_det_check : c3TensorGroup55.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 77)) = true := by kernel_rfl
private def c3GroupHessian55_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 80),([0,6], 40),([0,9], -16),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 40),([6,9], -40),([9,9], 16)]
def c3GroupHessian55_00 : Poly := List.flatten [c3GroupHessian55_00Chunk0]
theorem c3GroupHessian55_00_check : sumFast (c3TensorGroup55.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian55_00 := by kernel_rfl
private def c3GroupHessian55_01Chunk0 : Poly := [([0,0], 8),([0,2], 4),([0,7], -8),([0,8], -40),([1,8], -40),([2,9], 4),([5,8], -40),([6,7], -20),([6,9], -20),([7,9], 16),([9,9], 16)]
def c3GroupHessian55_01 : Poly := List.flatten [c3GroupHessian55_01Chunk0]
theorem c3GroupHessian55_01_check : sumFast (c3TensorGroup55.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian55_01 := by kernel_rfl
private def c3GroupHessian55_02Chunk0 : Poly := [([0,0], -32),([0,1], -40),([0,3], 20),([0,5], -80),([0,6], 20),([0,7], 8),([0,9], -8),([1,5], -40),([3,6], 40),([3,9], -20),([5,5], -40),([6,7], 20),([6,9], 20),([7,9], -16),([9,9], -16)]
def c3GroupHessian55_02 : Poly := List.flatten [c3GroupHessian55_02Chunk0]
theorem c3GroupHessian55_02_check : sumFast (c3TensorGroup55.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian55_02 := by kernel_rfl
private def c3GroupHessian55_03Chunk0 : Poly := [([0,0], 24),([0,1], 40),([0,4], 40),([0,5], 40),([0,6], -40),([0,8], 40),([0,9], 16),([1,4], 40),([1,8], 40),([4,5], 40),([5,8], 40),([6,6], -40),([6,9], 40),([9,9], -16)]
def c3GroupHessian55_03 : Poly := List.flatten [c3GroupHessian55_03Chunk0]
theorem c3GroupHessian55_03_check : sumFast (c3TensorGroup55.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian55_03 := by kernel_rfl
private def c3GroupHessian55_11Chunk0 : Poly := [([0,0], 16),([0,2], 16),([0,7], 16),([0,9], 16),([2,2], 8),([2,7], 8),([2,9], 8),([7,7], 16),([7,9], 32),([8,8], 40),([9,9], 16)]
def c3GroupHessian55_11 : Poly := List.flatten [c3GroupHessian55_11Chunk0]
theorem c3GroupHessian55_11_check : sumFast (c3TensorGroup55.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian55_11 := by kernel_rfl
private def c3GroupHessian55_12Chunk0 : Poly := [([0,0], -8),([0,2], -4),([0,7], -24),([0,8], 40),([0,9], -24),([2,7], -4),([2,9], -4),([3,7], -20),([3,9], -20),([5,8], 40),([7,7], -16),([7,9], -32),([9,9], -16)]
def c3GroupHessian55_12 : Poly := List.flatten [c3GroupHessian55_12Chunk0]
theorem c3GroupHessian55_12_check : sumFast (c3TensorGroup55.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian55_12 := by kernel_rfl
private def c3GroupHessian55_13Chunk0 : Poly := [([0,0], -8),([0,2], -4),([0,7], 8),([0,8], -40),([2,9], -4),([4,8], -40),([6,7], 20),([6,9], 20),([7,9], -16),([8,8], -40),([9,9], -16)]
def c3GroupHessian55_13 : Poly := List.flatten [c3GroupHessian55_13Chunk0]
theorem c3GroupHessian55_13_check : sumFast (c3TensorGroup55.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian55_13 := by kernel_rfl
private def c3GroupHessian55_22Chunk0 : Poly := [([0,0], 56),([0,3], 40),([0,5], 80),([0,7], 32),([0,9], 32),([3,3], 40),([3,7], 40),([3,9], 40),([5,5], 40),([7,7], 16),([7,9], 32),([9,9], 16)]
def c3GroupHessian55_22 : Poly := List.flatten [c3GroupHessian55_22Chunk0]
theorem c3GroupHessian55_22_check : sumFast (c3TensorGroup55.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian55_22 := by kernel_rfl
private def c3GroupHessian55_23Chunk0 : Poly := [([0,0], -48),([0,3], -20),([0,4], -40),([0,5], -40),([0,6], -20),([0,7], -8),([0,8], -40),([0,9], 8),([3,6], -40),([3,9], 20),([4,5], -40),([5,8], -40),([6,7], -20),([6,9], -20),([7,9], 16),([9,9], 16)]
def c3GroupHessian55_23 : Poly := List.flatten [c3GroupHessian55_23Chunk0]
theorem c3GroupHessian55_23_check : sumFast (c3TensorGroup55.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian55_23 := by kernel_rfl
private def c3GroupHessian55_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 40),([0,8], 80),([0,9], -16),([4,4], 40),([4,8], 80),([6,6], 40),([6,9], -40),([8,8], 40),([9,9], 16)]
def c3GroupHessian55_33 : Poly := List.flatten [c3GroupHessian55_33Chunk0]
theorem c3GroupHessian55_33_check : sumFast (c3TensorGroup55.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian55_33 := by kernel_rfl
end D4.Secondary
