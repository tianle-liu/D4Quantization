import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup34_det_check : c3TensorGroup34.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 51)) = true := by kernel_rfl
private def c3GroupHessian34_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 40),([0,6], 80),([0,9], -16),([1,1], 40),([1,6], 80),([5,5], 40),([5,9], -40),([6,6], 40),([9,9], 16)]
def c3GroupHessian34_00 : Poly := List.flatten [c3GroupHessian34_00Chunk0]
theorem c3GroupHessian34_00_check : sumFast (c3TensorGroup34.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian34_00 := by kernel_rfl
private def c3GroupHessian34_01Chunk0 : Poly := [([0,0], 8),([0,2], 4),([0,7], -40),([0,8], -8),([1,7], -40),([2,9], 4),([5,8], -20),([5,9], -20),([6,7], -40),([8,9], 16),([9,9], 16)]
def c3GroupHessian34_01 : Poly := List.flatten [c3GroupHessian34_01Chunk0]
theorem c3GroupHessian34_01_check : sumFast (c3TensorGroup34.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian34_01 := by kernel_rfl
private def c3GroupHessian34_02Chunk0 : Poly := [([0,0], 24),([0,1], 40),([0,3], 40),([0,5], -40),([0,6], 40),([0,7], 40),([0,9], 16),([1,3], 40),([1,7], 40),([3,6], 40),([5,5], -40),([5,9], 40),([6,7], 40),([9,9], -16)]
def c3GroupHessian34_02 : Poly := List.flatten [c3GroupHessian34_02Chunk0]
theorem c3GroupHessian34_02_check : sumFast (c3TensorGroup34.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian34_02 := by kernel_rfl
private def c3GroupHessian34_03Chunk0 : Poly := [([0,0], -32),([0,1], -40),([0,4], 20),([0,5], 20),([0,6], -80),([0,8], 8),([0,9], -8),([1,6], -40),([4,5], 40),([4,9], -20),([5,8], 20),([5,9], 20),([6,6], -40),([8,9], -16),([9,9], -16)]
def c3GroupHessian34_03 : Poly := List.flatten [c3GroupHessian34_03Chunk0]
theorem c3GroupHessian34_03_check : sumFast (c3TensorGroup34.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian34_03 := by kernel_rfl
private def c3GroupHessian34_11Chunk0 : Poly := [([0,0], 16),([0,2], 16),([0,8], 16),([0,9], 16),([2,2], 8),([2,8], 8),([2,9], 8),([7,7], 40),([8,8], 16),([8,9], 32),([9,9], 16)]
def c3GroupHessian34_11 : Poly := List.flatten [c3GroupHessian34_11Chunk0]
theorem c3GroupHessian34_11_check : sumFast (c3TensorGroup34.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian34_11 := by kernel_rfl
private def c3GroupHessian34_12Chunk0 : Poly := [([0,0], -8),([0,2], -4),([0,7], -40),([0,8], 8),([2,9], -4),([3,7], -40),([5,8], 20),([5,9], 20),([7,7], -40),([8,9], -16),([9,9], -16)]
def c3GroupHessian34_12 : Poly := List.flatten [c3GroupHessian34_12Chunk0]
theorem c3GroupHessian34_12_check : sumFast (c3TensorGroup34.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian34_12 := by kernel_rfl
private def c3GroupHessian34_13Chunk0 : Poly := [([0,0], -8),([0,2], -4),([0,7], 40),([0,8], -24),([0,9], -24),([2,8], -4),([2,9], -4),([4,8], -20),([4,9], -20),([6,7], 40),([8,8], -16),([8,9], -32),([9,9], -16)]
def c3GroupHessian34_13 : Poly := List.flatten [c3GroupHessian34_13Chunk0]
theorem c3GroupHessian34_13_check : sumFast (c3TensorGroup34.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian34_13 := by kernel_rfl
private def c3GroupHessian34_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 40),([0,7], 80),([0,9], -16),([3,3], 40),([3,7], 80),([5,5], 40),([5,9], -40),([7,7], 40),([9,9], 16)]
def c3GroupHessian34_22 : Poly := List.flatten [c3GroupHessian34_22Chunk0]
theorem c3GroupHessian34_22_check : sumFast (c3TensorGroup34.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian34_22 := by kernel_rfl
private def c3GroupHessian34_23Chunk0 : Poly := [([0,0], -48),([0,3], -40),([0,4], -20),([0,5], -20),([0,6], -40),([0,7], -40),([0,8], -8),([0,9], 8),([3,6], -40),([4,5], -40),([4,9], 20),([5,8], -20),([5,9], -20),([6,7], -40),([8,9], 16),([9,9], 16)]
def c3GroupHessian34_23 : Poly := List.flatten [c3GroupHessian34_23Chunk0]
theorem c3GroupHessian34_23_check : sumFast (c3TensorGroup34.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian34_23 := by kernel_rfl
private def c3GroupHessian34_33Chunk0 : Poly := [([0,0], 56),([0,4], 40),([0,6], 80),([0,8], 32),([0,9], 32),([4,4], 40),([4,8], 40),([4,9], 40),([6,6], 40),([8,8], 16),([8,9], 32),([9,9], 16)]
def c3GroupHessian34_33 : Poly := List.flatten [c3GroupHessian34_33Chunk0]
theorem c3GroupHessian34_33_check : sumFast (c3TensorGroup34.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian34_33 := by kernel_rfl
end D4.Secondary
