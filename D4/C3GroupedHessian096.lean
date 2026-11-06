import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup96_det_check : c3TensorGroup96.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 126)) = true := by kernel_rfl
private def c3GroupHessian96_00Chunk0 : Poly := [([0,0], 320),([0,1], 320),([0,5], 320),([0,6], 320),([0,9], 320),([1,1], 80),([1,5], 160),([1,6], 160),([1,9], 160),([5,5], 80),([5,6], 160),([5,9], 160),([6,6], 80),([6,9], 160),([9,9], 80)]
def c3GroupHessian96_00 : Poly := List.flatten [c3GroupHessian96_00Chunk0]
theorem c3GroupHessian96_00_check : sumFast (c3TensorGroup96.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian96_00 := by kernel_rfl
private def c3GroupHessian96_01Chunk0 : Poly := [([0,0], 160),([0,1], 80),([0,5], 80),([0,6], 80),([0,9], 240),([1,9], 80),([5,9], 80),([6,9], 80),([9,9], 80)]
def c3GroupHessian96_01 : Poly := List.flatten [c3GroupHessian96_01Chunk0]
theorem c3GroupHessian96_01_check : sumFast (c3TensorGroup96.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian96_01 := by kernel_rfl
private def c3GroupHessian96_02Chunk0 : Poly := [([0,0], -160),([0,1], -80),([0,5], -240),([0,6], -80),([0,9], -240),([1,5], -80),([1,9], -80),([5,5], -80),([5,6], -80),([5,9], -160),([6,9], -80),([9,9], -80)]
def c3GroupHessian96_02 : Poly := List.flatten [c3GroupHessian96_02Chunk0]
theorem c3GroupHessian96_02_check : sumFast (c3TensorGroup96.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian96_02 := by kernel_rfl
private def c3GroupHessian96_03Chunk0 : Poly := [([0,0], -160),([0,1], -80),([0,5], -80),([0,6], -240),([0,9], -240),([1,6], -80),([1,9], -80),([5,6], -80),([5,9], -80),([6,6], -80),([6,9], -160),([9,9], -80)]
def c3GroupHessian96_03 : Poly := List.flatten [c3GroupHessian96_03Chunk0]
theorem c3GroupHessian96_03_check : sumFast (c3TensorGroup96.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian96_03 := by kernel_rfl
private def c3GroupHessian96_11Chunk0 : Poly := [([0,0], 112),([0,2], 64),([0,7], -8),([0,8], 64),([0,9], 160),([2,2], 32),([2,7], -8),([2,8], 64),([7,7], 24),([7,8], -8),([8,8], 32),([9,9], 80)]
def c3GroupHessian96_11 : Poly := List.flatten [c3GroupHessian96_11Chunk0]
theorem c3GroupHessian96_11_check : sumFast (c3TensorGroup96.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian96_11 := by kernel_rfl
private def c3GroupHessian96_12Chunk0 : Poly := [([0,0], -48),([0,2], 32),([0,3], 32),([0,5], -80),([0,8], 32),([0,9], -160),([2,3], 32),([2,7], 4),([3,7], -4),([3,8], 32),([5,9], -80),([7,7], -24),([7,8], 4),([9,9], -80)]
def c3GroupHessian96_12 : Poly := List.flatten [c3GroupHessian96_12Chunk0]
theorem c3GroupHessian96_12_check : sumFast (c3TensorGroup96.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian96_12 := by kernel_rfl
private def c3GroupHessian96_13Chunk0 : Poly := [([0,0], -112),([0,2], -32),([0,4], -4),([0,6], -80),([0,7], 4),([0,8], -64),([0,9], -160),([2,4], -4),([2,8], -32),([4,7], 8),([4,8], -4),([6,9], -80),([7,8], 4),([8,8], -32),([9,9], -80)]
def c3GroupHessian96_13 : Poly := List.flatten [c3GroupHessian96_13Chunk0]
theorem c3GroupHessian96_13_check : sumFast (c3TensorGroup96.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian96_13 := by kernel_rfl
private def c3GroupHessian96_22Chunk0 : Poly := [([0,0], 112),([0,3], 64),([0,5], 160),([0,7], 8),([0,9], 160),([3,3], 32),([3,7], 8),([5,5], 80),([5,9], 160),([7,7], 24),([9,9], 80)]
def c3GroupHessian96_22 : Poly := List.flatten [c3GroupHessian96_22Chunk0]
theorem c3GroupHessian96_22_check : sumFast (c3TensorGroup96.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian96_22 := by kernel_rfl
private def c3GroupHessian96_23Chunk0 : Poly := [([0,0], 48),([0,3], -32),([0,4], -4),([0,5], 80),([0,6], 80),([0,7], -4),([0,8], -32),([0,9], 160),([3,4], -4),([3,8], -32),([4,7], -8),([5,6], 80),([5,9], 80),([6,9], 80),([7,8], -4),([9,9], 80)]
def c3GroupHessian96_23 : Poly := List.flatten [c3GroupHessian96_23Chunk0]
theorem c3GroupHessian96_23_check : sumFast (c3TensorGroup96.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian96_23 := by kernel_rfl
private def c3GroupHessian96_33Chunk0 : Poly := [([0,0], 112),([0,4], 8),([0,6], 160),([0,8], 64),([0,9], 160),([4,4], 24),([4,8], 8),([6,6], 80),([6,9], 160),([8,8], 32),([9,9], 80)]
def c3GroupHessian96_33 : Poly := List.flatten [c3GroupHessian96_33Chunk0]
theorem c3GroupHessian96_33_check : sumFast (c3TensorGroup96.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian96_33 := by kernel_rfl
end D4.Secondary
