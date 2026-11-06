import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup182_det_check : c3TensorGroup182.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 233)) = true := by kernel_rfl
private def c3GroupHessian182_00Chunk0 : Poly := [([0,0], 112),([0,1], 80),([0,5], 160),([0,6], -8),([0,9], 160),([1,1], 80),([1,6], -40),([5,5], 80),([5,9], 160),([6,6], 24),([9,9], 80)]
def c3GroupHessian182_00 : Poly := List.flatten [c3GroupHessian182_00Chunk0]
theorem c3GroupHessian182_00_check : sumFast (c3TensorGroup182.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian182_00 := by kernel_rfl
private def c3GroupHessian182_01Chunk0 : Poly := [([0,0], 112),([0,1], 40),([0,2], 40),([0,5], 80),([0,6], -4),([0,7], 80),([0,8], -4),([0,9], 160),([1,2], 80),([1,8], -20),([2,6], -20),([5,7], 80),([5,9], 80),([6,8], 8),([7,9], 80),([9,9], 80)]
def c3GroupHessian182_01 : Poly := List.flatten [c3GroupHessian182_01Chunk0]
theorem c3GroupHessian182_01_check : sumFast (c3TensorGroup182.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian182_01 := by kernel_rfl
private def c3GroupHessian182_02Chunk0 : Poly := [([0,0], -160),([0,3], -80),([0,5], -240),([0,7], -80),([0,9], -240),([3,5], -80),([3,9], -80),([5,5], -80),([5,7], -80),([5,9], -160),([7,9], -80),([9,9], -80)]
def c3GroupHessian182_02 : Poly := List.flatten [c3GroupHessian182_02Chunk0]
theorem c3GroupHessian182_02_check : sumFast (c3TensorGroup182.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian182_02 := by kernel_rfl
private def c3GroupHessian182_03Chunk0 : Poly := [([0,0], 8),([0,1], 40),([0,4], 40),([0,6], -12),([0,8], 4),([0,9], -80),([1,4], 80),([1,6], 20),([1,8], 20),([4,6], -20),([5,9], -80),([6,6], -24),([6,8], -8),([9,9], -80)]
def c3GroupHessian182_03 : Poly := List.flatten [c3GroupHessian182_03Chunk0]
theorem c3GroupHessian182_03_check : sumFast (c3TensorGroup182.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian182_03 := by kernel_rfl
private def c3GroupHessian182_11Chunk0 : Poly := [([0,0], 112),([0,2], 80),([0,7], 160),([0,8], -8),([0,9], 160),([2,2], 80),([2,8], -40),([7,7], 80),([7,9], 160),([8,8], 24),([9,9], 80)]
def c3GroupHessian182_11 : Poly := List.flatten [c3GroupHessian182_11Chunk0]
theorem c3GroupHessian182_11_check : sumFast (c3TensorGroup182.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian182_11 := by kernel_rfl
private def c3GroupHessian182_12Chunk0 : Poly := [([0,0], -160),([0,3], -80),([0,5], -80),([0,7], -240),([0,9], -240),([3,7], -80),([3,9], -80),([5,7], -80),([5,9], -80),([7,7], -80),([7,9], -160),([9,9], -80)]
def c3GroupHessian182_12 : Poly := List.flatten [c3GroupHessian182_12Chunk0]
theorem c3GroupHessian182_12_check : sumFast (c3TensorGroup182.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian182_12 := by kernel_rfl
private def c3GroupHessian182_13Chunk0 : Poly := [([0,0], 8),([0,2], 40),([0,4], 40),([0,6], 4),([0,8], -12),([0,9], -80),([2,4], 80),([2,6], 20),([2,8], 20),([4,8], -20),([6,8], -8),([7,9], -80),([8,8], -24),([9,9], -80)]
def c3GroupHessian182_13 : Poly := List.flatten [c3GroupHessian182_13Chunk0]
theorem c3GroupHessian182_13_check : sumFast (c3TensorGroup182.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian182_13 := by kernel_rfl
private def c3GroupHessian182_22Chunk0 : Poly := [([0,0], 320),([0,3], 320),([0,5], 320),([0,7], 320),([0,9], 320),([3,3], 80),([3,5], 160),([3,7], 160),([3,9], 160),([5,5], 80),([5,7], 160),([5,9], 160),([7,7], 80),([7,9], 160),([9,9], 80)]
def c3GroupHessian182_22 : Poly := List.flatten [c3GroupHessian182_22Chunk0]
theorem c3GroupHessian182_22_check : sumFast (c3TensorGroup182.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian182_22 := by kernel_rfl
private def c3GroupHessian182_23Chunk0 : Poly := [([0,9], 160),([3,9], 80),([5,9], 80),([7,9], 80),([9,9], 80)]
def c3GroupHessian182_23 : Poly := List.flatten [c3GroupHessian182_23Chunk0]
theorem c3GroupHessian182_23_check : sumFast (c3TensorGroup182.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian182_23 := by kernel_rfl
private def c3GroupHessian182_33Chunk0 : Poly := [([0,0], 32),([0,4], 80),([0,6], 32),([0,8], 32),([4,4], 80),([4,6], 40),([4,8], 40),([6,6], 24),([6,8], 16),([8,8], 24),([9,9], 80)]
def c3GroupHessian182_33 : Poly := List.flatten [c3GroupHessian182_33Chunk0]
theorem c3GroupHessian182_33_check : sumFast (c3TensorGroup182.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian182_33 := by kernel_rfl
end D4.Secondary
