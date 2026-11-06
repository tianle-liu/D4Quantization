import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup47_det_check : c3TensorGroup47.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 65)) = true := by kernel_rfl
private def c3GroupHessian47_00Chunk0 : Poly := [([0,0], 104),([0,1], 160),([0,5], 48),([0,6], 160),([0,9], 48),([1,1], 80),([1,6], 160),([5,5], 24),([5,9], 48),([6,6], 80),([9,9], 24)]
def c3GroupHessian47_00 : Poly := List.flatten [c3GroupHessian47_00Chunk0]
theorem c3GroupHessian47_00_check : sumFast (c3TensorGroup47.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian47_00 := by kernel_rfl
private def c3GroupHessian47_01Chunk0 : Poly := [([0,0], 16),([0,2], 8),([0,5], 16),([0,7], -80),([0,8], -4),([0,9], 40),([1,7], -80),([2,5], 8),([2,9], 8),([5,8], -4),([5,9], 24),([6,7], -80),([8,9], -4),([9,9], 24)]
def c3GroupHessian47_01 : Poly := List.flatten [c3GroupHessian47_01Chunk0]
theorem c3GroupHessian47_01_check : sumFast (c3TensorGroup47.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian47_01 := by kernel_rfl
private def c3GroupHessian47_02Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,3], 80),([0,5], -48),([0,6], 80),([0,7], 80),([0,9], -48),([1,3], 80),([1,7], 80),([3,6], 80),([5,5], -24),([5,9], -48),([6,7], 80),([9,9], -24)]
def c3GroupHessian47_02 : Poly := List.flatten [c3GroupHessian47_02Chunk0]
theorem c3GroupHessian47_02_check : sumFast (c3TensorGroup47.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian47_02 := by kernel_rfl
private def c3GroupHessian47_03Chunk0 : Poly := [([0,0], -88),([0,1], -80),([0,4], 8),([0,5], -8),([0,6], -160),([0,8], 4),([0,9], -32),([1,6], -80),([4,5], 8),([4,9], 8),([5,8], 4),([5,9], -24),([6,6], -80),([8,9], 4),([9,9], -24)]
def c3GroupHessian47_03 : Poly := List.flatten [c3GroupHessian47_03Chunk0]
theorem c3GroupHessian47_03_check : sumFast (c3TensorGroup47.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian47_03 := by kernel_rfl
private def c3GroupHessian47_11Chunk0 : Poly := [([0,0], 32),([0,2], 32),([0,8], 32),([0,9], 32),([2,2], 24),([2,8], -8),([2,9], 16),([7,7], 80),([8,8], 32),([8,9], -8),([9,9], 24)]
def c3GroupHessian47_11 : Poly := List.flatten [c3GroupHessian47_11Chunk0]
theorem c3GroupHessian47_11_check : sumFast (c3TensorGroup47.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian47_11 := by kernel_rfl
private def c3GroupHessian47_12Chunk0 : Poly := [([0,0], -16),([0,2], -8),([0,5], -16),([0,7], -80),([0,8], 4),([0,9], -40),([2,5], -8),([2,9], -8),([3,7], -80),([5,8], 4),([5,9], -24),([7,7], -80),([8,9], 4),([9,9], -24)]
def c3GroupHessian47_12 : Poly := List.flatten [c3GroupHessian47_12Chunk0]
theorem c3GroupHessian47_12_check : sumFast (c3TensorGroup47.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian47_12 := by kernel_rfl
private def c3GroupHessian47_13Chunk0 : Poly := [([0,0], -16),([0,2], 8),([0,4], 16),([0,7], 80),([0,8], -36),([0,9], -24),([2,4], 24),([2,8], 4),([2,9], -8),([4,8], -4),([4,9], 8),([6,7], 80),([8,8], -32),([8,9], 8),([9,9], -24)]
def c3GroupHessian47_13 : Poly := List.flatten [c3GroupHessian47_13Chunk0]
theorem c3GroupHessian47_13_check : sumFast (c3TensorGroup47.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian47_13 := by kernel_rfl
private def c3GroupHessian47_22Chunk0 : Poly := [([0,0], 104),([0,3], 160),([0,5], 48),([0,7], 160),([0,9], 48),([3,3], 80),([3,7], 160),([5,5], 24),([5,9], 48),([7,7], 80),([9,9], 24)]
def c3GroupHessian47_22 : Poly := List.flatten [c3GroupHessian47_22Chunk0]
theorem c3GroupHessian47_22_check : sumFast (c3TensorGroup47.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian47_22 := by kernel_rfl
private def c3GroupHessian47_23Chunk0 : Poly := [([0,0], -72),([0,3], -80),([0,4], -8),([0,5], 8),([0,6], -80),([0,7], -80),([0,8], -4),([0,9], 32),([3,6], -80),([4,5], -8),([4,9], -8),([5,8], -4),([5,9], 24),([6,7], -80),([8,9], -4),([9,9], 24)]
def c3GroupHessian47_23 : Poly := List.flatten [c3GroupHessian47_23Chunk0]
theorem c3GroupHessian47_23_check : sumFast (c3TensorGroup47.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian47_23 := by kernel_rfl
private def c3GroupHessian47_33Chunk0 : Poly := [([0,0], 104),([0,4], 16),([0,6], 160),([0,8], 40),([0,9], 16),([4,4], 24),([4,8], 8),([4,9], -16),([6,6], 80),([8,8], 32),([8,9], -8),([9,9], 24)]
def c3GroupHessian47_33 : Poly := List.flatten [c3GroupHessian47_33Chunk0]
theorem c3GroupHessian47_33_check : sumFast (c3TensorGroup47.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian47_33 := by kernel_rfl
end D4.Secondary
