import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup22_det_check : c3TensorGroup22.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 24)) = true := by kernel_rfl
private def c3GroupHessian22_00Chunk0 : Poly := [([0,0], 112),([0,1], 160),([0,5], 64),([0,6], -8),([0,9], 64),([1,1], 80),([5,5], 32),([5,6], -8),([5,9], 64),([6,6], 24),([6,9], -8),([9,9], 32)]
def c3GroupHessian22_00 : Poly := List.flatten [c3GroupHessian22_00Chunk0]
theorem c3GroupHessian22_00_check : sumFast (c3TensorGroup22.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian22_00 := by kernel_rfl
private def c3GroupHessian22_01Chunk0 : Poly := [([0,0], 112),([0,1], 80),([0,2], 80),([0,5], 32),([0,6], -4),([0,7], 32),([0,8], -4),([0,9], 64),([1,2], 80),([5,7], 32),([5,8], -4),([5,9], 32),([6,7], -4),([6,8], 8),([6,9], -4),([7,9], 32),([8,9], -4),([9,9], 32)]
def c3GroupHessian22_01 : Poly := List.flatten [c3GroupHessian22_01Chunk0]
theorem c3GroupHessian22_01_check : sumFast (c3TensorGroup22.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian22_01 := by kernel_rfl
private def c3GroupHessian22_02Chunk0 : Poly := [([0,0], -72),([0,3], 80),([0,5], -104),([0,6], 24),([0,7], -32),([0,9], -104),([1,3], 80),([5,5], -32),([5,6], 4),([5,7], -32),([5,9], -64),([6,7], 4),([6,9], 4),([7,9], -32),([9,9], -32)]
def c3GroupHessian22_02 : Poly := List.flatten [c3GroupHessian22_02Chunk0]
theorem c3GroupHessian22_02_check : sumFast (c3TensorGroup22.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian22_02 := by kernel_rfl
private def c3GroupHessian22_03Chunk0 : Poly := [([0,0], 8),([0,4], 80),([0,5], 8),([0,6], -12),([0,8], 4),([0,9], -24),([1,4], 80),([5,6], 4),([5,8], 4),([5,9], -32),([6,6], -24),([6,8], -8),([6,9], 8),([8,9], 4),([9,9], -32)]
def c3GroupHessian22_03 : Poly := List.flatten [c3GroupHessian22_03Chunk0]
theorem c3GroupHessian22_03_check : sumFast (c3TensorGroup22.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian22_03 := by kernel_rfl
private def c3GroupHessian22_11Chunk0 : Poly := [([0,0], 112),([0,2], 160),([0,7], 64),([0,8], -8),([0,9], 64),([2,2], 80),([7,7], 32),([7,8], -8),([7,9], 64),([8,8], 24),([8,9], -8),([9,9], 32)]
def c3GroupHessian22_11 : Poly := List.flatten [c3GroupHessian22_11Chunk0]
theorem c3GroupHessian22_11_check : sumFast (c3TensorGroup22.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian22_11 := by kernel_rfl
private def c3GroupHessian22_12Chunk0 : Poly := [([0,0], -72),([0,3], 80),([0,5], -32),([0,7], -104),([0,8], 24),([0,9], -104),([2,3], 80),([5,7], -32),([5,8], 4),([5,9], -32),([7,7], -32),([7,8], 4),([7,9], -64),([8,9], 4),([9,9], -32)]
def c3GroupHessian22_12 : Poly := List.flatten [c3GroupHessian22_12Chunk0]
theorem c3GroupHessian22_12_check : sumFast (c3TensorGroup22.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian22_12 := by kernel_rfl
private def c3GroupHessian22_13Chunk0 : Poly := [([0,0], 8),([0,4], 80),([0,6], 4),([0,7], 8),([0,8], -12),([0,9], -24),([2,4], 80),([6,7], 4),([6,8], -8),([6,9], 4),([7,8], 4),([7,9], -32),([8,8], -24),([8,9], 8),([9,9], -32)]
def c3GroupHessian22_13 : Poly := List.flatten [c3GroupHessian22_13Chunk0]
theorem c3GroupHessian22_13_check : sumFast (c3TensorGroup22.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian22_13 := by kernel_rfl
private def c3GroupHessian22_22Chunk0 : Poly := [([0,0], 192),([0,5], 144),([0,7], 144),([0,9], 144),([3,3], 80),([5,5], 32),([5,7], 64),([5,9], 64),([7,7], 32),([7,9], 64),([9,9], 32)]
def c3GroupHessian22_22 : Poly := List.flatten [c3GroupHessian22_22Chunk0]
theorem c3GroupHessian22_22_check : sumFast (c3TensorGroup22.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian22_22 := by kernel_rfl
private def c3GroupHessian22_23Chunk0 : Poly := [([0,0], -48),([0,5], -8),([0,6], -24),([0,7], -8),([0,8], -24),([0,9], 64),([3,4], 80),([5,6], -4),([5,8], -4),([5,9], 32),([6,7], -4),([6,9], -4),([7,8], -4),([7,9], 32),([8,9], -4),([9,9], 32)]
def c3GroupHessian22_23 : Poly := List.flatten [c3GroupHessian22_23Chunk0]
theorem c3GroupHessian22_23_check : sumFast (c3TensorGroup22.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian22_23 := by kernel_rfl
private def c3GroupHessian22_33Chunk0 : Poly := [([0,0], 32),([0,6], 32),([0,8], 32),([0,9], -16),([4,4], 80),([6,6], 24),([6,8], 16),([6,9], -8),([8,8], 24),([8,9], -8),([9,9], 32)]
def c3GroupHessian22_33 : Poly := List.flatten [c3GroupHessian22_33Chunk0]
theorem c3GroupHessian22_33_check : sumFast (c3TensorGroup22.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian22_33 := by kernel_rfl
end D4.Secondary
