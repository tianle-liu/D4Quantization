import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup111_det_check : c3TensorGroup111.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 145)) = true := by kernel_rfl
private def c3GroupHessian111_00Chunk0 : Poly := [([0,0], 152),([0,1], 64),([0,5], 240),([0,6], 240),([0,9], 240),([1,1], 32),([5,5], 120),([5,6], 240),([5,9], 240),([6,6], 120),([6,9], 240),([9,9], 120)]
def c3GroupHessian111_00 : Poly := List.flatten [c3GroupHessian111_00Chunk0]
theorem c3GroupHessian111_00_check : sumFast (c3TensorGroup111.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian111_00 := by kernel_rfl
private def c3GroupHessian111_01Chunk0 : Poly := [([0,0], 24),([0,1], 24),([0,2], -120),([0,8], 12),([0,9], 120),([1,8], 12),([2,5], -120),([2,6], -120),([2,9], -120),([5,9], 120),([6,9], 120),([9,9], 120)]
def c3GroupHessian111_01 : Poly := List.flatten [c3GroupHessian111_01Chunk0]
theorem c3GroupHessian111_01_check : sumFast (c3TensorGroup111.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian111_01 := by kernel_rfl
private def c3GroupHessian111_02Chunk0 : Poly := [([0,0], -132),([0,1], -12),([0,3], -120),([0,5], -240),([0,6], -120),([0,9], -240),([3,5], -120),([3,6], -120),([3,9], -120),([5,5], -120),([5,6], -120),([5,9], -240),([6,9], -120),([9,9], -120)]
def c3GroupHessian111_02 : Poly := List.flatten [c3GroupHessian111_02Chunk0]
theorem c3GroupHessian111_02_check : sumFast (c3TensorGroup111.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian111_02 := by kernel_rfl
private def c3GroupHessian111_03Chunk0 : Poly := [([0,0], -132),([0,1], -12),([0,4], -120),([0,5], -120),([0,6], -240),([0,8], -12),([0,9], -240),([1,8], -12),([4,5], -120),([4,6], -120),([4,9], -120),([5,6], -120),([5,9], -120),([6,6], -120),([6,9], -240),([9,9], -120)]
def c3GroupHessian111_03 : Poly := List.flatten [c3GroupHessian111_03Chunk0]
theorem c3GroupHessian111_03_check : sumFast (c3TensorGroup111.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian111_03 := by kernel_rfl
private def c3GroupHessian111_11Chunk0 : Poly := [([0,0], 48),([0,7], 48),([0,8], 48),([2,2], 120),([2,9], -240),([7,7], 48),([7,8], -24),([8,8], 40),([9,9], 120)]
def c3GroupHessian111_11 : Poly := List.flatten [c3GroupHessian111_11Chunk0]
theorem c3GroupHessian111_11_check : sumFast (c3TensorGroup111.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian111_11 := by kernel_rfl
private def c3GroupHessian111_12Chunk0 : Poly := [([0,0], -24),([0,2], 120),([0,7], -60),([0,8], 16),([0,9], -120),([2,3], 120),([2,5], 120),([2,9], 120),([3,9], -120),([5,9], -120),([7,7], -48),([7,8], 12),([9,9], -120)]
def c3GroupHessian111_12 : Poly := List.flatten [c3GroupHessian111_12Chunk0]
theorem c3GroupHessian111_12_check : sumFast (c3TensorGroup111.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian111_12 := by kernel_rfl
private def c3GroupHessian111_13Chunk0 : Poly := [([0,0], -24),([0,2], 120),([0,7], 12),([0,8], -64),([0,9], -120),([2,4], 120),([2,6], 120),([2,9], 120),([4,9], -120),([6,9], -120),([7,8], 12),([8,8], -40),([9,9], -120)]
def c3GroupHessian111_13 : Poly := List.flatten [c3GroupHessian111_13Chunk0]
theorem c3GroupHessian111_13_check : sumFast (c3TensorGroup111.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian111_13 := by kernel_rfl
private def c3GroupHessian111_22Chunk0 : Poly := [([0,0], 160),([0,3], 240),([0,5], 240),([0,7], 72),([0,9], 240),([3,3], 120),([3,5], 240),([3,9], 240),([5,5], 120),([5,9], 240),([7,7], 48),([9,9], 120)]
def c3GroupHessian111_22 : Poly := List.flatten [c3GroupHessian111_22Chunk0]
theorem c3GroupHessian111_22_check : sumFast (c3TensorGroup111.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian111_22 := by kernel_rfl
private def c3GroupHessian111_23Chunk0 : Poly := [([0,0], 104),([0,3], 120),([0,4], 120),([0,5], 120),([0,6], 120),([0,7], -12),([0,8], -16),([0,9], 240),([3,4], 120),([3,6], 120),([3,9], 120),([4,5], 120),([4,9], 120),([5,6], 120),([5,9], 120),([6,9], 120),([7,8], -12),([9,9], 120)]
def c3GroupHessian111_23 : Poly := List.flatten [c3GroupHessian111_23Chunk0]
theorem c3GroupHessian111_23_check : sumFast (c3TensorGroup111.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian111_23 := by kernel_rfl
private def c3GroupHessian111_33Chunk0 : Poly := [([0,0], 160),([0,4], 240),([0,6], 240),([0,8], 80),([0,9], 240),([4,4], 120),([4,6], 240),([4,9], 240),([6,6], 120),([6,9], 240),([8,8], 40),([9,9], 120)]
def c3GroupHessian111_33 : Poly := List.flatten [c3GroupHessian111_33Chunk0]
theorem c3GroupHessian111_33_check : sumFast (c3TensorGroup111.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian111_33 := by kernel_rfl
end D4.Secondary
