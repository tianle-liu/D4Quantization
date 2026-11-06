import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup30_det_check : c3TensorGroup30.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 44)) = true := by kernel_rfl
private def c3GroupHessian30_00Chunk0 : Poly := [([0,0], 48),([0,5], 48),([0,6], 48),([1,1], 120),([1,9], -240),([5,5], 48),([5,6], -24),([6,6], 40),([9,9], 120)]
def c3GroupHessian30_00 : Poly := List.flatten [c3GroupHessian30_00Chunk0]
theorem c3GroupHessian30_00_check : sumFast (c3TensorGroup30.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian30_00 := by kernel_rfl
private def c3GroupHessian30_01Chunk0 : Poly := [([0,0], 24),([0,1], -120),([0,2], 24),([0,6], 12),([0,9], 120),([1,7], -120),([1,8], -120),([1,9], -120),([2,6], 12),([7,9], 120),([8,9], 120),([9,9], 120)]
def c3GroupHessian30_01 : Poly := List.flatten [c3GroupHessian30_01Chunk0]
theorem c3GroupHessian30_01_check : sumFast (c3TensorGroup30.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian30_01 := by kernel_rfl
private def c3GroupHessian30_02Chunk0 : Poly := [([0,0], -24),([0,1], 120),([0,5], -60),([0,6], 16),([0,9], -120),([1,3], 120),([1,7], 120),([1,9], 120),([3,9], -120),([5,5], -48),([5,6], 12),([7,9], -120),([9,9], -120)]
def c3GroupHessian30_02 : Poly := List.flatten [c3GroupHessian30_02Chunk0]
theorem c3GroupHessian30_02_check : sumFast (c3TensorGroup30.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian30_02 := by kernel_rfl
private def c3GroupHessian30_03Chunk0 : Poly := [([0,0], -24),([0,1], 120),([0,5], 12),([0,6], -64),([0,9], -120),([1,4], 120),([1,8], 120),([1,9], 120),([4,9], -120),([5,6], 12),([6,6], -40),([8,9], -120),([9,9], -120)]
def c3GroupHessian30_03 : Poly := List.flatten [c3GroupHessian30_03Chunk0]
theorem c3GroupHessian30_03_check : sumFast (c3TensorGroup30.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian30_03 := by kernel_rfl
private def c3GroupHessian30_11Chunk0 : Poly := [([0,0], 152),([0,2], 64),([0,7], 240),([0,8], 240),([0,9], 240),([2,2], 32),([7,7], 120),([7,8], 240),([7,9], 240),([8,8], 120),([8,9], 240),([9,9], 120)]
def c3GroupHessian30_11 : Poly := List.flatten [c3GroupHessian30_11Chunk0]
theorem c3GroupHessian30_11_check : sumFast (c3TensorGroup30.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian30_11 := by kernel_rfl
private def c3GroupHessian30_12Chunk0 : Poly := [([0,0], -132),([0,2], -12),([0,3], -120),([0,7], -240),([0,8], -120),([0,9], -240),([3,7], -120),([3,8], -120),([3,9], -120),([7,7], -120),([7,8], -120),([7,9], -240),([8,9], -120),([9,9], -120)]
def c3GroupHessian30_12 : Poly := List.flatten [c3GroupHessian30_12Chunk0]
theorem c3GroupHessian30_12_check : sumFast (c3TensorGroup30.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian30_12 := by kernel_rfl
private def c3GroupHessian30_13Chunk0 : Poly := [([0,0], -132),([0,2], -12),([0,4], -120),([0,6], -12),([0,7], -120),([0,8], -240),([0,9], -240),([2,6], -12),([4,7], -120),([4,8], -120),([4,9], -120),([7,8], -120),([7,9], -120),([8,8], -120),([8,9], -240),([9,9], -120)]
def c3GroupHessian30_13 : Poly := List.flatten [c3GroupHessian30_13Chunk0]
theorem c3GroupHessian30_13_check : sumFast (c3TensorGroup30.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian30_13 := by kernel_rfl
private def c3GroupHessian30_22Chunk0 : Poly := [([0,0], 160),([0,3], 240),([0,5], 72),([0,7], 240),([0,9], 240),([3,3], 120),([3,7], 240),([3,9], 240),([5,5], 48),([7,7], 120),([7,9], 240),([9,9], 120)]
def c3GroupHessian30_22 : Poly := List.flatten [c3GroupHessian30_22Chunk0]
theorem c3GroupHessian30_22_check : sumFast (c3TensorGroup30.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian30_22 := by kernel_rfl
private def c3GroupHessian30_23Chunk0 : Poly := [([0,0], 104),([0,3], 120),([0,4], 120),([0,5], -12),([0,6], -16),([0,7], 120),([0,8], 120),([0,9], 240),([3,4], 120),([3,8], 120),([3,9], 120),([4,7], 120),([4,9], 120),([5,6], -12),([7,8], 120),([7,9], 120),([8,9], 120),([9,9], 120)]
def c3GroupHessian30_23 : Poly := List.flatten [c3GroupHessian30_23Chunk0]
theorem c3GroupHessian30_23_check : sumFast (c3TensorGroup30.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian30_23 := by kernel_rfl
private def c3GroupHessian30_33Chunk0 : Poly := [([0,0], 160),([0,4], 240),([0,6], 80),([0,8], 240),([0,9], 240),([4,4], 120),([4,8], 240),([4,9], 240),([6,6], 40),([8,8], 120),([8,9], 240),([9,9], 120)]
def c3GroupHessian30_33 : Poly := List.flatten [c3GroupHessian30_33Chunk0]
theorem c3GroupHessian30_33_check : sumFast (c3TensorGroup30.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian30_33 := by kernel_rfl
end D4.Secondary
