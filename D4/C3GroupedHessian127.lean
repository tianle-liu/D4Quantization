import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup127_det_check : c3TensorGroup127.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 165)) = true := by kernel_rfl
private def c3GroupHessian127_00Chunk0 : Poly := [([0,0], 32),([0,1], 32),([0,6], 80),([0,9], 32),([1,1], 24),([1,6], 40),([1,9], 16),([5,5], 80),([6,6], 80),([6,9], 40),([9,9], 24)]
def c3GroupHessian127_00 : Poly := List.flatten [c3GroupHessian127_00Chunk0]
theorem c3GroupHessian127_00_check : sumFast (c3TensorGroup127.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian127_00 := by kernel_rfl
private def c3GroupHessian127_01Chunk0 : Poly := [([0,0], -8),([0,1], -4),([0,5], -80),([0,6], -40),([0,7], -8),([0,9], 12),([1,7], -4),([1,9], 8),([2,5], -80),([5,8], -80),([6,7], -40),([6,9], 20),([7,9], -4),([9,9], 24)]
def c3GroupHessian127_01 : Poly := List.flatten [c3GroupHessian127_01Chunk0]
theorem c3GroupHessian127_01_check : sumFast (c3TensorGroup127.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian127_01 := by kernel_rfl
private def c3GroupHessian127_02Chunk0 : Poly := [([0,0], 8),([0,1], 4),([0,5], -80),([0,6], 40),([0,7], 8),([0,9], -12),([1,7], 4),([1,9], -8),([3,5], -80),([5,5], -80),([6,7], 40),([6,9], -20),([7,9], 4),([9,9], -24)]
def c3GroupHessian127_02 : Poly := List.flatten [c3GroupHessian127_02Chunk0]
theorem c3GroupHessian127_02_check : sumFast (c3TensorGroup127.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian127_02 := by kernel_rfl
private def c3GroupHessian127_03Chunk0 : Poly := [([0,0], -40),([0,1], -20),([0,4], -8),([0,5], 80),([0,6], -120),([0,9], -36),([1,4], -4),([1,6], -20),([1,9], -8),([4,6], -40),([4,9], -4),([5,8], 80),([6,6], -80),([6,9], -40),([9,9], -24)]
def c3GroupHessian127_03 : Poly := List.flatten [c3GroupHessian127_03Chunk0]
theorem c3GroupHessian127_03_check : sumFast (c3TensorGroup127.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian127_03 := by kernel_rfl
private def c3GroupHessian127_11Chunk0 : Poly := [([0,0], 112),([0,2], 160),([0,7], 64),([0,8], 160),([0,9], -8),([2,2], 80),([2,8], 160),([7,7], 32),([7,9], -8),([8,8], 80),([9,9], 24)]
def c3GroupHessian127_11 : Poly := List.flatten [c3GroupHessian127_11Chunk0]
theorem c3GroupHessian127_11_check : sumFast (c3TensorGroup127.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian127_11 := by kernel_rfl
private def c3GroupHessian127_12Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,3], 80),([0,5], 80),([0,7], -64),([0,8], 80),([0,9], 8),([2,3], 80),([2,5], 80),([3,8], 80),([5,8], 80),([7,7], -32),([7,9], 8),([9,9], -24)]
def c3GroupHessian127_12 : Poly := List.flatten [c3GroupHessian127_12Chunk0]
theorem c3GroupHessian127_12_check : sumFast (c3TensorGroup127.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian127_12 := by kernel_rfl
private def c3GroupHessian127_13Chunk0 : Poly := [([0,0], -40),([0,2], -80),([0,4], 32),([0,6], 40),([0,7], 40),([0,8], -160),([0,9], -16),([2,8], -80),([4,7], 32),([4,9], -4),([6,7], 40),([6,9], -20),([7,9], 4),([8,8], -80),([9,9], -24)]
def c3GroupHessian127_13 : Poly := List.flatten [c3GroupHessian127_13Chunk0]
theorem c3GroupHessian127_13_check : sumFast (c3TensorGroup127.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian127_13 := by kernel_rfl
private def c3GroupHessian127_22Chunk0 : Poly := [([0,0], 112),([0,3], 160),([0,5], 160),([0,7], 64),([0,9], -8),([3,3], 80),([3,5], 160),([5,5], 80),([7,7], 32),([7,9], -8),([9,9], 24)]
def c3GroupHessian127_22 : Poly := List.flatten [c3GroupHessian127_22Chunk0]
theorem c3GroupHessian127_22_check : sumFast (c3TensorGroup127.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian127_22 := by kernel_rfl
private def c3GroupHessian127_23Chunk0 : Poly := [([0,0], -120),([0,3], -80),([0,4], -32),([0,5], -80),([0,6], -40),([0,7], -40),([0,8], -80),([0,9], 16),([3,8], -80),([4,7], -32),([4,9], 4),([5,8], -80),([6,7], -40),([6,9], 20),([7,9], -4),([9,9], 24)]
def c3GroupHessian127_23 : Poly := List.flatten [c3GroupHessian127_23Chunk0]
theorem c3GroupHessian127_23_check : sumFast (c3TensorGroup127.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian127_23 := by kernel_rfl
private def c3GroupHessian127_33Chunk0 : Poly := [([0,0], 160),([0,4], 80),([0,6], 160),([0,8], 160),([0,9], 40),([4,4], 32),([4,6], 80),([4,9], 8),([6,6], 80),([6,9], 40),([8,8], 80),([9,9], 24)]
def c3GroupHessian127_33 : Poly := List.flatten [c3GroupHessian127_33Chunk0]
theorem c3GroupHessian127_33_check : sumFast (c3TensorGroup127.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian127_33 := by kernel_rfl
end D4.Secondary
