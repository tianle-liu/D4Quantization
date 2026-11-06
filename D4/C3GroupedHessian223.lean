import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup223_det_check : c3TensorGroup223.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 288)) = true := by kernel_rfl
private def c3GroupHessian223_00Chunk0 : Poly := [([0,0], 48),([0,1], 8),([0,5], 8),([0,6], 80),([0,9], 80),([1,1], 16),([1,5], -16),([5,5], 16),([6,6], 40),([6,9], 80),([9,9], 40)]
def c3GroupHessian223_00 : Poly := List.flatten [c3GroupHessian223_00Chunk0]
theorem c3GroupHessian223_00_check : sumFast (c3TensorGroup223.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian223_00 := by kernel_rfl
private def c3GroupHessian223_01Chunk0 : Poly := [([0,0], 48),([0,1], 4),([0,2], 8),([0,5], 4),([0,6], 40),([0,8], 40),([0,9], 80),([1,2], 4),([1,7], -20),([2,5], 4),([5,7], 20),([6,8], 40),([6,9], 40),([8,9], 40),([9,9], 40)]
def c3GroupHessian223_01 : Poly := List.flatten [c3GroupHessian223_01Chunk0]
theorem c3GroupHessian223_01_check : sumFast (c3TensorGroup223.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian223_01 := by kernel_rfl
private def c3GroupHessian223_02Chunk0 : Poly := [([0,0], -4),([0,1], 12),([0,3], 4),([0,5], -16),([0,9], -40),([1,3], 16),([1,5], 8),([1,7], 20),([3,5], -8),([5,5], -16),([5,7], -20),([6,9], -40),([9,9], -40)]
def c3GroupHessian223_02 : Poly := List.flatten [c3GroupHessian223_02Chunk0]
theorem c3GroupHessian223_02_check : sumFast (c3TensorGroup223.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian223_02 := by kernel_rfl
private def c3GroupHessian223_03Chunk0 : Poly := [([0,0], -80),([0,4], -40),([0,6], -120),([0,8], -40),([0,9], -120),([4,6], -40),([4,9], -40),([6,6], -40),([6,8], -40),([6,9], -80),([8,9], -40),([9,9], -40)]
def c3GroupHessian223_03 : Poly := List.flatten [c3GroupHessian223_03Chunk0]
theorem c3GroupHessian223_03_check : sumFast (c3TensorGroup223.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian223_03 := by kernel_rfl
private def c3GroupHessian223_11Chunk0 : Poly := [([0,0], 48),([0,2], 16),([0,8], 80),([0,9], 80),([2,2], 8),([7,7], 40),([8,8], 40),([8,9], 80),([9,9], 40)]
def c3GroupHessian223_11 : Poly := List.flatten [c3GroupHessian223_11Chunk0]
theorem c3GroupHessian223_11_check : sumFast (c3TensorGroup223.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian223_11 := by kernel_rfl
private def c3GroupHessian223_12Chunk0 : Poly := [([0,0], -4),([0,2], -4),([0,3], 4),([0,5], -4),([0,7], -20),([0,9], -40),([2,3], 4),([2,5], -4),([3,7], -20),([5,7], -20),([7,7], -40),([8,9], -40),([9,9], -40)]
def c3GroupHessian223_12 : Poly := List.flatten [c3GroupHessian223_12Chunk0]
theorem c3GroupHessian223_12_check : sumFast (c3TensorGroup223.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian223_12 := by kernel_rfl
private def c3GroupHessian223_13Chunk0 : Poly := [([0,0], -80),([0,4], -40),([0,6], -40),([0,8], -120),([0,9], -120),([4,8], -40),([4,9], -40),([6,8], -40),([6,9], -40),([8,8], -40),([8,9], -80),([9,9], -40)]
def c3GroupHessian223_13 : Poly := List.flatten [c3GroupHessian223_13Chunk0]
theorem c3GroupHessian223_13_check : sumFast (c3TensorGroup223.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian223_13 := by kernel_rfl
private def c3GroupHessian223_22Chunk0 : Poly := [([0,0], 16),([0,3], 24),([0,5], 24),([0,7], 40),([3,3], 16),([3,5], 16),([3,7], 40),([5,5], 16),([5,7], 40),([7,7], 40),([9,9], 40)]
def c3GroupHessian223_22 : Poly := List.flatten [c3GroupHessian223_22Chunk0]
theorem c3GroupHessian223_22_check : sumFast (c3TensorGroup223.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian223_22 := by kernel_rfl
private def c3GroupHessian223_23Chunk0 : Poly := [([0,9], 80),([4,9], 40),([6,9], 40),([8,9], 40),([9,9], 40)]
def c3GroupHessian223_23 : Poly := List.flatten [c3GroupHessian223_23Chunk0]
theorem c3GroupHessian223_23_check : sumFast (c3TensorGroup223.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian223_23 := by kernel_rfl
private def c3GroupHessian223_33Chunk0 : Poly := [([0,0], 160),([0,4], 160),([0,6], 160),([0,8], 160),([0,9], 160),([4,4], 40),([4,6], 80),([4,8], 80),([4,9], 80),([6,6], 40),([6,8], 80),([6,9], 80),([8,8], 40),([8,9], 80),([9,9], 40)]
def c3GroupHessian223_33 : Poly := List.flatten [c3GroupHessian223_33Chunk0]
theorem c3GroupHessian223_33_check : sumFast (c3TensorGroup223.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian223_33 := by kernel_rfl
end D4.Secondary
