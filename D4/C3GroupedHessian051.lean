import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup51_det_check : c3TensorGroup51.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 71)) = true := by kernel_rfl
private def c3GroupHessian51_00Chunk0 : Poly := [([0,0], 112),([0,1], 160),([0,5], -8),([0,6], 160),([0,9], 64),([1,1], 80),([1,6], 160),([5,5], 24),([5,9], -8),([6,6], 80),([9,9], 32)]
def c3GroupHessian51_00 : Poly := List.flatten [c3GroupHessian51_00Chunk0]
theorem c3GroupHessian51_00_check : sumFast (c3TensorGroup51.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian51_00 := by kernel_rfl
private def c3GroupHessian51_01Chunk0 : Poly := [([0,0], 64),([0,2], 32),([0,5], -8),([0,7], -80),([0,8], 32),([0,9], 96),([1,7], -80),([2,5], -4),([2,9], 32),([5,8], -4),([5,9], -4),([6,7], -80),([8,9], 32),([9,9], 32)]
def c3GroupHessian51_01 : Poly := List.flatten [c3GroupHessian51_01Chunk0]
theorem c3GroupHessian51_01_check : sumFast (c3TensorGroup51.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian51_01 := by kernel_rfl
private def c3GroupHessian51_02Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,3], 80),([0,5], 8),([0,6], 80),([0,7], 80),([0,9], -64),([1,3], 80),([1,7], 80),([3,6], 80),([5,5], -24),([5,9], 8),([6,7], 80),([9,9], -32)]
def c3GroupHessian51_02 : Poly := List.flatten [c3GroupHessian51_02Chunk0]
theorem c3GroupHessian51_02_check : sumFast (c3TensorGroup51.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian51_02 := by kernel_rfl
private def c3GroupHessian51_03Chunk0 : Poly := [([0,0], -112),([0,1], -80),([0,4], -4),([0,5], 4),([0,6], -160),([0,8], -32),([0,9], -64),([1,6], -80),([4,5], 8),([4,9], -4),([5,8], 4),([5,9], 4),([6,6], -80),([8,9], -32),([9,9], -32)]
def c3GroupHessian51_03 : Poly := List.flatten [c3GroupHessian51_03Chunk0]
theorem c3GroupHessian51_03_check : sumFast (c3TensorGroup51.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian51_03 := by kernel_rfl
private def c3GroupHessian51_11Chunk0 : Poly := [([0,0], 128),([0,2], 128),([0,8], 128),([0,9], 128),([2,2], 32),([2,8], 64),([2,9], 64),([7,7], 80),([8,8], 32),([8,9], 64),([9,9], 32)]
def c3GroupHessian51_11 : Poly := List.flatten [c3GroupHessian51_11Chunk0]
theorem c3GroupHessian51_11_check : sumFast (c3TensorGroup51.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian51_11 := by kernel_rfl
private def c3GroupHessian51_12Chunk0 : Poly := [([0,0], -64),([0,2], -32),([0,5], 8),([0,7], -80),([0,8], -32),([0,9], -96),([2,5], 4),([2,9], -32),([3,7], -80),([5,8], 4),([5,9], 4),([7,7], -80),([8,9], -32),([9,9], -32)]
def c3GroupHessian51_12 : Poly := List.flatten [c3GroupHessian51_12Chunk0]
theorem c3GroupHessian51_12_check : sumFast (c3TensorGroup51.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian51_12 := by kernel_rfl
private def c3GroupHessian51_13Chunk0 : Poly := [([0,0], -64),([0,2], -32),([0,4], -8),([0,7], 80),([0,8], -96),([0,9], -96),([2,4], -4),([2,8], -32),([2,9], -32),([4,8], -4),([4,9], -4),([6,7], 80),([8,8], -32),([8,9], -64),([9,9], -32)]
def c3GroupHessian51_13 : Poly := List.flatten [c3GroupHessian51_13Chunk0]
theorem c3GroupHessian51_13_check : sumFast (c3TensorGroup51.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian51_13 := by kernel_rfl
private def c3GroupHessian51_22Chunk0 : Poly := [([0,0], 112),([0,3], 160),([0,5], -8),([0,7], 160),([0,9], 64),([3,3], 80),([3,7], 160),([5,5], 24),([5,9], -8),([7,7], 80),([9,9], 32)]
def c3GroupHessian51_22 : Poly := List.flatten [c3GroupHessian51_22Chunk0]
theorem c3GroupHessian51_22_check : sumFast (c3TensorGroup51.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian51_22 := by kernel_rfl
private def c3GroupHessian51_23Chunk0 : Poly := [([0,0], -48),([0,3], -80),([0,4], 4),([0,5], -4),([0,6], -80),([0,7], -80),([0,8], 32),([0,9], 64),([3,6], -80),([4,5], -8),([4,9], 4),([5,8], -4),([5,9], -4),([6,7], -80),([8,9], 32),([9,9], 32)]
def c3GroupHessian51_23 : Poly := List.flatten [c3GroupHessian51_23Chunk0]
theorem c3GroupHessian51_23_check : sumFast (c3TensorGroup51.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian51_23 := by kernel_rfl
private def c3GroupHessian51_33Chunk0 : Poly := [([0,0], 112),([0,4], 8),([0,6], 160),([0,8], 64),([0,9], 64),([4,4], 24),([4,8], 8),([4,9], 8),([6,6], 80),([8,8], 32),([8,9], 64),([9,9], 32)]
def c3GroupHessian51_33 : Poly := List.flatten [c3GroupHessian51_33Chunk0]
theorem c3GroupHessian51_33_check : sumFast (c3TensorGroup51.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian51_33 := by kernel_rfl
end D4.Secondary
