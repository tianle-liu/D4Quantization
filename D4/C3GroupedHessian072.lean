import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup72_det_check : c3TensorGroup72.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 97)) = true := by kernel_rfl
private def c3GroupHessian72_00Chunk0 : Poly := [([0,0], 112),([0,1], 160),([0,5], 160),([0,6], -8),([0,9], 64),([1,1], 80),([1,5], 160),([5,5], 80),([6,6], 24),([6,9], -8),([9,9], 32)]
def c3GroupHessian72_00 : Poly := List.flatten [c3GroupHessian72_00Chunk0]
theorem c3GroupHessian72_00_check : sumFast (c3TensorGroup72.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian72_00 := by kernel_rfl
private def c3GroupHessian72_01Chunk0 : Poly := [([0,0], 64),([0,2], 32),([0,6], -8),([0,7], 32),([0,8], -80),([0,9], 96),([1,8], -80),([2,6], -4),([2,9], 32),([5,8], -80),([6,7], -4),([6,9], -4),([7,9], 32),([9,9], 32)]
def c3GroupHessian72_01 : Poly := List.flatten [c3GroupHessian72_01Chunk0]
theorem c3GroupHessian72_01_check : sumFast (c3TensorGroup72.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian72_01 := by kernel_rfl
private def c3GroupHessian72_02Chunk0 : Poly := [([0,0], -112),([0,1], -80),([0,3], -4),([0,5], -160),([0,6], 4),([0,7], -32),([0,9], -64),([1,5], -80),([3,6], 8),([3,9], -4),([5,5], -80),([6,7], 4),([6,9], 4),([7,9], -32),([9,9], -32)]
def c3GroupHessian72_02 : Poly := List.flatten [c3GroupHessian72_02Chunk0]
theorem c3GroupHessian72_02_check : sumFast (c3TensorGroup72.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian72_02 := by kernel_rfl
private def c3GroupHessian72_03Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,4], 80),([0,5], 80),([0,6], 8),([0,8], 80),([0,9], -64),([1,4], 80),([1,8], 80),([4,5], 80),([5,8], 80),([6,6], -24),([6,9], 8),([9,9], -32)]
def c3GroupHessian72_03 : Poly := List.flatten [c3GroupHessian72_03Chunk0]
theorem c3GroupHessian72_03_check : sumFast (c3TensorGroup72.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian72_03 := by kernel_rfl
private def c3GroupHessian72_11Chunk0 : Poly := [([0,0], 128),([0,2], 128),([0,7], 128),([0,9], 128),([2,2], 32),([2,7], 64),([2,9], 64),([7,7], 32),([7,9], 64),([8,8], 80),([9,9], 32)]
def c3GroupHessian72_11 : Poly := List.flatten [c3GroupHessian72_11Chunk0]
theorem c3GroupHessian72_11_check : sumFast (c3TensorGroup72.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian72_11 := by kernel_rfl
private def c3GroupHessian72_12Chunk0 : Poly := [([0,0], -64),([0,2], -32),([0,3], -8),([0,7], -96),([0,8], 80),([0,9], -96),([2,3], -4),([2,7], -32),([2,9], -32),([3,7], -4),([3,9], -4),([5,8], 80),([7,7], -32),([7,9], -64),([9,9], -32)]
def c3GroupHessian72_12 : Poly := List.flatten [c3GroupHessian72_12Chunk0]
theorem c3GroupHessian72_12_check : sumFast (c3TensorGroup72.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian72_12 := by kernel_rfl
private def c3GroupHessian72_13Chunk0 : Poly := [([0,0], -64),([0,2], -32),([0,6], 8),([0,7], -32),([0,8], -80),([0,9], -96),([2,6], 4),([2,9], -32),([4,8], -80),([6,7], 4),([6,9], 4),([7,9], -32),([8,8], -80),([9,9], -32)]
def c3GroupHessian72_13 : Poly := List.flatten [c3GroupHessian72_13Chunk0]
theorem c3GroupHessian72_13_check : sumFast (c3TensorGroup72.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian72_13 := by kernel_rfl
private def c3GroupHessian72_22Chunk0 : Poly := [([0,0], 112),([0,3], 8),([0,5], 160),([0,7], 64),([0,9], 64),([3,3], 24),([3,7], 8),([3,9], 8),([5,5], 80),([7,7], 32),([7,9], 64),([9,9], 32)]
def c3GroupHessian72_22 : Poly := List.flatten [c3GroupHessian72_22Chunk0]
theorem c3GroupHessian72_22_check : sumFast (c3TensorGroup72.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian72_22 := by kernel_rfl
private def c3GroupHessian72_23Chunk0 : Poly := [([0,0], -48),([0,3], 4),([0,4], -80),([0,5], -80),([0,6], -4),([0,7], 32),([0,8], -80),([0,9], 64),([3,6], -8),([3,9], 4),([4,5], -80),([5,8], -80),([6,7], -4),([6,9], -4),([7,9], 32),([9,9], 32)]
def c3GroupHessian72_23 : Poly := List.flatten [c3GroupHessian72_23Chunk0]
theorem c3GroupHessian72_23_check : sumFast (c3TensorGroup72.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian72_23 := by kernel_rfl
private def c3GroupHessian72_33Chunk0 : Poly := [([0,0], 112),([0,4], 160),([0,6], -8),([0,8], 160),([0,9], 64),([4,4], 80),([4,8], 160),([6,6], 24),([6,9], -8),([8,8], 80),([9,9], 32)]
def c3GroupHessian72_33 : Poly := List.flatten [c3GroupHessian72_33Chunk0]
theorem c3GroupHessian72_33_check : sumFast (c3TensorGroup72.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian72_33 := by kernel_rfl
end D4.Secondary
