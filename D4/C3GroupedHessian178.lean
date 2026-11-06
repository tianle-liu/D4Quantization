import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup178_det_check : c3TensorGroup178.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 228)) = true := by kernel_rfl
private def c3GroupHessian178_00Chunk0 : Poly := [([0,0], 112),([0,1], 64),([0,5], -8),([0,6], 64),([0,9], 160),([1,1], 32),([1,5], -8),([1,6], 64),([5,5], 24),([5,6], -8),([6,6], 32),([9,9], 80)]
def c3GroupHessian178_00 : Poly := List.flatten [c3GroupHessian178_00Chunk0]
theorem c3GroupHessian178_00_check : sumFast (c3TensorGroup178.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian178_00 := by kernel_rfl
private def c3GroupHessian178_01Chunk0 : Poly := [([0,0], 160),([0,2], 80),([0,7], 80),([0,8], 80),([0,9], 240),([2,9], 80),([7,9], 80),([8,9], 80),([9,9], 80)]
def c3GroupHessian178_01 : Poly := List.flatten [c3GroupHessian178_01Chunk0]
theorem c3GroupHessian178_01_check : sumFast (c3TensorGroup178.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian178_01 := by kernel_rfl
private def c3GroupHessian178_02Chunk0 : Poly := [([0,0], -48),([0,1], 32),([0,3], 32),([0,6], 32),([0,7], -80),([0,9], -160),([1,3], 32),([1,5], 4),([3,5], -4),([3,6], 32),([5,5], -24),([5,6], 4),([7,9], -80),([9,9], -80)]
def c3GroupHessian178_02 : Poly := List.flatten [c3GroupHessian178_02Chunk0]
theorem c3GroupHessian178_02_check : sumFast (c3TensorGroup178.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian178_02 := by kernel_rfl
private def c3GroupHessian178_03Chunk0 : Poly := [([0,0], -112),([0,1], -32),([0,4], -4),([0,5], 4),([0,6], -64),([0,8], -80),([0,9], -160),([1,4], -4),([1,6], -32),([4,5], 8),([4,6], -4),([5,6], 4),([6,6], -32),([8,9], -80),([9,9], -80)]
def c3GroupHessian178_03 : Poly := List.flatten [c3GroupHessian178_03Chunk0]
theorem c3GroupHessian178_03_check : sumFast (c3TensorGroup178.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian178_03 := by kernel_rfl
private def c3GroupHessian178_11Chunk0 : Poly := [([0,0], 320),([0,2], 320),([0,7], 320),([0,8], 320),([0,9], 320),([2,2], 80),([2,7], 160),([2,8], 160),([2,9], 160),([7,7], 80),([7,8], 160),([7,9], 160),([8,8], 80),([8,9], 160),([9,9], 80)]
def c3GroupHessian178_11 : Poly := List.flatten [c3GroupHessian178_11Chunk0]
theorem c3GroupHessian178_11_check : sumFast (c3TensorGroup178.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian178_11 := by kernel_rfl
private def c3GroupHessian178_12Chunk0 : Poly := [([0,0], -160),([0,2], -80),([0,7], -240),([0,8], -80),([0,9], -240),([2,7], -80),([2,9], -80),([7,7], -80),([7,8], -80),([7,9], -160),([8,9], -80),([9,9], -80)]
def c3GroupHessian178_12 : Poly := List.flatten [c3GroupHessian178_12Chunk0]
theorem c3GroupHessian178_12_check : sumFast (c3TensorGroup178.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian178_12 := by kernel_rfl
private def c3GroupHessian178_13Chunk0 : Poly := [([0,0], -160),([0,2], -80),([0,7], -80),([0,8], -240),([0,9], -240),([2,8], -80),([2,9], -80),([7,8], -80),([7,9], -80),([8,8], -80),([8,9], -160),([9,9], -80)]
def c3GroupHessian178_13 : Poly := List.flatten [c3GroupHessian178_13Chunk0]
theorem c3GroupHessian178_13_check : sumFast (c3TensorGroup178.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian178_13 := by kernel_rfl
private def c3GroupHessian178_22Chunk0 : Poly := [([0,0], 112),([0,3], 64),([0,5], 8),([0,7], 160),([0,9], 160),([3,3], 32),([3,5], 8),([5,5], 24),([7,7], 80),([7,9], 160),([9,9], 80)]
def c3GroupHessian178_22 : Poly := List.flatten [c3GroupHessian178_22Chunk0]
theorem c3GroupHessian178_22_check : sumFast (c3TensorGroup178.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian178_22 := by kernel_rfl
private def c3GroupHessian178_23Chunk0 : Poly := [([0,0], 48),([0,3], -32),([0,4], -4),([0,5], -4),([0,6], -32),([0,7], 80),([0,8], 80),([0,9], 160),([3,4], -4),([3,6], -32),([4,5], -8),([5,6], -4),([7,8], 80),([7,9], 80),([8,9], 80),([9,9], 80)]
def c3GroupHessian178_23 : Poly := List.flatten [c3GroupHessian178_23Chunk0]
theorem c3GroupHessian178_23_check : sumFast (c3TensorGroup178.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian178_23 := by kernel_rfl
private def c3GroupHessian178_33Chunk0 : Poly := [([0,0], 112),([0,4], 8),([0,6], 64),([0,8], 160),([0,9], 160),([4,4], 24),([4,6], 8),([6,6], 32),([8,8], 80),([8,9], 160),([9,9], 80)]
def c3GroupHessian178_33 : Poly := List.flatten [c3GroupHessian178_33Chunk0]
theorem c3GroupHessian178_33_check : sumFast (c3TensorGroup178.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian178_33 := by kernel_rfl
end D4.Secondary
