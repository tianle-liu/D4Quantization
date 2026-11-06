import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup224_det_check : c3TensorGroup224.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 289)) = true := by kernel_rfl
private def c3GroupHessian224_00Chunk0 : Poly := [([0,0], 112),([0,1], 64),([0,5], -8),([0,6], 160),([0,9], 160),([1,1], 32),([1,5], -8),([5,5], 24),([6,6], 80),([6,9], 160),([9,9], 80)]
def c3GroupHessian224_00 : Poly := List.flatten [c3GroupHessian224_00Chunk0]
theorem c3GroupHessian224_00_check : sumFast (c3TensorGroup224.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian224_00 := by kernel_rfl
private def c3GroupHessian224_01Chunk0 : Poly := [([0,0], 112),([0,1], 32),([0,2], 32),([0,5], -4),([0,6], 80),([0,7], -4),([0,8], 80),([0,9], 160),([1,2], 32),([1,7], -4),([2,5], -4),([5,7], 8),([6,8], 80),([6,9], 80),([8,9], 80),([9,9], 80)]
def c3GroupHessian224_01 : Poly := List.flatten [c3GroupHessian224_01Chunk0]
theorem c3GroupHessian224_01_check : sumFast (c3TensorGroup224.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian224_01 := by kernel_rfl
private def c3GroupHessian224_02Chunk0 : Poly := [([0,3], 32),([0,5], 4),([0,7], 4),([0,9], -80),([1,3], 32),([1,5], 4),([1,7], 4),([3,5], -4),([5,5], -24),([5,7], -8),([6,9], -80),([9,9], -80)]
def c3GroupHessian224_02 : Poly := List.flatten [c3GroupHessian224_02Chunk0]
theorem c3GroupHessian224_02_check : sumFast (c3TensorGroup224.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian224_02 := by kernel_rfl
private def c3GroupHessian224_03Chunk0 : Poly := [([0,0], -160),([0,4], -80),([0,6], -240),([0,8], -80),([0,9], -240),([4,6], -80),([4,9], -80),([6,6], -80),([6,8], -80),([6,9], -160),([8,9], -80),([9,9], -80)]
def c3GroupHessian224_03 : Poly := List.flatten [c3GroupHessian224_03Chunk0]
theorem c3GroupHessian224_03_check : sumFast (c3TensorGroup224.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian224_03 := by kernel_rfl
private def c3GroupHessian224_11Chunk0 : Poly := [([0,0], 112),([0,2], 64),([0,7], -8),([0,8], 160),([0,9], 160),([2,2], 32),([2,7], -8),([7,7], 24),([8,8], 80),([8,9], 160),([9,9], 80)]
def c3GroupHessian224_11 : Poly := List.flatten [c3GroupHessian224_11Chunk0]
theorem c3GroupHessian224_11_check : sumFast (c3TensorGroup224.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian224_11 := by kernel_rfl
private def c3GroupHessian224_12Chunk0 : Poly := [([0,3], 32),([0,5], 4),([0,7], 4),([0,9], -80),([2,3], 32),([2,5], 4),([2,7], 4),([3,7], -4),([5,7], -8),([7,7], -24),([8,9], -80),([9,9], -80)]
def c3GroupHessian224_12 : Poly := List.flatten [c3GroupHessian224_12Chunk0]
theorem c3GroupHessian224_12_check : sumFast (c3TensorGroup224.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian224_12 := by kernel_rfl
private def c3GroupHessian224_13Chunk0 : Poly := [([0,0], -160),([0,4], -80),([0,6], -80),([0,8], -240),([0,9], -240),([4,8], -80),([4,9], -80),([6,8], -80),([6,9], -80),([8,8], -80),([8,9], -160),([9,9], -80)]
def c3GroupHessian224_13 : Poly := List.flatten [c3GroupHessian224_13Chunk0]
theorem c3GroupHessian224_13_check : sumFast (c3TensorGroup224.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian224_13 := by kernel_rfl
private def c3GroupHessian224_22Chunk0 : Poly := [([3,3], 32),([3,5], 8),([3,7], 8),([5,5], 24),([5,7], 16),([7,7], 24),([9,9], 80)]
def c3GroupHessian224_22 : Poly := List.flatten [c3GroupHessian224_22Chunk0]
theorem c3GroupHessian224_22_check : sumFast (c3TensorGroup224.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian224_22 := by kernel_rfl
private def c3GroupHessian224_23Chunk0 : Poly := [([0,9], 160),([4,9], 80),([6,9], 80),([8,9], 80),([9,9], 80)]
def c3GroupHessian224_23 : Poly := List.flatten [c3GroupHessian224_23Chunk0]
theorem c3GroupHessian224_23_check : sumFast (c3TensorGroup224.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian224_23 := by kernel_rfl
private def c3GroupHessian224_33Chunk0 : Poly := [([0,0], 320),([0,4], 320),([0,6], 320),([0,8], 320),([0,9], 320),([4,4], 80),([4,6], 160),([4,8], 160),([4,9], 160),([6,6], 80),([6,8], 160),([6,9], 160),([8,8], 80),([8,9], 160),([9,9], 80)]
def c3GroupHessian224_33 : Poly := List.flatten [c3GroupHessian224_33Chunk0]
theorem c3GroupHessian224_33_check : sumFast (c3TensorGroup224.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian224_33 := by kernel_rfl
end D4.Secondary
