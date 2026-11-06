import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup126_det_check : c3TensorGroup126.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 164)) = true := by kernel_rfl
private def c3GroupHessian126_00Chunk0 : Poly := [([0,0], 32),([0,1], 32),([0,6], 32),([0,9], 32),([1,1], 24),([1,6], -8),([1,9], 16),([5,5], 80),([6,6], 32),([6,9], -8),([9,9], 24)]
def c3GroupHessian126_00 : Poly := List.flatten [c3GroupHessian126_00Chunk0]
theorem c3GroupHessian126_00_check : sumFast (c3TensorGroup126.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian126_00 := by kernel_rfl
private def c3GroupHessian126_01Chunk0 : Poly := [([0,0], 16),([0,1], 8),([0,5], -80),([0,6], -4),([0,7], 16),([0,9], 40),([1,7], 8),([1,9], 8),([2,5], -80),([5,8], -80),([6,7], -4),([6,9], -4),([7,9], 24),([9,9], 24)]
def c3GroupHessian126_01 : Poly := List.flatten [c3GroupHessian126_01Chunk0]
theorem c3GroupHessian126_01_check : sumFast (c3TensorGroup126.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian126_01 := by kernel_rfl
private def c3GroupHessian126_02Chunk0 : Poly := [([0,0], -16),([0,1], -8),([0,5], -80),([0,6], 4),([0,7], -16),([0,9], -40),([1,7], -8),([1,9], -8),([3,5], -80),([5,5], -80),([6,7], 4),([6,9], 4),([7,9], -24),([9,9], -24)]
def c3GroupHessian126_02 : Poly := List.flatten [c3GroupHessian126_02Chunk0]
theorem c3GroupHessian126_02_check : sumFast (c3TensorGroup126.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian126_02 := by kernel_rfl
private def c3GroupHessian126_03Chunk0 : Poly := [([0,0], -16),([0,1], 8),([0,4], 16),([0,5], 80),([0,6], -36),([0,9], -24),([1,4], 24),([1,6], 4),([1,9], -8),([4,6], -4),([4,9], 8),([5,8], 80),([6,6], -32),([6,9], 8),([9,9], -24)]
def c3GroupHessian126_03 : Poly := List.flatten [c3GroupHessian126_03Chunk0]
theorem c3GroupHessian126_03_check : sumFast (c3TensorGroup126.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian126_03 := by kernel_rfl
private def c3GroupHessian126_11Chunk0 : Poly := [([0,0], 104),([0,2], 160),([0,7], 48),([0,8], 160),([0,9], 48),([2,2], 80),([2,8], 160),([7,7], 24),([7,9], 48),([8,8], 80),([9,9], 24)]
def c3GroupHessian126_11 : Poly := List.flatten [c3GroupHessian126_11Chunk0]
theorem c3GroupHessian126_11_check : sumFast (c3TensorGroup126.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian126_11 := by kernel_rfl
private def c3GroupHessian126_12Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,3], 80),([0,5], 80),([0,7], -48),([0,8], 80),([0,9], -48),([2,3], 80),([2,5], 80),([3,8], 80),([5,8], 80),([7,7], -24),([7,9], -48),([9,9], -24)]
def c3GroupHessian126_12 : Poly := List.flatten [c3GroupHessian126_12Chunk0]
theorem c3GroupHessian126_12_check : sumFast (c3TensorGroup126.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian126_12 := by kernel_rfl
private def c3GroupHessian126_13Chunk0 : Poly := [([0,0], -88),([0,2], -80),([0,4], 8),([0,6], 4),([0,7], -8),([0,8], -160),([0,9], -32),([2,8], -80),([4,7], 8),([4,9], 8),([6,7], 4),([6,9], 4),([7,9], -24),([8,8], -80),([9,9], -24)]
def c3GroupHessian126_13 : Poly := List.flatten [c3GroupHessian126_13Chunk0]
theorem c3GroupHessian126_13_check : sumFast (c3TensorGroup126.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian126_13 := by kernel_rfl
private def c3GroupHessian126_22Chunk0 : Poly := [([0,0], 104),([0,3], 160),([0,5], 160),([0,7], 48),([0,9], 48),([3,3], 80),([3,5], 160),([5,5], 80),([7,7], 24),([7,9], 48),([9,9], 24)]
def c3GroupHessian126_22 : Poly := List.flatten [c3GroupHessian126_22Chunk0]
theorem c3GroupHessian126_22_check : sumFast (c3TensorGroup126.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian126_22 := by kernel_rfl
private def c3GroupHessian126_23Chunk0 : Poly := [([0,0], -72),([0,3], -80),([0,4], -8),([0,5], -80),([0,6], -4),([0,7], 8),([0,8], -80),([0,9], 32),([3,8], -80),([4,7], -8),([4,9], -8),([5,8], -80),([6,7], -4),([6,9], -4),([7,9], 24),([9,9], 24)]
def c3GroupHessian126_23 : Poly := List.flatten [c3GroupHessian126_23Chunk0]
theorem c3GroupHessian126_23_check : sumFast (c3TensorGroup126.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian126_23 := by kernel_rfl
private def c3GroupHessian126_33Chunk0 : Poly := [([0,0], 104),([0,4], 16),([0,6], 40),([0,8], 160),([0,9], 16),([4,4], 24),([4,6], 8),([4,9], -16),([6,6], 32),([6,9], -8),([8,8], 80),([9,9], 24)]
def c3GroupHessian126_33 : Poly := List.flatten [c3GroupHessian126_33Chunk0]
theorem c3GroupHessian126_33_check : sumFast (c3TensorGroup126.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian126_33 := by kernel_rfl
end D4.Secondary
