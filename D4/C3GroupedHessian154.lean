import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup154_det_check : c3TensorGroup154.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 199)) = true := by kernel_rfl
private def c3GroupHessian154_00Chunk0 : Poly := [([0,0], 128),([0,1], 128),([0,5], 128),([0,9], 128),([1,1], 32),([1,5], 64),([1,9], 64),([5,5], 32),([5,9], 64),([6,6], 80),([9,9], 32)]
def c3GroupHessian154_00 : Poly := List.flatten [c3GroupHessian154_00Chunk0]
theorem c3GroupHessian154_00_check : sumFast (c3TensorGroup154.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian154_00 := by kernel_rfl
private def c3GroupHessian154_01Chunk0 : Poly := [([0,0], 64),([0,1], 32),([0,5], 32),([0,6], -80),([0,8], -8),([0,9], 96),([1,8], -4),([1,9], 32),([2,6], -80),([5,8], -4),([5,9], 32),([6,7], -80),([8,9], -4),([9,9], 32)]
def c3GroupHessian154_01 : Poly := List.flatten [c3GroupHessian154_01Chunk0]
theorem c3GroupHessian154_01_check : sumFast (c3TensorGroup154.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian154_01 := by kernel_rfl
private def c3GroupHessian154_02Chunk0 : Poly := [([0,0], -64),([0,1], -32),([0,3], -8),([0,5], -96),([0,6], 80),([0,9], -96),([1,3], -4),([1,5], -32),([1,9], -32),([3,5], -4),([3,9], -4),([5,5], -32),([5,9], -64),([6,7], 80),([9,9], -32)]
def c3GroupHessian154_02 : Poly := List.flatten [c3GroupHessian154_02Chunk0]
theorem c3GroupHessian154_02_check : sumFast (c3TensorGroup154.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian154_02 := by kernel_rfl
private def c3GroupHessian154_03Chunk0 : Poly := [([0,0], -64),([0,1], -32),([0,5], -32),([0,6], -80),([0,8], 8),([0,9], -96),([1,8], 4),([1,9], -32),([4,6], -80),([5,8], 4),([5,9], -32),([6,6], -80),([8,9], 4),([9,9], -32)]
def c3GroupHessian154_03 : Poly := List.flatten [c3GroupHessian154_03Chunk0]
theorem c3GroupHessian154_03_check : sumFast (c3TensorGroup154.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian154_03 := by kernel_rfl
private def c3GroupHessian154_11Chunk0 : Poly := [([0,0], 112),([0,2], 160),([0,7], 160),([0,8], -8),([0,9], 64),([2,2], 80),([2,7], 160),([7,7], 80),([8,8], 24),([8,9], -8),([9,9], 32)]
def c3GroupHessian154_11 : Poly := List.flatten [c3GroupHessian154_11Chunk0]
theorem c3GroupHessian154_11_check : sumFast (c3TensorGroup154.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian154_11 := by kernel_rfl
private def c3GroupHessian154_12Chunk0 : Poly := [([0,0], -112),([0,2], -80),([0,3], -4),([0,5], -32),([0,7], -160),([0,8], 4),([0,9], -64),([2,7], -80),([3,8], 8),([3,9], -4),([5,8], 4),([5,9], -32),([7,7], -80),([8,9], 4),([9,9], -32)]
def c3GroupHessian154_12 : Poly := List.flatten [c3GroupHessian154_12Chunk0]
theorem c3GroupHessian154_12_check : sumFast (c3TensorGroup154.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian154_12 := by kernel_rfl
private def c3GroupHessian154_13Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,4], 80),([0,6], 80),([0,7], 80),([0,8], 8),([0,9], -64),([2,4], 80),([2,6], 80),([4,7], 80),([6,7], 80),([8,8], -24),([8,9], 8),([9,9], -32)]
def c3GroupHessian154_13 : Poly := List.flatten [c3GroupHessian154_13Chunk0]
theorem c3GroupHessian154_13_check : sumFast (c3TensorGroup154.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian154_13 := by kernel_rfl
private def c3GroupHessian154_22Chunk0 : Poly := [([0,0], 112),([0,3], 8),([0,5], 64),([0,7], 160),([0,9], 64),([3,3], 24),([3,5], 8),([3,9], 8),([5,5], 32),([5,9], 64),([7,7], 80),([9,9], 32)]
def c3GroupHessian154_22 : Poly := List.flatten [c3GroupHessian154_22Chunk0]
theorem c3GroupHessian154_22_check : sumFast (c3TensorGroup154.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian154_22 := by kernel_rfl
private def c3GroupHessian154_23Chunk0 : Poly := [([0,0], -48),([0,3], 4),([0,4], -80),([0,5], 32),([0,6], -80),([0,7], -80),([0,8], -4),([0,9], 64),([3,8], -8),([3,9], 4),([4,7], -80),([5,8], -4),([5,9], 32),([6,7], -80),([8,9], -4),([9,9], 32)]
def c3GroupHessian154_23 : Poly := List.flatten [c3GroupHessian154_23Chunk0]
theorem c3GroupHessian154_23_check : sumFast (c3TensorGroup154.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian154_23 := by kernel_rfl
private def c3GroupHessian154_33Chunk0 : Poly := [([0,0], 112),([0,4], 160),([0,6], 160),([0,8], -8),([0,9], 64),([4,4], 80),([4,6], 160),([6,6], 80),([8,8], 24),([8,9], -8),([9,9], 32)]
def c3GroupHessian154_33 : Poly := List.flatten [c3GroupHessian154_33Chunk0]
theorem c3GroupHessian154_33_check : sumFast (c3TensorGroup154.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian154_33 := by kernel_rfl
end D4.Secondary
