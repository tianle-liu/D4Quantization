import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup35_det_check : c2TensorGroup35.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 52)) = true := by kernel_rfl
private def c2GroupHessian35_00Chunk0 : Poly := [([0,0], 32),([0,5], 32),([0,6], 32),([1,1], 80),([5,5], 32),([5,6], -8),([6,6], 24)]
def c2GroupHessian35_00 : Poly := List.flatten [c2GroupHessian35_00Chunk0]
theorem c2GroupHessian35_00_check : sumFast (c2TensorGroup35.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian35_00 := by kernel_rfl
private def c2GroupHessian35_01Chunk0 : Poly := [([0,0], 16),([0,1], -80),([0,2], 16),([0,5], -4),([0,6], 8),([1,7], -80),([1,8], -80),([2,5], -4),([2,6], 8)]
def c2GroupHessian35_01 : Poly := List.flatten [c2GroupHessian35_01Chunk0]
theorem c2GroupHessian35_01_check : sumFast (c2TensorGroup35.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian35_01 := by kernel_rfl
private def c2GroupHessian35_02Chunk0 : Poly := [([0,0], -16),([0,1], 80),([0,5], -36),([0,6], 8),([0,9], 16),([1,3], 80),([1,7], 80),([5,5], -32),([5,6], 4),([5,9], -4),([6,9], 24)]
def c2GroupHessian35_02 : Poly := List.flatten [c2GroupHessian35_02Chunk0]
theorem c2GroupHessian35_02_check : sumFast (c2TensorGroup35.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian35_02 := by kernel_rfl
private def c2GroupHessian35_03Chunk0 : Poly := [([0,0], -16),([0,1], 80),([0,5], 4),([0,6], -40),([0,9], -16),([1,4], 80),([1,8], 80),([5,6], 4),([5,9], 4),([6,6], -24),([6,9], -24)]
def c2GroupHessian35_03 : Poly := List.flatten [c2GroupHessian35_03Chunk0]
theorem c2GroupHessian35_03_check : sumFast (c2TensorGroup35.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian35_03 := by kernel_rfl
private def c2GroupHessian35_11Chunk0 : Poly := [([0,0], 104),([0,2], 48),([0,7], 160),([0,8], 160),([2,2], 24),([7,7], 80),([7,8], 160),([8,8], 80)]
def c2GroupHessian35_11 : Poly := List.flatten [c2GroupHessian35_11Chunk0]
theorem c2GroupHessian35_11_check : sumFast (c2TensorGroup35.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian35_11 := by kernel_rfl
private def c2GroupHessian35_12Chunk0 : Poly := [([0,0], -88),([0,2], -8),([0,3], -80),([0,5], 4),([0,7], -160),([0,8], -80),([0,9], 8),([2,5], 4),([2,9], 8),([3,7], -80),([3,8], -80),([7,7], -80),([7,8], -80)]
def c2GroupHessian35_12 : Poly := List.flatten [c2GroupHessian35_12Chunk0]
theorem c2GroupHessian35_12_check : sumFast (c2TensorGroup35.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian35_12 := by kernel_rfl
private def c2GroupHessian35_13Chunk0 : Poly := [([0,0], -88),([0,2], -8),([0,4], -80),([0,6], -8),([0,7], -80),([0,8], -160),([0,9], -8),([2,6], -8),([2,9], -8),([4,7], -80),([4,8], -80),([7,8], -80),([8,8], -80)]
def c2GroupHessian35_13 : Poly := List.flatten [c2GroupHessian35_13Chunk0]
theorem c2GroupHessian35_13_check : sumFast (c2TensorGroup35.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian35_13 := by kernel_rfl
private def c2GroupHessian35_22Chunk0 : Poly := [([0,0], 104),([0,3], 160),([0,5], 40),([0,7], 160),([0,9], 16),([3,3], 80),([3,7], 160),([5,5], 32),([5,9], 8),([7,7], 80),([9,9], 24)]
def c2GroupHessian35_22 : Poly := List.flatten [c2GroupHessian35_22Chunk0]
theorem c2GroupHessian35_22_check : sumFast (c2TensorGroup35.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian35_22 := by kernel_rfl
private def c2GroupHessian35_23Chunk0 : Poly := [([0,0], 72),([0,3], 80),([0,4], 80),([0,5], -4),([0,6], -8),([0,7], 80),([0,8], 80),([0,9], -32),([3,4], 80),([3,8], 80),([4,7], 80),([5,6], -4),([5,9], -4),([6,9], -24),([7,8], 80),([9,9], -24)]
def c2GroupHessian35_23 : Poly := List.flatten [c2GroupHessian35_23Chunk0]
theorem c2GroupHessian35_23_check : sumFast (c2TensorGroup35.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian35_23 := by kernel_rfl
private def c2GroupHessian35_33Chunk0 : Poly := [([0,0], 104),([0,4], 160),([0,6], 48),([0,8], 160),([0,9], 48),([4,4], 80),([4,8], 160),([6,6], 24),([6,9], 48),([8,8], 80),([9,9], 24)]
def c2GroupHessian35_33 : Poly := List.flatten [c2GroupHessian35_33Chunk0]
theorem c2GroupHessian35_33_check : sumFast (c2TensorGroup35.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian35_33 := by kernel_rfl
end D4.Secondary
