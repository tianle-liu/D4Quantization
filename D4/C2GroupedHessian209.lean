import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup209_det_check : c2TensorGroup209.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 266)) = true := by kernel_rfl
private def c2GroupHessian209_00Chunk0 : Poly := [([0,0], 56),([0,1], 40),([0,5], 32),([0,6], 80),([1,1], 40),([1,5], 40),([5,5], 16),([6,6], 40)]
def c2GroupHessian209_00 : Poly := List.flatten [c2GroupHessian209_00Chunk0]
theorem c2GroupHessian209_00_check : sumFast (c2TensorGroup209.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian209_00 := by kernel_rfl
private def c2GroupHessian209_01Chunk0 : Poly := [([0,0], 44),([0,2], 4),([0,5], 4),([0,6], 40),([0,7], -8),([0,8], 40),([1,7], -20),([2,5], 4),([5,7], -8),([6,8], 40)]
def c2GroupHessian209_01 : Poly := List.flatten [c2GroupHessian209_01Chunk0]
theorem c2GroupHessian209_01_check : sumFast (c2TensorGroup209.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian209_01 := by kernel_rfl
private def c2GroupHessian209_02Chunk0 : Poly := [([0,0], 4),([0,1], 20),([0,3], 20),([0,5], -12),([0,7], 8),([0,9], 40),([1,3], 40),([1,5], -20),([1,7], 20),([3,5], 20),([5,5], -16),([5,7], 8),([6,9], 40)]
def c2GroupHessian209_02 : Poly := List.flatten [c2GroupHessian209_02Chunk0]
theorem c2GroupHessian209_02_check : sumFast (c2TensorGroup209.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian209_02 := by kernel_rfl
private def c2GroupHessian209_03Chunk0 : Poly := [([0,0], -80),([0,4], -40),([0,6], -120),([0,8], -40),([0,9], -40),([4,6], -40),([6,6], -40),([6,8], -40),([6,9], -40)]
def c2GroupHessian209_03 : Poly := List.flatten [c2GroupHessian209_03Chunk0]
theorem c2GroupHessian209_03_check : sumFast (c2TensorGroup209.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian209_03 := by kernel_rfl
private def c2GroupHessian209_11Chunk0 : Poly := [([0,0], 48),([0,2], 16),([0,7], 8),([0,8], 80),([2,2], 8),([2,7], 8),([7,7], 16),([8,8], 40)]
def c2GroupHessian209_11 : Poly := List.flatten [c2GroupHessian209_11Chunk0]
theorem c2GroupHessian209_11_check : sumFast (c2TensorGroup209.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian209_11 := by kernel_rfl
private def c2GroupHessian209_12Chunk0 : Poly := [([0,0], -4),([0,2], -4),([0,5], -4),([0,7], -16),([0,9], 40),([2,5], -4),([2,7], -4),([3,7], -20),([5,7], 8),([7,7], -16),([8,9], 40)]
def c2GroupHessian209_12 : Poly := List.flatten [c2GroupHessian209_12Chunk0]
theorem c2GroupHessian209_12_check : sumFast (c2TensorGroup209.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian209_12 := by kernel_rfl
private def c2GroupHessian209_13Chunk0 : Poly := [([0,0], -80),([0,4], -40),([0,6], -40),([0,8], -120),([0,9], -40),([4,8], -40),([6,8], -40),([8,8], -40),([8,9], -40)]
def c2GroupHessian209_13 : Poly := List.flatten [c2GroupHessian209_13Chunk0]
theorem c2GroupHessian209_13_check : sumFast (c2TensorGroup209.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian209_13 := by kernel_rfl
private def c2GroupHessian209_22Chunk0 : Poly := [([0,0], 16),([0,3], 40),([0,5], -8),([0,7], 24),([3,3], 40),([3,5], -40),([3,7], 40),([5,5], 16),([5,7], -16),([7,7], 16),([9,9], 40)]
def c2GroupHessian209_22 : Poly := List.flatten [c2GroupHessian209_22Chunk0]
theorem c2GroupHessian209_22_check : sumFast (c2TensorGroup209.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian209_22 := by kernel_rfl
private def c2GroupHessian209_23Chunk0 : Poly := [([0,9], -80),([4,9], -40),([6,9], -40),([8,9], -40),([9,9], -40)]
def c2GroupHessian209_23 : Poly := List.flatten [c2GroupHessian209_23Chunk0]
theorem c2GroupHessian209_23_check : sumFast (c2TensorGroup209.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian209_23 := by kernel_rfl
private def c2GroupHessian209_33Chunk0 : Poly := [([0,0], 160),([0,4], 160),([0,6], 160),([0,8], 160),([0,9], 160),([4,4], 40),([4,6], 80),([4,8], 80),([4,9], 80),([6,6], 40),([6,8], 80),([6,9], 80),([8,8], 40),([8,9], 80),([9,9], 40)]
def c2GroupHessian209_33 : Poly := List.flatten [c2GroupHessian209_33Chunk0]
theorem c2GroupHessian209_33_check : sumFast (c2TensorGroup209.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian209_33 := by kernel_rfl
end D4.Secondary
