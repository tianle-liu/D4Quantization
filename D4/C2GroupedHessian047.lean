import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup47_det_check : c2TensorGroup47.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 65)) = true := by kernel_rfl
private def c2GroupHessian47_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 32),([0,6], 80),([1,1], 40),([1,6], 80),([5,5], 16),([6,6], 40)]
def c2GroupHessian47_00 : Poly := List.flatten [c2GroupHessian47_00Chunk0]
theorem c2GroupHessian47_00_check : sumFast (c2TensorGroup47.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian47_00 := by kernel_rfl
private def c2GroupHessian47_01Chunk0 : Poly := [([0,0], -4),([0,2], -8),([0,5], -4),([0,7], -40),([0,8], -20),([1,7], -40),([2,5], -8),([5,8], -20),([6,7], -40)]
def c2GroupHessian47_01 : Poly := List.flatten [c2GroupHessian47_01Chunk0]
theorem c2GroupHessian47_01_check : sumFast (c2TensorGroup47.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian47_01 := by kernel_rfl
private def c2GroupHessian47_02Chunk0 : Poly := [([0,0], 24),([0,1], 40),([0,3], 40),([0,5], -32),([0,6], 40),([0,7], 40),([0,9], 40),([1,3], 40),([1,7], 40),([1,9], 40),([3,6], 40),([5,5], -16),([6,7], 40),([6,9], 40)]
def c2GroupHessian47_02 : Poly := List.flatten [c2GroupHessian47_02Chunk0]
theorem c2GroupHessian47_02_check : sumFast (c2TensorGroup47.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian47_02 := by kernel_rfl
private def c2GroupHessian47_03Chunk0 : Poly := [([0,0], -32),([0,1], -40),([0,4], 4),([0,5], 8),([0,6], -80),([0,8], 20),([0,9], -40),([1,6], -40),([1,9], -40),([4,5], 4),([5,8], 20),([6,6], -40),([6,9], -40)]
def c2GroupHessian47_03 : Poly := List.flatten [c2GroupHessian47_03Chunk0]
theorem c2GroupHessian47_03_check : sumFast (c2TensorGroup47.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian47_03 := by kernel_rfl
private def c2GroupHessian47_11Chunk0 : Poly := [([0,0], 16),([0,2], 24),([0,8], 40),([2,2], 16),([2,8], 40),([7,7], 40),([8,8], 40)]
def c2GroupHessian47_11 : Poly := List.flatten [c2GroupHessian47_11Chunk0]
theorem c2GroupHessian47_11_check : sumFast (c2TensorGroup47.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian47_11 := by kernel_rfl
private def c2GroupHessian47_12Chunk0 : Poly := [([0,0], 4),([0,2], 8),([0,5], 4),([0,7], -40),([0,8], 20),([2,5], 8),([3,7], -40),([5,8], 20),([7,7], -40),([7,9], -40)]
def c2GroupHessian47_12 : Poly := List.flatten [c2GroupHessian47_12Chunk0]
theorem c2GroupHessian47_12_check : sumFast (c2TensorGroup47.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian47_12 := by kernel_rfl
private def c2GroupHessian47_13Chunk0 : Poly := [([0,0], -12),([0,2], -8),([0,4], 4),([0,7], 40),([0,8], -40),([2,4], 4),([2,8], -20),([6,7], 40),([7,9], 40),([8,8], -40)]
def c2GroupHessian47_13 : Poly := List.flatten [c2GroupHessian47_13Chunk0]
theorem c2GroupHessian47_13_check : sumFast (c2TensorGroup47.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian47_13 := by kernel_rfl
private def c2GroupHessian47_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 32),([0,7], 80),([0,9], 80),([3,3], 40),([3,7], 80),([3,9], 80),([5,5], 16),([7,7], 40),([7,9], 80),([9,9], 40)]
def c2GroupHessian47_22 : Poly := List.flatten [c2GroupHessian47_22Chunk0]
theorem c2GroupHessian47_22_check : sumFast (c2TensorGroup47.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian47_22 := by kernel_rfl
private def c2GroupHessian47_23Chunk0 : Poly := [([0,0], -48),([0,3], -40),([0,4], -4),([0,5], -8),([0,6], -40),([0,7], -40),([0,8], -20),([0,9], -80),([3,6], -40),([3,9], -40),([4,5], -4),([5,8], -20),([6,7], -40),([6,9], -40),([7,9], -40),([9,9], -40)]
def c2GroupHessian47_23 : Poly := List.flatten [c2GroupHessian47_23Chunk0]
theorem c2GroupHessian47_23_check : sumFast (c2TensorGroup47.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian47_23 := by kernel_rfl
private def c2GroupHessian47_33Chunk0 : Poly := [([0,0], 56),([0,4], 8),([0,6], 80),([0,8], 40),([0,9], 80),([4,4], 8),([6,6], 40),([6,9], 80),([8,8], 40),([9,9], 40)]
def c2GroupHessian47_33 : Poly := List.flatten [c2GroupHessian47_33Chunk0]
theorem c2GroupHessian47_33_check : sumFast (c2TensorGroup47.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian47_33 := by kernel_rfl
end D4.Secondary
