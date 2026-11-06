import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup135_det_check : c2TensorGroup135.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 171)) = true := by kernel_rfl
private def c2GroupHessian135_00Chunk0 : Poly := [([0,0], 48),([0,1], 16),([0,6], 80),([1,1], 8),([5,5], 40),([6,6], 40)]
def c2GroupHessian135_00 : Poly := List.flatten [c2GroupHessian135_00Chunk0]
theorem c2GroupHessian135_00_check : sumFast (c2TensorGroup135.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian135_00 := by kernel_rfl
private def c2GroupHessian135_01Chunk0 : Poly := [([0,0], 24),([0,1], 4),([0,5], -40),([0,6], 20),([0,7], 24),([1,7], 4),([2,5], -40),([5,8], -40),([6,7], 20)]
def c2GroupHessian135_01 : Poly := List.flatten [c2GroupHessian135_01Chunk0]
theorem c2GroupHessian135_01_check : sumFast (c2TensorGroup135.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian135_01 := by kernel_rfl
private def c2GroupHessian135_02Chunk0 : Poly := [([0,0], -24),([0,1], -4),([0,5], -40),([0,6], -20),([0,7], -24),([1,7], -4),([3,5], -40),([5,5], -40),([5,9], -40),([6,7], -20)]
def c2GroupHessian135_02 : Poly := List.flatten [c2GroupHessian135_02Chunk0]
theorem c2GroupHessian135_02_check : sumFast (c2TensorGroup135.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian135_02 := by kernel_rfl
private def c2GroupHessian135_03Chunk0 : Poly := [([0,0], -40),([0,4], -16),([0,5], 40),([0,6], -80),([1,4], 4),([4,6], -20),([5,8], 40),([5,9], 40),([6,6], -40)]
def c2GroupHessian135_03 : Poly := List.flatten [c2GroupHessian135_03Chunk0]
theorem c2GroupHessian135_03_check : sumFast (c2TensorGroup135.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian135_03 := by kernel_rfl
private def c2GroupHessian135_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 32),([0,8], 80),([2,2], 40),([2,8], 80),([7,7], 16),([8,8], 40)]
def c2GroupHessian135_11 : Poly := List.flatten [c2GroupHessian135_11Chunk0]
theorem c2GroupHessian135_11_check : sumFast (c2TensorGroup135.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian135_11 := by kernel_rfl
private def c2GroupHessian135_12Chunk0 : Poly := [([0,0], 24),([0,2], 40),([0,3], 40),([0,5], 40),([0,7], -32),([0,8], 40),([0,9], 40),([2,3], 40),([2,5], 40),([2,9], 40),([3,8], 40),([5,8], 40),([7,7], -16),([8,9], 40)]
def c2GroupHessian135_12 : Poly := List.flatten [c2GroupHessian135_12Chunk0]
theorem c2GroupHessian135_12_check : sumFast (c2TensorGroup135.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian135_12 := by kernel_rfl
private def c2GroupHessian135_13Chunk0 : Poly := [([0,0], -60),([0,2], -40),([0,4], -8),([0,6], -20),([0,7], -20),([0,8], -80),([0,9], -40),([2,8], -40),([2,9], -40),([4,7], -8),([6,7], -20),([8,8], -40),([8,9], -40)]
def c2GroupHessian135_13 : Poly := List.flatten [c2GroupHessian135_13Chunk0]
theorem c2GroupHessian135_13_check : sumFast (c2TensorGroup135.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian135_13 := by kernel_rfl
private def c2GroupHessian135_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 80),([0,7], 32),([0,9], 80),([3,3], 40),([3,5], 80),([3,9], 80),([5,5], 40),([5,9], 80),([7,7], 16),([9,9], 40)]
def c2GroupHessian135_22 : Poly := List.flatten [c2GroupHessian135_22Chunk0]
theorem c2GroupHessian135_22_check : sumFast (c2TensorGroup135.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian135_22 := by kernel_rfl
private def c2GroupHessian135_23Chunk0 : Poly := [([0,0], -20),([0,3], -40),([0,4], 8),([0,5], -40),([0,6], 20),([0,7], 20),([0,8], -40),([0,9], -80),([3,8], -40),([3,9], -40),([4,7], 8),([5,8], -40),([5,9], -40),([6,7], 20),([8,9], -40),([9,9], -40)]
def c2GroupHessian135_23 : Poly := List.flatten [c2GroupHessian135_23Chunk0]
theorem c2GroupHessian135_23_check : sumFast (c2TensorGroup135.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian135_23 := by kernel_rfl
private def c2GroupHessian135_33Chunk0 : Poly := [([0,0], 80),([0,4], 40),([0,6], 80),([0,8], 80),([0,9], 80),([4,4], 16),([4,6], 40),([6,6], 40),([8,8], 40),([8,9], 80),([9,9], 40)]
def c2GroupHessian135_33 : Poly := List.flatten [c2GroupHessian135_33Chunk0]
theorem c2GroupHessian135_33_check : sumFast (c2TensorGroup135.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian135_33 := by kernel_rfl
end D4.Secondary
