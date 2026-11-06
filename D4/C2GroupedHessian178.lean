import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup178_det_check : c2TensorGroup178.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 223)) = true := by kernel_rfl
private def c2GroupHessian178_00Chunk0 : Poly := [([0,0], 56),([0,1], 32),([0,5], 32),([0,6], 32),([1,1], 16),([1,5], 32),([1,6], 32),([5,5], 16),([5,6], 32),([6,6], 16)]
def c2GroupHessian178_00 : Poly := List.flatten [c2GroupHessian178_00Chunk0]
theorem c2GroupHessian178_00_check : sumFast (c2TensorGroup178.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian178_00 := by kernel_rfl
private def c2GroupHessian178_01Chunk0 : Poly := [([0,0], 80),([0,2], 40),([0,7], 40),([0,8], 40)]
def c2GroupHessian178_01 : Poly := List.flatten [c2GroupHessian178_01Chunk0]
theorem c2GroupHessian178_01_check : sumFast (c2TensorGroup178.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian178_01 := by kernel_rfl
private def c2GroupHessian178_02Chunk0 : Poly := [([0,0], -48),([0,1], -8),([0,3], 4),([0,5], -24),([0,6], -8),([0,7], -40),([0,9], -8),([1,3], 4),([1,5], -16),([1,9], -8),([3,5], 4),([3,6], 4),([5,5], -16),([5,6], -16),([5,9], -8),([6,9], -8)]
def c2GroupHessian178_02 : Poly := List.flatten [c2GroupHessian178_02Chunk0]
theorem c2GroupHessian178_02_check : sumFast (c2TensorGroup178.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian178_02 := by kernel_rfl
private def c2GroupHessian178_03Chunk0 : Poly := [([0,0], -44),([0,1], -4),([0,4], 4),([0,5], -4),([0,6], -20),([0,8], -40),([0,9], 8),([1,4], 4),([1,6], -16),([1,9], 8),([4,5], 4),([4,6], 4),([5,6], -16),([5,9], 8),([6,6], -16),([6,9], 8)]
def c2GroupHessian178_03 : Poly := List.flatten [c2GroupHessian178_03Chunk0]
theorem c2GroupHessian178_03_check : sumFast (c2TensorGroup178.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian178_03 := by kernel_rfl
private def c2GroupHessian178_11Chunk0 : Poly := [([0,0], 160),([0,2], 160),([0,7], 160),([0,8], 160),([2,2], 40),([2,7], 80),([2,8], 80),([7,7], 40),([7,8], 80),([8,8], 40)]
def c2GroupHessian178_11 : Poly := List.flatten [c2GroupHessian178_11Chunk0]
theorem c2GroupHessian178_11_check : sumFast (c2TensorGroup178.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian178_11 := by kernel_rfl
private def c2GroupHessian178_12Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -120),([0,8], -40),([2,7], -40),([7,7], -40),([7,8], -40)]
def c2GroupHessian178_12 : Poly := List.flatten [c2GroupHessian178_12Chunk0]
theorem c2GroupHessian178_12_check : sumFast (c2TensorGroup178.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian178_12 := by kernel_rfl
private def c2GroupHessian178_13Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -40),([0,8], -120),([2,8], -40),([7,8], -40),([8,8], -40)]
def c2GroupHessian178_13 : Poly := List.flatten [c2GroupHessian178_13Chunk0]
theorem c2GroupHessian178_13_check : sumFast (c2TensorGroup178.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian178_13 := by kernel_rfl
private def c2GroupHessian178_22Chunk0 : Poly := [([0,0], 56),([0,3], 8),([0,5], 16),([0,7], 80),([0,9], 32),([3,3], 8),([3,5], -8),([3,9], 8),([5,5], 16),([5,9], 16),([7,7], 40),([9,9], 16)]
def c2GroupHessian178_22 : Poly := List.flatten [c2GroupHessian178_22Chunk0]
theorem c2GroupHessian178_22_check : sumFast (c2TensorGroup178.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian178_22 := by kernel_rfl
private def c2GroupHessian178_23Chunk0 : Poly := [([0,0], 36),([0,4], 4),([0,5], 4),([0,6], 8),([0,7], 40),([0,8], 40),([0,9], -20),([3,4], 8),([3,6], -4),([3,9], -4),([4,5], -4),([4,9], 4),([5,6], 16),([5,9], -8),([6,9], 8),([7,8], 40),([9,9], -16)]
def c2GroupHessian178_23 : Poly := List.flatten [c2GroupHessian178_23Chunk0]
theorem c2GroupHessian178_23_check : sumFast (c2TensorGroup178.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian178_23 := by kernel_rfl
private def c2GroupHessian178_33Chunk0 : Poly := [([0,0], 48),([0,6], 8),([0,8], 80),([0,9], 8),([4,4], 8),([4,6], -8),([4,9], -8),([6,6], 16),([6,9], -16),([8,8], 40),([9,9], 16)]
def c2GroupHessian178_33 : Poly := List.flatten [c2GroupHessian178_33Chunk0]
theorem c2GroupHessian178_33_check : sumFast (c2TensorGroup178.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian178_33 := by kernel_rfl
end D4.Secondary
