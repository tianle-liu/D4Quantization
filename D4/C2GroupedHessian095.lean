import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup95_det_check : c2TensorGroup95.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 125)) = true := by kernel_rfl
private def c2GroupHessian95_00Chunk0 : Poly := [([0,0], 160),([0,1], 160),([0,5], 160),([0,6], 160),([1,1], 40),([1,5], 80),([1,6], 80),([5,5], 40),([5,6], 80),([6,6], 40)]
def c2GroupHessian95_00 : Poly := List.flatten [c2GroupHessian95_00Chunk0]
theorem c2GroupHessian95_00_check : sumFast (c2TensorGroup95.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian95_00 := by kernel_rfl
private def c2GroupHessian95_01Chunk0 : Poly := [([0,0], 80),([0,1], 40),([0,5], 40),([0,6], 40)]
def c2GroupHessian95_01 : Poly := List.flatten [c2GroupHessian95_01Chunk0]
theorem c2GroupHessian95_01_check : sumFast (c2TensorGroup95.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian95_01 := by kernel_rfl
private def c2GroupHessian95_02Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -120),([0,6], -40),([1,5], -40),([5,5], -40),([5,6], -40)]
def c2GroupHessian95_02 : Poly := List.flatten [c2GroupHessian95_02Chunk0]
theorem c2GroupHessian95_02_check : sumFast (c2TensorGroup95.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian95_02 := by kernel_rfl
private def c2GroupHessian95_03Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -40),([0,6], -120),([1,6], -40),([5,6], -40),([6,6], -40)]
def c2GroupHessian95_03 : Poly := List.flatten [c2GroupHessian95_03Chunk0]
theorem c2GroupHessian95_03_check : sumFast (c2TensorGroup95.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian95_03 := by kernel_rfl
private def c2GroupHessian95_11Chunk0 : Poly := [([0,0], 48),([0,2], 8),([0,7], 16),([0,8], 16),([2,2], 16),([2,7], 8),([2,8], 8),([7,7], 8),([7,8], 16),([8,8], 8)]
def c2GroupHessian95_11 : Poly := List.flatten [c2GroupHessian95_11Chunk0]
theorem c2GroupHessian95_11_check : sumFast (c2TensorGroup95.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian95_11 := by kernel_rfl
private def c2GroupHessian95_12Chunk0 : Poly := [([0,0], -40),([0,2], 4),([0,3], 4),([0,5], -40),([0,7], -8),([0,9], 4),([2,3], 16),([2,7], -4),([2,9], -8),([3,7], 4),([3,8], 4),([7,7], -8),([7,8], -8),([7,9], 4),([8,9], 4)]
def c2GroupHessian95_12 : Poly := List.flatten [c2GroupHessian95_12Chunk0]
theorem c2GroupHessian95_12_check : sumFast (c2TensorGroup95.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian95_12 := by kernel_rfl
private def c2GroupHessian95_13Chunk0 : Poly := [([0,0], -44),([0,2], 8),([0,4], 4),([0,6], -40),([0,7], -4),([0,8], -12),([0,9], -4),([2,4], 16),([2,8], -4),([2,9], 8),([4,7], 4),([4,8], 4),([7,8], -8),([7,9], -4),([8,8], -8),([8,9], -4)]
def c2GroupHessian95_13 : Poly := List.flatten [c2GroupHessian95_13Chunk0]
theorem c2GroupHessian95_13_check : sumFast (c2TensorGroup95.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian95_13 := by kernel_rfl
private def c2GroupHessian95_22Chunk0 : Poly := [([0,0], 48),([0,3], 8),([0,5], 80),([0,9], 8),([3,3], 16),([3,7], -8),([3,9], -16),([5,5], 40),([7,7], 8),([7,9], -8),([9,9], 16)]
def c2GroupHessian95_22 : Poly := List.flatten [c2GroupHessian95_22Chunk0]
theorem c2GroupHessian95_22_check : sumFast (c2TensorGroup95.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian95_22 := by kernel_rfl
private def c2GroupHessian95_23Chunk0 : Poly := [([0,0], 36),([0,3], 8),([0,4], 4),([0,5], 40),([0,6], 40),([0,7], 4),([0,9], -20),([3,4], 16),([3,8], -4),([3,9], 8),([4,7], -4),([4,9], -8),([5,6], 40),([7,8], 8),([7,9], 4),([8,9], -4),([9,9], -16)]
def c2GroupHessian95_23 : Poly := List.flatten [c2GroupHessian95_23Chunk0]
theorem c2GroupHessian95_23_check : sumFast (c2TensorGroup95.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian95_23 := by kernel_rfl
private def c2GroupHessian95_33Chunk0 : Poly := [([0,0], 56),([0,4], 16),([0,6], 80),([0,8], 8),([0,9], 32),([4,4], 16),([4,8], -8),([4,9], 16),([6,6], 40),([8,8], 8),([8,9], 8),([9,9], 16)]
def c2GroupHessian95_33 : Poly := List.flatten [c2GroupHessian95_33Chunk0]
theorem c2GroupHessian95_33_check : sumFast (c2TensorGroup95.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian95_33 := by kernel_rfl
end D4.Secondary
