import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup81_det_check : c2TensorGroup81.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 107)) = true := by kernel_rfl
private def c2GroupHessian81_00Chunk0 : Poly := [([0,0], 160),([0,1], 160),([0,5], 160),([0,6], 160),([1,1], 40),([1,5], 80),([1,6], 80),([5,5], 40),([5,6], 80),([6,6], 40)]
def c2GroupHessian81_00 : Poly := List.flatten [c2GroupHessian81_00Chunk0]
theorem c2GroupHessian81_00_check : sumFast (c2TensorGroup81.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian81_00 := by kernel_rfl
private def c2GroupHessian81_01Chunk0 : Poly := [([0,0], 80),([0,1], 40),([0,5], 40),([0,6], 40)]
def c2GroupHessian81_01 : Poly := List.flatten [c2GroupHessian81_01Chunk0]
theorem c2GroupHessian81_01_check : sumFast (c2TensorGroup81.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian81_01 := by kernel_rfl
private def c2GroupHessian81_02Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -120),([0,6], -40),([1,5], -40),([5,5], -40),([5,6], -40)]
def c2GroupHessian81_02 : Poly := List.flatten [c2GroupHessian81_02Chunk0]
theorem c2GroupHessian81_02_check : sumFast (c2TensorGroup81.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian81_02 := by kernel_rfl
private def c2GroupHessian81_03Chunk0 : Poly := [([0,0], -80),([0,1], -40),([0,5], -40),([0,6], -120),([1,6], -40),([5,6], -40),([6,6], -40)]
def c2GroupHessian81_03 : Poly := List.flatten [c2GroupHessian81_03Chunk0]
theorem c2GroupHessian81_03_check : sumFast (c2TensorGroup81.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian81_03 := by kernel_rfl
private def c2GroupHessian81_11Chunk0 : Poly := [([0,0], 56),([0,2], 32),([0,7], 32),([0,8], 32),([2,2], 16),([2,7], 32),([2,8], 32),([7,7], 16),([7,8], 32),([8,8], 16)]
def c2GroupHessian81_11 : Poly := List.flatten [c2GroupHessian81_11Chunk0]
theorem c2GroupHessian81_11_check : sumFast (c2TensorGroup81.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian81_11 := by kernel_rfl
private def c2GroupHessian81_12Chunk0 : Poly := [([0,0], -48),([0,2], -8),([0,3], -8),([0,5], -40),([0,7], -24),([0,8], -8),([0,9], 4),([2,3], -8),([2,7], -16),([2,9], 4),([3,7], -8),([3,8], -8),([7,7], -16),([7,8], -16),([7,9], 4),([8,9], 4)]
def c2GroupHessian81_12 : Poly := List.flatten [c2GroupHessian81_12Chunk0]
theorem c2GroupHessian81_12_check : sumFast (c2TensorGroup81.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian81_12 := by kernel_rfl
private def c2GroupHessian81_13Chunk0 : Poly := [([0,0], -56),([0,2], -16),([0,4], -20),([0,6], -40),([0,7], -16),([0,8], -32),([0,9], -4),([2,4], -20),([2,8], -16),([2,9], -4),([4,7], -20),([4,8], -20),([7,8], -16),([7,9], -4),([8,8], -16),([8,9], -4)]
def c2GroupHessian81_13 : Poly := List.flatten [c2GroupHessian81_13Chunk0]
theorem c2GroupHessian81_13_check : sumFast (c2TensorGroup81.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian81_13 := by kernel_rfl
private def c2GroupHessian81_22Chunk0 : Poly := [([0,0], 56),([0,3], 32),([0,5], 80),([0,7], 16),([0,9], 8),([3,3], 16),([3,7], 16),([3,9], 8),([5,5], 40),([7,7], 16),([7,9], -8),([9,9], 8)]
def c2GroupHessian81_22 : Poly := List.flatten [c2GroupHessian81_22Chunk0]
theorem c2GroupHessian81_22_check : sumFast (c2TensorGroup81.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian81_22 := by kernel_rfl
private def c2GroupHessian81_23Chunk0 : Poly := [([0,0], 48),([0,3], 8),([0,4], 20),([0,5], 40),([0,6], 40),([0,7], 16),([0,8], 8),([0,9], -8),([3,4], 20),([3,8], 8),([3,9], -4),([4,7], 20),([5,6], 40),([7,8], 16),([7,9], 4),([8,9], -4),([9,9], -8)]
def c2GroupHessian81_23 : Poly := List.flatten [c2GroupHessian81_23Chunk0]
theorem c2GroupHessian81_23_check : sumFast (c2TensorGroup81.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian81_23 := by kernel_rfl
private def c2GroupHessian81_33Chunk0 : Poly := [([0,0], 56),([0,4], 40),([0,6], 80),([0,8], 32),([0,9], 8),([4,4], 40),([4,8], 40),([6,6], 40),([8,8], 16),([8,9], 8),([9,9], 8)]
def c2GroupHessian81_33 : Poly := List.flatten [c2GroupHessian81_33Chunk0]
theorem c2GroupHessian81_33_check : sumFast (c2TensorGroup81.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian81_33 := by kernel_rfl
end D4.Secondary
