import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup198_det_check : c2TensorGroup198.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 253)) = true := by kernel_rfl
private def c2GroupHessian198_00Chunk0 : Poly := [([0,0], 56),([0,1], 8),([0,5], 80),([0,6], 40),([1,1], 8),([5,5], 40),([6,6], 40)]
def c2GroupHessian198_00 : Poly := List.flatten [c2GroupHessian198_00Chunk0]
theorem c2GroupHessian198_00_check : sumFast (c2TensorGroup198.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian198_00 := by kernel_rfl
private def c2GroupHessian198_01Chunk0 : Poly := [([0,0], 56),([0,1], 4),([0,2], -8),([0,5], 40),([0,6], 20),([0,7], 40),([0,8], 20),([1,2], 4),([2,6], -20),([5,7], 40),([6,8], 40)]
def c2GroupHessian198_01 : Poly := List.flatten [c2GroupHessian198_01Chunk0]
theorem c2GroupHessian198_01_check : sumFast (c2TensorGroup198.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian198_01 := by kernel_rfl
private def c2GroupHessian198_02Chunk0 : Poly := [([0,0], -80),([0,3], -40),([0,5], -120),([0,7], -40),([0,9], -40),([3,5], -40),([5,5], -40),([5,7], -40),([5,9], -40)]
def c2GroupHessian198_02 : Poly := List.flatten [c2GroupHessian198_02Chunk0]
theorem c2GroupHessian198_02_check : sumFast (c2TensorGroup198.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian198_02 := by kernel_rfl
private def c2GroupHessian198_03Chunk0 : Poly := [([0,0], -24),([0,4], -8),([0,6], -60),([0,8], -20),([0,9], 40),([1,4], 4),([4,6], -20),([5,9], 40),([6,6], -40),([6,8], -40)]
def c2GroupHessian198_03 : Poly := List.flatten [c2GroupHessian198_03Chunk0]
theorem c2GroupHessian198_03_check : sumFast (c2TensorGroup198.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian198_03 := by kernel_rfl
private def c2GroupHessian198_11Chunk0 : Poly := [([0,0], 56),([0,2], -16),([0,7], 80),([0,8], 40),([2,2], 16),([2,8], -40),([7,7], 40),([8,8], 40)]
def c2GroupHessian198_11 : Poly := List.flatten [c2GroupHessian198_11Chunk0]
theorem c2GroupHessian198_11_check : sumFast (c2TensorGroup198.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian198_11 := by kernel_rfl
private def c2GroupHessian198_12Chunk0 : Poly := [([0,0], -80),([0,3], -40),([0,5], -40),([0,7], -120),([0,9], -40),([3,7], -40),([5,7], -40),([7,7], -40),([7,9], -40)]
def c2GroupHessian198_12 : Poly := List.flatten [c2GroupHessian198_12Chunk0]
theorem c2GroupHessian198_12_check : sumFast (c2TensorGroup198.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian198_12 := by kernel_rfl
private def c2GroupHessian198_13Chunk0 : Poly := [([0,0], -24),([0,2], 24),([0,4], -8),([0,6], -20),([0,8], -60),([0,9], 40),([2,4], 16),([2,6], 20),([2,8], 20),([4,8], -20),([6,8], -40),([7,9], 40),([8,8], -40)]
def c2GroupHessian198_13 : Poly := List.flatten [c2GroupHessian198_13Chunk0]
theorem c2GroupHessian198_13_check : sumFast (c2TensorGroup198.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian198_13 := by kernel_rfl
private def c2GroupHessian198_22Chunk0 : Poly := [([0,0], 160),([0,3], 160),([0,5], 160),([0,7], 160),([0,9], 160),([3,3], 40),([3,5], 80),([3,7], 80),([3,9], 80),([5,5], 40),([5,7], 80),([5,9], 80),([7,7], 40),([7,9], 80),([9,9], 40)]
def c2GroupHessian198_22 : Poly := List.flatten [c2GroupHessian198_22Chunk0]
theorem c2GroupHessian198_22_check : sumFast (c2TensorGroup198.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian198_22 := by kernel_rfl
private def c2GroupHessian198_23Chunk0 : Poly := [([0,9], -80),([3,9], -40),([5,9], -40),([7,9], -40),([9,9], -40)]
def c2GroupHessian198_23 : Poly := List.flatten [c2GroupHessian198_23Chunk0]
theorem c2GroupHessian198_23_check : sumFast (c2TensorGroup198.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian198_23 := by kernel_rfl
private def c2GroupHessian198_33Chunk0 : Poly := [([0,0], 48),([0,4], 48),([0,6], 80),([0,8], 80),([4,4], 16),([4,6], 40),([4,8], 40),([6,6], 40),([6,8], 80),([8,8], 40),([9,9], 40)]
def c2GroupHessian198_33 : Poly := List.flatten [c2GroupHessian198_33Chunk0]
theorem c2GroupHessian198_33_check : sumFast (c2TensorGroup198.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian198_33 := by kernel_rfl
end D4.Secondary
