import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup212_det_check : c2TensorGroup212.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 270)) = true := by kernel_rfl
private def c2GroupHessian212_00Chunk0 : Poly := [([0,0], 112),([0,1], -8),([0,5], 64),([0,6], 160),([1,1], 24),([1,5], -8),([5,5], 32),([6,6], 80)]
def c2GroupHessian212_00 : Poly := List.flatten [c2GroupHessian212_00Chunk0]
theorem c2GroupHessian212_00_check : sumFast (c2TensorGroup212.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian212_00 := by kernel_rfl
private def c2GroupHessian212_01Chunk0 : Poly := [([0,0], 112),([0,1], -4),([0,2], -4),([0,5], 32),([0,6], 80),([0,7], 32),([0,8], 80),([1,2], 8),([1,7], -4),([2,5], -4),([5,7], 32),([6,8], 80)]
def c2GroupHessian212_01 : Poly := List.flatten [c2GroupHessian212_01Chunk0]
theorem c2GroupHessian212_01_check : sumFast (c2TensorGroup212.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian212_01 := by kernel_rfl
private def c2GroupHessian212_02Chunk0 : Poly := [([0,0], -72),([0,1], 24),([0,3], -40),([0,5], -104),([0,7], -32),([0,9], 80),([1,3], 20),([1,5], 4),([1,7], 4),([3,5], -40),([5,5], -32),([5,7], -32),([6,9], 80)]
def c2GroupHessian212_02 : Poly := List.flatten [c2GroupHessian212_02Chunk0]
theorem c2GroupHessian212_02_check : sumFast (c2TensorGroup212.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian212_02 := by kernel_rfl
private def c2GroupHessian212_03Chunk0 : Poly := [([0,0], -160),([0,4], -80),([0,6], -240),([0,8], -80),([0,9], -80),([4,6], -80),([6,6], -80),([6,8], -80),([6,9], -80)]
def c2GroupHessian212_03 : Poly := List.flatten [c2GroupHessian212_03Chunk0]
theorem c2GroupHessian212_03_check : sumFast (c2TensorGroup212.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian212_03 := by kernel_rfl
private def c2GroupHessian212_11Chunk0 : Poly := [([0,0], 112),([0,2], -8),([0,7], 64),([0,8], 160),([2,2], 24),([2,7], -8),([7,7], 32),([8,8], 80)]
def c2GroupHessian212_11 : Poly := List.flatten [c2GroupHessian212_11Chunk0]
theorem c2GroupHessian212_11_check : sumFast (c2TensorGroup212.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian212_11 := by kernel_rfl
private def c2GroupHessian212_12Chunk0 : Poly := [([0,0], -72),([0,2], 24),([0,3], -40),([0,5], -32),([0,7], -104),([0,9], 80),([2,3], 20),([2,5], 4),([2,7], 4),([3,7], -40),([5,7], -32),([7,7], -32),([8,9], 80)]
def c2GroupHessian212_12 : Poly := List.flatten [c2GroupHessian212_12Chunk0]
theorem c2GroupHessian212_12_check : sumFast (c2TensorGroup212.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian212_12 := by kernel_rfl
private def c2GroupHessian212_13Chunk0 : Poly := [([0,0], -160),([0,4], -80),([0,6], -80),([0,8], -240),([0,9], -80),([4,8], -80),([6,8], -80),([8,8], -80),([8,9], -80)]
def c2GroupHessian212_13 : Poly := List.flatten [c2GroupHessian212_13Chunk0]
theorem c2GroupHessian212_13_check : sumFast (c2TensorGroup212.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian212_13 := by kernel_rfl
private def c2GroupHessian212_22Chunk0 : Poly := [([0,0], 192),([0,3], 240),([0,5], 144),([0,7], 144),([3,3], 80),([3,5], 80),([3,7], 80),([5,5], 32),([5,7], 64),([7,7], 32),([9,9], 80)]
def c2GroupHessian212_22 : Poly := List.flatten [c2GroupHessian212_22Chunk0]
theorem c2GroupHessian212_22_check : sumFast (c2TensorGroup212.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian212_22 := by kernel_rfl
private def c2GroupHessian212_23Chunk0 : Poly := [([0,9], -160),([4,9], -80),([6,9], -80),([8,9], -80),([9,9], -80)]
def c2GroupHessian212_23 : Poly := List.flatten [c2GroupHessian212_23Chunk0]
theorem c2GroupHessian212_23_check : sumFast (c2TensorGroup212.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian212_23 := by kernel_rfl
private def c2GroupHessian212_33Chunk0 : Poly := [([0,0], 320),([0,4], 320),([0,6], 320),([0,8], 320),([0,9], 320),([4,4], 80),([4,6], 160),([4,8], 160),([4,9], 160),([6,6], 80),([6,8], 160),([6,9], 160),([8,8], 80),([8,9], 160),([9,9], 80)]
def c2GroupHessian212_33 : Poly := List.flatten [c2GroupHessian212_33Chunk0]
theorem c2GroupHessian212_33_check : sumFast (c2TensorGroup212.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian212_33 := by kernel_rfl
end D4.Secondary
