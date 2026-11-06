import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup181_det_check : c2TensorGroup181.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 228)) = true := by kernel_rfl
private def c2GroupHessian181_00Chunk0 : Poly := [([0,0], 56),([0,1], -16),([0,5], 40),([0,6], 32),([1,1], 16),([1,5], -40),([1,6], -16),([5,5], 40),([5,6], 40),([6,6], 16)]
def c2GroupHessian181_00 : Poly := List.flatten [c2GroupHessian181_00Chunk0]
theorem c2GroupHessian181_00_check : sumFast (c2TensorGroup181.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian181_00 := by kernel_rfl
private def c2GroupHessian181_01Chunk0 : Poly := [([0,0], 80),([0,2], 40),([0,7], 40),([0,8], 40)]
def c2GroupHessian181_01 : Poly := List.flatten [c2GroupHessian181_01Chunk0]
theorem c2GroupHessian181_01_check : sumFast (c2TensorGroup181.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian181_01 := by kernel_rfl
private def c2GroupHessian181_02Chunk0 : Poly := [([0,0], -48),([0,1], 16),([0,3], -8),([0,5], -40),([0,6], -8),([0,7], -40),([0,9], 4),([1,3], 16),([1,5], 20),([1,9], 4),([3,5], -20),([3,6], -8),([5,5], -40),([5,6], -20),([6,9], 4)]
def c2GroupHessian181_02 : Poly := List.flatten [c2GroupHessian181_02Chunk0]
theorem c2GroupHessian181_02_check : sumFast (c2TensorGroup181.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian181_02 := by kernel_rfl
private def c2GroupHessian181_03Chunk0 : Poly := [([0,0], -56),([0,1], 8),([0,4], -8),([0,5], -20),([0,6], -32),([0,8], -40),([0,9], -4),([1,4], 16),([1,6], 8),([1,9], -4),([4,5], -20),([4,6], -8),([5,6], -20),([6,6], -16),([6,9], -4)]
def c2GroupHessian181_03 : Poly := List.flatten [c2GroupHessian181_03Chunk0]
theorem c2GroupHessian181_03_check : sumFast (c2TensorGroup181.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian181_03 := by kernel_rfl
private def c2GroupHessian181_11Chunk0 : Poly := [([0,0], 160),([0,2], 160),([0,7], 160),([0,8], 160),([2,2], 40),([2,7], 80),([2,8], 80),([7,7], 40),([7,8], 80),([8,8], 40)]
def c2GroupHessian181_11 : Poly := List.flatten [c2GroupHessian181_11Chunk0]
theorem c2GroupHessian181_11_check : sumFast (c2TensorGroup181.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian181_11 := by kernel_rfl
private def c2GroupHessian181_12Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -120),([0,8], -40),([2,7], -40),([7,7], -40),([7,8], -40)]
def c2GroupHessian181_12 : Poly := List.flatten [c2GroupHessian181_12Chunk0]
theorem c2GroupHessian181_12_check : sumFast (c2TensorGroup181.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian181_12 := by kernel_rfl
private def c2GroupHessian181_13Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -40),([0,8], -120),([2,8], -40),([7,8], -40),([8,8], -40)]
def c2GroupHessian181_13 : Poly := List.flatten [c2GroupHessian181_13Chunk0]
theorem c2GroupHessian181_13_check : sumFast (c2TensorGroup181.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian181_13 := by kernel_rfl
private def c2GroupHessian181_22Chunk0 : Poly := [([0,0], 56),([0,3], 32),([0,5], 40),([0,7], 80),([0,9], 8),([3,3], 16),([3,5], 40),([3,9], 8),([5,5], 40),([7,7], 40),([9,9], 8)]
def c2GroupHessian181_22 : Poly := List.flatten [c2GroupHessian181_22Chunk0]
theorem c2GroupHessian181_22_check : sumFast (c2TensorGroup181.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian181_22 := by kernel_rfl
private def c2GroupHessian181_23Chunk0 : Poly := [([0,0], 48),([0,3], 8),([0,4], 16),([0,5], 20),([0,6], 8),([0,7], 40),([0,8], 40),([0,9], -8),([3,4], 16),([3,6], 8),([3,9], -4),([4,5], 20),([4,9], 4),([5,6], 20),([6,9], -4),([7,8], 40),([9,9], -8)]
def c2GroupHessian181_23 : Poly := List.flatten [c2GroupHessian181_23Chunk0]
theorem c2GroupHessian181_23_check : sumFast (c2TensorGroup181.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian181_23 := by kernel_rfl
private def c2GroupHessian181_33Chunk0 : Poly := [([0,0], 56),([0,4], 16),([0,6], 32),([0,8], 80),([0,9], 8),([4,4], 16),([4,6], 16),([4,9], -8),([6,6], 16),([6,9], 8),([8,8], 40),([9,9], 8)]
def c2GroupHessian181_33 : Poly := List.flatten [c2GroupHessian181_33Chunk0]
theorem c2GroupHessian181_33_check : sumFast (c2TensorGroup181.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian181_33 := by kernel_rfl
end D4.Secondary
