import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup72_det_check : c2TensorGroup72.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 97)) = true := by kernel_rfl
private def c2GroupHessian72_00Chunk0 : Poly := [([0,0], 320),([0,1], 320),([0,5], 320),([0,6], 320),([1,1], 80),([1,5], 160),([1,6], 160),([5,5], 80),([5,6], 160),([6,6], 80)]
def c2GroupHessian72_00 : Poly := List.flatten [c2GroupHessian72_00Chunk0]
theorem c2GroupHessian72_00_check : sumFast (c2TensorGroup72.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian72_00 := by kernel_rfl
private def c2GroupHessian72_01Chunk0 : Poly := [([0,0], 160),([0,1], 80),([0,5], 80),([0,6], 80)]
def c2GroupHessian72_01 : Poly := List.flatten [c2GroupHessian72_01Chunk0]
theorem c2GroupHessian72_01_check : sumFast (c2TensorGroup72.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian72_01 := by kernel_rfl
private def c2GroupHessian72_02Chunk0 : Poly := [([0,0], -160),([0,1], -80),([0,5], -240),([0,6], -80),([1,5], -80),([5,5], -80),([5,6], -80)]
def c2GroupHessian72_02 : Poly := List.flatten [c2GroupHessian72_02Chunk0]
theorem c2GroupHessian72_02_check : sumFast (c2TensorGroup72.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian72_02 := by kernel_rfl
private def c2GroupHessian72_03Chunk0 : Poly := [([0,0], -160),([0,1], -80),([0,5], -80),([0,6], -240),([1,6], -80),([5,6], -80),([6,6], -80)]
def c2GroupHessian72_03 : Poly := List.flatten [c2GroupHessian72_03Chunk0]
theorem c2GroupHessian72_03_check : sumFast (c2TensorGroup72.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian72_03 := by kernel_rfl
private def c2GroupHessian72_11Chunk0 : Poly := [([0,0], 112),([0,2], -8),([0,7], 64),([0,8], 64),([2,2], 24),([2,7], -8),([2,8], -8),([7,7], 32),([7,8], 64),([8,8], 32)]
def c2GroupHessian72_11 : Poly := List.flatten [c2GroupHessian72_11Chunk0]
theorem c2GroupHessian72_11_check : sumFast (c2TensorGroup72.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian72_11 := by kernel_rfl
private def c2GroupHessian72_12Chunk0 : Poly := [([0,0], -120),([0,2], 20),([0,3], -40),([0,5], -80),([0,7], -72),([0,8], -40),([0,9], -4),([2,3], 20),([2,7], 4),([2,9], 8),([3,7], -40),([3,8], -40),([7,7], -32),([7,8], -32),([7,9], -4),([8,9], -4)]
def c2GroupHessian72_12 : Poly := List.flatten [c2GroupHessian72_12Chunk0]
theorem c2GroupHessian72_12_check : sumFast (c2TensorGroup72.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian72_12 := by kernel_rfl
private def c2GroupHessian72_13Chunk0 : Poly := [([0,0], -112),([0,2], 4),([0,4], -40),([0,6], -80),([0,7], -32),([0,8], -64),([0,9], 4),([2,4], 20),([2,8], 4),([2,9], -8),([4,7], -40),([4,8], -40),([7,8], -32),([7,9], 4),([8,8], -32),([8,9], 4)]
def c2GroupHessian72_13 : Poly := List.flatten [c2GroupHessian72_13Chunk0]
theorem c2GroupHessian72_13_check : sumFast (c2TensorGroup72.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian72_13 := by kernel_rfl
private def c2GroupHessian72_22Chunk0 : Poly := [([0,0], 160),([0,3], 160),([0,5], 160),([0,7], 80),([0,9], 40),([3,3], 80),([3,7], 80),([3,9], 40),([5,5], 80),([7,7], 32),([7,9], 8),([9,9], 24)]
def c2GroupHessian72_22 : Poly := List.flatten [c2GroupHessian72_22Chunk0]
theorem c2GroupHessian72_22_check : sumFast (c2TensorGroup72.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian72_22 := by kernel_rfl
private def c2GroupHessian72_23Chunk0 : Poly := [([0,0], 120),([0,3], 40),([0,4], 80),([0,5], 80),([0,6], 80),([0,7], 32),([0,8], 40),([0,9], -16),([3,4], 80),([3,8], 40),([3,9], -20),([4,7], 40),([4,9], 20),([5,6], 80),([7,8], 32),([7,9], -4),([8,9], 4),([9,9], -24)]
def c2GroupHessian72_23 : Poly := List.flatten [c2GroupHessian72_23Chunk0]
theorem c2GroupHessian72_23_check : sumFast (c2TensorGroup72.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian72_23 := by kernel_rfl
private def c2GroupHessian72_33Chunk0 : Poly := [([0,0], 112),([0,4], 80),([0,6], 160),([0,8], 64),([0,9], -8),([4,4], 80),([4,8], 80),([4,9], -40),([6,6], 80),([8,8], 32),([8,9], -8),([9,9], 24)]
def c2GroupHessian72_33 : Poly := List.flatten [c2GroupHessian72_33Chunk0]
theorem c2GroupHessian72_33_check : sumFast (c2TensorGroup72.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian72_33 := by kernel_rfl
end D4.Secondary
