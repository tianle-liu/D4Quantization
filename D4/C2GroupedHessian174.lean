import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup174_det_check : c2TensorGroup174.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 218)) = true := by kernel_rfl
private def c2GroupHessian174_00Chunk0 : Poly := [([0,0], 160),([0,1], 40),([0,5], 160),([0,6], 160),([1,1], 24),([1,5], 40),([1,6], 40),([5,5], 80),([5,6], 160),([6,6], 80)]
def c2GroupHessian174_00 : Poly := List.flatten [c2GroupHessian174_00Chunk0]
theorem c2GroupHessian174_00_check : sumFast (c2TensorGroup174.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian174_00 := by kernel_rfl
private def c2GroupHessian174_01Chunk0 : Poly := [([0,0], 160),([0,2], 80),([0,7], 80),([0,8], 80)]
def c2GroupHessian174_01 : Poly := List.flatten [c2GroupHessian174_01Chunk0]
theorem c2GroupHessian174_01_check : sumFast (c2TensorGroup174.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian174_01 := by kernel_rfl
private def c2GroupHessian174_02Chunk0 : Poly := [([0,0], -120),([0,1], -4),([0,3], -40),([0,5], -120),([0,6], -40),([0,7], -80),([0,9], 20),([1,3], -4),([1,5], -20),([1,9], 8),([3,5], -40),([3,6], -40),([5,5], -80),([5,6], -80),([5,9], 20),([6,9], 20)]
def c2GroupHessian174_02 : Poly := List.flatten [c2GroupHessian174_02Chunk0]
theorem c2GroupHessian174_02_check : sumFast (c2TensorGroup174.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian174_02 := by kernel_rfl
private def c2GroupHessian174_03Chunk0 : Poly := [([0,0], -160),([0,1], -20),([0,4], -40),([0,5], -80),([0,6], -160),([0,8], -80),([0,9], -20),([1,4], -4),([1,6], -20),([1,9], -8),([4,5], -40),([4,6], -40),([5,6], -80),([5,9], -20),([6,6], -80),([6,9], -20)]
def c2GroupHessian174_03 : Poly := List.flatten [c2GroupHessian174_03Chunk0]
theorem c2GroupHessian174_03_check : sumFast (c2TensorGroup174.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian174_03 := by kernel_rfl
private def c2GroupHessian174_11Chunk0 : Poly := [([0,0], 320),([0,2], 320),([0,7], 320),([0,8], 320),([2,2], 80),([2,7], 160),([2,8], 160),([7,7], 80),([7,8], 160),([8,8], 80)]
def c2GroupHessian174_11 : Poly := List.flatten [c2GroupHessian174_11Chunk0]
theorem c2GroupHessian174_11_check : sumFast (c2TensorGroup174.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian174_11 := by kernel_rfl
private def c2GroupHessian174_12Chunk0 : Poly := [([0,0], -160),([0,2], -80),([0,7], -240),([0,8], -80),([2,7], -80),([7,7], -80),([7,8], -80)]
def c2GroupHessian174_12 : Poly := List.flatten [c2GroupHessian174_12Chunk0]
theorem c2GroupHessian174_12_check : sumFast (c2TensorGroup174.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian174_12 := by kernel_rfl
private def c2GroupHessian174_13Chunk0 : Poly := [([0,0], -160),([0,2], -80),([0,7], -80),([0,8], -240),([2,8], -80),([7,8], -80),([8,8], -80)]
def c2GroupHessian174_13 : Poly := List.flatten [c2GroupHessian174_13Chunk0]
theorem c2GroupHessian174_13_check : sumFast (c2TensorGroup174.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian174_13 := by kernel_rfl
private def c2GroupHessian174_22Chunk0 : Poly := [([0,0], 112),([0,3], 64),([0,5], 80),([0,7], 160),([0,9], -8),([3,3], 32),([3,5], 80),([3,9], -8),([5,5], 80),([5,9], -40),([7,7], 80),([9,9], 24)]
def c2GroupHessian174_22 : Poly := List.flatten [c2GroupHessian174_22Chunk0]
theorem c2GroupHessian174_22_check : sumFast (c2TensorGroup174.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian174_22 := by kernel_rfl
private def c2GroupHessian174_23Chunk0 : Poly := [([0,0], 120),([0,3], 40),([0,4], 32),([0,5], 80),([0,6], 40),([0,7], 80),([0,8], 80),([0,9], -16),([3,4], 32),([3,6], 40),([3,9], 4),([4,5], 40),([4,9], -4),([5,6], 80),([5,9], 20),([6,9], -20),([7,8], 80),([9,9], -24)]
def c2GroupHessian174_23 : Poly := List.flatten [c2GroupHessian174_23Chunk0]
theorem c2GroupHessian174_23_check : sumFast (c2TensorGroup174.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian174_23 := by kernel_rfl
private def c2GroupHessian174_33Chunk0 : Poly := [([0,0], 160),([0,4], 80),([0,6], 160),([0,8], 160),([0,9], 40),([4,4], 32),([4,6], 80),([4,9], 8),([6,6], 80),([6,9], 40),([8,8], 80),([9,9], 24)]
def c2GroupHessian174_33 : Poly := List.flatten [c2GroupHessian174_33Chunk0]
theorem c2GroupHessian174_33_check : sumFast (c2TensorGroup174.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian174_33 := by kernel_rfl
end D4.Secondary
