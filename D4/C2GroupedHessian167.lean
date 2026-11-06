import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup167_det_check : c2TensorGroup167.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 211)) = true := by kernel_rfl
private def c2GroupHessian167_00Chunk0 : Poly := [([0,0], 80),([0,1], 40),([0,5], 80),([0,6], 80),([1,1], 16),([1,5], 40),([1,6], 40),([5,5], 40),([5,6], 80),([6,6], 40)]
def c2GroupHessian167_00 : Poly := List.flatten [c2GroupHessian167_00Chunk0]
theorem c2GroupHessian167_00_check : sumFast (c2TensorGroup167.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian167_00 := by kernel_rfl
private def c2GroupHessian167_01Chunk0 : Poly := [([0,0], 80),([0,2], 40),([0,7], 40),([0,8], 40)]
def c2GroupHessian167_01 : Poly := List.flatten [c2GroupHessian167_01Chunk0]
theorem c2GroupHessian167_01_check : sumFast (c2TensorGroup167.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian167_01 := by kernel_rfl
private def c2GroupHessian167_02Chunk0 : Poly := [([0,0], -40),([0,1], 4),([0,5], -40),([0,7], -40),([0,9], 40),([1,3], 4),([1,5], -20),([1,9], 20),([5,5], -40),([5,6], -40),([5,9], 40),([6,9], 40)]
def c2GroupHessian167_02 : Poly := List.flatten [c2GroupHessian167_02Chunk0]
theorem c2GroupHessian167_02_check : sumFast (c2TensorGroup167.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian167_02 := by kernel_rfl
private def c2GroupHessian167_03Chunk0 : Poly := [([0,0], -80),([0,1], -20),([0,4], -20),([0,5], -40),([0,6], -80),([0,8], -40),([0,9], -40),([1,4], -8),([1,6], -20),([1,9], -20),([4,5], -20),([4,6], -20),([5,6], -40),([5,9], -40),([6,6], -40),([6,9], -40)]
def c2GroupHessian167_03 : Poly := List.flatten [c2GroupHessian167_03Chunk0]
theorem c2GroupHessian167_03_check : sumFast (c2TensorGroup167.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian167_03 := by kernel_rfl
private def c2GroupHessian167_11Chunk0 : Poly := [([0,0], 160),([0,2], 160),([0,7], 160),([0,8], 160),([2,2], 40),([2,7], 80),([2,8], 80),([7,7], 40),([7,8], 80),([8,8], 40)]
def c2GroupHessian167_11 : Poly := List.flatten [c2GroupHessian167_11Chunk0]
theorem c2GroupHessian167_11_check : sumFast (c2TensorGroup167.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian167_11 := by kernel_rfl
private def c2GroupHessian167_12Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -120),([0,8], -40),([2,7], -40),([7,7], -40),([7,8], -40)]
def c2GroupHessian167_12 : Poly := List.flatten [c2GroupHessian167_12Chunk0]
theorem c2GroupHessian167_12_check : sumFast (c2TensorGroup167.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian167_12 := by kernel_rfl
private def c2GroupHessian167_13Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -40),([0,8], -120),([2,8], -40),([7,8], -40),([8,8], -40)]
def c2GroupHessian167_13 : Poly := List.flatten [c2GroupHessian167_13Chunk0]
theorem c2GroupHessian167_13_check : sumFast (c2TensorGroup167.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian167_13 := by kernel_rfl
private def c2GroupHessian167_22Chunk0 : Poly := [([0,0], 48),([0,3], 16),([0,7], 80),([3,3], 8),([5,5], 40),([5,9], -80),([7,7], 40),([9,9], 40)]
def c2GroupHessian167_22 : Poly := List.flatten [c2GroupHessian167_22Chunk0]
theorem c2GroupHessian167_22_check : sumFast (c2TensorGroup167.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian167_22 := by kernel_rfl
private def c2GroupHessian167_23Chunk0 : Poly := [([0,0], 40),([0,4], 4),([0,5], 40),([0,7], 40),([0,8], 40),([0,9], -40),([3,4], 4),([4,5], 20),([4,9], -20),([5,6], 40),([5,9], 40),([6,9], -40),([7,8], 40),([9,9], -40)]
def c2GroupHessian167_23 : Poly := List.flatten [c2GroupHessian167_23Chunk0]
theorem c2GroupHessian167_23_check : sumFast (c2TensorGroup167.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian167_23 := by kernel_rfl
private def c2GroupHessian167_33Chunk0 : Poly := [([0,0], 80),([0,4], 40),([0,6], 80),([0,8], 80),([0,9], 80),([4,4], 16),([4,6], 40),([4,9], 40),([6,6], 40),([6,9], 80),([8,8], 40),([9,9], 40)]
def c2GroupHessian167_33 : Poly := List.flatten [c2GroupHessian167_33Chunk0]
theorem c2GroupHessian167_33_check : sumFast (c2TensorGroup167.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian167_33 := by kernel_rfl
end D4.Secondary
