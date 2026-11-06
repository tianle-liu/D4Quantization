import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup215_det_check : c2TensorGroup215.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 275)) = true := by kernel_rfl
private def c2GroupHessian215_00Chunk0 : Poly := [([0,0], 56),([0,1], 32),([0,5], 40),([0,6], 80),([1,1], 16),([1,5], 40),([5,5], 40),([6,6], 40)]
def c2GroupHessian215_00 : Poly := List.flatten [c2GroupHessian215_00Chunk0]
theorem c2GroupHessian215_00_check : sumFast (c2TensorGroup215.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian215_00 := by kernel_rfl
private def c2GroupHessian215_01Chunk0 : Poly := [([0,0], 32),([0,1], -8),([0,2], -8),([0,5], -20),([0,6], 40),([0,7], -8),([0,8], 40),([1,2], -8),([1,7], -8),([2,5], -20),([5,7], -20),([6,8], 40)]
def c2GroupHessian215_01 : Poly := List.flatten [c2GroupHessian215_01Chunk0]
theorem c2GroupHessian215_01_check : sumFast (c2TensorGroup215.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian215_01 := by kernel_rfl
private def c2GroupHessian215_02Chunk0 : Poly := [([0,3], 4),([0,5], -20),([0,7], 8),([0,9], 40),([1,3], 4),([1,5], -20),([1,7], 8),([5,5], -40),([5,7], 20),([6,9], 40)]
def c2GroupHessian215_02 : Poly := List.flatten [c2GroupHessian215_02Chunk0]
theorem c2GroupHessian215_02_check : sumFast (c2TensorGroup215.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian215_02 := by kernel_rfl
private def c2GroupHessian215_03Chunk0 : Poly := [([0,0], -80),([0,4], -40),([0,6], -120),([0,8], -40),([0,9], -40),([4,6], -40),([6,6], -40),([6,8], -40),([6,9], -40)]
def c2GroupHessian215_03 : Poly := List.flatten [c2GroupHessian215_03Chunk0]
theorem c2GroupHessian215_03_check : sumFast (c2TensorGroup215.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian215_03 := by kernel_rfl
private def c2GroupHessian215_11Chunk0 : Poly := [([0,0], 56),([0,2], 32),([0,7], 32),([0,8], 80),([2,2], 16),([2,7], 32),([7,7], 16),([8,8], 40)]
def c2GroupHessian215_11 : Poly := List.flatten [c2GroupHessian215_11Chunk0]
theorem c2GroupHessian215_11_check : sumFast (c2TensorGroup215.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian215_11 := by kernel_rfl
private def c2GroupHessian215_12Chunk0 : Poly := [([0,3], 4),([0,5], 20),([0,7], -16),([0,9], 40),([2,3], 4),([2,5], 20),([2,7], -16),([3,7], 4),([5,7], 20),([7,7], -16),([8,9], 40)]
def c2GroupHessian215_12 : Poly := List.flatten [c2GroupHessian215_12Chunk0]
theorem c2GroupHessian215_12_check : sumFast (c2TensorGroup215.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian215_12 := by kernel_rfl
private def c2GroupHessian215_13Chunk0 : Poly := [([0,0], -80),([0,4], -40),([0,6], -40),([0,8], -120),([0,9], -40),([4,8], -40),([6,8], -40),([8,8], -40),([8,9], -40)]
def c2GroupHessian215_13 : Poly := List.flatten [c2GroupHessian215_13Chunk0]
theorem c2GroupHessian215_13_check : sumFast (c2TensorGroup215.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian215_13 := by kernel_rfl
private def c2GroupHessian215_22Chunk0 : Poly := [([3,3], 8),([3,7], -8),([5,5], 40),([5,7], -40),([7,7], 16),([9,9], 40)]
def c2GroupHessian215_22 : Poly := List.flatten [c2GroupHessian215_22Chunk0]
theorem c2GroupHessian215_22_check : sumFast (c2TensorGroup215.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian215_22 := by kernel_rfl
private def c2GroupHessian215_23Chunk0 : Poly := [([0,9], -80),([4,9], -40),([6,9], -40),([8,9], -40),([9,9], -40)]
def c2GroupHessian215_23 : Poly := List.flatten [c2GroupHessian215_23Chunk0]
theorem c2GroupHessian215_23_check : sumFast (c2TensorGroup215.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian215_23 := by kernel_rfl
private def c2GroupHessian215_33Chunk0 : Poly := [([0,0], 160),([0,4], 160),([0,6], 160),([0,8], 160),([0,9], 160),([4,4], 40),([4,6], 80),([4,8], 80),([4,9], 80),([6,6], 40),([6,8], 80),([6,9], 80),([8,8], 40),([8,9], 80),([9,9], 40)]
def c2GroupHessian215_33 : Poly := List.flatten [c2GroupHessian215_33Chunk0]
theorem c2GroupHessian215_33_check : sumFast (c2TensorGroup215.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian215_33 := by kernel_rfl
end D4.Secondary
