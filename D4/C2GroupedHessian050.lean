import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup50_det_check : c2TensorGroup50.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 69)) = true := by kernel_rfl
private def c2GroupHessian50_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 16),([0,6], 80),([1,1], 40),([1,6], 80),([5,5], 8),([6,6], 40)]
def c2GroupHessian50_00 : Poly := List.flatten [c2GroupHessian50_00Chunk0]
theorem c2GroupHessian50_00_check : sumFast (c2TensorGroup50.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian50_00 := by kernel_rfl
private def c2GroupHessian50_01Chunk0 : Poly := [([0,0], 8),([0,2], 4),([0,5], 8),([0,7], -40),([1,7], -40),([2,5], 4),([6,7], -40)]
def c2GroupHessian50_01 : Poly := List.flatten [c2GroupHessian50_01Chunk0]
theorem c2GroupHessian50_01_check : sumFast (c2TensorGroup50.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian50_01 := by kernel_rfl
private def c2GroupHessian50_02Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,3], 40),([0,5], -16),([0,6], 40),([0,7], 40),([0,9], 40),([1,3], 40),([1,7], 40),([1,9], 40),([3,6], 40),([5,5], -8),([6,7], 40),([6,9], 40)]
def c2GroupHessian50_02 : Poly := List.flatten [c2GroupHessian50_02Chunk0]
theorem c2GroupHessian50_02_check : sumFast (c2TensorGroup50.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian50_02 := by kernel_rfl
private def c2GroupHessian50_03Chunk0 : Poly := [([0,0], -40),([0,1], -40),([0,4], 4),([0,6], -80),([0,9], -40),([1,6], -40),([1,9], -40),([4,5], 4),([6,6], -40),([6,9], -40)]
def c2GroupHessian50_03 : Poly := List.flatten [c2GroupHessian50_03Chunk0]
theorem c2GroupHessian50_03_check : sumFast (c2TensorGroup50.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian50_03 := by kernel_rfl
private def c2GroupHessian50_11Chunk0 : Poly := [([0,0], 48),([0,2], 48),([0,8], 80),([2,2], 16),([2,8], 40),([7,7], 40),([8,8], 40)]
def c2GroupHessian50_11 : Poly := List.flatten [c2GroupHessian50_11Chunk0]
theorem c2GroupHessian50_11_check : sumFast (c2TensorGroup50.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian50_11 := by kernel_rfl
private def c2GroupHessian50_12Chunk0 : Poly := [([0,0], -8),([0,2], -4),([0,5], -8),([0,7], -40),([2,5], -4),([3,7], -40),([7,7], -40),([7,9], -40)]
def c2GroupHessian50_12 : Poly := List.flatten [c2GroupHessian50_12Chunk0]
theorem c2GroupHessian50_12_check : sumFast (c2TensorGroup50.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian50_12 := by kernel_rfl
private def c2GroupHessian50_13Chunk0 : Poly := [([0,0], -40),([0,2], -20),([0,4], -16),([0,7], 40),([0,8], -80),([2,4], -8),([2,8], -20),([4,8], -20),([6,7], 40),([7,9], 40),([8,8], -40)]
def c2GroupHessian50_13 : Poly := List.flatten [c2GroupHessian50_13Chunk0]
theorem c2GroupHessian50_13_check : sumFast (c2TensorGroup50.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian50_13 := by kernel_rfl
private def c2GroupHessian50_22Chunk0 : Poly := [([0,0], 48),([0,3], 80),([0,5], 16),([0,7], 80),([0,9], 80),([3,3], 40),([3,7], 80),([3,9], 80),([5,5], 8),([7,7], 40),([7,9], 80),([9,9], 40)]
def c2GroupHessian50_22 : Poly := List.flatten [c2GroupHessian50_22Chunk0]
theorem c2GroupHessian50_22_check : sumFast (c2TensorGroup50.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian50_22 := by kernel_rfl
private def c2GroupHessian50_23Chunk0 : Poly := [([0,0], -40),([0,3], -40),([0,4], -4),([0,6], -40),([0,7], -40),([0,9], -80),([3,6], -40),([3,9], -40),([4,5], -4),([6,7], -40),([6,9], -40),([7,9], -40),([9,9], -40)]
def c2GroupHessian50_23 : Poly := List.flatten [c2GroupHessian50_23Chunk0]
theorem c2GroupHessian50_23_check : sumFast (c2TensorGroup50.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian50_23 := by kernel_rfl
private def c2GroupHessian50_33Chunk0 : Poly := [([0,0], 80),([0,4], 40),([0,6], 80),([0,8], 80),([0,9], 80),([4,4], 16),([4,8], 40),([6,6], 40),([6,9], 80),([8,8], 40),([9,9], 40)]
def c2GroupHessian50_33 : Poly := List.flatten [c2GroupHessian50_33Chunk0]
theorem c2GroupHessian50_33_check : sumFast (c2TensorGroup50.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian50_33 := by kernel_rfl
end D4.Secondary
