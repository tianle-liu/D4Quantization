import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup21_det_check : c2TensorGroup21.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 26)) = true := by kernel_rfl
private def c2GroupHessian21_00Chunk0 : Poly := [([0,0], 960),([0,1], 960),([0,6], 960),([1,1], 240),([1,6], 480),([5,5], 80),([6,6], 240)]
def c2GroupHessian21_00 : Poly := List.flatten [c2GroupHessian21_00Chunk0]
theorem c2GroupHessian21_00_check : sumFast (c2TensorGroup21.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian21_00 := by kernel_rfl
private def c2GroupHessian21_01Chunk0 : Poly := [([0,0], 960),([0,1], 480),([0,2], 480),([0,6], 480),([0,8], 480),([1,2], 240),([1,8], 240),([2,6], 240),([6,8], 240)]
def c2GroupHessian21_01 : Poly := List.flatten [c2GroupHessian21_01Chunk0]
theorem c2GroupHessian21_01_check : sumFast (c2TensorGroup21.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian21_01 := by kernel_rfl
private def c2GroupHessian21_02Chunk0 : Poly := [([0,3], 480),([0,9], 480),([1,3], 240),([1,9], 240),([3,6], 240),([5,5], -80),([6,9], 240)]
def c2GroupHessian21_02 : Poly := List.flatten [c2GroupHessian21_02Chunk0]
theorem c2GroupHessian21_02_check : sumFast (c2TensorGroup21.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian21_02 := by kernel_rfl
private def c2GroupHessian21_03Chunk0 : Poly := [([0,0], -960),([0,1], -480),([0,6], -960),([0,8], -480),([0,9], -480),([1,6], -240),([1,8], -240),([1,9], -240),([6,6], -240),([6,8], -240),([6,9], -240)]
def c2GroupHessian21_03 : Poly := List.flatten [c2GroupHessian21_03Chunk0]
theorem c2GroupHessian21_03_check : sumFast (c2TensorGroup21.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian21_03 := by kernel_rfl
private def c2GroupHessian21_11Chunk0 : Poly := [([0,0], 960),([0,2], 960),([0,8], 960),([2,2], 240),([2,8], 480),([7,7], 80),([8,8], 240)]
def c2GroupHessian21_11 : Poly := List.flatten [c2GroupHessian21_11Chunk0]
theorem c2GroupHessian21_11_check : sumFast (c2TensorGroup21.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian21_11 := by kernel_rfl
private def c2GroupHessian21_12Chunk0 : Poly := [([0,3], 480),([0,9], 480),([2,3], 240),([2,9], 240),([3,8], 240),([7,7], -80),([8,9], 240)]
def c2GroupHessian21_12 : Poly := List.flatten [c2GroupHessian21_12Chunk0]
theorem c2GroupHessian21_12_check : sumFast (c2TensorGroup21.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian21_12 := by kernel_rfl
private def c2GroupHessian21_13Chunk0 : Poly := [([0,0], -960),([0,2], -480),([0,6], -480),([0,8], -960),([0,9], -480),([2,6], -240),([2,8], -240),([2,9], -240),([6,8], -240),([8,8], -240),([8,9], -240)]
def c2GroupHessian21_13 : Poly := List.flatten [c2GroupHessian21_13Chunk0]
theorem c2GroupHessian21_13_check : sumFast (c2TensorGroup21.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian21_13 := by kernel_rfl
private def c2GroupHessian21_22Chunk0 : Poly := [([3,3], 240),([3,9], 480),([5,5], 80),([7,7], 80),([9,9], 240)]
def c2GroupHessian21_22 : Poly := List.flatten [c2GroupHessian21_22Chunk0]
theorem c2GroupHessian21_22_check : sumFast (c2TensorGroup21.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian21_22 := by kernel_rfl
private def c2GroupHessian21_23Chunk0 : Poly := [([0,3], -480),([0,9], -480),([3,6], -240),([3,8], -240),([3,9], -240),([6,9], -240),([8,9], -240),([9,9], -240)]
def c2GroupHessian21_23 : Poly := List.flatten [c2GroupHessian21_23Chunk0]
theorem c2GroupHessian21_23_check : sumFast (c2TensorGroup21.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian21_23 := by kernel_rfl
private def c2GroupHessian21_33Chunk0 : Poly := [([0,0], 960),([0,6], 960),([0,8], 960),([0,9], 960),([4,4], 80),([6,6], 240),([6,8], 480),([6,9], 480),([8,8], 240),([8,9], 480),([9,9], 240)]
def c2GroupHessian21_33 : Poly := List.flatten [c2GroupHessian21_33Chunk0]
theorem c2GroupHessian21_33_check : sumFast (c2TensorGroup21.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian21_33 := by kernel_rfl
end D4.Secondary
