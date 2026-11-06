import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup25_det_check : c3TensorGroup25.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 34)) = true := by kernel_rfl
private def c3GroupHessian25_00Chunk0 : Poly := [([0,0], 960),([0,1], 960),([0,5], 960),([0,9], 960),([1,1], 240),([1,5], 480),([1,9], 480),([5,5], 240),([5,9], 480),([6,6], 80),([9,9], 240)]
def c3GroupHessian25_00 : Poly := List.flatten [c3GroupHessian25_00Chunk0]
theorem c3GroupHessian25_00_check : sumFast (c3TensorGroup25.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian25_00 := by kernel_rfl
private def c3GroupHessian25_01Chunk0 : Poly := [([0,0], 960),([0,1], 480),([0,2], 480),([0,5], 480),([0,7], 480),([0,9], 960),([1,2], 240),([1,7], 240),([1,9], 240),([2,5], 240),([2,9], 240),([5,7], 240),([5,9], 240),([7,9], 240),([9,9], 240)]
def c3GroupHessian25_01 : Poly := List.flatten [c3GroupHessian25_01Chunk0]
theorem c3GroupHessian25_01_check : sumFast (c3TensorGroup25.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian25_01 := by kernel_rfl
private def c3GroupHessian25_02Chunk0 : Poly := [([0,0], -960),([0,1], -480),([0,5], -960),([0,7], -480),([0,9], -960),([1,5], -240),([1,7], -240),([1,9], -240),([5,5], -240),([5,7], -240),([5,9], -480),([7,9], -240),([9,9], -240)]
def c3GroupHessian25_02 : Poly := List.flatten [c3GroupHessian25_02Chunk0]
theorem c3GroupHessian25_02_check : sumFast (c3TensorGroup25.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian25_02 := by kernel_rfl
private def c3GroupHessian25_03Chunk0 : Poly := [([0,4], 480),([0,9], -480),([1,4], 240),([1,9], -240),([4,5], 240),([4,9], 240),([5,9], -240),([6,6], -80),([9,9], -240)]
def c3GroupHessian25_03 : Poly := List.flatten [c3GroupHessian25_03Chunk0]
theorem c3GroupHessian25_03_check : sumFast (c3TensorGroup25.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian25_03 := by kernel_rfl
private def c3GroupHessian25_11Chunk0 : Poly := [([0,0], 960),([0,2], 960),([0,7], 960),([0,9], 960),([2,2], 240),([2,7], 480),([2,9], 480),([7,7], 240),([7,9], 480),([8,8], 80),([9,9], 240)]
def c3GroupHessian25_11 : Poly := List.flatten [c3GroupHessian25_11Chunk0]
theorem c3GroupHessian25_11_check : sumFast (c3TensorGroup25.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian25_11 := by kernel_rfl
private def c3GroupHessian25_12Chunk0 : Poly := [([0,0], -960),([0,2], -480),([0,5], -480),([0,7], -960),([0,9], -960),([2,5], -240),([2,7], -240),([2,9], -240),([5,7], -240),([5,9], -240),([7,7], -240),([7,9], -480),([9,9], -240)]
def c3GroupHessian25_12 : Poly := List.flatten [c3GroupHessian25_12Chunk0]
theorem c3GroupHessian25_12_check : sumFast (c3TensorGroup25.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian25_12 := by kernel_rfl
private def c3GroupHessian25_13Chunk0 : Poly := [([0,4], 480),([0,9], -480),([2,4], 240),([2,9], -240),([4,7], 240),([4,9], 240),([7,9], -240),([8,8], -80),([9,9], -240)]
def c3GroupHessian25_13 : Poly := List.flatten [c3GroupHessian25_13Chunk0]
theorem c3GroupHessian25_13_check : sumFast (c3TensorGroup25.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian25_13 := by kernel_rfl
private def c3GroupHessian25_22Chunk0 : Poly := [([0,0], 960),([0,5], 960),([0,7], 960),([0,9], 960),([3,3], 80),([5,5], 240),([5,7], 480),([5,9], 480),([7,7], 240),([7,9], 480),([9,9], 240)]
def c3GroupHessian25_22 : Poly := List.flatten [c3GroupHessian25_22Chunk0]
theorem c3GroupHessian25_22_check : sumFast (c3TensorGroup25.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian25_22 := by kernel_rfl
private def c3GroupHessian25_23Chunk0 : Poly := [([0,4], -480),([0,9], 480),([4,5], -240),([4,7], -240),([4,9], -240),([5,9], 240),([7,9], 240),([9,9], 240)]
def c3GroupHessian25_23 : Poly := List.flatten [c3GroupHessian25_23Chunk0]
theorem c3GroupHessian25_23_check : sumFast (c3TensorGroup25.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian25_23 := by kernel_rfl
private def c3GroupHessian25_33Chunk0 : Poly := [([4,4], 240),([4,9], -480),([6,6], 80),([8,8], 80),([9,9], 240)]
def c3GroupHessian25_33 : Poly := List.flatten [c3GroupHessian25_33Chunk0]
theorem c3GroupHessian25_33_check : sumFast (c3TensorGroup25.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian25_33 := by kernel_rfl
end D4.Secondary
