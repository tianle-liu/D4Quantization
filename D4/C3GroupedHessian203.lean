import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup203_det_check : c3TensorGroup203.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 259)) = true := by kernel_rfl
private def c3GroupHessian203_00Chunk0 : Poly := [([1,1], 80),([5,5], 240),([5,6], -480),([6,6], 240),([9,9], 80)]
def c3GroupHessian203_00 : Poly := List.flatten [c3GroupHessian203_00Chunk0]
theorem c3GroupHessian203_00_check : sumFast (c3TensorGroup203.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian203_00 := by kernel_rfl
private def c3GroupHessian203_01Chunk0 : Poly := [([5,7], 240),([5,8], -240),([6,7], -240),([6,8], 240),([9,9], 80)]
def c3GroupHessian203_01 : Poly := List.flatten [c3GroupHessian203_01Chunk0]
theorem c3GroupHessian203_01_check : sumFast (c3TensorGroup203.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian203_01 := by kernel_rfl
private def c3GroupHessian203_02Chunk0 : Poly := [([0,5], -480),([0,6], 480),([3,5], -240),([3,6], 240),([5,5], -240),([5,6], 240),([5,7], -240),([6,7], 240),([9,9], -80)]
def c3GroupHessian203_02 : Poly := List.flatten [c3GroupHessian203_02Chunk0]
theorem c3GroupHessian203_02_check : sumFast (c3TensorGroup203.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian203_02 := by kernel_rfl
private def c3GroupHessian203_03Chunk0 : Poly := [([0,5], 480),([0,6], -480),([4,5], 240),([4,6], -240),([5,6], 240),([5,8], 240),([6,6], -240),([6,8], -240),([9,9], -80)]
def c3GroupHessian203_03 : Poly := List.flatten [c3GroupHessian203_03Chunk0]
theorem c3GroupHessian203_03_check : sumFast (c3TensorGroup203.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian203_03 := by kernel_rfl
private def c3GroupHessian203_11Chunk0 : Poly := [([2,2], 80),([7,7], 240),([7,8], -480),([8,8], 240),([9,9], 80)]
def c3GroupHessian203_11 : Poly := List.flatten [c3GroupHessian203_11Chunk0]
theorem c3GroupHessian203_11_check : sumFast (c3TensorGroup203.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian203_11 := by kernel_rfl
private def c3GroupHessian203_12Chunk0 : Poly := [([0,7], -480),([0,8], 480),([3,7], -240),([3,8], 240),([5,7], -240),([5,8], 240),([7,7], -240),([7,8], 240),([9,9], -80)]
def c3GroupHessian203_12 : Poly := List.flatten [c3GroupHessian203_12Chunk0]
theorem c3GroupHessian203_12_check : sumFast (c3TensorGroup203.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian203_12 := by kernel_rfl
private def c3GroupHessian203_13Chunk0 : Poly := [([0,7], 480),([0,8], -480),([4,7], 240),([4,8], -240),([6,7], 240),([6,8], -240),([7,8], 240),([8,8], -240),([9,9], -80)]
def c3GroupHessian203_13 : Poly := List.flatten [c3GroupHessian203_13Chunk0]
theorem c3GroupHessian203_13_check : sumFast (c3TensorGroup203.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian203_13 := by kernel_rfl
private def c3GroupHessian203_22Chunk0 : Poly := [([0,0], 960),([0,3], 960),([0,5], 960),([0,7], 960),([3,3], 240),([3,5], 480),([3,7], 480),([5,5], 240),([5,7], 480),([7,7], 240),([9,9], 80)]
def c3GroupHessian203_22 : Poly := List.flatten [c3GroupHessian203_22Chunk0]
theorem c3GroupHessian203_22_check : sumFast (c3TensorGroup203.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian203_22 := by kernel_rfl
private def c3GroupHessian203_23Chunk0 : Poly := [([0,0], -960),([0,3], -480),([0,4], -480),([0,5], -480),([0,6], -480),([0,7], -480),([0,8], -480),([3,4], -240),([3,6], -240),([3,8], -240),([4,5], -240),([4,7], -240),([5,6], -240),([5,8], -240),([6,7], -240),([7,8], -240),([9,9], 80)]
def c3GroupHessian203_23 : Poly := List.flatten [c3GroupHessian203_23Chunk0]
theorem c3GroupHessian203_23_check : sumFast (c3TensorGroup203.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian203_23 := by kernel_rfl
private def c3GroupHessian203_33Chunk0 : Poly := [([0,0], 960),([0,4], 960),([0,6], 960),([0,8], 960),([4,4], 240),([4,6], 480),([4,8], 480),([6,6], 240),([6,8], 480),([8,8], 240),([9,9], 80)]
def c3GroupHessian203_33 : Poly := List.flatten [c3GroupHessian203_33Chunk0]
theorem c3GroupHessian203_33_check : sumFast (c3TensorGroup203.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian203_33 := by kernel_rfl
end D4.Secondary
