import D4.PrincipalTreeTensor00
import D4.PrincipalTreeTensor01
import D4.PrincipalTreeTensor02
import D4.PrincipalTreeTensor03
import D4.PrincipalTreeTensor11
import D4.PrincipalTreeTensor12
import D4.PrincipalTreeTensor13
import D4.PrincipalTreeTensor22
import D4.PrincipalTreeTensor23
import D4.PrincipalTreeTensor33
namespace D4.Principal
open Certificate
noncomputable section
def tensorPoly : Fin 4 → Fin 4 → Poly := ![![tensor00,tensor01,tensor02,tensor03],![tensor01,tensor11,tensor12,tensor13],![tensor02,tensor12,tensor22,tensor23],![tensor03,tensor13,tensor23,tensor33]]
theorem tensorPoly_eval (w : Fin 10 → ℝ) (i j : Fin 4) :
    eval (extendWeight w) (tensorPoly i j) = treeTensor w i j := by
  fin_cases i <;> fin_cases j
  · exact tensor00_eval w
  · exact tensor01_eval w
  · exact tensor02_eval w
  · exact tensor03_eval w
  · exact (tensor01_eval w).trans (treeTensor_symmetric w 0 1)
  · exact tensor11_eval w
  · exact tensor12_eval w
  · exact tensor13_eval w
  · exact (tensor02_eval w).trans (treeTensor_symmetric w 0 2)
  · exact (tensor12_eval w).trans (treeTensor_symmetric w 1 2)
  · exact tensor22_eval w
  · exact tensor23_eval w
  · exact (tensor03_eval w).trans (treeTensor_symmetric w 0 3)
  · exact (tensor13_eval w).trans (treeTensor_symmetric w 1 3)
  · exact (tensor23_eval w).trans (treeTensor_symmetric w 2 3)
  · exact tensor33_eval w
end
end D4.Principal
