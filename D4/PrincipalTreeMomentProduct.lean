import D4.PrincipalTreeProductMerge4_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Principal
open Certificate
def treeMomentProduct : Poly := treeProductMerge4_0
theorem treeProductDet_chunks : List.flatten [treeProductDet0,treeProductDet1,treeProductDet2,treeProductDet3,treeProductDet4,treeProductDet5,treeProductDet6,treeProductDet7,treeProductDet8,treeProductDet9,treeProductDet10,treeProductDet11,treeProductDet12,treeProductDet13,treeProductDet14,treeProductDet15,treeProductDet16,treeProductDet17,treeProductDet18,treeProductDet19,treeProductDet20,treeProductDet21,treeProductDet22,treeProductDet23,treeProductDet24] = CertificateMoments.determinantC1 := by kernel_rfl
theorem treeMomentProduct_eval (x : Nat → ℝ) : eval x treeMomentProduct = eval x CertificateMoments.determinantC1 * eval x CertificateMoments.momentC1 := by
  rw [treeMomentProduct, treeProductMerge4_0_eval, treeProductDet_chunks]
end D4.Principal
