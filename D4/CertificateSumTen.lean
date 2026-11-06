import D4.CertificateFast

namespace D4.Certificate

theorem sumFast_ten (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : Poly) :
    sumFast [p0,p1,p2,p3,p4,p5,p6,p7,p8,p9] =
      mergeAdd
        (mergeAdd (mergeAdd (mergeAdd p0 p1) (mergeAdd p2 p3))
          (mergeAdd (mergeAdd p4 p5) (mergeAdd p6 p7)))
        (mergeAdd p8 p9) := by rfl

end D4.Certificate
