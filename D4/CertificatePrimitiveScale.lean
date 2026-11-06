import D4.CertificatePrimitiveProduct

namespace D4.Certificate

def scalePrim (c : Int) (p : Poly) : Poly := mapRec (fun t => (t.1,c*t.2)) p

theorem scalePrim_eq_scale (c : Int) (p : Poly) : scalePrim c p = scale c p := by
  exact mapRec_eq_map _ _

end D4.Certificate
