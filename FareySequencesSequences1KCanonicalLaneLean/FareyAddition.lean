import canonicalLaneMathlib.AdmissibleClass
import HautevilleHouse.FareySequencesSequences1KCanonicalLaneLean.FareyPair

namespace HautevilleHouse
namespace FareySequencesSequences1KCanonicalLaneLean

def fareyAdd (p q : FareyPair) : FareyPair :=
  { a := p.a * q.a + p.b * q.c
    b := p.a * q.b + p.b * q.d
    c := p.c * q.a + p.d * q.c
    d := p.c * q.b + p.d * q.d
    reduced := by
      calc
        (p.a * q.a + p.b * q.c) * (p.c * q.b + p.d * q.d) - (p.a * q.b + p.b * q.d) * (p.c * q.a + p.d * q.c) = (p.a * p.d - p.b * p.c) * (q.a * q.d - q.b * q.c) := by ring
        _ = 1 * 1 := by simp [p.reduced, q.reduced]
        _ = 1 := by norm_num
    nonnegative := by
      constructor
      · positivity
      · positivity
  }

end FareySequencesSequences1KCanonicalLaneLean
end HautevilleHouse