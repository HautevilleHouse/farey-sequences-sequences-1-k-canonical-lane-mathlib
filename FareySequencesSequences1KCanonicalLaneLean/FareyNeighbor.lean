import canonicalLaneMathlib.AdmissibleClass
import HautevilleHouse.FareySequencesSequences1KCanonicalLaneLean.FareyPair

namespace HautevilleHouse
namespace FareySequencesSequences1KCanonicalLaneLean

structure FareyNeighbor where
  left : FareyPair
  right : FareyPair
  determinantOne : left.a * right.d - left.b * right.c = 1
  adjacency : left.b + right.b ≤ 1 -- placeholder condition

def FareyNeighbor.mediant (fn : FareyNeighbor) : FareyPair :=
  { a := fn.left.a + fn.right.a
    b := fn.left.b + fn.right.b
    c := fn.left.c + fn.right.c
    d := fn.left.d + fn.right.d
    reduced := by
      calc
        (fn.left.a + fn.right.a) * (fn.left.d + fn.right.d) - (fn.left.b + fn.right.b) * (fn.left.c + fn.right.c) = 1 := by
          nlinarith [fn.determinantOne]
      _ = 1 := rfl
    nonnegative := by
      constructor
      · exact add_nonneg (fn.left.nonnegative.1) (fn.right.nonnegative.1)
      · exact add_nonneg (fn.left.nonnegative.2) (fn.right.nonnegative.2)
  }

end FareySequencesSequences1KCanonicalLaneLean
end HautevilleHouse