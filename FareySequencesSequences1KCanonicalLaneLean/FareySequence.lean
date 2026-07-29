import canonicalLaneMathlib.AdmissibleClass
import HautevilleHouse.FareySequencesSequences1KCanonicalLaneLean.FareyPair

namespace HautevilleHouse
namespace FareySequencesSequences1KCanonicalLaneLean

structure FareySequence (n : ℕ) where
  elements : List ℚ
  ordered : ∀ x ∈ elements, ∀ y ∈ elements, x < y ↔ elements.indexOf x < elements.indexOf y
  containsZeroOne : 0 ∈ elements ∧ 1 ∈ elements
  mediantClosure : ∀ x ∈ elements, ∀ y ∈ elements, (x.num + y.num) / (x.den + y.den) ∈ elements

def FareySequence.length (n : ℕ) (fs : FareySequence n) : ℕ := fs.elements.length

end FareySequencesSequences1KCanonicalLaneLean
end HautevilleHouse