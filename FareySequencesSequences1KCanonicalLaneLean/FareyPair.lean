import canonicalLaneMathlib.AdmissibleClass

namespace HautevilleHouse
namespace FareySequencesSequences1KCanonicalLaneLean

structure FareyPair where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  reduced : a * d - b * c = 1
  nonnegative : a ≤ b ∧ c ≤ d

def FareyPair.key (p : FareyPair) : ℚ × ℚ := (p.a / p.b, p.c / p.d)

end FareySequencesSequences1KCanonicalLaneLean
end HautevilleHouse