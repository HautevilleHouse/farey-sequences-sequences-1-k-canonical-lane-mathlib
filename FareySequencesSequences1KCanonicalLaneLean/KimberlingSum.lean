import canonicalLaneMathlib.AdmissibleClass
import HautevilleHouse.FareySequencesSequences1KCanonicalLaneLean.FareyPairOperations

namespace HautevilleHouse
namespace FareySequencesSequences1KCanonicalLaneLean

structure KimberlingSum (n : Nat) where
  sum : Rat
  formula : Prop

structure KimberlingSumEvidence (s : KimberlingSum n) where
  formulaClosed : s.formula

def KimberlingSumClosed (s : KimberlingSum n) : Prop :=
  s.formula

theorem kimberling_sum_closed_from_evidence (s : KimberlingSum n) (e : KimberlingSumEvidence s) : KimberlingSumClosed s :=
  e.formulaClosed

end FareySequencesSequences1KCanonicalLaneLean
end HautevilleHouse