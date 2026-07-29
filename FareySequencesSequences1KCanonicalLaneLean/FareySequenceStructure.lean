import canonicalLaneMathlib.AdmissibleClass
import HautevilleHouse.FareySequencesSequences1KCanonicalLaneLean.FareyPairOperations

namespace HautevilleHouse
namespace FareySequencesSequences1KCanonicalLaneLean

structure FareySequence where
  n : Nat
  pairs : List FareyPair
  increasing : Prop
  endpoints : Prop

structure FareySequenceEvidence (fs : FareySequence) where
  increasingClosed : fs.increasing
  endpointsClosed : fs.endpoints

def FareySequenceClosed (fs : FareySequence) : Prop :=
  fs.increasing ∧ fs.endpoints

theorem farey_sequence_closed_from_evidence (fs : FareySequence) (e : FareySequenceEvidence fs) : FareySequenceClosed fs :=
  And.intro e.increasingClosed e.endpointsClosed

end FareySequencesSequences1KCanonicalLaneLean
end HautevilleHouse