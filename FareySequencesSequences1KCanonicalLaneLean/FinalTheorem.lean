import canonicalLaneMathlib.AdmissibleClass
import HautevilleHouse.FareySequencesSequences1KCanonicalLaneLean.FareyBridge

namespace HautevilleHouse
namespace FareySequencesSequences1KCanonicalLaneLean

def ConstrainedFareyClosure (A : AdmissibleClass) : Prop :=
  fareyBridgeClosed A ∧ gateClosed A

theorem constrained_farey_endgame (A : AdmissibleClass) : ConstrainedFareyClosure A := by
  exact And.intro (farey_bridge_from_admissible_class A) (gate_from_admissible_class A)

end FareySequencesSequences1KCanonicalLaneLean
end HautevilleHouse