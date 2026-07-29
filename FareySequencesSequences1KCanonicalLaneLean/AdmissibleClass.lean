import canonicalLaneMathlib.AdmissibleClass

namespace HautevilleHouse
namespace FareySequencesSequences1KCanonicalLaneLean

structure FareyAdmittedObject where
  modulus : Nat
  sequence : List ℚ
  property : Prop

structure AdmissibleClass where
  object : FareyAdmittedObject
  endpointSatisfied : Prop
  remainderRecorded : Prop
  gateWitness : endpointSatisfied ∨ remainderRecorded

def admittedClosure (A : AdmissibleClass) : Prop :=
  FareyWitnessClosed A.object ∧ (A.endpointSatisfied ∨ A.remainderRecorded)

end FareySequencesSequences1KCanonicalLaneLean
end HautevilleHouse