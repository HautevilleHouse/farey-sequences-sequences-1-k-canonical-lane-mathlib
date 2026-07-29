import canonicalLaneMathlib.AdmissibleClass

namespace HautevilleHouse
namespace FareySequencesSequences1KCanonicalLaneLean

def FareyWitnessClosed (O : FareyAdmittedObject) : Prop :=
  O.property

def bridgeClosed (A : AdmissibleClass) : Prop :=
  FareyWitnessClosed A.object

theorem bridge_from_admissible_class (A : AdmissibleClass) :
    bridgeClosed A := by
  exact A.object.property

end FareySequencesSequences1KCanonicalLaneLean
end HautevilleHouse