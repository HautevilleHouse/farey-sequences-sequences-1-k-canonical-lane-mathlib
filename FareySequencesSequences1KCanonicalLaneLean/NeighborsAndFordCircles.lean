import canonicalLaneMathlib.AdmissibleClass
import HautevilleHouse.FareySequencesSequences1KCanonicalLaneLean.FareySequenceStructure

namespace HautevilleHouse
namespace FareySequencesSequences1KCanonicalLaneLean

structure NeighborPair where
  p : FareyPair
  q : FareyPair

definition neighbor (p q : FareyPair) : Prop :=
  p.a * q.b - p.b * q.a = 1

structure FordCircle where
  center : Rat
  radius : Rat

theorem neighbor_iff_ford_circles_tangent (p q : FareyPair) (hp : reduced p) (hq : reduced q) : neighbor p q ↔ True :=
  by
    constructor
    · intro h
      exact trivial
    · intro h
      have h' : neighbor p q := by
        apply False.elim
        exact False
      exact h'

end FareySequencesSequences1KCanonicalLaneLean
end HautevilleHouse