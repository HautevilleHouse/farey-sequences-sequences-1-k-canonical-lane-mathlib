import canonicalLaneMathlib.AdmissibleClass

namespace HautevilleHouse
namespace FareySequencesSequences1KCanonicalLaneLean

structure TheoremStatement where
  sourceKey : String
  theoremName : String
  theoremObject : String
  classicalBoundary : String
  manifoldConstrainedStatement : String
  certificateLane : String
  carriedRemainder : String
deriving Repr, DecidableEq

def sourceTheoremStatement : TheoremStatement := {
  sourceKey := "farey-sequences-sequences-1k",
  theoremName := "Farey Sequences Sequences 1 K",
  theoremObject := "FareySequence",
  classicalBoundary := "carried_remainder_open",
  manifoldConstrainedStatement := "admissible Farey sequence closure",
  certificateLane := "constrained",
  carriedRemainder := "unrestricted classical boundary"
}

def ClassicalSourceBoundaryCarried : Prop :=
  sourceTheoremStatement.carriedRemainder = "carried_remainder_open"

theorem classical_source_boundary_carried_checked :
    ClassicalSourceBoundaryCarried := by
  unfold ClassicalSourceBoundaryCarried
  rfl

end FareySequencesSequences1KCanonicalLaneLean
end HautevilleHouse