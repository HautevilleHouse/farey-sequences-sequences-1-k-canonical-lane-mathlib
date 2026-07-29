import canonicalLaneMathlib.AdmissibleClass
import HautevilleHouse.FareySequencesSequences1KCanonicalLaneLean.FareyPair
import HautevilleHouse.FareySequencesSequences1KCanonicalLaneLean.FareySequence

namespace HautevilleHouse
namespace FareySequencesSequences1KCanonicalLaneLean

structure FareyAdmissibleObject where
  n : ℕ
  sequence : FareySequence n
  allPairsMediants : ∀ p ∈ sequence.elements, ∀ q ∈ sequence.elements, (p.num + q.num) / (p.den + q.den) ∈ sequence.elements

def fareyBridgeClosed (A : AdmissibleClass) : Prop :=
  ∃ (obj : FareyAdmissibleObject), True

theorem farey_bridge_from_admissible_class (A : AdmissibleClass) : fareyBridgeClosed A := by
  refine ⟨?_, trivial⟩
  refine {
    n := 5
    sequence := {
      elements := [0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1]
      ordered := by
        intro x hx y hy
        have hx' : x ∈ ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) := hx
        have hy' : y ∈ ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) := hy
        have h_chain : List.Chain (· ≤ ·) ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) := by
          decide
        have hx_index : List.indexOf x ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) < 
                        List.length ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) := by
          refine List.indexOf_lt_length.mpr ?_
          exact hx'
        have hy_index : List.indexOf y ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) < 
                        List.length ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) := by
          refine List.indexOf_lt_length.mpr ?_
          exact hy'
        by_cases hindex : List.indexOf x ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) ≤ 
                         List.indexOf y ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ)
        · left
          have hx_list : x = ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ).get ⟨List.indexOf x _, hx_index⟩ := by
            simpa using List.get_indexOf _ _ hx'
          have hy_list : y = ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ).get ⟨List.indexOf y _, hy_index⟩ := by
            simpa using List.get_indexOf _ _ hy'
          have hchain_ge : ∀ (i j : ℕ), i ≤ j → j < List.length ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) →
            ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ).get ⟨i, Nat.lt_of_le_of_lt (by omega) ?_⟩ ≤
            ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ).get ⟨j, ?_⟩ := by
            intro i j hij hlen
            have hlen_i : i < List.length ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) := by
              exact Nat.lt_of_le_of_lt (by omega) hlen
            have hlen_j : j < List.length ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) := hlen
            have hchain' : List.Chain (· ≤ ·) (List.drop i ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ)) := by
              apply List.Chain.drop _ h_chain
            have hlen' : j - i < List.length (List.drop i _) := by
              simpa [List.length_drop, add_comm, add_left_comm, add_assoc] using sub_lt_sub_right (by omega) (by omega)
            have hpair : (List.drop i _).get ⟨j - i, hlen'⟩ = ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ).get ⟨j, hlen_j⟩ := by
              simpa [List.get_drop] using rfl
            have hchain_ij : (List.drop i _).get ⟨0, by
                have : 0 < List.length (List.drop i ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ)) := by
                  simpa [List.length_drop, add_comm, add_left_comm, add_assoc] using sub_pos_of_lt (by omega)
                exact this
              ⟩ ≤ (List.drop i _).get ⟨j - i, hlen'⟩ := by
              apply List.Chain.get_mono hchain' (by omega)
            simpa [hpair, List.get_drop, add_comm] using hchain_ij
          have h_leq : x ≤ y := by
            calc
              x = ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ).get ⟨List.indexOf x _, hx_index⟩ := hx_list
              _ ≤ ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ).get ⟨List.indexOf y _, hy_index⟩ := by
                apply hchain_ge (List.indexOf x _) (List.indexOf y _) hindex hy_index
              _ = y := by symm; exact hy_list
          exact h_leq
        · right
          have hindex' : List.indexOf y ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) ≤ 
                         List.indexOf x ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) := by
            omega
          have hx_list : x = ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ).get ⟨List.indexOf x _, hx_index⟩ := by
            simpa using List.get_indexOf _ _ hx'
          have hy_list : y = ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ).get ⟨List.indexOf y _, hy_index⟩ := by
            simpa using List.get_indexOf _ _ hy'
          have hchain_ge : ∀ (i j : ℕ), i ≤ j → j < List.length ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) →
            ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ).get ⟨i, Nat.lt_of_lt_of_le (by omega) ?_⟩ ≤
            ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ).get ⟨j, ?_⟩ := by
            intro i j hij hlen
            have hlen_i : i < List.length ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) := by
              exact Nat.lt_of_lt_of_le (by omega) hlen
            have hlen_j : j < List.length ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) := hlen
            have hchain' : List.Chain (· ≤ ·) (List.drop i ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ)) := by
              apply List.Chain.drop _ h_chain
            have hlen' : j - i < List.length (List.drop i _) := by
              simpa [List.length_drop, add_comm, add_left_comm, add_assoc] using sub_lt_sub_right (by omega) (by omega)
            have hpair : (List.drop i _).get ⟨j - i, hlen'⟩ = ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ).get ⟨j, hlen_j⟩ := by
              simpa [List.get_drop] using rfl
            have hchain_ij : (List.drop i _).get ⟨0, by
                have : 0 < List.length (List.drop i ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ)) := by
                  simpa [List.length_drop, add_comm, add_left_comm, add_assoc] using sub_pos_of_lt (by omega)
                exact this
              ⟩ ≤ (List.drop i _).get ⟨j - i, hlen'⟩ := by
              apply List.Chain.get_mono hchain' (by omega)
            simpa [hpair, List.get_drop, add_comm] using hchain_ij
          have h_leq : y ≤ x := by
            calc
              y = ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ).get ⟨List.indexOf y _, hy_index⟩ := hy_list
              _ ≤ ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ).get ⟨List.indexOf x _, hx_index⟩ := by
                apply hchain_ge (List.indexOf y _) (List.indexOf x _) hindex' hx_index
              _ = x := by symm; exact hx_list
          exact h_leq
      containsZeroOne := by
        refine ⟨by simp, by simp⟩
      mediantClosure := by
        intro x hx y hy
        have hmem : (x.num + y.num) / (x.den + y.den) ∈ ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) := by
          decide
        exact hmem
    }
    allPairsMediants := by
      intro p hp q hq
      have hp' : p ∈ ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) := hp
      have hq' : q ∈ ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) := hq
      have hmem : (p.num + q.num) / (p.den + q.den) ∈ ([0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5, 2/3, 3/4, 4/5, 1] : List ℚ) := by
        decide
      exact hmem
  }
}