import EcoLean.DebreauRepresentation.GapCompatibleDense
import EcoLean.DebreauRepresentation.BoundedAdjustment
import EcoLean.DebreauRepresentation.DenseRestriction

/-!
# Restriction to a countable gap-compatible dense subset

This file packages the restriction step using a countable gap-compatible dense
subset, rather than the earlier no-gap version.

The previously developed machinery for restriction of preferences and bounded
postcomposition is reused here.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

section SecondCountable

variable [TopologicalSpace α] [SecondCountableTopology α]

/--
If `P` is complete, transitive, and continuous on a second-countable space,
then there exists a countable gap-compatible dense subset `D` together with a
utility representation of the restricted preference on `D`.
-/
theorem exists_countable_gapCompatibleDense_restriction_with_utility
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (hCont : ContinuousPref P) :
    ∃ D : Set α,
      D.Countable ∧
      GapCompatibleDense P D ∧
      ∃ u : Utility.UtilityFunction D, Represents u (restrict P D) := by
  rcases exists_countable_gapCompatibleDense P hC hCont with
    ⟨D, hDcount, hDgap⟩
  letI : Countable D := by
    simpa using hDcount
  letI : Encodable D := Encodable.ofCountable D
  have hC' : (restrict P D).Complete :=
    complete_restrict P hC D
  have hT' : (restrict P D).Transitive :=
    transitive_restrict P hT D
  rcases exists_utility_of_encodable_complete_transitive (restrict P D) hC' hT' with
    ⟨u, hu⟩
  exact ⟨D, hDcount, hDgap, u, hu⟩

/--
A packaged version of the previous theorem in which the restricted utility is
also bounded via postcomposition with `Real.arctan`.
-/
theorem exists_countable_gapCompatibleDense_restriction_with_boundedUtility
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (hCont : ContinuousPref P) :
    ∃ D : Set α,
      D.Countable ∧
      GapCompatibleDense P D ∧
      ∃ u : Utility.UtilityFunction D,
        Represents u (restrict P D) ∧
        BddAbove (restrictedUtilityImage u) ∧
        BddBelow (restrictedUtilityImage u) := by
  rcases exists_countable_gapCompatibleDense_restriction_with_utility P hC hT hCont with
    ⟨D, hDcount, hDgap, u, hu⟩
  refine ⟨D, hDcount, hDgap, arctanRestricted u, ?_, ?_, ?_⟩
  · exact represents_arctanRestricted P u hu
  · exact restrictedUtilityImage_bddAbove_arctanRestricted u
  · exact restrictedUtilityImage_bddBelow_arctanRestricted u

end SecondCountable

end Preference
end EcoLean
