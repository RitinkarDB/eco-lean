import EcoLean.DebreauRepresentation.GapCompatibleRestriction
import EcoLean.DebreauRepresentation.BoundedOrderGapAdjustmentTransfer
import EcoLean.DebreauRepresentation.BoundPreservingGapAdjustment

/-!
# Bounded gap-adjusted restricted utilities

This file combines the countable gap-compatible restriction step with the
bounded transfer of the order-version open gap lemma.

The output is a countable gap-compatible dense subset together with a bounded,
gap-adjusted restricted utility representation.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

section SecondCountable

variable [TopologicalSpace α] [SecondCountableTopology α]

/--
If the order-version open gap lemma holds, then every complete, transitive,
continuous preference on a second-countable space admits a countable
gap-compatible dense subset together with a bounded, gap-adjusted restricted
utility representation.
-/
theorem exists_countable_gapCompatibleDense_restriction_with_boundedGapAdjustedUtility
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (hCont : ContinuousPref P)
    (hOrder : CountableOpenGapLemmaOnOrders) :
    ∃ D : Set α,
      D.Countable ∧
      GapCompatibleDense P D ∧
      ∃ u : Utility.UtilityFunction D,
        Represents u (restrict P D) ∧
        IsGapAdjustedRestrictedUtility u ∧
        BddAbove (restrictedUtilityImage u) ∧
        BddBelow (restrictedUtilityImage u) := by
  rcases exists_countable_gapCompatibleDense_restriction_with_utility
      P hC hT hCont with
    ⟨D, hDcount, hDgap, u, hu⟩
  letI : Countable D := by
    simpa using hDcount
  rcases boundPreservingGapAdjustmentExists_of_countable_restrictedUtility
      u hOrder with
    ⟨u', hSame, hGap, hAbove, hBelow⟩
  refine ⟨D, hDcount, hDgap, u', ?_, hGap, hAbove, hBelow⟩
  exact represents_of_sameOrderRestrictedUtility P u u' hu hSame

/--
A weaker packaged form of the previous theorem, forgetting the boundedness
information.
-/
theorem exists_countable_gapCompatibleDense_restriction_with_gapAdjustedUtility
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (hCont : ContinuousPref P)
    (hOrder : CountableOpenGapLemmaOnOrders) :
    ∃ D : Set α,
      D.Countable ∧
      GapCompatibleDense P D ∧
      ∃ u : Utility.UtilityFunction D,
        Represents u (restrict P D) ∧
        IsGapAdjustedRestrictedUtility u := by
  rcases exists_countable_gapCompatibleDense_restriction_with_boundedGapAdjustedUtility
      P hC hT hCont hOrder with
    ⟨D, hDcount, hDgap, u, huRep, huGap, huAbove, huBelow⟩
  exact ⟨D, hDcount, hDgap, u, huRep, huGap⟩

end SecondCountable

end Preference
end EcoLean
