import EcoLean.DebreauRepresentation.GapAdjustment
import EcoLean.DebreauRepresentation.GapCompatibleRestriction
import EcoLean.DebreauRepresentation.BoundedAdjustment

/-!
# Gap-adjusted restriction packages

This file shows how the eventual gap-adjustment theorem plugs into the
countable restriction step.

It does not prove the gap-adjustment theorem itself. Instead, it packages the
consequence that once a restricted utility is gap-adjustable, we may replace it
by a gap-adjusted restricted utility without losing representation.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
If a restricted utility admits a gap adjustment, then there is a gap-adjusted
restricted utility representing the same restricted preference.
-/
theorem exists_gapAdjusted_restriction
    {D : Set α}
    (P : Preference α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    (hAdj : GapAdjustmentExists u) :
    ∃ u' : Utility.UtilityFunction D,
      Represents u' (restrict P D) ∧
      IsGapAdjustedRestrictedUtility u' := by
  rcases hAdj with ⟨u', hSame, hGap⟩
  refine ⟨u', ?_, hGap⟩
  intro x y
  rw [hu x y]
  exact hSame x y

section SecondCountable

variable [TopologicalSpace α] [SecondCountableTopology α]

/--
If every restricted utility admits a gap adjustment, then every complete,
transitive, continuous preference on a second-countable space admits a
countable gap-compatible dense subset together with a gap-adjusted restricted
utility representation.
-/
theorem exists_countable_gapCompatibleDense_restriction_with_gapAdjustedUtility
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (hCont : ContinuousPref P)
    (hGapAdj :
      ∀ {D : Set α} (u : Utility.UtilityFunction D), GapAdjustmentExists u) :
    ∃ D : Set α,
      D.Countable ∧
      GapCompatibleDense P D ∧
      ∃ u : Utility.UtilityFunction D,
        Represents u (restrict P D) ∧
        IsGapAdjustedRestrictedUtility u := by
  rcases exists_countable_gapCompatibleDense_restriction_with_utility
      P hC hT hCont with
    ⟨D, hDcount, hDgap, u, hu⟩
  rcases exists_gapAdjusted_restriction P u hu (hGapAdj u) with
    ⟨u', hu'Rep, hu'Gap⟩
  exact ⟨D, hDcount, hDgap, u', hu'Rep, hu'Gap⟩

/--
A bounded version of the previous package, retaining the arctan-bounded
restricted utility but also recording the abstract availability of a gap
adjustment for that bounded restricted utility.
-/
theorem exists_countable_gapCompatibleDense_restriction_with_boundedUtility_and_gapAdjustment
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (hCont : ContinuousPref P)
    (hGapAdj :
      ∀ {D : Set α} (u : Utility.UtilityFunction D), GapAdjustmentExists u) :
    ∃ D : Set α,
      D.Countable ∧
      GapCompatibleDense P D ∧
      ∃ u : Utility.UtilityFunction D,
        Represents u (restrict P D) ∧
        BddAbove (restrictedUtilityImage u) ∧
        BddBelow (restrictedUtilityImage u) ∧
        GapAdjustmentExists u := by
  rcases exists_countable_gapCompatibleDense_restriction_with_boundedUtility
      P hC hT hCont with
    ⟨D, hDcount, hDgap, u, hu, hAbove, hBelow⟩
  exact ⟨D, hDcount, hDgap, u, hu, hAbove, hBelow, hGapAdj u⟩

end SecondCountable

end Preference
end EcoLean
