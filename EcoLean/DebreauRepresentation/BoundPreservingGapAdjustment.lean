import EcoLean.DebreauRepresentation.GapAdjustedRestriction
import EcoLean.DebreauRepresentation.BoundedAdjustment

/-!
# Bound-preserving gap adjustment

This file strengthens the abstract gap-adjustment interface so that the adjusted
restricted utility still takes values in the arctan interval `(-π / 2, π / 2)`.

This is the form needed by the anchored-cut construction.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
A real map lands inside the arctan interval if all of its values lie strictly
between `-π / 2` and `π / 2`.
-/
def MapsIntoArctanInterval (φ : ℝ → ℝ) : Prop :=
  ∀ r : ℝ, -(Real.pi / 2) < φ r ∧ φ r < Real.pi / 2

/--
A bound-preserving gap adjustment for a restricted utility is a strictly
increasing postcomposition whose values remain in the arctan interval and whose
image has only open gaps.
-/
def BoundPreservingGapAdjustmentExists
    {D : Set α}
    (u : Utility.UtilityFunction D) : Prop :=
  ∃ φ : ℝ → ℝ,
    StrictMono φ ∧
    MapsIntoArctanInterval φ ∧
    HasOnlyOpenGaps (restrictedUtilityImage (postcomposeRestricted u φ))

/--
If a postcomposition lands in the arctan interval, then the image of the
postcomposed restricted utility is bounded above by `π / 2`.
-/
theorem restrictedUtilityImage_bddAbove_of_mapsIntoArctanInterval
    {D : Set α}
    (u : Utility.UtilityFunction D)
    {φ : ℝ → ℝ}
    (hφ : MapsIntoArctanInterval φ) :
    BddAbove (restrictedUtilityImage (postcomposeRestricted u φ)) := by
  refine ⟨Real.pi / 2, ?_⟩
  intro r hr
  rcases hr with ⟨d, rfl⟩
  exact le_of_lt (hφ (u d)).2

/--
If a postcomposition lands in the arctan interval, then the image of the
postcomposed restricted utility is bounded below by `-π / 2`.
-/
theorem restrictedUtilityImage_bddBelow_of_mapsIntoArctanInterval
    {D : Set α}
    (u : Utility.UtilityFunction D)
    {φ : ℝ → ℝ}
    (hφ : MapsIntoArctanInterval φ) :
    BddBelow (restrictedUtilityImage (postcomposeRestricted u φ)) := by
  refine ⟨-(Real.pi / 2), ?_⟩
  intro r hr
  rcases hr with ⟨d, rfl⟩
  exact le_of_lt (hφ (u d)).1

/--
If a restricted utility admits a bound-preserving gap adjustment, then there is
a restricted utility that still represents the restricted preference, has only
open gaps in its image, and remains bounded inside the arctan interval.
-/
theorem exists_boundPreservingGapAdjusted_restriction
    {D : Set α}
    (P : Preference α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    (hAdj : BoundPreservingGapAdjustmentExists u) :
    ∃ u' : Utility.UtilityFunction D,
      Represents u' (restrict P D) ∧
      IsGapAdjustedRestrictedUtility u' ∧
      BddAbove (restrictedUtilityImage u') ∧
      BddBelow (restrictedUtilityImage u') := by
  rcases hAdj with ⟨φ, hφmono, hφbd, hφgap⟩
  refine ⟨postcomposeRestricted u φ, ?_, ?_, ?_, ?_⟩
  · exact represents_postcomposeRestricted_strictMono P u hu hφmono
  · exact hφgap
  · exact restrictedUtilityImage_bddAbove_of_mapsIntoArctanInterval u hφbd
  · exact restrictedUtilityImage_bddBelow_of_mapsIntoArctanInterval u hφbd

section SecondCountable

variable [TopologicalSpace α] [SecondCountableTopology α]

/--
A packaged second-countable restriction theorem using a bound-preserving gap
adjustment.
-/
theorem exists_countable_gapCompatibleDense_restriction_with_boundPreservingGapAdjustedUtility
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (hCont : ContinuousPref P)
    (hAdj :
      ∀ {D : Set α} (u : Utility.UtilityFunction D),
        BoundPreservingGapAdjustmentExists u) :
    ∃ D : Set α,
      D.Countable ∧
      GapCompatibleDense P D ∧
      ∃ u : Utility.UtilityFunction D,
        Represents u (restrict P D) ∧
        IsGapAdjustedRestrictedUtility u ∧
        BddAbove (restrictedUtilityImage u) ∧
        BddBelow (restrictedUtilityImage u) := by
  rcases exists_countable_gapCompatibleDense_restriction_with_utility
      P hC hT hCont with ⟨D, hDcount, hDgap, u, hu⟩
  rcases exists_boundPreservingGapAdjusted_restriction P u hu (hAdj u) with
    ⟨u', hu'Rep, hu'Gap, hu'Above, hu'Below⟩
  exact ⟨D, hDcount, hDgap, u', hu'Rep, hu'Gap, hu'Above, hu'Below⟩

end SecondCountable

end Preference
end EcoLean
