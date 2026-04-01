import EcoLean.DebreauRepresentation.GapAdjustment

/-!
# Bound-preserving gap adjustment

This file packages the bounded version of gap adjustment for restricted
utilities.

A bound-preserving gap adjustment is a new restricted utility with the same
induced weak order, whose image has only open gaps and is bounded above and
below.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
A restricted utility admits a bound-preserving gap adjustment if there exists
another restricted utility with the same induced weak order, only open gaps in
its image, and bounded image.
-/
def BoundPreservingGapAdjustmentExists
    {D : Set α}
    (u : Utility.UtilityFunction D) : Prop :=
  ∃ u' : Utility.UtilityFunction D,
    SameOrderRestrictedUtility u u' ∧
    IsGapAdjustedRestrictedUtility u' ∧
    BddAbove (restrictedUtilityImage u') ∧
    BddBelow (restrictedUtilityImage u')

/--
If a restricted utility admits a bound-preserving gap adjustment, then it also
admits a gap adjustment.
-/
theorem gapAdjustmentExists_of_boundPreserving
    {D : Set α}
    (u : Utility.UtilityFunction D)
    (h : BoundPreservingGapAdjustmentExists u) :
    GapAdjustmentExists u := by
  rcases h with ⟨u', hSame, hGap, hAbove, hBelow⟩
  exact ⟨u', hSame, hGap⟩

/--
A bounded, gap-adjusted restricted utility represents the same restricted
preference whenever it has the same induced weak order as the original utility.
-/
theorem represents_of_sameOrderRestrictedUtility
    {D : Set α}
    (P : Preference α)
    (u u' : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    (hSame : SameOrderRestrictedUtility u u') :
    Represents u' (restrict P D) := by
  intro x y
  exact (hu x y).trans (hSame x y)

end Preference
end EcoLean
