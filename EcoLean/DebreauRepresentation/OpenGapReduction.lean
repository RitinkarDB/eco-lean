import EcoLean.DebreauRepresentation.BoundPreservingGapAdjustment
import Mathlib.Data.Set.Countable

/-!
# Preparatory lemmas for Debreau's gap lemma

This file reduces the gap-adjustment problem for a restricted utility function
to the corresponding problem for its image as a subset of `ℝ`.

The actual real-line gap lemma is still the main missing theorem. This file
sets up the exact interface that theorem will need.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
If the restricted domain is countable, then the image of a restricted utility
function is countable.
-/
theorem restrictedUtilityImage_countable
    {D : Set α}
    [Countable D]
    (u : Utility.UtilityFunction D) :
    (restrictedUtilityImage u).Countable := by
  classical
  simpa [restrictedUtilityImage] using (Set.countable_range u)

/--
A subset `S ⊆ ℝ` admits a bound-preserving open-gap adjustment if there is a
strictly increasing map into the arctan interval whose image of `S` has only
open gaps.
-/
def BoundPreservingOpenGapAdjustmentOn (S : Set ℝ) : Prop :=
  ∃ φ : ℝ → ℝ,
    StrictMono φ ∧
    MapsIntoArctanInterval φ ∧
    HasOnlyOpenGaps (φ '' S)

/--
If the image of a restricted utility admits a bound-preserving open-gap
adjustment, then the restricted utility itself admits a bound-preserving gap
adjustment.
-/
theorem boundPreservingGapAdjustmentExists_of_image
    {D : Set α}
    (u : Utility.UtilityFunction D)
    (hImg : BoundPreservingOpenGapAdjustmentOn (restrictedUtilityImage u)) :
    BoundPreservingGapAdjustmentExists u := by
  rcases hImg with ⟨φ, hφmono, hφbd, hφgap⟩
  refine ⟨φ, hφmono, hφbd, ?_⟩
  simpa [restrictedUtilityImage_postcompose] using hφgap

/--
A countable restricted utility admits a bound-preserving gap adjustment once
its image subset of `ℝ` does.
-/
theorem boundPreservingGapAdjustmentExists_of_countable_image
    {D : Set α}
    (u : Utility.UtilityFunction D)
    (hImg :
      BoundPreservingOpenGapAdjustmentOn (restrictedUtilityImage u)) :
    BoundPreservingGapAdjustmentExists u := by
  exact boundPreservingGapAdjustmentExists_of_image u hImg

/--
Target form of Debreau's open gap lemma for countable subsets of `ℝ`.

This is the remaining theorem needed to complete the gap-adjustment step.
-/
def CountableOpenGapLemma : Prop :=
  ∀ S : Set ℝ, S.Countable → BoundPreservingOpenGapAdjustmentOn S

/--
If the countable open gap lemma holds on `ℝ`, then every countable restricted
utility admits a bound-preserving gap adjustment.
-/
theorem boundPreservingGapAdjustmentExists_of_countable
    {D : Set α}
    [Countable D]
    (hGapLemma : CountableOpenGapLemma)
    (u : Utility.UtilityFunction D) :
    BoundPreservingGapAdjustmentExists u := by
  apply boundPreservingGapAdjustmentExists_of_image
  apply hGapLemma
  exact restrictedUtilityImage_countable u

end Preference
end EcoLean
