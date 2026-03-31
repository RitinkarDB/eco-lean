import EcoLean.DebreauRepresentation.BoundPreservingGapAdjustment
import Mathlib.Data.Set.Countable

/-!
# Reduction of the open gap lemma

This file reduces the gap-adjustment problem for a restricted utility function
to the corresponding problem for its image as a subset of `ℝ`.

The naive set-level countable open gap lemma is too strong for arbitrary
countable subsets of `ℝ`, so we use a compatibility condition on the gap
pattern of the set.
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
A countable subset of `ℝ` has compatible gap pattern if every strict interval
between two of its points either contains another point of the set or is an
open gap.
-/
def GapPatternCompatible (S : Set ℝ) : Prop :=
  ∀ ⦃a b : ℝ⦄, a ∈ S → b ∈ S → a < b →
    (∃ c : ℝ, c ∈ S ∧ a < c ∧ c < b) ∨ IsOpenGap S a b

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
    (hImg : BoundPreservingOpenGapAdjustmentOn (restrictedUtilityImage u)) :
    BoundPreservingGapAdjustmentExists u := by
  exact boundPreservingGapAdjustmentExists_of_image u hImg

/--
Patched form of the countable open gap lemma.

The compatibility hypothesis rules out the obvious counterexamples coming from
isolated adjacent image points.
-/
def CountableOpenGapLemma : Prop :=
  ∀ S : Set ℝ, S.Countable → GapPatternCompatible S →
    BoundPreservingOpenGapAdjustmentOn S

/--
If the patched countable open gap lemma holds on `ℝ`, then every countable
restricted utility whose image has compatible gap pattern admits a
bound-preserving gap adjustment.
-/
theorem boundPreservingGapAdjustmentExists_of_countable
    {D : Set α}
    [Countable D]
    (hGapLemma : CountableOpenGapLemma)
    (u : Utility.UtilityFunction D)
    (hCompat : GapPatternCompatible (restrictedUtilityImage u)) :
    BoundPreservingGapAdjustmentExists u := by
  apply boundPreservingGapAdjustmentExists_of_image
  apply hGapLemma
  · exact restrictedUtilityImage_countable u
  · exact hCompat

end Preference
end EcoLean
