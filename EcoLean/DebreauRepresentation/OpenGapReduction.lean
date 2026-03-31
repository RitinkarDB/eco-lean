import EcoLean.DebreauRepresentation.BoundPreservingGapAdjustment
import Mathlib.Data.Set.Countable

/-!
# Reduction of the open gap lemma

This file reduces the gap-adjustment problem for a restricted utility function
to the corresponding problem for its image as a subset of `ℝ`.

The compatibility condition is phrased on adjacent points in the subtype order
of a subset of `ℝ`, rather than directly as a property of arbitrary pairs of
real numbers in the set.
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
There is no point strictly between `a` and `b`.
-/
def NoMiddlePoint {T : Type} [LinearOrder T] (a b : T) : Prop :=
  ¬ ∃ c : T, a < c ∧ c < b

/--
Compatibility condition for a subset `S ⊆ ℝ`, phrased on the subtype order
of `S`.

If `a < b` are adjacent points of `S` in the subtype order, then the interval
between their real values is an open gap of `S`.
-/
def SetGapPatternCompatible (S : Set ℝ) : Prop :=
  ∀ {a b : S}, a < b → NoMiddlePoint a b → IsOpenGap S a.1 b.1

/--
Compatibility condition for a strictly increasing real-valued map on a linear
order.

If `a < b` are adjacent in the domain order, then the interval between `e a`
and `e b` is an open gap in the image of `e`.
-/
def DomainGapCompatible
    {T : Type} [LinearOrder T]
    (e : T → ℝ) : Prop :=
  ∀ {a b : T}, a < b → NoMiddlePoint a b →
    IsOpenGap (Set.range e) (e a) (e b)

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

The compatibility hypothesis is expressed on the subtype order of `S`.
-/
def CountableOpenGapLemma : Prop :=
  ∀ S : Set ℝ, S.Countable → SetGapPatternCompatible S →
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
    (hCompat : SetGapPatternCompatible (restrictedUtilityImage u)) :
    BoundPreservingGapAdjustmentExists u := by
  apply boundPreservingGapAdjustmentExists_of_image
  apply hGapLemma
  · exact restrictedUtilityImage_countable u
  · exact hCompat

end Preference
end EcoLean
