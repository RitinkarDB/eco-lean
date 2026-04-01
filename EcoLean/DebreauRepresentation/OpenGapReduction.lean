import EcoLean.DebreauRepresentation.OpenGapOrderVersion
import Mathlib.Data.Set.Countable

/-!
# Reduction of the open gap lemma

This file contains the basic countability and compatibility notions used in the
open-gap reduction.

The set-level open-gap adjustment is phrased in terms of a bounded open-gap
embedding of the subtype `S`.
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
A set-level bound-preserving open-gap adjustment of `S` is a bounded open-gap
embedding of the subtype `S`.
-/
def BoundPreservingOpenGapAdjustmentOn (S : Set ℝ) : Prop :=
  BoundedOpenGapEmbedding ↥S

/--
Patched form of the countable open gap lemma.

The compatibility hypothesis is expressed on the subtype order of `S`.
-/
def CountableOpenGapLemma : Prop :=
  ∀ S : Set ℝ, S.Countable → SetGapPatternCompatible S →
    BoundPreservingOpenGapAdjustmentOn S

end Preference
end EcoLean
