import EcoLean.DebreauRepresentation.OpenGapLemmaSubtypeReduction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Set.Countable
import Mathlib.Order.Monotone.Basic

/-!
# Open gap lemma

This file is intended to prove the patched countable open gap lemma in subtype
form, and then recover the set-level version by reduction.
-/

universe u

namespace EcoLean
namespace Preference

/--
`Real.arctan` lands inside the arctan interval.
-/
theorem mapsIntoArctanInterval_arctan :
    MapsIntoArctanInterval Real.arctan := by
  intro r
  constructor
  · exact Real.neg_pi_div_two_lt_arctan r
  · exact Real.arctan_lt_pi_div_two r

/--
Set-level patched countable open gap lemma, once the subtype-level version is
proved.
-/
theorem countableOpenGapLemma
    (hSub : CountableOpenGapLemmaOnSubtypes) :
    CountableOpenGapLemma := by
  exact countableOpenGapLemma_of_subtypeVersion hSub

/--
If the range of a strictly increasing map has compatible gap pattern, then for
any two points `a < b` in the domain, either there is a domain point strictly
between them or the corresponding image interval is an open gap.
-/
theorem gapPatternCompatible_of_strictMono_range
    {T : Type} [LinearOrder T]
    (e : T → ℝ)
    (he : StrictMono e)
    (hCompat : GapPatternCompatible (Set.range e)) :
    ∀ {a b : T}, a < b →
      (∃ c : T, a < c ∧ c < b) ∨
      IsOpenGap (Set.range e) (e a) (e b) := by
  intro a b hab
  have hea : e a ∈ Set.range e := ⟨a, rfl⟩
  have heb : e b ∈ Set.range e := ⟨b, rfl⟩
  have heab : e a < e b := he hab
  rcases hCompat hea heb heab with hmid | hgap
  · left
    rcases hmid with ⟨x, hxS, hax, hxb⟩
    rcases hxS with ⟨c, rfl⟩
    refine ⟨c, ?_, ?_⟩
    · by_contra hnot
      have hca : c ≤ a := le_of_not_gt hnot
      have heca : e c ≤ e a := he.monotone hca
      exact (not_le_of_gt hax) heca
    · by_contra hnot
      have hbc : b ≤ c := le_of_not_gt hnot
      have hebc : e b ≤ e c := he.monotone hbc
      exact (not_le_of_gt hxb) hebc
  · right
    exact hgap

/--
If there is no domain point strictly between `a` and `b`, then the image
interval between `e a` and `e b` is an open gap.
-/
theorem isOpenGap_of_no_middlePoint_of_strictMono_range
    {T : Type} [LinearOrder T]
    (e : T → ℝ)
    (he : StrictMono e)
    (hCompat : GapPatternCompatible (Set.range e))
    {a b : T}
    (hab : a < b)
    (hNoMid : ¬ ∃ c : T, a < c ∧ c < b) :
    IsOpenGap (Set.range e) (e a) (e b) := by
  rcases gapPatternCompatible_of_strictMono_range e he hCompat hab with
    hMid | hGap
  · exact False.elim (hNoMid hMid)
  · exact hGap

/--
There is no point strictly between `a` and `b`.
-/
def NoMiddlePoint {T : Type} [LinearOrder T] (a b : T) : Prop :=
  ¬ ∃ c : T, a < c ∧ c < b

/--
If there is no point strictly between `a` and `b`, then the image interval
between `e a` and `e b` is an open gap.
-/
theorem isOpenGap_of_noMiddlePoint_of_strictMono_range
    {T : Type} [LinearOrder T]
    (e : T → ℝ)
    (he : StrictMono e)
    (hCompat : GapPatternCompatible (Set.range e))
    {a b : T}
    (hab : a < b)
    (hNoMid : NoMiddlePoint a b) :
    IsOpenGap (Set.range e) (e a) (e b) := by
  rcases gapPatternCompatible_of_strictMono_range e he hCompat hab with
    hMid | hGap
  · exact False.elim (hNoMid hMid)
  · exact hGap

/--
If there is a point strictly between `a` and `b`, then `NoMiddlePoint a b`
fails.
-/
theorem not_noMiddlePoint_of_exists_middle
    {T : Type} [LinearOrder T]
    {a b : T}
    (hMid : ∃ c : T, a < c ∧ c < b) :
    ¬ NoMiddlePoint a b := by
  intro hNoMid
  exact hNoMid hMid

/--
If `a < b` and there is no point strictly between them, then their images under
a strictly increasing map form an open gap in the image set.
-/
theorem image_pair_isOpenGap_of_noMiddlePoint
    {T : Type} [LinearOrder T]
    (e : T → ℝ)
    (he : StrictMono e)
    (hCompat : GapPatternCompatible (Set.range e))
    {a b : T}
    (hab : a < b)
    (hNoMid : NoMiddlePoint a b) :
    e a < e b ∧ IsOpenGap (Set.range e) (e a) (e b) := by
  refine ⟨he hab, ?_⟩
  exact isOpenGap_of_noMiddlePoint_of_strictMono_range e he hCompat hab hNoMid

/--
There is no point strictly between `a` and `b`.
-/
def NoMiddlePoint {T : Type} [LinearOrder T] (a b : T) : Prop :=
  ¬ ∃ c : T, a < c ∧ c < b

/--
If there is no point strictly between `a` and `b`, then the image interval
between `e a` and `e b` is an open gap.
-/
theorem isOpenGap_of_noMiddlePoint_of_strictMono_range
    {T : Type} [LinearOrder T]
    (e : T → ℝ)
    (he : StrictMono e)
    (hCompat : GapPatternCompatible (Set.range e))
    {a b : T}
    (hab : a < b)
    (hNoMid : NoMiddlePoint a b) :
    IsOpenGap (Set.range e) (e a) (e b) := by
  rcases gapPatternCompatible_of_strictMono_range e he hCompat hab with
    hMid | hGap
  · exact False.elim (hNoMid hMid)
  · exact hGap


/--
If `NoMiddlePoint a b` fails, then there exists a point strictly between `a`
and `b`.
-/
theorem exists_middlePoint_of_not_noMiddlePoint
    {T : Type} [LinearOrder T]
    {a b : T}
    (hNot : ¬ NoMiddlePoint a b) :
    ∃ c : T, a < c ∧ c < b := by
  classical
  by_contra hNoMid
  exact hNot hNoMid

/--
For any `a < b`, either there is a point strictly between them, or their image
interval under a strictly increasing map is an open gap.
-/
theorem exists_middlePoint_or_isOpenGap
    {T : Type} [LinearOrder T]
    (e : T → ℝ)
    (he : StrictMono e)
    (hCompat : GapPatternCompatible (Set.range e))
    {a b : T}
    (hab : a < b) :
    (∃ c : T, a < c ∧ c < b) ∨
      IsOpenGap (Set.range e) (e a) (e b) := by
  by_cases hNoMid : NoMiddlePoint a b
  · right
    exact isOpenGap_of_noMiddlePoint_of_strictMono_range e he hCompat hab hNoMid
  · left
    exact exists_middlePoint_of_not_noMiddlePoint hNoMid
/--
Target theorem: the patched countable open gap lemma for countable linear
orders already realised as subtypes of `ℝ`.
-/
theorem countableOpenGapLemmaOnSubtypes_proof :
    CountableOpenGapLemmaOnSubtypes := by
  intro T _ _ e he hCompat
  -- real proof starts here
  sorry



end Preference
end EcoLean
