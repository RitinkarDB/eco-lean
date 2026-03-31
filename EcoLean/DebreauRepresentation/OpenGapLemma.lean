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
If `a < b` and there is no point strictly between them, then their images under
a strictly increasing map form an open gap in the image set.
-/
theorem image_pair_isOpenGap_of_noMiddlePoint
    {T : Type} [LinearOrder T]
    (e : T → ℝ)
    (he : StrictMono e)
    (hCompat : DomainGapCompatible e)
    {a b : T}
    (hab : a < b)
    (hNoMid : NoMiddlePoint a b) :
    e a < e b ∧ IsOpenGap (Set.range e) (e a) (e b) := by
  refine ⟨he hab, ?_⟩
  exact hCompat hab hNoMid

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
    (hCompat : DomainGapCompatible e)
    {a b : T}
    (hab : a < b) :
    (∃ c : T, a < c ∧ c < b) ∨
      IsOpenGap (Set.range e) (e a) (e b) := by
  by_cases hNoMid : NoMiddlePoint a b
  · right
    exact (image_pair_isOpenGap_of_noMiddlePoint e he hCompat hab hNoMid).2
  · left
    exact exists_middlePoint_of_not_noMiddlePoint hNoMid

/--
If there is no point strictly between two points of `Set.range e` in the subtype
order, then there is no point strictly between their preimages in the domain
order.
-/
theorem noMiddlePoint_domain_of_noMiddlePoint_range
    {T : Type} [LinearOrder T]
    (e : T → ℝ)
    (he : StrictMono e)
    {a b : T}
    (hNoMid :
      NoMiddlePoint
        (⟨e a, ⟨a, rfl⟩⟩ : Set.range e)
        (⟨e b, ⟨b, rfl⟩⟩ : Set.range e)) :
    NoMiddlePoint a b := by
  intro hMid
  rcases hMid with ⟨c, hac, hcb⟩
  let rc : Set.range e := ⟨e c, ⟨c, rfl⟩⟩
  have ha : (⟨e a, ⟨a, rfl⟩⟩ : Set.range e) < rc := by
    exact he hac
  have hb : rc < (⟨e b, ⟨b, rfl⟩⟩ : Set.range e) := by
    exact he hcb
  exact hNoMid ⟨rc, ha, hb⟩

/--
A domain-side compatibility statement for a strictly increasing map induces the
corresponding subtype-order compatibility statement on its range.
-/
theorem setGapPatternCompatible_range_of_domainGapCompatible
    {T : Type} [LinearOrder T]
    (e : T → ℝ)
    (he : StrictMono e)
    (hCompat : DomainGapCompatible e) :
    SetGapPatternCompatible (Set.range e) := by
  intro a b hab hNoMid
  rcases a with ⟨ra, ⟨a0, rfl⟩⟩
  rcases b with ⟨rb, ⟨b0, rfl⟩⟩
  have hab' : a0 < b0 := by
    exact (he.lt_iff_lt).1 hab
  have hNoMid' : NoMiddlePoint a0 b0 := by
    exact noMiddlePoint_domain_of_noMiddlePoint_range e he hNoMid
  simpa using hCompat hab' hNoMid'

/--
A bound-preserving open-gap adjustment constructed directly along the embedding
`e`.
-/
def BoundPreservingOpenGapAdjustmentAlong
    {T : Type} [LinearOrder T]
    (e : T → ℝ) : Prop :=
  ∃ φ : ℝ → ℝ,
    StrictMono φ ∧
    MapsIntoArctanInterval φ ∧
    HasOnlyOpenGaps (Set.range (fun t => φ (e t)))

/--
Postcomposing the range of `e` by `φ` is the same as taking the range of the
postcomposed map `t ↦ φ (e t)`.
-/
theorem image_range_eq_range_postcompose
    {T : Type} (e : T → ℝ) (φ : ℝ → ℝ) :
    φ '' (Set.range e) = Set.range (fun t => φ (e t)) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases hx with ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  · intro hy
    rcases hy with ⟨t, rfl⟩
    exact ⟨e t, ⟨t, rfl⟩, rfl⟩

/--
If one has a bound-preserving open-gap adjustment along `e`, then one obtains a
bound-preserving open-gap adjustment of the range of `e`.
-/
theorem boundPreservingOpenGapAdjustmentOn_of_along
    {T : Type} [LinearOrder T]
    (e : T → ℝ)
    (h : BoundPreservingOpenGapAdjustmentAlong e) :
    BoundPreservingOpenGapAdjustmentOn (Set.range e) := by
  rcases h with ⟨φ, hφmono, hφbd, hφgap⟩
  refine ⟨φ, hφmono, hφbd, ?_⟩
  simpa [image_range_eq_range_postcompose] using hφgap

/--
If one can construct a bound-preserving open-gap adjustment along every
countable strictly increasing embedding `e`, then the subtype-level patched
open gap lemma follows.
-/
theorem countableOpenGapLemmaOnSubtypes_of_along
    (hAlong :
      ∀ (T : Type) [LinearOrder T] [Countable T] (e : T → ℝ),
        StrictMono e →
        DomainGapCompatible e →
        BoundPreservingOpenGapAdjustmentAlong e) :
    CountableOpenGapLemmaOnSubtypes := by
  intro T _ _ e he hCompat
  exact boundPreservingOpenGapAdjustmentOn_of_along e
    (hAlong T e he hCompat)


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
