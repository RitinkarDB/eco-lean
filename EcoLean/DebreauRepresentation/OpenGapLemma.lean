import EcoLean.DebreauRepresentation.OpenGapLemmaSubtypeReduction
import EcoLean.DebreauRepresentation.OpenGapOrderVersion
import Mathlib.Data.Set.Countable
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Topology.Separation.Basic
import Mathlib.Data.Finset.Sort

/-!
# Open gap lemma

This file reduces the subtype-level open gap lemma to the order-version theorem,
and records a few basic compatibility lemmas for strictly increasing maps.
-/

namespace EcoLean
namespace Preference

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
The range of a function on a finite type has only open gaps.
-/
theorem finite_range_has_only_openGaps
    {T : Type} [Fintype T]
    (g : T → ℝ) :
    HasOnlyOpenGaps (Set.range g) := by
  intro a b hGap
  rcases hGap with ⟨hab, ha_cl, hb_cl, hNoMid⟩
  have hfin : (Set.range g).Finite := Set.finite_range g
  have hclosed : IsClosed (Set.range g) := hfin.isClosed
  have hclosure : closure (Set.range g) = Set.range g := hclosed.closure_eq
  have ha : a ∈ Set.range g := by
    simpa [hclosure] using ha_cl
  have hb : b ∈ Set.range g := by
    simpa [hclosure] using hb_cl
  exact ⟨⟨hab, ha_cl, hb_cl, hNoMid⟩, ha, hb⟩

/--
A finite linear order admits a strictly increasing map into `ℕ`.
-/
theorem exists_strictMono_nat_of_finite
    (T : Type) [LinearOrder T] [Fintype T] :
    ∃ f : T → ℕ, StrictMono f := by
  classical
  let n := Fintype.card T
  let e : Fin n ≃o T := Fintype.orderIsoFinOfCardEq T rfl
  refine ⟨fun t => ((e.symm t : Fin n) : ℕ), ?_⟩
  intro a b hab
  exact_mod_cast (e.symm.strictMono hab)


/--
If the order-version open gap lemma holds, then the subtype-level patched open
gap lemma follows.
-/
theorem countableOpenGapLemmaOnSubtypes_of_orderVersion
    (hOrder : CountableOpenGapLemmaOnOrders) :
    CountableOpenGapLemmaOnSubtypes := by
  intro T _ _ e he hCompat
  letI : Countable ↥(Set.range e) := by
    simpa using (Set.Countable.to_subtype (Set.countable_range e))
  simpa [BoundPreservingOpenGapAdjustmentOn] using
    (hOrder ↥(Set.range e))

/--
A bounded open-gap embedding of a finite linear order into `ℝ`.
-/
theorem boundedOpenGapEmbedding_of_finite
    (T : Type) [LinearOrder T] [Fintype T] :
    BoundedOpenGapEmbedding T := by
  sorry

/--
A countable linear order admits a bounded open-gap embedding if every finite
suborder does.
-/
theorem countableOpenGapLemmaOnOrders_of_finite
    (hFinite :
      ∀ (T : Type) [LinearOrder T] [Fintype T], BoundedOpenGapEmbedding T) :
    CountableOpenGapLemmaOnOrders := by
  intro T _ _
  sorry

/--
Order-version open gap lemma.

This is the main remaining theorem.
-/
theorem countableOpenGapLemmaOnOrders_proof :
    CountableOpenGapLemmaOnOrders := by
  exact countableOpenGapLemmaOnOrders_of_finite boundedOpenGapEmbedding_of_finite

/--
Target theorem: the patched countable open gap lemma for countable linear
orders already realised as subtypes of `ℝ`.
-/
theorem countableOpenGapLemmaOnSubtypes_proof :
    CountableOpenGapLemmaOnSubtypes := by
  exact countableOpenGapLemmaOnSubtypes_of_orderVersion
    countableOpenGapLemmaOnOrders_proof

end Preference
end EcoLean
