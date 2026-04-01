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
  classical
  rcases exists_strictMono_nat_of_finite T with ⟨f, hf⟩
  let g : T → ℝ := fun t => Real.arctan (f t)
  refine ⟨g, ?_, ?_, ?_⟩
  · intro a b hab
    exact Real.arctan_strictMono (by exact_mod_cast hf hab)
  · intro t
    constructor
    · exact Real.neg_pi_div_two_lt_arctan (f t)
    · exact Real.arctan_lt_pi_div_two (f t)
  · exact finite_range_has_only_openGaps g
/--
A countable linear order admits an injective coding into `ℕ`.
-/
theorem exists_injective_nat_of_countable
    (T : Type) [LinearOrder T] [Countable T] :
    ∃ f : T → ℕ, Function.Injective f := by
  classical
  letI : Encodable T := Encodable.ofCountable T
  exact ⟨Encodable.encode, Encodable.encode_injective⟩


/--
The finite truncation of a countable order along a coding `f : T → ℕ`.
-/
def codeTruncation {T : Type} (f : T → ℕ) (n : ℕ) : Type :=
  { t : T // f t ≤ n }

/--
A coding truncation inherits the linear order from the ambient type.
-/
instance {T : Type} [LinearOrder T] (f : T → ℕ) (n : ℕ) :
    LinearOrder (codeTruncation f n) := by
  dsimp [codeTruncation]
  infer_instance

/--
Each finite coding truncation admits a bounded open-gap embedding.
-/
theorem boundedOpenGapEmbedding_codeTruncation
    {T : Type} [LinearOrder T]
    (f : T → ℕ)
    (hf : Function.Injective f)
    (n : ℕ) :
    BoundedOpenGapEmbedding (codeTruncation f n) := by
  letI : Fintype (codeTruncation f n) := by
    classical
    let g : codeTruncation f n → Fin (n + 1) :=
      fun t => ⟨f t.1, Nat.lt_succ_of_le t.2⟩
    exact Fintype.ofInjective g (by
      intro a b h
      apply Subtype.ext
      exact hf (Fin.mk.inj h))
  exact boundedOpenGapEmbedding_of_finite (codeTruncation f n)

/--
The natural inclusion of the `n`-th truncation into the `(n+1)`-st truncation.
-/
def codeTruncationSuccInclusion
    {T : Type} [LinearOrder T]
    (f : T → ℕ) (n : ℕ) :
    codeTruncation f n → codeTruncation f (n + 1) :=
  fun x => ⟨x.1, Nat.le_trans x.2 (Nat.le_succ n)⟩

@[simp] theorem codeTruncationSuccInclusion_val
    {T : Type} [LinearOrder T]
    (f : T → ℕ) (n : ℕ) (x : codeTruncation f n) :
    (codeTruncationSuccInclusion f n x).1 = x.1 := by
  rfl

/--
A coherent family of bounded open-gap embeddings on the finite truncations.
-/
def CoherentBoundedOpenGapEmbeddingChain
    {T : Type} [LinearOrder T]
    (f : T → ℕ) : Prop :=
  ∃ g : ∀ n, codeTruncation f n → ℝ,
    (∀ n, StrictMono (g n)) ∧
    (∀ n, MapsIntoArctanIntervalOn (g n)) ∧
    (∀ n, HasOnlyOpenGaps (Set.range (g n))) ∧
    (∀ n (x : codeTruncation f n),
      g (n + 1) (codeTruncationSuccInclusion f n x) = g n x)

/--
Target coherence theorem for the finite truncations induced by an injective
coding into `ℕ`.
-/
theorem exists_coherent_boundedOpenGapEmbedding_chain
    {T : Type} [LinearOrder T]
    (f : T → ℕ)
    (hf : Function.Injective f) :
    CoherentBoundedOpenGapEmbeddingChain f := by
  sorry


/--
Order-version open gap lemma.

This is the main remaining theorem.
-/
theorem countableOpenGapLemmaOnOrders_proof :
    CountableOpenGapLemmaOnOrders := by
  intro T _ _
  classical
  rcases exists_injective_nat_of_countable T with ⟨f, hf⟩
  rcases exists_coherent_boundedOpenGapEmbedding_chain f hf with
    ⟨g, hgmono, hgint, hggap, hcoh⟩
  sorry
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
