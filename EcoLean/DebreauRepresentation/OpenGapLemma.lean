import EcoLean.DebreauRepresentation.OpenGapLemmaSubtypeReduction
import EcoLean.DebreauRepresentation.OpenGapOrderVersion
import Mathlib.Data.Set.Countable
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Topology.Separation.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Encodable.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

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
The natural inclusion of the `m`-th truncation into the `n`-th truncation,
given `m ≤ n`.
-/
def codeTruncationInclusion
    {T : Type} [LinearOrder T]
    (f : T → ℕ) {m n : ℕ} (hmn : m ≤ n) :
    codeTruncation f m → codeTruncation f n :=
  fun x => ⟨x.1, Nat.le_trans x.2 hmn⟩

@[simp] theorem codeTruncationInclusion_val
    {T : Type} [LinearOrder T]
    (f : T → ℕ) {m n : ℕ} (hmn : m ≤ n) (x : codeTruncation f m) :
    (codeTruncationInclusion f hmn x).1 = x.1 := by
  rfl

@[simp] theorem codeTruncationInclusion_refl
    {T : Type} [LinearOrder T]
    (f : T → ℕ) (n : ℕ) (x : codeTruncation f n) :
    codeTruncationInclusion f (show n ≤ n by rfl) x = x := by
  apply Subtype.ext
  rfl

@[simp] theorem codeTruncationInclusion_succ
    {T : Type} [LinearOrder T]
    (f : T → ℕ) (n : ℕ) (x : codeTruncation f n) :
    codeTruncationInclusion f (Nat.le_succ n) x =
      codeTruncationSuccInclusion f n x := by
  rfl

/--
Successor coherence implies coherence along arbitrary inclusions.
-/
theorem coherent_on_all_inclusions
    {T : Type} [LinearOrder T]
    (f : T → ℕ)
    {g : ∀ n, codeTruncation f n → ℝ}
    (hcoh : ∀ n (x : codeTruncation f n),
      g (n + 1) (codeTruncationSuccInclusion f n x) = g n x) :
    ∀ {m n : ℕ} (hmn : m ≤ n) (x : codeTruncation f m),
      g n (codeTruncationInclusion f hmn x) = g m x := by
  intro m n hmn x
  induction hmn with
  | refl =>
      simp
  | @step n hmn ih =>
      have h1 :
          g (n + 1)
            (codeTruncationSuccInclusion f n
              (codeTruncationInclusion f hmn x)) =
          g n (codeTruncationInclusion f hmn x) := by
        exact hcoh n (codeTruncationInclusion f hmn x)
      simpa [codeTruncationInclusion, codeTruncationSuccInclusion] using h1.trans ih


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
The global candidate extracted from a coherent chain, using the stage indexed by
the code of the point itself.
-/
def coherentChainGlobalCandidate
    {T : Type} [LinearOrder T]
    (f : T → ℕ)
    (g : ∀ n, codeTruncation f n → ℝ) :
    T → ℝ :=
  fun t => g (f t) ⟨t, le_rfl⟩

/--
The global candidate agrees with any later stage, via the canonical inclusion.
-/
theorem coherentChainGlobalCandidate_eq_stage
    {T : Type} [LinearOrder T]
    (f : T → ℕ)
    {g : ∀ n, codeTruncation f n → ℝ}
    (hcoh : ∀ n (x : codeTruncation f n),
      g (n + 1) (codeTruncationSuccInclusion f n x) = g n x)
    {t : T} {n : ℕ}
    (htn : f t ≤ n) :
    coherentChainGlobalCandidate f g t =
      g n (codeTruncationInclusion f htn ⟨t, le_rfl⟩) := by
  unfold coherentChainGlobalCandidate
  symm
  exact coherent_on_all_inclusions f hcoh htn ⟨t, le_rfl⟩

/--
The global candidate extracted from a coherent chain is strictly increasing.
-/
theorem strictMono_coherentChainGlobalCandidate
    {T : Type} [LinearOrder T]
    (f : T → ℕ)
    {g : ∀ n, codeTruncation f n → ℝ}
    (hgmono : ∀ n, StrictMono (g n))
    (hcoh : ∀ n (x : codeTruncation f n),
      g (n + 1) (codeTruncationSuccInclusion f n x) = g n x) :
    StrictMono (coherentChainGlobalCandidate f g) := by
  intro a b hab
  let n := max (f a) (f b)
  have ha : f a ≤ n := le_max_left _ _
  have hb : f b ≤ n := le_max_right _ _
  have hlt_stage :
      g n (codeTruncationInclusion f ha ⟨a, le_rfl⟩) <
        g n (codeTruncationInclusion f hb ⟨b, le_rfl⟩) := by
    have hsub :
        codeTruncationInclusion f ha ⟨a, le_rfl⟩ <
          codeTruncationInclusion f hb ⟨b, le_rfl⟩ := by
      exact hab
    exact hgmono n hsub
  have hGa :
      coherentChainGlobalCandidate f g a =
        g n (codeTruncationInclusion f ha ⟨a, le_rfl⟩) := by
    exact coherentChainGlobalCandidate_eq_stage f hcoh ha
  have hGb :
      coherentChainGlobalCandidate f g b =
        g n (codeTruncationInclusion f hb ⟨b, le_rfl⟩) := by
    exact coherentChainGlobalCandidate_eq_stage f hcoh hb
  simpa [hGa, hGb] using hlt_stage


/--
The global candidate lands in the arctan interval if each finite stage does.
-/
theorem mapsIntoArctanIntervalOn_coherentChainGlobalCandidate
    {T : Type} [LinearOrder T]
    (f : T → ℕ)
    {g : ∀ n, codeTruncation f n → ℝ}
    (hgint : ∀ n, MapsIntoArctanIntervalOn (g n)) :
    MapsIntoArctanIntervalOn (coherentChainGlobalCandidate f g) := by
  intro t
  simpa [coherentChainGlobalCandidate] using hgint (f t) ⟨t, le_rfl⟩



/--
The `n`-th dyadic summand in the direct countable open-gap embedding.
-/
noncomputable def openGapSummand
    {T : Type} [LinearOrder T] [Countable T]
    (x : T) (n : ℕ) : NNReal := by
  classical
  letI : Encodable T := Encodable.ofCountable T
  exact match Encodable.decode (α := T) n with
  | none => 0
  | some t => if t < x then dyadicWeightNat n else 0

/--
If `n` does not decode to an element of `T`, then the corresponding summand is
zero.
-/
theorem openGapSummand_eq_zero_of_decode_none
    {T : Type} [LinearOrder T] [Countable T]
    (x : T) (n : ℕ)
    (h : @Encodable.decode T (Encodable.ofCountable T) n = none) :
    openGapSummand x n = 0 := by
  classical
  simp [openGapSummand, h]

/--
If `n` decodes to `t < x`, then the corresponding summand is the full dyadic
weight at `n`.
-/
theorem openGapSummand_eq_weight_of_decode_some_of_lt
    {T : Type} [LinearOrder T] [Countable T]
    (x t : T) (n : ℕ)
    (hDec : @Encodable.decode T (Encodable.ofCountable T) n = some t)
    (ht : t < x) :
    openGapSummand x n = dyadicWeightNat n := by
  classical
  simp [openGapSummand, hDec, ht]

/--
If `n` decodes to `t` but `t < x` fails, then the corresponding summand is
zero.
-/
theorem openGapSummand_eq_zero_of_decode_some_of_not_lt
    {T : Type} [LinearOrder T] [Countable T]
    (x t : T) (n : ℕ)
    (hDec : @Encodable.decode T (Encodable.ofCountable T) n = some t)
    (ht : ¬ t < x) :
    openGapSummand x n = 0 := by
  classical
  simp [openGapSummand, hDec, ht]

/--
Each dyadic summand is bounded above by the corresponding dyadic weight.
-/
theorem openGapSummand_le_weight
    {T : Type} [LinearOrder T] [Countable T]
    (x : T) (n : ℕ) :
    openGapSummand x n ≤ dyadicWeightNat n := by
  classical
  letI : Encodable T := Encodable.ofCountable T
  cases hDec : Encodable.decode (α := T) n with
  | none =>
      simp [openGapSummand, hDec]
  | some t =>
      by_cases hlt : t < x
      · simp [openGapSummand, hDec, hlt]
      · simp [openGapSummand, hDec, hlt]

/--
The summand family defining the direct countable open-gap embedding is
summable.
-/
theorem summable_openGapSummand
    {T : Type} [LinearOrder T] [Countable T]
    (x : T) :
    Summable (openGapSummand x) := by
  exact NNReal.summable_of_le
    (fun n => openGapSummand_le_weight x n)
    summable_dyadicWeightNat

/--
The direct dyadic embedding of a countable linear order into `ℝ`.
-/
noncomputable def openGapEmbedding
    {T : Type} [LinearOrder T] [Countable T] :
    T → ℝ :=
  fun x => ∑' n : ℕ, (openGapSummand x n : ℝ)

/--
If `x ≤ y`, then each dyadic summand for `x` is bounded above by the
corresponding summand for `y`.
-/
theorem openGapSummand_mono
    {T : Type} [LinearOrder T] [Countable T]
    {x y : T}
    (hxy : x ≤ y) :
    ∀ n : ℕ, openGapSummand x n ≤ openGapSummand y n := by
  intro n
  classical
  letI : Encodable T := Encodable.ofCountable T
  cases hDec : Encodable.decode (α := T) n with
  | none =>
      simp [openGapSummand, hDec]
  | some t =>
      by_cases htx : t < x
      · have hty : t < y := lt_of_lt_of_le htx hxy
        simp [openGapSummand, hDec, htx, hty]
      · by_cases hty : t < y
        · simp [openGapSummand, hDec, htx, hty]
        · simp [openGapSummand, hDec, htx, hty]

/--
At the code of `x`, the summand for `x` itself is zero.
-/
theorem openGapSummand_encode_self_eq_zero
    {T : Type} [LinearOrder T] [Countable T]
    (x : T) :
    openGapSummand x (@Encodable.encode T (Encodable.ofCountable T) x) = 0 := by
  classical
  unfold openGapSummand
  rw [Encodable.encodek (self := Encodable.ofCountable T) (a := x)]
  simp

/--
At the code of `x`, the summand for any strict upper point `y` is the full
dyadic weight.
-/
theorem openGapSummand_encode_of_lt
    {T : Type} [LinearOrder T] [Countable T]
    {x y : T}
    (hxy : x < y) :
    openGapSummand y (@Encodable.encode T (Encodable.ofCountable T) x) =
      dyadicWeightNat (@Encodable.encode T (Encodable.ofCountable T) x) := by
  classical
  unfold openGapSummand
  rw [Encodable.encodek (self := Encodable.ofCountable T) (a := x)]
  simp [hxy]

/--
At the code of `x`, the summand for `x` is strictly smaller than the summand
for any strict upper point `y`.
-/
theorem openGapSummand_encode_strict_of_lt
    {T : Type} [LinearOrder T] [Countable T]
    {x y : T}
    (hxy : x < y) :
    openGapSummand x (@Encodable.encode T (Encodable.ofCountable T) x) <
      openGapSummand y (@Encodable.encode T (Encodable.ofCountable T) x) := by
  classical
  rw [openGapSummand_encode_self_eq_zero x, openGapSummand_encode_of_lt hxy]
  exact dyadicWeightNat_pos _

/--
If `x < y`, then the direct dyadic embedding is strictly increasing at `x,y`.
-/
theorem openGapEmbedding_lt_of_lt
    {T : Type} [LinearOrder T] [Countable T]
    {x y : T}
    (hxy : x < y) :
    openGapEmbedding x < openGapEmbedding y := by
  classical
  -- pointwise monotonicity from `openGapSummand_mono`
  have hle :
      ∀ n : ℕ, (openGapSummand x n : ℝ) ≤ (openGapSummand y n : ℝ) := by
    intro n
    exact_mod_cast openGapSummand_mono (x := x) (y := y) (le_of_lt hxy) n
  -- strict inequality at the code of `x`
  have hlt :
      (openGapSummand x (@Encodable.encode T (Encodable.ofCountable T) x) : ℝ) <
      (openGapSummand y (@Encodable.encode T (Encodable.ofCountable T) x) : ℝ) := by
    exact_mod_cast openGapSummand_encode_strict_of_lt (x := x) (y := y) hxy
  -- now use the standard strict comparison theorem for nonnegative summable series
  -- with witness `Encodable.encode x`
  sorry

theorem strictMono_openGapEmbedding
    {T : Type} [LinearOrder T] [Countable T] :
    StrictMono (openGapEmbedding : T → ℝ) := by
  intro x y hxy
  exact openGapEmbedding_lt_of_lt hxy
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
  let G : T → ℝ := coherentChainGlobalCandidate f g
  have hGmono : StrictMono G := by
    exact strictMono_coherentChainGlobalCandidate f hgmono hcoh
  have hGint : MapsIntoArctanIntervalOn G := by
    exact mapsIntoArctanIntervalOn_coherentChainGlobalCandidate f hgint
  -- next: prove `HasOnlyOpenGaps (Set.range G)`
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
