import EcoLean.DebreauRepresentation.OpenGapLemmaSubtypeReduction
import EcoLean.DebreauRepresentation.OpenGapOrderVersion
import Mathlib.Data.Set.Countable
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Topology.Separation.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Encodable.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Order



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

theorem openGapEmbedding_lt_of_lt
    {T : Type} [LinearOrder T] [Countable T]
    {x y : T}
    (hxy : x < y) :
    openGapEmbedding x < openGapEmbedding y := by
  classical
  let i : ℕ := @Encodable.encode T (Encodable.ofCountable T) x
  have hle : ∀ n : ℕ, openGapSummand x n ≤ openGapSummand y n := by
    exact openGapSummand_mono (x := x) (y := y) (le_of_lt hxy)
  have hi : openGapSummand x i < openGapSummand y i := by
    simpa [i] using openGapSummand_encode_strict_of_lt (x := x) (y := y) hxy
  have hsy : Summable (openGapSummand y) := summable_openGapSummand y
  have hxy_tsum :
      (∑' n : ℕ, openGapSummand x n) < ∑' n : ℕ, openGapSummand y n := by
    exact NNReal.tsum_lt_tsum hle hi hsy
  rw [openGapEmbedding, openGapEmbedding]
  rw [← NNReal.coe_tsum, ← NNReal.coe_tsum]
  exact_mod_cast hxy_tsum
/--
The direct dyadic embedding is strictly increasing.
-/
theorem strictMono_openGapEmbedding
    {T : Type} [LinearOrder T] [Countable T] :
    StrictMono (openGapEmbedding : T → ℝ) := by
  intro x y hxy
  exact openGapEmbedding_lt_of_lt hxy

/--
Each direct dyadic embedding value is nonnegative.
-/
theorem openGapEmbedding_nonneg
    {T : Type} [LinearOrder T] [Countable T]
    (x : T) :
    0 ≤ openGapEmbedding x := by
  rw [openGapEmbedding]
  positivity


/--
The dyadic-weight series sums to `1` in `ℝ`.
-/
theorem tsum_dyadicWeightNat_real :
    (∑' n : ℕ, (dyadicWeightNat n : ℝ)) = 1 := by
  calc
    (∑' n : ℕ, (dyadicWeightNat n : ℝ))
        = ∑' n : ℕ, ((2 : ℝ)⁻¹ / 2 ^ n) := by
            apply tsum_congr
            intro n
            calc
              ((dyadicWeightNat n : NNReal) : ℝ)
                  = (((2 : ℝ) ^ (n + 1))⁻¹) := by
                      simp [dyadicWeightNat]
              _ = ((2 : ℝ)⁻¹ / 2 ^ n) := by
                      rw [pow_succ]
                      field_simp
    _ = 1 := by
        simpa using (tsum_geometric_two' (a := (1 : ℝ)))
/--
Each direct dyadic embedding value is bounded above by the dyadic-weight sum.
-/
theorem openGapEmbedding_le_tsum_dyadicWeight
    {T : Type} [LinearOrder T] [Countable T]
    (x : T) :
    openGapEmbedding x ≤ ∑' n : ℕ, (dyadicWeightNat n : ℝ) := by
  have hnn :
      (∑' n : ℕ, openGapSummand x n) ≤ ∑' n : ℕ, dyadicWeightNat n := by
    exact (summable_openGapSummand x).tsum_le_tsum
      (fun n => openGapSummand_le_weight x n)
      summable_dyadicWeightNat
  rw [openGapEmbedding, ← NNReal.coe_tsum, ← NNReal.coe_tsum]
  exact_mod_cast hnn
/--
The direct dyadic embedding lands in the arctan interval.
-/
theorem mapsIntoArctanIntervalOn_openGapEmbedding
    {T : Type} [LinearOrder T] [Countable T] :
    MapsIntoArctanIntervalOn (openGapEmbedding : T → ℝ) := by
  intro x
  constructor
  · have hx : 0 ≤ openGapEmbedding x := openGapEmbedding_nonneg x
    have hpi : 0 < Real.pi / 2 := by positivity
    linarith
  · have hx :
      openGapEmbedding x ≤ ∑' n : ℕ, (dyadicWeightNat n : ℝ) :=
        openGapEmbedding_le_tsum_dyadicWeight x
    have hsum : (∑' n : ℕ, (dyadicWeightNat n : ℝ)) = 1 :=
      tsum_dyadicWeightNat_real
    have hpi : (1 : ℝ) < Real.pi / 2 := by
      nlinarith [Real.pi_gt_three]
    rw [hsum] at hx
    linarith

/--
The dyadic tail after `N` is the sum of all dyadic weights with index strictly
greater than `N`.
-/
noncomputable def dyadicTail (N : ℕ) : ℝ :=
  ∑' n : ℕ, if N < n then (dyadicWeightNat n : ℝ) else 0

/--
The dyadic tail is nonnegative.
-/
theorem dyadicTail_nonneg (N : ℕ) :
    0 ≤ dyadicTail N := by
  unfold dyadicTail
  positivity

/--
Expanding the dyadic tail as a series of nonnegative terms.
-/
theorem dyadicTail_def (N : ℕ) :
    dyadicTail N = ∑' n : ℕ, if N < n then (dyadicWeightNat n : ℝ) else 0 := by
  rfl

/--
The dyadic tail after `N` is the geometric tail starting at `N+1`.
-/
theorem dyadicTail_eq_tsum_from_succ (N : ℕ) :
    dyadicTail N = ∑' n : ℕ, (dyadicWeightNat (n + (N + 1)) : ℝ) := by
  unfold dyadicTail
  sorry
/--
The dyadic tail can be made arbitrarily small.
-/
theorem exists_dyadicTail_lt
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N : ℕ, dyadicTail N < ε := by
  sorry

/--
If `x < y` and there is no point strictly between them, then their images under
the direct dyadic embedding form an open gap in the image set.
-/
theorem isOpenGap_range_openGapEmbedding_of_noMiddlePoint
    {T : Type} [LinearOrder T] [Countable T]
    {x y : T}
    (hxy : x < y)
    (hNoMid : NoMiddlePoint x y) :
    IsOpenGap (Set.range (openGapEmbedding : T → ℝ))
      (openGapEmbedding x) (openGapEmbedding y) := by
  have hg : StrictMono (openGapEmbedding : T → ℝ) := strictMono_openGapEmbedding
  have hxmem : openGapEmbedding x ∈ Set.range (openGapEmbedding : T → ℝ) := ⟨x, rfl⟩
  have hymem : openGapEmbedding y ∈ Set.range (openGapEmbedding : T → ℝ) := ⟨y, rfl⟩
  refine ⟨?_, hxmem, hymem⟩
  refine ⟨hg hxy, subset_closure hxmem, subset_closure hymem, ?_⟩
  intro c hxc hcy hc
  rcases hc with ⟨z, rfl⟩
  have hxz : x < z := (hg.lt_iff_lt).mp hxc
  have hzy : z < y := (hg.lt_iff_lt).mp hcy
  exact hNoMid ⟨z, hxz, hzy⟩

/--
The direct dyadic embedding is domain-gap-compatible.
-/
theorem domainGapCompatible_openGapEmbedding
    {T : Type} [LinearOrder T] [Countable T] :
    DomainGapCompatible (openGapEmbedding : T → ℝ) := by
  intro x y hxy hNoMid
  exact isOpenGap_range_openGapEmbedding_of_noMiddlePoint hxy hNoMid

/--
If `(a,b)` is a gap of `S`, then any sufficiently small neighbourhood of `a`
contains a point of `S` lying on or to the left of `a`.
-/
theorem exists_mem_left_of_gap_closure
    {S : Set ℝ} {a b ε : ℝ}
    (hGap : IsGap S a b)
    (hε0 : 0 < ε)
    (hε : ε < b - a) :
    ∃ s ∈ S, a - ε < s ∧ s ≤ a := by
  rcases hGap with ⟨hab, ha_cl, hb_cl, hNoMid⟩
  rcases Metric.mem_closure_iff.1 ha_cl ε hε0 with ⟨s, hsS, hdist⟩
  have hAbs : |s - a| < ε := by
    simpa [Real.dist_eq, abs_sub_comm] using hdist
  have hs_left : a - ε < s := by
    have h1 : -ε < s - a := (abs_lt.mp hAbs).1
    linarith
  have hs_right : s < a + ε := by
    have h2 : s - a < ε := (abs_lt.mp hAbs).2
    linarith
  have hsle : s ≤ a := by
    by_contra hsa
    have hsa' : a < s := lt_of_not_ge hsa
    have hsb : s < b := by
      linarith
    exact hNoMid s hsa' hsb hsS
  exact ⟨s, hsS, hs_left, hsle⟩

/--
If `(a,b)` is a gap of `S`, then any sufficiently small neighbourhood of `b`
contains a point of `S` lying on or to the right of `b`.
-/
theorem exists_mem_right_of_gap_closure
    {S : Set ℝ} {a b ε : ℝ}
    (hGap : IsGap S a b)
    (hε0 : 0 < ε)
    (hε : ε < b - a) :
    ∃ s ∈ S, b ≤ s ∧ s < b + ε := by
  rcases hGap with ⟨hab, ha_cl, hb_cl, hNoMid⟩
  rcases Metric.mem_closure_iff.1 hb_cl ε hε0 with ⟨s, hsS, hdist⟩
  have hAbs : |s - b| < ε := by
    simpa [Real.dist_eq, abs_sub_comm] using hdist
  have hs_left : b - ε < s := by
    have h1 : -ε < s - b := (abs_lt.mp hAbs).1
    linarith
  have hs_right : s < b + ε := by
    have h2 : s - b < ε := (abs_lt.mp hAbs).2
    linarith
  have hble : b ≤ s := by
    by_contra hsb
    have hsb' : s < b := lt_of_not_ge hsb
    have has : a < s := by
      linarith
    exact hNoMid s has hsb' hsS
  exact ⟨s, hsS, hble, hs_right⟩

/--
If an open gap `(u,v)` lies sufficiently tightly around a gap `(a,b)`, then
the endpoints must agree.
-/
theorem eq_endpoints_of_openGap_squeezing_gap
    {S : Set ℝ} {a b u v ε : ℝ}
    (hGap : IsGap S a b)
    (hOpen : IsOpenGap S u v)
    (hε0 : 0 < ε)
    (hε : ε < b - a)
    (hu : a - ε < u ∧ u ≤ a)
    (hv : b ≤ v ∧ v < b + ε) :
    u = a ∧ v = b := by
  rcases hGap with ⟨hab, ha_cl, hb_cl, hNoMid⟩
  rcases hOpen with ⟨⟨huv, hu_cl, hv_cl, hNoMid'⟩, huS, hvS⟩
  constructor
  · by_cases hEq : u = a
    · exact hEq
    · have hu_lt_a : u < a := lt_of_le_of_ne hu.2 hEq
      let ε' : ℝ := a - u
      have hε'0 : 0 < ε' := sub_pos.mpr hu_lt_a
      have hε' : ε' < b - a := by
        have : a - u < ε := by
          linarith
        linarith
      rcases exists_mem_left_of_gap_closure
          (S := S) (a := a) (b := b) (ε := ε')
          ⟨hab, ha_cl, hb_cl, hNoMid⟩ hε'0 hε' with
        ⟨s, hsS, hs_left, hs_le⟩
      have hus : u < s := by
        dsimp [ε'] at hs_left
        linarith
      have hsv : s < v := by
        have : a < v := by
          linarith [hab, hv.1]
        linarith
      exact False.elim (hNoMid' s hus hsv hsS)
  · by_cases hEq : v = b
    · exact hEq
    · have hneq : b ≠ v := by
        intro h
        exact hEq h.symm
      have hb_lt_v : b < v := lt_of_le_of_ne hv.1 hneq
      let ε' : ℝ := v - b
      have hε'0 : 0 < ε' := sub_pos.mpr hb_lt_v
      have hε' : ε' < b - a := by
        have : v - b < ε := by
          linarith
        linarith
      rcases exists_mem_right_of_gap_closure
          (S := S) (a := a) (b := b) (ε := ε')
          ⟨hab, ha_cl, hb_cl, hNoMid⟩ hε'0 hε' with
        ⟨s, hsS, hs_ge, hs_right⟩
      have hus : u < s := by
        have : u < b := by
          linarith [hu.2, hab]
        linarith
      have hsv : s < v := by
        dsimp [ε'] at hs_right
        linarith
      exact False.elim (hNoMid' s hus hsv hsS)


/--
If `(a,b)` is a gap in the range of the direct dyadic embedding, then for every
small enough `ε` there are domain points whose images lie just to the left of
`a` and just to the right of `b`.
-/
theorem exists_domain_points_near_gap_endpoints
    {T : Type} [LinearOrder T] [Countable T]
    {a b ε : ℝ}
    (hGap : IsGap (Set.range (openGapEmbedding : T → ℝ)) a b)
    (hε0 : 0 < ε)
    (hε : ε < b - a) :
    ∃ x y : T,
      a - ε < openGapEmbedding x ∧
      openGapEmbedding x ≤ a ∧
      b ≤ openGapEmbedding y ∧
      openGapEmbedding y < b + ε := by
  rcases exists_mem_left_of_gap_closure hGap hε0 hε with
    ⟨s, hsS, hs_left, hs_le⟩
  rcases exists_mem_right_of_gap_closure hGap hε0 hε with
    ⟨t, htS, ht_ge, ht_right⟩
  rcases hsS with ⟨x, rfl⟩
  rcases htS with ⟨y, rfl⟩
  exact ⟨x, y, hs_left, hs_le, ht_ge, ht_right⟩

/--
The approximating domain points near the endpoints of a gap are ordered.
-/
theorem exists_ordered_domain_points_near_gap_endpoints
    {T : Type} [LinearOrder T] [Countable T]
    {a b ε : ℝ}
    (hGap : IsGap (Set.range (openGapEmbedding : T → ℝ)) a b)
    (hε0 : 0 < ε)
    (hε : ε < b - a) :
    ∃ x y : T,
      x < y ∧
      a - ε < openGapEmbedding x ∧
      openGapEmbedding x ≤ a ∧
      b ≤ openGapEmbedding y ∧
      openGapEmbedding y < b + ε := by
  rcases exists_domain_points_near_gap_endpoints hGap hε0 hε with
    ⟨x, y, hx_left, hx_le, hy_ge, hy_right⟩
  have hGapAB : a < b := hGap.1
  have hxy_img : openGapEmbedding x < openGapEmbedding y := by
    linarith
  have hxy : x < y := by
    by_contra hnot
    have hyx : y ≤ x := le_of_not_gt hnot
    have hmono := (strictMono_openGapEmbedding : StrictMono (openGapEmbedding : T → ℝ)).monotone
    have : openGapEmbedding y ≤ openGapEmbedding x := hmono hyx
    exact not_le_of_gt hxy_img this
  exact ⟨x, y, hxy, hx_left, hx_le, hy_ge, hy_right⟩

/--
If a pair `x < y` squeezes a gap and there is a middle point `z`, then one can
refine the squeezing pair to either `(z,y)` or `(x,z)`.
-/
theorem refine_squeezing_pair_at_middle
    {T : Type} [LinearOrder T] [Countable T]
    {a b ε : ℝ}
    (hGap : IsGap (Set.range (openGapEmbedding : T → ℝ)) a b)
    {x y z : T}
    (hxy : x < y)
    (hxz : x < z)
    (hzy : z < y)
    (hx₁ : a - ε < openGapEmbedding x)
    (hx₂ : openGapEmbedding x ≤ a)
    (hy₁ : b ≤ openGapEmbedding y)
    (hy₂ : openGapEmbedding y < b + ε) :
    (a - ε < openGapEmbedding z ∧
      openGapEmbedding z ≤ a ∧
      b ≤ openGapEmbedding y ∧
      openGapEmbedding y < b + ε) ∨
    (a - ε < openGapEmbedding x ∧
      openGapEmbedding x ≤ a ∧
      b ≤ openGapEmbedding z ∧
      openGapEmbedding z < b + ε) := by
  have hg : StrictMono (openGapEmbedding : T → ℝ) := strictMono_openGapEmbedding
  have hxz_img : openGapEmbedding x < openGapEmbedding z := hg hxz
  have hzy_img : openGapEmbedding z < openGapEmbedding y := hg hzy
  by_cases hz_left : openGapEmbedding z ≤ a
  · left
    refine ⟨?_, hz_left, hy₁, hy₂⟩
    linarith
  · right
    have hz_right : b ≤ openGapEmbedding z := by
      by_contra hz_not
      have hza : a < openGapEmbedding z := lt_of_not_ge hz_left
      have hzb : openGapEmbedding z < b := lt_of_not_ge hz_not
      exact hGap.2.2.2 (openGapEmbedding z) hza hzb ⟨z, rfl⟩
    refine ⟨hx₁, hx₂, hz_right, ?_⟩
    linarith

/--
If a gap of the range can be squeezed by an adjacent domain pair, then it is
already an open gap.
-/
theorem isOpenGap_of_exists_adjacent_domain_points_squeezing_gap
    {T : Type} [LinearOrder T] [Countable T]
    {a b ε : ℝ}
    (hGap : IsGap (Set.range (openGapEmbedding : T → ℝ)) a b)
    (hε0 : 0 < ε)
    (hε : ε < b - a)
    {x y : T}
    (hxy : x < y)
    (hNoMid : NoMiddlePoint x y)
    (hx₁ : a - ε < openGapEmbedding x)
    (hx₂ : openGapEmbedding x ≤ a)
    (hy₁ : b ≤ openGapEmbedding y)
    (hy₂ : openGapEmbedding y < b + ε) :
    IsOpenGap (Set.range (openGapEmbedding : T → ℝ)) a b := by
  have hOpenXY :
      IsOpenGap (Set.range (openGapEmbedding : T → ℝ))
        (openGapEmbedding x) (openGapEmbedding y) := by
    exact isOpenGap_range_openGapEmbedding_of_noMiddlePoint hxy hNoMid
  have hEq :
      openGapEmbedding x = a ∧ openGapEmbedding y = b := by
    exact eq_endpoints_of_openGap_squeezing_gap
      (S := Set.range (openGapEmbedding : T → ℝ))
      hGap hOpenXY hε0 hε ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
  rcases hEq with ⟨hx, hy⟩
  symm at hx
  symm at hy
  subst a
  subst b
  simpa using hOpenXY

/--
If `(a,b)` is a gap in the range of the direct dyadic embedding, then every
domain point lies either on the left of `a` or on the right of `b`.
-/
theorem le_left_or_right_le_of_gap_range_openGapEmbedding
    {T : Type} [LinearOrder T] [Countable T]
    {a b : ℝ}
    (hGap : IsGap (Set.range (openGapEmbedding : T → ℝ)) a b)
    (z : T) :
    openGapEmbedding z ≤ a ∨ b ≤ openGapEmbedding z := by
  by_cases hz : openGapEmbedding z ≤ a
  · exact Or.inl hz
  · right
    by_contra hzb
    have h1 : a < openGapEmbedding z := lt_of_not_ge hz
    have h2 : openGapEmbedding z < b := lt_of_not_ge hzb
    exact hGap.2.2.2 (openGapEmbedding z) h1 h2 ⟨z, rfl⟩

/--
The left side of a gap in the range of the direct dyadic embedding is downward
closed in the domain order.
-/
theorem gap_left_side_downward_closed
    {T : Type} [LinearOrder T] [Countable T]
    {a b : ℝ}
    (hGap : IsGap (Set.range (openGapEmbedding : T → ℝ)) a b)
    {x y : T}
    (hxy : x ≤ y)
    (hy : openGapEmbedding y ≤ a) :
    openGapEmbedding x ≤ a := by
  have hmono := (strictMono_openGapEmbedding : StrictMono (openGapEmbedding : T → ℝ)).monotone
  exact le_trans (hmono hxy) hy

/--
The right side of a gap in the range of the direct dyadic embedding is upward
closed in the domain order.
-/
theorem gap_right_side_upward_closed
    {T : Type} [LinearOrder T] [Countable T]
    {a b : ℝ}
    (hGap : IsGap (Set.range (openGapEmbedding : T → ℝ)) a b)
    {x y : T}
    (hxy : x ≤ y)
    (hx : b ≤ openGapEmbedding x) :
    b ≤ openGapEmbedding y := by
  have hmono := (strictMono_openGapEmbedding : StrictMono (openGapEmbedding : T → ℝ)).monotone
  exact le_trans hx (hmono hxy)

/--
The left and right sides determined by a gap form a cut on the domain.
-/
theorem gap_range_openGapEmbedding_cut
    {T : Type} [LinearOrder T] [Countable T]
    {a b : ℝ}
    (hGap : IsGap (Set.range (openGapEmbedding : T → ℝ)) a b) :
    ∀ z : T, openGapEmbedding z ≤ a ∨ b ≤ openGapEmbedding z := by
  intro z
  exact le_left_or_right_le_of_gap_range_openGapEmbedding hGap z

/--
The range of the direct dyadic embedding has only open gaps.
-/
theorem hasOnlyOpenGaps_range_openGapEmbedding
    {T : Type} [LinearOrder T] [Countable T] :
    HasOnlyOpenGaps (Set.range (openGapEmbedding : T → ℝ)) := by
  sorry

/--
Order-version open gap lemma.

This is the main remaining theorem.
-/
theorem countableOpenGapLemmaOnOrders_proof :
    CountableOpenGapLemmaOnOrders := by
  intro T _ _
  refine ⟨openGapEmbedding, ?_, ?_, ?_⟩
  · exact strictMono_openGapEmbedding
  · exact mapsIntoArctanIntervalOn_openGapEmbedding
  · exact hasOnlyOpenGaps_range_openGapEmbedding
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
