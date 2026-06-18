import EcoLean.SocialChoiceTheory.Arrow
import Mathlib.Order.Filter.Ultrafilter.Basic

open Finset
open scoped Classical

namespace EcoLean.SocialChoiceTheory

/-!
# Arrow's impossibility theorem via ultrafilters

This file gives a second, independent proof of Arrow's theorem (`arrow` proves it by the pivotal-voter
route), following the Kirman–Sondermann analysis as presented by Vasey.

The proof strategy is the ultrafilter route:

1. Define when a coalition of voters is *decisive*, and prove the contagion lemma `fieldExpansion`:
   weak decisiveness on one pair spreads to decisiveness on every pair (using weak Pareto, IIA, and a
   third alternative; hence `3 ≤ X.card`).
2. Show the decisive coalitions form an ultrafilter: they contain `univ`, exclude `∅`, are upward
   closed, are closed under intersection, and satisfy the dichotomy `G` or `Gᶜ` decisive.
   Intersection-closure follows Vasey, by collapsing a three-block partition into a three-voter
   *quotient* system and settling it with the base case (`base_fin3`).
3. Conclude: on a finite voter set an ultrafilter is principal, and its generator is a dictator.

The development reuses `Preference`, `Profile`, `SocialWelfareFunction`, `ParetoOn`, `IIAOn`,
`DictatorialOn`, and the order gadgets `maketop`/`makebot`/`makeabove` from `Basic.lean`/`Arrow.lean`,
and Mathlib's `Ultrafilter` API. It is logically independent of the pivotal argument.
-/

variable {σ ι : Type*} [DecidableEq σ]

/-! ### Score-based preferences

A score `s : σ → ℕ` induces the complete transitive weak preference `x ≽ y ↔ s y ≤ s x`
(`prefOfScore`), whose strict part is the strict inequality of scores. This supplies cheap explicit
profiles in which designated alternatives are ranked in a prescribed strict order. -/

def prefOfScore (s : σ → ℕ) : Preference σ :=
  Preference.ofPrefOrder
    { rel := fun x y => s y ≤ s x
      refl := fun x => le_refl (s x)
      total := fun x y => le_total (s y) (s x)
      trans := @fun _ _ _ h₁ h₂ => le_trans h₂ h₁ }

omit [DecidableEq σ] in
@[simp] lemma weakPref_prefOfScore (s : σ → ℕ) (x y : σ) :
    (prefOfScore s) x y ↔ s y ≤ s x := by
  simp [prefOfScore]

omit [DecidableEq σ] in
@[simp] lemma strictPref_prefOfScore (s : σ → ℕ) (x y : σ) :
    StrictPref (prefOfScore s) x y ↔ s y < s x := by
  simp only [StrictPref, weakPref_prefOfScore]
  omega

/-! ### Strict ∘ weak transitivity

`strictPref_trans` (in `Basic.lean`) composes two strict preferences; here is the variant composing a
strict preference with a weak one on the right, used in the dichotomy lemma. -/

omit [DecidableEq σ] in
lemma strictPref_weak_right {R : σ → σ → Prop}
    (htrans : ∀ ⦃x y z : σ⦄, R x y → R y z → R x z)
    {x y z : σ} (h1 : StrictPref R x y) (h2 : R y z) :
    StrictPref R x z := by
  refine ⟨htrans h1.1 h2, ?_⟩
  intro hzx
  exact h1.2 (htrans h2 hzx)

/-! ### A three-level ranking

`rank3 a b c` ranks `a ≻ b ≻ c` with every other alternative tied at the bottom; only the order among
`a`, `b`, `c` is used. It builds the fixed comparison profiles of the later constructions, whose three
strict comparisons are `rank3_fst_snd`, `rank3_fst_thd`, `rank3_snd_thd`. -/

def rank3 (a b c : σ) : Preference σ :=
  prefOfScore (fun x => if x = a then 3 else if x = b then 2 else if x = c then 1 else 0)

lemma rank3_fst_snd {a b c : σ} (hab : a ≠ b) : StrictPref (rank3 a b c) a b := by
  rw [rank3, strictPref_prefOfScore]
  show (if b = a then 3 else if b = b then 2 else if b = c then 1 else 0)
      < (if a = a then 3 else if a = b then 2 else if a = c then 1 else 0)
  rw [if_neg (Ne.symm hab), if_pos rfl, if_pos rfl]; omega

lemma rank3_fst_thd {a b c : σ} (hac : a ≠ c) (hbc : b ≠ c) :
    StrictPref (rank3 a b c) a c := by
  rw [rank3, strictPref_prefOfScore]
  show (if c = a then 3 else if c = b then 2 else if c = c then 1 else 0)
      < (if a = a then 3 else if a = b then 2 else if a = c then 1 else 0)
  rw [if_neg (Ne.symm hac), if_neg (Ne.symm hbc), if_pos rfl, if_pos rfl]; omega

lemma rank3_snd_thd {a b c : σ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    StrictPref (rank3 a b c) b c := by
  rw [rank3, strictPref_prefOfScore]
  show (if c = a then 3 else if c = b then 2 else if c = c then 1 else 0)
      < (if b = a then 3 else if b = b then 2 else if b = c then 1 else 0)
  rw [if_neg (Ne.symm hac), if_neg (Ne.symm hbc), if_pos rfl, if_neg (Ne.symm hab), if_pos rfl]; omega

/-! ### Decisive coalitions

A coalition `G ⊆ ι` of voters is:

* `Decisive f G a b` if whenever every voter in `G` strictly prefers `a` to `b`, society does too
  (regardless of the voters outside `G`);
* `WeaklyDecisive f G a b` if society ranks `a ≻ b` at least when `G` ranks `a ≻ b` and everyone
  outside `G` ranks `b ≻ a`;
* `IsDecisiveCoalition f X G` if it is decisive for every ordered pair of distinct alternatives of `X`.

A decisive pair is weakly decisive (`Decisive.weaklyDecisive`), and decisiveness is monotone in the
coalition (`decisive_mono`). -/

def Decisive (f : SocialWelfareFunction ι σ) (G : Set ι) (a b : σ) : Prop :=
  ∀ P : Profile ι σ, (∀ i ∈ G, StrictPref (P i) a b) → StrictPref (f P) a b

def WeaklyDecisive (f : SocialWelfareFunction ι σ) (G : Set ι) (a b : σ) : Prop :=
  ∀ P : Profile ι σ, (∀ i ∈ G, StrictPref (P i) a b) → (∀ i ∉ G, StrictPref (P i) b a) →
    StrictPref (f P) a b

def IsDecisiveCoalition (f : SocialWelfareFunction ι σ) (X : Finset σ) (G : Set ι) : Prop :=
  ∀ a b : σ, a ∈ X → b ∈ X → a ≠ b → Decisive f G a b

variable {f : SocialWelfareFunction ι σ} {X : Finset σ}

omit [DecidableEq σ] in
theorem Decisive.weaklyDecisive {G : Set ι} {a b : σ} (h : Decisive f G a b) :
    WeaklyDecisive f G a b :=
  fun P hG _ => h P hG

omit [DecidableEq σ] in
theorem decisive_mono {G H : Set ι} (hsub : G ⊆ H) (h : IsDecisiveCoalition f X G) :
    IsDecisiveCoalition f X H :=
  fun a b ha hb hne P hyp => h a b ha hb hne P (fun i hiG => hyp i (hsub hiG))

/-! ### Field expansion

Weak decisiveness on one pair spreads to full decisiveness on every pair. The constructions reposition
the intermediate alternative voter-by-voter with `makeabove`/`maketop`/`makebot`, leaving the target
pair untouched, then transport the social verdict back with IIA — the standard profile-modification
and IIA-transport technique.

* `fe_expand_right`: weak decisiveness for `(α, β)` gives decisiveness for `(α, γ)` — place `β` just
  below `α` for `G` and on top for the rest, so weak decisiveness gives `α ≻ β`, Pareto gives `β ≻ γ`,
  and transitivity `α ≻ γ`.
* `fe_expand_left`: the mirror image, giving decisiveness for `(γ, β)`.
* `fieldExpansion`: chaining these through third alternatives, weak decisiveness for a single pair
  makes `G` a full decisive coalition. -/

theorem fe_expand_right (hPareto : ParetoOn f X) (hIIA : IIAOn f X)
    {G : Set ι} {α β γ : σ} (hα : α ∈ X) (hβ : β ∈ X) (hγ : γ ∈ X)
    (hαβ : α ≠ β) (hβγ : β ≠ γ)
    (hwd : WeaklyDecisive f G α β) : Decisive f G α γ := by
  classical
  intro P hP
  let P' : Profile ι σ := fun i => if i ∈ G then makeabove (P i) γ β else maketop (P i) β
  have hG : ∀ i, i ∈ G → P' i = makeabove (P i) γ β := fun i hi => if_pos hi
  have hNG : ∀ i, i ∉ G → P' i = maketop (P i) β := fun i hi => if_neg hi
  -- society ranks `α ≻ β` by weak decisiveness of `G`
  have hsoc_αβ : StrictPref (f P') α β := by
    apply hwd P'
    · intro i hi
      rw [hG i hi]
      exact makeabove_below hαβ (hP i hi).2
    · intro i hi
      rw [hNG i hi]
      exact is_strictlyBest_maketop β (P i) X α hα hαβ
  -- everyone ranks `β ≻ γ`, so society does by Pareto
  have hsoc_βγ : StrictPref (f P') β γ := by
    apply hPareto β γ hβ hγ P'
    intro i
    show StrictPref (P' i) β γ
    by_cases hi : i ∈ G
    · rw [hG i hi]; exact makeabove_above (P i) hβγ.symm
    · rw [hNG i hi]; exact is_strictlyBest_maketop β (P i) X γ hγ hβγ.symm
  have hsoc_αγ : StrictPref (f P') α γ := strictPref_trans (f P').trans hsoc_αβ hsoc_βγ
  -- `P` and `P'` agree on the pair `(α, γ)`, which never involves `β`
  have hagree : PairwiseAgreesOn P P' α γ := by
    intro i
    by_cases hi : i ∈ G
    · rw [hG i hi]
      obtain ⟨h1, h2⟩ := makeabove_noteq (P i) γ (b := β) (c := α) (d := γ) hαβ hβγ.symm
      obtain ⟨h3, h4⟩ := makeabove_noteq' (P i) γ (b := β) (c := α) (d := γ) hαβ hβγ.symm
      exact ⟨⟨h1.symm, h2.symm⟩, h3.symm, h4.symm⟩
    · rw [hNG i hi]
      obtain ⟨h1, h2⟩ := maketop_noteq (P i) (a := α) (c := γ) hαβ hβγ.symm
      obtain ⟨h3, h4⟩ := maketop_noteq' (P i) (a := α) (c := γ) hαβ hβγ.symm
      exact ⟨⟨h1.symm, h2.symm⟩, h3.symm, h4.symm⟩
  exact ((hIIA P P' α γ hα hγ hagree).2.1).mpr hsoc_αγ

theorem fe_expand_left (hPareto : ParetoOn f X) (hIIA : IIAOn f X)
    {G : Set ι} {α β γ : σ} (hα : α ∈ X) (hβ : β ∈ X) (hγ : γ ∈ X)
    (hαβ : α ≠ β) (hαγ : α ≠ γ)
    (hwd : WeaklyDecisive f G α β) : Decisive f G γ β := by
  classical
  intro P hP
  let P' : Profile ι σ := fun i => if i ∈ G then makeabove (P i) β α else makebot (P i) α
  have hG : ∀ i, i ∈ G → P' i = makeabove (P i) β α := fun i hi => if_pos hi
  have hNG : ∀ i, i ∉ G → P' i = makebot (P i) α := fun i hi => if_neg hi
  -- everyone ranks `γ ≻ α`, so society does by Pareto
  have hsoc_γα : StrictPref (f P') γ α := by
    apply hPareto γ α hγ hα P'
    intro i
    show StrictPref (P' i) γ α
    by_cases hi : i ∈ G
    · rw [hG i hi]; exact makeabove_below hαγ.symm (hP i hi).2
    · rw [hNG i hi]; exact is_strictlyWorst_makebot α (P i) X γ hγ hαγ.symm
  -- society ranks `α ≻ β` by weak decisiveness of `G`
  have hsoc_αβ : StrictPref (f P') α β := by
    apply hwd P'
    · intro i hi
      rw [hG i hi]; exact makeabove_above (P i) hαβ.symm
    · intro i hi
      rw [hNG i hi]; exact is_strictlyWorst_makebot α (P i) X β hβ hαβ.symm
  have hsoc_γβ : StrictPref (f P') γ β := strictPref_trans (f P').trans hsoc_γα hsoc_αβ
  -- `P` and `P'` agree on the pair `(γ, β)`, which never involves `α`
  have hagree : PairwiseAgreesOn P P' γ β := by
    intro i
    by_cases hi : i ∈ G
    · rw [hG i hi]
      obtain ⟨h1, h2⟩ := makeabove_noteq (P i) β (b := α) (c := γ) (d := β) hαγ.symm hαβ.symm
      obtain ⟨h3, h4⟩ := makeabove_noteq' (P i) β (b := α) (c := γ) (d := β) hαγ.symm hαβ.symm
      exact ⟨⟨h1.symm, h2.symm⟩, h3.symm, h4.symm⟩
    · rw [hNG i hi]
      obtain ⟨h1, h2⟩ := makebot_noteq (P i) (a := γ) (c := β) hαγ.symm hαβ.symm
      obtain ⟨h3, h4⟩ := makebot_noteq' (P i) (a := γ) (c := β) hαγ.symm hαβ.symm
      exact ⟨⟨h1.symm, h2.symm⟩, h3.symm, h4.symm⟩
  exact ((hIIA P P' γ β hγ hβ hagree).2.1).mpr hsoc_γβ

theorem fieldExpansion (hPareto : ParetoOn f X) (hIIA : IIAOn f X) (hX : 3 ≤ X.card)
    {G : Set ι} {a b : σ} (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b)
    (hwd : WeaklyDecisive f G a b) : IsDecisiveCoalition f X G := by
  -- `a` beats every other alternative
  have hI : ∀ y, y ∈ X → y ≠ a → Decisive f G a y := by
    intro y hy hya
    by_cases hyb : y = b
    · subst hyb
      obtain ⟨e, he, hea, heb⟩ := Finset.existsThirdDistinctMem hX ha hb hab
      have d_ae : Decisive f G a e :=
        fe_expand_right hPareto hIIA ha hb he hab (Ne.symm heb) hwd
      exact fe_expand_right hPareto hIIA ha he hb (Ne.symm hea) heb d_ae.weaklyDecisive
    · exact fe_expand_right hPareto hIIA ha hb hy hab (Ne.symm hyb) hwd
  intro p q hp hq hpq
  by_cases hpa : p = a
  · subst hpa
    exact hI q hq (Ne.symm hpq)
  · by_cases hqa : q = a
    · rw [hqa]
      obtain ⟨e, he, hea, hep⟩ := Finset.existsThirdDistinctMem hX ha hp (Ne.symm hpa)
      have d_ae : Decisive f G a e := hI e he hea
      have d_pe : Decisive f G p e :=
        fe_expand_left hPareto hIIA ha he hp (Ne.symm hea) (Ne.symm hpa) d_ae.weaklyDecisive
      exact fe_expand_right hPareto hIIA hp he ha (Ne.symm hep) hea d_pe.weaklyDecisive
    · have d_aq : Decisive f G a q := hI q hq hqa
      exact fe_expand_left hPareto hIIA ha hq hp (Ne.symm hqa) (Ne.symm hpa) d_aq.weaklyDecisive

/-! ### Filter and ultrafilter axioms

The grand coalition is decisive (`univ_decisive`, weak Pareto) and the empty one is not
(`empty_not_decisive`); two decisive coalitions cannot be disjoint (`decisive_not_disjoint`); and for
every coalition either it or its complement is decisive (`decisive_dichotomy`). The dichotomy reads the
social verdict off a fixed `rank3` profile — `G` ranks `a ≻ b ≻ c`, `Gᶜ` ranks `b ≻ c ≻ a`, so Pareto
forces `b ≻ c`; whichever of `a ≻ c` or `c ≽ a` holds makes `G` or `Gᶜ` weakly decisive — and upgrades
it with `fieldExpansion`. With monotonicity and intersection-closure (proved next), these are the
ultrafilter axioms. -/

omit [DecidableEq σ] in
theorem univ_decisive (hPareto : ParetoOn f X) : IsDecisiveCoalition f X Set.univ := by
  intro a b ha hb _ P hP
  apply hPareto a b ha hb P
  intro i
  show StrictPref (P i) a b
  exact hP i (Set.mem_univ i)

theorem empty_not_decisive (hPareto : ParetoOn f X) (hX : 3 ≤ X.card) :
    ¬ IsDecisiveCoalition f X (∅ : Set ι) := by
  intro h
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < X.card by omega)
  obtain ⟨b, hb, hba⟩ := Finset.existsSecondDistinctMem (show 2 ≤ X.card by omega) ha
  let P : Profile ι σ := fun _ => makebot (prefOfScore (fun _ => 0)) a
  have hsoc_ab : StrictPref (f P) a b :=
    h a b ha hb (Ne.symm hba) P (fun i hi => absurd hi (Set.notMem_empty i))
  have hsoc_ba : StrictPref (f P) b a := by
    apply hPareto b a hb ha P
    intro i
    show StrictPref (P i) b a
    exact is_strictlyWorst_makebot a (prefOfScore (fun _ => 0)) X b hb hba
  exact (not_strictPref_of_reverse hsoc_ab) hsoc_ba

theorem decisive_dichotomy (hPareto : ParetoOn f X) (hIIA : IIAOn f X) (hX : 3 ≤ X.card)
    (G : Set ι) : IsDecisiveCoalition f X G ∨ IsDecisiveCoalition f X Gᶜ := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < X.card by omega)
  obtain ⟨b, hb, hba⟩ := Finset.existsSecondDistinctMem (show 2 ≤ X.card by omega) ha
  obtain ⟨c, hc, hca, hcb⟩ := Finset.existsThirdDistinctMem hX ha hb (Ne.symm hba)
  let P : Profile ι σ := fun i => if i ∈ G then rank3 a b c else rank3 b c a
  have hPval : ∀ i, P i = (if i ∈ G then rank3 a b c else rank3 b c a) := fun _ => rfl
  have hPbc : StrictPref (f P) b c := by
    apply hPareto b c hb hc P
    intro i
    show StrictPref (P i) b c
    rw [hPval i]
    by_cases hi : i ∈ G
    · rw [if_pos hi]; exact rank3_snd_thd (Ne.symm hba) (Ne.symm hca) (Ne.symm hcb)
    · rw [if_neg hi]; exact rank3_fst_snd (Ne.symm hcb)
  by_cases hac : StrictPref (f P) a c
  · left
    apply fieldExpansion hPareto hIIA hX ha hc (Ne.symm hca)
    intro Q hQac hQca
    have hagree : PairwiseAgreesOn Q P a c := by
      intro i
      by_cases hi : i ∈ G
      · have hPi : StrictPref (P i) a c := by
          rw [hPval i, if_pos hi]; exact rank3_fst_thd (Ne.symm hca) (Ne.symm hcb)
        exact sameOrder_of_strict_strict (hQac i hi) hPi
      · have hPi : StrictPref (P i) c a := by
          rw [hPval i, if_neg hi]; exact rank3_snd_thd (Ne.symm hcb) hba hca
        exact sameOrder_of_reverse_strict (hQca i hi) hPi
    exact ((hIIA Q P a c ha hc hagree).2.1).mpr hac
  · right
    have hca_soc : (f P) c a := rel_of_not_strictPref_total (f P).total hac
    have hba_soc : StrictPref (f P) b a := strictPref_weak_right (f P).trans hPbc hca_soc
    apply fieldExpansion hPareto hIIA hX hb ha hba
    intro Q hQba hQab
    have hagree : PairwiseAgreesOn Q P b a := by
      intro i
      by_cases hi : i ∈ G
      · have hPi : StrictPref (P i) a b := by
          rw [hPval i, if_pos hi]; exact rank3_fst_snd (Ne.symm hba)
        exact sameOrder_of_reverse_strict (hQab i (not_not_intro hi)) hPi
      · have hPi : StrictPref (P i) b a := by
          rw [hPval i, if_neg hi]; exact rank3_fst_thd hba hca
        exact sameOrder_of_strict_strict (hQba i hi) hPi
    exact ((hIIA Q P b a hb ha hagree).2.1).mpr hba_soc

theorem decisive_not_disjoint {G H : Set ι} (hX : 3 ≤ X.card)
    (hG : IsDecisiveCoalition f X G) (hH : IsDecisiveCoalition f X H) (hdisj : G ∩ H = ∅) :
    False := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < X.card by omega)
  obtain ⟨b, hb, hba⟩ := Finset.existsSecondDistinctMem (show 2 ≤ X.card by omega) ha
  let P : Profile ι σ := fun v => if v ∈ G then rank3 a b b else rank3 b a a
  have hsoc_ab : StrictPref (f P) a b := by
    refine hG a b ha hb (Ne.symm hba) P ?_
    intro v hv
    show StrictPref (P v) a b
    rw [show P v = rank3 a b b from if_pos hv]
    exact rank3_fst_snd (Ne.symm hba)
  have hsoc_ba : StrictPref (f P) b a := by
    refine hH b a hb ha hba P ?_
    intro v hv
    show StrictPref (P v) b a
    have hvG : v ∉ G := by
      intro hvG'
      have : v ∈ G ∩ H := ⟨hvG', hv⟩
      rw [hdisj] at this
      exact Set.notMem_empty v this
    rw [show P v = rank3 b a a from if_neg hvG]
    exact rank3_fst_snd hba
  exact (not_strictPref_of_reverse hsoc_ab) hsoc_ba

/-! ### The quotient voting system

Collapsing the voters along a coloring `q : ι → κ` (whose fibres are the blocks of a partition) yields
the voting system `quotientSWF q f` on the blocks `κ`, in which each voter uses its block's preference.
Weak Pareto and IIA are inherited (`quotientSWF_pareto`, `quotientSWF_iia`). This is the engine of the
intersection axiom: a three-block partition produces a three-voter system, settled by the base case. -/

def quotientSWF {κ : Type*} (q : ι → κ) (f : SocialWelfareFunction ι σ) :
    SocialWelfareFunction κ σ :=
  fun g => f (fun v => g (q v))

omit [DecidableEq σ] in
theorem quotientSWF_pareto {κ : Type*} (q : ι → κ) (hPareto : ParetoOn f X) :
    ParetoOn (quotientSWF q f) X :=
  fun x y hx hy g hg => hPareto x y hx hy (fun v => g (q v)) (fun v => hg (q v))

omit [DecidableEq σ] in
theorem quotientSWF_iia {κ : Type*} (q : ι → κ) (hIIA : IIAOn f X) :
    IIAOn (quotientSWF q f) X :=
  fun g g' x y hx hy hagree =>
    hIIA (fun v => g (q v)) (fun v => g' (q v)) x y hx hy (fun v => hagree (q v))

/-! ### Base case: three voters

A voting system on `Fin 3` satisfying the axioms has a decisive voter. If no singleton were decisive,
the dichotomy makes all three two-element complements decisive; the Condorcet profile (voter `0`:
`a ≻ b ≻ c`, voter `1`: `b ≻ c ≻ a`, voter `2`: `c ≻ a ≻ b`) then forces `a ≻ b`, `b ≻ c` and `c ≻ a`
socially, contradicting transitivity. (For two voters the dichotomy alone suffices, and for one voter
the single voter is decisive; only the three-voter case is needed below.) -/
theorem base_fin3 (F : SocialWelfareFunction (Fin 3) σ) (hP : ParetoOn F X) (hI : IIAOn F X)
    (hX : 3 ≤ X.card) : ∃ j : Fin 3, IsDecisiveCoalition F X {j} := by
  classical
  by_contra hcon
  push_neg at hcon
  have d0 : IsDecisiveCoalition F X {(0 : Fin 3)}ᶜ :=
    (decisive_dichotomy hP hI hX {0}).resolve_left (hcon 0)
  have d1 : IsDecisiveCoalition F X {(1 : Fin 3)}ᶜ :=
    (decisive_dichotomy hP hI hX {1}).resolve_left (hcon 1)
  have d2 : IsDecisiveCoalition F X {(2 : Fin 3)}ᶜ :=
    (decisive_dichotomy hP hI hX {2}).resolve_left (hcon 2)
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < X.card by omega)
  obtain ⟨b, hb, hba⟩ := Finset.existsSecondDistinctMem (show 2 ≤ X.card by omega) ha
  obtain ⟨c, hc, hca, hcb⟩ := Finset.existsThirdDistinctMem hX ha hb (Ne.symm hba)
  let G : Profile (Fin 3) σ :=
    fun v => if v = 0 then rank3 a b c else if v = 1 then rank3 b c a else rank3 c a b
  have sbc : StrictPref (F G) b c := by
    refine d2 b c hb hc (Ne.symm hcb) G ?_
    intro v hv
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hv
    show StrictPref (G v) b c
    fin_cases v
    · exact rank3_snd_thd (Ne.symm hba) (Ne.symm hca) (Ne.symm hcb)
    · exact rank3_fst_snd (Ne.symm hcb)
    · exact absurd rfl hv
  have sab : StrictPref (F G) a b := by
    refine d1 a b ha hb (Ne.symm hba) G ?_
    intro v hv
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hv
    show StrictPref (G v) a b
    fin_cases v
    · exact rank3_fst_snd (Ne.symm hba)
    · exact absurd rfl hv
    · exact rank3_snd_thd hca hcb (Ne.symm hba)
  have sca : StrictPref (F G) c a := by
    refine d0 c a hc ha hca G ?_
    intro v hv
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hv
    show StrictPref (G v) c a
    fin_cases v
    · exact absurd rfl hv
    · exact rank3_snd_thd (Ne.symm hcb) hba hca
    · exact rank3_fst_snd hca
  exact (not_strictPref_of_reverse (strictPref_trans (F G).trans sab sbc)) sca

/-! ### Lifting a decisive quotient-voter to a decisive block

If the block `j` is a decisive voter of the quotient, then its fibre `q ⁻¹' {j}` is a decisive
coalition of `f`. The proof needs only *weak* decisiveness of the fibre for one pair: the opposition
profile (fibre `j` ranks `a ≻ b`, everyone else `b ≻ a`) is constant on the blocks, hence agrees
pairwise with the quotient profile `g` that records each block's `(a, b)`-vote, so IIA transports the
quotient verdict; `fieldExpansion` then upgrades to full decisiveness. -/
theorem decisive_block_of_quotient {n : ℕ} (q : ι → Fin n) (j : Fin n)
    (hPareto : ParetoOn f X) (hIIA : IIAOn f X) (hX : 3 ≤ X.card)
    (hj : IsDecisiveCoalition (quotientSWF q f) X {j}) :
    IsDecisiveCoalition f X (q ⁻¹' {j}) := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < X.card by omega)
  obtain ⟨b, hb, hba⟩ := Finset.existsSecondDistinctMem (show 2 ≤ X.card by omega) ha
  refine fieldExpansion hPareto hIIA hX ha hb (Ne.symm hba) ?_
  intro P hin hout
  let g : Profile (Fin n) σ := fun jj => if jj = j then rank3 a b b else rank3 b a a
  have hgj : g j = rank3 a b b := if_pos rfl
  have hquot : StrictPref (f (fun v => g (q v))) a b := by
    refine hj a b ha hb (Ne.symm hba) g ?_
    intro jj hjj
    rw [Set.mem_singleton_iff] at hjj
    rw [hjj, hgj]
    exact rank3_fst_snd (Ne.symm hba)
  have hagree : PairwiseAgreesOn P (fun v => g (q v)) a b := by
    intro v
    by_cases hv : q v = j
    · have hPv : StrictPref (P v) a b :=
        hin v (by rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hv)
      have hGv : StrictPref (g (q v)) a b := by rw [hv, hgj]; exact rank3_fst_snd (Ne.symm hba)
      exact sameOrder_of_strict_strict hPv hGv
    · have hPv : StrictPref (P v) b a :=
        hout v (by rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hv)
      have hGv : StrictPref (g (q v)) b a := by
        rw [show g (q v) = rank3 b a a from if_neg hv]; exact rank3_fst_snd hba
      exact sameOrder_of_reverse_strict hPv hGv
  exact ((hIIA P (fun v => g (q v)) a b ha hb hagree).2.1).mpr hquot

/-! ### Intersection-closure

Decisive coalitions are closed under intersection. Colour the voters by the three-block partition
`G ∩ H`, `G ∖ H`, `Gᶜ`; the three-voter quotient has a decisive voter (`base_fin3`), whose fibre is a
decisive block (`decisive_block_of_quotient`). The `G ∖ H` block lies in `Hᶜ` and the `Gᶜ` block in
`Gᶜ`, both ruled out by `decisive_not_disjoint`, so the decisive block is `G ∩ H`. -/

theorem decisive_inter (hPareto : ParetoOn f X) (hIIA : IIAOn f X) (hX : 3 ≤ X.card)
    {G H : Set ι} (hG : IsDecisiveCoalition f X G) (hH : IsDecisiveCoalition f X H) :
    IsDecisiveCoalition f X (G ∩ H) := by
  classical
  set q : ι → Fin 3 := fun v => if v ∈ G then (if v ∈ H then 0 else 1) else 2 with hq
  obtain ⟨j, hj⟩ :=
    base_fin3 (quotientSWF q f) (quotientSWF_pareto q hPareto) (quotientSWF_iia q hIIA) hX
  have hblock : IsDecisiveCoalition f X (q ⁻¹' {j}) :=
    decisive_block_of_quotient q j hPareto hIIA hX hj
  -- the three fibres of the colouring
  have hf0 : q ⁻¹' {(0 : Fin 3)} = G ∩ H := by
    ext v
    rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff]
    constructor
    · intro hv
      simp only [hq] at hv
      by_cases hvG : v ∈ G
      · by_cases hvH : v ∈ H
        · exact ⟨hvG, hvH⟩
        · rw [if_pos hvG, if_neg hvH] at hv; exact absurd hv (by decide)
      · rw [if_neg hvG] at hv; exact absurd hv (by decide)
    · rintro ⟨hvG, hvH⟩
      simp only [hq]
      rw [if_pos hvG, if_pos hvH]
  have hf1 : q ⁻¹' {(1 : Fin 3)} ⊆ Hᶜ := by
    intro v hv
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hv
    simp only [hq] at hv
    rw [Set.mem_compl_iff]
    intro hvH
    by_cases hvG : v ∈ G
    · rw [if_pos hvG, if_pos hvH] at hv; exact absurd hv (by decide)
    · rw [if_neg hvG] at hv; exact absurd hv (by decide)
  have hf2 : q ⁻¹' {(2 : Fin 3)} ⊆ Gᶜ := by
    intro v hv
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hv
    simp only [hq] at hv
    rw [Set.mem_compl_iff]
    intro hvG
    by_cases hvH : v ∈ H
    · rw [if_pos hvG, if_pos hvH] at hv; exact absurd hv (by decide)
    · rw [if_pos hvG, if_neg hvH] at hv; exact absurd hv (by decide)
  -- the decisive block cannot be `G ∖ H ⊆ Hᶜ` or `Gᶜ`, so it is `G ∩ H`
  have hjne1 : j ≠ 1 := by
    rintro rfl
    exact decisive_not_disjoint hX hH (decisive_mono hf1 hblock) (Set.inter_compl_self H)
  have hjne2 : j ≠ 2 := by
    rintro rfl
    exact decisive_not_disjoint hX hG (decisive_mono hf2 hblock) (Set.inter_compl_self G)
  have hj0 : j = 0 := by omega
  rw [hj0, hf0] at hblock
  exact hblock

/-! ### Arrow's theorem

The decisive coalitions form a filter (`decisiveFilter`: `univ`, upward closure, intersection) and
hence an ultrafilter (`decisiveUltrafilter`, via the dichotomy and `decisive_not_disjoint`). On a
finite voter set an ultrafilter is principal (`Ultrafilter.eq_pure_of_finite`), and its generator is a
dictator. -/

def decisiveFilter (hPareto : ParetoOn f X) (hIIA : IIAOn f X) (hX : 3 ≤ X.card) : Filter ι where
  sets := {G | IsDecisiveCoalition f X G}
  univ_sets := univ_decisive hPareto
  sets_of_superset := fun hx hsub => decisive_mono hsub hx
  inter_sets := fun hx hy => decisive_inter hPareto hIIA hX hx hy

def decisiveUltrafilter (hPareto : ParetoOn f X) (hIIA : IIAOn f X) (hX : 3 ≤ X.card) :
    Ultrafilter ι :=
  Ultrafilter.ofComplNotMemIff (decisiveFilter hPareto hIIA hX) <| by
    intro s
    constructor
    · intro hsc
      rcases decisive_dichotomy hPareto hIIA hX s with hs | hsc'
      · exact hs
      · exact absurd hsc' hsc
    · intro hs hsc
      exact decisive_not_disjoint hX hs hsc (Set.inter_compl_self s)

/-- Arrow's impossibility theorem, via the ultrafilter of decisive coalitions: on a finite voter set,
weak Pareto + IIA on an agenda with at least three alternatives implies dictatorship. The decisive
coalitions form an ultrafilter, which is principal since the voter set is finite, and its generator is
a dictator. -/
theorem arrow_ultrafilter [Finite ι] (hPareto : ParetoOn f X) (hIIA : IIAOn f X)
    (hX : 3 ≤ X.card) : DictatorialOn f X := by
  classical
  obtain ⟨i₀, hi₀⟩ := Ultrafilter.eq_pure_of_finite (decisiveUltrafilter hPareto hIIA hX)
  refine ⟨i₀, ?_⟩
  have hmem : {i₀} ∈ (decisiveUltrafilter hPareto hIIA hX) := by
    rw [hi₀]; exact Ultrafilter.mem_pure.mpr rfl
  have hdec : IsDecisiveCoalition f X {i₀} := hmem
  intro P x y hx hy hxy
  rcases eq_or_ne x y with rfl | hxyne
  · exact (false_of_strictPref_self hxy).elim
  · refine hdec x y hx hy hxyne P ?_
    intro i hi
    rw [Set.mem_singleton_iff] at hi
    subst hi
    exact hxy

end EcoLean.SocialChoiceTheory
