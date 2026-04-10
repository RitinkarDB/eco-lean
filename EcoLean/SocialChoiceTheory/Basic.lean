import EcoLean.ChoicePreferenceUtility.Preference
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic

open Relation

namespace EcoLean.SocialChoiceTheory

/-!
# Basic infrastructure for finite social-choice theory

This file builds the foundational layer used later in the Arrow file.

Mathematically, it does four things.

First, it proves a few elementary finite-set lemmas. These are the small cardinality
facts needed whenever one wants to pick a second or third alternative distinct from a
given one. In Arrow-style arguments, these are what let us exploit the hypothesis that
the agenda contains at least three alternatives.

Second, it defines the core language of preference relations. We work with a weak
relation `R`, then define strict preference and indifference in the usual way:
`x P y` means `x R y` and not `y R x`, while `x I y` means both `x R y` and `y R x`.
Several lemmas then record the standard interaction of strict preference,
indifference, transitivity, and totality.

Third, it develops the finite-choice notions of maximal element, best element,
maximal set, and choice set. These are abstract order-theoretic notions, not yet
Arrow-specific.

Fourth, it introduces bundled structures for quasi-orders and preference orders.
A `QuasiOrder` is reflexive and transitive. A `PrefOrder` is reflexive,
transitive, and total; later in the file we also expose the eco-lean-aligned
alias `Preference` for the same structure. This bundled formulation is
convenient later because social welfare functions return preferences.

The later Arrow file uses all of this as its "algebra of pairwise comparisons".
-/

section FinsetLemmas

variable {α : Type*}
variable {s : Finset α} {a b : α}

namespace Finset

/--
If `s` is nonempty and not equal to `{a}`, then `s` contains some element distinct from `a`.

This is the most primitive finite-set separation lemma in the file. It says that once a
finite agenda is not collapsed to a singleton, one can find a genuine second option.
-/
lemma existsDistinctMemOfNeSingleton
    [DecidableEq α]
    (hs₁ : s.Nonempty) (hs₂ : s ≠ {a}) :
    ∃ b ∈ s, b ≠ a := by
  classical
  by_contra h
  push_neg at h
  apply hs₂
  ext x
  constructor
  · intro hx
    have hx' := h x hx
    simp [hx']
  · intro hx
    rcases hs₁ with ⟨y, hy⟩
    have hy' : y = a := h y hy
    have hx' : x = a := by simpa using hx
    subst hy'
    subst hx'
    simpa using hy

/--
If a finite set has cardinality at least `2` and contains `a`, then it contains some
other element distinct from `a`.

This packages the previous idea in cardinality form, which is often more convenient in
social-choice arguments because hypotheses naturally come as lower bounds on the number
of alternatives.
-/
lemma existsSecondDistinctMem
    [DecidableEq α]
    (hs : 2 ≤ s.card) (ha : a ∈ s) :
    ∃ b ∈ s, b ≠ a := by
  classical
  have hcard : 1 ≤ (s.erase a).card := by
    have hs' : 2 ≤ (s.erase a).card + 1 := by
      simpa [Finset.card_erase_add_one ha] using hs
    omega
  have hpos : 0 < (s.erase a).card := by omega
  have hne : (s.erase a).Nonempty := Finset.card_pos.1 hpos
  rcases hne with ⟨b, hb⟩
  exact ⟨b, (Finset.mem_erase.1 hb).2, (Finset.mem_erase.1 hb).1⟩

/--
If a finite set has cardinality strictly greater than `2` and already contains two
distinct elements `a` and `b`, then it contains a third element distinct from both.

This lemma is one of the key combinatorial inputs to Arrow-style proofs: from an agenda
of size at least three, one can always pick a "third alternative" used to mediate
pivotality and dictatorship arguments.
-/
lemma existsThirdDistinctMem
    [DecidableEq α]
    (hs : 2 < s.card) (ha : a ∈ s) (hb : b ∈ s) (h : a ≠ b) :
    ∃ c ∈ s, c ≠ a ∧ c ≠ b := by
  classical
  have hba : a ∈ s.erase b := Finset.mem_erase.mpr ⟨h, ha⟩
  have h1 : ((s.erase b).erase a).card + 1 = (s.erase b).card := by
    simpa using Finset.card_erase_add_one hba
  have h2 : (s.erase b).card + 1 = s.card := by
    simpa using Finset.card_erase_add_one hb
  have hpos : 0 < ((s.erase b).erase a).card := by
    omega
  have hne : ((s.erase b).erase a).Nonempty := Finset.card_pos.mp hpos
  rcases hne with ⟨c, hc⟩
  have hce : c ∈ s.erase b := (Finset.mem_erase.mp hc).2
  have hca : c ≠ a := (Finset.mem_erase.mp hc).1
  have hcb : c ≠ b := (Finset.mem_erase.mp hce).1
  have hcs : c ∈ s := (Finset.mem_erase.mp hce).2
  exact ⟨c, hcs, hca, hcb⟩

/--
A member of a finite set witnesses that the set is nonempty.

This trivial lemma is kept as a named fact because it streamlines later proofs.
-/
lemma nonemptyOfMem (ha : a ∈ s) : s.Nonempty := ⟨a, ha⟩

end Finset

namespace Relation

/--
If every element of `s` has an incoming `R`-edge from another element of `s`, then every
element also has an incoming edge in the transitive closure `TransGen R`.

This is conceptually simple but useful when moving from one-step comparison information
to path-based information.
-/

lemma forallExistsTransGen
    (R : α → α → Prop)
    (hR : ∀ a ∈ s, ∃ b ∈ s, R b a) :
    ∀ a ∈ s, ∃ b ∈ s, TransGen R b a := by
  intro a ha
  rcases hR a ha with ⟨b, hb, hab⟩
  exact ⟨b, hb, TransGen.single hab⟩

end Relation

end FinsetLemmas

open Finset

section BasicDefs

/-!
## Basic relational definitions

We now fix a type `σ` of alternatives and work with binary relations on `σ`.
The philosophy throughout the file is that weak preference is primitive, while strict
preference and indifference are derived notions.
-/

variable {σ ι : Type*}
variable {x y z a b : σ}
variable {R R' : σ → σ → Prop}

/--
Strict preference induced by a weak relation.

Mathematically, `StrictPref R x y` means "`x` is weakly preferred to `y`, but not vice
versa". This is the standard way of extracting the asymmetric part of a weak order.
-/
def StrictPref (R : σ → σ → Prop) (x y : σ) : Prop :=
  R x y ∧ ¬ R y x

/--
Indifference induced by a weak relation.

Mathematically, `Indiff R x y` means the weak relation ranks `x` and `y` both ways,
which is the usual notion of indifference for weak orders.
-/
def Indiff (R : σ → σ → Prop) (x y : σ) : Prop :=
  R x y ∧ R y x

/--
If two relations agree on the pair `(a,b)` in both directions, then they also agree on
the induced strict comparisons between `a` and `b`.

This is a tiny transport lemma, but it is fundamental when using IIA later: once the
pairwise weak comparison data are preserved, the pairwise strict comparison data are
preserved as well.
-/
lemma strictPref_iff_of_iff
    (h₁ : R a b ↔ R' a b)
    (h₂ : R b a ↔ R' b a) :
    (StrictPref R a b ↔ StrictPref R' a b) ∧
    (StrictPref R b a ↔ StrictPref R' b a) := by
  constructor <;> simp [StrictPref, h₁, h₂]

/--
Indifference is transitive whenever the underlying weak relation is transitive.

This is the familiar fact that if `x ~ y` and `y ~ z` under a transitive weak order,
then `x ~ z`.
-/
lemma indiff_trans
    (htrans : ∀ ⦃a b c : σ⦄, R a b → R b c → R a c)
    (h1 : Indiff R x y) (h2 : Indiff R y z) :
    Indiff R x z := by
  exact ⟨htrans h1.1 h2.1, htrans h2.2 h1.2⟩

/--
Strict preference composed with indifference remains strict preference.

If `x P y` and `y I z`, then `x P z`, provided the weak relation is transitive.

Strict preference is transitive whenever the underlying weak relation is transitive.

This is the standard fact that the asymmetric part of a transitive weak order is itself
transitive.
-/
lemma strictPref_trans_indiff
    (htrans : ∀ ⦃a b c : σ⦄, R a b → R b c → R a c)
    (h1 : StrictPref R x y) (h2 : Indiff R y z) :
    StrictPref R x z := by
  refine ⟨htrans h1.1 h2.1, ?_⟩
  intro hzx
  exact h1.2 (htrans h2.1 hzx)

/--
Indifference is transitive whenever the underlying weak relation is transitive.

This is the familiar fact that if `x ~ y` and `y ~ z` under a transitive weak order,
then `x ~ z`.

Indifference composed with strict preference remains strict preference.

If `x I y` and `y P z`, then `x P z`, under transitivity.
-/
lemma indiff_trans_strictPref
    (htrans : ∀ ⦃a b c : σ⦄, R a b → R b c → R a c)
    (h1 : Indiff R x y) (h2 : StrictPref R y z) :
    StrictPref R x z := by
  refine ⟨htrans h1.1 h2.1, ?_⟩
  intro hzx
  exact h2.2 (htrans hzx h1.1)

/--
Strict preference is transitive whenever the underlying weak relation is transitive.

This is the standard fact that the asymmetric part of a transitive weak order is itself
transitive.
-/
lemma strictPref_trans
    (htrans : ∀ ⦃a b c : σ⦄, R a b → R b c → R a c)
    (h1 : StrictPref R x y) (h2 : StrictPref R y z) :
    StrictPref R x z := by
  refine ⟨htrans h1.1 h2.1, ?_⟩
  intro hzx
  exact h2.2 (htrans hzx h1.1)

/--
Under totality, failure of the reverse strict preference implies the forward weak relation.

Concretely, if the relation is total and it is *not* the case that `y P x`, then
necessarily `x R y`. This is one of the characteristic ways totality is used later.
-/
lemma rel_of_not_strictPref_total
    (htot : ∀ a b : σ, R a b ∨ R b a) (h : ¬ StrictPref R y x) :
    R x y := by
  rcases htot x y with hxy | hyx
  · exact hxy
  · by_contra hxy
    exact h ⟨hyx, hxy⟩

/--
Strict preference cannot hold in both directions.

This is the asymmetry of strict preference.
-/
lemma not_strictPref_of_reverse
    (h : StrictPref R x y) :
    ¬ StrictPref R y x := by
  intro hyx
  exact hyx.2 h.1

/--
If `x R y` already fails, then certainly `x P y` fails.

This is a convenience lemma for eliminating impossible strict comparisons.
-/
lemma not_strictPref_of_not_rel
    (h : ¬ R x y) :
    ¬ StrictPref R x y := by
  intro hxy
  exact h hxy.1

/--
No element can be strictly preferred to itself.

This is the irreflexivity of strict preference, derived from its definition.
-/
lemma false_of_strictPref_self
    (h : StrictPref R x x) :
    False := by
  exact h.2 h.1

/--
Agreement of two relations on a given pair, both at the weak and strict levels.

`SameOrder R R' x y x' y'` says that the comparison of `x` versus `y` under `R` matches
the comparison of `x'` versus `y'` under `R'`, in *both* weak directions and hence also
in both strict directions.
-/

def SameOrder
    (R R' : σ → σ → Prop) (x y x' y' : σ) : Prop :=
  ((R x y ↔ R' x' y') ∧ (R y x ↔ R' y' x')) ∧
  (StrictPref R x y ↔ StrictPref R' x' y') ∧
  (StrictPref R y x ↔ StrictPref R' y' x')

/--
A lighter pairwise agreement notion that remembers only the strict comparison pattern.

This is useful when only strict preference transport is needed.
-/

def SameOrder'
    (R R' : σ → σ → Prop) (x y x' y' : σ) : Prop :=
  (StrictPref R x y ↔ StrictPref R' x' y') ∧
  (StrictPref R y x ↔ StrictPref R' y' x')

/--
If both relations strictly rank `x` above `y`, then they certainly induce the same order
on the pair `(x,y)`.

This packages the obvious observation that two identical strict pairwise rankings imply
pairwise agreement in the stronger `SameOrder` sense.
-/
lemma sameOrder_of_strict_strict
    (hR : StrictPref R x y) (hR' : StrictPref R' x y) :
    SameOrder R R' x y x y := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact Iff.intro (fun _ => hR'.1) (fun _ => hR.1)
    · exact Iff.intro
        (fun hyx => False.elim (hR.2 hyx))
        (fun hyx => False.elim (hR'.2 hyx))
  · exact Iff.intro (fun _ => hR') (fun _ => hR)
  · exact Iff.intro
      (fun hyx => False.elim ((not_strictPref_of_reverse hR) hyx))
      (fun hyx => False.elim ((not_strictPref_of_reverse hR') hyx))

/--
If both relations strictly rank `y` above `x`, then they induce the same order on the
pair `(x,y)` as well.

This is the reverse-oriented companion to `sameOrder_of_strict_strict`.
-/
lemma sameOrder_of_reverse_strict
    (hR : StrictPref R y x) (hR' : StrictPref R' y x) :
    SameOrder R R' x y x y := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact Iff.intro
        (fun hxy => False.elim (hR.2 hxy))
        (fun hxy => False.elim (hR'.2 hxy))
    · exact Iff.intro (fun _ => hR'.1) (fun _ => hR.1)
  · exact Iff.intro
      (fun hxy => False.elim ((not_strictPref_of_reverse hR) hxy))
      (fun hxy => False.elim ((not_strictPref_of_reverse hR') hxy))
  · exact Iff.intro (fun _ => hR') (fun _ => hR)

lemma sameOrder'_comm :
    SameOrder' R R' x y x y ↔ SameOrder' R R' y x y x := by
  exact and_comm

/--
`x` is maximal in `S` if no element of `S` is strictly preferred to `x`.

This is the usual order-theoretic notion of maximality: other elements may tie with `x`,
but none can beat it strictly.
-/
def IsMaximalElement
    (x : σ) (S : Finset σ) (R : σ → σ → Prop) : Prop :=
  ∀ y ∈ S, ¬ StrictPref R y x

/--
`x` is best in `S` if it weakly dominates every element of `S`.

This is stronger than maximality: a best element is above everyone, not merely unbeaten.
-/
def IsBestElement
    (x : σ) (S : Finset σ) (R : σ → σ → Prop) : Prop :=
  ∀ y ∈ S, R x y

/--
The set of maximal elements of `S` under the relation `R`.

The definition is noncomputable only because we use classical decidability for the
filtering predicate.
-/
noncomputable def maximalSet [DecidableEq σ]
    (S : Finset σ) (R : σ → σ → Prop) : Finset σ := by
  classical
  exact S.filter (fun x => IsMaximalElement x S R)

/--
The set of best elements of `S` under the relation `R`.

For a complete and transitive order on a finite set, this is the usual "choice set" of
alternatives that beat or tie everything else.
-/
noncomputable def choiceSet [DecidableEq σ]
    (S : Finset σ) (R : σ → σ → Prop) : Finset σ := by
  classical
  exact S.filter (fun x => IsBestElement x S R)

/--
Membership in `maximalSet` gives the corresponding maximality property.
-/
lemma maximalElement_of_mem_maximalSet
    [DecidableEq σ] {r : σ → σ → Prop} {s : Finset σ} {x : σ}
    (h : x ∈ maximalSet s r) :
    IsMaximalElement x s r := by
  simp [maximalSet] at h
  exact h.2

/--
A maximal element of `S` belongs to `maximalSet S R`.

Together with the previous lemma, this identifies `maximalSet` exactly with the
predicate `IsMaximalElement`.
-/
lemma mem_maximalSet_of_maximalElement
    [DecidableEq σ] {r : σ → σ → Prop} {s : Finset σ} {x : σ}
    (hx : x ∈ s) (h : IsMaximalElement x s r) :
    x ∈ maximalSet s r := by
  simp [maximalSet, hx, h]

/--
The maximal set is a subset of the underlying agenda `s`.

This is immediate from the filter definition, but it is often useful as a standalone
fact in later arguments.
-/
lemma maximalSet_subset
    [DecidableEq σ] (s : Finset σ) (r : σ → σ → Prop) :
    maximalSet s r ⊆ s := by
  classical
  intro x hx
  exact (Finset.mem_filter.mp hx).1

/--
In a singleton set, the unique element is maximal under any reflexive relation.

This is the finite base case behind later inductive existence arguments.
-/
lemma isMaximal_of_singleton
    [DecidableEq σ] {R : σ → σ → Prop}
    (hR : Reflexive R) (x : σ) :
    IsMaximalElement x ({x} : Finset σ) R := by
  intro y hy
  have hy' : y = x := by
    simpa using hy
  subst hy'
  intro h
  exact h.2 (hR _)


/--
The maximal set of the empty agenda is empty.
-/
lemma maximalSet_eq_empty_of_empty
    [DecidableEq σ] (R : σ → σ → Prop) :
    maximalSet (∅ : Finset σ) R = ∅ := by
  simp [maximalSet]

/--
The choice set of the empty agenda is empty.
-/
lemma choiceSet_eq_empty_of_empty
    [DecidableEq σ] (R : σ → σ → Prop) :
    choiceSet (∅ : Finset σ) R = ∅ := by
  simp [choiceSet]

/--
Every best element is maximal.

Mathematically, if `x` weakly beats everyone, then nobody can strictly beat `x`.
-/
lemma choiceSet_subset_maximalSet
    [DecidableEq σ] (S : Finset σ) (R : σ → σ → Prop) :
    choiceSet S R ⊆ maximalSet S R := by
  classical
  intro a ha
  rcases Finset.mem_filter.mp ha with ⟨haS, haBest⟩
  apply Finset.mem_filter.mpr
  refine ⟨haS, ?_⟩
  intro y hy hya
  exact hya.2 (haBest y hy)

end BasicDefs

section QuasiOrders

/-!
## Quasi-orders and their finite maximal elements

A quasi-order is only reflexive and transitive, so totality is *not* assumed here.
The main theorem of this section is the finite analogue of a standard order-theoretic
fact: every nonempty finite quasi-ordered set has a maximal element.
-/

variable {σ : Type*}

/--
A bundled quasi-order: reflexive and transitive, but not necessarily total.

This is the correct generality for several finite maximality arguments.
-/

structure QuasiOrder (α : Type*) where
  rel : α → α → Prop
  refl : Reflexive rel
  trans : ∀ ⦃a b c : α⦄, rel a b → rel b c → rel a c

instance : CoeFun (QuasiOrder σ) (fun _ => σ → σ → Prop) where
  coe r := r.rel

namespace QuasiOrder

lemma eq_coe (r : QuasiOrder σ) : r.rel = r := rfl

end QuasiOrder

open Finset

/--
Every nonempty finite quasi-ordered set has a maximal element.

The proof is by induction on the finite set. At each step, compare the new point `a`
to a maximal element of the old set. Either `a` strictly beats it, in which case `a`
is maximal in the enlarged set, or else the old maximal element remains maximal.
-/
lemma maximal_of_finite_quasiOrdered
    [DecidableEq σ]
    (r : QuasiOrder σ)
    (S : Finset σ) (hS : S.Nonempty) :
    ∃ x ∈ S, IsMaximalElement x S r := by
  classical
  refine Finset.induction_on S ?h0 ?hstep hS
  · intro h
    cases h with
    | intro x hx => cases hx
  · intro a s ha_not_mem ih hs_nonempty
    by_cases hs : s.Nonempty
    · rcases ih hs with ⟨x, hxS, hxmax⟩
      by_cases hax : StrictPref r a x
      · refine ⟨a, by simp, ?_⟩
        intro b hb
        by_cases hba : b = a
        · subst hba
          intro haa
          exact haa.2 (r.refl _)
        · have hbS : b ∈ s := by
            simpa [hba] using hb
          intro hba_strict
          exact hxmax b hbS (strictPref_trans r.trans hba_strict hax)
      · refine ⟨x, by simp [hxS], ?_⟩
        intro b hb
        by_cases hba : b = a
        · subst hba
          simpa using hax
        · exact hxmax b (by simpa [hba] using hb)
    · have hs' : s = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using hs
      subst hs'
      refine ⟨a, by simp, ?_⟩
      simpa using isMaximal_of_singleton r.refl a

/--
For a reflexive relation, the choice set of a singleton is exactly that singleton.
-/
lemma choiceSet_of_singleton
    [DecidableEq σ]
    {r : σ → σ → Prop} (hr : Reflexive r) (x : σ) :
    choiceSet ({x} : Finset σ) r = {x} := by
  classical
  ext y
  constructor
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hyx, _⟩
    simpa using hyx
  · intro hy
    apply Finset.mem_filter.mpr
    refine ⟨by simp [hy], ?_⟩
    intro z hz
    have hz' : z = x := by
      simpa using hz
    have hy' : y = x := by
      simpa using hy
    rw [hy', hz']
    exact hr x

/--
On a two-point agenda `{x,y}`, the choice set is `{x}` exactly when `x P y`.

This is a useful bridge between the abstract choice-set notion and an explicit strict
pairwise comparison.
-/
lemma singleton_choiceSet
    [DecidableEq σ]
    {r : σ → σ → Prop}
    (x y : σ) (hxy : x ≠ y) (hR : Reflexive r) :
    StrictPref r x y ↔ ({x} : Finset σ) = choiceSet ({x, y} : Finset σ) r := by
  classical
  constructor
  · intro h
    ext z
    constructor
    · intro hz
      have hz' : z = x := by
        simpa using hz
      apply Finset.mem_filter.mpr
      refine ⟨by simp [hz'], ?_⟩
      intro w hw
      have hw' : w = x ∨ w = y := by
        simpa using hw
      rcases hw' with hwx | hwy
      · rw [hz', hwx]
        exact hR x
      · rw [hz', hwy]
        exact h.1
    · intro hz
      rcases Finset.mem_filter.mp hz with ⟨hzS, hzBest⟩
      by_cases hzx : z = x
      · simp [hzx]
      · have hzy : z = y := by
          have : z = x ∨ z = y := by
            simpa using hzS
          rcases this with h1 | h2
          · exact False.elim (hzx h1)
          · exact h2
        have hyx : r y x := by
          rw [← hzy]
          exact hzBest x (by simp)
        exfalso
        exact h.2 hyx
  · intro hEq
    have hx : x ∈ choiceSet ({x, y} : Finset σ) r := by
      rw [← hEq]
      simp
    rcases Finset.mem_filter.mp hx with ⟨hxS, hxBest⟩
    have hxy' : r x y := by
      exact hxBest y (by simp)
    have hy_not : y ∉ choiceSet ({x, y} : Finset σ) r := by
      intro hy_mem
      rw [← hEq] at hy_mem
      have : y = x := by
        simpa using hy_mem
      exact hxy this.symm
    have hyx_not : ¬ r y x := by
      intro hyx
      apply hy_not
      apply Finset.mem_filter.mpr
      refine ⟨by simp, ?_⟩
      intro z hz
      have hz' : z = x ∨ z = y := by
        simpa using hz
      rcases hz' with hzx | hzy
      · rw [hzx]
        exact hyx
      · rw [hzy]
        exact hR y
    exact ⟨hxy', hyx_not⟩

/--
If the choice set of a finite quasi-order is nonempty, then it coincides with the
maximal set.

The intuition is that once some best element exists, every maximal element must be
indifferent to it and hence also be best.
-/
lemma choiceEq_maximal_of_quasi
    [DecidableEq σ]
    {r : QuasiOrder σ}
    (S : Finset σ) (hS : (choiceSet S r).Nonempty) :
    choiceSet S r = maximalSet S r := by
  classical
  apply Finset.Subset.antisymm
  · exact choiceSet_subset_maximalSet S r
  · intro z hz
    rcases hS with ⟨x, hx⟩
    rcases Finset.mem_filter.mp hz with ⟨hzS, hzmax⟩
    rcases Finset.mem_filter.mp hx with ⟨hxS, hxbest⟩
    apply Finset.mem_filter.mpr
    refine ⟨hzS, ?_⟩
    intro y hy
    have hzx : r z x := by
      by_contra hzx
      exact hzmax x hxS ⟨hxbest z hzS, hzx⟩
    exact r.trans hzx (hxbest y hy)

/--
On a nonempty finite quasi-order, the maximal elements are pairwise indifferent iff the
choice set and the maximal set coincide.

This is the most conceptually substantial lemma in the file outside Arrow itself.
It characterizes when maximality collapses to full best-element status.
-/
lemma maximal_indiff_iff_choiceEq_maximal
    [DecidableEq σ]
    (r : QuasiOrder σ)
    (S : Finset σ) (hS : S.Nonempty) :
    (∀ x y, x ∈ maximalSet S r → y ∈ maximalSet S r → Indiff r x y) ↔
      choiceSet S r = maximalSet S r := by
  classical
  constructor
  · intro hyp
    by_contra sets_neq
    obtain ⟨x₀, x₀_in, hx₀⟩ := maximal_of_finite_quasiOrdered r S hS
    have choice_empty : choiceSet S r = ∅ := by
      by_contra hne
      have hchoice_nonempty : (choiceSet S r).Nonempty := by
        by_contra hchoice_empty
        exact hne (Finset.not_nonempty_iff_eq_empty.mp hchoice_empty)
      exact sets_neq (choiceEq_maximal_of_quasi S hchoice_nonempty)
    have x₀_not_in : x₀ ∉ choiceSet S r := by
      rw [choice_empty]
      simp
    have hx₀_not_best : ¬ IsBestElement x₀ S r := by
      intro hxbest
      exact x₀_not_in (Finset.mem_filter.mpr ⟨x₀_in, hxbest⟩)
    unfold IsBestElement at hx₀_not_best
    push_neg at hx₀_not_best
    obtain ⟨x₁, x₁_in, hx₁⟩ := hx₀_not_best

    have hx₀M : x₀ ∈ maximalSet S r := by
      exact mem_maximalSet_of_maximalElement x₀_in hx₀

    have x₁_not_in : x₁ ∉ maximalSet S r := by
      intro x₁_in_max
      exact hx₁ (hyp x₀ x₁ hx₀M x₁_in_max).1

    let T : Finset σ := S.filter (fun z => StrictPref r z x₁ ∧ z ∉ maximalSet S r)

    have h_no_max :
        ¬ ∃ x ∈ T, IsMaximalElement x T r := by
      intro hmax
      rcases hmax with ⟨x, x_in, hxmaxT⟩
      have hx_in : x ∈ S ∧ StrictPref r x x₁ ∧ x ∉ maximalSet S r := by
        simpa [T] using x_in
      rcases hx_in with ⟨hxS, hPx₁, hx_not_max⟩

      have hx_not_max' : ¬ IsMaximalElement x S r := by
        intro hxMaxS
        exact hx_not_max (mem_maximalSet_of_maximalElement hxS hxMaxS)

      unfold IsMaximalElement at hx_not_max'
      push_neg at hx_not_max'
      obtain ⟨y, y_in, hy⟩ := hx_not_max'

      have hy_in_T : y ∈ T := by
        apply Finset.mem_filter.mpr
        refine ⟨y_in, ?_⟩
        refine ⟨strictPref_trans r.trans hy hPx₁, ?_⟩
        intro y_max
        apply hx₁
        exact (indiff_trans_strictPref r.trans
          (hyp x₀ y hx₀M y_max)
          (strictPref_trans r.trans hy hPx₁)).1

      have hy_strict : StrictPref r y x := by
        exact hy

      exact hxmaxT y hy_in_T hy_strict

    have hT_nonempty : T.Nonempty := by
      have x₁_not_max' : ¬ IsMaximalElement x₁ S r := by
        intro hx₁max
        exact x₁_not_in (mem_maximalSet_of_maximalElement x₁_in hx₁max)
      unfold IsMaximalElement at x₁_not_max'
      push_neg at x₁_not_max'
      obtain ⟨x₂, x₂_in, hx₂⟩ := x₁_not_max'
      refine ⟨x₂, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨x₂_in, ?_⟩
      refine ⟨hx₂, ?_⟩
      intro x₂_in_max
      apply hx₁
      exact r.trans (hyp x₀ x₂ hx₀M x₂_in_max).1 hx₂.1

    exact h_no_max (maximal_of_finite_quasiOrdered r T hT_nonempty)

  · intro hEq
    rw [← hEq]
    intro x y x_in y_in
    rcases Finset.mem_filter.mp x_in with ⟨hxS, hxbest⟩
    rcases Finset.mem_filter.mp y_in with ⟨hyS, hybest⟩
    exact ⟨hxbest y hyS, hybest x hxS⟩
section PrefOrders

/-!
## Preference orders and compatibility notions

We now strengthen quasi-orders to preference orders by adding totality.
This is the structure used for individual preferences and social rankings later on.
-/

variable {σ : Type*}

/--
A bundled preference order: reflexive, transitive, and total.

This is the standard formal model of a complete weak preference ordering.
-/

structure PrefOrder (α : Type*) where
  rel : α → α → Prop
  refl : Reflexive rel
  total : ∀ a b : α, rel a b ∨ rel b a
  trans : ∀ ⦃a b c : α⦄, rel a b → rel b c → rel a c

instance : CoeFun (PrefOrder σ) (fun _ => σ → σ → Prop) where
  coe r := r.rel

namespace PrefOrder

lemma eq_coe (r : PrefOrder σ) : r.rel = r := rfl

/--
Totality in contrapositive form: if `a` is not weakly above `b`, then `b` is weakly
above `a`.
-/
lemma reverse {r : PrefOrder σ} {a b : σ} (h : ¬ r a b) : r b a :=
  (r.total a b).resolve_left h

end PrefOrder

/--
Compatibility notions used when comparing quasi-orders and preference orders.

`IsSubrelation` says one quasi-order sits inside another in a way compatible with strict
comparisons. `IsCompatible` says a quasi-order is coherently embedded into a preference
order. These notions are not central to Arrow's theorem itself, but they belong to the
general order-theoretic infrastructure of the library.
-/

def IsSubrelation (Q₁ Q₂ : QuasiOrder σ) : Prop :=
  ∀ x y : σ, (Q₁ x y → Q₂ x y) ∧ ((Q₁ x y ∧ ¬ Q₁ y x) → ¬ Q₂ y x)

def IsCompatible (Q : QuasiOrder σ) (R : PrefOrder σ) : Prop :=
  ∀ x y : σ, (Q x y → R x y) ∧ ((Q x y ∧ ¬ Q y x) → ¬ R y x)

end PrefOrders

section SocialChoiceVocabulary

universe u v

/-!
## EcoLean-style social-choice vocabulary

The original development in this repository is phrased in terms of `PrefOrder`,
an explicit bundled complete weak order.  The `eco-lean` project instead uses
the terminology `Preference`, `Profile`, `SocialChoiceFunction`, and
`SocialWelfareFunction`, with weak preference as the primitive notion and strict
preference and indifference derived from it.

To make the two libraries interoperate smoothly, we expose that vocabulary here
as definitional wrappers around the existing infrastructure.  This keeps the
Arrow development stable while giving downstream files a shared language.
-/

/--
`RationalPreference A` is a complete and transitive weak preference on `A`,
built directly on top of `EcoLean.Preference A`.

This keeps the social-choice development aligned with eco-lean's primitive
weak-preference layer while still bundling the rationality properties that the
Arrow and Gibbard-Satterthwaite proofs use pervasively.
-/
structure RationalPreference (A : Type u) extends _root_.EcoLean.Preference A where
  isComplete : _root_.EcoLean.Preference.Complete toPreference
  isTransitive : _root_.EcoLean.Preference.Transitive toPreference

/--
`Preference A` is the bundled rational preference type used in the
social-choice-theory development.

It is a thin rational wrapper over `EcoLean.Preference A`, with a compatibility
projection `toPrefOrder` back to the older `PrefOrder` infrastructure.
-/
abbrev Preference := RationalPreference

namespace Preference

variable {A : Type u} (P : Preference A)

instance : Coe (Preference A) (_root_.EcoLean.Preference A) where
  coe P := P.toPreference

instance : CoeFun (Preference A) (fun _ => A → A → Prop) where
  coe P := P.weakPref

/-- Compatibility projection back to the older bundled `PrefOrder` structure. -/
def toPrefOrder : PrefOrder A where
  rel := P.weakPref
  refl := by
    intro x
    exact _root_.EcoLean.Preference.weakPref_refl_of_complete
      (P := P.toPreference) P.isComplete x
  total := P.isComplete
  trans := P.isTransitive

/-- Build a bundled social-choice preference from a complete transitive weak order. -/
def ofPrefOrder (r : PrefOrder A) : Preference A where
  toPreference := { weakPref := r.rel }
  isComplete := r.total
  isTransitive := r.trans

instance : Coe (Preference A) (PrefOrder A) where
  coe P := P.toPrefOrder

@[simp] theorem toPrefOrder_apply
    (x y : A) :
    P.toPrefOrder x y ↔ P x y := by
  rfl

@[simp] theorem ofPrefOrder_apply
    (r : PrefOrder A) (x y : A) :
    Preference.ofPrefOrder r x y ↔ r x y := by
  rfl

@[simp] theorem ofPrefOrder_weakPref
    (r : PrefOrder A) (x y : A) :
    (Preference.ofPrefOrder r).weakPref x y ↔ r x y := by
  rfl

theorem refl : Reflexive P :=
  by
    intro x
    exact _root_.EcoLean.Preference.weakPref_refl_of_complete
      (P := P.toPreference) P.isComplete x

theorem total : ∀ x y : A, P x y ∨ P y x :=
  P.isComplete

theorem trans : ∀ ⦃x y z : A⦄, P x y → P y z → P x z :=
  P.isTransitive

/-- Primitive weak preference relation. -/
@[simp] abbrev weakPref : A → A → Prop := P.toPreference.weakPref

/-- Strict preference derived from weak preference. -/
def StrictPref (x y : A) : Prop :=
  P.toPreference.StrictPref x y

/-- Indifference derived from weak preference. -/
def Indiff (x y : A) : Prop :=
  P.toPreference.Indiff x y

/-- Completeness of weak preference. -/
def Complete : Prop :=
  P.toPreference.Complete

/-- Transitivity of weak preference. -/
def Transitive : Prop :=
  P.toPreference.Transitive

theorem complete : P.Complete :=
  P.isComplete

theorem transitive : P.Transitive :=
  P.isTransitive

theorem weakPref_refl_of_complete
    (hC : P.Complete) (x : A) :
    P.weakPref x x := by
  exact _root_.EcoLean.Preference.weakPref_refl_of_complete
    (P := P.toPreference) hC x

@[simp] theorem strictPref_def
    (x y : A) :
    P.StrictPref x y ↔ (P.weakPref x y ∧ ¬ P.weakPref y x) := by
  rfl

@[simp] theorem indiff_def
    (x y : A) :
    P.Indiff x y ↔ (P.weakPref x y ∧ P.weakPref y x) := by
  rfl

end Preference

scoped notation:50 x " ≽[" P "] " y => Preference.weakPref P x y
scoped notation:50 x " ≻[" P "] " y => Preference.StrictPref P x y
scoped notation:50 x " ∼[" P "] " y => Preference.Indiff P x y

/--
A preference profile assigns a preference relation over alternatives to each voter.
-/
abbrev Profile (V : Type u) (A : Type v) : Type (max u v) :=
  V → Preference A

namespace Profile

variable {V : Type u} {A : Type v}

/-- The preference of voter `i` in profile `P`. -/
@[simp] abbrev pref (P : Profile V A) (i : V) : Preference A :=
  P i

/-- Voter `i` weakly prefers `x` to `y` under profile `P`. -/
def WeakPref (P : Profile V A) (i : V) (x y : A) : Prop :=
  (P i).weakPref x y

/-- Voter `i` strictly prefers `x` to `y` under profile `P`. -/
def StrictPref (P : Profile V A) (i : V) (x y : A) : Prop :=
  (P i).StrictPref x y

/-- Voter `i` is indifferent between `x` and `y` under profile `P`. -/
def Indiff (P : Profile V A) (i : V) (x y : A) : Prop :=
  (P i).Indiff x y

scoped notation:50 x " ≽[" P "," i "] " y => Profile.WeakPref P i x y
scoped notation:50 x " ≻[" P "," i "] " y => Profile.StrictPref P i x y
scoped notation:50 x " ∼[" P "," i "] " y => Profile.Indiff P i x y

theorem strictPref_def_notation
    (P : Profile V A) (i : V) (x y : A) :
    (x ≻[P,i] y) ↔ ((x ≽[P,i] y) ∧ ¬ (y ≽[P,i] x)) := by
  rfl

theorem indiff_def_notation
    (P : Profile V A) (i : V) (x y : A) :
    (x ∼[P,i] y) ↔ ((x ≽[P,i] y) ∧ (y ≽[P,i] x)) := by
  rfl

end Profile

/-- A social choice function assigns a chosen alternative to each preference profile. -/
abbrev SocialChoiceFunction (V : Type u) (A : Type v) : Type (max u v) :=
  Profile V A → A

namespace SocialChoiceFunction

variable {V : Type u} {A : Type v}

/-- Evaluate a social choice function at a profile. -/
@[simp] abbrev eval (f : SocialChoiceFunction V A) (P : Profile V A) : A :=
  f P

end SocialChoiceFunction

/--
A social welfare function assigns a social preference relation to each profile.
-/
abbrev SocialWelfareFunction (V : Type u) (A : Type v) : Type (max u v) :=
  Profile V A → Preference A

/-- Compatibility alias for the older Arrow development. -/
abbrev SWF (V : Type u) (A : Type v) := SocialWelfareFunction V A

namespace SocialWelfareFunction

variable {V : Type u} {A : Type v}

/-- Evaluate a social welfare function at a profile. -/
@[simp] abbrev eval (F : SocialWelfareFunction V A) (P : Profile V A) : Preference A :=
  F P

/-- The social weak preference induced by `F` at profile `P`. -/
def WeakPref (F : SocialWelfareFunction V A) (P : Profile V A) (x y : A) : Prop :=
  (F P).weakPref x y

/-- The social strict preference induced by `F` at profile `P`. -/
def StrictPref (F : SocialWelfareFunction V A) (P : Profile V A) (x y : A) : Prop :=
  (F P).StrictPref x y

/-- The social indifference induced by `F` at profile `P`. -/
def Indiff (F : SocialWelfareFunction V A) (P : Profile V A) (x y : A) : Prop :=
  (F P).Indiff x y

scoped notation:50 x " ≽ₛ[" F "," P "] " y => SocialWelfareFunction.WeakPref F P x y
scoped notation:50 x " ≻ₛ[" F "," P "] " y => SocialWelfareFunction.StrictPref F P x y
scoped notation:50 x " ∼ₛ[" F "," P "] " y => SocialWelfareFunction.Indiff F P x y

theorem strictPref_def
    (F : SocialWelfareFunction V A) (P : Profile V A) (x y : A) :
    SocialWelfareFunction.StrictPref F P x y ↔
      ((F P).weakPref x y ∧ ¬ (F P).weakPref y x) := by
  rfl

theorem indiff_def
    (F : SocialWelfareFunction V A) (P : Profile V A) (x y : A) :
    SocialWelfareFunction.Indiff F P x y ↔
      ((F P).weakPref x y ∧ (F P).weakPref y x) := by
  rfl

end SocialWelfareFunction

/--
A social welfare function is complete if, at every profile, the induced social
preference is complete.
-/
def CompleteSWF
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) : Prop :=
  ∀ P : Profile V A, (F P).Complete

/--
A social welfare function is transitive if, at every profile, the induced social
preference is transitive.
-/
def TransitiveSWF
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) : Prop :=
  ∀ P : Profile V A, (F P).Transitive

/--
A social welfare function is rational if, at every profile, the induced social
preference is complete and transitive.
-/
def RationalSWF
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) : Prop :=
  CompleteSWF F ∧ TransitiveSWF F

/-- A profile is rational if every voter's preference is complete and transitive. -/
def RationalProfile
    {V : Type u} {A : Type v}
    (P : Profile V A) : Prop :=
  ∀ i : V, (P i).Complete ∧ (P i).Transitive

namespace CompleteSWF

variable {V : Type u} {A : Type v} {F : SocialWelfareFunction V A}

theorem apply
    (h : CompleteSWF F)
    (P : Profile V A) :
    (F P).Complete :=
  h P

end CompleteSWF

namespace TransitiveSWF

variable {V : Type u} {A : Type v} {F : SocialWelfareFunction V A}

theorem apply
    (h : TransitiveSWF F)
    (P : Profile V A) :
    (F P).Transitive :=
  h P

end TransitiveSWF

namespace RationalSWF

variable {V : Type u} {A : Type v} {F : SocialWelfareFunction V A}

theorem complete
    (h : RationalSWF F)
    (P : Profile V A) :
    (F P).Complete :=
  h.1 P

theorem transitive
    (h : RationalSWF F)
    (P : Profile V A) :
    (F P).Transitive :=
  h.2 P

end RationalSWF

namespace RationalProfile

variable {V : Type u} {A : Type v} {P : Profile V A}

theorem complete
    (h : RationalProfile P)
    (i : V) :
    (P i).Complete :=
  (h i).1

theorem transitive
    (h : RationalProfile P)
    (i : V) :
    (P i).Transitive :=
  (h i).2

end RationalProfile

/--
Profiles `P` and `Q` agree on the pairwise comparison of `x` and `y` for every voter.
-/
def PairwiseAgreesOn
    {V : Type u} {A : Type v}
    (P Q : Profile V A) (x y : A) : Prop :=
  ∀ i : V, SameOrder (P i) (Q i) x y x y

/--
Independence of irrelevant alternatives: the social comparison of `x` and `y`
depends only on individuals' comparisons of `x` and `y`.
-/
def IIA
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) : Prop :=
  ∀ (P Q : Profile V A) (x y : A),
    PairwiseAgreesOn P Q x y →
    SameOrder (F P) (F Q) x y x y

namespace PairwiseAgreesOn

variable {V : Type u} {A : Type v}
variable {P Q : Profile V A} {x y : A}

theorem sameOrder
    (h : PairwiseAgreesOn P Q x y) (i : V) :
    SameOrder (P i) (Q i) x y x y :=
  h i

theorem apply
    (h : PairwiseAgreesOn P Q x y) (i : V) :
    (Profile.WeakPref P i x y ↔ Profile.WeakPref Q i x y) ∧
    (Profile.WeakPref P i y x ↔ Profile.WeakPref Q i y x) :=
  (h i).1

theorem strict
    (h : PairwiseAgreesOn P Q x y) (i : V) :
    (Profile.StrictPref P i x y ↔ Profile.StrictPref Q i x y) ∧
    (Profile.StrictPref P i y x ↔ Profile.StrictPref Q i y x) :=
  ⟨(h i).2.1, (h i).2.2⟩

theorem swap
    (h : PairwiseAgreesOn P Q x y) :
    PairwiseAgreesOn P Q y x := by
  intro i
  rcases h i with ⟨⟨hxy, hyx⟩, hstrictxy, hstrictyx⟩
  exact ⟨⟨hyx, hxy⟩, hstrictyx, hstrictxy⟩

end PairwiseAgreesOn

namespace IIA

variable {V : Type u} {A : Type v} {F : SocialWelfareFunction V A}

theorem apply
    (h : IIA F)
    (P Q : Profile V A) (x y : A)
    (hxy : PairwiseAgreesOn P Q x y) :
    SameOrder (F P) (F Q) x y x y :=
  h P Q x y hxy

theorem weak
    (h : IIA F)
    (P Q : Profile V A) (x y : A)
    (hxy : PairwiseAgreesOn P Q x y) :
    ((SocialWelfareFunction.WeakPref F P x y ↔
      SocialWelfareFunction.WeakPref F Q x y) ∧
     (SocialWelfareFunction.WeakPref F P y x ↔
      SocialWelfareFunction.WeakPref F Q y x)) :=
  (h.apply P Q x y hxy).1

theorem strict
    (h : IIA F)
    (P Q : Profile V A) (x y : A)
    (hxy : PairwiseAgreesOn P Q x y) :
    (SocialWelfareFunction.StrictPref F P x y ↔
      SocialWelfareFunction.StrictPref F Q x y) ∧
    (SocialWelfareFunction.StrictPref F P y x ↔
      SocialWelfareFunction.StrictPref F Q y x) :=
  ⟨(h.apply P Q x y hxy).2.1, (h.apply P Q x y hxy).2.2⟩

end IIA

/--
Pareto on an agenda `X`: unanimous strict preference for `x` over `y` among the
voters implies the same strict social preference whenever `x,y ∈ X`.
-/
def ParetoOn
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) (X : Finset A) : Prop :=
  ∀ x y, x ∈ X → y ∈ X → ∀ P : Profile V A,
    (∀ i : V, Profile.StrictPref P i x y) →
      SocialWelfareFunction.StrictPref F P x y

/-- Compatibility alias emphasising that Pareto is phrased via strict preference. -/
abbrev StrictParetoOn
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) (X : Finset A) : Prop :=
  ParetoOn F X

namespace StrictParetoOn

variable {V : Type u} {A : Type v} {F : SocialWelfareFunction V A} {X : Finset A}

theorem apply
    (h : StrictParetoOn F X)
    (P : Profile V A) {x y : A}
    (hx : x ∈ X) (hy : y ∈ X)
    (hxy : ∀ i : V, Profile.StrictPref P i x y) :
    SocialWelfareFunction.StrictPref F P x y :=
  h x y hx hy P hxy

end StrictParetoOn

/--
IIA on an agenda `X`: pairwise agreement on `x` versus `y` across all voters
forces the same pairwise social order whenever `x,y ∈ X`.
-/
def IIAOn
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) (X : Finset A) : Prop :=
  ∀ (P Q : Profile V A) (x y : A),
    x ∈ X → y ∈ X →
    PairwiseAgreesOn P Q x y →
    SameOrder (F P) (F Q) x y x y

/--
Voter `i` is a dictator on an agenda `X` if, for every pair in `X`, their
strict ranking is always inherited by society.
-/
def IsDictatorOn
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) (X : Finset A) (i : V) : Prop :=
  ∀ (P : Profile V A) (x y : A),
    x ∈ X → y ∈ X →
    Profile.StrictPref P i x y →
      SocialWelfareFunction.StrictPref F P x y

/-- A social welfare function is dictatorial on `X` if some voter dictates it on `X`. -/
def DictatorialOn
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) (X : Finset A) : Prop :=
  ∃ i : V, IsDictatorOn F X i

namespace ParetoOn

variable {V : Type u} {A : Type v} {F : SocialWelfareFunction V A} {X : Finset A}

theorem apply
    (h : ParetoOn F X)
    (P : Profile V A) {x y : A}
    (hx : x ∈ X) (hy : y ∈ X)
    (hxy : ∀ i : V, Profile.StrictPref P i x y) :
    SocialWelfareFunction.StrictPref F P x y :=
  h x y hx hy P hxy

end ParetoOn

namespace IIAOn

variable {V : Type u} {A : Type v} {F : SocialWelfareFunction V A} {X : Finset A}

theorem apply
    (h : IIAOn F X)
    (P Q : Profile V A) (x y : A)
    (hx : x ∈ X) (hy : y ∈ X)
    (hxy : PairwiseAgreesOn P Q x y) :
    SameOrder (F P) (F Q) x y x y :=
  h P Q x y hx hy hxy

end IIAOn

/--
Voter `i` is a dictator for the social welfare function `F` if, for every
profile, whenever `i` strictly prefers `x` to `y`, society also strictly
prefers `x` to `y`.
-/
def IsDictatorSWF
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) (i : V) : Prop :=
  ∀ (P : Profile V A) (x y : A),
    Profile.StrictPref P i x y →
    SocialWelfareFunction.StrictPref F P x y

/-- A social welfare function is dictatorial if some voter is a dictator. -/
def DictatorialSWF
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) : Prop :=
  ∃ i : V, IsDictatorSWF F i

namespace IsDictatorSWF

variable {V : Type u} {A : Type v}
variable {F : SocialWelfareFunction V A} {i : V}

theorem apply
    (h : IsDictatorSWF F i)
    (P : Profile V A) (x y : A)
    (hxy : Profile.StrictPref P i x y) :
    SocialWelfareFunction.StrictPref F P x y :=
  h P x y hxy

theorem toOn
    {X : Finset A}
    (h : IsDictatorSWF F i) :
    IsDictatorOn F X i := by
  intro P x y hx hy hxy
  exact h P x y hxy

end IsDictatorSWF

namespace DictatorialSWF

variable {V : Type u} {A : Type v} {F : SocialWelfareFunction V A}

theorem witness
    (h : DictatorialSWF F) :
    ∃ i : V, IsDictatorSWF F i :=
  h

theorem toOn
    {X : Finset A}
    (h : DictatorialSWF F) :
    DictatorialOn F X := by
  rcases h with ⟨i, hi⟩
  exact ⟨i, hi.toOn (X := X)⟩

end DictatorialSWF

namespace IsDictatorOn

variable {V : Type u} {A : Type v}
variable {F : SocialWelfareFunction V A} {X : Finset A} {i : V}

theorem apply
    (h : IsDictatorOn F X i)
    (P : Profile V A) {x y : A}
    (hx : x ∈ X) (hy : y ∈ X)
    (hxy : Profile.StrictPref P i x y) :
    SocialWelfareFunction.StrictPref F P x y :=
  h P x y hx hy hxy

end IsDictatorOn

namespace DictatorialOn

variable {V : Type u} {A : Type v} {F : SocialWelfareFunction V A} {X : Finset A}

theorem witness
    (h : DictatorialOn F X) :
    ∃ i : V, IsDictatorOn F X i :=
  h

end DictatorialOn

end SocialChoiceVocabulary

end QuasiOrders
end EcoLean.SocialChoiceTheory
