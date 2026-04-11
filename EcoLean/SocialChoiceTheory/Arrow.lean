import EcoLean.SocialChoiceTheory.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open Finset

namespace EcoLean.SocialChoiceTheory

/-!
# Arrow's impossibility theorem

This file formalises a standard proof of Arrow's theorem for a finite set `X`
of alternatives.

The proof strategy is the classical "pivot" route:

1. Define what it means for an alternative `b` to be *strictly worst*,
   *strictly best*, or more generally *extremal* in an ordering.
2. Introduce three order-modification gadgets:
   `maketop`, `makebot`, and `makeabove`.
   These let us manipulate the position of a designated alternative while
   keeping the rest of the pairwise structure unchanged.
3. Formalise the Arrow axioms:
   weak Pareto and independence of irrelevant alternatives.
4. Prove four main steps:
   * `first_step`: if every individual's ranking makes `b` extremal, then
     society must also rank `b` as extremal.
   * `second_step`: for each `b ∈ X`, there is a *pivot voter* for `b`,
     namely a voter whose reversal of `b` from bottom to top forces a social
     reversal from bottom to top.
   * `third_step`: a pivot for `b` is a dictator on every pair of alternatives
     different from `b`.
   * `fourth_step`: if every alternative has a pivot, then one voter is a full
     dictator on all pairs.
5. Conclude Arrow's theorem.

The development uses `Preference σ` from `Basic.lean` for complete and transitive
weak preferences, and `StrictPref` for the associated strict part.
-/

variable {σ ι : Type*}
variable [DecidableEq σ]

variable {x y x' y' a b c : σ} {r r' : Preference σ} {X : Finset σ}

/-! ### Extremal alternatives

For a fixed finite agenda `X`, an alternative `b` is:

* `IsStrictlyWorst b r X` if every other member of `X` is strictly preferred to `b`;
* `IsStrictlyBest b r X` if `b` is strictly preferred to every other member of `X`;
* `IsExtremal b r X` if it is either strictly worst or strictly best.

The later proof uses extremality because the pivot construction toggles an
alternative `b` from one extreme to the other.
-/

def IsStrictlyWorst (b : σ) (r : Preference σ) (X : Finset σ) : Prop :=
  ∀ a ∈ X, a ≠ b → StrictPref r a b

def IsStrictlyBest (b : σ) (r : Preference σ) (X : Finset σ) : Prop :=
  ∀ a ∈ X, a ≠ b → StrictPref r b a

def IsExtremal (b : σ) (r : Preference σ) (X : Finset σ) : Prop :=
  IsStrictlyWorst b r X ∨ IsStrictlyBest b r X

/-!
The next three lemmas unpack the negations of these notions.

Mathematically:
* `¬ IsStrictlyWorst b r X` means there is some `a ≠ b` in `X` such that
  `a` is **not** strictly above `b`.
* `¬ IsStrictlyBest b r X` means there is some `c ≠ b` in `X` such that
  `b` is **not** strictly above `c`.
* Therefore `¬ IsExtremal b r X` yields one witness on each side.

These witnesses are the raw material for producing a nontrivial chain
`a ≽ b ≽ c` in `exists_of_not_extremal`.
-/

omit [DecidableEq σ] in
lemma not_strictlyWorst_iff :
    ¬ IsStrictlyWorst b r X ↔ ∃ a, a ∈ X ∧ a ≠ b ∧ ¬ StrictPref r a b := by
  classical
  simp [IsStrictlyWorst]

omit [DecidableEq σ] in
lemma not_strictlyBest_iff :
    ¬ IsStrictlyBest b r X ↔ ∃ a, a ∈ X ∧ a ≠ b ∧ ¬ StrictPref r b a := by
  classical
  simp [IsStrictlyBest]

omit [DecidableEq σ] in
lemma not_extremal_iff :
    ¬ IsExtremal b r X ↔
      (∃ a, a ∈ X ∧ a ≠ b ∧ ¬ StrictPref r a b) ∧
      (∃ c, c ∈ X ∧ c ≠ b ∧ ¬ StrictPref r b c) := by
  classical
  simp [IsExtremal, not_strictlyWorst_iff, not_strictlyBest_iff]

/-!
Using totality, the preceding strict-failure witnesses can be turned into weak
comparisons. If `a` is not strictly above `b`, totality forces `b ≽ a`; and if
`b` is not strictly above `c`, totality forces `c ≽ b`.

So non-extremality yields a weak "sandwich" `c ≽ b ≽ a`.
-/
omit [DecidableEq σ] in
lemma not_extremal'
    (r : Preference σ) (h : ¬ IsExtremal b r X) :
    ∃ a c, a ∈ X ∧ c ∈ X ∧ a ≠ b ∧ c ≠ b ∧ r b a ∧ r c b := by
  rcases (not_extremal_iff.mp h) with ⟨⟨a, ha, hab, hna⟩, ⟨c, hc, hcb, hnc⟩⟩
  refine ⟨a, c, ha, hc, hab, hcb, ?_, ?_⟩
  · exact rel_of_not_strictPref_total r.total hna
  · exact rel_of_not_strictPref_total r.total hnc

/-!
The next block records that "strictly best" and "strictly worst" are mutually
exclusive whenever there is at least one distinct alternative in the agenda.
The primed forms package the distinct witness using cardinality assumptions.
-/
omit [DecidableEq σ] in
lemma IsStrictlyBest.not_strictlyWorst
    (htop : IsStrictlyBest b r X) (h : ∃ a, a ∈ X ∧ a ≠ b) :
    ¬ IsStrictlyWorst b r X := by
  rcases h with ⟨a, ha, hab⟩
  intro hbot
  exact (hbot a ha hab).2 (htop a ha hab).1

lemma IsStrictlyBest.not_strictlyWorst'
    (htop : IsStrictlyBest b r X) (hX : 2 ≤ X.card) (hb : b ∈ X) :
    ¬ IsStrictlyWorst b r X := by
  exact htop.not_strictlyWorst (Finset.existsSecondDistinctMem hX hb)

omit [DecidableEq σ] in
lemma IsStrictlyWorst.not_strictlyBest
    (hbot : IsStrictlyWorst b r X) (h : ∃ a, a ∈ X ∧ a ≠ b) :
    ¬ IsStrictlyBest b r X := by
  rcases h with ⟨a, ha, hab⟩
  intro htop
  exact (htop a ha hab).2 (hbot a ha hab).1

lemma IsStrictlyWorst.not_strictlyBest'
    (hbot : IsStrictlyWorst b r X) (hX : 2 ≤ X.card) (hb : b ∈ X) :
    ¬ IsStrictlyBest b r X := by
  exact hbot.not_strictlyBest (Finset.existsSecondDistinctMem hX hb)

omit [DecidableEq σ] in
lemma IsExtremal.isStrictlyBest
    (hextr : IsExtremal b r X) (hnw : ¬ IsStrictlyWorst b r X) :
    IsStrictlyBest b r X := by
  rcases hextr with hW | hB
  · exact False.elim (hnw hW)
  · exact hB

omit [DecidableEq σ] in
lemma IsExtremal.isStrictlyWorst
    (hextr : IsExtremal b r X) (hnb : ¬ IsStrictlyBest b r X) :
    IsStrictlyWorst b r X := by
  rcases hextr with hW | hB
  · exact hW
  · exact False.elim (hnb hB)

omit [DecidableEq σ] in
lemma IsStrictlyWorst.isExtremal
    (hbot : IsStrictlyWorst b r X) : IsExtremal b r X := Or.inl hbot

omit [DecidableEq σ] in
lemma IsStrictlyBest.isExtremal
    (htop : IsStrictlyBest b r X) : IsExtremal b r X := Or.inr htop

/-! ### Order-modification gadgets

The functions `maketop`, `makebot`, and `makeabove` are the standard tools in
Arrow proofs for modifying one individual's ranking while leaving other pairwise
comparisons intact.

* `maketop r b` forces `b` to the very top.
* `makebot r b` forces `b` to the very bottom.
* `makeabove r a b` inserts `b` just above the set of alternatives weakly below
  `a`, in particular making `b` strictly above `a`.

The corresponding `*_noteq` lemmas say that away from the distinguished
alternative, the old and new orders agree pairwise.
-/

noncomputable def maketop (r : Preference σ) (b : σ) : Preference σ := by
  classical
  refine Preference.ofPrefOrder {
    rel := fun x y => if x = b then True else if y = b then False else r x y
    refl := ?_
    total := ?_
    trans := ?_ }
  · intro x
    by_cases hx : x = b
    · simp [hx]
    · simp [hx, r.refl x]
  · intro x y
    by_cases hx : x = b <;> by_cases hy : y = b <;> simp [hx, hy, r.total x y]
  · intro x y z
    by_cases hx : x = b <;>
    by_cases hy : y = b <;>
    by_cases hz : z = b <;>
    all_goals simp [hx, hy, hz]
    · intro hxy hyz
      exact r.trans hxy hyz

noncomputable def makebot (r : Preference σ) (b : σ) : Preference σ := by
  classical
  refine Preference.ofPrefOrder {
    rel := fun x y => if y = b then True else if x = b then False else r x y
    refl := ?_
    total := ?_
    trans := ?_ }
  · intro x
    by_cases hx : x = b
    · simp [hx]
    · simp [hx, r.refl x]
  · intro x y
    by_cases hx : x = b <;> by_cases hy : y = b <;> simp [hx, hy, r.total x y]
  · intro x y z
    by_cases hx : x = b <;>
    by_cases hy : y = b <;>
    by_cases hz : z = b <;>
    all_goals simp [hx, hy, hz]
    · intro hxy hyz
      exact r.trans hxy hyz

noncomputable def makeabove (r : Preference σ) (a b : σ) : Preference σ := by
  classical
  let s : σ → σ → Prop := fun x y =>
    if x = b then
      if y = b then True else if r a y then True else False
    else if y = b then
      if r a x then False else True
  else
      r x y
  refine Preference.ofPrefOrder {
    rel := s
    refl := ?_
    total := ?_
    trans := ?_ }
  · intro x
    dsimp [s]
    by_cases hx : x = b
    · simp [hx]
    · simp [hx, r.refl x]
  · intro x y
    dsimp [s]
    by_cases hx : x = b
    · by_cases hy : y = b
      · simp [hx, hy]
      · simp [hx, hy]
        exact Classical.em (r a y)
    · by_cases hy : y = b
      · simp [hx, hy]
        exact (Classical.em (r a x)).symm
      · simp [hx, hy]
        exact r.total x y
  · intro x y z
    dsimp [s]
    by_cases hx : x = b
    · by_cases hy : y = b
      · by_cases hz : z = b
        · simp [hx, hy, hz]
        · simp [hx, hy, hz]
      · by_cases hz : z = b
        · simp [hx, hy, hz]
        · simp [hx, hy, hz]
          intro hxy hyz
          exact r.trans hxy hyz
    · by_cases hy : y = b
      · by_cases hz : z = b
        · simp [hx, hy, hz]
        · simp [hx, hy, hz]
          intro hxy hyz
          rcases r.total x z with hxz | hzx
          · exact hxz
          · exfalso
            exact hxy (r.trans hyz hzx)
      · by_cases hz : z = b
        · simp [hx, hy, hz]
          intro hxy hyz hax
          exact hyz (r.trans hax hxy)
        · simp [hx, hy, hz]
          intro hxy hyz
          exact r.trans hxy hyz

lemma maketop_noteq
    (r : Preference σ) {a b c : σ} (ha : a ≠ b) (hc : c ≠ b) :
    ((maketop r b) a c ↔ r a c) ∧ ((maketop r b) c a ↔ r c a) := by
  simp [maketop, ha, hc]

lemma maketop_noteq'
    (r : Preference σ) {a b c : σ} (ha : a ≠ b) (hc : c ≠ b) :
    (StrictPref (maketop r b) a c ↔ StrictPref r a c) ∧
    (StrictPref (maketop r b) c a ↔ StrictPref r c a) := by
  exact strictPref_iff_of_iff (maketop_noteq r ha hc).1 (maketop_noteq r ha hc).2

lemma makebot_noteq
    (r : Preference σ) {a b c : σ} (ha : a ≠ b) (hc : c ≠ b) :
    ((makebot r b) a c ↔ r a c) ∧ ((makebot r b) c a ↔ r c a) := by
  simp [makebot, ha, hc]

lemma makebot_noteq'
    (r : Preference σ) {a b c : σ} (ha : a ≠ b) (hc : c ≠ b) :
    (StrictPref (makebot r b) a c ↔ StrictPref r a c) ∧
    (StrictPref (makebot r b) c a ↔ StrictPref r c a) := by
  exact strictPref_iff_of_iff (makebot_noteq r ha hc).1 (makebot_noteq r ha hc).2

lemma makeabove_noteq
    (r : Preference σ) (a : σ) {b c d : σ} (hc : c ≠ b) (hd : d ≠ b) :
    ((makeabove r a b) c d ↔ r c d) ∧ ((makeabove r a b) d c ↔ r d c) := by
  simp [makeabove, hc, hd]

lemma makeabove_noteq'
    (r : Preference σ) (a : σ) {b c d : σ} (hc : c ≠ b) (hd : d ≠ b) :
    (StrictPref (makeabove r a b) c d ↔ StrictPref r c d) ∧
    (StrictPref (makeabove r a b) d c ↔ StrictPref r d c) := by
  exact strictPref_iff_of_iff (makeabove_noteq r a hc hd).1 (makeabove_noteq r a hc hd).2

lemma is_strictlyBest_maketop (b : σ) (r : Preference σ) (X : Finset σ) :
    IsStrictlyBest b (maketop r b) X := by
  intro a ha hab
  simp [StrictPref, maketop, hab]

lemma is_strictlyWorst_makebot (b : σ) (r : Preference σ) (X : Finset σ) :
    IsStrictlyWorst b (makebot r b) X := by
  intro a ha hab
  simp [StrictPref, makebot, hab]

lemma makeabove_above {a b : σ} (r : Preference σ) (ha : a ≠ b) :
    StrictPref (makeabove r a b) b a := by
  simpa [StrictPref, makeabove, ha] using r.refl a

lemma makeabove_above' {a b c : σ} {r : Preference σ} (hc : c ≠ b) (hr : r a c) :
    StrictPref (makeabove r a b) b c := by
  simp [StrictPref, makeabove, hc, hr]

lemma makeabove_below {a b c : σ} {r : Preference σ} (hc : c ≠ b) (hr : ¬ r a c) :
    StrictPref (makeabove r a b) c b := by
  simp [StrictPref, makeabove, hc, hr]

/-! ### Profiles, social welfare functions, and Arrow-style properties

A profile is a function assigning each voter a preference.
A social welfare function sends profiles to a social preference.

The axioms are encoded through the shared vocabulary from `Basic.lean`.

* `ParetoOn`: if everyone strictly prefers `x` to `y`, society does too.
* `IIAOn`: if two profiles agree on the pairwise ordering of `x` and `y`
  for every individual, then society also agrees on that pairwise ordering.
* `DictatorialOn`: some voter's strict ranking is always inherited socially.
* `IsPivotal f X i b`: voter `i` can change the social status of `b` from
  strictly worst to strictly best while the other voters keep `b` extremal.
* `IsDictatorExcept f X i b`: voter `i` dictates every pair not involving `b`.
-/

def IsPivotal (f : SocialWelfareFunction ι σ) (X : Finset σ) (i : ι) (b : σ) : Prop :=
  ∃ (R R' : Profile ι σ),
    (∀ j : ι, j ≠ i → ∀ x y, x ∈ X → y ∈ X → R j = R' j) ∧
    (∀ j : ι, IsExtremal b (R j) X) ∧
    (∀ j : ι, IsExtremal b (R' j) X) ∧
    IsStrictlyWorst b (R i) X ∧
    IsStrictlyBest b (R' i) X ∧
    IsStrictlyWorst b (f R) X ∧
    IsStrictlyBest b (f R') X

def HasPivot (f : SocialWelfareFunction ι σ) (X : Finset σ) (b : σ) : Prop :=
  ∃ i, IsPivotal f X i b

def IsDictatorExcept (f : SocialWelfareFunction ι σ) (X : Finset σ) (i : ι) (b : σ) : Prop :=
  ∀ a c, a ∈ X → c ∈ X → a ≠ b → c ≠ b → ∀ R : Profile ι σ,
    StrictPref (R i) c a → StrictPref (f R) c a

variable {R : Profile ι σ} {f : SocialWelfareFunction ι σ}

/-! ### Auxiliary lemmas

These lemmas lift individual extremality to social extremality using weak Pareto,
and extract a useful weak chain from a social order in which `b` is not extremal.
-/

omit [DecidableEq σ] in
theorem is_strictlyBest_of_forall_is_strictlyBest
    (b_in : b ∈ X) (hPareto : ParetoOn f X)
    (htop : ∀ i, IsStrictlyBest b (R i) X) :
    IsStrictlyBest b (f R) X := by
  intro a ha hab
  exact hPareto b a b_in ha R (fun i => htop i a ha hab)

omit [DecidableEq σ] in
theorem is_strictlyWorst_of_forall_is_strictlyWorst
    (b_in : b ∈ X) (hPareto : ParetoOn f X)
    (hbot : ∀ i, IsStrictlyWorst b (R i) X) :
    IsStrictlyWorst b (f R) X := by
  intro a ha hab
  exact hPareto a b ha b_in R (fun i => hbot i a ha hab)

lemma exists_of_not_extremal
    (hX : 3 ≤ X.card) (hb : b ∈ X) (h : ¬ IsExtremal b (f R) X) :
    ∃ a c, a ∈ X ∧ c ∈ X ∧ a ≠ b ∧ c ≠ b ∧ a ≠ c ∧ (f R) a b ∧ (f R) b c := by
  rcases not_extremal' (f R) h with
    ⟨u, v, hu, hv, hub, hvb, hbu, hvb'⟩
  rcases ne_or_eq u v with huv | huv
  · exact ⟨v, u, hv, hu, hvb, hub, huv.symm, hvb', hbu⟩
  · subst v
    rcases Finset.existsThirdDistinctMem hX hu hb hub with ⟨d, hd, hdu, hdb⟩
    rcases (f R).total b d with hbd | hdb'
    · exact ⟨u, d, hu, hd, hub, hdb, hdu.symm, hvb', hbd⟩
    · exact ⟨d, u, hd, hu, hdb, hub, hdu, hdb', hbu⟩

/-!
`worstSet R b X` is the set of voters who rank `b` strictly worst in profile `R`.
The second step of the proof inducts on the size of this set.
-/
noncomputable def worstSet [Fintype ι] [DecidableEq ι]
    (R : Profile ι σ) (b : σ) (X : Finset σ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => IsStrictlyWorst b (R i) X)

/-! ### Step 1: if everyone places `b` at an extreme, so does society

The idea is standard.
Assume every individual makes `b` extremal but society does not.
Then there are distinct `a,c` with a weak social chain `a ≽ b ≽ c`.
Modify every individual's order by inserting `b` relative to `a,c` in a way
that preserves pairwise information away from `b` but forces society to have
`c P a` by Pareto. IIA transports the social weak relations `a ≽ b` and
`b ≽ c` to the new profile, yielding `a ≽ c`, contradiction.
-/

lemma first_step
    (hPareto : ParetoOn f X) (hIIA : IIAOn f X)
    (hX : 3 ≤ X.card) (hb : b ∈ X) (hextr : ∀ i, IsExtremal b (R i) X) :
    IsExtremal b (f R) X := by
  classical
  by_contra hnot
  rcases exists_of_not_extremal hX hb hnot with
    ⟨a, c, ha, hc, hab, hcb, hac, hfab, hfbc⟩
  let R' : Profile ι σ := fun j => makeabove (R j) a c
  have H1 : ∀ {j}, ¬ IsStrictlyWorst b (R j) X → StrictPref (R' j) b c := by
    intro j h
    exact makeabove_below hcb.symm ((hextr j).isStrictlyBest h a ha hab).2
  have H2 : ∀ {j}, ¬ IsStrictlyBest b (R j) X → StrictPref (R' j) c b := by
    intro j h
    exact makeabove_above' hcb.symm ((hextr j).isStrictlyWorst h a ha hab).1
  have hca' : StrictPref (f R') c a := by
    refine hPareto c a hc ha R' ?_
    intro j
    simpa [R', Profile.StrictPref] using makeabove_above (R j) hac
  have h_ab :
      SameOrder (f R) (f R') a b a b := by
    refine hIIA R R' a b ha hb ?_
    intro j
    rcases makeabove_noteq (R j) a (b := c) (c := a) (d := b) hac hcb.symm with ⟨h1, h2⟩
    rcases makeabove_noteq' (R j) a (b := c) (c := a) (d := b) hac hcb.symm with ⟨h3, h4⟩
    exact ⟨⟨h1.symm, h2.symm⟩, h3.symm, h4.symm⟩
  have h_bc :
      SameOrder (f R) (f R') b c b c := by
    refine hIIA R R' b c hb hc ?_
    intro j
    rcases hextr j with hW | hB
    · have hnb : ¬ IsStrictlyBest b (R j) X := by
        exact hW.not_strictlyBest ⟨c, hc, hcb⟩
      exact sameOrder_of_reverse_strict
        (hW c hc hcb)
        (H2 hnb)
    · have hnw : ¬ IsStrictlyWorst b (R j) X := by
        exact hB.not_strictlyWorst ⟨c, hc, hcb⟩
      exact sameOrder_of_strict_strict
        (hB c hc hcb)
        (H1 hnw)
  have hab' : (f R') a b := (h_ab.1.1).mp hfab
  have hbc' : (f R') b c := (h_bc.1.1).mp hfbc
  exact hca'.2 ((f R').trans hab' hbc')

/-!
`r₂ b` is the artificial order with `b` at the very bottom and everything else
weakly tied above it. It supplies the base profile for the pivot-existence
argument.
-/
noncomputable def r₂ (b : σ) : Preference σ := by
  classical
  refine Preference.ofPrefOrder {
    rel := fun x y => if y = b then True else if x = b then False else True
    refl := ?_
    total := ?_
    trans := ?_ }
  · intro x
    by_cases hx : x = b <;> simp [hx]
  · intro x y
    by_cases hx : x = b <;> by_cases hy : y = b <;> simp [hx, hy]
  · intro x y z
    by_cases hx : x = b <;>
    by_cases hy : y = b <;>
    by_cases hz : z = b <;>
    simp [hx, hy, hz]

/-! ### Step 2: existence of a pivot for each alternative `b`

Induct on the set of voters who rank `b` strictly worst. Starting from the
profile `R0` where everyone ranks `b` worst, we flip voters one by one from
`b`-worst to `b`-best using `maketop`. The first voter whose flip makes society
switch from `b`-worst to `b`-best is the pivot.
-/

lemma second_step_aux [Fintype ι] [DecidableEq ι]
    (hPareto : ParetoOn f X) (hIIA : IIAOn f X)
    (hX : 2 < X.card) (b_in : b ∈ X) {D' : Finset ι} :
    ∀ {R : Profile ι σ},
      D' = worstSet R b X →
      (∀ i, IsExtremal b (R i) X) →
      IsStrictlyWorst b (f R) X →
      HasPivot f X b := by
  classical
  intro R hD hextr hbot
  induction D' using Finset.induction_on generalizing R with
  | empty =>
      have hallBest : ∀ j, IsStrictlyBest b (R j) X := by
        intro j
        have hj : j ∉ worstSet R b X := by
          simpa [hD] using (Finset.eq_empty_iff_forall_notMem.mp hD.symm j)
        exact (hextr j).isStrictlyBest (by
          intro hW
          exact hj (by simp [worstSet, hW]))
      have htopSoc : IsStrictlyBest b (f R) X :=
        is_strictlyBest_of_forall_is_strictlyBest b_in hPareto hallBest
      exact False.elim ((htopSoc.not_strictlyWorst' hX.le b_in) hbot)
  | @insert i D hi IH =>
      let R' : Profile ι σ := fun j => if j = i then maketop (R j) b else R j
      have hextr' : ∀ j, IsExtremal b (R' j) X := by
        intro j
        by_cases hji : j = i
        · subst hji
          simpa [R'] using (is_strictlyBest_maketop b (R j) X).isExtremal
        · simp [R', hji, hextr j]
      by_cases hR' : IsStrictlyBest b (f R') X
      · refine ⟨i, R, R', ?_, hextr, hextr', ?_, ?_, hbot, hR'⟩
        · intro j hj x y hx hy
          simp [R', hj]
        · have : i ∈ worstSet R b X := by
            rw [← hD]
            exact Finset.mem_insert_self i D
          simpa [worstSet] using this
        · simpa [R'] using is_strictlyBest_maketop b (R i) X
      · have hX3 : 3 ≤ X.card := by
          omega
        refine IH ?_ hextr' ((first_step hPareto hIIA hX3 b_in hextr').isStrictlyWorst hR')
        ext j
        constructor
        · intro hj
          have hjIns : j ∈ insert i D := Finset.mem_insert_of_mem hj
          have hjWorst : j ∈ worstSet R b X := by
            rw [← hD]
            exact hjIns
          by_cases hji : j = i
          · subst hji
            exfalso
            exact hi hj
          · simpa [worstSet, R', hji] using hjWorst
        · intro hj
          by_cases hji : j = i
          · subst hji
            exfalso
            rcases Finset.existsSecondDistinctMem hX.le b_in with ⟨a, ha, hab⟩
            have hjWorst' : IsStrictlyWorst b (R' j) X := by
              simpa [worstSet] using hj
            have htop : IsStrictlyBest b (R' j) X := by
              simpa [R'] using (is_strictlyBest_maketop b (R j) X)
            exact (htop a ha hab).2 (hjWorst' a ha hab).1
          · have hjWorst : j ∈ worstSet R b X := by
              simpa [worstSet, R', hji] using hj
            have hjIns : j ∈ insert i D := by
              rw [hD]
              exact hjWorst
            simpa [Finset.mem_insert, hji] using hjIns

lemma second_step [Fintype ι] [DecidableEq ι]
    (hPareto : ParetoOn f X) (hIIA : IIAOn f X)
    (hX : 3 ≤ X.card) (b : σ) (b_in : b ∈ X) :
    HasPivot f X b := by
  let R0 : Profile ι σ := fun _ => r₂ b
  have hbot_ind : IsStrictlyWorst b (r₂ b) X := by
    intro a ha hab
    simp [r₂, StrictPref, hab]
  have hbot : IsStrictlyWorst b (f R0) X := by
    exact is_strictlyWorst_of_forall_is_strictlyWorst b_in hPareto (fun _ => hbot_ind)
  have hextr : ∀ i, IsExtremal b (R0 i) X := by
    intro i
    exact hbot_ind.isExtremal
  refine second_step_aux
      (D' := worstSet R0 b X)
      hPareto hIIA (by omega) b_in
      (R := R0)
      rfl
      hextr
      hbot

/-! ### Step 3: a pivot voter for `b` dictates all pairs away from `b`

Fix a pivot voter `i` for `b`, and fix two alternatives `a,c ≠ b`.
We build a hybrid profile `Q'`:
* voter `i` places `b` just above `a`,
* every other voter places `b` at the top or bottom depending on whether they
  were in the "worst" part of the pivotal profiles.

IIA transfers pairwise information from the pivotal profiles to `Q'`, and from
the target profile `Q` to `Q'`. This yields social chains forcing society to
follow voter `i` on the pair `(c,a)`.
-/

lemma third_step
    (hIIA : IIAOn f X)
    (b_in : b ∈ X) {i : ι} (i_piv : IsPivotal f X i b) :
    IsDictatorExcept f X i b := by
  classical
  intro a c a_in c_in hab hcb Q hQi
  rcases hQi with ⟨hQca, hQac_not⟩
  rcases i_piv with ⟨R, R', hso, hextr, hextr', hbot_i, htop_i, hbot_soc, htop_soc⟩
  let Q' : Profile ι σ := fun j =>
    if j = i then makeabove (Q j) a b
    else if IsStrictlyWorst b (R j) X then makebot (Q j) b else maketop (Q j) b
  have Q'bot : ∀ j, j ≠ i → IsStrictlyWorst b (R j) X → Q' j = makebot (Q j) b := by
    intro j hj hbot
    simp [Q', hj, hbot]
  have Q'top : ∀ j, j ≠ i → ¬ IsStrictlyWorst b (R j) X → Q' j = maketop (Q j) b := by
    intro j hj hbot
    simp [Q', hj, hbot]
  have Q'above : Q' i = makeabove (Q i) a b := by
    simp [Q']
  have hQ' : ∀ j, SameOrder (Q j) (Q' j) c a c a := by
    intro j
    have hsuff : ∀ d, d ≠ b → ∀ e, e ≠ b → SameOrder (Q j) (Q' j) e d e d := by
      intro d hdb e heb
      by_cases hji : j = i
      · subst hji
        rcases makeabove_noteq (Q j) a (b := b) (c := e) (d := d) heb hdb with ⟨h1, h2⟩
        rcases makeabove_noteq' (Q j) a (b := b) (c := e) (d := d) heb hdb with ⟨h3, h4⟩
        have hEq : Q' j = makeabove (Q j) a b := by
          simp [Q']
        simpa [hEq] using
          (show SameOrder (Q j) (makeabove (Q j) a b) e d e d from
            ⟨⟨h1.symm, h2.symm⟩, h3.symm, h4.symm⟩)
      · by_cases hW : IsStrictlyWorst b (R j) X
        · rcases makebot_noteq (Q j) (a := e) (b := b) (c := d) heb hdb with ⟨h1, h2⟩
          rcases makebot_noteq' (Q j) (a := e) (b := b) (c := d) heb hdb with ⟨h3, h4⟩
          have hEq : Q' j = makebot (Q j) b := Q'bot j hji hW
          simpa [hEq] using
            (show SameOrder (Q j) (makebot (Q j) b) e d e d from
              ⟨⟨h1.symm, h2.symm⟩, h3.symm, h4.symm⟩)
        · rcases maketop_noteq (Q j) (a := e) (b := b) (c := d) heb hdb with ⟨h1, h2⟩
          rcases maketop_noteq' (Q j) (a := e) (b := b) (c := d) heb hdb with ⟨h3, h4⟩
          have hEq : Q' j = maketop (Q j) b := Q'top j hji hW
          simpa [hEq] using
            (show SameOrder (Q j) (maketop (Q j) b) e d e d from
              ⟨⟨h1.symm, h2.symm⟩, h3.symm, h4.symm⟩)
    exact hsuff a hab c hcb
  have h_cb : SameOrder (f R) (f Q') c b c b := by
    refine hIIA R Q' c b c_in b_in ?_
    intro j
    rcases eq_or_ne j i with rfl | hj
    · have hnew : StrictPref (Q' j) c b := by
        simpa [Q'] using (makeabove_below hcb hQac_not)
      exact sameOrder_of_strict_strict (hbot_i c c_in hcb) hnew
    · by_cases hW : IsStrictlyWorst b (R j) X
      · have hnew : StrictPref (Q' j) c b := by
          rw [Q'bot j hj hW]
          exact is_strictlyWorst_makebot b (Q j) X c c_in hcb
        exact sameOrder_of_strict_strict (hW c c_in hcb) hnew
      · have hB : IsStrictlyBest b (R j) X := (hextr j).isStrictlyBest hW
        have hnew : StrictPref (Q' j) b c := by
          rw [Q'top j hj hW]
          exact is_strictlyBest_maketop b (Q j) X c c_in hcb
        exact sameOrder_of_reverse_strict (hB c c_in hcb) hnew
  have h_ba : SameOrder (f R') (f Q') b a b a := by
    refine hIIA R' Q' b a b_in a_in ?_
    intro j
    rcases eq_or_ne j i with rfl | hj
    · have hnew : StrictPref (Q' j) b a := by
        simpa [Q'] using (makeabove_above (Q j) hab)
      exact sameOrder_of_strict_strict (htop_i a a_in hab) hnew
    · have hRj : R j = R' j := hso j hj b a b_in a_in
      by_cases hW : IsStrictlyWorst b (R j) X
      · have hW' : IsStrictlyWorst b (R' j) X := by
          simpa [hRj] using hW
        have hnew : StrictPref (Q' j) a b := by
          rw [Q'bot j hj hW]
          exact is_strictlyWorst_makebot b (Q j) X a a_in hab
        exact sameOrder_of_reverse_strict (hW' a a_in hab) hnew
      · have hB : IsStrictlyBest b (R j) X := (hextr j).isStrictlyBest hW
        have hB' : IsStrictlyBest b (R' j) X := by
          simpa [hRj] using hB
        have hnew : StrictPref (Q' j) b a := by
          rw [Q'top j hj hW]
          exact is_strictlyBest_maketop b (Q j) X a a_in hab
        exact sameOrder_of_strict_strict (hB' a a_in hab) hnew
  have hcb' : StrictPref (f Q') c b := by
    exact (h_cb.2.1).mp (hbot_soc c c_in hcb)
  have hba' : StrictPref (f Q') b a := by
    exact (h_ba.2.1).mp (htop_soc a a_in hab)
  have hca' : StrictPref (f Q') c a := by
    exact strictPref_trans (f Q').trans hcb' hba'
  exact (hIIA Q Q' c a c_in a_in hQ').2.1.mpr hca'

/-! ### Step 4: from one excluded alternative to full dictatorship

Pick any `b ∈ X` and a pivot voter `i` for `b`. Step 3 shows that `i` dictates
all pairs not involving `b`. To bring `b` itself back in, we compare with the
pivot voter for a third alternative `c`, and show that the relevant pivot voter
must in fact be the same `i`. This extends dictatorship to all pairs.
-/

lemma fourth_step
    (hIIA : IIAOn f X)
    (hX : 3 ≤ X.card) (hpiv : ∀ b ∈ X, HasPivot f X b) :
    DictatorialOn f X := by
  classical
  have hXpos : 0 < X.card := by
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hXpos
  obtain ⟨i, i_piv⟩ := hpiv b hb
  have h :
      ∀ a ∈ X, a ≠ b → ∀ Rᵢ : Profile ι σ,
        (StrictPref (Rᵢ i) a b → StrictPref (f Rᵢ) a b) ∧
        (StrictPref (Rᵢ i) b a → StrictPref (f Rᵢ) b a) := by
    intro a ha hab Rᵢ
    rcases Finset.existsThirdDistinctMem hX ha hb hab with ⟨c, hc, hca, hcb⟩
    have hac : a ≠ c := hca.symm
    have hbc : b ≠ c := hcb.symm
    rcases hpiv c hc with ⟨j, j_piv⟩
    have hdict := third_step hIIA hc j_piv
    have hji : j = i := by
      by_contra hne
      rcases i_piv with ⟨R, R', hso, hextr, hextr', hbot_i, htop_i, hbot_soc, htop_soc⟩
      have hEq : R j = R' j := hso j hne a b ha hb
      rcases hextr' j with hW | hB
      · have hja' : StrictPref (R' j) a b := hW a ha hab
        have hsoc : StrictPref (f R') a b := hdict b a hb ha hbc hac R' hja'
        exact (htop_soc a ha hab).2 hsoc.1
      · have hjb' : StrictPref (R' j) b a := hB a ha hab
        have hjb : StrictPref (R j) b a := by
          simpa [hEq] using hjb'
        have hsoc : StrictPref (f R) b a := hdict a b ha hb hac hbc R hjb
        exact (hbot_soc a ha hab).2 hsoc.1
    subst hji
    constructor
    · intro hP
      exact hdict b a hb ha hbc hac Rᵢ hP
    · intro hP
      exact hdict a b ha hb hac hbc Rᵢ hP
  refine ⟨i, ?_⟩
  intro Rᵢ x y hx hy hRᵢ
  rcases eq_or_ne b x with rfl | hbx
  · rcases eq_or_ne b y with rfl | hby
    · exact False.elim (false_of_strictPref_self hRᵢ)
    · exact (h y hy hby.symm Rᵢ).2 hRᵢ
  · rcases eq_or_ne b y with rfl | hby
    · exact (h x hx hbx.symm Rᵢ).1 hRᵢ
    · exact third_step hIIA hb i_piv y x hy hx hby.symm hbx.symm Rᵢ hRᵢ

/-- Arrow's impossibility theorem: weak Pareto + IIA on an agenda with at least
three alternatives implies dictatorship. -/
theorem arrow [Fintype ι] [DecidableEq ι]
    (hPareto : ParetoOn f X) (hIIA : IIAOn f X) (hX : 3 ≤ X.card) :
    DictatorialOn f X := by
  exact fourth_step hIIA hX (second_step hPareto hIIA hX)

end EcoLean.SocialChoiceTheory
