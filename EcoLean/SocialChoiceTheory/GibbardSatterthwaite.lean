import EcoLean.SocialChoiceTheory.Arrow
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Finset

namespace EcoLean.SocialChoiceTheory

/-!
# Gibbard-Satterthwaite from Arrow

This file derives a strict-ballot version of Gibbard-Satterthwaite 

For interoperability with `EcoLean`, it also exposes forward-facing operations
`prefers`, `weakPref`, and `toPreference` on top of the legacy internal ballot
orientation.
-/

section StrictBallots

variable {ι σ : Type*}
variable [Fintype ι] [DecidableEq ι] [DecidableEq σ]

/--
Strict linear ballots for the Gibbard-Satterthwaite side.

`lt x y` means "`y` is strictly preferred to `x`".
This matches Nipkow's orientation.

For interoperability with `EcoLean`, prefer the derived forward relation
`LinBallot.prefers x y`.
-/
structure LinBallot (σ : Type*) where
  lt : σ → σ → Prop
  irrefl : ∀ x : σ, ¬ lt x x
  trans : ∀ ⦃x y z : σ⦄, lt x y → lt y z → lt x z
  total : ∀ ⦃x y : σ⦄, x ≠ y → lt x y ∨ lt y x

namespace LinBallot

/-- Forward strict preference associated to a Nipkow-style ballot. -/
def prefers (L : LinBallot σ) (x y : σ) : Prop :=
  L.lt y x

/-- Forward weak preference associated to a strict ballot. -/
def weakPref (L : LinBallot σ) (x y : σ) : Prop :=
  x = y ∨ L.prefers x y

/--
Preferred forward-facing preference associated to a strict ballot.

This is the forward-facing translation that should be used for interoperability:
`x ≽ y` means that `x` is weakly preferred to `y`.
-/
def toPreference (L : LinBallot σ) : Preference σ :=
  Preference.ofPrefOrder
    { rel := L.weakPref
      refl := by
        intro x
        exact Or.inl rfl
      total := by
        intro x y
        by_cases h : x = y
        · exact Or.inl (Or.inl h)
        · rcases L.total h with hxy | hyx
          · exact Or.inr (Or.inr hxy)
          · exact Or.inl (Or.inr hyx)
      trans := by
        intro x y z hxy hyz
        rcases hxy with rfl | hxy
        · exact hyz
        · rcases hyz with rfl | hyz
          · exact Or.inr hxy
          · exact Or.inr (L.trans hyz hxy) }

/--
Legacy weak-order translation matching the internal `lt` orientation.

Prefer `toPreference` for new code that wants the same forward weak-preference
semantics as `EcoLean`.
-/
def toPrefOrder (L : LinBallot σ) : PrefOrder σ where
  rel x y := x = y ∨ L.lt x y
  refl x := Or.inl rfl
  total x y := by
    by_cases h : x = y
    · exact Or.inl (Or.inl h)
    · rcases L.total h with hxy | hyx
      · exact Or.inl (Or.inr hxy)
      · exact Or.inr (Or.inr hyx)
  trans := by
    intro x y z hxy hyz
    rcases hxy with rfl | hxy
    · exact hyz
    · rcases hyz with rfl | hyz
      · exact Or.inr hxy
      · exact Or.inr (L.trans hxy hyz)

lemma toPrefOrder_strict_iff (L : LinBallot σ) {x y : σ} :
    StrictPref (toPrefOrder L) x y ↔ L.lt x y := by
  constructor
  · intro h
    rcases h with ⟨hxy, hyx⟩
    rcases hxy with hEq | hlt
    · subst hEq
      exfalso
      exact hyx (Or.inl rfl)
    · exact hlt
  · intro h
    constructor
    · exact Or.inr h
    · intro hyx
      rcases hyx with hEq | hlt
      · subst hEq
        exact L.irrefl _ h
      · exact L.irrefl _ (L.trans h hlt)

lemma toPreference_strictPref_iff (L : LinBallot σ) {x y : σ} :
    Preference.StrictPref (L.toPreference) x y ↔ L.prefers x y := by
  constructor
  · intro h
    rcases h with ⟨hxy, hyx⟩
    rcases hxy with hEq | hlt
    · subst hEq
      exfalso
      exact hyx (Or.inl rfl)
    · exact hlt
  · intro h
    constructor
    · exact Or.inr h
    · intro hyx
      rcases hyx with hEq | hlt
      · subst hEq
        exact L.irrefl _ h
      · exact L.irrefl _ (L.trans hlt h)

lemma toPreference_eq_or_prefers (L : LinBallot σ) (x y : σ) :
    Preference.weakPref (L.toPreference) x y ↔ x = y ∨ L.prefers x y := by
  rfl

lemma toPrefOrder_eq_or_lt (L : LinBallot σ) (x y : σ) :
    L.toPrefOrder x y ↔ x = y ∨ L.lt x y := by
  rfl

end LinBallot

/-- Preferred name for profiles of strict ballots. -/
abbrev StrictProfile (ι σ : Type*) := ι → LinBallot σ

/-- Preferred name for strict-ballot social choice functions. -/
abbrev StrictSocialChoiceFunction (ι σ : Type*) := StrictProfile ι σ → σ

def ChoosesFrom (g : StrictSocialChoiceFunction ι σ) (X : Finset σ) : Prop :=
  ∀ P : StrictProfile ι σ, g P ∈ X

def OntoOn (g : StrictSocialChoiceFunction ι σ) (X : Finset σ) : Prop :=
  ∀ a, a ∈ X → ∃ P : StrictProfile ι σ, g P = a

/-- Update one voter in a strict profile. -/
def strictProfileUpdate
    (P : StrictProfile ι σ) (i : ι) (L : LinBallot σ) : StrictProfile ι σ :=
  fun j => if j = i then L else P j

def Manipulable (g : StrictSocialChoiceFunction ι σ) (X : Finset σ) : Prop :=
  ∃ P : StrictProfile ι σ, ∃ i : ι, ∃ L : LinBallot σ,
    let P' := strictProfileUpdate P i L
    g P ∈ X ∧ g P' ∈ X ∧
    g P ≠ g P' ∧
    (P i).lt (g P) (g P')

def NonManipulable (g : StrictSocialChoiceFunction ι σ) (X : Finset σ) : Prop :=
  ¬ Manipulable g X

/--
Choice dictatorship on the strict-ballot side:
the chosen alternative is top-ranked by voter `i` among all alternatives in `X`.
-/
def IsChoiceDictatorship (g : StrictSocialChoiceFunction ι σ) (X : Finset σ) : Prop :=
  ∃ i : ι, ∀ P : StrictProfile ι σ, ∀ a : σ,
    a ∈ X → a ≠ g P → (P i).lt a (g P)

/-- Coerce a strict-ballot profile to the weak-order profile used by `SocialWelfareFunction`. -/
def weakProfileOf (P : StrictProfile ι σ) : Profile ι σ :=
  fun i => (P i).toPreference

namespace StrictProfile

/--
Strict profiles `P` and `Q` agree on the pair `(x,y)` when each voter's
forward-facing weak preference induces the same pairwise order on that pair.
-/
def PairwiseAgreesOn
    (P Q : StrictProfile ι σ) (x y : σ) : Prop :=
  ∀ i : ι, SameOrder ((P i).toPreference) ((Q i).toPreference) x y x y

namespace PairwiseAgreesOn

variable {P Q : StrictProfile ι σ} {x y : σ}

omit [Fintype ι] [DecidableEq ι] in
theorem apply
    (h : PairwiseAgreesOn P Q x y) (i : ι) :
    SameOrder ((P i).toPreference) ((Q i).toPreference) x y x y :=
  h i

omit [Fintype ι] [DecidableEq ι] in
theorem swap
    (h : PairwiseAgreesOn P Q x y) :
    PairwiseAgreesOn P Q y x := by
  intro i
  rcases h i with ⟨⟨hxy, hyx⟩, hstrictxy, hstrictyx⟩
  exact ⟨⟨hyx, hxy⟩, hstrictyx, hstrictxy⟩

end PairwiseAgreesOn

end StrictProfile

end StrictBallots

section Top

variable {σ : Type*} [DecidableEq σ]

/--
Move every element of `S` to the top of the strict ballot, preserving
the relative order within `S` and within its complement.
-/
noncomputable def topifyLin (S : Finset σ) (L : LinBallot σ) : LinBallot σ where
  lt x y :=
    if x ∈ S then
      if y ∈ S then L.lt x y else False
    else
      if y ∈ S then True else L.lt x y
  irrefl := by
    intro x
    by_cases hx : x ∈ S <;> simp [hx, L.irrefl x]
  trans := by
    intro x y z
    by_cases hx : x ∈ S
    · by_cases hy : y ∈ S
      · by_cases hz : z ∈ S
        · simp [hx, hy, hz]
          intro hxy hyz
          exact L.trans hxy hyz
        · simp [hx, hy, hz]
      · by_cases hz : z ∈ S
        · simp [hx, hy, hz]
        · simp [hx, hy, hz]
    · by_cases hy : y ∈ S
      · by_cases hz : z ∈ S
        · simp [hx, hy, hz]
        · simp [hx, hy, hz]
      · by_cases hz : z ∈ S
        · simp [hx, hy, hz]
        · simp [hx, hy, hz]
          intro hxy hyz
          exact L.trans hxy hyz
  total := by
    intro x y hxy
    by_cases hx : x ∈ S
    · by_cases hy : y ∈ S
      · simp [hx, hy]
        exact L.total hxy
      · simp [hx, hy]
    · by_cases hy : y ∈ S
      · simp [hx, hy]
      · simp [hx, hy]
        exact L.total hxy

private lemma topifyLin_mem_mem
    {S : Finset σ} {L : LinBallot σ} {x y : σ}
    (hx : x ∈ S) (hy : y ∈ S) :
    (topifyLin S L).lt x y ↔ L.lt x y := by
  simp [topifyLin, hx, hy]

private lemma topifyLin_not_mem_not_mem
    {S : Finset σ} {L : LinBallot σ} {x y : σ}
    (hx : x ∉ S) (hy : y ∉ S) :
    (topifyLin S L).lt x y ↔ L.lt x y := by
  simp [topifyLin, hx, hy]

private lemma topifyLin_not_mem_mem
    {S : Finset σ} {L : LinBallot σ} {x y : σ}
    (hx : x ∉ S) (hy : y ∈ S) :
    (topifyLin S L).lt x y := by
  simp [topifyLin, hx, hy]

private lemma not_topifyLin_mem_not_mem
    {S : Finset σ} {L : LinBallot σ} {x y : σ}
    (hx : x ∈ S) (hy : y ∉ S) :
    ¬ (topifyLin S L).lt x y := by
  simp [topifyLin, hx, hy]

end Top

section TopProfile

variable {ι σ : Type*} [DecidableEq σ]

noncomputable def topProfile
    (S : Finset σ) (P : StrictProfile ι σ) : StrictProfile ι σ :=
  fun i => topifyLin S (P i)

private lemma topProfile_apply
    (S : Finset σ) (P : StrictProfile ι σ) (i : ι) :
    topProfile S P i = topifyLin S (P i) := rfl

end TopProfile

section NonManipAndMonotonicity

variable {ι σ : Type*}
variable [Fintype ι] [DecidableEq ι] [DecidableEq σ]

omit [Fintype ι] [DecidableEq σ] in
private lemma nonManipulable_iff
    (g : StrictSocialChoiceFunction ι σ) (X : Finset σ) :
    NonManipulable g X ↔
      ∀ P : StrictProfile ι σ, ∀ i : ι, ∀ L : LinBallot σ,
        let P' := strictProfileUpdate P i L
        g P ∈ X → g P' ∈ X → g P ≠ g P' →
          (P i).lt (g P') (g P) ∧ L.lt (g P) (g P') := by
  classical
  constructor
  · intro hnm P i L
    dsimp
    intro hP hP' hneq
    constructor
    · by_contra hnot
      have htot := (P i).total hneq
      rcases htot with hleft | hright
      · exact hnm ⟨P, i, L, hP, hP', hneq, hleft⟩
      · exact hnot hright
    · by_contra hnot
      have hneq' : g (strictProfileUpdate P i L) ≠ g P := by
        intro hEq
        apply hneq
        exact hEq.symm
      have htot := L.total hneq'
      rcases htot with hleft | hright
      · have hrestore : strictProfileUpdate (strictProfileUpdate P i L) i (P i) = P := by
          funext j
          by_cases hji : j = i
          · subst hji
            simp [strictProfileUpdate]
          · simp [strictProfileUpdate, hji]
        apply hnm
        refine ⟨strictProfileUpdate P i L, i, P i, hP', ?_, ?_, ?_⟩
        · simpa [hrestore] using hP
        · simpa [hrestore] using hneq'
        · simpa [strictProfileUpdate, hrestore] using hleft
      · exact hnot hright
  · intro h hman
    rcases hman with ⟨P, i, L, hP, hP', hneq, hlt⟩
    have hback := h P i L hP hP' hneq
    exact (P i).irrefl _ ((P i).trans hlt hback.1)

noncomputable def switchProfile
    [Fintype ι] [DecidableEq ι]
    (P P' : StrictProfile ι σ) (k : ℕ) : StrictProfile ι σ :=
  let e := Fintype.equivFin ι
  fun i =>
    if (e i : ℕ) < k then P' i else P i

set_option linter.unusedSectionVars false in
private lemma switchProfile_zero
    [Fintype ι] [DecidableEq ι]
    (P P' : StrictProfile ι σ) :
    switchProfile P P' 0 = P := by
  classical
  funext i
  simp [switchProfile]

set_option linter.unusedSectionVars false in
private lemma switchProfile_all
    [Fintype ι] [DecidableEq ι]
    (P P' : StrictProfile ι σ) :
    switchProfile P P' (Fintype.card ι) = P' := by
  classical
  funext i
  have hi : (Fintype.equivFin ι i : ℕ) < Fintype.card ι := by
    exact (Fintype.equivFin ι i).is_lt
  simp [switchProfile]

set_option linter.unusedSectionVars false in
private lemma switchProfile_succ
    [Fintype ι] [DecidableEq ι]
    (P P' : StrictProfile ι σ) (k : ℕ)
    (hk : k < Fintype.card ι) :
    ∃ i : ι,
      switchProfile P P' (k + 1) =
        strictProfileUpdate (switchProfile P P' k) i (P' i) := by
  classical
  let e := Fintype.equivFin ι
  let i : ι := e.symm ⟨k, hk⟩
  refine ⟨i, ?_⟩
  funext j
  by_cases hj : j = i
  · subst hj
    have hi_eq : (e i : ℕ) = k := by
      simp [i, e]
    have hi_lt_succ : (e i : ℕ) < k + 1 := by
      rw [hi_eq]
      exact Nat.lt_succ_self k
    have hleft : switchProfile P P' (k + 1) i = P' i := by
      change (if (Fintype.equivFin ι i : ℕ) < k + 1 then P' i else P i) = P' i
      rw [if_pos hi_lt_succ]
    have hright : strictProfileUpdate (switchProfile P P' k) i (P' i) i = P' i := by
      unfold strictProfileUpdate
      simp
    rw [hleft, hright]
  · have hneNat : (e j : ℕ) ≠ k := by
      intro hej
      apply hj
      apply e.injective
      apply Fin.ext
      simpa [i, e] using hej
    have hright :
        strictProfileUpdate (switchProfile P P' k) i (P' i) j = switchProfile P P' k j := by
      unfold strictProfileUpdate
      simp [hj]
    by_cases hlt : (e j : ℕ) < k
    · have hlt_succ : (e j : ℕ) < k + 1 := Nat.lt_succ_of_lt hlt
      have hleft1 : switchProfile P P' (k + 1) j = P' j := by
        change (if (Fintype.equivFin ι j : ℕ) < k + 1 then P' j else P j) = P' j
        rw [if_pos hlt_succ]
      have hleft2 : switchProfile P P' k j = P' j := by
        change (if (Fintype.equivFin ι j : ℕ) < k then P' j else P j) = P' j
        rw [if_pos hlt]
      rw [hleft1, hright, hleft2]
    · have hnotlt' : ¬ ((e j : ℕ) < k + 1) := by
        intro h
        rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
        · exact hlt h'
        · exact hneNat h'
      have hleft1 : switchProfile P P' (k + 1) j = P j := by
        change (if (Fintype.equivFin ι j : ℕ) < k + 1 then P' j else P j) = P j
        rw [if_neg hnotlt']
      have hleft2 : switchProfile P P' k j = P j := by
        change (if (Fintype.equivFin ι j : ℕ) < k then P' j else P j) = P j
        rw [if_neg hlt]
      rw [hleft1, hright, hleft2]

/-- If nobody demotes the current winner, the winner stays the winner. -/
private lemma monotonicity
    (g : StrictSocialChoiceFunction ι σ) (X : Finset σ)
    (hchoose : ChoosesFrom g X)
    (hnm : NonManipulable g X)
    {P P' : StrictProfile ι σ}
    (hmono :
      ∀ i : ι, ∀ a : σ,
        (P i).lt a (g P) →
        (P' i).lt a (g P)) :
    g P' = g P := by
  classical
  have hnm' := (nonManipulable_iff (g := g) (X := X)).mp hnm
  let Q : ℕ → StrictProfile ι σ := fun k => switchProfile P P' k
  have hQ0 : Q 0 = P := by
    funext i
    simp [Q, switchProfile]
  have hQall : Q (Fintype.card ι) = P' := by
    funext i
    have hi : (Fintype.equivFin ι i : ℕ) < Fintype.card ι := by
      exact (Fintype.equivFin ι i).is_lt
    simp [Q, switchProfile, hi]
  have hconst :
      ∀ k, k ≤ Fintype.card ι → g (Q k) = g P := by
    intro k hk
    induction' k with k ih
    · simp [Q, hQ0]
    · have hk' : k < Fintype.card ι := Nat.lt_of_succ_le hk
      rcases switchProfile_succ (P := P) (P' := P') k hk' with ⟨i, hi⟩
      have hi' : Q (k + 1) = strictProfileUpdate (Q k) i (P' i) := by
        simpa [Q] using hi
      rw [hi']
      by_cases hEq : g (Q k) = g (strictProfileUpdate (Q k) i (P' i))
      · rw [hEq.symm, ih (Nat.le_of_lt hk')]
      · have hkEq : g (Q k) = g P := ih (Nat.le_of_lt hk')
        have hmem1 : g (Q k) ∈ X := hchoose (Q k)
        have hmem2 : g (strictProfileUpdate (Q k) i (P' i)) ∈ X := by
          exact hchoose (strictProfileUpdate (Q k) i (P' i))
        have hstrict := hnm' (Q k) i (P' i) hmem1 hmem2 hEq
        have hstrict1 :
            (Q k i).lt (g (strictProfileUpdate (Q k) i (P' i))) (g P) := by
          rw [← hkEq]
          exact hstrict.1
        have hstrict2 :
            (P' i).lt (g P) (g (strictProfileUpdate (Q k) i (P' i))) := by
          rw [← hkEq]
          exact hstrict.2
        have hPi_or_P'i : Q k i = P i ∨ Q k i = P' i := by
          by_cases hklt : (Fintype.equivFin ι i : ℕ) < k
          · right
            simp [Q, switchProfile, hklt]
          · left
            simp [Q, switchProfile, hklt]
        rcases hPi_or_P'i with hOld | hNew
        · have hPi :
              (P i).lt (g (strictProfileUpdate (Q k) i (P' i))) (g P) := by
            simpa [hOld] using hstrict1
          have hPi' :
              (P' i).lt (g (strictProfileUpdate (Q k) i (P' i))) (g P) := by
            exact hmono i (g (strictProfileUpdate (Q k) i (P' i))) hPi
          exfalso
          exact (P' i).irrefl _ ((P' i).trans hstrict2 hPi')
        · have hP'i :
              (P' i).lt (g (strictProfileUpdate (Q k) i (P' i))) (g P) := by
            simpa [hNew] using hstrict1
          exfalso
          exact (P' i).irrefl _ ((P' i).trans hstrict2 hP'i)
  rw [← hQall]
  exact hconst (Fintype.card ι) le_rfl

end NonManipAndMonotonicity

section PairTopHelpers

variable {ι σ : Type*}
variable [Fintype ι] [DecidableEq ι] [DecidableEq σ]

omit [Fintype ι] [DecidableEq ι] in
private lemma topProfile_pair_eq_swap
    (P : StrictProfile ι σ) (a b : σ) :
    topProfile ({a, b} : Finset σ) P = topProfile ({b, a} : Finset σ) P := by
  funext i
  have hswap : ({a, b} : Finset σ) = ({b, a} : Finset σ) := by
    ext x
    simp [or_comm]
  simp [topProfile, hswap]

end PairTopHelpers

section TopUnanimityAndStrictRoute

variable {ι σ : Type*}
variable [Fintype ι] [DecidableEq ι] [DecidableEq σ] [Nonempty ι]

omit [Nonempty ι] in
private lemma top_unanimity
    (g : StrictSocialChoiceFunction ι σ) (X S : Finset σ)
    (hchoose : ChoosesFrom g X)
    (honto : OntoOn g X)
    (hnm : NonManipulable g X)
    (hS : S.Nonempty)
    (hSX : S ⊆ X)
    (P : StrictProfile ι σ) :
    g (topProfile S P) ∈ S := by
  classical
  rcases hS with ⟨a, haS⟩
  have haX : a ∈ X := hSX haS
  rcases honto a haX with ⟨P₀, hP₀⟩
  let Q₀ : StrictProfile ι σ := topProfile S P₀
  let T : StrictProfile ι σ := topProfile S P
  have hQ₀a : g Q₀ = a := by
    have hmono₀ :
        ∀ i : ι, ∀ x : σ,
          (P₀ i).lt x (g P₀) →
          (Q₀ i).lt x (g P₀) := by
      intro i x hx
      rw [hP₀] at hx ⊢
      by_cases hxS : x ∈ S
      · have hiff :
            (Q₀ i).lt x a ↔ (P₀ i).lt x a := by
          simp [Q₀, topProfile, topifyLin_mem_mem hxS haS]
        exact hiff.2 hx
      · have : (Q₀ i).lt x a := by
          simp [Q₀, topProfile, topifyLin_not_mem_mem hxS haS]
        exact this
    have hQQ : g Q₀ = g P₀ := by
      exact monotonicity g X hchoose hnm hmono₀
    rw [hP₀] at hQQ
    exact hQQ
  let R : ℕ → StrictProfile ι σ := fun k => switchProfile Q₀ T k
  have hR0 : R 0 = Q₀ := by
    funext i
    simp [R, switchProfile]
  have hRall : R (Fintype.card ι) = T := by
    funext i
    have hi : (Fintype.equivFin ι i : ℕ) < Fintype.card ι := by
      exact (Fintype.equivFin ι i).is_lt
    simp [R, switchProfile, hi]
  have hmem :
      ∀ k, k ≤ Fintype.card ι → g (R k) ∈ S := by
    intro k hk
    induction' k with k ih
    · simpa [hR0, hQ₀a] using haS
    · have hk' : k < Fintype.card ι := Nat.lt_of_succ_le hk
      rcases switchProfile_succ (P := Q₀) (P' := T) k hk' with ⟨i, hi⟩
      have hi' : R (k + 1) = strictProfileUpdate (R k) i (T i) := by
        simpa [R] using hi
      rw [hi']
      by_cases hEq : g (R k) = g (strictProfileUpdate (R k) i (T i))
      · rw [hEq.symm]
        exact ih (Nat.le_of_lt hk')
      · have holdS : g (R k) ∈ S := ih (Nat.le_of_lt hk')
        by_cases hnewS : g (strictProfileUpdate (R k) i (T i)) ∈ S
        · exact hnewS
        · have hmem1 : g (R k) ∈ X := hchoose (R k)
          have hmem2 : g (strictProfileUpdate (R k) i (T i)) ∈ X := by
            exact hchoose (strictProfileUpdate (R k) i (T i))
          have hstrict :=
            ((nonManipulable_iff (g := g) (X := X)).mp hnm)
              (R k) i (T i) hmem1 hmem2 hEq
          have htop :
              (T i).lt (g (strictProfileUpdate (R k) i (T i))) (g (R k)) := by
            simpa [T, topProfile] using
              (topifyLin_not_mem_mem
                (S := S) (L := P i)
                (x := g (strictProfileUpdate (R k) i (T i)))
                (y := g (R k))
                hnewS holdS)
          exfalso
          exact (T i).irrefl _ ((T i).trans hstrict.2 htop)
  have hfinal : g (R (Fintype.card ι)) ∈ S := hmem (Fintype.card ι) le_rfl
  simpa [T, hRall] using hfinal

set_option linter.unusedSectionVars false in
private lemma swf_binary_choice_mem_pair
    (g : StrictSocialChoiceFunction ι σ) (X : Finset σ)
    (hchoose : ChoosesFrom g X)
    (honto : OntoOn g X)
    (hnm : NonManipulable g X)
    (P : StrictProfile ι σ) (a b : σ)
    (ha : a ∈ X) (hb : b ∈ X) :
    g (topProfile ({a, b} : Finset σ) P) ∈ ({a, b} : Finset σ) := by
  apply top_unanimity g X ({a, b} : Finset σ) hchoose honto hnm
  · simp
  · intro x hx
    simp [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb

/--
Forward strict social comparison induced by the pair-top construction.

`socialPrefers g P x y` means that after moving `{x, y}` to the top, the choice
function picks `x`, so `x` is socially ranked above `y`.
-/
def socialPrefers
    (g : StrictSocialChoiceFunction ι σ)
    (P : StrictProfile ι σ) : σ → σ → Prop :=
  fun x y => x ≠ y ∧ g (topProfile ({x, y} : Finset σ) P) = x

namespace StrictSocialRelation

/-- Pareto on strict-ballot profiles, phrased in the forward `prefers` language. -/
def ParetoOn
    (f : StrictProfile ι σ → σ → σ → Prop) (X : Finset σ) : Prop :=
  ∀ x y, x ∈ X → y ∈ X → ∀ P : StrictProfile ι σ,
    (∀ i : ι, (P i).prefers x y) → f P x y

/--
IIA on strict-ballot profiles: agreement on the forward-facing ballot views for
`x` versus `y` implies the same strict social verdict on that pair.
-/
def IIAOn
    (f : StrictProfile ι σ → σ → σ → Prop) (X : Finset σ) : Prop :=
  ∀ P Q : StrictProfile ι σ, ∀ x y,
    x ∈ X → y ∈ X →
    StrictProfile.PairwiseAgreesOn P Q x y →
    ((f P x y ↔ f Q x y) ∧
     (f P y x ↔ f Q y x))

/-- Voter `i` dictates a strict social relation on `X`. -/
def IsDictatorOn
    (f : StrictProfile ι σ → σ → σ → Prop) (X : Finset σ) (i : ι) : Prop :=
  ∀ P : StrictProfile ι σ, ∀ x y : σ,
    x ∈ X → y ∈ X →
    (f P x y ↔ (P i).prefers x y)

/-- Some voter dictates the strict social relation on `X`. -/
def DictatorialOn
    (f : StrictProfile ι σ → σ → σ → Prop) (X : Finset σ) : Prop :=
  ∃ i : ι, IsDictatorOn f X i

namespace ParetoOn

omit [Fintype ι] [DecidableEq ι] [DecidableEq σ] [Nonempty ι] in
theorem apply
    {f : StrictProfile ι σ → σ → σ → Prop} {X : Finset σ}
    (h : ParetoOn f X)
    (P : StrictProfile ι σ) {x y : σ}
    (hx : x ∈ X) (hy : y ∈ X)
    (hxy : ∀ i : ι, (P i).prefers x y) :
    f P x y :=
  h x y hx hy P hxy

end ParetoOn

namespace IIAOn

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem apply
    {f : StrictProfile ι σ → σ → σ → Prop} {X : Finset σ}
    (h : IIAOn f X)
    (P Q : StrictProfile ι σ) (x y : σ)
    (hx : x ∈ X) (hy : y ∈ X)
    (hxy : StrictProfile.PairwiseAgreesOn P Q x y) :
    ((f P x y ↔ f Q x y) ∧
     (f P y x ↔ f Q y x)) :=
  h P Q x y hx hy hxy

end IIAOn

namespace IsDictatorOn

omit [Fintype ι] [DecidableEq ι] [DecidableEq σ] [Nonempty ι] in
theorem apply
    {f : StrictProfile ι σ → σ → σ → Prop} {X : Finset σ} {i : ι}
    (h : IsDictatorOn f X i)
    (P : StrictProfile ι σ) {x y : σ}
    (hx : x ∈ X) (hy : y ∈ X) :
    (f P x y ↔ (P i).prefers x y) :=
  h P x y hx hy

end IsDictatorOn

namespace DictatorialOn

omit [Fintype ι] [DecidableEq ι] [DecidableEq σ] [Nonempty ι] in
theorem witness
    {f : StrictProfile ι σ → σ → σ → Prop} {X : Finset σ}
    (h : DictatorialOn f X) :
    ∃ i : ι, IsDictatorOn f X i :=
  h

end DictatorialOn

end StrictSocialRelation

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
private lemma topProfile_pair_strict_iff'
    (P : StrictProfile ι σ) (a b : σ) (i : ι)
    (hab : a ≠ b) :
    (topProfile ({a, b} : Finset σ) P i).lt a b ↔ (P i).lt a b := by
  simpa [topProfile] using
    (topifyLin_mem_mem
      (S := ({a, b} : Finset σ)) (L := P i)
      (x := a) (y := b)
      (by simp [hab]) (by simp))

set_option linter.unusedSectionVars false in
private lemma topProfile_pair_prefers_iff
    (P Q : StrictProfile ι σ) (x y : σ)
    (hxy : StrictProfile.PairwiseAgreesOn P Q x y)
    (hxy_ne : x ≠ y) :
    ∀ i : ι,
      (topProfile ({x, y} : Finset σ) P i).lt y x ↔
      (topProfile ({x, y} : Finset σ) Q i).lt y x := by
  intro i
  have hpref : (P i).lt y x ↔ (Q i).lt y x := by
    have hs := hxy i
    constructor
    · intro h
      have hstrict : Preference.StrictPref ((P i).toPreference) x y := by
        exact (LinBallot.toPreference_strictPref_iff (L := P i) (x := x) (y := y)).2 h
      have hstrict' : Preference.StrictPref ((Q i).toPreference) x y := hs.2.1.mp hstrict
      exact (LinBallot.toPreference_strictPref_iff (L := Q i) (x := x) (y := y)).1 hstrict'
    · intro h
      have hstrict : Preference.StrictPref ((Q i).toPreference) x y := by
        exact (LinBallot.toPreference_strictPref_iff (L := Q i) (x := x) (y := y)).2 h
      have hstrict' : Preference.StrictPref ((P i).toPreference) x y := hs.2.1.mpr hstrict
      exact (LinBallot.toPreference_strictPref_iff (L := P i) (x := x) (y := y)).1 hstrict'
  have htopP :
      (topProfile ({x, y} : Finset σ) P i).lt y x ↔
      (P i).lt y x := by
    simpa [topProfile_pair_eq_swap P y x] using
      (topProfile_pair_strict_iff' P y x i hxy_ne.symm)
  have htopQ :
      (topProfile ({x, y} : Finset σ) Q i).lt y x ↔
      (Q i).lt y x := by
    simpa [topProfile_pair_eq_swap Q y x] using
      (topProfile_pair_strict_iff' Q y x i hxy_ne.symm)
  constructor
  · intro h
    exact htopQ.2 (hpref.mp (htopP.1 h))
  · intro h
    exact htopP.2 (hpref.mpr (htopQ.1 h))

set_option linter.unusedSectionVars false in
private lemma binary_top_choice_eq_left
    (g : StrictSocialChoiceFunction ι σ) (X : Finset σ)
    (hchoose : ChoosesFrom g X)
    (honto : OntoOn g X)
    (hnm : NonManipulable g X)
    (P : StrictProfile ι σ) (a b : σ)
    (ha : a ∈ X) (_hb : b ∈ X)
    (hall : ∀ i : ι, (P i).lt b a) :
    g (topProfile ({a, b} : Finset σ) P) = a := by
  classical
  let Pa : StrictProfile ι σ := topProfile ({a} : Finset σ) P
  let Pab : StrictProfile ι σ := topProfile ({a, b} : Finset σ) P
  have hPa_mem : g Pa ∈ ({a} : Finset σ) := by
    apply top_unanimity g X ({a} : Finset σ) hchoose honto hnm
    · simp
    · intro x hx
      simp at hx
      subst x
      exact ha
  have hPa_eq : g Pa = a := by
    simpa [Pa] using hPa_mem
  have hmono :
      ∀ i : ι, ∀ x : σ,
        (Pa i).lt x (g Pa) →
        (Pab i).lt x (g Pa) := by
    intro i x hx
    rw [hPa_eq] at hx ⊢
    by_cases hxa : x = a
    · subst x
      exact False.elim ((Pa i).irrefl _ hx)
    · by_cases hxb : x = b
      · subst x
        have hiff :
            (Pab i).lt b a ↔ (P i).lt b a := by
          simpa [Pa, Pab, topProfile] using
            (topifyLin_mem_mem
              (S := ({a, b} : Finset σ)) (L := P i)
              (x := b) (y := a)
              (by simp) (by simp))
        exact hiff.2 (hall i)
      · have hx_not_ab : x ∉ ({a, b} : Finset σ) := by
          simp [hxa, hxb]
        have : (Pab i).lt x a := by
          simpa [Pab, topProfile] using
            (topifyLin_not_mem_mem
              (S := ({a, b} : Finset σ)) (L := P i)
              (x := x) (y := a)
              hx_not_ab (by simp))
        exact this
  have hEq : g Pab = g Pa := by
    exact monotonicity g X hchoose hnm hmono
  rw [hPa_eq] at hEq
  simpa [Pab] using hEq

private lemma socialPrefers_pareto
    (g : StrictSocialChoiceFunction ι σ) (X : Finset σ)
    (hchoose : ChoosesFrom g X)
    (honto : OntoOn g X)
    (hnm : NonManipulable g X) :
    StrictSocialRelation.ParetoOn (socialPrefers g) X := by
  classical
  intro x y hx hy P hall
  have i0 : ι := Classical.choice ‹Nonempty ι›
  have hxy_ne : x ≠ y := by
    intro hEq
    subst hEq
    exact (P i0).irrefl _ (by simpa [LinBallot.prefers] using hall i0)
  refine ⟨hxy_ne, ?_⟩
  exact binary_top_choice_eq_left g X hchoose honto hnm P x y hx hy <| by
    intro i
    simpa [LinBallot.prefers] using hall i

private lemma socialPrefers_iia
    (g : StrictSocialChoiceFunction ι σ) (X : Finset σ)
    (hchoose : ChoosesFrom g X)
    (_honto : OntoOn g X)
    (hnm : NonManipulable g X) :
    StrictSocialRelation.IIAOn (socialPrefers g) X := by
  classical
  intro P Q x y hx hy hxy
  have hiff :
      ∀ a b : σ,
        a ∈ X → b ∈ X →
        StrictProfile.PairwiseAgreesOn P Q a b →
        (socialPrefers g P a b ↔ socialPrefers g Q a b) := by
    intro a b ha hb hab
    by_cases hEq : a = b
    · subst hEq
      constructor <;> intro h <;> exact False.elim (h.1 rfl)
    · let S : Finset σ := ({a, b} : Finset σ)
      constructor
      · intro habP
        rcases habP with ⟨hab_ne, hchoiceP⟩
        refine ⟨hab_ne, ?_⟩
        have hpair :
            ∀ i : ι,
              (topProfile S P i).lt b a ↔
              (topProfile S Q i).lt b a := by
          intro i
          simpa [S] using topProfile_pair_prefers_iff P Q a b hab hEq i
        have hmono :
            ∀ i : ι, ∀ t : σ,
              (topProfile S P i).lt t (g (topProfile S P)) →
              (topProfile S Q i).lt t (g (topProfile S P)) := by
          intro i t ht
          rw [hchoiceP] at ht ⊢
          by_cases hta : t = a
          · subst hta
            exact False.elim ((topProfile S P i).irrefl _ ht)
          · by_cases htb : t = b
            · subst htb
              exact (hpair i).mp ht
            · have ht_not_S : t ∉ S := by
                simp [S, hta, htb]
              have : (topProfile S Q i).lt t a := by
                have ha_in_S : a ∈ S := by
                  simp [S]
                simpa [S, topProfile] using
                  (topifyLin_not_mem_mem
                    (S := S) (L := Q i)
                    (x := t) (y := a)
                    ht_not_S ha_in_S)
              exact this
        have hchoiceEq : g (topProfile S Q) = g (topProfile S P) := by
          exact monotonicity g X hchoose hnm
            (P := topProfile S P)
            (P' := topProfile S Q) hmono
        rw [hchoiceP] at hchoiceEq
        simpa [S] using hchoiceEq
      · intro habQ
        rcases habQ with ⟨hab_ne, hchoiceQ⟩
        refine ⟨hab_ne, ?_⟩
        have hpair :
            ∀ i : ι,
              (topProfile S Q i).lt b a ↔
              (topProfile S P i).lt b a := by
          intro i
          have htmp :
              (topProfile S P i).lt b a ↔
              (topProfile S Q i).lt b a := by
            simpa [S] using topProfile_pair_prefers_iff P Q a b hab hEq i
          exact htmp.symm
        have hmono :
            ∀ i : ι, ∀ t : σ,
              (topProfile S Q i).lt t (g (topProfile S Q)) →
              (topProfile S P i).lt t (g (topProfile S Q)) := by
          intro i t ht
          rw [hchoiceQ] at ht ⊢
          by_cases hta : t = a
          · subst hta
            exact False.elim ((topProfile S Q i).irrefl _ ht)
          · by_cases htb : t = b
            · subst htb
              exact (hpair i).mp ht
            · have ht_not_S : t ∉ S := by
                simp [S, hta, htb]
              have : (topProfile S P i).lt t a := by
                have ha_in_S : a ∈ S := by
                  simp [S]
                simpa [S, topProfile] using
                  (topifyLin_not_mem_mem
                    (S := S) (L := P i)
                    (x := t) (y := a)
                    ht_not_S ha_in_S)
              exact this
        have hchoiceEq : g (topProfile S P) = g (topProfile S Q) := by
          exact monotonicity g X hchoose hnm
            (P := topProfile S Q)
            (P' := topProfile S P) hmono
        rw [hchoiceQ] at hchoiceEq
        simpa [S] using hchoiceEq
  exact ⟨hiff x y hx hy hxy, hiff y x hy hx (StrictProfile.PairwiseAgreesOn.swap hxy)⟩

set_option linter.unusedSectionVars false in
private lemma socialPrefers_dictatorial_implies_choice_dictator
    (g : StrictSocialChoiceFunction ι σ) (X : Finset σ)
    (hchoose : ChoosesFrom g X)
    (_honto : OntoOn g X)
    (hnm : NonManipulable g X)
    (hdict : StrictSocialRelation.DictatorialOn (socialPrefers g) X) :
    IsChoiceDictatorship g X := by
  classical
  rcases hdict with ⟨i, hdict_i⟩
  refine ⟨i, ?_⟩
  intro P y hyX hyNe
  set q : σ := y with hq

  let w : σ := g P
  let S : Finset σ := insert w ({q} : Finset σ)
  let T : Finset σ := insert q ({w} : Finset σ)

  have hqX : q ∈ X := by
    simpa [hq] using hyX

  have hqNe : q ≠ g P := by
    simpa [hq] using hyNe

  have hwX : w ∈ X := hchoose P

  have hwq_ne : w ≠ q := by
    intro h
    apply hqNe
    simpa [w] using h.symm

  have hS_w : w ∈ S := by
    simp [S]

  have hS_q : q ∈ S := by
    simp [S]

  have hT_eq_S : T = S := by
    ext u
    simp [S, T, or_comm]

  have htopchoice : g (topProfile S P) = w := by
    have hmono :
        ∀ j : ι, ∀ t : σ,
          (P j).lt t w →
          (topProfile S P j).lt t w := by
      intro j t ht
      by_cases htw : t = w
      · subst htw
        exact False.elim ((P j).irrefl _ ht)
      · by_cases htq : t = q
        · subst htq
          have hiff :
              (topProfile S P j).lt q w ↔ (P j).lt q w := by
            simpa [S, topProfile] using
              (topifyLin_mem_mem
                (S := S) (L := P j)
                (x := q) (y := w)
                hS_q hS_w)
          exact hiff.2 ht
        · have ht_not_S : t ∉ S := by
            simp [S, htw, htq]
          have : (topProfile S P j).lt t w := by
            simpa [S, topProfile] using
              (topifyLin_not_mem_mem
                (S := S) (L := P j)
                (x := t) (y := w)
                ht_not_S hS_w)
          exact this
    exact monotonicity g X hchoose hnm
      (P := P) (P' := topProfile S P) hmono

  have hqw_choice : g (topProfile T P) = w := by
    simpa [hT_eq_S] using htopchoice

  have hqw_choice' : g (topProfile ({w, q} : Finset σ) P) = w := by
    simpa [T, topProfile_pair_eq_swap P q w] using hqw_choice

  have hsocial : socialPrefers g P w q := by
    simpa [socialPrefers] using And.intro hwq_ne hqw_choice'

  have hdict_wq : (socialPrefers g P w q ↔ (P i).prefers w q) := by
    exact hdict_i P w q hwX hqX

  simpa [LinBallot.prefers, q, w] using hdict_wq.mp hsocial

theorem gibbardSatterthwaite
    (g : StrictSocialChoiceFunction ι σ) (X : Finset σ)
    (hchoose : ChoosesFrom g X)
    (honto : OntoOn g X)
    (hnm : NonManipulable g X)
    (_hX : 3 ≤ X.card)
    (harrow :
      StrictSocialRelation.ParetoOn (socialPrefers g) X →
      StrictSocialRelation.IIAOn (socialPrefers g) X →
      StrictSocialRelation.DictatorialOn (socialPrefers g) X) :
    IsChoiceDictatorship g X := by
  have hPareto : StrictSocialRelation.ParetoOn (socialPrefers g) X :=
    socialPrefers_pareto g X hchoose honto hnm
  have hIIA : StrictSocialRelation.IIAOn (socialPrefers g) X :=
    socialPrefers_iia g X hchoose honto hnm
  have hDict : StrictSocialRelation.DictatorialOn (socialPrefers g) X :=
    harrow hPareto hIIA
  exact socialPrefers_dictatorial_implies_choice_dictator g X hchoose honto hnm hDict

end TopUnanimityAndStrictRoute

end EcoLean.SocialChoiceTheory
