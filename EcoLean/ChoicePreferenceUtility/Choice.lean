import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic

universe u

namespace EcoLean

/--
A choice function on a domain `α`.

For each feasible set `A`, the function returns the set of objects
that the decision maker would be content to choose from `A`.

Following Kreps, the intended domain is the class of nonempty subsets of `α`.
Formally, we define `choose` on all subsets and place the relevant restrictions
in separate predicates.
-/
structure ChoiceFunction (α : Type u) where
  choose : Set α → Set α

namespace ChoiceFunction

@[ext]
theorem ext {α : Type u} {c d : ChoiceFunction α}
    (h : ∀ A : Set α, c.choose A = d.choose A) :
    c = d := by
  cases c with
  | mk f =>
      cases d with
      | mk g =>
          have hfg : f = g := by
            funext A
            exact h A
          simp [hfg]

variable {α : Type u} (c : ChoiceFunction α)

/-! ### Basic admissibility properties of a choice function -/

/--
`c` chooses only from the feasible set.

This is the condition `c(A) ⊆ A`.
-/
def ChoosesFrom : Prop :=
  ∀ (A : Set α), c.choose A ⊆ A

/--
Finite nonemptiness.

Whenever `A` is finite and nonempty, the choice set `c(A)` is nonempty.
-/
def FiniteNonempty : Prop :=
  ∀ ⦃A : Set α⦄, A.Finite → A.Nonempty → (c.choose A).Nonempty

/--
Nonempty-valued choice.

This is stronger than finite nonemptiness: it requires
nonemptiness of `c(A)` for every nonempty feasible set `A`.
-/
def NonemptyValued : Prop :=
  ∀ ⦃A : Set α⦄, A.Nonempty → (c.choose A).Nonempty

/--
Choice coherence.

If two feasible sets `A` and `B` both contain `x` and `y`, and `x` is chosen
from `A` while `y` is not chosen from `A`, then `y` is not chosen from `B`.
-/
def ChoiceCoherent : Prop :=
  ∀ ⦃A B : Set α⦄ ⦃x y : α⦄,
    x ∈ A →
    y ∈ A →
    x ∈ B →
    y ∈ B →
    x ∈ c.choose A →
    y ∉ c.choose A →
    y ∉ c.choose B

/-! ### Immediate consequences of the definitions -/

/-- If `c` chooses only from feasible sets, then every chosen object is feasible. -/
theorem mem_of_mem_choose
    (hFrom : c.ChoosesFrom)
    {A : Set α} {x : α} :
    x ∈ c.choose A → x ∈ A := by
  intro hx
  exact hFrom A hx

/-- If `c` is nonempty-valued, then it is finite-nonempty. -/
theorem finiteNonempty_of_nonemptyValued
    (hNE : c.NonemptyValued) :
    c.FiniteNonempty := by
  intro A hFin hA
  exact hNE hA

/-- Every singleton feasible set has a nonempty choice set under finite nonemptiness. -/
theorem singleton_choice_nonempty
    (hFN : c.FiniteNonempty) (x : α) :
    (c.choose ({x} : Set α)).Nonempty := by
  apply hFN
  · exact Set.finite_singleton x
  · exact ⟨x, by simp⟩

/--
If `c` chooses only from feasible sets and is finite-nonempty,
then `x` is chosen from the singleton set `{x}`.
-/
theorem singleton_choose_eq_singleton
    (hFrom : c.ChoosesFrom)
    (hFN : c.FiniteNonempty)
    (x : α) :
    c.choose ({x} : Set α) = ({x} : Set α) := by
  apply Set.Subset.antisymm
  · exact hFrom ({x} : Set α)
  · intro y hy
    have hNE : (c.choose ({x} : Set α)).Nonempty :=
      singleton_choice_nonempty c hFN x
    rcases hNE with ⟨z, hz⟩
    have hz' : z ∈ ({x} : Set α) := hFrom ({x} : Set α) hz
    have hzEq : z = x := by
      simpa using hz'
    have hyEq : y = x := by
      simpa using hy
    subst hzEq
    subst hyEq
    exact hz

/--
Choice coherence can be used directly to transfer a rejection
from one feasible set to another.
-/
theorem not_mem_choose_of_choiceCoherent
    (hCC : c.ChoiceCoherent)
    {A B : Set α} {x y : α}
    (hxA : x ∈ A) (hyA : y ∈ A)
    (hxB : x ∈ B) (hyB : y ∈ B)
    (hxChooseA : x ∈ c.choose A)
    (hyNotChooseA : y ∉ c.choose A) :
    y ∉ c.choose B := by
  exact hCC hxA hyA hxB hyB hxChooseA hyNotChooseA

/--
Choice coherence can be applied after swapping the role
of the two feasible sets.
-/
theorem not_mem_choose_of_choiceCoherent_swap
    (hCC : c.ChoiceCoherent)
    {A B : Set α} {x y : α}
    (hxA : x ∈ A) (hyA : y ∈ A)
    (hxB : x ∈ B) (hyB : y ∈ B)
    (hxChooseB : x ∈ c.choose B)
    (hyNotChooseB : y ∉ c.choose B) :
    y ∉ c.choose A := by
  exact hCC hxB hyB hxA hyA hxChooseB hyNotChooseB

/--
For any two-element feasible set `{x, y}`, finite nonemptiness implies
that the choice set from `{x, y}` is nonempty.
-/
theorem pair_choice_nonempty
    (hFN : c.FiniteNonempty)
    (x y : α) :
    (c.choose ({x, y} : Set α)).Nonempty := by
  apply hFN
  ·
    have hsingle : ({y} : Set α).Finite := by
      exact Set.finite_singleton y
    exact hsingle.insert x
  · exact ⟨x, by simp⟩

/--
If `c` chooses only from feasible sets and an element is chosen from `{x, y}`,
then it is either `x` or `y`.
-/
theorem mem_pair_of_mem_choose_pair
    (hFrom : c.ChoosesFrom)
    {x y z : α}
    (hz : z ∈ c.choose ({x, y} : Set α)) :
    z = x ∨ z = y := by
  have hz' : z ∈ ({x, y} : Set α) := hFrom ({x, y} : Set α) hz
  simpa using hz'

/--
If `x` is not chosen from `{x, y}`, but choice is finite-nonempty and constrained
to the feasible set, then `y` is chosen from `{x, y}`.
-/
theorem other_mem_choose_of_not_mem_choose_pair
    (hFrom : c.ChoosesFrom)
    (hFN : c.FiniteNonempty)
    {x y : α}
    (hxNot : x ∉ c.choose ({x, y} : Set α)) :
    y ∈ c.choose ({x, y} : Set α) := by
  have hNE : (c.choose ({x, y} : Set α)).Nonempty :=
    pair_choice_nonempty c hFN x y
  rcases hNE with ⟨z, hz⟩
  rcases mem_pair_of_mem_choose_pair c hFrom hz with hzx | hzy
  · subst hzx
    exact False.elim (hxNot hz)
  · subst hzy
    exact hz

end ChoiceFunction

end EcoLean
