import Mathlib.Order.Basic

universe u

namespace EcoLean

/--
A preference relation on a choice domain `α`.

The primitive notion is weak preference.
-/
structure Preference (α : Type u) where
  weakPref : α → α → Prop

namespace Preference

variable {α : Type u} (P : Preference α)

/-!
# Derived preference relations

These are the standard derived notions from a weak preference relation.
-/

/-- Strict preference derived from weak preference. -/
def StrictPref (x y : α) : Prop :=
  P.weakPref x y ∧ ¬ P.weakPref y x

/-- Indifference derived from weak preference. -/
def Indiff (x y : α) : Prop :=
  P.weakPref x y ∧ P.weakPref y x

/-- Incomparability derived from weak preference. -/
def Incomparable (x y : α) : Prop :=
  ¬ P.weakPref x y ∧ ¬ P.weakPref y x

/-!
# Rationality axioms

These are the standard textbook rationality properties.
-/

/-- Reflexivity of weak preference. -/
def Reflexive : Prop :=
  ∀ x : α, P.weakPref x x

/-- Transitivity of weak preference. -/
def Transitive : Prop :=
  ∀ x y z : α, P.weakPref x y → P.weakPref y z → P.weakPref x z

/-- Completeness of weak preference. -/
def Complete : Prop :=
  ∀ x y : α, P.weakPref x y ∨ P.weakPref y x

/-- A total preorder preference. -/
def TotalPreorder : Prop :=
  P.Reflexive ∧ P.Transitive ∧ P.Complete

scoped notation:50 x " ≽[" P "] " y => Preference.weakPref P x y
scoped notation:50 x " ≻[" P "] " y => Preference.StrictPref P x y
scoped notation:50 x " ∼[" P "] " y => Preference.Indiff P x y

/-!
# Definitional lemmas
-/

/-- Unfolding lemma for strict preference. -/
theorem strictPref_def (x y : α) :
    P.StrictPref x y ↔ P.weakPref x y ∧ ¬ P.weakPref y x := by
  rfl

/-- Unfolding lemma for indifference. -/
theorem indiff_def (x y : α) :
    P.Indiff x y ↔ P.weakPref x y ∧ P.weakPref y x := by
  rfl

/-- Unfolding lemma for incomparability. -/
theorem incomparable_def (x y : α) :
    P.Incomparable x y ↔ ¬ P.weakPref x y ∧ ¬ P.weakPref y x := by
  rfl

/-!
# Elementary lemmas
-/

/-- Theorem: strict preference implies weak preference. -/
theorem weakPref_of_strictPref {x y : α} :
    P.StrictPref x y → P.weakPref x y := by
  intro hxy
  exact hxy.1

/-- Theorem: strict preference rules out the reverse weak preference. -/
theorem not_weakPref_of_strictPref {x y : α} :
    P.StrictPref x y → ¬ P.weakPref y x := by
  intro hxy
  exact hxy.2

/-- Theorem: indifference implies weak preference in the first direction. -/
theorem weakPref_left_of_indiff {x y : α} :
    P.Indiff x y → P.weakPref x y := by
  intro hxy
  exact hxy.1

/-- Theorem: indifference implies weak preference in the second direction. -/
theorem weakPref_right_of_indiff {x y : α} :
    P.Indiff x y → P.weakPref y x := by
  intro hxy
  exact hxy.2

/-- Theorem: indifference is symmetric. -/
theorem indiff_symm {x y : α} :
    P.Indiff x y → P.Indiff y x := by
  intro hxy
  exact ⟨hxy.2, hxy.1⟩

/-- Theorem: incomparability is symmetric. -/
theorem incomparable_symm {x y : α} :
    P.Incomparable x y → P.Incomparable y x := by
  intro hxy
  exact ⟨hxy.2, hxy.1⟩

/-- Theorem: strict preference excludes indifference. -/
theorem strictPref_not_indiff {x y : α} :
    P.StrictPref x y → ¬ P.Indiff x y := by
  intro hxy hInd
  exact hxy.2 hInd.2

/-- Theorem: strict preference is asymmetric. -/
theorem strictPref_asymm {x y : α} :
    P.StrictPref x y → ¬ P.StrictPref y x := by
  intro hxy hyx
  exact hxy.2 hyx.1

/-!
# Consequences of reflexivity
-/

/-- Reflexivity implies self-indifference. -/
theorem indiff_refl_of_reflexive
    (hR : P.Reflexive) (x : α) :
    P.Indiff x x := by
  exact ⟨hR x, hR x⟩

/-- Under reflexivity, strict preference is irreflexive. -/
theorem not_strictPref_self_of_reflexive
    (hR : P.Reflexive) (x : α) :
    ¬ P.StrictPref x x := by
  intro hxx
  exact hxx.2 (hR x)

/-!
# Consequences of transitivity
-/

/-- Under transitivity, strict preference is transitive. -/
theorem strictPref_trans_of_transitive
    (hT : P.Transitive) {x y z : α} :
    P.StrictPref x y → P.StrictPref y z → P.StrictPref x z := by
  intro hxy hyz
  refine ⟨hT x y z hxy.1 hyz.1, ?_⟩
  intro hzx
  have hzy : P.weakPref z y := hT z x y hzx hxy.1
  exact hyz.2 hzy

/-- Under transitivity, indifference is transitive. -/
theorem indiff_trans_of_transitive
    (hT : P.Transitive) {x y z : α} :
    P.Indiff x y → P.Indiff y z → P.Indiff x z := by
  intro hxy hyz
  constructor
  · exact hT x y z hxy.1 hyz.1
  · exact hT z y x hyz.2 hxy.2

/-!
# Consequences of completeness
-/

/-- Completeness rules out incomparability. -/
theorem not_incomparable_of_complete
    (hC : P.Complete) (x y : α) :
    ¬ P.Incomparable x y := by
  intro hInc
  cases hC x y with
  | inl hxy =>
      exact hInc.1 hxy
  | inr hyx =>
      exact hInc.2 hyx

/--
If `x ≽ y`, then either `x ≻ y` or `x ∼ y`.
-/
theorem strict_or_indiff_of_weakPref
    {x y : α} (hxy : P.weakPref x y) :
    P.StrictPref x y ∨ P.Indiff x y := by
  by_cases hyx : P.weakPref y x
  · right
    exact ⟨hxy, hyx⟩
  · left
    exact ⟨hxy, hyx⟩

/--
Under completeness, for any two objects either `x ≻ y`, or `y ≻ x`, or `x ∼ y`.
-/
theorem complete_cases
    (hC : P.Complete) (x y : α) :
    P.StrictPref x y ∨ P.StrictPref y x ∨ P.Indiff x y := by
  cases hC x y with
  | inl hxy =>
      by_cases hyx : P.weakPref y x
      · exact Or.inr (Or.inr ⟨hxy, hyx⟩)
      · exact Or.inl ⟨hxy, hyx⟩
  | inr hyx =>
      by_cases hxy : P.weakPref x y
      · exact Or.inr (Or.inr ⟨hxy, hyx⟩)
      · exact Or.inr (Or.inl ⟨hyx, hxy⟩)

/-- Packaging lemma for total preorders. -/
theorem totalPreorder_intro
    (hR : P.Reflexive)
    (hT : P.Transitive)
    (hC : P.Complete) :
    P.TotalPreorder := by
  exact ⟨hR, hT, hC⟩

end Preference

end EcoLean
