import EcoLean.ChoicePreferenceUtility.Preference
import Mathlib.Data.Set.Basic

universe u

namespace EcoLean
namespace Preference

variable {α : Type u} (P : Preference α)

/-!
# No-better-than sets and contour sets

This file formalises the set-based language Kreps uses in Chapter 1.
For each object `x`, the no-better-than set of `x` is the set of objects
that are weakly worse than `x`.
-/

/--
The no-better-than set of `x`.

An object `y` belongs to `P.NoBetterThan x` iff `x ≽ y`.
-/
def NoBetterThan (x : α) : Set α :=
  {y : α | P.weakPref x y}

/--
The at-least-as-good-as set of `x`.

An object `y` belongs to `P.AtLeastAsGoodAs x` iff `y ≽ x`.
-/
def AtLeastAsGoodAs (x : α) : Set α :=
  {y : α | P.weakPref y x}

/-!
# Basic membership lemmas
-/

/-- Membership in the no-better-than set is just weak preference. -/
theorem mem_noBetterThan_iff {x y : α} :
    y ∈ P.NoBetterThan x ↔ P.weakPref x y := by
  rfl

/-- Membership in the at-least-as-good-as set is just reverse weak preference. -/
theorem mem_atLeastAsGoodAs_iff {x y : α} :
    y ∈ P.AtLeastAsGoodAs x ↔ P.weakPref y x := by
  rfl

/-- Under completeness, every object belongs to its own no-better-than set. -/
theorem self_mem_noBetterThan_of_complete
    (hC : P.Complete) (x : α) :
    x ∈ P.NoBetterThan x := by
  exact weakPref_refl_of_complete P hC x

/-- Under completeness, every object belongs to its own at-least-as-good-as set. -/
theorem self_mem_atLeastAsGoodAs_of_complete
    (hC : P.Complete) (x : α) :
    x ∈ P.AtLeastAsGoodAs x := by
  exact weakPref_refl_of_complete P hC x

/-!
# Monotonicity of no-better-than sets under weak preference
-/

/--
If `x ≽ y`, then everything no better than `y` is also no better than `x`.

Equivalently, `NoBetterThan y ⊆ NoBetterThan x`.
-/
theorem noBetterThan_subset_of_weakPref
    (hT : P.Transitive) {x y : α}
    (hxy : P.weakPref x y) :
    P.NoBetterThan y ⊆ P.NoBetterThan x := by
  intro z hz
  exact hT x y z hxy hz

/--
If `x ≽ y`, then everything at least as good as `x` is also at least as good as `y`.

Equivalently, `AtLeastAsGoodAs x ⊆ AtLeastAsGoodAs y`.
-/
theorem atLeastAsGoodAs_subset_of_weakPref
    (hT : P.Transitive) {x y : α}
    (hxy : P.weakPref x y) :
    P.AtLeastAsGoodAs x ⊆ P.AtLeastAsGoodAs y := by
  intro z hz
  exact hT z x y hz hxy

/--
Under completeness, if `NoBetterThan y ⊆ NoBetterThan x`, then `x ≽ y`.

This is the converse of the previous subset statement.
-/
theorem weakPref_of_noBetterThan_subset
    (hC : P.Complete) {x y : α}
    (hSub : P.NoBetterThan y ⊆ P.NoBetterThan x) :
    P.weakPref x y := by
  have hyy : y ∈ P.NoBetterThan y :=
    self_mem_noBetterThan_of_complete P hC y
  exact hSub hyy

/--
Under completeness and transitivity, weak preference is equivalent
to reverse inclusion of no-better-than sets.
-/
theorem weakPref_iff_noBetterThan_subset
    (hC : P.Complete) (hT : P.Transitive) {x y : α} :
    P.weakPref x y ↔ P.NoBetterThan y ⊆ P.NoBetterThan x := by
  constructor
  · intro hxy
    exact noBetterThan_subset_of_weakPref P hT hxy
  · intro hSub
    exact weakPref_of_noBetterThan_subset P hC hSub

/-!
# Strict containment results
-/

/--
If `¬ x ≽ y`, then `NoBetterThan x` is a strict subset of `NoBetterThan y`.

This is the key set-theoretic fact used in the finite utility-representation proof.
-/
theorem noBetterThan_ssubset_of_not_weakPref
    (hC : P.Complete) (hT : P.Transitive) {x y : α}
    (hNot : ¬ P.weakPref x y) :
    P.NoBetterThan x ⊂ P.NoBetterThan y := by
  constructor
  · have hyx : P.weakPref y x := by
      cases hC x y with
      | inl hxy =>
          exact False.elim (hNot hxy)
      | inr hyx =>
          exact hyx
    exact noBetterThan_subset_of_weakPref P hT hyx
  · intro hRev
    have hyy : y ∈ P.NoBetterThan y :=
      self_mem_noBetterThan_of_complete P hC y
    have hyIn : y ∈ P.NoBetterThan x := hRev hyy
    exact hNot hyIn

/--
Under completeness and transitivity, strict preference is equivalent
to strict containment of no-better-than sets.
-/
theorem strictPref_iff_noBetterThan_ssubset
    (hC : P.Complete) (hT : P.Transitive) {x y : α} :
    P.StrictPref x y ↔ P.NoBetterThan y ⊂ P.NoBetterThan x := by
  constructor
  · intro hxy
    constructor
    · exact noBetterThan_subset_of_weakPref P hT hxy.1
    · intro hRev
      have hxx : x ∈ P.NoBetterThan x :=
        self_mem_noBetterThan_of_complete P hC x
      have hxIn : x ∈ P.NoBetterThan y := hRev hxx
      exact hxy.2 hxIn
  · intro hSub
    constructor
    · exact weakPref_of_noBetterThan_subset P hC hSub.1
    · intro hyx
      have hxySub : P.NoBetterThan x ⊆ P.NoBetterThan y :=
        noBetterThan_subset_of_weakPref P hT hyx
      exact hSub.2 hxySub
/-!
# Equality of no-better-than sets under indifference
-/

/--
If `x ∼ y`, then `x` and `y` have the same no-better-than set.
-/
theorem noBetterThan_eq_of_indiff
    (hT : P.Transitive) {x y : α}
    (hxy : P.Indiff x y) :
    P.NoBetterThan x = P.NoBetterThan y := by
  apply Set.Subset.antisymm
  · exact noBetterThan_subset_of_weakPref P hT hxy.2
  · exact noBetterThan_subset_of_weakPref P hT hxy.1

end Preference
end EcoLean
