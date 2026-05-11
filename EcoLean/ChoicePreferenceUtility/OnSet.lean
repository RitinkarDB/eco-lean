import EcoLean.ChoicePreferenceUtility.Utility
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Carrier-relative preference and utility notions

This file adds the carrier-relative API needed for microeconomics and expected
utility theory.

The core `EcoLean.Preference` structure remains deliberately global: a weak
preference is a binary relation on a type.  Economic models, however, usually
work relative to a feasible set, a consumption set, or a set of lotteries.  The
definitions here package those restrictions without introducing a parallel
Isabelle-style `carrier + relation` hierarchy.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u} (P : Preference α)

/-! ## Rationality and representation on a carrier -/

/-- Reflexivity of a preference restricted to a carrier `S`. -/
def ReflexiveOn (S : Set α) : Prop :=
  ∀ ⦃x : α⦄, x ∈ S → P.weakPref x x

/-- Completeness of a preference restricted to a carrier `S`. -/
def CompleteOn (S : Set α) : Prop :=
  ∀ ⦃x y : α⦄, x ∈ S → y ∈ S → P.weakPref x y ∨ P.weakPref y x

/-- Transitivity of a preference restricted to a carrier `S`. -/
def TransitiveOn (S : Set α) : Prop :=
  ∀ ⦃x y z : α⦄,
    x ∈ S → y ∈ S → z ∈ S →
      P.weakPref x y → P.weakPref y z → P.weakPref x z

/-- A complete and transitive weak preference on a carrier. -/
def RationalOn (S : Set α) : Prop :=
  P.CompleteOn S ∧ P.TransitiveOn S

/-- A utility function represents a preference on a carrier `S`. -/
def RepresentsOn (S : Set α) (u : α → ℝ) : Prop :=
  ∀ ⦃x y : α⦄, x ∈ S → y ∈ S → (P.weakPref x y ↔ u x ≥ u y)

theorem reflexiveOn_of_completeOn {S : Set α}
    (hC : P.CompleteOn S) :
    P.ReflexiveOn S := by
  intro x hx
  exact (hC hx hx).elim id id

theorem completeOn_of_complete {S : Set α}
    (hC : P.Complete) :
    P.CompleteOn S := by
  intro x y _ _
  exact hC x y

theorem transitiveOn_of_transitive {S : Set α}
    (hT : P.Transitive) :
    P.TransitiveOn S := by
  intro x y z _ _ _ hxy hyz
  exact hT x y z hxy hyz

theorem representsOn_of_represents {S : Set α} {u : α → ℝ}
    (hRep : Represents u P) :
    P.RepresentsOn S u := by
  intro x y _ _
  exact hRep x y

theorem completeOn_of_representsOn {S : Set α} {u : α → ℝ}
    (hRep : P.RepresentsOn S u) :
    P.CompleteOn S := by
  intro x y hx hy
  cases le_total (u x) (u y) with
  | inl hxy =>
      exact Or.inr ((hRep hy hx).mpr hxy)
  | inr hyx =>
      exact Or.inl ((hRep hx hy).mpr hyx)

theorem transitiveOn_of_representsOn {S : Set α} {u : α → ℝ}
    (hRep : P.RepresentsOn S u) :
    P.TransitiveOn S := by
  intro x y z hx hy hz hxy hyz
  have hxy' : u x ≥ u y := (hRep hx hy).mp hxy
  have hyz' : u y ≥ u z := (hRep hy hz).mp hyz
  exact (hRep hx hz).mpr (le_trans hyz' hxy')

theorem rationalOn_of_representsOn {S : Set α} {u : α → ℝ}
    (hRep : P.RepresentsOn S u) :
    P.RationalOn S :=
  ⟨P.completeOn_of_representsOn hRep, P.transitiveOn_of_representsOn hRep⟩

theorem strictPref_iff_gt_of_representsOn {S : Set α} {u : α → ℝ}
    (hRep : P.RepresentsOn S u) {x y : α}
    (hx : x ∈ S) (hy : y ∈ S) :
    P.StrictPref x y ↔ u x > u y := by
  constructor
  · intro hxy
    have hyx_not : ¬ u y ≥ u x := by
      intro hyx
      exact hxy.2 ((hRep hy hx).mpr hyx)
    exact lt_of_not_ge hyx_not
  · intro hxy
    constructor
    · exact (hRep hx hy).mpr (le_of_lt hxy)
    · intro hyx
      exact (not_le_of_gt hxy) ((hRep hy hx).mp hyx)

theorem indiff_iff_eq_of_representsOn {S : Set α} {u : α → ℝ}
    (hRep : P.RepresentsOn S u) {x y : α}
    (hx : x ∈ S) (hy : y ∈ S) :
    P.Indiff x y ↔ u x = u y := by
  constructor
  · intro hxy
    exact le_antisymm ((hRep hy hx).mp hxy.2) ((hRep hx hy).mp hxy.1)
  · intro hxy
    constructor
    · exact (hRep hx hy).mpr (by simp [hxy])
    · exact (hRep hy hx).mpr (by simp [hxy])

/-! ## Carrier-relative contour sets -/

/-- The carrier-restricted upper contour set of `x`. -/
def AtLeastAsGoodAsOn (S : Set α) (x : α) : Set α :=
  {y : α | y ∈ S ∧ P.weakPref y x}

/-- The carrier-restricted lower contour set of `x`. -/
def NoBetterThanOn (S : Set α) (x : α) : Set α :=
  {y : α | y ∈ S ∧ P.weakPref x y}

/-- The carrier-restricted indifference class of `x`. -/
def AsGoodAsOn (S : Set α) (x : α) : Set α :=
  {y : α | y ∈ S ∧ P.Indiff y x}

@[simp] theorem mem_atLeastAsGoodAsOn_iff {S : Set α} {x y : α} :
    y ∈ P.AtLeastAsGoodAsOn S x ↔ y ∈ S ∧ P.weakPref y x :=
  Iff.rfl

@[simp] theorem mem_noBetterThanOn_iff {S : Set α} {x y : α} :
    y ∈ P.NoBetterThanOn S x ↔ y ∈ S ∧ P.weakPref x y :=
  Iff.rfl

@[simp] theorem mem_asGoodAsOn_iff {S : Set α} {x y : α} :
    y ∈ P.AsGoodAsOn S x ↔ y ∈ S ∧ P.Indiff y x :=
  Iff.rfl

theorem atLeastAsGoodAsOn_subset {S : Set α} {x : α} :
    P.AtLeastAsGoodAsOn S x ⊆ S := by
  intro y hy
  exact hy.1

theorem noBetterThanOn_subset {S : Set α} {x : α} :
    P.NoBetterThanOn S x ⊆ S := by
  intro y hy
  exact hy.1

/-! ## Local non-satiation -/

/--
Local non-satiation on `S`: every feasible bundle can be strictly improved
arbitrarily nearby, with distance measured by the ambient pseudo-metric.
-/
def LocalNonSatiationOn [PseudoMetricSpace α] (S : Set α) : Prop :=
  ∀ ⦃x : α⦄, x ∈ S → ∀ ε : ℝ, 0 < ε →
    ∃ y : α, y ∈ S ∧ dist y x ≤ ε ∧ P.StrictPref y x

/-- Utility-form local non-satiation on `S`. -/
def UtilityLocalNonSatiationOn [PseudoMetricSpace α]
    (S : Set α) (u : α → ℝ) : Prop :=
  ∀ ⦃x : α⦄, x ∈ S → ∀ ε : ℝ, 0 < ε →
    ∃ y : α, y ∈ S ∧ dist y x ≤ ε ∧ u y > u x

theorem localNonSatiationOn_iff_utilityLocalNonSatiationOn
    [PseudoMetricSpace α] {S : Set α} {u : α → ℝ}
    (hRep : P.RepresentsOn S u) :
    P.LocalNonSatiationOn S ↔ UtilityLocalNonSatiationOn S u := by
  constructor
  · intro hLNS x hx ε hε
    rcases hLNS hx ε hε with ⟨y, hy, hdist, hyx⟩
    exact ⟨y, hy, hdist, (P.strictPref_iff_gt_of_representsOn hRep hy hx).mp hyx⟩
  · intro hLNS x hx ε hε
    rcases hLNS hx ε hε with ⟨y, hy, hdist, hyx⟩
    exact ⟨y, hy, hdist, (P.strictPref_iff_gt_of_representsOn hRep hy hx).mpr hyx⟩

/-! ## Convexity and monotonicity of preferences -/

section Ordered

variable [LE α] [LT α]

/-- Weak monotonicity on `S`: componentwise larger bundles are weakly preferred. -/
def WeaklyMonotoneOn (S : Set α) : Prop :=
  ∀ ⦃x y : α⦄, x ∈ S → y ∈ S → x ≥ y → P.weakPref x y

/-- Strict monotonicity on `S`: componentwise larger bundles are strictly preferred. -/
def MonotoneOn (S : Set α) : Prop :=
  ∀ ⦃x y : α⦄, x ∈ S → y ∈ S → x > y → P.StrictPref x y

end Ordered

section Convex

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]
variable (P : Preference E)

/--
Weakly convex preferences: mixing a weakly better bundle with a worse bundle
keeps the mixture weakly above the worse bundle.
-/
def WeaklyConvexOn (S : Set E) : Prop :=
  ∀ ⦃x y : E⦄, x ∈ S → y ∈ S → P.weakPref x y →
    ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
      P.weakPref (a • x + b • y) y

/--
Convex preferences in the strict-upper-contour sense used in the welfare
formalization.
-/
def ConvexOn (S : Set E) : Prop :=
  ∀ ⦃x y : E⦄, x ∈ S → y ∈ S → P.StrictPref x y →
    ∀ a : ℝ, 0 < a → a < 1 →
      P.StrictPref (a • x + (1 - a) • y) y

/--
Strictly convex preferences: every nontrivial mixture of a weakly better
distinct bundle is strictly preferred to the worse bundle.
-/
def StrictlyConvexOn (S : Set E) : Prop :=
  ∀ ⦃x y : E⦄, x ∈ S → y ∈ S → x ≠ y → P.weakPref x y →
    ∀ a : ℝ, 0 < a → a < 1 →
      P.StrictPref (a • x + (1 - a) • y) y

end Convex

end Preference
end EcoLean
