import EcoLean.DebreauRepresentation.DenseRestriction
import Mathlib.Order.Interval.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Gap adjustment on the restricted utility image

This file packages the order-theoretic target of the Debreau gap-adjustment step.

The key idea is that, after representing the restricted preference on a
countable Debreu-dense subset `D`, one wants to postcompose that representation
with a strictly increasing map `φ : ℝ → ℝ` so that the image has a good gap
structure for the later extension step.

This file does not yet prove existence of such a `φ`. It sets up the relevant
definitions and proves the preservation lemmas needed later.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
A gap of a subset `S ⊆ ℝ` is a pair of real numbers `a < b` such that
no point of `S` lies strictly between them.
-/
def IsGap (S : Set ℝ) (a b : ℝ) : Prop :=
  a < b ∧ ∀ c : ℝ, a < c → c < b → c ∉ S

/--
A gap of `S` is open if both endpoints are outside `S`.
-/
def IsOpenGap (S : Set ℝ) (a b : ℝ) : Prop :=
  IsGap S a b ∧ a ∉ S ∧ b ∉ S

/--
A subset of `ℝ` has only open gaps if every gap of the set is open.
-/
def HasOnlyOpenGaps (S : Set ℝ) : Prop :=
  ∀ ⦃a b : ℝ⦄, IsGap S a b → IsOpenGap S a b

/--
The image of a restricted utility representation.
-/
def restrictedUtilityImage
    {D : Set α}
    (u : Utility.UtilityFunction D) : Set ℝ :=
  Set.range u

@[simp] theorem mem_restrictedUtilityImage
    {D : Set α}
    (u : Utility.UtilityFunction D) (r : ℝ) :
    r ∈ restrictedUtilityImage u ↔ ∃ d : D, u d = r := by
  rfl

/--
The postcomposition of a restricted utility function by a real map.
-/
def postcomposeRestricted
    {D : Set α}
    (u : Utility.UtilityFunction D) (φ : ℝ → ℝ) : Utility.UtilityFunction D :=
  fun d => φ (u d)

@[simp] theorem postcomposeRestricted_apply
    {D : Set α}
    (u : Utility.UtilityFunction D) (φ : ℝ → ℝ) (d : D) :
    postcomposeRestricted u φ d = φ (u d) := by
  rfl

/--
A strictly increasing postcomposition preserves representation of the
restricted preference.
-/
theorem represents_postcomposeRestricted_strictMono
    {D : Set α}
    (P : Preference α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    {φ : ℝ → ℝ}
    (hφ : StrictMono φ) :
    Represents (postcomposeRestricted u φ) (restrict P D) := by
  intro x y
  rw [hu x y]
  simpa [postcomposeRestricted, ge_iff_le] using
    (hφ.le_iff_le (a := u y) (b := u x)).symm

/--
The image of the postcomposed restricted utility is the image of the original
restricted utility under `φ`.
-/
theorem restrictedUtilityImage_postcompose
    {D : Set α}
    (u : Utility.UtilityFunction D)
    (φ : ℝ → ℝ) :
    restrictedUtilityImage (postcomposeRestricted u φ) = φ '' restrictedUtilityImage u := by
  ext r
  constructor
  · intro hr
    rcases hr with ⟨d, rfl⟩
    exact ⟨u d, ⟨d, rfl⟩, rfl⟩
  · intro hr
    rcases hr with ⟨s, hs, rfl⟩
    rcases hs with ⟨d, rfl⟩
    exact ⟨d, rfl⟩

/--
If `φ` is strictly increasing, then gaps in the transformed image correspond to
gaps in the original image after pulling back along `φ`.
-/
theorem isGap_preimage_of_strictMono
    {D : Set α}
    (u : Utility.UtilityFunction D)
    {φ : ℝ → ℝ}
    (hφ : StrictMono φ)
    {a b : ℝ}
    (hgap : IsGap (restrictedUtilityImage (postcomposeRestricted u φ)) (φ a) (φ b)) :
    IsGap (restrictedUtilityImage u) a b := by
  rcases hgap with ⟨hab, hmid⟩
  refine ⟨(hφ.lt_iff_lt).1 hab, ?_⟩
  intro c hac hcb hc
  have hφac : φ a < φ c := hφ hac
  have hφcb : φ c < φ b := hφ hcb
  have hmem : φ c ∈ restrictedUtilityImage (postcomposeRestricted u φ) := by
    rcases hc with ⟨d, rfl⟩
    exact ⟨d, rfl⟩
  exact hmid (φ c) hφac hφcb hmem

/--
A gap-adjusted restricted utility is one whose image has only open gaps.
-/
def IsGapAdjustedRestrictedUtility
    {D : Set α}
    (u : Utility.UtilityFunction D) : Prop :=
  HasOnlyOpenGaps (restrictedUtilityImage u)

/--
Gap-adjustability of a restricted utility means that some strictly increasing
postcomposition of it has only open gaps in its image.
-/
def IsGapAdjustableRestrictedUtility
    {D : Set α}
    (u : Utility.UtilityFunction D) : Prop :=
  ∃ φ : ℝ → ℝ, StrictMono φ ∧
    IsGapAdjustedRestrictedUtility (postcomposeRestricted u φ)

/--
A packaged statement of the Debreau gap-adjustment step for a restricted
utility representation.

This is the target theorem needed later. The proof is not part of the present
file.
-/
def GapAdjustmentExists
    {D : Set α}
    (u : Utility.UtilityFunction D) : Prop :=
  ∃ φ : ℝ → ℝ, StrictMono φ ∧
    HasOnlyOpenGaps (restrictedUtilityImage (postcomposeRestricted u φ))

/--
If a restricted utility is gap-adjustable, then there is a strictly increasing
postcomposition of it which still represents the restricted preference and has
only open gaps in its image.
-/
theorem exists_gapAdjusted_representation_of_isGapAdjustable
    {D : Set α}
    (P : Preference α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    (hAdj : IsGapAdjustableRestrictedUtility u) :
    ∃ u' : Utility.UtilityFunction D,
      Represents u' (restrict P D) ∧
      IsGapAdjustedRestrictedUtility u' := by
  rcases hAdj with ⟨φ, hφ, hGap⟩
  refine ⟨postcomposeRestricted u φ, ?_, ?_⟩
  · exact represents_postcomposeRestricted_strictMono P u hu hφ
  · exact hGap

end Preference
end EcoLean
