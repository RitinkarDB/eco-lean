import EcoLean.DebreauRepresentation.DenseRestriction
import Mathlib.Order.Monotone.Basic

/-!
# Gap adjustment for restricted utilities
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
A gap of a subset `S ⊆ ℝ` is a pair `a < b` such that no point of `S` lies
strictly between `a` and `b`.
-/
def IsGap (S : Set ℝ) (a b : ℝ) : Prop :=
  a < b ∧ ∀ c : ℝ, a < c → c < b → c ∉ S

/--
A gap is open if both endpoints belong to the set.
-/
def IsOpenGap (S : Set ℝ) (a b : ℝ) : Prop :=
  IsGap S a b ∧ a ∈ S ∧ b ∈ S

/--
A subset of `ℝ` has only open gaps if every gap is open.
-/
def HasOnlyOpenGaps (S : Set ℝ) : Prop :=
  ∀ ⦃a b : ℝ⦄, IsGap S a b → IsOpenGap S a b

/--
The image of a restricted utility.
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
Postcomposition of a restricted utility by a real-valued map.
-/
def postcomposeRestricted
    {D : Set α}
    (u : Utility.UtilityFunction D) (φ : ℝ → ℝ) :
    Utility.UtilityFunction D :=
  fun d => φ (u d)

@[simp] theorem postcomposeRestricted_apply
    {D : Set α}
    (u : Utility.UtilityFunction D) (φ : ℝ → ℝ) (d : D) :
    postcomposeRestricted u φ d = φ (u d) := by
  rfl

/--
The image of a postcomposed restricted utility is the image of the original
restricted utility under the postcomposing map.
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
Two restricted utilities induce the same weak order on the restricted domain.
-/
def SameOrderRestrictedUtility
    {D : Set α}
    (u u' : Utility.UtilityFunction D) : Prop :=
  ∀ x y : D, u x ≥ u y ↔ u' x ≥ u' y

/--
A gap-adjusted restricted utility is one whose image has only open gaps.
-/
def IsGapAdjustedRestrictedUtility
    {D : Set α}
    (u : Utility.UtilityFunction D) : Prop :=
  HasOnlyOpenGaps (restrictedUtilityImage u)

/--
A restricted utility admits a gap adjustment if there exists another restricted
utility with the same induced weak order and only open gaps in its image.
-/
def GapAdjustmentExists
    {D : Set α}
    (u : Utility.UtilityFunction D) : Prop :=
  ∃ u' : Utility.UtilityFunction D,
    SameOrderRestrictedUtility u u' ∧
    IsGapAdjustedRestrictedUtility u'

/--
Postcomposing a restricted utility by a strictly increasing map preserves
representation of the restricted preference.
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
A restricted utility with the same induced weak order represents the same
restricted preference.
-/
theorem represents_of_sameOrderRestrictedUtility
    {D : Set α}
    (P : Preference α)
    (u u' : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    (hSame : SameOrderRestrictedUtility u u') :
    Represents u' (restrict P D) := by
  intro x y
  exact (hu x y).trans (hSame x y)

end Preference
end EcoLean
