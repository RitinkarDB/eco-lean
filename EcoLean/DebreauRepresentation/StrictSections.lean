import EcoLean.DebreauRepresentation.ContinuousPreference

/-!
# Strict contour sections

In a complete preference, strict upper and lower contour sets can be described
as complements of the corresponding weak contour sets.

This is the key bridge from continuity of weak preference, formulated via
closed contour sets, to openness of strict preference sections.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u} [TopologicalSpace α]

/--
Membership in the strict upper contour set of `x` is equivalent to non-membership
in the lower weak contour set of `x`.

Intuitively: `y ≻ x` iff it is not the case that `x ≽ y`, provided the
preference is complete.
-/
theorem mem_strictUpperContourSet_iff_not_mem_lowerContourSet
    (P : Preference α) (hC : P.Complete) {x y : α} :
    y ∈ strictUpperContourSet P x ↔ y ∉ lowerContourSet P x := by
  change P.StrictPref y x ↔ ¬ P.weakPref x y
  constructor
  · intro hy
    exact hy.2
  · intro hnot
    have hyx : P.weakPref y x := by
      rcases hC y x with hyx | hxy
      · exact hyx
      · exact False.elim (hnot hxy)
    exact ⟨hyx, hnot⟩

/--
Membership in the strict lower contour set of `x` is equivalent to non-membership
in the upper weak contour set of `x`.

Intuitively: `x ≻ y` iff it is not the case that `y ≽ x`, provided the
preference is complete.
-/
theorem mem_strictLowerContourSet_iff_not_mem_upperContourSet
    (P : Preference α) (hC : P.Complete) {x y : α} :
    y ∈ strictLowerContourSet P x ↔ y ∉ upperContourSet P x := by
  change P.StrictPref x y ↔ ¬ P.weakPref y x
  constructor
  · intro hy
    exact hy.2
  · intro hnot
    have hxy : P.weakPref x y := by
      rcases hC x y with hxy | hyx
      · exact hxy
      · exact False.elim (hnot hyx)
    exact ⟨hxy, hnot⟩

/--
The strict upper contour set of `x` is exactly the complement of the lower weak
contour set of `x`, under completeness.
-/
theorem strictUpperContourSet_eq_compl_lowerContourSet
    (P : Preference α) (hC : P.Complete) (x : α) :
    strictUpperContourSet P x = (lowerContourSet P x)ᶜ := by
  ext y
  exact mem_strictUpperContourSet_iff_not_mem_lowerContourSet P hC

/--
The strict lower contour set of `x` is exactly the complement of the upper weak
contour set of `x`, under completeness.
-/
theorem strictLowerContourSet_eq_compl_upperContourSet
    (P : Preference α) (hC : P.Complete) (x : α) :
    strictLowerContourSet P x = (upperContourSet P x)ᶜ := by
  ext y
  exact mem_strictLowerContourSet_iff_not_mem_upperContourSet P hC

/--
If a preference is complete and continuous, then each strict upper contour set
is open.

This follows because the strict upper contour set is the complement of a closed
lower weak contour set.
-/
theorem isOpen_strictUpperContourSet
    (P : Preference α)
    (hC : P.Complete)
    (hCont : ContinuousPref P)
    (x : α) :
    IsOpen (strictUpperContourSet P x) := by
  rw [strictUpperContourSet_eq_compl_lowerContourSet P hC x]
  exact (hCont.2 x).isOpen_compl

/--
If a preference is complete and continuous, then each strict lower contour set
is open.

This follows because the strict lower contour set is the complement of a closed
upper weak contour set.
-/
theorem isOpen_strictLowerContourSet
    (P : Preference α)
    (hC : P.Complete)
    (hCont : ContinuousPref P)
    (x : α) :
    IsOpen (strictLowerContourSet P x) := by
  rw [strictLowerContourSet_eq_compl_upperContourSet P hC x]
  exact (hCont.1 x).isOpen_compl

end Preference
end EcoLean
