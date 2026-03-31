import EcoLean.DebreauRepresentation.Contours

/-!
# Continuous preferences

This file defines continuity of a preference in terms of the closedness of its
upper and lower weak contour sets.

It also proves the easy direction of the representation story:

if a preference is represented by a continuous utility function, then the
preference is continuous in this contour-set sense.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u} [TopologicalSpace α]

/--
A preference is continuous if each upper and lower weak contour set is closed.
-/
def ContinuousPref (P : Preference α) : Prop :=
  (∀ x, IsClosed (upperContourSet P x)) ∧
  (∀ x, IsClosed (lowerContourSet P x))

/--
A continuous utility representation induces a continuous preference.

The idea is simple: each contour set of the represented preference is the
preimage of a closed ray in `ℝ` under the utility function, and continuous
preimages of closed sets are closed.
-/
theorem continuousPref_of_continuous_represents
    {P : Preference α}
    {u : Utility.UtilityFunction α}
    (hu : Continuous u)
    (hRep : Represents u P) :
    ContinuousPref P := by
  constructor
  · intro x
    have hEq : upperContourSet P x = u ⁻¹' Set.Ici (u x) := by
      ext y
      rw [upperContourSet, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici]
      simpa [ge_iff_le] using (hRep y x)
    rw [hEq]
    exact IsClosed.preimage hu isClosed_Ici
  · intro x
    have hEq : lowerContourSet P x = u ⁻¹' Set.Iic (u x) := by
      ext y
      rw [lowerContourSet, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic]
      simpa [ge_iff_le] using (hRep x y)
    rw [hEq]
    exact IsClosed.preimage hu isClosed_Iic

end Preference
end EcoLean
