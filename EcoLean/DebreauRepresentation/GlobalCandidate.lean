import EcoLean.DebreauRepresentation.CutLemmas

/-!
# Global utility candidates from cuts

This file defines the global real-valued functions obtained from the lower and
upper cuts, together with the midpoint candidate that will later be used in the
extension step.

At points of the dense subset `D`, all of these candidates agree with the
original restricted utility.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
The lower-cut candidate utility on the whole space.
-/
noncomputable def lowerCutUtility
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) : α → ℝ :=
  fun x => lowerCut P D u x

/--
The upper-cut candidate utility on the whole space.
-/
noncomputable def upperCutUtility
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) : α → ℝ :=
  fun x => upperCut P D u x

/--
The midpoint candidate utility on the whole space.

This is the average of the lower and upper cuts.
-/
noncomputable def midpointUtility
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) : α → ℝ :=
  fun x => (lowerCut P D u x + upperCut P D u x) / 2

@[simp] theorem lowerCutUtility_apply
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) (x : α) :
    lowerCutUtility P D u x = lowerCut P D u x := by
  rfl

@[simp] theorem upperCutUtility_apply
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) (x : α) :
    upperCutUtility P D u x = upperCut P D u x := by
  rfl

@[simp] theorem midpointUtility_apply
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) (x : α) :
    midpointUtility P D u x = (lowerCut P D u x + upperCut P D u x) / 2 := by
  rfl

section Complete

/--
On the dense subset `D`, the lower-cut candidate agrees with the original
utility representation.
-/
theorem lowerCutUtility_eq_on_dense
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    (d : D) :
    lowerCutUtility P D u d.1 = u d := by
  exact lowerCut_eq_self P hC hT D u hu d

/--
On the dense subset `D`, the upper-cut candidate agrees with the original
utility representation.
-/
theorem upperCutUtility_eq_on_dense
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    (d : D) :
    upperCutUtility P D u d.1 = u d := by
  exact upperCut_eq_self P hC hT D u hu d

/--
On the dense subset `D`, the midpoint candidate agrees with the original
utility representation.
-/
theorem midpointUtility_eq_on_dense
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    (d : D) :
    midpointUtility P D u d.1 = u d := by
  rw [midpointUtility_apply]
  rw [lowerCut_eq_self P hC hT D u hu d, upperCut_eq_self P hC hT D u hu d]
  ring

end Complete

end Preference
end EcoLean
