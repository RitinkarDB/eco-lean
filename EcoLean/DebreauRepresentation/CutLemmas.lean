import EcoLean.DebreauRepresentation.CutExtension
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Basic order lemmas for lower and upper cuts

This file proves the first structural facts about the lower and upper cuts
attached to a utility representation on a subset `D`.

The main point is that values coming from the lower section are always below
values coming from the upper section, and hence the corresponding cuts inherit
the expected order properties.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
Any value coming from the lower value set witnesses nonemptiness of that set.
-/
theorem lowerValueSet_nonempty_of_mem
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x : α} {r : ℝ}
    (hr : r ∈ lowerValueSet P D u x) :
    (lowerValueSet P D u x).Nonempty := by
  exact ⟨r, hr⟩

/--
Any value coming from the upper value set witnesses nonemptiness of that set.
-/
theorem upperValueSet_nonempty_of_mem
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x : α} {r : ℝ}
    (hr : r ∈ upperValueSet P D u x) :
    (upperValueSet P D u x).Nonempty := by
  exact ⟨r, hr⟩

/--
Any value coming from the upper value set yields an upper bound on the lower
value set.
-/
theorem lowerValueSet_bddAbove_of_mem_upperValue
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    {x : α} {s : ℝ}
    (hs : s ∈ upperValueSet P D u x) :
    BddAbove (lowerValueSet P D u x) := by
  refine ⟨s, ?_⟩
  intro r hr
  exact lowerValue_le_upperValue P hT D u hu hr hs

/--
Any value coming from the lower value set yields a lower bound on the upper
value set.
-/
theorem upperValueSet_bddBelow_of_mem_lowerValue
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    {x : α} {r : ℝ}
    (hr : r ∈ lowerValueSet P D u x) :
    BddBelow (upperValueSet P D u x) := by
  refine ⟨r, ?_⟩
  intro s hs
  exact lowerValue_le_upperValue P hT D u hu hr hs

/--
If `s` belongs to the upper value set at `x`, and the lower value set is
nonempty, then the lower cut at `x` is at most `s`.
-/
theorem lowerCut_le_of_mem_upperValue
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    {x : α} {s : ℝ}
    (hLowerNonempty : (lowerValueSet P D u x).Nonempty)
    (hs : s ∈ upperValueSet P D u x) :
    lowerCut P D u x ≤ s := by
  unfold lowerCut
  apply csSup_le hLowerNonempty
  intro r hr
  exact lowerValue_le_upperValue P hT D u hu hr hs

/--
If the upper value set is nonempty and bounded below, then every lower-section
value is below the upper cut.
-/
theorem le_upperCut_of_mem_lowerValue
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    {x : α} {r : ℝ}
    (hBdd : BddBelow (upperValueSet P D u x))
    (hUpperNonempty : (upperValueSet P D u x).Nonempty)
    (hr : r ∈ lowerValueSet P D u x) :
    r ≤ upperCut P D u x := by
  unfold upperCut
  exact (le_csInf_iff hBdd hUpperNonempty).2 (by
    intro s hs
    exact lowerValue_le_upperValue P hT D u hu hr hs)

/--
If both value sets are suitably nonempty and bounded, then the lower cut is at
most the upper cut.
-/
theorem lowerCut_le_upperCut
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    {x : α}
    (hLowerNonempty : (lowerValueSet P D u x).Nonempty)
    (hBdd : BddBelow (upperValueSet P D u x))
    (hUpperNonempty : (upperValueSet P D u x).Nonempty) :
    lowerCut P D u x ≤ upperCut P D u x := by
  unfold lowerCut
  apply csSup_le hLowerNonempty
  intro r hr
  exact le_upperCut_of_mem_lowerValue P hT D u hu hBdd hUpperNonempty hr

/--
If `x ≽ y`, then the lower cut at `y` is at most the lower cut at `x`,
provided the lower value set at `y` is nonempty and the lower value set at `x`
is bounded above.
-/
theorem lowerCut_mono_of_weakPref
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x y : α}
    (hxy : P.weakPref x y)
    (hNonempty : (lowerValueSet P D u y).Nonempty)
    (hBdd : BddAbove (lowerValueSet P D u x)) :
    lowerCut P D u y ≤ lowerCut P D u x := by
  unfold lowerCut
  apply csSup_le hNonempty
  intro r hr
  exact le_csSup hBdd
    ((lowerValueSet_mono_of_weakPref P hT D u hxy) hr)

/--
If `x ≽ y`, then the upper cut at `y` is at most the upper cut at `x`,
provided the upper value set at `x` is nonempty, the upper value set at `x`
is bounded below, and the upper value set at `y` is bounded below.
-/
theorem upperCut_mono_of_weakPref
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x y : α}
    (hxy : P.weakPref x y)
    (hBddX : BddBelow (upperValueSet P D u x))
    (hNonemptyX : (upperValueSet P D u x).Nonempty)
    (hBddY : BddBelow (upperValueSet P D u y)) :
    upperCut P D u y ≤ upperCut P D u x := by
  unfold upperCut
  apply (le_csInf_iff hBddX hNonemptyX).2
  intro r hr
  exact csInf_le hBddY
    ((upperValueSet_mono_of_weakPref P hT D u hxy) hr)

section Complete

/--
At a point of the dense subset, the represented utility value belongs to the
lower value set at that point.
-/
theorem self_mem_lowerValueSet'
    (P : Preference α)
    (hC : P.Complete)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (d : D) :
    u d ∈ lowerValueSet P D u d.1 := by
  exact self_mem_lowerValueSet P hC D u d

/--
At a point of the dense subset, the represented utility value belongs to the
upper value set at that point.
-/
theorem self_mem_upperValueSet'
    (P : Preference α)
    (hC : P.Complete)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (d : D) :
    u d ∈ upperValueSet P D u d.1 := by
  exact self_mem_upperValueSet P hC D u d

/--
At a point of the dense subset, the lower value set is nonempty.
-/
theorem lowerValueSet_nonempty_self
    (P : Preference α)
    (hC : P.Complete)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (d : D) :
    (lowerValueSet P D u d.1).Nonempty := by
  exact ⟨u d, self_mem_lowerValueSet' P hC D u d⟩

/--
At a point of the dense subset, the upper value set is nonempty.
-/
theorem upperValueSet_nonempty_self
    (P : Preference α)
    (hC : P.Complete)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (d : D) :
    (upperValueSet P D u d.1).Nonempty := by
  exact ⟨u d, self_mem_upperValueSet' P hC D u d⟩

/--
At a point of the dense subset, the represented utility value is an upper bound
for the corresponding lower value set.
-/
theorem upperBounds_lowerValueSet_self
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    (d : D) :
    BddAbove (lowerValueSet P D u d.1) := by
  exact lowerValueSet_bddAbove_of_mem_upperValue P hT D u hu
    (self_mem_upperValueSet' P hC D u d)

/--
At a point of the dense subset, the represented utility value is a lower bound
for the corresponding upper value set.
-/
theorem lowerBounds_upperValueSet_self
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    (d : D) :
    BddBelow (upperValueSet P D u d.1) := by
  exact upperValueSet_bddBelow_of_mem_lowerValue P hT D u hu
    (self_mem_lowerValueSet' P hC D u d)

/--
At a point of `D`, the lower cut recovers the represented utility value.
-/
theorem lowerCut_eq_self
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    (d : D) :
    lowerCut P D u d.1 = u d := by
  apply le_antisymm
  · exact lowerCut_le_of_mem_upperValue P hT D u hu
      (lowerValueSet_nonempty_self P hC D u d)
      (self_mem_upperValueSet' P hC D u d)
  · unfold lowerCut
    exact le_csSup
      (upperBounds_lowerValueSet_self P hC hT D u hu d)
      (self_mem_lowerValueSet' P hC D u d)

/--
At a point of `D`, the upper cut recovers the represented utility value.
-/
theorem upperCut_eq_self
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    (d : D) :
    upperCut P D u d.1 = u d := by
  apply le_antisymm
  · unfold upperCut
    exact csInf_le
      (lowerBounds_upperValueSet_self P hC hT D u hu d)
      (self_mem_upperValueSet' P hC D u d)
  · exact le_upperCut_of_mem_lowerValue P hT D u hu
      (lowerBounds_upperValueSet_self P hC hT D u hu d)
      (upperValueSet_nonempty_self P hC D u d)
      (self_mem_lowerValueSet' P hC D u d)

/--
At a point of `D`, the lower and upper cuts agree.
-/
theorem lowerCut_eq_upperCut_self
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    (d : D) :
    lowerCut P D u d.1 = upperCut P D u d.1 := by
  rw [lowerCut_eq_self P hC hT D u hu d, upperCut_eq_self P hC hT D u hu d]

end Complete

end Preference
end EcoLean
