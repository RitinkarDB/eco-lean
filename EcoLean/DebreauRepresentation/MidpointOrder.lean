import EcoLean.DebreauRepresentation.GlobalCandidate
import Mathlib.Tactic.Linarith

/-!
# Order lemmas for the midpoint candidate

This file proves the basic comparison properties of the midpoint utility
candidate.

The key idea is simple: if the lower and upper cuts at a point are ordered in
the expected way, then the midpoint lies between them. This lets us turn
separation of cuts into separation of the midpoint candidate.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
If `r` belongs to the lower value set at `x`, and that lower value set is
bounded above, then `r` is at most the lower cut at `x`.
-/
theorem le_lowerCut_of_mem_lowerValue
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x : α} {r : ℝ}
    (hBdd : BddAbove (lowerValueSet P D u x))
    (hr : r ∈ lowerValueSet P D u x) :
    r ≤ lowerCut P D u x := by
  unfold lowerCut
  exact le_csSup hBdd hr

/--
If `s` belongs to the upper value set at `x`, and that upper value set is
bounded below, then the upper cut at `x` is at most `s`.
-/
theorem upperCut_le_of_mem_upperValue
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x : α} {s : ℝ}
    (hBdd : BddBelow (upperValueSet P D u x))
    (hs : s ∈ upperValueSet P D u x) :
    upperCut P D u x ≤ s := by
  unfold upperCut
  exact csInf_le hBdd hs

/--
If the upper cut at `x` is strictly below the lower cut at `y`, then the
midpoint candidate at `x` is strictly below the midpoint candidate at `y`,
provided each midpoint lies between its two cuts.
-/
theorem midpointUtility_lt_of_upperCut_lt_lowerCut
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x y : α}
    (hx : lowerCut P D u x ≤ upperCut P D u x)
    (hxy : upperCut P D u x < lowerCut P D u y)
    (hy : lowerCut P D u y ≤ upperCut P D u y) :
    midpointUtility P D u x < midpointUtility P D u y := by
  rw [midpointUtility_apply, midpointUtility_apply]
  linarith

/--
If there is a strict gap between some upper-section utility value at `x`
and some lower-section utility value at `y`, then the corresponding cuts are
strictly separated.
-/
theorem upperCut_lt_lowerCut_of_separated_values
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x y : α} {r s : ℝ}
    (hBddUpper : BddBelow (upperValueSet P D u x))
    (hBddLower : BddAbove (lowerValueSet P D u y))
    (hr : r ∈ upperValueSet P D u x)
    (hs : s ∈ lowerValueSet P D u y)
    (hrs : r < s) :
    upperCut P D u x < lowerCut P D u y := by
  have hxr : upperCut P D u x ≤ r :=
    upperCut_le_of_mem_upperValue P D u hBddUpper hr
  have hsy : s ≤ lowerCut P D u y :=
    le_lowerCut_of_mem_lowerValue P D u hBddLower hs
  linarith

/--
If there is a strict gap between some upper-section utility value at `x`
and some lower-section utility value at `y`, then the midpoint candidate at `x`
is strictly below the midpoint candidate at `y`, provided the cuts at `x` and
`y` are internally ordered.
-/
theorem midpointUtility_lt_of_separated_values
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x y : α} {r s : ℝ}
    (hx : lowerCut P D u x ≤ upperCut P D u x)
    (hy : lowerCut P D u y ≤ upperCut P D u y)
    (hBddUpper : BddBelow (upperValueSet P D u x))
    (hBddLower : BddAbove (lowerValueSet P D u y))
    (hr : r ∈ upperValueSet P D u x)
    (hs : s ∈ lowerValueSet P D u y)
    (hrs : r < s) :
    midpointUtility P D u x < midpointUtility P D u y := by
  apply midpointUtility_lt_of_upperCut_lt_lowerCut P D u hx ?_ hy
  exact upperCut_lt_lowerCut_of_separated_values P D u
    hBddUpper hBddLower hr hs hrs

/--
If `x ≽ y`, then the midpoint candidate at `y` is at most the midpoint
candidate at `x`, provided the two cuts are monotone in the required sense.
-/
theorem midpointUtility_mono_of_weakPref
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x y : α}
    (hLower : lowerCut P D u y ≤ lowerCut P D u x)
    (hUpper : upperCut P D u y ≤ upperCut P D u x) :
    midpointUtility P D u y ≤ midpointUtility P D u x := by
  rw [midpointUtility_apply, midpointUtility_apply]
  linarith

section Complete

/--
At a point of the dense subset `D`, the midpoint candidate agrees with both
cut candidates.
-/
theorem midpointUtility_eq_lowerCut_self
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    (d : D) :
    midpointUtility P D u d.1 = lowerCut P D u d.1 := by
  rw [midpointUtility_eq_on_dense P hC hT D u hu d,
      lowerCut_eq_self P hC hT D u hu d]

/--
At a point of the dense subset `D`, the midpoint candidate agrees with both
cut candidates.
-/
theorem midpointUtility_eq_upperCut_self
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    (d : D) :
    midpointUtility P D u d.1 = upperCut P D u d.1 := by
  rw [midpointUtility_eq_on_dense P hC hT D u hu d,
      upperCut_eq_self P hC hT D u hu d]

end Complete

end Preference
end EcoLean
