import EcoLean.DebreauRepresentation.BoundedCuts
import EcoLean.DebreauRepresentation.SeparatedValues

/-!
# Conditional representation via the midpoint candidate

This file packages the final representation argument for the midpoint utility
candidate under the hypotheses that the lower and upper value sets are nonempty
at every point.

The remaining job after this file is to obtain those nonemptiness hypotheses
from the gap-adjustment step.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
If `x ≽ y`, then the midpoint candidate at `y` is at most the midpoint candidate
at `x`, provided the restricted utility image is bounded and both lower and
upper value sets are nonempty everywhere.
-/
theorem midpointUtility_ge_of_weakPref_of_image_bdd
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    (hAbove : BddAbove (restrictedUtilityImage u))
    (hBelow : BddBelow (restrictedUtilityImage u))
    (hLowerNonempty : ∀ x : α, (lowerValueSet P D u x).Nonempty)
    (hUpperNonempty : ∀ x : α, (upperValueSet P D u x).Nonempty)
    {x y : α}
    (hxy : P.weakPref x y) :
    midpointUtility P D u x ≥ midpointUtility P D u y := by
  have hLower :
      lowerCut P D u y ≤ lowerCut P D u x := by
    exact lowerCut_mono_of_weakPref P hT D u hxy
      (hLowerNonempty y)
      (lowerValueSet_bddAbove_of_image_bddAbove P D u x hAbove)
  have hUpper :
      upperCut P D u y ≤ upperCut P D u x := by
    exact upperCut_mono_of_weakPref P hT D u hxy
      (upperValueSet_bddBelow_of_image_bddBelow P D u x hBelow)
      (hUpperNonempty x)
      (upperValueSet_bddBelow_of_image_bddBelow P D u y hBelow)
  exact midpointUtility_mono_of_weakPref P D u hLower hUpper

/--
If `x ≻ y`, then the midpoint candidate at `x` is strictly larger than the
midpoint candidate at `y`, provided the restricted utility image is bounded and
both lower and upper value sets are nonempty everywhere.
-/
theorem midpointUtility_gt_of_strictPref_of_image_bdd
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (hD : DebreuDense P D)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    (hAbove : BddAbove (restrictedUtilityImage u))
    (hBelow : BddBelow (restrictedUtilityImage u))
    (hLowerNonempty : ∀ x : α, (lowerValueSet P D u x).Nonempty)
    (hUpperNonempty : ∀ x : α, (upperValueSet P D u x).Nonempty)
    {x y : α}
    (hxy : P.StrictPref x y) :
    midpointUtility P D u x > midpointUtility P D u y := by
  have hy :
      lowerCut P D u y ≤ upperCut P D u y := by
    exact lowerCut_le_upperCut_of_image_bdd P hT D u hu
      hAbove hBelow (hLowerNonempty y) (hUpperNonempty y)
  have hx :
      lowerCut P D u x ≤ upperCut P D u x := by
    exact lowerCut_le_upperCut_of_image_bdd P hT D u hu
      hAbove hBelow (hLowerNonempty x) (hUpperNonempty x)
  have hlt :
      midpointUtility P D u y < midpointUtility P D u x := by
    exact midpointUtility_lt_of_strictPref P D hD u hu hxy
      hy hx
      (upperValueSet_bddBelow_of_image_bddBelow P D u y hBelow)
      (lowerValueSet_bddAbove_of_image_bddAbove P D u x hAbove)
  exact hlt

/--
Under boundedness of the restricted utility image and nonemptiness of all lower
and upper value sets, the midpoint candidate represents `P`.
-/
theorem midpointUtility_represents_of_image_bdd
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (D : Set α)
    (hD : DebreuDense P D)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    (hAbove : BddAbove (restrictedUtilityImage u))
    (hBelow : BddBelow (restrictedUtilityImage u))
    (hLowerNonempty : ∀ x : α, (lowerValueSet P D u x).Nonempty)
    (hUpperNonempty : ∀ x : α, (upperValueSet P D u x).Nonempty) :
    Represents (midpointUtility P D u) P := by
  intro x y
  constructor
  · intro hxy
    exact midpointUtility_ge_of_weakPref_of_image_bdd
      P hT D u hu hAbove hBelow hLowerNonempty hUpperNonempty hxy
  · intro hxy
    by_contra hNot
    have hyx : P.StrictPref y x := by
      have hyxWeak : P.weakPref y x := by
        rcases hC y x with hyx | hxy'
        · exact hyx
        · exact False.elim (hNot hxy')
      exact ⟨hyxWeak, hNot⟩
    have hlt :
        midpointUtility P D u x < midpointUtility P D u y := by
      exact midpointUtility_gt_of_strictPref_of_image_bdd
        P hT D hD u hu hAbove hBelow hLowerNonempty hUpperNonempty hyx
    exact not_lt_of_ge hxy hlt

end Preference
end EcoLean
