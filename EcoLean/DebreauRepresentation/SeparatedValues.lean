import EcoLean.DebreauRepresentation.MidpointOrder
import Mathlib.Tactic.Linarith

/-!
# Separated values from a Debreu-dense subset

This file extracts strict separation in utility values from strict preference,
using a Debreu-dense subset together with a utility representation on that
subset.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
On a restricted domain, strict preference corresponds to strict inequality of
any representing utility.
-/
theorem strictPref_iff_lt_of_represents_restrict
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    {x y : D} :
    P.StrictPref x.1 y.1 ↔ u x > u y := by
  constructor
  · intro hxy
    have hxy_ge : u x ≥ u y := (hu x y).mp hxy.1
    have hyx_not : ¬ P.weakPref y.1 x.1 := hxy.2
    have hnot_ge : ¬ u y ≥ u x := by
      intro hyx_ge
      exact hyx_not ((hu y x).mpr hyx_ge)
    linarith
  · intro hlt
    have hxy : P.weakPref x.1 y.1 := by
      exact (hu x y).mpr (by linarith)
    have hyx_not : ¬ P.weakPref y.1 x.1 := by
      intro hyx
      have hyx_ge : u y ≥ u x := (hu y x).mp hyx
      linarith
    exact ⟨hxy, hyx_not⟩

/--
If `x ≻ y`, then the Debreu-dense subset supplies two restricted utility values,
one in the upper value set of `y` and one in the lower value set of `x`, with
the former strictly smaller than the latter.
-/
theorem exists_separated_values_of_strictPref
    (P : Preference α)
    (D : Set α)
    (hD : DebreuDense P D)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    {x y : α}
    (hxy : P.StrictPref x y) :
    ∃ r s : ℝ,
      r ∈ upperValueSet P D u y ∧
      s ∈ lowerValueSet P D u x ∧
      r < s := by
  rcases hD hxy with ⟨z, hzD, hxz, hzy⟩
  rcases hD hxz with ⟨d, hdD, hxd, hdz⟩

  let zD : D := ⟨z, hzD⟩
  let dD : D := ⟨d, hdD⟩

  refine ⟨u zD, u dD, ?_, ?_, ?_⟩

  · exact ⟨zD, hzy.1, rfl⟩

  · exact ⟨dD, hxd.1, rfl⟩

  · have hlt : u dD > u zD := by
      exact (strictPref_iff_lt_of_represents_restrict P D u hu).mp hdz
    linarith
/--
If `x ≻ y`, then the midpoint candidate at `y` is strictly below the midpoint
candidate at `x`, provided the relevant lower and upper cuts are internally
ordered and have the boundedness hypotheses needed by the cut lemmas.
-/
theorem midpointUtility_lt_of_strictPref
    (P : Preference α)
    (D : Set α)
    (hD : DebreuDense P D)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    {x y : α}
    (hxy : P.StrictPref x y)
    (hy : lowerCut P D u y ≤ upperCut P D u y)
    (hx : lowerCut P D u x ≤ upperCut P D u x)
    (hBddUpperY : BddBelow (upperValueSet P D u y))
    (hBddLowerX : BddAbove (lowerValueSet P D u x)) :
    midpointUtility P D u y < midpointUtility P D u x := by
  rcases exists_separated_values_of_strictPref P D hD u hu hxy with
  ⟨r, s, hr, hs, hrs⟩ 
  exact midpointUtility_lt_of_separated_values P D u
    hy hx hBddUpperY hBddLowerX hr hs hrs

end Preference
end EcoLean
