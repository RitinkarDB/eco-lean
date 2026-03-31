import EcoLean.DebreauRepresentation.AnchoredCuts
import EcoLean.DebreauRepresentation.SeparatedValues
import Mathlib.Tactic.Linarith

/-!
# Representation via anchored midpoint cuts

This file defines the anchored midpoint candidate and proves that, for the
arctan-adjusted restricted utility on a Debreu-dense subset, it represents the
ambient preference.

This gives the order-theoretic representation step. The remaining work after
this file is the continuity step.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u}

/--
The anchored midpoint candidate utility on the whole space.
-/
noncomputable def anchoredMidpointUtility
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) : α → ℝ :=
  fun x => (anchoredLowerCut P D u x + anchoredUpperCut P D u x) / 2

@[simp] theorem anchoredMidpointUtility_apply
    (P : Preference α) (D : Set α)
    (u : Utility.UtilityFunction D) (x : α) :
    anchoredMidpointUtility P D u x =
      (anchoredLowerCut P D u x + anchoredUpperCut P D u x) / 2 := by
  rfl

/--
Anchored lower value sets are monotone under weak preference.
-/
theorem anchoredLowerValueSet_mono_of_weakPref
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x y : α}
    (hxy : P.weakPref x y) :
    anchoredLowerValueSet P D u y ⊆ anchoredLowerValueSet P D u x := by
  intro r hr
  rcases hr with hr | rfl
  · exact Or.inl (lowerValueSet_mono_of_weakPref P hT D u hxy hr)
  · exact Or.inr rfl

/--
Anchored upper value sets are monotone under weak preference.
-/
theorem anchoredUpperValueSet_mono_of_weakPref
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x y : α}
    (hxy : P.weakPref x y) :
    anchoredUpperValueSet P D u x ⊆ anchoredUpperValueSet P D u y := by
  intro r hr
  rcases hr with hr | rfl
  · exact Or.inl (upperValueSet_mono_of_weakPref P hT D u hxy hr)
  · exact Or.inr rfl

/--
Anchored lower cuts are monotone under weak preference.
-/
theorem anchoredLowerCut_mono_of_weakPref
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x y : α}
    (hxy : P.weakPref x y)
    (hBddX : BddAbove (anchoredLowerValueSet P D u x)) :
    anchoredLowerCut P D u y ≤ anchoredLowerCut P D u x := by
  unfold anchoredLowerCut
  apply csSup_le
  · exact anchoredLowerValueSet_nonempty P D u y
  · intro r hr
    exact le_csSup hBddX
      ((anchoredLowerValueSet_mono_of_weakPref P hT D u hxy) hr)

/--
Anchored upper cuts are monotone under weak preference.
-/
theorem anchoredUpperCut_mono_of_weakPref
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x y : α}
    (hxy : P.weakPref x y)
    (hBddX : BddBelow (anchoredUpperValueSet P D u x))
    (hBddY : BddBelow (anchoredUpperValueSet P D u y)) :
    anchoredUpperCut P D u y ≤ anchoredUpperCut P D u x := by
  unfold anchoredUpperCut
  apply (le_csInf_iff hBddX (anchoredUpperValueSet_nonempty P D u x)).2
  intro r hr
  exact anchoredUpperCut_le_of_mem P D u hBddY
    ((anchoredUpperValueSet_mono_of_weakPref P hT D u hxy) hr)

/--
For the arctan-adjusted restricted utility, any lower-section value lies below
the anchored upper cut.
-/
theorem le_anchoredUpperCut_of_mem_lowerValue_arctanRestricted
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    {x : α} {r : ℝ}
    (hr : r ∈ lowerValueSet P D (arctanRestricted u) x) :
    r ≤ anchoredUpperCut P D (arctanRestricted u) x := by
  rcases hr with ⟨d, hd, rfl⟩
  unfold anchoredUpperCut
  exact (le_csInf_iff
    (anchoredUpperValueSet_bddBelow_arctanRestricted P D u x)
    (anchoredUpperValueSet_nonempty P D (arctanRestricted u) x)).2 (by
      intro s hs
      rcases hs with hs | rfl
      · exact lowerValue_le_upperValue P hT D (arctanRestricted u)
          (represents_arctanRestricted P u hu)
          (by exact ⟨d, hd, rfl⟩)
          hs
      · exact le_of_lt (Real.arctan_lt_pi_div_two (u d)))

/--
For the arctan-adjusted restricted utility, the anchored lower cut is at most
the anchored upper cut.
-/
theorem anchoredLowerCut_le_anchoredUpperCut_arctanRestricted
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    (x : α) :
    anchoredLowerCut P D (arctanRestricted u) x ≤
      anchoredUpperCut P D (arctanRestricted u) x := by
  unfold anchoredLowerCut
  apply csSup_le
  · exact anchoredLowerValueSet_nonempty P D (arctanRestricted u) x
  · intro r hr
    rcases hr with hr | rfl
    · exact le_anchoredUpperCut_of_mem_lowerValue_arctanRestricted
        P hT D u hu hr
    · exact leftEndpoint_le_anchoredUpperCut_arctanRestricted P D u x

/--
If there is a strict gap between some upper-section value at `y` and some
lower-section value at `x`, then the anchored cuts are strictly separated.
-/
theorem anchoredUpperCut_lt_anchoredLowerCut_of_separated_values_arctanRestricted
    (P : Preference α)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x y : α} {r s : ℝ}
    (hr : r ∈ upperValueSet P D (arctanRestricted u) y)
    (hs : s ∈ lowerValueSet P D (arctanRestricted u) x)
    (hrs : r < s) :
    anchoredUpperCut P D (arctanRestricted u) y <
      anchoredLowerCut P D (arctanRestricted u) x := by
  have hyr :
      anchoredUpperCut P D (arctanRestricted u) y ≤ r := by
    exact anchoredUpperCut_le_of_mem P D (arctanRestricted u)
      (anchoredUpperValueSet_bddBelow_arctanRestricted P D u y)
      (Or.inl hr)
  have hsx :
      s ≤ anchoredLowerCut P D (arctanRestricted u) x := by
    exact le_anchoredLowerCut_of_mem P D (arctanRestricted u)
      (anchoredLowerValueSet_bddAbove_arctanRestricted P D u x)
      (Or.inl hs)
  linarith

/--
If `x ≽ y`, then the anchored midpoint candidate at `y` is at most that at `x`.
-/
theorem anchoredMidpointUtility_ge_of_weakPref_arctanRestricted
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (u : Utility.UtilityFunction D)
    {x y : α}
    (hxy : P.weakPref x y) :
    anchoredMidpointUtility P D (arctanRestricted u) x ≥
      anchoredMidpointUtility P D (arctanRestricted u) y := by
  have hLower :
      anchoredLowerCut P D (arctanRestricted u) y ≤
        anchoredLowerCut P D (arctanRestricted u) x := by
    exact anchoredLowerCut_mono_of_weakPref P hT D (arctanRestricted u)
      hxy
      (anchoredLowerValueSet_bddAbove_arctanRestricted P D u x)
  have hUpper :
      anchoredUpperCut P D (arctanRestricted u) y ≤
        anchoredUpperCut P D (arctanRestricted u) x := by
    exact anchoredUpperCut_mono_of_weakPref P hT D (arctanRestricted u)
      hxy
      (anchoredUpperValueSet_bddBelow_arctanRestricted P D u x)
      (anchoredUpperValueSet_bddBelow_arctanRestricted P D u y)
  rw [anchoredMidpointUtility_apply, anchoredMidpointUtility_apply]
  linarith

/--
If `x ≻ y`, then the anchored midpoint candidate at `x` is strictly larger than
that at `y`.
-/
theorem anchoredMidpointUtility_gt_of_strictPref_arctanRestricted
    (P : Preference α)
    (hT : P.Transitive)
    (D : Set α)
    (hD : DebreuDense P D)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D))
    {x y : α}
    (hxy : P.StrictPref x y) :
    anchoredMidpointUtility P D (arctanRestricted u) x >
      anchoredMidpointUtility P D (arctanRestricted u) y := by
  rcases exists_separated_values_of_strictPref
      P D hD (arctanRestricted u) (represents_arctanRestricted P u hu) hxy with
    ⟨r, s, hr, hs, hrs⟩
  have hSep :
      anchoredUpperCut P D (arctanRestricted u) y <
        anchoredLowerCut P D (arctanRestricted u) x := by
    exact anchoredUpperCut_lt_anchoredLowerCut_of_separated_values_arctanRestricted
      P D u hr hs hrs
  have hy :
      anchoredLowerCut P D (arctanRestricted u) y ≤
        anchoredUpperCut P D (arctanRestricted u) y := by
    exact anchoredLowerCut_le_anchoredUpperCut_arctanRestricted
      P hT D u hu y
  have hx :
      anchoredLowerCut P D (arctanRestricted u) x ≤
        anchoredUpperCut P D (arctanRestricted u) x := by
    exact anchoredLowerCut_le_anchoredUpperCut_arctanRestricted
      P hT D u hu x
  rw [anchoredMidpointUtility_apply, anchoredMidpointUtility_apply]
  linarith

/--
The anchored midpoint candidate built from the arctan-adjusted restricted
utility represents the ambient preference.
-/
theorem anchoredMidpointUtility_represents_arctanRestricted
    (P : Preference α)
    (hC : P.Complete)
    (hT : P.Transitive)
    (D : Set α)
    (hD : DebreuDense P D)
    (u : Utility.UtilityFunction D)
    (hu : Represents u (restrict P D)) :
    Represents (anchoredMidpointUtility P D (arctanRestricted u)) P := by
  intro x y
  constructor
  · intro hxy
    exact anchoredMidpointUtility_ge_of_weakPref_arctanRestricted
      P hT D u hxy
  · intro hxy
    by_contra hNot
    have hyx : P.StrictPref y x := by
      have hyxWeak : P.weakPref y x := by
        rcases hC y x with hyx | hxy'
        · exact hyx
        · exact False.elim (hNot hxy')
      exact ⟨hyxWeak, hNot⟩
    have hlt :
        anchoredMidpointUtility P D (arctanRestricted u) x <
          anchoredMidpointUtility P D (arctanRestricted u) y := by
      exact anchoredMidpointUtility_gt_of_strictPref_arctanRestricted
        P hT D hD u hu hyx
    exact not_lt_of_ge hxy hlt

end Preference
end EcoLean
