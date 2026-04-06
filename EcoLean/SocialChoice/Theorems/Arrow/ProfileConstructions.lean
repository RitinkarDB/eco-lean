import EcoLean.SocialChoice.Theorems.Arrow.ProfileVariants

universe u v

namespace EcoLean
namespace SocialChoice

namespace Arrow

/--
A simple preference relation that makes `x` weakly preferred to everything and
everything weakly preferred to `y`.
-/
def prefXY {A : Type v} (x y : A) : Preference A where
  weakPref := fun a b => a = x ∨ b = y

/--
A simple preference relation that makes `y` weakly preferred to everything and
everything weakly preferred to `x`.
-/
def prefYX {A : Type v} (x y : A) : Preference A where
  weakPref := fun a b => a = y ∨ b = x

section SyntheticPreferences

variable {A : Type v} {x y : A}

theorem prefXY_weak_self_left :
    (prefXY x y).weakPref x x := by
  left
  rfl

theorem prefYX_weak_self_left :
    (prefYX x y).weakPref y y := by
  left
  rfl

theorem prefXY_strict
    (hxy : x ≠ y) :
    Preference.StrictPref (prefXY x y) x y := by
  constructor
  · left
    rfl
  · intro hyx
    cases hyx with
    | inl hy =>
        exact hxy hy.symm
    | inr hx =>
        exact hxy hx

theorem prefYX_strict
    (hxy : x ≠ y) :
    Preference.StrictPref (prefYX x y) y x := by
  constructor
  · left
    rfl
  · intro hxy'
    cases hxy' with
    | inl hx =>
        exact hxy hx
    | inr hy =>
        exact hxy hy.symm

theorem prefXY_not_reverse
    (hxy : x ≠ y) :
    ¬ (prefXY x y).weakPref y x := by
  intro hyx
  cases hyx with
  | inl hy =>
      exact hxy hy.symm
  | inr hx =>
      exact hxy hx

theorem prefYX_not_reverse
    (hxy : x ≠ y) :
    ¬ (prefYX x y).weakPref x y := by
  intro hxy'
  cases hxy' with
  | inl hx =>
      exact hxy hx
  | inr hy =>
      exact hxy hy.symm

end SyntheticPreferences

section ReplaceVoter

variable {V : Type u} {A : Type v} [DecidableEq V]

/--
Replace voter `i`'s preference in profile `P` by `R`.
-/
def replaceVoter (P : Profile V A) (i : V) (R : Preference A) : Profile V A :=
  fun j => if j = i then R else P j

@[simp] theorem replaceVoter_self
    (P : Profile V A) (i : V) (R : Preference A) :
    replaceVoter P i R i = R := by
  simp [replaceVoter]

@[simp] theorem replaceVoter_of_ne
    (P : Profile V A) (i j : V) (R : Preference A)
    (hji : j ≠ i) :
    replaceVoter P i R j = P j := by
  simp [replaceVoter, hji]

/--
Replacing voter `i` preserves every other voter's preference.
-/
theorem replaceVoter_agreeOff
    (P : Profile V A) (i : V) (R : Preference A) :
    AgreeOff P (replaceVoter P i R) i := by
  intro j hji
  exact replaceVoter_of_ne P i j R hji

/--
Replacing voter `i` with their original preference leaves the profile unchanged.
-/
theorem replaceVoter_same
    (P : Profile V A) (i : V) :
    replaceVoter P i (P i) = P := by
  apply profile_ext
  intro j
  by_cases h : j = i
  · simp [replaceVoter, h]
  · simp [replaceVoter, h]

end ReplaceVoter

end Arrow

end SocialChoice
end EcoLean
