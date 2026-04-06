import Mathlib.Order.Basic

universe u

namespace EcoLean
namespace SocialChoice

/--
A preference relation on a domain `A`.

The primitive notion is weak preference.
-/
structure Preference (A : Type u) where
  weakPref : A → A → Prop

namespace Preference

variable {A : Type u} (P : Preference A)

/-- Strict preference derived from weak preference. -/
def StrictPref (x y : A) : Prop :=
  P.weakPref x y ∧ ¬ P.weakPref y x

/-- Indifference derived from weak preference. -/
def Indiff (x y : A) : Prop :=
  P.weakPref x y ∧ P.weakPref y x

/-- Completeness of weak preference. -/
def Complete : Prop :=
  ∀ x y : A, P.weakPref x y ∨ P.weakPref y x

/-- Transitivity of weak preference. -/
def Transitive : Prop :=
  ∀ x y z : A, P.weakPref x y → P.weakPref y z → P.weakPref x z

scoped notation:50 x " ≽[" P "] " y => Preference.weakPref P x y
scoped notation:50 x " ≻[" P "] " y => Preference.StrictPref P x y
scoped notation:50 x " ∼[" P "] " y => Preference.Indiff P x y

theorem weakPref_refl_of_complete
    (hC : P.Complete) (x : A) :
    P.weakPref x x := by
  cases hC x x with
  | inl hxx => exact hxx
  | inr hxx => exact hxx

end Preference

end SocialChoice
end EcoLean
