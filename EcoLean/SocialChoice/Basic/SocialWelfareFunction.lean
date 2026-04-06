import EcoLean.SocialChoice.Basic.Profile

universe u v

namespace EcoLean
namespace SocialChoice

/--
A social welfare function assigns a social preference relation to each profile.
-/
abbrev SocialWelfareFunction (V : Type u) (A : Type v) : Type (max u v) :=
  Profile V A → Preference A

namespace SocialWelfareFunction

variable {V : Type u} {A : Type v}

/-- Evaluate a social welfare function at a profile. -/
@[simp] abbrev eval (F : SocialWelfareFunction V A) (P : Profile V A) : Preference A :=
  F P

/-- The social weak preference induced by `F` at profile `P`. -/
def WeakPref (F : SocialWelfareFunction V A) (P : Profile V A) (x y : A) : Prop :=
  (F P).weakPref x y

/-- The social strict preference induced by `F` at profile `P`. -/
def StrictPref (F : SocialWelfareFunction V A) (P : Profile V A) (x y : A) : Prop :=
  (F P).StrictPref x y

/-- The social indifference induced by `F` at profile `P`. -/
def Indiff (F : SocialWelfareFunction V A) (P : Profile V A) (x y : A) : Prop :=
  (F P).Indiff x y

scoped notation:50 x " ≽ₛ[" F "," P "] " y => SocialWelfareFunction.WeakPref F P x y
scoped notation:50 x " ≻ₛ[" F "," P "] " y => SocialWelfareFunction.StrictPref F P x y
scoped notation:50 x " ∼ₛ[" F "," P "] " y => SocialWelfareFunction.Indiff F P x y

theorem strictPref_def
    (F : SocialWelfareFunction V A) (P : Profile V A) (x y : A) :
    SocialWelfareFunction.StrictPref F P x y ↔
      ((F P).weakPref x y ∧ ¬ (F P).weakPref y x) := by
  rfl

theorem indiff_def
    (F : SocialWelfareFunction V A) (P : Profile V A) (x y : A) :
    SocialWelfareFunction.Indiff F P x y ↔
      ((F P).weakPref x y ∧ (F P).weakPref y x) := by
  rfl

end SocialWelfareFunction

end SocialChoice
end EcoLean
