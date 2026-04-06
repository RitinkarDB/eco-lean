import EcoLean.SocialChoice.Basic.Preference

universe u v

namespace EcoLean
namespace SocialChoice

/--
A preference profile assigns a preference relation over alternatives to each voter.
-/
abbrev Profile (V : Type u) (A : Type v) : Type (max u v) :=
  V → Preference A

variable {V : Type u} {A : Type v}

/-- The preference of voter `i` in profile `P`. -/
@[simp] abbrev Profile.pref (P : Profile V A) (i : V) : Preference A :=
  P i

/-- Voter `i` weakly prefers `x` to `y` under profile `P`. -/
def Profile.WeakPref (P : Profile V A) (i : V) (x y : A) : Prop :=
  (P i).weakPref x y

/-- Voter `i` strictly prefers `x` to `y` under profile `P`. -/
def Profile.StrictPref (P : Profile V A) (i : V) (x y : A) : Prop :=
  (P i).StrictPref x y

/-- Voter `i` is indifferent between `x` and `y` under profile `P`. -/
def Profile.Indiff (P : Profile V A) (i : V) (x y : A) : Prop :=
  (P i).Indiff x y

scoped notation:50 x " ≽[" P "," i "] " y => Profile.WeakPref P i x y
scoped notation:50 x " ≻[" P "," i "] " y => Profile.StrictPref P i x y
scoped notation:50 x " ∼[" P "," i "] " y => Profile.Indiff P i x y

theorem Profile.strictPref_def_notation
    (P : Profile V A) (i : V) (x y : A) :
    (x ≻[P,i] y) ↔ ((x ≽[P,i] y) ∧ ¬ (y ≽[P,i] x)) := by
  rfl

theorem Profile.indiff_def_notation
    (P : Profile V A) (i : V) (x y : A) :
    (x ∼[P,i] y) ↔ ((x ≽[P,i] y) ∧ (y ≽[P,i] x)) := by
  rfl

end SocialChoice
end EcoLean
