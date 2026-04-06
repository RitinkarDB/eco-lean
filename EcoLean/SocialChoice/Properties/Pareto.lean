import EcoLean.SocialChoice.Basic.SocialWelfareFunction

universe u v

namespace EcoLean
namespace SocialChoice

/--
Weak Pareto: if every voter weakly prefers `x` to `y`, then society weakly
prefers `x` to `y`.
-/
def WeakPareto
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) : Prop :=
  ∀ (P : Profile V A) (x y : A),
    (∀ i : V, Profile.WeakPref P i x y) →
    SocialWelfareFunction.WeakPref F P x y

/--
Strong Pareto: if every voter weakly prefers `x` to `y` and at least one voter
strictly prefers `x` to `y`, then society strictly prefers `x` to `y`.
-/
def StrongPareto
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) : Prop :=
  ∀ (P : Profile V A) (x y : A),
    (∀ i : V, Profile.WeakPref P i x y) →
    (∃ i : V, Profile.StrictPref P i x y) →
    SocialWelfareFunction.StrictPref F P x y

namespace WeakPareto

variable {V : Type u} {A : Type v} {F : SocialWelfareFunction V A}

theorem apply
    (h : WeakPareto F)
    (P : Profile V A) (x y : A)
    (hxy : ∀ i : V, Profile.WeakPref P i x y) :
    SocialWelfareFunction.WeakPref F P x y :=
  h P x y hxy

end WeakPareto

namespace StrongPareto

variable {V : Type u} {A : Type v} {F : SocialWelfareFunction V A}

theorem apply
    (h : StrongPareto F)
    (P : Profile V A) (x y : A)
    (hweak : ∀ i : V, Profile.WeakPref P i x y)
    (hstrict : ∃ i : V, Profile.StrictPref P i x y) :
    SocialWelfareFunction.StrictPref F P x y :=
  h P x y hweak hstrict

end StrongPareto

end SocialChoice
end EcoLean
