import EcoLean.SocialChoice.Basic.SocialWelfareFunction

universe u v

namespace EcoLean
namespace SocialChoice

/--
Voter `i` is a dictator for the social welfare function `F` if, for every
profile, whenever `i` strictly prefers `x` to `y`, society also strictly
prefers `x` to `y`.
-/
def IsDictatorSWF
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) (i : V) : Prop :=
  ∀ (P : Profile V A) (x y : A),
    Profile.StrictPref P i x y →
    SocialWelfareFunction.StrictPref F P x y

/--
A social welfare function is dictatorial if some voter is a dictator.
-/
def DictatorialSWF
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) : Prop :=
  ∃ i : V, IsDictatorSWF F i

namespace IsDictatorSWF

variable {V : Type u} {A : Type v}
variable {F : SocialWelfareFunction V A} {i : V}

theorem apply
    (h : IsDictatorSWF F i)
    (P : Profile V A) (x y : A)
    (hxy : Profile.StrictPref P i x y) :
    SocialWelfareFunction.StrictPref F P x y :=
  h P x y hxy

end IsDictatorSWF

namespace DictatorialSWF

variable {V : Type u} {A : Type v} {F : SocialWelfareFunction V A}

theorem witness
    (h : DictatorialSWF F) :
    ∃ i : V, IsDictatorSWF F i :=
  h

end DictatorialSWF

end SocialChoice
end EcoLean