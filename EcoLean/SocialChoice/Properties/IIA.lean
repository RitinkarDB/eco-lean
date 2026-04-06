import EcoLean.SocialChoice.Basic.SocialWelfareFunction

universe u v

namespace EcoLean
namespace SocialChoice

/--
Profiles `P` and `Q` agree on the pairwise comparison of `x` and `y` for every voter.
-/
def PairwiseAgreesOn
    {V : Type u} {A : Type v}
    (P Q : Profile V A) (x y : A) : Prop :=
  ∀ i : V,
    ((Profile.WeakPref P i x y ↔ Profile.WeakPref Q i x y) ∧
     (Profile.WeakPref P i y x ↔ Profile.WeakPref Q i y x))

/--
Independence of Irrelevant Alternatives: the social comparison of `x` and `y`
depends only on individuals' comparisons of `x` and `y`.
-/
def IIA
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) : Prop :=
  ∀ (P Q : Profile V A) (x y : A),
    PairwiseAgreesOn P Q x y →
    ((SocialWelfareFunction.WeakPref F P x y ↔
      SocialWelfareFunction.WeakPref F Q x y) ∧
     (SocialWelfareFunction.WeakPref F P y x ↔
      SocialWelfareFunction.WeakPref F Q y x))

namespace PairwiseAgreesOn

variable {V : Type u} {A : Type v}
variable {P Q : Profile V A} {x y : A}

theorem apply
    (h : PairwiseAgreesOn P Q x y) (i : V) :
    (Profile.WeakPref P i x y ↔ Profile.WeakPref Q i x y) ∧
    (Profile.WeakPref P i y x ↔ Profile.WeakPref Q i y x) :=
  h i

end PairwiseAgreesOn

namespace IIA

variable {V : Type u} {A : Type v} {F : SocialWelfareFunction V A}

theorem apply
    (h : IIA F)
    (P Q : Profile V A) (x y : A)
    (hxy : PairwiseAgreesOn P Q x y) :
    ((SocialWelfareFunction.WeakPref F P x y ↔
      SocialWelfareFunction.WeakPref F Q x y) ∧
     (SocialWelfareFunction.WeakPref F P y x ↔
      SocialWelfareFunction.WeakPref F Q y x)) :=
  h P Q x y hxy

end IIA

end SocialChoice
end EcoLean
