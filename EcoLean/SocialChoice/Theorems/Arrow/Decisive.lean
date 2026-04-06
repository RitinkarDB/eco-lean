import EcoLean.SocialChoice.Basic.SocialWelfareFunction
import EcoLean.SocialChoice.Properties.Pareto
import EcoLean.SocialChoice.Properties.IIA
import EcoLean.SocialChoice.Properties.SWFDictatorship

universe u v

namespace EcoLean
namespace SocialChoice

/--
A set of voters `S` is decisive for `x` over `y` under `F` if, whenever every
voter in `S` strictly prefers `x` to `y` and every voter outside `S` strictly
prefers `y` to `x`, society strictly prefers `x` to `y`.
-/
def Decisive
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) (S : Set V) (x y : A) : Prop :=
  ∀ P : Profile V A,
    (∀ i : V, i ∈ S → Profile.StrictPref P i x y) →
    (∀ i : V, i ∉ S → Profile.StrictPref P i y x) →
    SocialWelfareFunction.StrictPref F P x y

/--
A set of voters `S` is universally decisive under `F` if it is decisive for
every ordered pair of distinct alternatives.
-/
def UniversallyDecisive
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) (S : Set V) : Prop :=
  ∀ x y : A, x ≠ y → Decisive F S x y

namespace Decisive

variable {V : Type u} {A : Type v}
variable {F : SocialWelfareFunction V A}
variable {S : Set V} {x y : A}

theorem apply
    (h : Decisive F S x y)
    (P : Profile V A)
    (hIn : ∀ i : V, i ∈ S → Profile.StrictPref P i x y)
    (hOut : ∀ i : V, i ∉ S → Profile.StrictPref P i y x) :
    SocialWelfareFunction.StrictPref F P x y :=
  h P hIn hOut

end Decisive

namespace UniversallyDecisive

variable {V : Type u} {A : Type v}
variable {F : SocialWelfareFunction V A}
variable {S : Set V}

theorem apply
    (h : UniversallyDecisive F S)
    (x y : A) (hxy : x ≠ y) :
    Decisive F S x y :=
  h x y hxy

end UniversallyDecisive

end SocialChoice
end EcoLean
