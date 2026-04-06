import EcoLean.SocialChoice.Theorems.Arrow.Decisive
import EcoLean.SocialChoice.Theorems.Arrow.ProfileVariants
import EcoLean.SocialChoice.Theorems.Arrow.ProfileConstructions
import EcoLean.SocialChoice.Theorems.Arrow.SingleVoterVariants

universe u v

namespace EcoLean
namespace SocialChoice

namespace Arrow

section DecisiveFacts

variable {V : Type u} {A : Type v}

/--
If a coalition is decisive for `x` over `y`, then any profile witnessing the
required pattern of individual strict preferences yields the corresponding
social strict preference.
-/
theorem decisive_on_profile
    {F : SocialWelfareFunction V A}
    {S : Set V} {x y : A}
    (hS : Decisive F S x y)
    (P : Profile V A)
    (hIn : ∀ i : V, i ∈ S → Profile.StrictPref P i x y)
    (hOut : ∀ i : V, i ∉ S → Profile.StrictPref P i y x) :
    SocialWelfareFunction.StrictPref F P x y := by
  exact hS P hIn hOut

/--
Universal decisiveness immediately gives decisiveness for any distinct ordered
pair.
-/
theorem universallyDecisive_of_pair
    {F : SocialWelfareFunction V A}
    {S : Set V}
    (hS : UniversallyDecisive F S)
    {x y : A}
    (hxy : x ≠ y) :
    Decisive F S x y := by
  exact hS x y hxy

/--
A dictator in the SWF sense induces universal singleton decisiveness, once we
have a profile whose designated voter strictly ranks one alternative over the
other and all others rank the reverse way.
-/
theorem dictator_singleton_decisive
    {F : SocialWelfareFunction V A}
    {i : V}
    (hD : IsDictatorSWF F i)
    {x y : A} :
    Decisive F ({i} : Set V) x y := by
  intro P hIn hOut
  have hi : Profile.StrictPref P i x y := by
    exact hIn i (by show i = i; rfl)
  exact hD P x y hi

/--
A dictator in the SWF sense induces universal singleton decisiveness.
-/
theorem dictator_singleton_universallyDecisive
    {F : SocialWelfareFunction V A}
    {i : V}
    (hD : IsDictatorSWF F i) :
    UniversallyDecisive F ({i} : Set V) := by
  intro x y _hxy
  exact dictator_singleton_decisive hD

/--
If `F` is dictatorial in the SWF sense, then some singleton coalition is
universally decisive.
-/
theorem dictatorialSWF_has_singleton_universallyDecisive
    {F : SocialWelfareFunction V A}
    (hD : DictatorialSWF F) :
    ∃ i : V, UniversallyDecisive F ({i} : Set V) := by
  rcases hD with ⟨i, hi⟩
  exact ⟨i, dictator_singleton_universallyDecisive hi⟩

end DecisiveFacts

end Arrow

end SocialChoice
end EcoLean
