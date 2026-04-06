import EcoLean.SocialChoice.Basic.SocialChoiceFunction

universe u v

namespace EcoLean
namespace SocialChoice

/--
Voter `i` is a dictator for `f` if the social outcome is always that voter's
strict top-ranked alternative.
-/
def IsDictator
    {V : Type u} {A : Type v}
    (f : SocialChoiceFunction V A) (i : V) : Prop :=
  ∀ P : Profile V A, ∀ y : A, y ≠ f P → f P ≻[P,i] y

/--
A social choice function is dictatorial if some voter is a dictator.
-/
def Dictatorial
    {V : Type u} {A : Type v}
    (f : SocialChoiceFunction V A) : Prop :=
  ∃ i : V, IsDictator f i

namespace Dictatorial

variable {V : Type u} {A : Type v} {f : SocialChoiceFunction V A}

theorem witness
    (h : Dictatorial f) :
    ∃ i : V, IsDictator f i := by
  exact h

end Dictatorial

end SocialChoice
end EcoLean
