import EcoLean.SocialChoice.Basic.SocialChoiceFunction

universe u v

namespace EcoLean
namespace SocialChoice

/--
A social choice function is onto if every alternative is selected at some profile.
-/
def Onto
    {V : Type u} {A : Type v}
    (f : SocialChoiceFunction V A) : Prop :=
  ∀ x : A, ∃ P : Profile V A, f P = x

namespace Onto

variable {V : Type u} {A : Type v} {f : SocialChoiceFunction V A}

theorem image_nonempty
    (h : Onto f) (x : A) :
    ∃ P : Profile V A, f P = x :=
  h x

end Onto

end SocialChoice
end EcoLean
