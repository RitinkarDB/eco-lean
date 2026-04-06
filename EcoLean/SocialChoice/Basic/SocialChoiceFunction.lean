import EcoLean.SocialChoice.Basic.Profile

universe u v

namespace EcoLean
namespace SocialChoice

/--
A social choice function assigns a chosen alternative to each preference profile.
-/
abbrev SocialChoiceFunction (V : Type u) (A : Type v) : Type (max u v) :=
  Profile V A → A

namespace SocialChoiceFunction

variable {V : Type u} {A : Type v}

/-- Evaluate a social choice function at a profile. -/
@[simp] abbrev eval (f : SocialChoiceFunction V A) (P : Profile V A) : A :=
  f P

end SocialChoiceFunction

end SocialChoice
end EcoLean
