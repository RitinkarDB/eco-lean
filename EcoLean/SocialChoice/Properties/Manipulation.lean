import EcoLean.SocialChoice.Basic.SocialChoiceFunction

universe u v

namespace EcoLean
namespace SocialChoice

/--
At preference `P`, alternative `x` is weakly preferred by voter `i` to
alternative `y`.
-/
def WeaklyPrefersOutcome
    {V : Type u} {A : Type v}
    (P : Profile V A) (i : V) (x y : A) : Prop :=
  x ≽[P,i] y

/--
At preference `P`, alternative `x` is strictly preferred by voter `i` to
alternative `y`.
-/
def StrictlyPrefersOutcome
    {V : Type u} {A : Type v}
    (P : Profile V A) (i : V) (x y : A) : Prop :=
  x ≻[P,i] y

/--
`P'` is a unilateral deviation from `P` by voter `i` if all other voters keep
the same preferences.
-/
def IsDeviation
    {V : Type u} {A : Type v}
    (P P' : Profile V A) (i : V) : Prop :=
  ∀ j : V, j ≠ i → P' j = P j

/--
Voter `i` can manipulate `f` at profile `P` by reporting `P'` if `P'` differs
from `P` only in voter `i`'s report and the outcome under `P'` is strictly
better for `i`, according to `i`'s true preference in `P`.
-/
def Manipulates
    {V : Type u} {A : Type v}
    (f : SocialChoiceFunction V A)
    (i : V) (P P' : Profile V A) : Prop :=
  IsDeviation P P' i ∧ StrictlyPrefersOutcome P i (f P') (f P)

/--
The social choice function `f` is manipulable by voter `i` if there exist a true
profile and a unilateral deviation yielding a strictly better outcome for `i`.
-/
def ManipulableBy
    {V : Type u} {A : Type v}
    (f : SocialChoiceFunction V A) (i : V) : Prop :=
  ∃ P P' : Profile V A, Manipulates f i P P'

/--
The social choice function `f` is manipulable if some voter can manipulate it.
-/
def Manipulable
    {V : Type u} {A : Type v}
    (f : SocialChoiceFunction V A) : Prop :=
  ∃ i : V, ManipulableBy f i

namespace Manipulates

variable {V : Type u} {A : Type v}
variable {f : SocialChoiceFunction V A} {i : V} {P P' : Profile V A}

theorem deviation
    (h : Manipulates f i P P') :
    IsDeviation P P' i :=
  h.1

theorem improves
    (h : Manipulates f i P P') :
    StrictlyPrefersOutcome P i (f P') (f P) :=
  h.2

end Manipulates

end SocialChoice
end EcoLean
