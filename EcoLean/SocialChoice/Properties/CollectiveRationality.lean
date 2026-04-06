import EcoLean.SocialChoice.Basic.SocialWelfareFunction

universe u v

namespace EcoLean
namespace SocialChoice

/--
A social welfare function is complete if, at every profile, the induced social
preference is complete.
-/
def CompleteSWF
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) : Prop :=
  ∀ P : Profile V A, (F P).Complete

/--
A social welfare function is transitive if, at every profile, the induced social
preference is transitive.
-/
def TransitiveSWF
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) : Prop :=
  ∀ P : Profile V A, (F P).Transitive

/--
A social welfare function is rational if, at every profile, the induced social
preference is complete and transitive.
-/
def RationalSWF
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A) : Prop :=
  CompleteSWF F ∧ TransitiveSWF F

/--
A profile is rational if every voter's preference is complete and transitive.
-/
def RationalProfile
    {V : Type u} {A : Type v}
    (P : Profile V A) : Prop :=
  ∀ i : V, (P i).Complete ∧ (P i).Transitive

namespace CompleteSWF

variable {V : Type u} {A : Type v} {F : SocialWelfareFunction V A}

theorem apply
    (h : CompleteSWF F)
    (P : Profile V A) :
    (F P).Complete :=
  h P

end CompleteSWF

namespace TransitiveSWF

variable {V : Type u} {A : Type v} {F : SocialWelfareFunction V A}

theorem apply
    (h : TransitiveSWF F)
    (P : Profile V A) :
    (F P).Transitive :=
  h P

end TransitiveSWF

namespace RationalSWF

variable {V : Type u} {A : Type v} {F : SocialWelfareFunction V A}

theorem complete
    (h : RationalSWF F)
    (P : Profile V A) :
    (F P).Complete :=
  h.1 P

theorem transitive
    (h : RationalSWF F)
    (P : Profile V A) :
    (F P).Transitive :=
  h.2 P

end RationalSWF

namespace RationalProfile

variable {V : Type u} {A : Type v} {P : Profile V A}

theorem complete
    (h : RationalProfile P)
    (i : V) :
    (P i).Complete :=
  (h i).1

theorem transitive
    (h : RationalProfile P)
    (i : V) :
    (P i).Transitive :=
  (h i).2

end RationalProfile

end SocialChoice
end EcoLean
