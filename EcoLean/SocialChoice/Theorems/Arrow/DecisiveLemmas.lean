import EcoLean.SocialChoice.Theorems.Arrow.Decisive
import EcoLean.SocialChoice.Properties.CollectiveRationality

universe u v

namespace EcoLean
namespace SocialChoice

namespace Arrow

/--
If every voter strictly prefers `x` to `y`, then every voter weakly prefers
`x` to `y`.
-/
theorem unanimous_strict_implies_unanimous_weak
    {V : Type u} {A : Type v}
    {P : Profile V A} {x y : A}
    (h : ∀ i : V, Profile.StrictPref P i x y) :
    ∀ i : V, Profile.WeakPref P i x y := by
  intro i
  exact (h i).1

/--
If `F` satisfies Weak Pareto and every voter strictly prefers `x` to `y`, then
society weakly prefers `x` to `y`.
-/
theorem social_weak_of_unanimous_strict
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A)
    (hPareto : WeakPareto F)
    {P : Profile V A} {x y : A}
    (h : ∀ i : V, Profile.StrictPref P i x y) :
    SocialWelfareFunction.WeakPref F P x y := by
  apply hPareto P x y
  exact unanimous_strict_implies_unanimous_weak h

/--
If `F` is rational, then at each profile its social preference is complete.
-/
theorem social_complete
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A)
    (hRat : RationalSWF F)
    (P : Profile V A) :
    (F P).Complete :=
  hRat.1 P

/--
If `F` is rational, then at each profile its social preference is transitive.
-/
theorem social_transitive
    {V : Type u} {A : Type v}
    (F : SocialWelfareFunction V A)
    (hRat : RationalSWF F)
    (P : Profile V A) :
    (F P).Transitive :=
  hRat.2 P

end Arrow

end SocialChoice
end EcoLean
