import EcoLean.SocialChoice.Properties.IIA

universe u v

namespace EcoLean
namespace SocialChoice

namespace Arrow

/--
Two profiles agree off voter `i` if every other voter has the same preference
relation in both profiles.
-/
def AgreeOff
    {V : Type u} {A : Type v}
    (P Q : Profile V A) (i : V) : Prop :=
  ∀ j : V, j ≠ i → Q j = P j

/--
If profiles agree on all voters, then they are equal.
-/
theorem profile_ext
    {V : Type u} {A : Type v}
    {P Q : Profile V A}
    (h : ∀ i : V, P i = Q i) :
    P = Q := by
  funext i
  exact h i

/--
Pairwise agreement is symmetric in the two profiles.
-/
theorem pairwiseAgreesOn_symm
    {V : Type u} {A : Type v}
    {P Q : Profile V A} {x y : A}
    (h : PairwiseAgreesOn P Q x y) :
    PairwiseAgreesOn Q P x y := by
  intro i
  rcases h i with ⟨hxy, hyx⟩
  exact ⟨hxy.symm, hyx.symm⟩

/--
If two profiles agree on the pair `(x, y)`, then they also agree on `(y, x)`.
-/
theorem pairwiseAgreesOn_swap
    {V : Type u} {A : Type v}
    {P Q : Profile V A} {x y : A}
    (h : PairwiseAgreesOn P Q x y) :
    PairwiseAgreesOn P Q y x := by
  intro i
  rcases h i with ⟨hxy, hyx⟩
  exact ⟨hyx, hxy⟩

/--
Any profile agrees with itself on every ordered pair.
-/
theorem pairwiseAgreesOn_refl
    {V : Type u} {A : Type v}
    (P : Profile V A) (x y : A) :
    PairwiseAgreesOn P P x y := by
  intro i
  exact ⟨Iff.rfl, Iff.rfl⟩

/--
If `F` satisfies IIA, then pairwise agreement transfers social weak preference
from `P` to `Q`.
-/
theorem social_weak_transfer
    {V : Type u} {A : Type v}
    {F : SocialWelfareFunction V A}
    (hIIA : IIA F)
    {P Q : Profile V A} {x y : A}
    (hagree : PairwiseAgreesOn P Q x y)
    (hP : SocialWelfareFunction.WeakPref F P x y) :
    SocialWelfareFunction.WeakPref F Q x y := by
  exact (hIIA P Q x y hagree).1.mp hP

/--
If `F` satisfies IIA, then pairwise agreement transfers social weak preference
from `Q` back to `P`.
-/
theorem social_weak_transfer_back
    {V : Type u} {A : Type v}
    {F : SocialWelfareFunction V A}
    (hIIA : IIA F)
    {P Q : Profile V A} {x y : A}
    (hagree : PairwiseAgreesOn P Q x y)
    (hQ : SocialWelfareFunction.WeakPref F Q x y) :
    SocialWelfareFunction.WeakPref F P x y := by
  exact (hIIA P Q x y hagree).1.mpr hQ

/--
If `F` satisfies IIA, then pairwise agreement transfers the reverse social weak
preference from `P` to `Q`.
-/
theorem social_weak_transfer_rev
    {V : Type u} {A : Type v}
    {F : SocialWelfareFunction V A}
    (hIIA : IIA F)
    {P Q : Profile V A} {x y : A}
    (hagree : PairwiseAgreesOn P Q x y)
    (hP : SocialWelfareFunction.WeakPref F P y x) :
    SocialWelfareFunction.WeakPref F Q y x := by
  have hswap : PairwiseAgreesOn P Q y x := pairwiseAgreesOn_swap hagree
  exact (hIIA P Q y x hswap).1.mp hP

/--
If `F` satisfies IIA, then pairwise agreement transfers social strict preference
from `P` to `Q`.
-/
theorem social_strict_transfer
    {V : Type u} {A : Type v}
    {F : SocialWelfareFunction V A}
    (hIIA : IIA F)
    {P Q : Profile V A} {x y : A}
    (hagree : PairwiseAgreesOn P Q x y)
    (hP : SocialWelfareFunction.StrictPref F P x y) :
    SocialWelfareFunction.StrictPref F Q x y := by
  constructor
  · exact social_weak_transfer hIIA hagree hP.1
  · intro hyx
    have hswap : PairwiseAgreesOn P Q y x := pairwiseAgreesOn_swap hagree
    exact hP.2 (social_weak_transfer_back hIIA hswap hyx)

/--
If `F` satisfies IIA, then pairwise agreement transfers social strict preference
from `Q` back to `P`.
-/
theorem social_strict_transfer_back
    {V : Type u} {A : Type v}
    {F : SocialWelfareFunction V A}
    (hIIA : IIA F)
    {P Q : Profile V A} {x y : A}
    (hagree : PairwiseAgreesOn P Q x y)
    (hQ : SocialWelfareFunction.StrictPref F Q x y) :
    SocialWelfareFunction.StrictPref F P x y := by
  have hsymm : PairwiseAgreesOn Q P x y := pairwiseAgreesOn_symm hagree
  exact social_strict_transfer hIIA hsymm hQ

end Arrow

end SocialChoice
end EcoLean
