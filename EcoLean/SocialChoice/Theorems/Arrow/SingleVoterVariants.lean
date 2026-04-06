import EcoLean.SocialChoice.Theorems.Arrow.ProfileConstructions

universe u v

namespace EcoLean
namespace SocialChoice

namespace Arrow

section SingleVoterVariants

variable {V : Type u} {A : Type v} [DecidableEq V]

/--
If voter `i`'s replacement preference agrees with their original preference on
`x` versus `y`, then replacing `i` preserves pairwise agreement on `(x, y)`.
-/
theorem pairwiseAgreesOn_replaceVoter
    (P : Profile V A) (i : V) (R : Preference A) (x y : A)
    (hxy : (P i).weakPref x y ↔ R.weakPref x y)
    (hyx : (P i).weakPref y x ↔ R.weakPref y x) :
    PairwiseAgreesOn P (replaceVoter P i R) x y := by
  intro j
  by_cases hj : j = i
  · subst hj
    constructor
    · simpa [Profile.WeakPref, replaceVoter] using hxy
    · simpa [Profile.WeakPref, replaceVoter] using hyx
  · constructor
    · simp [Profile.WeakPref, replaceVoter, hj]
    · simp [Profile.WeakPref, replaceVoter, hj]

/--
A variant of the previous lemma with the profiles reversed.
-/
theorem pairwiseAgreesOn_replaceVoter_symm
    (P : Profile V A) (i : V) (R : Preference A) (x y : A)
    (hxy : (P i).weakPref x y ↔ R.weakPref x y)
    (hyx : (P i).weakPref y x ↔ R.weakPref y x) :
    PairwiseAgreesOn (replaceVoter P i R) P x y := by
  exact pairwiseAgreesOn_symm (pairwiseAgreesOn_replaceVoter P i R x y hxy hyx)

/--
If voter `i`'s replacement preference preserves their comparison of `x` and `y`,
then IIA transfers the social comparison of `x` and `y` across the replacement.
-/
theorem social_weak_replaceVoter
    {F : SocialWelfareFunction V A}
    (hIIA : IIA F)
    (P : Profile V A) (i : V) (R : Preference A) (x y : A)
    (hxy : (P i).weakPref x y ↔ R.weakPref x y)
    (hyx : (P i).weakPref y x ↔ R.weakPref y x) :
    (SocialWelfareFunction.WeakPref F P x y ↔
      SocialWelfareFunction.WeakPref F (replaceVoter P i R) x y) := by
  exact (hIIA P (replaceVoter P i R) x y
    (pairwiseAgreesOn_replaceVoter P i R x y hxy hyx)).1

/--
The strict social comparison also transfers across a one-voter replacement that
preserves the replaced voter's comparison of `x` and `y`.
-/
theorem social_strict_replaceVoter
    {F : SocialWelfareFunction V A}
    (hIIA : IIA F)
    (P : Profile V A) (i : V) (R : Preference A) (x y : A)
    (hxy : (P i).weakPref x y ↔ R.weakPref x y)
    (hyx : (P i).weakPref y x ↔ R.weakPref y x) :
    (SocialWelfareFunction.StrictPref F P x y ↔
      SocialWelfareFunction.StrictPref F (replaceVoter P i R) x y) := by
  constructor
  · intro hP
    exact social_strict_transfer hIIA
      (pairwiseAgreesOn_replaceVoter P i R x y hxy hyx) hP
  · intro hR
    exact social_strict_transfer_back hIIA
      (pairwiseAgreesOn_replaceVoter P i R x y hxy hyx) hR

end SingleVoterVariants

end Arrow

end SocialChoice
end EcoLean
