import EcoLean.SocialChoice.Theorems.Arrow.PivotalVoter
import EcoLean.SocialChoice.Theorems.Arrow.ThreeWayProfiles
import EcoLean.SocialChoice.Properties.Pareto
import EcoLean.SocialChoice.Properties.IIA
import EcoLean.SocialChoice.Properties.CollectiveRationality

universe u v

namespace EcoLean
namespace SocialChoice

namespace Arrow

section SingletonTransfer

variable {V : Type u} {A : Type v}
variable [Fintype V] [DecidableEq V]

/--
If the social welfare function is rational, then social weak preference is transitive
at every profile.
-/
theorem social_weak_trans
    {F : SocialWelfareFunction V A}
    (hRat : RationalSWF F)
    (P : Profile V A)
    {a b c : A}
    (hab : SocialWelfareFunction.WeakPref F P a b)
    (hbc : SocialWelfareFunction.WeakPref F P b c) :
    SocialWelfareFunction.WeakPref F P a c := by
  exact (RationalSWF.transitive hRat P) a b c hab hbc

/--
If the social welfare function is rational, then social strict preference is
obtained from weak preference plus failure of the reverse weak preference.
-/
theorem social_strict_of_weak_not_reverse
    {F : SocialWelfareFunction V A}
    (P : Profile V A)
    {a b : A}
    (hab : SocialWelfareFunction.WeakPref F P a b)
    (hnot : ¬ SocialWelfareFunction.WeakPref F P b a) :
    SocialWelfareFunction.StrictPref F P a b := by
  exact ⟨hab, hnot⟩

theorem social_weak_yz_in_threeway_profile
    {F : SocialWelfareFunction V A}
    (hPareto : WeakPareto F)
    {i : V}
    {x y z : A}
    (Q : Profile V A)
    (hQ :
      ∀ k : V,
        (k = i → Q k = prefXYZ x y z) ∧
        (k ≠ i → Q k = prefYZX x y z)) :
    SocialWelfareFunction.WeakPref F Q y z := by
  apply hPareto Q y z
  intro k
  change (Q k).weakPref y z
  by_cases hk : k = i
  · rw [(hQ k).1 hk]
    exact prefXYZ_yz_weak
  · rw [(hQ k).2 hk]
    exact prefYZX_yz_weak

theorem social_strict_xy_in_threeway_profile
    {F : SocialWelfareFunction V A}
    {i : V}
    {x y z : A}
    (hSingle : Decisive F ({i} : Set V) x y)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (Q : Profile V A)
    (hQ :
      ∀ k : V,
        (k = i → Q k = prefXYZ x y z) ∧
        (k ≠ i → Q k = prefYZX x y z)) :
    SocialWelfareFunction.StrictPref F Q x y := by
  apply hSingle Q
  · intro k hk
    change Preference.StrictPref (Q k) x y
    rw [(hQ k).1 hk]
    exact prefXYZ_xy hxy hxz
  · intro k hk
    change Preference.StrictPref (Q k) y x
    rw [(hQ k).2 hk]
    exact prefYZX_yx hxy.symm

theorem pairwiseAgreesOn_xz_with_threeway_profile
    (i : V)
    {x y z : A}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (P : Profile V A)
    (hIn : ∀ k ∈ ({j : V | j = i} : Set V), Profile.StrictPref P k x z)
    (hOut : ∀ k ∉ ({j : V | j = i} : Set V), Profile.StrictPref P k z x) :
    PairwiseAgreesOn P
      (fun k => if k = i then prefXYZ x y z else prefYZX x y z)
      x z := by
  let S : Set V := {j : V | j = i}
  let Q : Profile V A := fun k => if k = i then prefXYZ x y z else prefYZX x y z
  intro k
  by_cases hk : k ∈ S
  · have hki : k = i := by
      simpa [S] using hk
    constructor
    · change (P k).weakPref x z ↔ (Q k).weakPref x z
      rw [hki]
      constructor
      · intro _
        simp [Q]
        exact prefXYZ_xz_weak
      · intro _
        exact (hIn i (by simp [S])).1
    · change (P k).weakPref z x ↔ (Q k).weakPref z x
      rw [hki]
      constructor
      · intro hz
        exact False.elim ((hIn i (by simp [S])).2 hz)
      · intro hz
        simp [Q, prefXYZ] at hz
        cases hz with
        | inl hzx =>
            exact False.elim (hxz hzx.symm)
        | inr hz' =>
            cases hz' with
            | inl hxz' =>
                exact False.elim (hxz hxz')
            | inr hzx' =>
                exact False.elim (hxz hzx'.symm)
  · have hki : k ≠ i := by
      intro hEq
      apply hk
      simp [S, hEq]
    constructor
    · change (P k).weakPref x z ↔ (Q k).weakPref x z
      constructor
      · intro hxzP
        exact False.elim ((hOut k (by simpa [S] using hk)).2 hxzP)
      · intro hxzQ
        simp [Q, hki, prefYZX] at hxzQ
        cases hxzQ with
        | inl hxy' =>
            exact False.elim (hxy hxy')
        | inr hxzQ' =>
            cases hxzQ' with
            | inl hzx' =>
                exact False.elim (hxz hzx'.symm)
            | inr hxx =>
                exact False.elim (hxz hxx)
    · change (P k).weakPref z x ↔ (Q k).weakPref z x
      constructor
      · intro _
        simp [Q, hki]
        exact prefYZX_zx_weak
      · intro _
        exact (hOut k (by simpa [S] using hk)).1

/--
Main transfer lemma scaffold.

This is the first genuinely substantive Arrow step, and we keep it as a scaffold
for now.
-/
theorem singleton_transfer_left
    {F : SocialWelfareFunction V A}
    (hRat : RationalSWF F)
    (hPareto : WeakPareto F)
    (hIIA : IIA F)
    {i : V}
    {x y z : A}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hSingle : Decisive F ({i} : Set V) x y) :
    Decisive F ({i} : Set V) x z := by
  sorry

/--
Symmetric transfer lemma scaffold.
-/
theorem singleton_transfer_right
    {F : SocialWelfareFunction V A}
    (hRat : RationalSWF F)
    (hPareto : WeakPareto F)
    (hIIA : IIA F)
    {i : V}
    {x y z : A}
    (hxy : x ≠ y)
    (hzy : z ≠ y)
    (hzx : z ≠ x)
    (hSingle : Decisive F ({i} : Set V) x y) :
    Decisive F ({i} : Set V) z y := by
  sorry

/--
Universal singleton decisiveness scaffold.
-/
theorem singleton_universallyDecisive_of_pair
    {F : SocialWelfareFunction V A}
    (hRat : RationalSWF F)
    (hPareto : WeakPareto F)
    (hIIA : IIA F)
    {i : V}
    {x y : A}
    (hxy : x ≠ y)
    (hSingle : Decisive F ({i} : Set V) x y) :
    UniversallyDecisive F ({i} : Set V) := by
  sorry

end SingletonTransfer

end Arrow

end SocialChoice
end EcoLean
