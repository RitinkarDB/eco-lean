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

theorem social_not_zx_in_threeway_profile
    {F : SocialWelfareFunction V A}
    (hRat : RationalSWF F)
    {x y z : A}
    (Q : Profile V A)
    (hQxy : SocialWelfareFunction.StrictPref F Q x y)
    (hQyz : SocialWelfareFunction.WeakPref F Q y z)
    (hxz_rev : SocialWelfareFunction.WeakPref F Q z x) :
    False := by
  have hyx : SocialWelfareFunction.WeakPref F Q y x := by
    exact social_weak_trans hRat Q hQyz hxz_rev
  exact hQxy.2 hyx

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
  intro P hIn hOut
  let Q : Profile V A := fun k =>
    if k = i then prefXYZ x y z else prefYZX x y z

  have hQ : ∀ k : V,
      (k = i → Q k = prefXYZ x y z) ∧
      (k ≠ i → Q k = prefYZX x y z) := by
    intro k
    constructor
    · intro hk
      simp [Q, hk]
    · intro hk
      simp [Q, hk]

  have hQxy : SocialWelfareFunction.StrictPref F Q x y := by
    exact social_strict_xy_in_threeway_profile hSingle hxy hxz Q hQ

  have hQyz : SocialWelfareFunction.WeakPref F Q y z := by
    exact social_weak_yz_in_threeway_profile hPareto Q hQ

  have hPair : PairwiseAgreesOn P Q x z := by
    exact pairwiseAgreesOn_xz_with_threeway_profile i hxy hxz P hIn hOut

  have hQxz : SocialWelfareFunction.StrictPref F Q x z := by
    apply social_strict_of_weak_not_reverse Q
    · exact social_weak_trans hRat Q hQxy.1 hQyz
    · intro hzx
      exact social_not_zx_in_threeway_profile hRat Q hQxy hQyz hzx

  exact social_strict_transfer_back hIIA hPair hQxz
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
  intro P hIn hOut
  let Q : Profile V A := fun k =>
    if k = i then prefZXY x y z else prefYZX x y z

  have hQ : ∀ k : V,
      (k = i → Q k = prefZXY x y z) ∧
      (k ≠ i → Q k = prefYZX x y z) := by
    intro k
    constructor
    · intro hk
      simp [Q, hk]
    · intro hk
      simp [Q, hk]

  have hQxy : SocialWelfareFunction.StrictPref F Q x y := by
    apply hSingle Q
    · intro k hk
      change Preference.StrictPref (Q k) x y
      rw [(hQ k).1 hk]
      exact prefZXY_xy hxy hzy.symm
    · intro k hk
      change Preference.StrictPref (Q k) y x
      rw [(hQ k).2 hk]
      exact prefYZX_yx hxy.symm


  have hQzx : SocialWelfareFunction.WeakPref F Q z x := by
    apply hPareto Q z x
    intro k
    change (Q k).weakPref z x
    by_cases hk : k = i
    · rw [(hQ k).1 hk]
      exact prefZXY_zx_weak
    · rw [(hQ k).2 hk]
      exact prefYZX_zx_weak

  have hPair : PairwiseAgreesOn P Q z y := by
    let S : Set V := {j : V | j = i}
    intro k
    by_cases hk : k ∈ S
    · have hki : k = i := by
        simpa [S] using hk
      constructor
      · change (P k).weakPref z y ↔ (Q k).weakPref z y
        rw [hki]
        constructor
        · intro _
          simp [Q]
          exact (prefZXY_zy hzy).1
        · intro _
          exact (hIn i (by simp [S])).1
      · change (P k).weakPref y z ↔ (Q k).weakPref y z
        rw [hki]
        constructor
        · intro hyzP
          exact False.elim ((hIn i (by simp [S])).2 hyzP)
        · intro hyzQ
          simp [Q, prefZXY] at hyzQ
          cases hyzQ with
          | inl h =>
              exact False.elim (hzy h.symm)
          | inr h' =>
              cases h' with
              | inl h =>
                  exact False.elim (hzy h)
              | inr h =>
                  exact False.elim (hzy h.symm)
    · have hki : k ≠ i := by
        intro hEq
        apply hk
        simp [S, hEq]
      constructor
      · change (P k).weakPref z y ↔ (Q k).weakPref z y
        constructor
        · intro hPzy
          exact False.elim ((hOut k (by simpa [S] using hk)).2 hPzy)
        · intro hQzy
          simp [Q, hki, prefYZX] at hQzy
          cases hQzy with
          | inl h =>
              exact False.elim (hzy h)
          | inr h' =>
              cases h' with
              | inl h =>
                  exact False.elim (hxy h.symm)
              | inr h =>
                  exact False.elim (hzy h)
      · change (P k).weakPref y z ↔ (Q k).weakPref y z
        constructor
        · intro _
          rw [(hQ k).2 hki]
          exact prefYZX_yz_weak
        · intro _
          exact (hOut k (by simpa [S] using hk)).1


  have hQzy : SocialWelfareFunction.StrictPref F Q z y := by
    apply social_strict_of_weak_not_reverse Q
    · exact social_weak_trans hRat Q hQzx hQxy.1
    · intro hyz
      have hyx : SocialWelfareFunction.WeakPref F Q y x := by
        exact social_weak_trans hRat Q hyz hQzx
      exact hQxy.2 hyx

  exact social_strict_transfer_back hIIA hPair hQzy

theorem singleton_decisive_all_pairs
    {F : SocialWelfareFunction V A}
    (hRat : RationalSWF F)
    (hPareto : WeakPareto F)
    (hIIA : IIA F)
    {i : V}
    {x y : A}
    (hxy : x ≠ y)
    (hSingle : Decisive F ({i} : Set V) x y) :
    ∀ z : A,
      z ≠ x →
      z ≠ y →
      Decisive F ({i} : Set V) x z ∧
      Decisive F ({i} : Set V) z y := by
  intro z hzx hzy
  constructor
  · exact singleton_transfer_left hRat hPareto hIIA hxy hzx.symm hzy.symm hSingle
  · exact singleton_transfer_right hRat hPareto hIIA hxy hzy hzx hSingle

theorem singleton_transfer_swap
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
    Decisive F ({i} : Set V) y x := by
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
  intro a b hab
  by_cases hax : a = x
  · subst hax
    by_cases hby : b = y
    · subst hby
      exact hSingle
    · exact singleton_transfer_left hRat hPareto hIIA
        (x := a) (y := y) (z := b)
        hxy hab (fun h => hby h.symm) hSingle
  · by_cases hby : b = y
    · subst hby
      exact singleton_transfer_right hRat hPareto hIIA
        (x := x) (y := b) (z := a)
        hxy hab (fun h => hax h) hSingle
    · sorry
end SingletonTransfer

end Arrow

end SocialChoice
end EcoLean
