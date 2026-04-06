import EcoLean.SocialChoice.Theorems.Arrow.SingletonSwap
import EcoLean.SocialChoice.Theorems.Arrow.ThreeWayProfiles

universe u v

namespace EcoLean
namespace SocialChoice

namespace Arrow

section SwapProfiles

variable {V : Type u} {A : Type v}
variable [Fintype V] [DecidableEq V]

/--
A profile used in the swap argument: voter `i` ranks `y ≻ z ≻ x`, while all
other voters rank `z ≻ x ≻ y`.
-/
def swapProfileLeft
    (i : V) (x y z : A) : Profile V A :=
  fun k => if k = i then prefYZX x y z else prefZXY y x z

/--
A profile used in the swap argument: voter `i` ranks `z ≻ y ≻ x`, while all
other voters rank `x ≻ z ≻ y`.
-/
def swapProfileRight
    (i : V) (x y z : A) : Profile V A :=
  fun k => if k = i then prefZXY x y z else prefXYZ x y z

theorem swapProfileLeft_pattern
    {i : V} {x y z : A}
    (hyz : y ≠ z)
    (hyx : y ≠ x)
    (hzx : z ≠ x) :
    (∀ k ∈ ({j : V | j = i} : Set V),
      Profile.StrictPref (swapProfileLeft i x y z) k y z) ∧
    (∀ k ∉ ({j : V | j = i} : Set V),
      Profile.StrictPref (swapProfileLeft i x y z) k z y) := by
  constructor
  · intro k hk
    change Preference.StrictPref ((swapProfileLeft i x y z) k) y z
    have hki : k = i := by
      simpa using hk
    simp [swapProfileLeft, hki]
    exact prefYZX_yz hyz hyx
  · intro k hk
    change Preference.StrictPref ((swapProfileLeft i x y z) k) z y
    have hki : k ≠ i := by
      intro hEq
      apply hk
      simpa [hEq]
    simp [swapProfileLeft, hki]
    exact prefZXY_zx hyz.symm hzx

theorem swapProfileRight_pattern
    {i : V} {x y z : A}
    (hzx : z ≠ x)
    (zny : z ≠ y)
    (hxz : x ≠ z) :
    (∀ k ∈ ({j : V | j = i} : Set V),
      Profile.StrictPref (swapProfileRight i x y z) k z x) ∧
    (∀ k ∉ ({j : V | j = i} : Set V),
      Profile.StrictPref (swapProfileRight i x y z) k x z) := by
  constructor
  · intro k hk
    change Preference.StrictPref ((swapProfileRight i x y z) k) z x
    have hki : k = i := by
      simpa using hk
    simp [swapProfileRight, hki]
    exact prefZXY_zx hzx zny
  · intro k hk
    change Preference.StrictPref ((swapProfileRight i x y z) k) x z
    have hki : k ≠ i := by
      intro hEq
      apply hk
      simpa [hEq]
    simp [swapProfileRight, hki]
    exact prefXYZ_xz hxz

end SwapProfiles

end Arrow

end SocialChoice
end EcoLean
