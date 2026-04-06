import EcoLean.SocialChoice.Theorems.Arrow.ProfileConstructions

universe u v

namespace EcoLean
namespace SocialChoice

namespace Arrow

section ThreeWayProfiles

variable {A : Type v}

/--
A simple weak preference intended to encode the pattern `x ≻ y ≻ z`,
with `x` at the top and `z` at the bottom.
-/
def prefXYZ (x y z : A) : Preference A where
  weakPref := fun a b => a = x ∨ b = z ∨ a = b

/--
A simple weak preference intended to encode the pattern `y ≻ z ≻ x`,
with `y` at the top and `x` at the bottom.
-/
def prefYZX (x y z : A) : Preference A where
  weakPref := fun a b => a = y ∨ b = x ∨ a = b



theorem prefXYZ_xy
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) :
    Preference.StrictPref (prefXYZ x y z) x y := by
  constructor
  · left
    rfl
  · intro hyx
    cases hyx with
    | inl hy =>
        exact hxy hy.symm
    | inr hyx' =>
        cases hyx' with
        | inl hz =>
            exact hxz hz
        | inr hy' =>
            exact hxy hy'.symm

theorem prefXYZ_xz
    {x y z : A} (hxz : x ≠ z) :
    Preference.StrictPref (prefXYZ x y z) x z := by
  constructor
  · left
    rfl
  · intro hzx
    cases hzx with
    | inl hz =>
        exact hxz hz.symm
    | inr hzx' =>
        cases hzx' with
        | inl hx =>
            exact hxz hx
        | inr hz' =>
            exact hxz hz'.symm

theorem prefYZX_yx
    {x y z : A} (hyx : y ≠ x) :
    Preference.StrictPref (prefYZX x y z) y x := by
  constructor
  · left
    rfl
  · intro hxy
    cases hxy with
    | inl hx =>
        exact hyx hx.symm
    | inr hxy' =>
        cases hxy' with
        | inl hy =>
            exact hyx hy
        | inr hx' =>
            exact hyx hx'.symm

theorem prefYZX_zx
    {x y z : A} (hzx : z ≠ x) (hxy : x ≠ y) :
    Preference.StrictPref (prefYZX x y z) z x := by
  constructor
  · right
    left
    rfl
  · intro hxz
    cases hxz with
    | inl hxy' =>
        exact hxy hxy'
    | inr hxz' =>
        cases hxz' with
        | inl hzx' =>
            exact hzx hzx'
        | inr hxz'' =>
            exact hzx hxz''.symm

theorem prefXYZ_xz_weak
    {x y z : A} :
    (prefXYZ x y z).weakPref x z := by
  left
  rfl

theorem prefYZX_zx_weak
    {x y z : A} :
    (prefYZX x y z).weakPref z x := by
  right
  left
  rfl

theorem prefYZX_yz_weak
    {x y z : A} :
    (prefYZX x y z).weakPref y z := by
  left
  rfl

theorem prefXYZ_yz_weak
    {x y z : A} :
    (prefXYZ x y z).weakPref y z := by
  right
  left
  rfl

end ThreeWayProfiles

end Arrow

end SocialChoice
end EcoLean
