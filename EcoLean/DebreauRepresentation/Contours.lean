import EcoLean.DebreauRepresentation.Basic

universe u

namespace EcoLean
namespace Preference

variable {α : Type u} [TopologicalSpace α]

/-- The upper weak contour set at `x`: all `y` such that `y ≽ x`. -/
def upperContourSet (P : Preference α) (x : α) : Set α :=
  {y | P.weakPref y x}

/-- The lower weak contour set at `x`: all `y` such that `x ≽ y`. -/
def lowerContourSet (P : Preference α) (x : α) : Set α :=
  {y | P.weakPref x y}

/-- The upper strict contour set at `x`: all `y` such that `y ≻ x`. -/
def strictUpperContourSet (P : Preference α) (x : α) : Set α :=
  {y | P.StrictPref y x}

/-- The lower strict contour set at `x`: all `y` such that `x ≻ y`. -/
def strictLowerContourSet (P : Preference α) (x : α) : Set α :=
  {y | P.StrictPref x y}

end Preference
end EcoLean
