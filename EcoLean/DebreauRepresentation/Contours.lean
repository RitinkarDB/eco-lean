import EcoLean.DebreauRepresentation.Basic

/-!
# Contour sets of a preference

This file introduces the basic geometric objects attached to a preference on a
topological space:

- upper weak contour sets
- lower weak contour sets
- upper strict contour sets
- lower strict contour sets

These sets are the natural topological objects that appear in continuity
assumptions for preferences and in the proof of continuous utility
representation.
-/

universe u

namespace EcoLean
namespace Preference

variable {α : Type u} [TopologicalSpace α]

/--
The upper weak contour set at `x`.

This is the set of all `y` such that `y ≽ x`.
-/
def upperContourSet (P : Preference α) (x : α) : Set α :=
  {y | P.weakPref y x}

/--
The lower weak contour set at `x`.

This is the set of all `y` such that `x ≽ y`.
-/
def lowerContourSet (P : Preference α) (x : α) : Set α :=
  {y | P.weakPref x y}

/--
The upper strict contour set at `x`.

This is the set of all `y` such that `y ≻ x`.
-/
def strictUpperContourSet (P : Preference α) (x : α) : Set α :=
  {y | P.StrictPref y x}

/--
The lower strict contour set at `x`.

This is the set of all `y` such that `x ≻ y`.
-/
def strictLowerContourSet (P : Preference α) (x : α) : Set α :=
  {y | P.StrictPref x y}

end Preference
end EcoLean
