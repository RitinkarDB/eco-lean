import Mathlib.Data.Set.Basic

namespace EcoLean.GameTheory

universe u v w

/--
A correspondence from `X` to `Y` is a set-valued map:
for each `x : X`, it returns a subset of `Y`.
-/
abbrev Correspondence (X : Type u) (Y : Type v) := X → Set Y

namespace Correspondence

section Basic

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- Extensionality for correspondences. -/
@[ext] theorem ext {F G : Correspondence X Y}
    (h : ∀ x y, y ∈ F x ↔ y ∈ G x) : F = G := by
  funext x
  ext y
  exact h x y

/-- A function as a single-valued correspondence. -/
def ofFun (f : X → Y) : Correspondence X Y :=
  fun x => {f x}

@[simp] theorem mem_ofFun_iff {f : X → Y} {x : X} {y : Y} :
    y ∈ ofFun f x ↔ y = f x := by
  change y ∈ ({f x} : Set Y) ↔ y = f x
  change y = f x ↔ y = f x
  rfl

/-- The graph of a correspondence. -/
def graph (F : Correspondence X Y) : Set (X × Y) :=
  {p | p.2 ∈ F p.1}

@[simp] theorem mem_graph_iff {F : Correspondence X Y} {x : X} {y : Y} :
    (x, y) ∈ graph F ↔ y ∈ F x := Iff.rfl

/-- The domain of a correspondence: the set of points with nonempty value. -/
def dom (F : Correspondence X Y) : Set X :=
  {x | (F x).Nonempty}

@[simp] theorem mem_dom_iff {F : Correspondence X Y} {x : X} :
    x ∈ dom F ↔ (F x).Nonempty := Iff.rfl

/-- The range of a correspondence. -/
def ran (F : Correspondence X Y) : Set Y :=
  {y | ∃ x, y ∈ F x}

@[simp] theorem mem_ran_iff {F : Correspondence X Y} {y : Y} :
    y ∈ ran F ↔ ∃ x, y ∈ F x := Iff.rfl

/-- Image of a set under a correspondence. -/
def image (F : Correspondence X Y) (A : Set X) : Set Y :=
  {y | ∃ x, x ∈ A ∧ y ∈ F x}

@[simp] theorem mem_image_iff {F : Correspondence X Y} {A : Set X} {y : Y} :
    y ∈ image F A ↔ ∃ x, x ∈ A ∧ y ∈ F x := Iff.rfl

/--
Lower inverse of a set under a correspondence:
the points whose image meets `B`.
-/
def lowerPreimage (F : Correspondence X Y) (B : Set Y) : Set X :=
  {x | ∃ y, y ∈ F x ∧ y ∈ B}

@[simp] theorem mem_lowerPreimage_iff {F : Correspondence X Y}
    {B : Set Y} {x : X} :
    x ∈ lowerPreimage F B ↔ ∃ y, y ∈ F x ∧ y ∈ B := Iff.rfl

/--
Upper inverse of a set under a correspondence:
the points whose image is contained in `B`.
-/
def upperPreimage (F : Correspondence X Y) (B : Set Y) : Set X :=
  {x | F x ⊆ B}

end Basic

end Correspondence

end EcoLean.GameTheory
