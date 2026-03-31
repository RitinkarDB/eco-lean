import EcoLean.GameTheory.MathLanguage.SetsFunctionsCorrespondences
import Mathlib.Data.Set.Basic

namespace EcoLean.GameTheory

universe u v

/--
An indexed family of objects of type `α`.
This is just a dependent function type, named for readability.
-/
abbrev Family (I : Type u) (α : Sort v) := I → α

/-- A binary relation on `X`. -/
abbrev BinRel (X : Type u) := X → X → Prop

namespace BinRel

section Basic

variable {X : Type u}

/-- The converse of a binary relation. -/
def converse (R : BinRel X) : BinRel X :=
  fun x y => R y x

@[simp] theorem converse_iff {R : BinRel X} {x y : X} :
    converse R x y ↔ R y x := Iff.rfl

@[simp] theorem converse_converse (R : BinRel X) :
    converse (converse R) = R := by
  funext x y
  rfl

/--
The strict part of a relation:
`x` is strictly related to `y` iff `xRy` holds but `yRx` does not.
-/
def strictPart (R : BinRel X) : BinRel X :=
  fun x y => R x y ∧ ¬ R y x

@[simp] theorem strictPart_iff {R : BinRel X} {x y : X} :
    strictPart R x y ↔ R x y ∧ ¬ R y x := Iff.rfl

theorem irrefl_strictPart (R : BinRel X) :
    Irreflexive (strictPart R) := by
  intro x hx
  exact hx.2 hx.1

/--
The symmetric part of a relation:
`x` and `y` are symmetrically related iff both directions hold.
-/
def symmetricPart (R : BinRel X) : BinRel X :=
  fun x y => R x y ∧ R y x

@[simp] theorem symmetricPart_iff {R : BinRel X} {x y : X} :
    symmetricPart R x y ↔ R x y ∧ R y x := Iff.rfl

theorem symmetric_symmetricPart (R : BinRel X) :
    Symmetric (symmetricPart R) := by
  intro x y hxy
  exact ⟨hxy.2, hxy.1⟩

end Basic

section OnSet

variable {X : Type u}

/-- Reflexivity of `R` on a subset `A`. -/
def ReflexiveOn (R : BinRel X) (A : Set X) : Prop :=
  ∀ ⦃x⦄, x ∈ A → R x x

/-- Symmetry of `R` on a subset `A`. -/
def SymmetricOn (R : BinRel X) (A : Set X) : Prop :=
  ∀ ⦃x y⦄, x ∈ A → y ∈ A → R x y → R y x

/-- Antisymmetry of `R` on a subset `A`. -/
def AntisymmetricOn (R : BinRel X) (A : Set X) : Prop :=
  ∀ ⦃x y⦄, x ∈ A → y ∈ A → R x y → R y x → x = y

/-- Transitivity of `R` on a subset `A`. -/
def TransitiveOn (R : BinRel X) (A : Set X) : Prop :=
  ∀ ⦃x y z⦄, x ∈ A → y ∈ A → z ∈ A → R x y → R y z → R x z

/--
Completeness of `R` on a subset `A`:
distinct points in `A` are comparable.
-/
def CompleteOn (R : BinRel X) (A : Set X) : Prop :=
  ∀ ⦃x y⦄, x ∈ A → y ∈ A → x ≠ y → R x y ∨ R y x

theorem ReflexiveOn.mono {R : BinRel X} {A B : Set X}
    (hR : ReflexiveOn R B) (hAB : A ⊆ B) :
    ReflexiveOn R A := by
  intro x hxA
  exact hR (hAB hxA)

theorem SymmetricOn.mono {R : BinRel X} {A B : Set X}
    (hR : SymmetricOn R B) (hAB : A ⊆ B) :
    SymmetricOn R A := by
  intro x y hxA hyA hxy
  exact hR (hAB hxA) (hAB hyA) hxy

theorem AntisymmetricOn.mono {R : BinRel X} {A B : Set X}
    (hR : AntisymmetricOn R B) (hAB : A ⊆ B) :
    AntisymmetricOn R A := by
  intro x y hxA hyA hxy hyx
  exact hR (hAB hxA) (hAB hyA) hxy hyx

theorem TransitiveOn.mono {R : BinRel X} {A B : Set X}
    (hR : TransitiveOn R B) (hAB : A ⊆ B) :
    TransitiveOn R A := by
  intro x y z hxA hyA hzA hxy hyz
  exact hR (hAB hxA) (hAB hyA) (hAB hzA) hxy hyz

theorem CompleteOn.mono {R : BinRel X} {A B : Set X}
    (hR : CompleteOn R B) (hAB : A ⊆ B) :
    CompleteOn R A := by
  intro x y hxA hyA hxy
  exact hR (hAB hxA) (hAB hyA) hxy

end OnSet

section Extremal

variable {X : Type u}

/--
`x` is maximal in `A` with respect to `R` iff `x ∈ A`
and every `y ∈ A` that relates to `x` is also related by `x`.
-/
def MaximalIn (R : BinRel X) (A : Set X) (x : X) : Prop :=
  x ∈ A ∧ ∀ ⦃y⦄, y ∈ A → R y x → R x y

/--
`x` is minimal in `A` with respect to `R` iff `x ∈ A`
and every `y ∈ A` to which `x` relates is also related by `y`.
-/
def MinimalIn (R : BinRel X) (A : Set X) (x : X) : Prop :=
  x ∈ A ∧ ∀ ⦃y⦄, y ∈ A → R x y → R y x

/-- The set of maximal elements of `A` with respect to `R`. -/
def maximalSet (R : BinRel X) (A : Set X) : Set X :=
  {x | MaximalIn R A x}

/-- The set of minimal elements of `A` with respect to `R`. -/
def minimalSet (R : BinRel X) (A : Set X) : Set X :=
  {x | MinimalIn R A x}

@[simp] theorem mem_maximalSet_iff {R : BinRel X} {A : Set X} {x : X} :
    x ∈ maximalSet R A ↔ MaximalIn R A x := Iff.rfl

@[simp] theorem mem_minimalSet_iff {R : BinRel X} {A : Set X} {x : X} :
    x ∈ minimalSet R A ↔ MinimalIn R A x := Iff.rfl

theorem maximalSet_subset {R : BinRel X} {A : Set X} :
    maximalSet R A ⊆ A := by
  intro x hx
  exact hx.1

theorem minimalSet_subset {R : BinRel X} {A : Set X} :
    minimalSet R A ⊆ A := by
  intro x hx
  exact hx.1

end Extremal

end BinRel

end EcoLean.GameTheory
