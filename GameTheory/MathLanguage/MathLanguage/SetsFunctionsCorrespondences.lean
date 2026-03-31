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

@[simp] theorem mem_upperPreimage_iff {F : Correspondence X Y}
    {B : Set Y} {x : X} :
    x ∈ upperPreimage F B ↔ F x ⊆ B := Iff.rfl

/-- The inverse correspondence. -/
def inverse (F : Correspondence X Y) : Correspondence Y X :=
  fun y => {x | y ∈ F x}

@[simp] theorem mem_inverse_iff {F : Correspondence X Y} {x : X} {y : Y} :
    x ∈ inverse F y ↔ y ∈ F x := Iff.rfl

/-- Composition of correspondences. -/
def comp (G : Correspondence Y Z) (F : Correspondence X Y) : Correspondence X Z :=
  fun x => {z | ∃ y, y ∈ F x ∧ z ∈ G y}

@[simp] theorem mem_comp_iff {F : Correspondence X Y} {G : Correspondence Y Z}
    {x : X} {z : Z} :
    z ∈ comp G F x ↔ ∃ y, y ∈ F x ∧ z ∈ G y := Iff.rfl

/-- Identity correspondence. -/
def idc (X : Type u) : Correspondence X X :=
  fun x => {x}

@[simp] theorem mem_idc_iff {x x' : X} :
    x' ∈ idc X x ↔ x' = x := by
  change x' ∈ ({x} : Set X) ↔ x' = x
  change x' = x ↔ x' = x
  rfl

/-- Restrict the domain of a correspondence to a subset. -/
def restrictDomain (F : Correspondence X Y) (A : Set X) : Correspondence A Y :=
  fun x => F x.1

@[simp] theorem mem_restrictDomain_iff {F : Correspondence X Y}
    {A : Set X} {x : A} {y : Y} :
    y ∈ restrictDomain F A x ↔ y ∈ F x.1 := Iff.rfl

/-- Restrict the values of a correspondence to a subset of the codomain. -/
def restrictCodomain (F : Correspondence X Y) (B : Set Y) : Correspondence X Y :=
  fun x => F x ∩ B

@[simp] theorem mem_restrictCodomain_iff {F : Correspondence X Y}
    {B : Set Y} {x : X} {y : Y} :
    y ∈ restrictCodomain F B x ↔ y ∈ F x ∧ y ∈ B := Iff.rfl

/-- Pointwise image containment on a subset of the domain. -/
def MapsTo (F : Correspondence X Y) (A : Set X) (B : Set Y) : Prop :=
  ∀ ⦃x⦄, x ∈ A → F x ⊆ B

theorem image_subset_of_mapsTo {F : Correspondence X Y}
    {A : Set X} {B : Set Y} (h : MapsTo F A B) :
    image F A ⊆ B := by
  intro y hy
  rcases hy with ⟨x, hxA, hyF⟩
  exact h hxA hyF

theorem graph_mono {F G : Correspondence X Y}
    (hFG : ∀ x, F x ⊆ G x) :
    graph F ⊆ graph G := by
  intro p hp
  exact hFG p.1 hp

theorem image_mono {F : Correspondence X Y}
    {A A' : Set X} (hAA' : A ⊆ A') :
    image F A ⊆ image F A' := by
  intro y hy
  rcases hy with ⟨x, hxA, hyF⟩
  exact ⟨x, hAA' hxA, hyF⟩

theorem lowerPreimage_mono_right {F : Correspondence X Y}
    {B B' : Set Y} (hBB' : B ⊆ B') :
    lowerPreimage F B ⊆ lowerPreimage F B' := by
  intro x hx
  rcases hx with ⟨y, hyF, hyB⟩
  exact ⟨y, hyF, hBB' hyB⟩

theorem upperPreimage_mono_right {F : Correspondence X Y}
    {B B' : Set Y} (hBB' : B ⊆ B') :
    upperPreimage F B ⊆ upperPreimage F B' := by
  intro x hx
  exact Set.Subset.trans hx hBB'

theorem ran_eq_image_univ (F : Correspondence X Y) :
    ran F = image F Set.univ := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hyFx⟩
    exact ⟨x, by simp, hyFx⟩
  · intro hy
    rcases hy with ⟨x, _, hyFx⟩
    exact ⟨x, hyFx⟩

theorem dom_eq_lowerPreimage_univ (F : Correspondence X Y) :
    dom F = lowerPreimage F Set.univ := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hyFx⟩
    exact ⟨y, hyFx, by simp⟩
  · intro hx
    rcases hx with ⟨y, hyFx, _⟩
    exact ⟨y, hyFx⟩

@[simp] theorem comp_idc (F : Correspondence X Y) :
    comp F (idc X) = F := by
  ext x y
  constructor
  · intro h
    rcases h with ⟨x', hx', hy⟩
    change x' = x at hx'
    simpa [hx'] using hy
  · intro h
    refine ⟨x, ?_, h⟩
    change x = x
    rfl

@[simp] theorem idc_comp (F : Correspondence X Y) :
    comp (idc Y) F = F := by
  ext x y
  constructor
  · intro h
    rcases h with ⟨y', hy', hy''⟩
    change y = y' at hy''
    simpa [hy''] using hy'
  · intro h
    refine ⟨y, h, ?_⟩
    change y = y
    rfl
    
@[simp] theorem inverse_inverse (F : Correspondence X Y) :
    inverse (inverse F) = F := by
  ext x y
  simp [inverse]

end Basic

end Correspondence

end EcoLean.GameTheory
