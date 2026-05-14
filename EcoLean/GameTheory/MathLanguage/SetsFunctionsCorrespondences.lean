import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Real

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

end Basic

section Carrier

variable {X : Type u} {Y : Type v}

/--
`F` maps the carrier `A` into the carrier `B` when every value over `A`
is contained in `B`.
-/
def MapsToOn (F : Correspondence X Y) (A : Set X) (B : Set Y) : Prop :=
  ∀ ⦃x⦄, x ∈ A → F x ⊆ B

/-- `F` has nonempty values on `A`. -/
def NonemptyValuedOn (F : Correspondence X Y) (A : Set X) : Prop :=
  ∀ ⦃x⦄, x ∈ A → (F x).Nonempty

theorem MapsToOn.mono {F : Correspondence X Y} {A A' : Set X} {B B' : Set Y}
    (hF : MapsToOn F A B) (hA : A' ⊆ A) (hB : B ⊆ B') :
    MapsToOn F A' B' := by
  intro x hx y hy
  exact hB (hF (hA hx) hy)

theorem NonemptyValuedOn.mono {F : Correspondence X Y} {A A' : Set X}
    (hF : NonemptyValuedOn F A) (hA : A' ⊆ A) :
    NonemptyValuedOn F A' := by
  intro x hx
  exact hF (hA hx)

theorem mapsToOn_iff_image_subset {F : Correspondence X Y}
    {A : Set X} {B : Set Y} :
    MapsToOn F A B ↔ image F A ⊆ B := by
  constructor
  · intro hF y hy
    rcases hy with ⟨x, hxA, hyF⟩
    exact hF hxA hyF
  · intro hF x hxA y hyF
    exact hF ⟨x, hxA, hyF⟩

theorem nonemptyValuedOn_iff_subset_dom {F : Correspondence X Y} {A : Set X} :
    NonemptyValuedOn F A ↔ A ⊆ dom F := by
  constructor
  · intro hF x hx
    exact hF hx
  · intro hF x hx
    exact hF hx

@[simp] theorem mapsToOn_ofFun_iff {f : X → Y} {A : Set X} {B : Set Y} :
    MapsToOn (ofFun f) A B ↔ Set.MapsTo f A B := by
  constructor
  · intro hF x hxA
    exact hF hxA rfl
  · intro hf x hxA y hy
    rw [mem_ofFun_iff] at hy
    exact hy.symm ▸ hf hxA

/-- The graph of a correspondence restricted to a domain carrier. -/
def graphOn (F : Correspondence X Y) (A : Set X) : Set (X × Y) :=
  {p | p.1 ∈ A ∧ p.2 ∈ F p.1}

@[simp] theorem mem_graphOn_iff {F : Correspondence X Y}
    {A : Set X} {x : X} {y : Y} :
    (x, y) ∈ graphOn F A ↔ x ∈ A ∧ y ∈ F x := Iff.rfl

@[simp] theorem graphOn_univ (F : Correspondence X Y) :
    graphOn F Set.univ = graph F := by
  ext p
  simp [graphOn, graph]

theorem graphOn_subset_graph {F : Correspondence X Y} {A : Set X} :
    graphOn F A ⊆ graph F := by
  intro p hp
  exact hp.2

/--
The graph of `F` restricted both to a domain carrier `A` and a codomain carrier
`B`. This is useful when treating correspondences as maps between subspaces.
-/
def graphWithin (F : Correspondence X Y) (A : Set X) (B : Set Y) : Set (X × Y) :=
  {p | p.1 ∈ A ∧ p.2 ∈ B ∧ p.2 ∈ F p.1}

@[simp] theorem mem_graphWithin_iff {F : Correspondence X Y}
    {A : Set X} {B : Set Y} {x : X} {y : Y} :
    (x, y) ∈ graphWithin F A B ↔ x ∈ A ∧ y ∈ B ∧ y ∈ F x := Iff.rfl

theorem graphWithin_subset_graphOn {F : Correspondence X Y}
    {A : Set X} {B : Set Y} :
    graphWithin F A B ⊆ graphOn F A := by
  intro p hp
  exact ⟨hp.1, hp.2.2⟩

theorem graphWithin_eq_graphOn_of_mapsToOn {F : Correspondence X Y}
    {A : Set X} {B : Set Y} (hF : MapsToOn F A B) :
    graphWithin F A B = graphOn F A := by
  ext p
  constructor
  · intro hp
    exact graphWithin_subset_graphOn hp
  · intro hp
    exact ⟨hp.1, hF hp.1 hp.2, hp.2⟩

end Carrier

section Topology

variable {X : Type u} {Y : Type v}

/-- `F` has closed values on `A`. -/
def ClosedValuedOn [TopologicalSpace Y] (F : Correspondence X Y) (A : Set X) : Prop :=
  ∀ ⦃x⦄, x ∈ A → IsClosed (F x)

/-- `F` has compact values on `A`. -/
def CompactValuedOn [TopologicalSpace Y] (F : Correspondence X Y) (A : Set X) : Prop :=
  ∀ ⦃x⦄, x ∈ A → IsCompact (F x)

/-- The restricted graph of `F` is closed in the ambient product topology. -/
def ClosedGraphOn [TopologicalSpace X] [TopologicalSpace Y]
    (F : Correspondence X Y) (A : Set X) : Prop :=
  IsClosed (graphOn F A)

/--
The graph restricted to both a domain and codomain carrier is closed in the
ambient product topology.
-/
def ClosedGraphWithin [TopologicalSpace X] [TopologicalSpace Y]
    (F : Correspondence X Y) (A : Set X) (B : Set Y) : Prop :=
  IsClosed (graphWithin F A B)

/-- Alias for mathlib's upper hemicontinuity, localized to correspondences. -/
abbrev UpperHemicontinuousOn [TopologicalSpace X] [TopologicalSpace Y]
    (F : Correspondence X Y) (A : Set X) : Prop :=
  _root_.UpperHemicontinuousOn F A

/-- Alias for mathlib's lower hemicontinuity, localized to correspondences. -/
abbrev LowerHemicontinuousOn [TopologicalSpace X] [TopologicalSpace Y]
    (F : Correspondence X Y) (A : Set X) : Prop :=
  _root_.LowerHemicontinuousOn F A

theorem CompactValuedOn.closedValuedOn [TopologicalSpace Y] [T2Space Y]
    {F : Correspondence X Y} {A : Set X} (hF : CompactValuedOn F A) :
    ClosedValuedOn F A := by
  intro x hx
  exact (hF hx).isClosed

@[simp] theorem upperHemicontinuousOn_ofFun_iff
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {A : Set X} :
    UpperHemicontinuousOn (ofFun f) A ↔ ContinuousOn f A := by
  change _root_.UpperHemicontinuousOn (fun x => {f x}) A ↔ ContinuousOn f A
  exact _root_.upperHemicontinuousOn_singleton_iff

@[simp] theorem lowerHemicontinuousOn_ofFun_iff
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {A : Set X} :
    LowerHemicontinuousOn (ofFun f) A ↔ ContinuousOn f A := by
  change _root_.LowerHemicontinuousOn (fun x => {f x}) A ↔ ContinuousOn f A
  constructor
  · intro hF x hxA
    rw [ContinuousWithinAt, Filter.tendsto_iff_forall_eventually_mem]
    intro u hu
    rcases mem_nhds_iff.mp hu with ⟨v, hvu, hvOpen, hfv⟩
    have hInter : ({f x} ∩ v : Set Y).Nonempty := by
      exact ⟨f x, by simp [hfv]⟩
    filter_upwards [hF x hxA v ⟨hvOpen, hInter⟩] with x' hx'
    rcases hx'.2 with ⟨y, hyF, hyv⟩
    rw [Set.mem_singleton_iff] at hyF
    exact hvu (hyF ▸ hyv)
  · intro hf x hxA u hu
    rcases hu with ⟨huOpen, hInter⟩
    rcases hInter with ⟨y, hyF, hyu⟩
    rw [Set.mem_singleton_iff] at hyF
    have hxu : f x ∈ u := hyF ▸ hyu
    have hu : u ∈ nhds (f x) := huOpen.mem_nhds hxu
    filter_upwards [hf x hxA hu] with x' hx'u
    exact ⟨huOpen, ⟨f x', by simp, hx'u⟩⟩

end Topology

section Convex

variable {𝕜 : Type u} {X : Type v} {Y : Type w}

/-- `F` has convex values on `A`. -/
def ConvexValuedOn [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid Y] [SMul 𝕜 Y]
    (F : Correspondence X Y) (A : Set X) : Prop :=
  ∀ ⦃x⦄, x ∈ A → Convex 𝕜 (F x)

theorem ConvexValuedOn.mono [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid Y] [SMul 𝕜 Y]
    {F : Correspondence X Y} {A A' : Set X}
    (hF : ConvexValuedOn (𝕜 := 𝕜) F A) (hA : A' ⊆ A) :
    ConvexValuedOn (𝕜 := 𝕜) F A' := by
  intro x hx
  exact hF (hA hx)

end Convex

section Argmax

variable {X : Type u} {Y : Type v}

/--
The pointwise argmax correspondence associated to an objective `u` and a
feasible-set correspondence `F`.

At parameter `x`, this returns the feasible points in `F x` maximizing
`fun y => u x y` over `F x`.
-/
def argmax (u : X → Y → ℝ) (F : Correspondence X Y) : Correspondence X Y :=
  fun x => {y | y ∈ F x ∧ ∀ z, z ∈ F x → u x z ≤ u x y}

@[simp] theorem mem_argmax_iff {u : X → Y → ℝ} {F : Correspondence X Y}
    {x : X} {y : Y} :
    y ∈ argmax u F x ↔ y ∈ F x ∧ ∀ z, z ∈ F x → u x z ≤ u x y := Iff.rfl

theorem argmax_subset {u : X → Y → ℝ} {F : Correspondence X Y} (x : X) :
    argmax u F x ⊆ F x := by
  intro y hy
  exact hy.1

theorem isMaxOn_of_mem_argmax {u : X → Y → ℝ} {F : Correspondence X Y}
    {x : X} {y : Y} (hy : y ∈ argmax u F x) :
    IsMaxOn (u x) (F x) y := by
  rw [isMaxOn_iff]
  exact hy.2

theorem mem_argmax_of_isMaxOn {u : X → Y → ℝ} {F : Correspondence X Y}
    {x : X} {y : Y} (hyF : y ∈ F x) (hy : IsMaxOn (u x) (F x) y) :
    y ∈ argmax u F x := by
  rw [mem_argmax_iff, isMaxOn_iff] at *
  exact ⟨hyF, hy⟩

/--
Compact feasible values and objective continuity give nonempty argmax values.

This is the reusable extreme-value-theorem half of Berge-style arguments.
-/
theorem argmax_nonemptyValuedOn_of_compact
    [TopologicalSpace Y] {u : X → Y → ℝ} {F : Correspondence X Y}
    {A : Set X} (hCompact : CompactValuedOn F A)
    (hNonempty : NonemptyValuedOn F A)
    (hu : ∀ ⦃x⦄, x ∈ A → ContinuousOn (u x) (F x)) :
    NonemptyValuedOn (argmax u F) A := by
  intro x hxA
  rcases (hCompact hxA).exists_isMaxOn (hNonempty hxA) (hu hxA) with
    ⟨y, hyF, hyMax⟩
  exact ⟨y, mem_argmax_of_isMaxOn hyF hyMax⟩

/--
If the objective is quasiconcave on each feasible value and argmax values are
nonempty, then the argmax correspondence is convex-valued.
-/
theorem argmax_convexValuedOn_of_quasiconcave
    [AddCommMonoid Y] [Module ℝ Y] {u : X → Y → ℝ} {F : Correspondence X Y}
    {A : Set X} (hArgmax : NonemptyValuedOn (argmax u F) A)
    (hu : ∀ ⦃x⦄, x ∈ A → QuasiconcaveOn ℝ (F x) (u x)) :
    ConvexValuedOn (𝕜 := ℝ) (argmax u F) A := by
  intro x hxA
  rcases hArgmax hxA with ⟨y₀, hy₀⟩
  have hEq :
      argmax u F x = {y ∈ F x | u x y₀ ≤ u x y} := by
    ext y
    constructor
    · intro hy
      exact ⟨hy.1, hy.2 y₀ hy₀.1⟩
    · intro hy
      exact ⟨hy.1, fun z hz => (hy₀.2 z hz).trans hy.2⟩
  simpa [hEq] using hu hxA (u x y₀)

end Argmax

section FixedPoints

variable {X : Type u}

/-- Fixed points of a self-correspondence. -/
def fixedPoints (F : Correspondence X X) : Set X :=
  {x | x ∈ F x}

@[simp] theorem mem_fixedPoints_iff {F : Correspondence X X} {x : X} :
    x ∈ fixedPoints F ↔ x ∈ F x := Iff.rfl

/-- `x` is a fixed point of `F` lying in carrier `A`. -/
def FixedPointOn (F : Correspondence X X) (A : Set X) (x : X) : Prop :=
  x ∈ A ∧ x ∈ F x

/-- `F` has a fixed point in carrier `A`. -/
def HasFixedPointOn (F : Correspondence X X) (A : Set X) : Prop :=
  ∃ x, FixedPointOn F A x

/-- Fixed points of `F` restricted to carrier `A`. -/
def fixedPointsOn (F : Correspondence X X) (A : Set X) : Set X :=
  {x | FixedPointOn F A x}

@[simp] theorem fixedPointOn_iff {F : Correspondence X X}
    {A : Set X} {x : X} :
    FixedPointOn F A x ↔ x ∈ A ∧ x ∈ F x := Iff.rfl

@[simp] theorem hasFixedPointOn_iff {F : Correspondence X X} {A : Set X} :
    HasFixedPointOn F A ↔ ∃ x ∈ A, x ∈ F x := by
  constructor
  · intro h
    rcases h with ⟨x, hxA, hxF⟩
    exact ⟨x, hxA, hxF⟩
  · intro h
    rcases h with ⟨x, hxA, hxF⟩
    exact ⟨x, hxA, hxF⟩

@[simp] theorem mem_fixedPointsOn_iff {F : Correspondence X X}
    {A : Set X} {x : X} :
    x ∈ fixedPointsOn F A ↔ x ∈ A ∧ x ∈ F x := Iff.rfl

theorem fixedPointsOn_eq_inter (F : Correspondence X X) (A : Set X) :
    fixedPointsOn F A = A ∩ fixedPoints F := by
  ext x
  rfl

theorem fixedPointsOn_subset (F : Correspondence X X) (A : Set X) :
    fixedPointsOn F A ⊆ A := by
  intro x hx
  exact hx.1

theorem fixedPoints_subset_dom (F : Correspondence X X) :
    fixedPoints F ⊆ dom F := by
  intro x hx
  exact ⟨x, hx⟩

@[simp] theorem mem_fixedPoints_ofFun_iff {f : X → X} {x : X} :
    x ∈ fixedPoints (ofFun f) ↔ f x = x := by
  rw [mem_fixedPoints_iff, mem_ofFun_iff, eq_comm]

@[simp] theorem fixedPointOn_ofFun_iff {f : X → X} {A : Set X} {x : X} :
    FixedPointOn (ofFun f) A x ↔ x ∈ A ∧ f x = x := by
  rw [fixedPointOn_iff, mem_ofFun_iff, eq_comm]

end FixedPoints

end Correspondence

end EcoLean.GameTheory
