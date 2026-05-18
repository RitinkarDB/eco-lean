import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Algebra.ContinuousAffineEquiv
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Real

namespace EcoLean.GameTheory

universe u v w t

/--
A correspondence from `X` to `Y` is a set-valued map:
for each `x : X`, it returns a subset of `Y`.
-/
abbrev Correspondence (X : Type u) (Y : Type v) := X → Set Y

namespace Correspondence

section Basic

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type t}

/-- Extensionality for correspondences. -/
@[ext] theorem ext {F G : Correspondence X Y}
    (h : ∀ x y, y ∈ F x ↔ y ∈ G x) : F = G := by
  funext x
  ext y
  exact h x y

/-- A function as a single-valued correspondence. -/
def ofFun (f : X → Y) : Correspondence X Y :=
  fun x => {f x}

/-- The constant correspondence with value `S`. -/
def const (S : Set Y) : Correspondence X Y :=
  fun _ => S

@[simp] theorem mem_ofFun_iff {f : X → Y} {x : X} {y : Y} :
    y ∈ ofFun f x ↔ y = f x := by
  change y ∈ ({f x} : Set Y) ↔ y = f x
  change y = f x ↔ y = f x
  rfl

@[simp] theorem mem_const_iff {S : Set Y} {x : X} {y : Y} :
    y ∈ const (X := X) S x ↔ y ∈ S := Iff.rfl

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

/-- The identity correspondence. -/
def identity (X : Type u) : Correspondence X X :=
  fun x => {x}

@[simp] theorem mem_identity_iff {x y : X} :
    y ∈ identity X x ↔ y = x := by
  rfl

/-- Composition of correspondences. -/
def comp (G : Correspondence Y Z) (F : Correspondence X Y) : Correspondence X Z :=
  fun x => {z | ∃ y, y ∈ F x ∧ z ∈ G y}

@[simp] theorem mem_comp_iff {F : Correspondence X Y} {G : Correspondence Y Z}
    {x : X} {z : Z} :
    z ∈ comp G F x ↔ ∃ y, y ∈ F x ∧ z ∈ G y := Iff.rfl

@[simp] theorem comp_identity (F : Correspondence X Y) :
    comp (identity Y) F = F := by
  ext x y
  constructor
  · intro hy
    rcases hy with ⟨z, hzF, hyz⟩
    rw [mem_identity_iff] at hyz
    simpa [hyz] using hzF
  · intro hy
    exact ⟨y, hy, rfl⟩

@[simp] theorem identity_comp (F : Correspondence X Y) :
    comp F (identity X) = F := by
  ext x y
  constructor
  · intro hy
    rcases hy with ⟨z, hz, hyF⟩
    rw [mem_identity_iff] at hz
    simpa [hz] using hyF
  · intro hy
    exact ⟨x, rfl, hy⟩

theorem comp_assoc (H : Correspondence Z W)
    (G : Correspondence Y Z) (F : Correspondence X Y) :
    comp H (comp G F) = comp (comp H G) F := by
  ext x w
  constructor
  · intro hw
    rcases hw with ⟨z, hz, hwH⟩
    rcases hz with ⟨y, hyF, hzG⟩
    exact ⟨y, hyF, ⟨z, hzG, hwH⟩⟩
  · intro hw
    rcases hw with ⟨y, hyF, hw⟩
    rcases hw with ⟨z, hzG, hwH⟩
    exact ⟨z, ⟨y, hyF, hzG⟩, hwH⟩

@[simp] theorem comp_ofFun_ofFun (g : Y → Z) (f : X → Y) :
    comp (ofFun g) (ofFun f) = ofFun (g ∘ f) := by
  ext x z
  constructor
  · intro hz
    rcases hz with ⟨y, hyf, hzg⟩
    rw [mem_ofFun_iff] at hyf hzg
    subst y
    exact hzg
  · intro hz
    exact ⟨f x, rfl, hz⟩

/-- Pointwise product of two correspondences with the same domain. -/
def prod (F : Correspondence X Y) (G : Correspondence X Z) :
    Correspondence X (Y × Z) :=
  fun x => F x ×ˢ G x

@[simp] theorem mem_prod_iff {F : Correspondence X Y} {G : Correspondence X Z}
    {x : X} {p : Y × Z} :
    p ∈ prod F G x ↔ p.1 ∈ F x ∧ p.2 ∈ G x := by
  exact Set.mem_prod

@[simp] theorem prod_ofFun_ofFun (f : X → Y) (g : X → Z) :
    prod (ofFun f) (ofFun g) = ofFun (fun x => (f x, g x)) := by
  ext x p
  constructor
  · intro hp
    rw [mem_prod_iff] at hp
    rcases hp with ⟨hpf, hpg⟩
    rw [mem_ofFun_iff] at hpf hpg
    exact Prod.ext hpf hpg
  · intro hp
    rw [mem_ofFun_iff] at hp
    subst p
    exact ⟨rfl, rfl⟩

/-- Indexed product of a family of correspondences with a common domain. -/
def pi {ι : Type w} {Yᵢ : ι → Type v}
    (F : ∀ i, Correspondence X (Yᵢ i)) :
    Correspondence X (∀ i, Yᵢ i) :=
  fun x => Set.pi Set.univ fun i => F i x

@[simp] theorem mem_pi_iff {ι : Type w} {Yᵢ : ι → Type v}
    {F : ∀ i, Correspondence X (Yᵢ i)} {x : X} {y : ∀ i, Yᵢ i} :
    y ∈ pi F x ↔ ∀ i, y i ∈ F i x := by
  simp [pi]

/-- Restrict the domain of a correspondence to a subtype carrier. -/
def restrictDomain (F : Correspondence X Y) (A : Set X) : Correspondence A Y :=
  fun x => F x.1

@[simp] theorem mem_restrictDomain_iff {F : Correspondence X Y}
    {A : Set X} {x : A} {y : Y} :
    y ∈ restrictDomain F A x ↔ y ∈ F x.1 := Iff.rfl

/-- Restrict the codomain of a correspondence to a subtype carrier. -/
def restrictCodomain (F : Correspondence X Y) (B : Set Y) : Correspondence X B :=
  fun x => {y | (y : Y) ∈ F x}

@[simp] theorem mem_restrictCodomain_iff {F : Correspondence X Y}
    {B : Set Y} {x : X} {y : B} :
    y ∈ restrictCodomain F B x ↔ (y : Y) ∈ F x := Iff.rfl

/-- Restrict both domain and codomain of a correspondence to subtype carriers. -/
def restrict (F : Correspondence X Y) (A : Set X) (B : Set Y) :
    Correspondence A B :=
  fun x => {y | (y : Y) ∈ F x.1}

@[simp] theorem mem_restrict_iff {F : Correspondence X Y}
    {A : Set X} {B : Set Y} {x : A} {y : B} :
    y ∈ restrict F A B x ↔ (y : Y) ∈ F x.1 := Iff.rfl

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

theorem nonemptyValuedOn_ofFun (f : X → Y) {A : Set X} :
    NonemptyValuedOn (ofFun f) A := by
  intro x hx
  exact ⟨f x, rfl⟩

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

theorem mapsToOn_const {S B : Set Y} {A : Set X} (hS : S ⊆ B) :
    MapsToOn (const (X := X) S) A B := by
  intro x hx y hy
  exact hS hy

theorem nonemptyValuedOn_const {S : Set Y} {A : Set X} (hS : S.Nonempty) :
    NonemptyValuedOn (const (X := X) S) A := by
  intro x hx
  exact hS

@[simp] theorem mapsToOn_identity_iff {A B : Set X} :
    MapsToOn (identity X) A B ↔ A ⊆ B := by
  constructor
  · intro hF x hx
    exact hF hx rfl
  · intro hAB x hx y hy
    rw [mem_identity_iff] at hy
    simpa [hy] using hAB hx

theorem comp_mapsToOn {F : Correspondence X Y} {G : Correspondence Y Z}
    {A : Set X} {B : Set Y} {C : Set Z}
    (hF : MapsToOn F A B) (hG : MapsToOn G B C) :
    MapsToOn (comp G F) A C := by
  intro x hx z hz
  rcases hz with ⟨y, hyF, hzG⟩
  exact hG (hF hx hyF) hzG

theorem comp_nonemptyValuedOn {F : Correspondence X Y} {G : Correspondence Y Z}
    {A : Set X} {B : Set Y}
    (hFmap : MapsToOn F A B)
    (hF : NonemptyValuedOn F A) (hG : NonemptyValuedOn G B) :
    NonemptyValuedOn (comp G F) A := by
  intro x hx
  rcases hF hx with ⟨y, hyF⟩
  rcases hG (hFmap hx hyF) with ⟨z, hzG⟩
  exact ⟨z, ⟨y, hyF, hzG⟩⟩

theorem prod_mapsToOn {F : Correspondence X Y} {G : Correspondence X Z}
    {A : Set X} {B : Set Y} {C : Set Z}
    (hF : MapsToOn F A B) (hG : MapsToOn G A C) :
    MapsToOn (prod F G) A (B ×ˢ C) := by
  intro x hx p hp
  rw [mem_prod_iff] at hp
  exact ⟨hF hx hp.1, hG hx hp.2⟩

theorem prod_nonemptyValuedOn {F : Correspondence X Y} {G : Correspondence X Z}
    {A : Set X} (hF : NonemptyValuedOn F A) (hG : NonemptyValuedOn G A) :
    NonemptyValuedOn (prod F G) A := by
  intro x hx
  rcases hF hx with ⟨y, hyF⟩
  rcases hG hx with ⟨z, hzG⟩
  exact ⟨(y, z), ⟨hyF, hzG⟩⟩

theorem pi_mapsToOn {ι : Type w} {Yᵢ : ι → Type v}
    {F : ∀ i, Correspondence X (Yᵢ i)}
    {A : Set X} {B : ∀ i, Set (Yᵢ i)}
    (hF : ∀ i, MapsToOn (F i) A (B i)) :
    MapsToOn (pi F) A (Set.pi Set.univ B) := by
  intro x hx y hy
  rw [mem_pi_iff] at hy
  rw [Set.mem_univ_pi]
  intro i
  exact hF i hx (hy i)

theorem pi_nonemptyValuedOn {ι : Type w} {Yᵢ : ι → Type v}
    {F : ∀ i, Correspondence X (Yᵢ i)} {A : Set X}
    (hF : ∀ i, NonemptyValuedOn (F i) A) :
    NonemptyValuedOn (pi F) A := by
  classical
  intro x hx
  choose y hy using fun i => hF i hx
  exact ⟨y, by simpa [mem_pi_iff] using hy⟩

@[simp] theorem nonemptyValuedOn_restrictDomain_univ_iff
    {F : Correspondence X Y} {A : Set X} :
    NonemptyValuedOn (restrictDomain F A) Set.univ ↔ NonemptyValuedOn F A := by
  constructor
  · intro hF x hx
    simpa using hF (x := ⟨x, hx⟩) (by simp)
  · intro hF x _hx
    exact hF x.2

@[simp] theorem mapsToOn_restrictDomain_univ_iff
    {F : Correspondence X Y} {A : Set X} {B : Set Y} :
    MapsToOn (restrictDomain F A) Set.univ B ↔ MapsToOn F A B := by
  constructor
  · intro hF x hx y hy
    exact hF (x := ⟨x, hx⟩) (by simp) hy
  · intro hF x _hx y hy
    exact hF x.2 hy

end Carrier

section Topology

variable {X : Type u} {Y : Type v} {Z : Type w}

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

theorem closedValuedOn_const [TopologicalSpace Y] {S : Set Y} {A : Set X}
    (hS : IsClosed S) :
    ClosedValuedOn (const (X := X) S) A := by
  intro x hx
  exact hS

theorem compactValuedOn_const [TopologicalSpace Y] {S : Set Y} {A : Set X}
    (hS : IsCompact S) :
    CompactValuedOn (const (X := X) S) A := by
  intro x hx
  exact hS

theorem compactValuedOn_ofFun [TopologicalSpace Y] (f : X → Y) {A : Set X} :
    CompactValuedOn (ofFun f) A := by
  intro x hx
  exact isCompact_singleton

theorem ClosedGraphOn.closedValuedOn [TopologicalSpace X] [TopologicalSpace Y]
    {F : Correspondence X Y} {A : Set X} (hF : ClosedGraphOn F A) :
    ClosedValuedOn F A := by
  intro x hx
  have hpre : (fun y : Y => (x, y)) ⁻¹' graphOn F A = F x := by
    ext y
    simp [graphOn, hx]
  simpa [hpre] using IsClosed.preimage (Continuous.prodMk_right x) hF

theorem ClosedGraphOn.closedGraphWithin [TopologicalSpace X] [TopologicalSpace Y]
    {F : Correspondence X Y} {A : Set X} {B : Set Y}
    (hF : ClosedGraphOn F A) (hB : IsClosed B) :
    ClosedGraphWithin F A B := by
  have hEq : graphWithin F A B = graphOn F A ∩ Prod.snd ⁻¹' B := by
    ext p
    constructor
    · intro hp
      exact ⟨⟨hp.1, hp.2.2⟩, hp.2.1⟩
    · intro hp
      exact ⟨hp.1.1, hp.2, hp.1.2⟩
  rw [ClosedGraphWithin, hEq]
  exact hF.inter (IsClosed.preimage continuous_snd hB)

theorem ClosedGraphWithin.closedGraphOn_of_mapsToOn
    [TopologicalSpace X] [TopologicalSpace Y]
    {F : Correspondence X Y} {A : Set X} {B : Set Y}
    (hF : ClosedGraphWithin F A B) (hMap : MapsToOn F A B) :
    ClosedGraphOn F A := by
  simpa [ClosedGraphWithin, ClosedGraphOn, graphWithin_eq_graphOn_of_mapsToOn hMap] using hF

@[simp] theorem closedValuedOn_restrictDomain_univ_iff
    [TopologicalSpace Y] {F : Correspondence X Y} {A : Set X} :
    ClosedValuedOn (restrictDomain F A) Set.univ ↔ ClosedValuedOn F A := by
  constructor
  · intro hF x hx
    simpa using hF (x := ⟨x, hx⟩) (by simp)
  · intro hF x _hx
    exact hF x.2

@[simp] theorem compactValuedOn_restrictDomain_univ_iff
    [TopologicalSpace Y] {F : Correspondence X Y} {A : Set X} :
    CompactValuedOn (restrictDomain F A) Set.univ ↔ CompactValuedOn F A := by
  constructor
  · intro hF x hx
    simpa using hF (x := ⟨x, hx⟩) (by simp)
  · intro hF x _hx
    exact hF x.2

theorem prod_closedValuedOn [TopologicalSpace Y] [TopologicalSpace Z]
    {F : Correspondence X Y} {G : Correspondence X Z} {A : Set X}
    (hF : ClosedValuedOn F A) (hG : ClosedValuedOn G A) :
    ClosedValuedOn (prod F G) A := by
  intro x hx
  exact (hF hx).prod (hG hx)

theorem prod_compactValuedOn [TopologicalSpace Y] [TopologicalSpace Z]
    {F : Correspondence X Y} {G : Correspondence X Z} {A : Set X}
    (hF : CompactValuedOn F A) (hG : CompactValuedOn G A) :
    CompactValuedOn (prod F G) A := by
  intro x hx
  exact (hF hx).prod (hG hx)

/-- Closed graphs are preserved by pointwise products of correspondences. -/
theorem prod_closedGraphOn [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {F : Correspondence X Y} {G : Correspondence X Z} {A : Set X}
    (hF : ClosedGraphOn F A) (hG : ClosedGraphOn G A) :
    ClosedGraphOn (prod F G) A := by
  let πF : X × (Y × Z) → X × Y := fun p => (p.1, p.2.1)
  let πG : X × (Y × Z) → X × Z := fun p => (p.1, p.2.2)
  have hπF : Continuous πF :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hπG : Continuous πG :=
    continuous_fst.prodMk (continuous_snd.comp continuous_snd)
  have hEq :
      graphOn (prod F G) A =
        πF ⁻¹' graphOn F A ∩ πG ⁻¹' graphOn G A := by
    ext p
    constructor
    · intro hp
      exact ⟨⟨hp.1, hp.2.1⟩, ⟨hp.1, hp.2.2⟩⟩
    · intro hp
      exact ⟨hp.1.1, hp.1.2, hp.2.2⟩
  rw [ClosedGraphOn, hEq]
  exact (IsClosed.preimage hπF hF).inter (IsClosed.preimage hπG hG)

theorem pi_closedValuedOn {ι : Type w} {Yᵢ : ι → Type v}
    [∀ i, TopologicalSpace (Yᵢ i)]
    {F : ∀ i, Correspondence X (Yᵢ i)} {A : Set X}
    (hF : ∀ i, ClosedValuedOn (F i) A) :
    ClosedValuedOn (pi F) A := by
  intro x hx
  have hEq :
      pi F x = ⋂ i, (fun y : ∀ i, Yᵢ i => y i) ⁻¹' F i x := by
    ext y
    simp [pi]
  rw [hEq]
  exact isClosed_iInter fun i => IsClosed.preimage (continuous_apply i) (hF i hx)

theorem pi_compactValuedOn {ι : Type w} {Yᵢ : ι → Type v}
    [∀ i, TopologicalSpace (Yᵢ i)]
    {F : ∀ i, Correspondence X (Yᵢ i)} {A : Set X}
    (hF : ∀ i, CompactValuedOn (F i) A) :
    CompactValuedOn (pi F) A := by
  intro x hx
  simpa [pi] using isCompact_univ_pi fun i => hF i hx

/--
Closed graphs are preserved by indexed products when the carrier is closed.
The explicit closed-carrier hypothesis handles the empty index type.
-/
theorem pi_closedGraphOn {ι : Type w} {Yᵢ : ι → Type v}
    [TopologicalSpace X] [∀ i, TopologicalSpace (Yᵢ i)]
    {F : ∀ i, Correspondence X (Yᵢ i)} {A : Set X}
    (hA : IsClosed A) (hF : ∀ i, ClosedGraphOn (F i) A) :
    ClosedGraphOn (pi F) A := by
  let π : (i : ι) → X × (∀ i, Yᵢ i) → X × Yᵢ i :=
    fun i p => (p.1, p.2 i)
  have hπ : ∀ i, Continuous (π i) := by
    intro i
    exact continuous_fst.prodMk (continuous_apply i |>.comp continuous_snd)
  have hEq :
      graphOn (pi F) A =
        Prod.fst ⁻¹' A ∩ ⋂ i, (π i) ⁻¹' graphOn (F i) A := by
    ext p
    simp [graphOn, pi, π]
    intro hpA
    constructor
    · intro hp i
      exact ⟨hpA, hp i⟩
    · intro hp i
      exact (hp i).2
  rw [ClosedGraphOn, hEq]
  exact (IsClosed.preimage continuous_fst hA).inter
    (isClosed_iInter fun i => IsClosed.preimage (hπ i) (hF i))

/-- A continuous single-valued map has a closed graph over a closed carrier. -/
theorem closedGraphOn_ofFun [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} {A : Set X} (hA : IsClosed A) (hf : ContinuousOn f A) :
    ClosedGraphOn (ofFun f) A := by
  let carrier : Set (X × Y) := Prod.fst ⁻¹' A
  have hcarrier : IsClosed carrier := IsClosed.preimage continuous_fst hA
  have hfOn : ContinuousOn (fun p : X × Y => f p.1) carrier :=
    hf.comp continuous_fst.continuousOn (by intro p hp; exact hp)
  have hsndOn : ContinuousOn (fun p : X × Y => p.2) carrier :=
    continuous_snd.continuousOn
  have hEq :
      graphOn (ofFun f) A = {p ∈ carrier | p.2 = f p.1} := by
    ext p
    rfl
  rw [ClosedGraphOn, hEq]
  exact hcarrier.isClosed_eq hsndOn hfOn

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

variable {𝕜 : Type u} {X : Type v} {Y : Type w} {Z : Type t}

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

theorem convexValuedOn_const [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid Y] [SMul 𝕜 Y] {S : Set Y} {A : Set X}
    (hS : Convex 𝕜 S) :
    ConvexValuedOn (𝕜 := 𝕜) (const (X := X) S) A := by
  intro x hx
  exact hS

theorem convexValuedOn_ofFun [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid Y] [Module 𝕜 Y] (f : X → Y) {A : Set X} :
    ConvexValuedOn (𝕜 := 𝕜) (ofFun f) A := by
  intro x hx
  exact convex_singleton (f x)

@[simp] theorem convexValuedOn_restrictDomain_univ_iff
    [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid Y] [SMul 𝕜 Y]
    {F : Correspondence X Y} {A : Set X} :
    ConvexValuedOn (𝕜 := 𝕜) (restrictDomain F A) Set.univ ↔
      ConvexValuedOn (𝕜 := 𝕜) F A := by
  constructor
  · intro hF x hx
    simpa using hF (x := ⟨x, hx⟩) (by simp)
  · intro hF x _hx
    exact hF x.2

theorem prod_convexValuedOn [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid Y] [SMul 𝕜 Y] [AddCommMonoid Z] [SMul 𝕜 Z]
    {F : Correspondence X Y} {G : Correspondence X Z} {A : Set X}
    (hF : ConvexValuedOn (𝕜 := 𝕜) F A)
    (hG : ConvexValuedOn (𝕜 := 𝕜) G A) :
    ConvexValuedOn (𝕜 := 𝕜) (prod F G) A := by
  intro x hx
  exact (hF hx).prod (hG hx)

theorem pi_convexValuedOn {ι : Type t} {Yᵢ : ι → Type w}
    [Semiring 𝕜] [PartialOrder 𝕜]
    [∀ i, AddCommMonoid (Yᵢ i)] [∀ i, SMul 𝕜 (Yᵢ i)]
    {F : ∀ i, Correspondence X (Yᵢ i)} {A : Set X}
    (hF : ∀ i, ConvexValuedOn (𝕜 := 𝕜) (F i) A) :
    ConvexValuedOn (𝕜 := 𝕜) (pi F) A := by
  intro x hx
  simpa [pi] using convex_pi (s := (Set.univ : Set ι)) (fun i _hi => hF i hx)

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

theorem argmax_mapsToOn {u : X → Y → ℝ} {F : Correspondence X Y}
    {A : Set X} {B : Set Y} (hF : MapsToOn F A B) :
    MapsToOn (argmax u F) A B := by
  intro x hxA y hy
  exact hF hxA hy.1

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
If maximizers exist, closed feasible values and objective continuity make the
argmax correspondence closed-valued.
-/
theorem argmax_closedValuedOn_of_closed_of_nonempty
    [TopologicalSpace Y] {u : X → Y → ℝ} {F : Correspondence X Y}
    {A : Set X} (hClosed : ClosedValuedOn F A)
    (hArgmax : NonemptyValuedOn (argmax u F) A)
    (hu : ∀ ⦃x⦄, x ∈ A → ContinuousOn (u x) (F x)) :
    ClosedValuedOn (argmax u F) A := by
  intro x hxA
  rcases hArgmax hxA with ⟨y₀, hy₀⟩
  have hEq :
      argmax u F x = F x ∩ (u x) ⁻¹' Set.Ici (u x y₀) := by
    ext y
    constructor
    · intro hy
      exact ⟨hy.1, hy.2 y₀ hy₀.1⟩
    · intro hy
      exact ⟨hy.1, fun z hz => (hy₀.2 z hz).trans hy.2⟩
  simpa [hEq] using
    (hu hxA).preimage_isClosed_of_isClosed (hClosed hxA) isClosed_Ici

/--
Compact feasible values, closed feasible values, existing maximizers, and
objective continuity make the argmax correspondence compact-valued.
-/
theorem argmax_compactValuedOn_of_compact_of_closed_of_nonempty
    [TopologicalSpace Y] {u : X → Y → ℝ} {F : Correspondence X Y}
    {A : Set X} (hCompact : CompactValuedOn F A)
    (hClosed : ClosedValuedOn F A)
    (hArgmax : NonemptyValuedOn (argmax u F) A)
    (hu : ∀ ⦃x⦄, x ∈ A → ContinuousOn (u x) (F x)) :
    CompactValuedOn (argmax u F) A := by
  have hClosedArgmax :
      ClosedValuedOn (argmax u F) A :=
    argmax_closedValuedOn_of_closed_of_nonempty hClosed hArgmax hu
  intro x hxA
  exact (hCompact hxA).of_isClosed_subset (hClosedArgmax hxA) (argmax_subset x)

/--
In Hausdorff codomains, compact feasible values and objective continuity make
argmax compact-valued whenever the feasible correspondence is nonempty-valued.
-/
theorem argmax_compactValuedOn_of_compact
    [TopologicalSpace Y] [T2Space Y] {u : X → Y → ℝ}
    {F : Correspondence X Y} {A : Set X}
    (hCompact : CompactValuedOn F A)
    (hNonempty : NonemptyValuedOn F A)
    (hu : ∀ ⦃x⦄, x ∈ A → ContinuousOn (u x) (F x)) :
    CompactValuedOn (argmax u F) A := by
  exact argmax_compactValuedOn_of_compact_of_closed_of_nonempty
    hCompact hCompact.closedValuedOn
    (argmax_nonemptyValuedOn_of_compact hCompact hNonempty hu) hu

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

/--
Fixed-feasible-set argmax has a closed graph when the feasible set and carrier
are closed and the objective is continuous on their product.

This is the constant-feasible-set core of the maximum theorem; the fully
variable-feasible version will require lower hemicontinuity.
-/
theorem argmax_const_closedGraphOn
    [TopologicalSpace X] [TopologicalSpace Y] {u : X → Y → ℝ}
    {A : Set X} {K : Set Y}
    (hA : IsClosed A) (hK : IsClosed K) (hKne : K.Nonempty)
    (hu : ContinuousOn (fun p : X × Y => u p.1 p.2) (A ×ˢ K)) :
    ClosedGraphOn (argmax u (const (X := X) K)) A := by
  let feasible : Set (X × Y) := A ×ˢ K
  have hfeasible : IsClosed feasible := hA.prod hK
  have hEq :
      graphOn (argmax u (const (X := X) K)) A =
        ⋂ z : K, {p : X × Y | p ∈ feasible ∧ u p.1 z.1 ≤ u p.1 p.2} := by
    ext p
    constructor
    · intro hp
      rw [Set.mem_iInter]
      intro z
      exact ⟨⟨hp.1, hp.2.1⟩, hp.2.2 z.1 z.2⟩
    · intro hp
      rw [Set.mem_iInter] at hp
      rcases hKne with ⟨z₀, hz₀⟩
      have hp₀ := hp ⟨z₀, hz₀⟩
      exact ⟨hp₀.1.1, hp₀.1.2, fun z hzK => (hp ⟨z, hzK⟩).2⟩
  rw [ClosedGraphOn, hEq]
  refine isClosed_iInter fun z : K => ?_
  have hconst :
      ContinuousOn (fun p : X × Y => u p.1 z.1) feasible := by
    let φ : X × Y → X × Y := fun p => (p.1, z.1)
    have hφcont : Continuous φ := continuous_fst.prodMk continuous_const
    have hφmap : Set.MapsTo φ feasible feasible := by
      intro p hp
      exact ⟨hp.1, z.2⟩
    simpa [φ, Function.comp_def] using hu.comp hφcont.continuousOn hφmap
  exact hfeasible.isClosed_le hconst hu

/--
Variable-feasible-set argmax has a closed graph when the feasible
correspondence has a closed graph, is lower hemicontinuous, and the objective
is globally continuous.

This is the closed-graph half of Berge's maximum theorem in the form needed
for best-response correspondences: lower hemicontinuity supplies nearby
feasible competitors, while continuity of payoffs transfers strict
non-optimality to nearby parameters.
-/
theorem argmax_closedGraphOn
    [TopologicalSpace X] [TopologicalSpace Y] {u : X → Y → ℝ}
    {F : Correspondence X Y} {A : Set X}
    (hA : IsClosed A) (hFclosed : ClosedGraphOn F A)
    (hFlhc : LowerHemicontinuousOn F A)
    (hu : Continuous fun p : X × Y => u p.1 p.2) :
    ClosedGraphOn (argmax u F) A := by
  classical
  rw [ClosedGraphOn, ← isOpen_compl_iff]
  refine isOpen_iff_mem_nhds.mpr ?_
  intro p hp
  rcases p with ⟨x, y⟩
  by_cases hxA : x ∈ A
  · by_cases hyF : y ∈ F x
    · have hnotArg : y ∉ argmax u F x := by
        intro hyArg
        exact hp ⟨hxA, hyArg⟩
      rw [mem_argmax_iff] at hnotArg
      have hnotMax : ¬ ∀ z, z ∈ F x → u x z ≤ u x y := by
        intro hmax
        exact hnotArg ⟨hyF, hmax⟩
      push_neg at hnotMax
      rcases hnotMax with ⟨z, hzF, hyz⟩
      rcases exists_between hyz with ⟨c, hyc, hcz⟩
      let low : Set (X × Y) := {q | u q.1 q.2 < c}
      let high : Set (X × Y) := {q | c < u q.1 q.2}
      have hlowOpen : IsOpen low := isOpen_Iio.preimage hu
      have hhighOpen : IsOpen high := isOpen_Ioi.preimage hu
      have hhighMem : high ∈ nhds (x, z) :=
        hhighOpen.mem_nhds hcz
      rcases mem_nhds_prod_iff'.mp hhighMem with
        ⟨Ux, Vz, hUxOpen, hxUx, hVzOpen, hzVz, hprodHigh⟩
      have hInter : (F x ∩ Vz).Nonempty := ⟨z, hzF, hzVz⟩
      have hLhcEventually :
          ∀ᶠ x' in nhdsWithin x A, IsOpen Vz ∧ (F x' ∩ Vz).Nonempty :=
        hFlhc x hxA Vz ⟨hVzOpen, hInter⟩
      have hLhcSet : {x' | (F x' ∩ Vz).Nonempty} ∈ nhdsWithin x A := by
        filter_upwards [hLhcEventually] with x' hx'
        exact hx'.2
      rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hLhcSet with
        ⟨Nlhc, hNlhcMem, hNlhcSub⟩
      rcases mem_nhds_iff.mp hNlhcMem with
        ⟨Ulhc, hUlhcSub, hUlhcOpen, hxUlhc⟩
      let U : Set (X × Y) := low ∩ Prod.fst ⁻¹' (Ux ∩ Ulhc)
      have hUopen : IsOpen U :=
        hlowOpen.inter ((hUxOpen.inter hUlhcOpen).preimage continuous_fst)
      have hpU : (x, y) ∈ U := ⟨hyc, hxUx, hxUlhc⟩
      have hUsub : U ⊆ (graphOn (argmax u F) A)ᶜ := by
        intro q hq hqGraph
        rcases hq with ⟨hqLow, hqUx, hqUlhc⟩
        rcases hqGraph with ⟨hqA, hqArg⟩
        have hNonempty : (F q.1 ∩ Vz).Nonempty :=
          hNlhcSub ⟨hUlhcSub hqUlhc, hqA⟩
        rcases hNonempty with ⟨z', hz'F, hz'Vz⟩
        have hHigh : c < u q.1 z' :=
          show (q.1, z') ∈ high from hprodHigh ⟨hqUx, hz'Vz⟩
        have hz'Le : u q.1 z' ≤ u q.1 q.2 :=
          hqArg.2 z' hz'F
        exact not_lt_of_ge hz'Le (hqLow.trans hHigh)
      exact Filter.mem_of_superset (hUopen.mem_nhds hpU) hUsub
    · let U : Set (X × Y) := (graphOn F A)ᶜ
      have hUopen : IsOpen U := isOpen_compl_iff.mpr hFclosed
      have hpU : (x, y) ∈ U := by
        intro hpF
        exact hyF hpF.2
      have hUsub : U ⊆ (graphOn (argmax u F) A)ᶜ := by
        intro q hq hqGraph
        exact hq ⟨hqGraph.1, argmax_subset q.1 hqGraph.2⟩
      exact Filter.mem_of_superset (hUopen.mem_nhds hpU) hUsub
  · let U : Set (X × Y) := Prod.fst ⁻¹' Aᶜ
    have hUopen : IsOpen U :=
      hA.isOpen_compl.preimage continuous_fst
    have hpU : (x, y) ∈ U := hxA
    have hUsub : U ⊆ (graphOn (argmax u F) A)ᶜ := by
      intro q hq hqGraph
      exact hq hqGraph.1
    exact Filter.mem_of_superset (hUopen.mem_nhds hpU) hUsub

end Argmax

section FixedPoints

variable {X : Type u} {Y : Type v}

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

/--
Transport a self-correspondence across an equivalence of ambient spaces.

This is the correspondence-level conjugation operation: a point `y` in the
target space is sent to the image, under `e`, of the old value at `e.symm y`.
It is the fixed-point version of changing coordinates.
-/
def equivConjugate (e : X ≃ Y) (F : Correspondence X X) : Correspondence Y Y :=
  fun y => e '' F (e.symm y)

@[simp] theorem mem_equivConjugate_iff {e : X ≃ Y}
    {F : Correspondence X X} {y y' : Y} :
    y' ∈ equivConjugate e F y ↔ e.symm y' ∈ F (e.symm y) := by
  constructor
  · rintro ⟨x, hxF, rfl⟩
    simpa using hxF
  · intro hy
    exact ⟨e.symm y', hy, by simp⟩

@[simp] theorem mem_fixedPoints_equivConjugate_iff {e : X ≃ Y}
    {F : Correspondence X X} {y : Y} :
    y ∈ fixedPoints (equivConjugate e F) ↔ e.symm y ∈ fixedPoints F := by
  rw [mem_fixedPoints_iff, mem_equivConjugate_iff, mem_fixedPoints_iff]

@[simp] theorem fixedPointOn_equivConjugate_iff {e : X ≃ Y}
    {F : Correspondence X X} {A : Set X} {y : Y} :
    FixedPointOn (equivConjugate e F) (e '' A) y ↔
      FixedPointOn F A (e.symm y) := by
  constructor
  · intro hy
    exact
      ⟨by simpa [Equiv.image_eq_preimage_symm] using hy.1,
        by simpa using (mem_equivConjugate_iff.mp hy.2)⟩
  · intro hx
    exact
      ⟨by simpa [Equiv.image_eq_preimage_symm] using hx.1,
        by simpa using (mem_equivConjugate_iff.mpr hx.2)⟩

theorem fixedPointsOn_equivConjugate {e : X ≃ Y}
    (F : Correspondence X X) (A : Set X) :
    fixedPointsOn (equivConjugate e F) (e '' A) = e '' fixedPointsOn F A := by
  ext y
  change FixedPointOn (equivConjugate e F) (e '' A) y ↔
    y ∈ e '' fixedPointsOn F A
  constructor
  · intro hy
    exact ⟨e.symm y, fixedPointOn_equivConjugate_iff.mp hy, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    exact fixedPointOn_equivConjugate_iff.mpr (by simpa using hx)

theorem graphOn_equivConjugate {e : X ≃ Y}
    (F : Correspondence X X) (A : Set X) :
    graphOn (equivConjugate e F) (e '' A) =
      (e.prodCongr e) '' graphOn F A := by
  ext p
  constructor
  · intro hp
    refine ⟨(e.symm p.1, e.symm p.2), ?_, ?_⟩
    · exact
        ⟨by simpa [Equiv.image_eq_preimage_symm] using hp.1,
          by simpa using (mem_equivConjugate_iff.mp hp.2)⟩
    · ext <;> simp
  · rintro ⟨p, hp, rfl⟩
    have hpF : e.symm (e p.2) ∈ F (e.symm (e p.1)) := by
      simpa using hp.2
    exact
      ⟨⟨p.1, hp.1, rfl⟩,
        mem_equivConjugate_iff.mpr hpF⟩

@[simp] theorem mem_fixedPoints_ofFun_iff {f : X → X} {x : X} :
    x ∈ fixedPoints (ofFun f) ↔ f x = x := by
  rw [mem_fixedPoints_iff, mem_ofFun_iff, eq_comm]

@[simp] theorem fixedPointOn_ofFun_iff {f : X → X} {A : Set X} {x : X} :
    FixedPointOn (ofFun f) A x ↔ x ∈ A ∧ f x = x := by
  rw [fixedPointOn_iff, mem_ofFun_iff, eq_comm]

/-- Closed graph correspondences have closed fixed-point sets. -/
theorem ClosedGraphOn.isClosed_fixedPointsOn [TopologicalSpace X]
    {F : Correspondence X X} {A : Set X} (hF : ClosedGraphOn F A) :
    IsClosed (fixedPointsOn F A) := by
  let diagonal : X → X × X := fun x => (x, x)
  have hDiagonal : Continuous diagonal := continuous_id.prodMk continuous_id
  have hpre : diagonal ⁻¹' graphOn F A = fixedPointsOn F A := by
    ext x
    simp [diagonal]
  simpa [hpre] using IsClosed.preimage hDiagonal hF

/-- On a compact carrier, closed graph correspondences have compact fixed-point sets. -/
theorem ClosedGraphOn.isCompact_fixedPointsOn [TopologicalSpace X]
    {F : Correspondence X X} {A : Set X}
    (hF : ClosedGraphOn F A) (hA : IsCompact A) :
    IsCompact (fixedPointsOn F A) := by
  exact hA.of_isClosed_subset hF.isClosed_fixedPointsOn (fixedPointsOn_subset F A)

/--
A carrier has the Brouwer fixed-point property if every continuous
self-map of the carrier has a fixed point.

This is deliberately stated as a reusable property rather than specialized
to Euclidean simplexes; later Brouwer theorems can instantiate it for
compact convex finite-dimensional domains.
-/
def BrouwerFixedPointProperty [TopologicalSpace X] (K : Set X) : Prop :=
  ∀ f : X → X, Set.MapsTo f K K → ContinuousOn f K → ∃ x ∈ K, f x = x

theorem BrouwerFixedPointProperty.hasFixedPointOn_ofFun [TopologicalSpace X]
    {K : Set X} (hK : BrouwerFixedPointProperty K)
    {f : X → X} (hfMap : Set.MapsTo f K K) (hfCont : ContinuousOn f K) :
    HasFixedPointOn (ofFun f) K := by
  rcases hK f hfMap hfCont with ⟨x, hxK, hfx⟩
  exact ⟨x, hxK, by rw [mem_ofFun_iff]; exact hfx.symm⟩

/-- Brouwer's fixed-point property is invariant under homeomorphic changes
of coordinates. -/
theorem BrouwerFixedPointProperty.image_homeomorph
    [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set X} (hK : BrouwerFixedPointProperty K) (e : X ≃ₜ Y) :
    BrouwerFixedPointProperty (e '' K) := by
  intro g hgMap hgCont
  let f : X → X := fun x => e.symm (g (e x))
  have hfMap : Set.MapsTo f K K := by
    intro x hxK
    have hgx : g (e x) ∈ e '' K := hgMap ⟨x, hxK, rfl⟩
    simpa [f, Homeomorph.image_eq_preimage_symm] using hgx
  have heMap : Set.MapsTo e K (e '' K) := by
    intro x hxK
    exact ⟨x, hxK, rfl⟩
  have hgeCont : ContinuousOn (fun x : X => g (e x)) K :=
    hgCont.comp e.continuous.continuousOn heMap
  have hfCont : ContinuousOn f K := by
    simpa [f, Function.comp_def] using
      e.symm.continuous.comp_continuousOn hgeCont
  rcases hK f hfMap hfCont with ⟨x, hxK, hfx⟩
  refine ⟨e x, ⟨x, hxK, rfl⟩, ?_⟩
  have hfx' := congrArg (fun z : X => e z) hfx
  simpa [f] using hfx'

/-- Brouwer's fixed-point property pulls back along homeomorphisms. -/
theorem BrouwerFixedPointProperty.preimage_homeomorph
    [TopologicalSpace X] [TopologicalSpace Y]
    {L : Set Y} (hL : BrouwerFixedPointProperty L) (e : X ≃ₜ Y) :
    BrouwerFixedPointProperty (e ⁻¹' L) := by
  simpa [Homeomorph.image_symm] using hL.image_homeomorph e.symm

/--
Brouwer's fixed-point property is invariant under homeomorphisms of the
carrier subtypes.

This bridges mathlib's common style of building homeomorphisms between
subtypes, such as `stdSimplex ℝ (Fin 2) ≃ₜ unitInterval`, with eco-lean's
carrier-set API.
-/
theorem BrouwerFixedPointProperty.of_subtype_homeomorph
    [TopologicalSpace X] [TopologicalSpace Y] {K : Set X} {L : Set Y}
    (hK : BrouwerFixedPointProperty K) (e : K ≃ₜ L) :
    BrouwerFixedPointProperty L := by
  classical
  intro f hfMap hfCont
  let fL : L → L := fun y => ⟨f y, hfMap y.2⟩
  have hfLCont : Continuous fL := by
    have hfRestrict : Continuous (L.restrict f) := hfCont.restrict
    exact hfRestrict.codRestrict (fun y => hfMap y.2)
  let gK : K → K := e.symm ∘ fL ∘ e
  let g : X → X := fun x => if hx : x ∈ K then (gK ⟨x, hx⟩ : X) else x
  have hgMap : Set.MapsTo g K K := by
    intro x hx
    simp [g, hx]
  have hgCont : ContinuousOn g K := by
    rw [continuousOn_iff_continuous_restrict]
    have hgKCont : Continuous gK := e.symm.continuous.comp (hfLCont.comp e.continuous)
    have hgValCont : Continuous fun x : K => (gK x : X) :=
      continuous_subtype_val.comp hgKCont
    refine hgValCont.congr ?_
    intro x
    simp [g, x.2]
  rcases hK g hgMap hgCont with ⟨x, hxK, hxFixed⟩
  let xK : K := ⟨x, hxK⟩
  have hxKFixed : gK xK = xK := by
    apply Subtype.ext
    simpa [g, xK, hxK] using hxFixed
  have hyFixedSubtype : fL (e xK) = e xK := by
    have h := congrArg e hxKFixed
    simpa [gK, Function.comp_def] using h
  refine ⟨(e xK : Y), (e xK).2, ?_⟩
  exact congrArg Subtype.val hyFixedSubtype

theorem brouwerFixedPointProperty_image_homeomorph_iff
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (K : Set X) :
    BrouwerFixedPointProperty (e '' K) ↔ BrouwerFixedPointProperty K := by
  constructor
  · intro hK
    simpa using hK.preimage_homeomorph e
  · intro hK
    exact hK.image_homeomorph e

/-- Brouwer's fixed-point property is preserved by continuous affine
equivalences. -/
theorem BrouwerFixedPointProperty.image_continuousAffineEquiv
    [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommGroup X] [AddCommGroup Y] [Module ℝ X] [Module ℝ Y]
    {K : Set X} (hK : BrouwerFixedPointProperty K) (e : X ≃ᴬ[ℝ] Y) :
    BrouwerFixedPointProperty (e '' K) :=
  hK.image_homeomorph e.toHomeomorph

theorem brouwerFixedPointProperty_image_continuousAffineEquiv_iff
    [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommGroup X] [AddCommGroup Y] [Module ℝ X] [Module ℝ Y]
    (e : X ≃ᴬ[ℝ] Y) (K : Set X) :
    BrouwerFixedPointProperty (e '' K) ↔ BrouwerFixedPointProperty K :=
  brouwerFixedPointProperty_image_homeomorph_iff e.toHomeomorph K

/--
The one-dimensional Brouwer fixed-point theorem for closed intervals.

This is the first concrete instance of `BrouwerFixedPointProperty` in the
library. It packages mathlib's intermediate-value-theorem fixed-point result
in the correspondence API used by the game-theory existence layer.
-/
theorem brouwerFixedPointProperty_Icc
    {α : Type u} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [DenselyOrdered α] {a b : α} (hab : a ≤ b) :
    BrouwerFixedPointProperty (Set.Icc a b) := by
  intro f hfMap hfCont
  exact exists_mem_Icc_isFixedPt_of_mapsTo hfCont hab hfMap

/--
The one-dimensional Brouwer fixed-point theorem for unordered closed
intervals.

This wrapper is useful when an interval is constructed before choosing an
orientation for its endpoints.
-/
theorem brouwerFixedPointProperty_uIcc
    {α : Type u} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [DenselyOrdered α] (a b : α) :
    BrouwerFixedPointProperty (Set.uIcc a b) := by
  rcases le_total a b with hab | hba
  · simpa [Set.uIcc_of_le hab] using
      (brouwerFixedPointProperty_Icc (a := a) (b := b) hab)
  · simpa [Set.uIcc_of_ge hba] using
      (brouwerFixedPointProperty_Icc (a := b) (b := a) hba)

/-- Singleton carriers have the Brouwer fixed-point property. -/
theorem brouwerFixedPointProperty_singleton [TopologicalSpace X] (x : X) :
    BrouwerFixedPointProperty ({x} : Set X) := by
  intro f hfMap _hfCont
  exact ⟨x, by simp, by simpa using hfMap (by simp : x ∈ ({x} : Set X))⟩

/--
The standard one-dimensional simplex has Brouwer's fixed-point property.

This is the first simplex-shaped Brouwer instance in the eco-lean carrier API:
it transfers the interval theorem through mathlib's homeomorphism
`stdSimplexHomeomorphUnitInterval`.
-/
theorem brouwerFixedPointProperty_stdSimplex_fin_two :
    BrouwerFixedPointProperty (stdSimplex ℝ (Fin 2)) := by
  have hI : BrouwerFixedPointProperty unitInterval :=
    brouwerFixedPointProperty_Icc (α := ℝ) (a := 0) (b := 1) zero_le_one
  exact hI.of_subtype_homeomorph stdSimplexHomeomorphUnitInterval.symm

/--
The face of a standard simplex whose nonzero coordinates are supported on
the finite index set `J`.

This is the carrier-set version of the usual notation
`conv {e i | i ∈ J}` for a coordinate face.
-/
def stdSimplexFace {ι : Type u} [Fintype ι] (J : Finset ι) :
    Set (stdSimplex ℝ ι) :=
  {x | ∀ i, x i ≠ 0 → i ∈ J}

@[simp] theorem mem_stdSimplexFace_iff {ι : Type u} [Fintype ι]
    {J : Finset ι} {x : stdSimplex ℝ ι} :
    x ∈ stdSimplexFace J ↔ ∀ i, x i ≠ 0 → i ∈ J :=
  Iff.rfl

theorem mem_stdSimplexFace_iff_eq_zero_of_not_mem {ι : Type u} [Fintype ι]
    {J : Finset ι} {x : stdSimplex ℝ ι} :
    x ∈ stdSimplexFace J ↔ ∀ i, i ∉ J → x i = 0 := by
  constructor
  · intro hx i hiJ
    by_contra hxi
    exact hiJ (hx i hxi)
  · intro hx i hxi
    by_contra hiJ
    exact hxi (hx i hiJ)

theorem stdSimplexFace_mono {ι : Type u} [Fintype ι]
    {J K : Finset ι} (hJK : J ⊆ K) :
    stdSimplexFace J ⊆ stdSimplexFace K := by
  intro x hx i hxi
  exact hJK (hx i hxi)

@[simp] theorem stdSimplexFace_univ {ι : Type u} [Fintype ι] :
    stdSimplexFace (Finset.univ : Finset ι) = Set.univ := by
  ext x
  simp [stdSimplexFace]

theorem vertex_mem_stdSimplexFace {ι : Type u} [Fintype ι] [DecidableEq ι]
    {J : Finset ι} {i : ι} (hi : i ∈ J) :
    stdSimplex.vertex (S := ℝ) i ∈ stdSimplexFace J := by
  intro j hj
  have hji : j = i := by
    by_contra hne
    have hzero : stdSimplex.vertex (S := ℝ) i j = 0 := by
      simp [stdSimplex.vertex, Pi.single_eq_of_ne hne]
    exact hj hzero
  simpa [hji] using hi

theorem nonempty_stdSimplexFace {ι : Type u} [Fintype ι] [DecidableEq ι]
    {J : Finset ι} (hJ : J.Nonempty) :
    (stdSimplexFace J).Nonempty := by
  rcases hJ with ⟨i, hi⟩
  exact ⟨stdSimplex.vertex (S := ℝ) i, vertex_mem_stdSimplexFace hi⟩

theorem isClosed_stdSimplexFace {ι : Type u} [Fintype ι]
    (J : Finset ι) : IsClosed (stdSimplexFace J) := by
  rw [show stdSimplexFace J =
      Set.iInter (fun i : Subtype (fun i : ι => i ∉ J) =>
        {x : stdSimplex ℝ ι | x (i : ι) = 0}) by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hx i
      exact (mem_stdSimplexFace_iff_eq_zero_of_not_mem.mp hx) i i.2
    · intro hx
      exact mem_stdSimplexFace_iff_eq_zero_of_not_mem.mpr fun i hiJ => hx ⟨i, hiJ⟩]
  exact isClosed_iInter fun i =>
    isClosed_eq ((continuous_apply (i : ι)).comp continuous_subtype_val) continuous_const

theorem isCompact_stdSimplexFace {ι : Type u} [Fintype ι]
    (J : Finset ι) : IsCompact (stdSimplexFace J) :=
  (isClosed_stdSimplexFace J).isCompact

/--
The canonical parametrization of a coordinate face by a lower-dimensional
standard simplex.

An element of `stdSimplex ℝ {i // i ∈ J}` is extended by zero outside `J`.
-/
noncomputable def stdSimplexFaceMap {ι : Type u} [Fintype ι] [DecidableEq ι]
    (J : Finset ι) : stdSimplex ℝ {i // i ∈ J} → stdSimplex ℝ ι :=
  stdSimplex.map (S := ℝ) (fun i : {i // i ∈ J} => (i : ι))

@[simp] theorem stdSimplexFaceMap_apply_of_mem {ι : Type u}
    [Fintype ι] [DecidableEq ι] (J : Finset ι)
    (x : stdSimplex ℝ {i // i ∈ J}) {i : ι} (hi : i ∈ J) :
    stdSimplexFaceMap J x i = x ⟨i, hi⟩ := by
  classical
  change (FunOnFinite.linearMap ℝ ℝ (fun j : {i // i ∈ J} => (j : ι)) x) i =
    x ⟨i, hi⟩
  rw [FunOnFinite.linearMap_apply_apply]
  have hfilter :
      Finset.univ.filter (fun j : {i // i ∈ J} => (j : ι) = i) = {⟨i, hi⟩} := by
    ext j
    simp [Subtype.ext_iff]
  rw [hfilter]
  simp

@[simp] theorem stdSimplexFaceMap_apply_of_not_mem {ι : Type u}
    [Fintype ι] [DecidableEq ι] (J : Finset ι)
    (x : stdSimplex ℝ {i // i ∈ J}) {i : ι} (hi : i ∉ J) :
    stdSimplexFaceMap J x i = 0 := by
  classical
  change (FunOnFinite.linearMap ℝ ℝ (fun j : {i // i ∈ J} => (j : ι)) x) i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  have hfilter :
      Finset.univ.filter (fun j : {i // i ∈ J} => (j : ι) = i) = ∅ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hji
      exact (hi (by simpa [hji] using j.2)).elim
    · intro hfalse
      simp at hfalse
  rw [hfilter]
  simp

theorem stdSimplexFaceMap_mem {ι : Type u} [Fintype ι] [DecidableEq ι]
    (J : Finset ι) (x : stdSimplex ℝ {i // i ∈ J}) :
    stdSimplexFaceMap J x ∈ stdSimplexFace J := by
  rw [mem_stdSimplexFace_iff_eq_zero_of_not_mem]
  intro i hi
  exact stdSimplexFaceMap_apply_of_not_mem J x hi

theorem continuous_stdSimplexFaceMap {ι : Type u} [Fintype ι] [DecidableEq ι]
    (J : Finset ι) : Continuous (stdSimplexFaceMap J) :=
  stdSimplex.continuous_map (S := ℝ) (fun i : {i // i ∈ J} => (i : ι))

/-- Restrict a point of a coordinate face to the coordinates that support it. -/
noncomputable def stdSimplexFaceRestrict {ι : Type u} [Fintype ι]
    [DecidableEq ι] (J : Finset ι) :
    stdSimplexFace J → stdSimplex ℝ {i // i ∈ J} := by
  intro x
  refine ⟨fun i => (x : stdSimplex ℝ ι) (i : ι), ?_, ?_⟩
  · intro i
    exact stdSimplex.zero_le (x : stdSimplex ℝ ι) (i : ι)
  · calc
      (∑ i : {i // i ∈ J}, (x : stdSimplex ℝ ι) (i : ι))
          = ∑ i ∈ J, (x : stdSimplex ℝ ι) i := by
            simpa using
              (Finset.sum_finset_coe (fun i => (x : stdSimplex ℝ ι) i) J)
      _ = ∑ i, (x : stdSimplex ℝ ι) i := by
        exact Finset.sum_subset (Finset.subset_univ J) fun i _hi hiJ =>
          (mem_stdSimplexFace_iff_eq_zero_of_not_mem.mp x.2) i hiJ
      _ = 1 := stdSimplex.sum_eq_one (x : stdSimplex ℝ ι)

@[simp] theorem stdSimplexFaceRestrict_apply {ι : Type u}
    [Fintype ι] [DecidableEq ι] (J : Finset ι)
    (x : stdSimplexFace J) (i : {i // i ∈ J}) :
    stdSimplexFaceRestrict J x i = (x : stdSimplex ℝ ι) (i : ι) :=
  rfl

theorem continuous_stdSimplexFaceRestrict {ι : Type u}
    [Fintype ι] [DecidableEq ι] (J : Finset ι) :
    Continuous (stdSimplexFaceRestrict J) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_pi fun i =>
    (continuous_apply (i : ι)).comp (continuous_subtype_val.comp continuous_subtype_val)

/--
A coordinate face of the standard simplex is homeomorphic to the standard
simplex on its supporting index subtype.
-/
noncomputable def stdSimplexFaceHomeomorph {ι : Type u}
    [Fintype ι] [DecidableEq ι] (J : Finset ι) :
    stdSimplex ℝ {i // i ∈ J} ≃ₜ stdSimplexFace J where
  toFun x := ⟨stdSimplexFaceMap J x, stdSimplexFaceMap_mem J x⟩
  invFun x := stdSimplexFaceRestrict J x
  left_inv x := by
    ext i
    exact stdSimplexFaceMap_apply_of_mem J x i.2
  right_inv x := by
    apply Subtype.ext
    ext i
    by_cases hi : i ∈ J
    · exact stdSimplexFaceMap_apply_of_mem J (stdSimplexFaceRestrict J x) hi
    · have hxi : (x : stdSimplex ℝ ι) i = 0 :=
        (mem_stdSimplexFace_iff_eq_zero_of_not_mem.mp x.2) i hi
      calc
        stdSimplexFaceMap J (stdSimplexFaceRestrict J x) i = 0 :=
          stdSimplexFaceMap_apply_of_not_mem J (stdSimplexFaceRestrict J x) hi
        _ = (x : stdSimplex ℝ ι) i := hxi.symm
  continuous_toFun := by
    exact (continuous_stdSimplexFaceMap J).subtype_mk (stdSimplexFaceMap_mem J)
  continuous_invFun := continuous_stdSimplexFaceRestrict J

/--
The finite-dimensional KKM covering condition on the standard simplex.

For every nonempty coordinate face indexed by `J`, the face is covered by
the corresponding subfamily `(C i)_{i ∈ J}`.
-/
def StdSimplexKKMCondition {ι : Type u} [Fintype ι]
    (C : ι → Set (stdSimplex ℝ ι)) : Prop :=
  ∀ J : Finset ι, J.Nonempty →
    ∀ x : stdSimplex ℝ ι, x ∈ stdSimplexFace J → ∃ i ∈ J, x ∈ C i

theorem StdSimplexKKMCondition.mono {ι : Type u} [Fintype ι]
    {C D : ι → Set (stdSimplex ℝ ι)}
    (hC : StdSimplexKKMCondition C) (hCD : ∀ i, C i ⊆ D i) :
    StdSimplexKKMCondition D := by
  intro J hJ x hxFace
  rcases hC J hJ x hxFace with ⟨i, hiJ, hxi⟩
  exact ⟨i, hiJ, hCD i hxi⟩

theorem StdSimplexKKMCondition.exists_mem {ι : Type u} [Fintype ι] [Nonempty ι]
    {C : ι → Set (stdSimplex ℝ ι)} (hC : StdSimplexKKMCondition C)
    (x : stdSimplex ℝ ι) : ∃ i, x ∈ C i := by
  classical
  rcases hC Finset.univ
      ⟨Classical.arbitrary ι, Finset.mem_univ (Classical.arbitrary ι)⟩
      x (by simp) with
    ⟨i, _hi, hxi⟩
  exact ⟨i, hxi⟩

theorem StdSimplexKKMCondition.vertex_mem {ι : Type u}
    [Fintype ι] [DecidableEq ι] {C : ι → Set (stdSimplex ℝ ι)}
    (hC : StdSimplexKKMCondition C) (i : ι) :
    stdSimplex.vertex (S := ℝ) i ∈ C i := by
  have hface :
      stdSimplex.vertex (S := ℝ) i ∈ stdSimplexFace ({i} : Finset ι) :=
    vertex_mem_stdSimplexFace (by simp)
  rcases hC ({i} : Finset ι) (by simp) (stdSimplex.vertex (S := ℝ) i) hface with
    ⟨j, hj, hxj⟩
  have hji : j = i := by
    simpa using hj
  simpa [hji] using hxj

theorem StdSimplexKKMCondition.restrict_face {ι : Type u}
    [Fintype ι] [DecidableEq ι] {C : ι → Set (stdSimplex ℝ ι)}
    (hC : StdSimplexKKMCondition C) (J : Finset ι) :
    StdSimplexKKMCondition (fun i : {i // i ∈ J} =>
      (stdSimplexFaceMap J) ⁻¹' C (i : ι)) := by
  intro L hL x hxFace
  let emb : {i // i ∈ J} ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  let K : Finset ι := L.map emb
  have hKne : K.Nonempty := by
    rcases hL with ⟨i, hiL⟩
    exact ⟨(i : ι), Finset.mem_map.mpr ⟨i, hiL, rfl⟩⟩
  have hxAmbientFace : stdSimplexFaceMap J x ∈ stdSimplexFace K := by
    rw [mem_stdSimplexFace_iff_eq_zero_of_not_mem]
    intro i hiK
    by_cases hiJ : i ∈ J
    · rw [stdSimplexFaceMap_apply_of_mem J x hiJ]
      by_contra hxi
      have hiL : (⟨i, hiJ⟩ : {i // i ∈ J}) ∈ L := hxFace ⟨i, hiJ⟩ hxi
      exact hiK (Finset.mem_map.mpr ⟨⟨i, hiJ⟩, hiL, rfl⟩)
    · exact stdSimplexFaceMap_apply_of_not_mem J x hiJ
  rcases hC K hKne (stdSimplexFaceMap J x) hxAmbientFace with ⟨i, hiK, hiC⟩
  rcases Finset.mem_map.mp hiK with ⟨j, hjL, hji⟩
  refine ⟨j, hjL, ?_⟩
  change stdSimplexFaceMap J x ∈ C (j : ι)
  simpa [← hji] using hiC

theorem isClosed_stdSimplexFaceMap_preimage {ι : Type u}
    [Fintype ι] [DecidableEq ι] {C : ι → Set (stdSimplex ℝ ι)}
    (hclosed : ∀ i, IsClosed (C i)) (J : Finset ι) :
    ∀ i : {i // i ∈ J}, IsClosed ((stdSimplexFaceMap J) ⁻¹' C (i : ι)) := by
  intro i
  exact (hclosed (i : ι)).preimage (continuous_stdSimplexFaceMap J)

/--
The KKM intersection property for closed covers of the standard simplex.

This is the reusable target for the later Sperner/KKM development: once the
property is proved for finite index types, Brouwer follows below.
-/
def StdSimplexKKMProperty (ι : Type u) [Fintype ι] : Prop :=
  ∀ C : ι → Set (stdSimplex ℝ ι),
    (∀ i, IsClosed (C i)) →
      StdSimplexKKMCondition C → ∃ x : stdSimplex ℝ ι, ∀ i, x ∈ C i

theorem closed_iInter_nonempty_of_finiteIntersections
    [TopologicalSpace X] [CompactSpace X] {α : Type w} {C : α → Set X}
    (hclosed : ∀ i, IsClosed (C i))
    (hfinite : ∀ s : Finset α, (⋂ i ∈ s, C i).Nonempty) :
    ∃ x : X, ∀ i, x ∈ C i := by
  rcases CompactSpace.iInter_nonempty hclosed hfinite with ⟨x, hx⟩
  exact ⟨x, fun i => (Set.mem_iInter.mp hx) i⟩

theorem stdSimplex_closed_iInter_nonempty_of_finiteIntersections
    {ι : Type u} [Fintype ι] {α : Type w}
    {C : α → Set (stdSimplex ℝ ι)}
    (hclosed : ∀ i, IsClosed (C i))
    (hfinite : ∀ s : Finset α, (⋂ i ∈ s, C i).Nonempty) :
    ∃ x : stdSimplex ℝ ι, ∀ i, x ∈ C i :=
  closed_iInter_nonempty_of_finiteIntersections hclosed hfinite

theorem stdSimplexKKMProperty_subsingleton
    {ι : Type u} [Fintype ι] [Nonempty ι] [Subsingleton ι] :
    StdSimplexKKMProperty ι := by
  classical
  intro C _hclosed hcond
  let i : ι := Classical.arbitrary ι
  refine ⟨stdSimplex.vertex (S := ℝ) i, ?_⟩
  intro j
  have hji : j = i := Subsingleton.elim j i
  simpa [hji] using hcond.vertex_mem i

theorem StdSimplexKKMProperty.exists_mem_face_iInter {ι : Type u}
    [Fintype ι] [DecidableEq ι] {C : ι → Set (stdSimplex ℝ ι)}
    {J : Finset ι} (hKKM : StdSimplexKKMProperty {i // i ∈ J})
    (hclosed : ∀ i, IsClosed (C i)) (hcond : StdSimplexKKMCondition C) :
    ∃ x : stdSimplex ℝ ι, x ∈ stdSimplexFace J ∧ ∀ i, i ∈ J → x ∈ C i := by
  rcases hKKM
      (fun i : {i // i ∈ J} => (stdSimplexFaceMap J) ⁻¹' C (i : ι))
      (isClosed_stdSimplexFaceMap_preimage hclosed J)
      (hcond.restrict_face J) with
    ⟨x, hx⟩
  refine ⟨stdSimplexFaceMap J x, stdSimplexFaceMap_mem J x, ?_⟩
  intro i hiJ
  exact hx ⟨i, hiJ⟩

theorem nonempty_inter_of_isClosed_union_eq_univ_of_nonempty
    [TopologicalSpace X] [PreconnectedSpace X] {A B : Set X}
    (hAclosed : IsClosed A) (hBclosed : IsClosed B)
    (hcover : A ∪ B = Set.univ) (hAne : A.Nonempty) (hBne : B.Nonempty) :
    (A ∩ B).Nonempty := by
  by_contra hAB
  have hABempty : A ∩ B = ∅ := Set.not_nonempty_iff_eq_empty.mp hAB
  have hAeq : A = Bᶜ := by
    ext x
    constructor
    · intro hxA hxB
      have hxAB : x ∈ A ∩ B := ⟨hxA, hxB⟩
      rw [hABempty] at hxAB
      exact hxAB
    · intro hxB
      have hxcover : x ∈ A ∪ B := by
        rw [hcover]
        trivial
      rcases hxcover with hxA | hxB'
      · exact hxA
      · exact (hxB hxB').elim
  have hAclopen : IsClopen A := by
    refine ⟨hAclosed, ?_⟩
    rw [hAeq]
    exact hBclosed.isOpen_compl
  have hAuniv : A = Set.univ := hAclopen.eq_univ hAne
  rcases hBne with ⟨x, hxB⟩
  have hxA : x ∈ A := by
    rw [hAuniv]
    trivial
  have hxAB : x ∈ A ∩ B := ⟨hxA, hxB⟩
  rw [hABempty] at hxAB
  exact hxAB

theorem stdSimplexKKMProperty_fin_two : StdSimplexKKMProperty (Fin 2) := by
  intro C hclosed hcond
  have hcover : C 0 ∪ C 1 = Set.univ := by
    ext x
    constructor
    · intro _hx
      trivial
    · intro _hx
      rcases hcond.exists_mem x with ⟨i, hxi⟩
      fin_cases i
      · exact Or.inl hxi
      · exact Or.inr hxi
  have hC0ne : (C 0).Nonempty :=
    ⟨stdSimplex.vertex (S := ℝ) (0 : Fin 2), hcond.vertex_mem 0⟩
  have hC1ne : (C 1).Nonempty :=
    ⟨stdSimplex.vertex (S := ℝ) (1 : Fin 2), hcond.vertex_mem 1⟩
  rcases nonempty_inter_of_isClosed_union_eq_univ_of_nonempty
      (hclosed 0) (hclosed 1) hcover hC0ne hC1ne with
    ⟨x, hx0, hx1⟩
  refine ⟨x, ?_⟩
  intro i
  fin_cases i
  · exact hx0
  · exact hx1

/--
The KKM intersection property implies Brouwer's fixed-point property on the
standard simplex.

Given a continuous self-map `f`, the usual KKM cover is
`C i = {x | f x i ≤ x i}`. The KKM point belongs to every `C i`, so `f x ≤ x`
coordinatewise. Since both `x` and `f x` have coordinate sum `1`, all
coordinates are equal.
-/
theorem brouwerFixedPointProperty_stdSimplex_of_kkm
    {ι : Type u} [Fintype ι] (hKKM : StdSimplexKKMProperty ι) :
    BrouwerFixedPointProperty (stdSimplex ℝ ι) := by
  intro f hfMap hfCont
  let fS : stdSimplex ℝ ι → stdSimplex ℝ ι := fun x => ⟨f x, hfMap x.2⟩
  have hfSCont : Continuous fS := by
    have hfRestrict : Continuous ((stdSimplex ℝ ι).restrict f) := hfCont.restrict
    exact hfRestrict.codRestrict (fun x => hfMap x.2)
  let C : ι → Set (stdSimplex ℝ ι) := fun i => {x | fS x i ≤ x i}
  have hclosed : ∀ i, IsClosed (C i) := by
    intro i
    have hleft : Continuous fun x : stdSimplex ℝ ι => fS x i :=
      (continuous_apply i).comp (continuous_subtype_val.comp hfSCont)
    have hright : Continuous fun x : stdSimplex ℝ ι => x i :=
      (continuous_apply i).comp continuous_subtype_val
    simpa [C] using isClosed_le hleft hright
  have hcond : StdSimplexKKMCondition C := by
    intro J hJ x hxFace
    by_contra hnone
    push_neg at hnone
    have hltJ : ∀ i, i ∈ J → x i < fS x i := by
      intro i hi
      have hnotle : ¬ fS x i ≤ x i := by
        simpa [C] using hnone i hi
      exact lt_of_not_ge hnotle
    have hleAll : ∀ i, x i ≤ fS x i := by
      intro i
      by_cases hi : i ∈ J
      · exact (hltJ i hi).le
      · have hx0 : x i = 0 := by
          by_contra hxne
          exact hi (hxFace i hxne)
        have hfnonneg : 0 ≤ fS x i := stdSimplex.zero_le (fS x) i
        rw [hx0]
        exact hfnonneg
    have hsum_lt : (∑ i, x i) < ∑ i, fS x i := by
      refine Finset.sum_lt_sum (s := Finset.univ) ?_ ?_
      · intro i _hi
        exact hleAll i
      · rcases hJ with ⟨i, hi⟩
        exact ⟨i, Finset.mem_univ i, hltJ i hi⟩
    have hltOne : (1 : ℝ) < 1 := by
      calc
        (1 : ℝ) = ∑ i, x i := (stdSimplex.sum_eq_one x).symm
        _ < ∑ i, fS x i := hsum_lt
        _ = 1 := stdSimplex.sum_eq_one (fS x)
    exact (lt_irrefl (1 : ℝ)) hltOne
  rcases hKKM C hclosed hcond with ⟨x, hxC⟩
  refine ⟨x, x.2, ?_⟩
  have hle : ∀ i, fS x i ≤ x i := by
    intro i
    simpa [C] using hxC i
  have hcoord : ∀ i, fS x i = x i := by
    intro i
    refine le_antisymm (hle i) ?_
    by_contra hnot
    have hlt : fS x i < x i := lt_of_not_ge hnot
    have hsum_lt : (∑ j, fS x j) < ∑ j, x j := by
      refine Finset.sum_lt_sum (s := Finset.univ) ?_ ?_
      · intro j _hj
        exact hle j
      · exact ⟨i, Finset.mem_univ i, hlt⟩
    have hltOne : (1 : ℝ) < 1 := by
      calc
        (1 : ℝ) = ∑ j, fS x j := (stdSimplex.sum_eq_one (fS x)).symm
        _ < ∑ j, x j := hsum_lt
        _ = 1 := stdSimplex.sum_eq_one x
    exact (lt_irrefl (1 : ℝ)) hltOne
  funext i
  simpa [fS] using hcoord i

/--
The standard closed-graph form of Kakutani's fixed-point hypotheses on a
carrier `K`.

For applications, `F` is usually a best-response or excess-demand
correspondence. The fields are intentionally factored so later game-theory
theorems can assemble them by reusable lemmas: product preservation,
Berge maximum theorem, and convexity of argmax values.
-/
structure KakutaniPremises [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]
    (K : Set X) (F : Correspondence X X) : Prop where
  compact_domain : IsCompact K
  convex_domain : Convex ℝ K
  nonempty_domain : K.Nonempty
  mapsTo_domain : MapsToOn F K K
  nonempty_values : NonemptyValuedOn F K
  compact_values : CompactValuedOn F K
  convex_values : ConvexValuedOn (𝕜 := ℝ) F K
  closed_graph : ClosedGraphOn F K

/--
Kakutani hypotheses are preserved by continuous linear changes of coordinates.

This is the reusable transport lemma needed to prove fixed-point theorems on a
standard carrier and move them to linearly equivalent strategy spaces.
-/
theorem KakutaniPremises.image_continuousLinearEquiv
    [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommMonoid X] [AddCommMonoid Y] [Module ℝ X] [Module ℝ Y]
    {K : Set X} {F : Correspondence X X}
    (hF : KakutaniPremises K F) (e : X ≃L[ℝ] Y) :
    KakutaniPremises (e '' K) (equivConjugate e.toLinearEquiv.toEquiv F) := by
  let E : X ≃ Y := e.toLinearEquiv.toEquiv
  change KakutaniPremises (E '' K) (equivConjugate E F)
  refine
    { compact_domain := by
        simpa [E] using hF.compact_domain.image e.continuous
      convex_domain := by
        simpa [E] using hF.convex_domain.linear_image e.toLinearEquiv.toLinearMap
      nonempty_domain := by
        rcases hF.nonempty_domain with ⟨x, hxK⟩
        exact ⟨E x, ⟨x, hxK, rfl⟩⟩
      mapsTo_domain := by
        intro y hyK y' hyF
        have hyK' : E.symm y ∈ K := by
          rcases hyK with ⟨x, hxK, rfl⟩
          simpa [E] using hxK
        have hyF' : E.symm y' ∈ F (E.symm y) := by
          simpa using (mem_equivConjugate_iff.mp hyF)
        exact ⟨E.symm y', hF.mapsTo_domain hyK' hyF', by simp⟩
      nonempty_values := by
        intro y hyK
        have hyK' : E.symm y ∈ K := by
          rcases hyK with ⟨x, hxK, rfl⟩
          simpa [E] using hxK
        rcases hF.nonempty_values hyK' with ⟨x, hxF⟩
        exact ⟨E x, ⟨x, hxF, rfl⟩⟩
      compact_values := by
        intro y hyK
        have hyK' : E.symm y ∈ K := by
          rcases hyK with ⟨x, hxK, rfl⟩
          simpa [E] using hxK
        simpa [E] using (hF.compact_values hyK').image e.continuous
      convex_values := by
        intro y hyK
        have hyK' : E.symm y ∈ K := by
          rcases hyK with ⟨x, hxK, rfl⟩
          simpa [E] using hxK
        simpa [E] using
          (hF.convex_values hyK').linear_image e.toLinearEquiv.toLinearMap
      closed_graph := by
        have hGraph :
            graphOn (equivConjugate E F) (E '' K) =
              (E.prodCongr E) '' graphOn F K :=
          graphOn_equivConjugate F K
        rw [ClosedGraphOn, hGraph]
        have hClosedImage : IsClosed ((e.prodCongr e) '' graphOn F K) :=
          (e.prodCongr e).toHomeomorph.isClosed_image.mpr hF.closed_graph
        simpa [E] using hClosedImage }

/--
Kakutani hypotheses are preserved by continuous affine changes of coordinates.

This is the affine analogue of `KakutaniPremises.image_continuousLinearEquiv`.
It is the version needed for translated boxes, affine simplexes, and strategy
sets whose natural coordinates do not put the origin in a distinguished place.
-/
theorem KakutaniPremises.image_continuousAffineEquiv
    [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommGroup X] [AddCommGroup Y] [Module ℝ X] [Module ℝ Y]
    {K : Set X} {F : Correspondence X X}
    (hF : KakutaniPremises K F) (e : X ≃ᴬ[ℝ] Y) :
    KakutaniPremises (e '' K) (equivConjugate e.toEquiv F) := by
  let E : X ≃ Y := e.toEquiv
  change KakutaniPremises (E '' K) (equivConjugate E F)
  refine
    { compact_domain := by
        simpa [E] using hF.compact_domain.image e.continuous
      convex_domain := by
        simpa [E] using hF.convex_domain.affine_image e.toAffineEquiv.toAffineMap
      nonempty_domain := by
        rcases hF.nonempty_domain with ⟨x, hxK⟩
        exact ⟨E x, ⟨x, hxK, rfl⟩⟩
      mapsTo_domain := by
        intro y hyK y' hyF
        have hyK' : E.symm y ∈ K := by
          rcases hyK with ⟨x, hxK, rfl⟩
          simpa [E] using hxK
        have hyF' : E.symm y' ∈ F (E.symm y) := by
          simpa using (mem_equivConjugate_iff.mp hyF)
        exact ⟨E.symm y', hF.mapsTo_domain hyK' hyF', by simp⟩
      nonempty_values := by
        intro y hyK
        have hyK' : E.symm y ∈ K := by
          rcases hyK with ⟨x, hxK, rfl⟩
          simpa [E] using hxK
        rcases hF.nonempty_values hyK' with ⟨x, hxF⟩
        exact ⟨E x, ⟨x, hxF, rfl⟩⟩
      compact_values := by
        intro y hyK
        have hyK' : E.symm y ∈ K := by
          rcases hyK with ⟨x, hxK, rfl⟩
          simpa [E] using hxK
        simpa [E] using (hF.compact_values hyK').image e.continuous
      convex_values := by
        intro y hyK
        have hyK' : E.symm y ∈ K := by
          rcases hyK with ⟨x, hxK, rfl⟩
          simpa [E] using hxK
        simpa [E] using
          (hF.convex_values hyK').affine_image e.toAffineEquiv.toAffineMap
      closed_graph := by
        have hGraph :
            graphOn (equivConjugate E F) (E '' K) =
              (E.prodCongr E) '' graphOn F K :=
          graphOn_equivConjugate F K
        rw [ClosedGraphOn, hGraph]
        have hClosedImage : IsClosed ((e.prodCongr e) '' graphOn F K) :=
          (e.prodCongr e).toHomeomorph.isClosed_image.mpr hF.closed_graph
        simpa [E] using hClosedImage }

/-- Continuous self-maps of compact Hausdorff carriers are single-valued
instances of the Kakutani hypotheses. -/
theorem KakutaniPremises.ofFun
    [TopologicalSpace X] [T2Space X] [AddCommMonoid X] [Module ℝ X]
    {K : Set X} {f : X → X}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (hfMap : Set.MapsTo f K K) (hfCont : ContinuousOn f K) :
    KakutaniPremises K (ofFun f) where
  compact_domain := hKcompact
  convex_domain := hKconvex
  nonempty_domain := hKne
  mapsTo_domain := mapsToOn_ofFun_iff.mpr hfMap
  nonempty_values := nonemptyValuedOn_ofFun f
  compact_values := compactValuedOn_ofFun f
  convex_values := convexValuedOn_ofFun f
  closed_graph := closedGraphOn_ofFun hKcompact.isClosed hfCont

/--
Argmax correspondences satisfy the Kakutani hypotheses under the standard
Berge maximum-theorem assumptions plus quasiconcavity.

This is the reusable bridge from payoff maximization problems to fixed-point
theorems: once a model constructs `F` and verifies these assumptions, the
argmax correspondence is ready for a Kakutani-style existence theorem.
-/
theorem KakutaniPremises.of_argmax
    [TopologicalSpace X] [T2Space X] [AddCommMonoid X] [Module ℝ X]
    {K : Set X} {u : X → X → ℝ} {F : Correspondence X X}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (hFmap : MapsToOn F K K)
    (hFnonempty : NonemptyValuedOn F K)
    (hFcompact : CompactValuedOn F K)
    (hFclosed : ClosedGraphOn F K)
    (hFlhc : LowerHemicontinuousOn F K)
    (hu : Continuous fun p : X × X => u p.1 p.2)
    (huQuasi : ∀ ⦃x⦄, x ∈ K → QuasiconcaveOn ℝ (F x) (u x)) :
    KakutaniPremises K (argmax u F) := by
  have huSections : ∀ ⦃x⦄, x ∈ K → ContinuousOn (u x) (F x) := by
    intro x hxK
    have hxcont : Continuous fun y : X => u x y :=
      hu.comp (continuous_const.prodMk continuous_id)
    exact hxcont.continuousOn
  have hArgmaxNonempty : NonemptyValuedOn (argmax u F) K :=
    argmax_nonemptyValuedOn_of_compact hFcompact hFnonempty huSections
  exact
    { compact_domain := hKcompact
      convex_domain := hKconvex
      nonempty_domain := hKne
      mapsTo_domain := argmax_mapsToOn hFmap
      nonempty_values := hArgmaxNonempty
      compact_values :=
        argmax_compactValuedOn_of_compact hFcompact hFnonempty huSections
      convex_values :=
        argmax_convexValuedOn_of_quasiconcave hArgmaxNonempty huQuasi
      closed_graph :=
        argmax_closedGraphOn hKcompact.isClosed hFclosed hFlhc hu }

/-- A carrier satisfies Kakutani when every correspondence satisfying the
Kakutani hypotheses has a fixed point on that carrier. -/
def KakutaniFixedPointProperty [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]
    (K : Set X) : Prop :=
  ∀ F : Correspondence X X, KakutaniPremises K F → HasFixedPointOn F K

theorem KakutaniFixedPointProperty.image_continuousAffineEquiv
    [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommGroup X] [AddCommGroup Y] [Module ℝ X] [Module ℝ Y]
    {K : Set X} (hK : KakutaniFixedPointProperty K) (e : X ≃ᴬ[ℝ] Y) :
    KakutaniFixedPointProperty (e '' K) := by
  intro G hG
  let E : X ≃ Y := e.toEquiv
  let Gpull : Correspondence X X := equivConjugate E.symm G
  have hPull : KakutaniPremises K Gpull := by
    have hImage := hG.image_continuousAffineEquiv e.symm
    simpa [Gpull, E] using hImage
  rcases hK Gpull hPull with ⟨x, hxK, hxGpull⟩
  refine ⟨E x, ⟨x, hxK, rfl⟩, ?_⟩
  have hxG : E.symm (E x) ∈ Gpull (E.symm (E x)) := by
    simpa [Gpull, E] using hxGpull
  have hmem : E x ∈ equivConjugate E Gpull (E x) := by
    simpa using (mem_equivConjugate_iff.mpr hxG)
  simpa [Gpull, E, equivConjugate] using hmem

theorem kakutaniFixedPointProperty_image_continuousAffineEquiv_iff
    [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommGroup X] [AddCommGroup Y] [Module ℝ X] [Module ℝ Y]
    (e : X ≃ᴬ[ℝ] Y) (K : Set X) :
    KakutaniFixedPointProperty (e '' K) ↔ KakutaniFixedPointProperty K := by
  constructor
  · intro hK
    simpa using hK.image_continuousAffineEquiv e.symm
  · intro hK
    exact hK.image_continuousAffineEquiv e

theorem KakutaniFixedPointProperty.hasFixedPointOn
    [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]
    {K : Set X} (hK : KakutaniFixedPointProperty K)
    {F : Correspondence X X} (hF : KakutaniPremises K F) :
    HasFixedPointOn F K :=
  hK F hF

theorem KakutaniFixedPointProperty.nonempty_fixedPointsOn
    [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]
    {K : Set X} (hK : KakutaniFixedPointProperty K)
    {F : Correspondence X X} (hF : KakutaniPremises K F) :
    (fixedPointsOn F K).Nonempty := by
  rcases hK.hasFixedPointOn hF with ⟨x, hx⟩
  exact ⟨x, hx⟩

/-- Kakutani's fixed-point property implies Brouwer's fixed-point property
on compact convex Hausdorff carriers by viewing functions as singleton-valued
correspondences. -/
theorem KakutaniFixedPointProperty.brouwerFixedPointProperty
    [TopologicalSpace X] [T2Space X] [AddCommMonoid X] [Module ℝ X]
    {K : Set X} (hK : KakutaniFixedPointProperty K)
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty) :
    BrouwerFixedPointProperty K := by
  intro f hfMap hfCont
  have hPremises : KakutaniPremises K (ofFun f) :=
    KakutaniPremises.ofFun hKcompact hKconvex hKne hfMap hfCont
  rcases hK.hasFixedPointOn hPremises with ⟨x, hxK, hxF⟩
  rw [mem_ofFun_iff] at hxF
  exact ⟨x, hxK, hxF.symm⟩

theorem KakutaniPremises.isClosed_fixedPointsOn
    [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]
    {K : Set X} {F : Correspondence X X} (hF : KakutaniPremises K F) :
    IsClosed (fixedPointsOn F K) :=
  hF.closed_graph.isClosed_fixedPointsOn

theorem KakutaniPremises.isCompact_fixedPointsOn
    [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]
    {K : Set X} {F : Correspondence X X} (hF : KakutaniPremises K F) :
    IsCompact (fixedPointsOn F K) :=
  hF.closed_graph.isCompact_fixedPointsOn hF.compact_domain

end FixedPoints

end Correspondence

end EcoLean.GameTheory
