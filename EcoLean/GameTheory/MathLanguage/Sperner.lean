import Mathlib

/-!
# Abstract combinatorial Sperner theorem

This file follows the shape requested in leanprover-community/mathlib4 issue
[#25231](https://github.com/leanprover-community/mathlib4/issues/25231):
Sperner's lemma is isolated as a finite combinatorial parity theorem about
colourings of triangulations.  The geometric work needed to instantiate the
theorem is packaged as an explicit finite incidence certificate.

In particular, this file deliberately avoids bespoke concrete triangulation
machinery.  Such geometry belongs in a separate instantiation of the certificate
below.
-/

namespace EcoLean
namespace Sperner

open scoped BigOperators

universe u v w x

variable {ι : Type u} {V : Type v} {Cell : Type w} {Facet : Type x}

/-- The set of labels appearing on a finite vertex set. -/
def labelsOn [DecidableEq ι] (color : V → ι) (verts : Finset V) : Finset ι :=
  verts.image color

/-- A finite vertex set is fully labelled if every label appears on it. -/
def FullyLabeled [Fintype ι] [DecidableEq ι]
    (color : V → ι) (verts : Finset V) : Prop :=
  Finset.univ ⊆ labelsOn color verts

/-- A finite vertex set is almost fully labelled with one specified missing label. -/
def AlmostFullyLabeled [Fintype ι] [DecidableEq ι]
    (color : V → ι) (missing : ι) (verts : Finset V) : Prop :=
  ∀ i : ι, i ≠ missing → i ∈ labelsOn color verts

theorem mem_labelsOn_iff [DecidableEq ι]
    (color : V → ι) (verts : Finset V) (i : ι) :
    i ∈ labelsOn color verts ↔ ∃ v ∈ verts, color v = i := by
  simp [labelsOn]

theorem fullyLabeled_iff [Fintype ι] [DecidableEq ι]
    (color : V → ι) (verts : Finset V) :
    FullyLabeled color verts ↔ ∀ i : ι, i ∈ labelsOn color verts := by
  constructor
  · intro h i
    exact h (Finset.mem_univ i)
  · intro h i _hi
    exact h i

theorem almostFullyLabeled_iff [Fintype ι] [DecidableEq ι]
    (color : V → ι) (missing : ι) (verts : Finset V) :
    AlmostFullyLabeled color missing verts
      ↔ ∀ i : ι, i ≠ missing → i ∈ labelsOn color verts := by
  rfl

/--
A finite combinatorial triangulation certificate sufficient for the abstract
Sperner parity argument.

`Cell` is the finite type of top-dimensional cells and `Facet` is the finite
type of codimension-one facets.  The certificate records only the finite
incidence data and the boundary/interior incidence cardinalities needed for
double-counting.
-/
structure SpernerTriangulationCertificate
    (V Cell Facet : Type*) where
  [fintypeCell : Fintype Cell]
  [fintypeFacet : Fintype Facet]
  [decCell : DecidableEq Cell]
  [decFacet : DecidableEq Facet]
  verticesOfCell : Cell → Finset V
  verticesOfFacet : Facet → Finset V
  facetsOfCell : Cell → Finset Facet
  incidentCells : Facet → Finset Cell
  incident_iff :
    ∀ c f, c ∈ incidentCells f ↔ f ∈ facetsOfCell c
  facet_vertices_subset :
    ∀ c f, f ∈ facetsOfCell c →
      verticesOfFacet f ⊆ verticesOfCell c
  boundaryFacet : Facet → Prop
  boundary_incident_card :
    ∀ f, boundaryFacet f → (incidentCells f).card = 1
  interior_incident_card :
    ∀ f, ¬ boundaryFacet f → (incidentCells f).card = 2

namespace SpernerTriangulationCertificate

attribute [instance] fintypeCell fintypeFacet decCell decFacet

variable (T : SpernerTriangulationCertificate V Cell Facet)

local instance : Fintype Cell := T.fintypeCell
local instance : Fintype Facet := T.fintypeFacet
local instance : DecidableEq Cell := T.decCell
local instance : DecidableEq Facet := T.decFacet

/-- A facet relevant to a missing label is an almost fully labelled facet. -/
def relevantFacet [Fintype ι] [DecidableEq ι]
    (color : V → ι) (missing : ι) (f : Facet) : Prop :=
  AlmostFullyLabeled color missing (T.verticesOfFacet f)

/-- All relevant facets. -/
noncomputable def relevantFacets [Fintype ι] [DecidableEq ι]
    (color : V → ι) (missing : ι) : Finset Facet := by
  classical
  letI := T.fintypeFacet
  exact Finset.univ.filter fun f =>
    T.relevantFacet color missing f

/-- Boundary facets that are relevant to a missing label. -/
noncomputable def boundaryRelevantFacets [Fintype ι] [DecidableEq ι]
    (color : V → ι) (missing : ι) : Finset Facet := by
  classical
  letI := T.fintypeFacet
  exact Finset.univ.filter fun f =>
    T.boundaryFacet f ∧ T.relevantFacet color missing f

/-- Relevant facets incident to a fixed top cell. -/
noncomputable def relevantFacetsOfCell [Fintype ι] [DecidableEq ι]
    (color : V → ι) (missing : ι) (c : Cell) : Finset Facet := by
  classical
  exact (T.facetsOfCell c).filter fun f =>
    T.relevantFacet color missing f

theorem mem_relevantFacets_iff [Fintype ι] [DecidableEq ι]
    (color : V → ι) (missing : ι) (f : Facet) :
    f ∈ T.relevantFacets color missing ↔
      T.relevantFacet color missing f := by
  classical
  simp [relevantFacets]

theorem mem_boundaryRelevantFacets_iff [Fintype ι] [DecidableEq ι]
    (color : V → ι) (missing : ι) (f : Facet) :
    f ∈ T.boundaryRelevantFacets color missing ↔
      T.boundaryFacet f ∧ T.relevantFacet color missing f := by
  classical
  simp [boundaryRelevantFacets]

theorem mem_relevantFacetsOfCell_iff [Fintype ι] [DecidableEq ι]
    (color : V → ι) (missing : ι) (c : Cell) (f : Facet) :
    f ∈ T.relevantFacetsOfCell color missing c ↔
      f ∈ T.facetsOfCell c ∧ T.relevantFacet color missing f := by
  classical
  simp [relevantFacetsOfCell]

/--
Relevant facet-cell incidences, represented as ordinary pairs.

This is definitionally a sigma-finite set indexed by relevant facets; the
membership lemma below exposes the requested product-pair view.
-/
noncomputable def relevantIncidences [Fintype ι] [DecidableEq ι]
    (color : V → ι) (missing : ι) : Finset (Facet × Cell) := by
  classical
  exact
    ((T.relevantFacets color missing).sigma fun f => T.incidentCells f).map
      (Equiv.sigmaEquivProd Facet Cell).toEmbedding

private noncomputable def relevantIncidencesByCell [Fintype ι] [DecidableEq ι]
    (color : V → ι) (missing : ι) : Finset (Facet × Cell) := by
  classical
  letI := T.fintypeCell
  exact
    ((Finset.univ : Finset Cell).sigma
      fun c => T.relevantFacetsOfCell color missing c).map
        ((Equiv.sigmaEquivProd Cell Facet).trans
          (Equiv.prodComm Cell Facet)).toEmbedding

theorem mem_relevantIncidences_iff [Fintype ι] [DecidableEq ι]
    (color : V → ι) (missing : ι) (f : Facet) (c : Cell) :
    (f, c) ∈ T.relevantIncidences color missing ↔
      T.relevantFacet color missing f ∧ c ∈ T.incidentCells f := by
  classical
  simp [relevantIncidences, mem_relevantFacets_iff]

private theorem mem_relevantIncidencesByCell_iff [Fintype ι] [DecidableEq ι]
    (color : V → ι) (missing : ι) (f : Facet) (c : Cell) :
    (f, c) ∈ T.relevantIncidencesByCell color missing ↔
      T.relevantFacet color missing f ∧ f ∈ T.facetsOfCell c := by
  classical
  letI := T.fintypeCell
  simp [relevantIncidencesByCell, relevantFacetsOfCell, and_comm, and_assoc]

theorem relevantIncidences_card_eq_sum_incidentCells
    [Fintype ι] [DecidableEq ι]
    (color : V → ι) (missing : ι) :
    (T.relevantIncidences color missing).card
      =
    ∑ f ∈ T.relevantFacets color missing,
      (T.incidentCells f).card := by
  classical
  let S := (T.relevantFacets color missing).sigma fun f => T.incidentCells f
  calc
    (T.relevantIncidences color missing).card = S.card := by
      simp [relevantIncidences, S]
    _ = ∑ x ∈ S, (1 : ℕ) := by
      rw [Finset.card_eq_sum_ones]
    _ = ∑ f ∈ T.relevantFacets color missing,
          ∑ c ∈ T.incidentCells f, (1 : ℕ) := by
      rw [Finset.sum_sigma]
    _ = ∑ f ∈ T.relevantFacets color missing,
          (T.incidentCells f).card := by
      apply Finset.sum_congr rfl
      intro f _hf
      rw [Finset.card_eq_sum_ones]

private theorem relevantIncidencesByCell_card_eq_sum_relevantFacetsOfCell
    [Fintype ι] [DecidableEq ι]
    (color : V → ι) (missing : ι) :
    (T.relevantIncidencesByCell color missing).card
      =
    ∑ c ∈ (@Finset.univ Cell T.fintypeCell),
      (T.relevantFacetsOfCell color missing c).card := by
  classical
  letI := T.fintypeCell
  let S := (Finset.univ : Finset Cell).sigma
    fun c => T.relevantFacetsOfCell color missing c
  calc
    (T.relevantIncidencesByCell color missing).card = S.card := by
      simp [relevantIncidencesByCell, S]
    _ = ∑ x ∈ S, (1 : ℕ) := by
      rw [Finset.card_eq_sum_ones]
    _ = ∑ c ∈ (Finset.univ : Finset Cell),
          ∑ f ∈ T.relevantFacetsOfCell color missing c, (1 : ℕ) := by
      rw [Finset.sum_sigma]
    _ = ∑ c ∈ (@Finset.univ Cell T.fintypeCell),
          (T.relevantFacetsOfCell color missing c).card := by
      apply Finset.sum_congr rfl
      intro c _hc
      rw [Finset.card_eq_sum_ones]

theorem relevantIncidences_card_eq_sum_relevantFacetsOfCell
    [Fintype ι] [DecidableEq ι]
    (color : V → ι) (missing : ι) :
    (T.relevantIncidences color missing).card
      =
    ∑ c ∈ (@Finset.univ Cell T.fintypeCell),
      (T.relevantFacetsOfCell color missing c).card := by
  classical
  letI := T.fintypeCell
  have hsame :
      T.relevantIncidences color missing =
        T.relevantIncidencesByCell color missing := by
    ext fc
    rcases fc with ⟨f, c⟩
    rw [T.mem_relevantIncidences_iff color missing f c,
      T.mem_relevantIncidencesByCell_iff color missing f c]
    exact and_congr_right fun _ => T.incident_iff c f
  rw [hsame, T.relevantIncidencesByCell_card_eq_sum_relevantFacetsOfCell]

theorem odd_relevantIncidences_iff_boundaryRelevant_odd
    [Fintype ι] [DecidableEq ι]
    (color : V → ι) (missing : ι) :
    Odd (T.relevantIncidences color missing).card
      ↔
    Odd (T.boundaryRelevantFacets color missing).card := by
  classical
  have hfilter :
      ((T.relevantFacets color missing).filter
        fun f => Odd (T.incidentCells f).card)
        =
      T.boundaryRelevantFacets color missing := by
    ext f
    by_cases hb : T.boundaryFacet f
    · have hodd : Odd (T.incidentCells f).card := by
        rw [T.boundary_incident_card f hb]
        norm_num
      simp [T.mem_relevantFacets_iff, T.mem_boundaryRelevantFacets_iff, hb,
        hodd]
    · have hnot_odd : ¬ Odd (T.incidentCells f).card := by
        rw [T.interior_incident_card f hb]
        norm_num
      simp [T.mem_relevantFacets_iff, T.mem_boundaryRelevantFacets_iff, hb,
        hnot_odd]
  rw [T.relevantIncidences_card_eq_sum_incidentCells color missing]
  rw [Finset.odd_sum_iff_odd_card_odd]
  simp [hfilter]

theorem exists_cell_odd_relevantFacetsOfCell_of_odd_boundary
    [Fintype ι] [DecidableEq ι]
    (color : V → ι) (missing : ι)
    (hodd : Odd (T.boundaryRelevantFacets color missing).card) :
    ∃ c : Cell,
      Odd (T.relevantFacetsOfCell color missing c).card := by
  classical
  letI := T.fintypeCell
  have hinc_odd : Odd (T.relevantIncidences color missing).card :=
    (T.odd_relevantIncidences_iff_boundaryRelevant_odd color missing).mpr hodd
  have hsum_odd :
      Odd (∑ c ∈ (@Finset.univ Cell T.fintypeCell),
        (T.relevantFacetsOfCell color missing c).card) := by
    rwa [← T.relevantIncidences_card_eq_sum_relevantFacetsOfCell color missing]
  have hodd_filter :
      Odd (((@Finset.univ Cell T.fintypeCell).filter fun c =>
        Odd (T.relevantFacetsOfCell color missing c).card).card) := by
    simpa using
      (Finset.odd_sum_iff_odd_card_odd
        (s := (@Finset.univ Cell T.fintypeCell))
        (f := fun c => (T.relevantFacetsOfCell color missing c).card)).mp
        hsum_odd
  have hnonempty :
      ((@Finset.univ Cell T.fintypeCell).filter fun c =>
        Odd (T.relevantFacetsOfCell color missing c).card).Nonempty := by
    rw [← Finset.card_pos]
    exact Nat.pos_of_ne_zero (by
      intro hzero
      rw [hzero] at hodd_filter
      norm_num at hodd_filter)
  rcases hnonempty with ⟨c, hc⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  exact ⟨c, hc⟩

/--
The abstract combinatorial Sperner theorem.

If the number of relevant boundary facets is odd, and if the local parity
criterion identifies cells with an odd number of relevant facets exactly as the
fully labelled cells, then some top cell is fully labelled.
-/
theorem exists_fully_labeled_of_boundary_odd
    [Fintype ι] [DecidableEq ι]
    (color : V → ι)
    (missing : ι)
    (boundary_odd :
      Odd (T.boundaryRelevantFacets color missing).card)
    (local_parity :
      ∀ c : Cell,
        Odd (T.relevantFacetsOfCell color missing c).card ↔
          FullyLabeled color (T.verticesOfCell c)) :
    ∃ c : Cell, FullyLabeled color (T.verticesOfCell c) := by
  classical
  rcases T.exists_cell_odd_relevantFacetsOfCell_of_odd_boundary
      color missing boundary_odd with ⟨c, hcodd⟩
  exact ⟨c, (local_parity c).mp hcodd⟩

/-- Alias for the abstract finite combinatorial Sperner theorem. -/
theorem abstract_sperner
    [Fintype ι] [DecidableEq ι]
    (color : V → ι)
    (missing : ι)
    (boundary_odd :
      Odd (T.boundaryRelevantFacets color missing).card)
    (local_parity :
      ∀ c : Cell,
        Odd (T.relevantFacetsOfCell color missing c).card ↔
          FullyLabeled color (T.verticesOfCell c)) :
    ∃ c : Cell, FullyLabeled color (T.verticesOfCell c) :=
  T.exists_fully_labeled_of_boundary_odd
    color missing boundary_odd local_parity

end SpernerTriangulationCertificate

/--
A bundled certificate for the abstract combinatorial Sperner theorem.

The two genuinely geometric/combinatorial inputs are explicit fields:
`boundary_odd` supplies the odd boundary count, and `local_parity` identifies
the cells with an odd number of relevant facets as exactly the fully labelled
cells.
-/
structure SpernerCertificate
    (ι V Cell Facet : Type*) [Fintype ι] [DecidableEq ι] where
  triangulation : SpernerTriangulationCertificate V Cell Facet
  color : V → ι
  missing : ι
  boundary_odd :
    Odd (triangulation.boundaryRelevantFacets color missing).card
  local_parity :
    ∀ c : Cell,
      Odd (triangulation.relevantFacetsOfCell color missing c).card ↔
        FullyLabeled color (triangulation.verticesOfCell c)

namespace SpernerCertificate

theorem exists_fully_labeled [Fintype ι] [DecidableEq ι]
    (C : SpernerCertificate ι V Cell Facet) :
    ∃ c : Cell,
      FullyLabeled C.color (C.triangulation.verticesOfCell c) := by
  classical
  exact C.triangulation.abstract_sperner
    C.color C.missing C.boundary_odd C.local_parity

end SpernerCertificate

/--
Finished abstract Sperner theorem, packaged as a single certificate input.
-/
theorem combinatorial_sperner [Fintype ι] [DecidableEq ι]
    (C : SpernerCertificate ι V Cell Facet) :
    ∃ c : Cell,
      FullyLabeled C.color (C.triangulation.verticesOfCell c) :=
  C.exists_fully_labeled

/-!
## Indexed simplex-cell API

The abstract theorem deliberately takes local parity as certificate input.
The basic API below is useful for future instantiations where a top cell has
one distinguished vertex for each label and facets are deletion facets.

Important warning: the tempting theorem

`Odd (C.relevantDeletionIndices color missing).card ↔ FullyLabeled color C.vertices`

is false for arbitrary colourings of an indexed cell.  For example, with four
labels and vertex colours `[1, 1, 1, 2]` while `missing = 0`, the three vertices
of colour `1` can yield three relevant deletion facets although the cell is not
fully labelled.  Concrete Sperner instantiations must therefore prove the
appropriate local parity statement for their own geometric certificate.
-/

section IndexedSimplexLocalParity

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [DecidableEq V]

/-- A cell whose vertices are indexed by the label type. -/
structure IndexedCell (ι V : Type*) [Fintype ι] where
  vertex : ι → V
  vertex_injective : Function.Injective vertex

namespace IndexedCell

/-- The vertices of an indexed cell. -/
def vertices (C : IndexedCell ι V) : Finset V :=
  Finset.univ.image C.vertex

/-- The deletion facet obtained by omitting the vertex indexed by `k`. -/
def deletionFacetVertices (C : IndexedCell ι V) (k : ι) : Finset V :=
  (Finset.univ.erase k).image C.vertex

/-- Indices whose deletion facets are relevant to the missing label. -/
noncomputable def relevantDeletionIndices
    (C : IndexedCell ι V)
    (color : V → ι)
    (missing : ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun k =>
    AlmostFullyLabeled color missing (C.deletionFacetVertices k)

omit [DecidableEq ι] in
theorem mem_vertices_iff
    (C : IndexedCell ι V) (v : V) :
    v ∈ C.vertices ↔ ∃ i : ι, C.vertex i = v := by
  classical
  simp [vertices]

omit [DecidableEq ι] in
theorem vertex_mem_vertices
    (C : IndexedCell ι V) (i : ι) :
    C.vertex i ∈ C.vertices := by
  classical
  simp [vertices]

theorem mem_deletionFacetVertices_iff
    (C : IndexedCell ι V) (k : ι) (v : V) :
    v ∈ C.deletionFacetVertices k ↔
      ∃ i : ι, i ≠ k ∧ C.vertex i = v := by
  classical
  simp [deletionFacetVertices]

theorem vertex_mem_deletionFacetVertices_iff
    (C : IndexedCell ι V) (k i : ι) :
    C.vertex i ∈ C.deletionFacetVertices k ↔ i ≠ k := by
  classical
  rw [C.mem_deletionFacetVertices_iff k (C.vertex i)]
  constructor
  · intro h
    rcases h with ⟨j, hjk, hji⟩
    have hji' : j = i := C.vertex_injective hji
    simpa [hji'] using hjk
  · intro hi
    exact ⟨i, hi, rfl⟩

theorem label_mem_labelsOn_vertices_iff
    (C : IndexedCell ι V)
    (color : V → ι)
    (a : ι) :
    a ∈ labelsOn color C.vertices
      ↔
    ∃ i : ι, color (C.vertex i) = a := by
  classical
  simp [labelsOn, vertices]

theorem label_mem_labelsOn_deletionFacet_iff
    (C : IndexedCell ι V)
    (color : V → ι)
    (k a : ι) :
    a ∈ labelsOn color (C.deletionFacetVertices k)
      ↔
    ∃ i : ι, i ≠ k ∧ color (C.vertex i) = a := by
  classical
  simp [labelsOn, deletionFacetVertices]

theorem mem_relevantDeletionIndices_iff
    (C : IndexedCell ι V)
    (color : V → ι)
    (missing k : ι) :
    k ∈ C.relevantDeletionIndices color missing
      ↔
    AlmostFullyLabeled color missing (C.deletionFacetVertices k) := by
  classical
  simp [relevantDeletionIndices]

/-- Indices of vertices with a fixed colour. -/
def colorFiber
    (C : IndexedCell ι V)
    (color : V → ι)
    (a : ι) : Finset ι :=
  Finset.univ.filter fun i => color (C.vertex i) = a

omit [DecidableEq V] in
theorem mem_colorFiber_iff
    (C : IndexedCell ι V)
    (color : V → ι)
    (a i : ι) :
    i ∈ C.colorFiber color a ↔ color (C.vertex i) = a := by
  classical
  simp [colorFiber]

theorem label_mem_labelsOn_vertices_iff_colorFiber_nonempty
    (C : IndexedCell ι V)
    (color : V → ι)
    (a : ι) :
    a ∈ labelsOn color C.vertices
      ↔
    (C.colorFiber color a).Nonempty := by
  classical
  rw [C.label_mem_labelsOn_vertices_iff color a]
  constructor
  · intro h
    rcases h with ⟨i, hi⟩
    exact ⟨i, by simp [colorFiber, hi]⟩
  · intro h
    rcases h with ⟨i, hi⟩
    exact ⟨i, by simpa [colorFiber] using hi⟩

theorem deletionFacet_almostFullyLabeled_iff
    (C : IndexedCell ι V)
    (color : V → ι)
    (missing k : ι) :
    AlmostFullyLabeled color missing (C.deletionFacetVertices k)
      ↔
    ∀ a : ι, a ≠ missing →
      ∃ i : ι, i ≠ k ∧ color (C.vertex i) = a := by
  classical
  simp [AlmostFullyLabeled, label_mem_labelsOn_deletionFacet_iff]

end IndexedCell

end IndexedSimplexLocalParity

end Sperner
end EcoLean
