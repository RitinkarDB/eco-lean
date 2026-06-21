import EcoLean.MathematicalMiscellany.Sperner.Kuhn.Mesh

/-! The Freudenthal triangulation packaged as an abstract `Sperner.SpernerTriangulationCertificate`,
the Sperner labelling layer, and the per-cell `local_parity` certificate. -/

namespace EconLib
namespace SpernerFreudenthal
namespace BarycentricFreudenthal
open Finset
/-! ### Certificate wiring: the Kuhn triangulation as a `SpernerTriangulationCertificate`

The local incidence classification (door + boundary degree-1 + interior degree-2) is exactly the
incidence data an abstract `Sperner.SpernerTriangulationCertificate` consumes.  The `facetsOfCell`
field wants TYPED facets (`Finset (KuhnGeometricGridFacet d N)`), whereas
`KuhnGeometricGridCell.facets` returns the raw underlying finsets, so we first lift them. -/

/-- The TYPED facets of a sorted cell — each `erase`-facet carries its `IsKuhnGridFacet`
witness `⟨C, …⟩`.  This is the `facetsOfCell` data the certificate expects. -/
noncomputable def KuhnGeometricGridCell.cellFacets {d N : ℕ}
    (C : KuhnGeometricGridCell d N) : Finset (KuhnGeometricGridFacet d N) :=
  C.vertices.attach.image fun x =>
    ⟨C.vertices.erase x.1, ⟨C, (C.mem_facets_iff (C.vertices.erase x.1)).mpr ⟨x.1, x.2, rfl⟩⟩⟩

theorem KuhnGeometricGridCell.mem_cellFacets_iff {d N : ℕ}
    (C : KuhnGeometricGridCell d N) (F : KuhnGeometricGridFacet d N) :
    F ∈ C.cellFacets ↔ F.vertices ∈ C.facets := by
  classical
  rw [KuhnGeometricGridCell.cellFacets, Finset.mem_image]
  constructor
  · rintro ⟨x, _, hx⟩
    rw [← hx]
    exact (C.mem_facets_iff (C.vertices.erase x.1)).mpr ⟨x.1, x.2, rfl⟩
  · intro hF
    rw [C.mem_facets_iff] at hF
    obtain ⟨x, hx, hFeq⟩ := hF
    exact ⟨⟨x, hx⟩, Finset.mem_attach _ _, Subtype.ext hFeq.symm⟩

/-- **THE KUHN TRIANGULATION CERTIFICATE.**  The geometric incidence data of the Kuhn
triangulation, packaged as an abstract `Sperner.SpernerTriangulationCertificate`.  Every
field is discharged by the proven local-incidence theorems; the two hard obligations
`boundary_incident_card` / `interior_incident_card` are exactly `incidentCells_card_eq_one_of_boundary`
/ `incidentCells_card_eq_two_of_not_boundary`.  (The `Fintype`/`DecidableEq` instance fields are
synthesised from the auto-derived `Subtype`/`Finite` instances.) -/
noncomputable def kuhnTriangulationCertificate {d N : ℕ} (hd : 2 ≤ d) :
    Sperner.SpernerTriangulationCertificate
      (SimplexGrid d N) (KuhnGeometricGridCell d N)
      (KuhnGeometricGridFacet d N) :=
  { verticesOfCell := fun C => C.vertices
    verticesOfFacet := fun F => F.vertices
    facetsOfCell := fun C => C.cellFacets
    incidentCells := fun F => F.incidentCells
    incident_iff := fun C F => (F.mem_incidentCells_iff C).trans (C.mem_cellFacets_iff F).symm
    facet_vertices_subset := fun C F hF => C.facet_subset ((C.mem_cellFacets_iff F).mp hF)
    boundaryFacet := fun F => F.IsBoundary
    boundary_incident_card := fun F hF => F.incidentCells_card_eq_one_of_boundary hd hF
    interior_incident_card := fun F hF => F.incidentCells_card_eq_two_of_not_boundary hd hF }

/-! ### Facet enumeration + boundary facet set (for the boundary-oddness layer) -/

/-- All facets of the Kuhn triangulation (the union of every cell's typed facets). -/
noncomputable def allKuhnGeometricGridFacets (d N : ℕ) :
    Finset (KuhnGeometricGridFacet d N) :=
  (allKuhnGeometricGridCells d N).biUnion fun C => C.cellFacets

theorem KuhnGeometricGridFacet.mem_all {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) :
    F ∈ allKuhnGeometricGridFacets d N := by
  classical
  show F ∈ (allKuhnGeometricGridCells d N).biUnion fun C => C.cellFacets
  rw [Finset.mem_biUnion]
  obtain ⟨C, hC⟩ := F.2
  exact ⟨C, C.mem_all, (C.mem_cellFacets_iff F).mpr hC⟩

/-- The boundary facets of the Kuhn triangulation. -/
noncomputable def allBoundaryKuhnGeometricGridFacets (d N : ℕ) :
    Finset (KuhnGeometricGridFacet d N) := by
  classical
  exact (allKuhnGeometricGridFacets d N).filter fun F => F.IsBoundary

theorem KuhnGeometricGridFacet.mem_allBoundary_iff {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) :
    F ∈ allBoundaryKuhnGeometricGridFacets d N ↔ F.IsBoundary := by
  classical
  rw [allBoundaryKuhnGeometricGridFacets, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨F.mem_all, h⟩⟩

/-- Boundary facets (as a finite-set membership) have exactly one incident cell. -/
theorem KuhnGeometricGridFacet.incidentCells_card_eq_one_of_mem_boundary {d N : ℕ}
    (hd : 2 ≤ d) {F : KuhnGeometricGridFacet d N}
    (hF : F ∈ allBoundaryKuhnGeometricGridFacets d N) :
    F.incidentCells.card = 1 :=
  F.incidentCells_card_eq_one_of_boundary hd ((F.mem_allBoundary_iff).mp hF)

/-- Non-boundary facets (finite-set form) have exactly two incident cells. -/
theorem KuhnGeometricGridFacet.incidentCells_card_eq_two_of_not_mem_boundary {d N : ℕ}
    (hd : 2 ≤ d) {F : KuhnGeometricGridFacet d N}
    (hnb : F ∉ allBoundaryKuhnGeometricGridFacets d N) :
    F.incidentCells.card = 2 :=
  F.incidentCells_card_eq_two_of_not_boundary hd (fun hbd => hnb ((F.mem_allBoundary_iff).mpr hbd))

/-! ### Sperner labelling layer — audit + the first geometry→colour bridge

**`Sperner.SpernerCertificate (Fin (d+1)) (SimplexGrid d N) Cell Facet`** (the LABELLED layer atop
`SpernerTriangulationCertificate`) has FIVE fields; the discharge for each:
• `triangulation` — `kuhnTriangulationCertificate hd` (proved above).
• `color : SimplexGrid d N → Fin (d+1)` — DATA: a Sperner labelling.  REUSE the existing API
  `GridIsSperner color := ∀ x, color x ∈ x.support` (`GridPackage.lean`) as the Sperner boundary
  condition (a vertex's label is a NON-zero coordinate; equivalently `x.1 i = 0 → color x ≠ i` via
  `GridIsSperner.label_ne_missing_of_onBoundaryFace`).  Do NOT define a new predicate.
• `missing : Fin (d+1)` — DATA: the distinguished outside label.
• `boundary_odd : Odd (triangulation.boundaryRelevantFacets color missing).card` — the BOUNDARY
  DOUBLE-COUNT, the hard remaining fact (`boundaryRelevantFacets = univ.filter (boundaryFacet ∧
  relevantFacet)`, `relevantFacet f = Sperner.AlmostFullyLabeled color missing F.verticesOfFacet`).
• `local_parity : ∀ C, Odd (triangulation.relevantFacetsOfCell color missing C).card ↔
  Sperner.FullyLabeled color C.vertices` — the LOCAL per-cell parity.
`Sperner.combinatorial_sperner` then yields `∃ C, FullyLabeled color C.vertices`.
This module provides the FIRST geometry→colour bridge (boundary coordinate face ⟹ that colour is
forbidden on the facet) and isolates the two `boundary_odd` / `local_parity` obligations as explicit
hypotheses; those two are discharged in `BoundaryOdd.lean`. -/

/-- **THE FIRST GEOMETRY→COLOUR BRIDGE.**  If a coordinate `i` vanishes on every vertex of a facet
(the geometric boundary condition), then `i` is a FORBIDDEN colour on that facet — it never appears
as a label.  Direct consequence of the Sperner labelling condition `GridIsSperner` (a label is
always a non-zero coordinate). -/
theorem KuhnGeometricGridFacet.boundary_forbids_coordinate_color {d N : ℕ}
    {color : SimplexGrid d N → Fin (d + 1)} (hSperner : GridIsSperner color)
    {F : KuhnGeometricGridFacet d N} {i : Fin (d + 1)}
    (hi : ∀ x ∈ F.vertices, x.1 i = 0) :
    i ∉ F.vertices.image color := by
  classical
  intro hmem
  rw [Finset.mem_image] at hmem
  obtain ⟨x, hxF, hxc⟩ := hmem
  exact hSperner.label_ne_missing_of_onBoundaryFace i x (hi x hxF) hxc

/-- A boundary facet is missing at least one colour (the coordinate of its boundary face). -/
theorem KuhnGeometricGridFacet.exists_missing_color_of_boundary {d N : ℕ}
    {color : SimplexGrid d N → Fin (d + 1)} (hSperner : GridIsSperner color)
    {F : KuhnGeometricGridFacet d N} (hbd : F.IsBoundary) :
    ∃ i : Fin (d + 1), i ∉ F.vertices.image color := by
  rcases hbd with ⟨i, hi⟩
  exact ⟨i, F.boundary_forbids_coordinate_color hSperner hi⟩

/-! ### Sorted-cell `local_parity` (the per-cell colouring obligation of `SpernerCertificate`)

**The exact `local_parity` field** (`Sperner.SpernerCertificate`, `Sperner.lean`):
```
local_parity : ∀ c : Cell,
  Odd (triangulation.relevantFacetsOfCell color missing c).card ↔
    FullyLabeled color (triangulation.verticesOfCell c)
```
Reading off the fields:
• the cell variable is `c : Cell` (here `Cell = KuhnGeometricGridCell d N`);
• the set of facets of a cell is `triangulation.facetsOfCell c`, which for our certificate is
  `c.cellFacets` (the typed `d+1` deletion facets);
• the colour/missing predicate on a facet `f` is `relevantFacet color missing f =
  Sperner.AlmostFullyLabeled color missing (triangulation.verticesOfFacet f)`, i.e. every colour
  except `missing` appears on `f.vertices`; `relevantFacetsOfCell` filters `facetsOfCell` by it;
• the parity conclusion is `Odd (…relevantFacetsOfCell…).card`;
• fully-labelled cells appear as the RHS `Sperner.FullyLabeled color (verticesOfCell c)`
  (= `FullyLabeled color c.vertices`), i.e. every colour appears on the cell's `d+1` vertices.

**The `local_parity` proof** is PURELY COMBINATORIAL
in a cell's `d+1` vertices and its `d+1` erase-facets: it (i) rewrites the typed-facet filter to an
`attach`-filter via `Finset.filter_image` + `Finset.card_image_of_injective` (the deletion-facet map
is injective by `Finset.erase_inj`), (ii) drops `attach` via the cell-agnostic
`FiniteSimplexLocalParity.card_attach_filter_eq_filter`, (iii) reduces `AlmostFullyLabeled` to the
explicit `∀ j ≠ missing, ∃ y ∈ erase, colour y = j`, and (iv) finishes with the cell-agnostic
`FiniteSimplexLocalParity.odd_relevant_erasures_iff_surjective` (the colour-counting parity:
odd #relevant-erasures ⟺ the colouring is surjective on the `d+1` vertices ⟺ fully labelled).  Only
`Finset.card = Fintype.card (Fin (d+1))` is used from the cell — NO grid-specific geometry — so the
two `FiniteSimplexLocalParity` lemmas (cell-agnostic) are used for the Kuhn cells. -/

/-- Decidability (classical) of "almost fully labelled" on a Kuhn facet, so the per-cell
relevant-facet filter elaborates in the statement of `localParity`.  Only the FACET predicate is provided
classically; the inner vertex filters keep their canonical `Fintype` decidability. -/
noncomputable instance instDecidableAlmostFullyLabeledSortedFacet {d N : ℕ}
    (color : SimplexGrid d N → Fin (d + 1)) (missing : Fin (d + 1)) :
    DecidablePred fun F : KuhnGeometricGridFacet d N =>
      Sperner.AlmostFullyLabeled color missing F.vertices := by
  classical
  intro F
  exact Classical.propDecidable _

/-- **SORTED-CELL LOCAL PARITY.**  For a Kuhn cell `C`, the number of its (typed) deletion
facets that are *almost fully labelled* (every colour but `missing` appears) is odd iff `C` itself is
*fully labelled* (every colour appears on its `d+1` vertices).  This is the finite colour-counting
parity of a single simplex; it holds for ANY colouring (no Sperner boundary condition needed).  The
proof is the finite colour-counting parity via the cell-agnostic
`FiniteSimplexLocalParity` combinatorics. -/
theorem KuhnGeometricGridCell.localParity {d N : ℕ}
    (C : KuhnGeometricGridCell d N)
    (color : SimplexGrid d N → Fin (d + 1))
    (missing : Fin (d + 1)) :
    Odd
      ((C.cellFacets.filter fun F : KuhnGeometricGridFacet d N =>
        Sperner.AlmostFullyLabeled color missing F.vertices).card)
      ↔
    Sperner.FullyLabeled color C.vertices := by
  classical
  let facetOf : {x : SimplexGrid d N // x ∈ C.vertices} →
      KuhnGeometricGridFacet d N :=
    fun x => ⟨C.vertices.erase x.1,
      ⟨C, (C.mem_facets_iff (C.vertices.erase x.1)).mpr ⟨x.1, x.2, rfl⟩⟩⟩
  have hinj : Function.Injective facetOf := by
    intro x y hxy
    have herase : C.vertices.erase x.1 = C.vertices.erase y.1 :=
      congrArg Subtype.val hxy
    have hxyval : x.1 = y.1 := (Finset.erase_inj C.vertices x.2).mp herase
    exact Subtype.ext hxyval
  have hcardFacets :
      ((C.cellFacets.filter fun F : KuhnGeometricGridFacet d N =>
        Sperner.AlmostFullyLabeled color missing F.vertices).card)
        =
      ((C.vertices.attach.filter fun x =>
        Sperner.AlmostFullyLabeled color missing (C.vertices.erase x.1)).card) := by
    rw [KuhnGeometricGridCell.cellFacets]
    rw [Finset.filter_image]
    rw [Finset.card_image_of_injective _ hinj]
    rfl
  have hcardAttach :
      ((C.vertices.attach.filter fun x =>
        Sperner.AlmostFullyLabeled color missing (C.vertices.erase x.1)).card)
        =
      ((C.vertices.filter fun x =>
        Sperner.AlmostFullyLabeled color missing (C.vertices.erase x)).card) :=
    FiniteSimplexLocalParity.card_attach_filter_eq_filter
      C.vertices
      (fun x => Sperner.AlmostFullyLabeled color missing (C.vertices.erase x))
  have hvertexCard : C.vertices.card = Fintype.card (Fin (d + 1)) := by
    rw [C.vertices_card, Fintype.card_fin]
  have hfinite :=
    FiniteSimplexLocalParity.odd_relevant_erasures_iff_surjective
      (α := SimplexGrid d N) (ι := Fin (d + 1))
      C.vertices color hvertexCard missing
  have halmost :
      ((C.vertices.filter fun x =>
        Sperner.AlmostFullyLabeled color missing (C.vertices.erase x)).card)
        =
      ((C.vertices.filter fun x =>
        ∀ j : Fin (d + 1), j ≠ missing →
          ∃ y ∈ C.vertices.erase x, color y = j).card) := by
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro x _hx
    rw [Sperner.almostFullyLabeled_iff]
    simp only [Sperner.mem_labelsOn_iff]
  rw [hcardFacets, hcardAttach, halmost, Sperner.fullyLabeled_iff]
  simpa [Sperner.mem_labelsOn_iff] using hfinite

/-- **LOCAL PARITY IN CERTIFICATE FORM.**  Discharges the `local_parity` field of the abstract
`Sperner.SpernerCertificate` for the Kuhn triangulation, for every cell `C`. -/
theorem kuhnGridLocalParityForCertificate {d N : ℕ} (hd : 2 ≤ d)
    (color : SimplexGrid d N → Fin (d + 1))
    (missing : Fin (d + 1))
    (C : KuhnGeometricGridCell d N) :
    Odd
      ((kuhnTriangulationCertificate hd).relevantFacetsOfCell color missing C).card
      ↔
    Sperner.FullyLabeled color C.vertices := by
  simpa [kuhnTriangulationCertificate,
    Sperner.SpernerTriangulationCertificate.relevantFacetsOfCell,
    Sperner.SpernerTriangulationCertificate.relevantFacet,
    KuhnGeometricGridFacet.vertices] using
    KuhnGeometricGridCell.localParity C color missing

/-- **Isolating the two Sperner obligations.**  Given the two hard Sperner facts (`boundary_odd` and
`local_parity`) as hypotheses, the Kuhn triangulation upgrades to a full
`Sperner.SpernerCertificate` (the `triangulation` data is already proved).  Both hypotheses are
discharged unconditionally downstream, yielding `kuhnSpernerCertificate`. -/
noncomputable def kuhnSpernerCertificate_of_boundaryOdd_localParity {d N : ℕ} (hd : 2 ≤ d)
    (color : SimplexGrid d N → Fin (d + 1)) (missing : Fin (d + 1))
    (hbo : Odd ((kuhnTriangulationCertificate hd).boundaryRelevantFacets
      color missing).card)
    (hlp : ∀ C : KuhnGeometricGridCell d N,
      Odd ((kuhnTriangulationCertificate hd).relevantFacetsOfCell color missing C).card ↔
        Sperner.FullyLabeled color C.vertices) :
    Sperner.SpernerCertificate (Fin (d + 1)) (SimplexGrid d N)
      (KuhnGeometricGridCell d N) (KuhnGeometricGridFacet d N) :=
  { triangulation := kuhnTriangulationCertificate hd
    color := color
    missing := missing
    boundary_odd := hbo
    local_parity := hlp }

/-- The Sperner OUTPUT for the Kuhn triangulation, CONDITIONAL on the two remaining
obligations: a fully-labelled cell exists.  (Once `boundary_odd`/`local_parity` are proved, this
becomes unconditional and feeds Brouwer.) -/
theorem kuhn_exists_fullyLabeled_of_boundaryOdd_localParity {d N : ℕ} (hd : 2 ≤ d)
    (color : SimplexGrid d N → Fin (d + 1)) (missing : Fin (d + 1))
    (hbo : Odd ((kuhnTriangulationCertificate hd).boundaryRelevantFacets
      color missing).card)
    (hlp : ∀ C : KuhnGeometricGridCell d N,
      Odd ((kuhnTriangulationCertificate hd).relevantFacetsOfCell color missing C).card ↔
        Sperner.FullyLabeled color C.vertices) :
    ∃ C : KuhnGeometricGridCell d N, Sperner.FullyLabeled color C.vertices :=
  Sperner.combinatorial_sperner
    (kuhnSpernerCertificate_of_boundaryOdd_localParity hd color missing hbo hlp)

/-- **SHARPER CERTIFICATE — only `boundary_odd` remains.**  `local_parity` is now PROVED
(`kuhnGridLocalParityForCertificate`), so the Kuhn triangulation upgrades to a
full `Sperner.SpernerCertificate` from the single remaining obligation `boundary_odd`.  (Supersedes
`kuhnSpernerCertificate_of_boundaryOdd_localParity`, which is kept as the general bridge
that accepts an arbitrary `local_parity` proof.) -/
noncomputable def kuhnSpernerCertificate_of_boundaryOdd {d N : ℕ} (hd : 2 ≤ d)
    (color : SimplexGrid d N → Fin (d + 1)) (missing : Fin (d + 1))
    (hbo : Odd ((kuhnTriangulationCertificate hd).boundaryRelevantFacets
      color missing).card) :
    Sperner.SpernerCertificate (Fin (d + 1)) (SimplexGrid d N)
      (KuhnGeometricGridCell d N) (KuhnGeometricGridFacet d N) :=
  kuhnSpernerCertificate_of_boundaryOdd_localParity hd color missing hbo
    (fun C => kuhnGridLocalParityForCertificate hd color missing C)

/-- The Sperner OUTPUT for the Kuhn triangulation, CONDITIONAL only on `boundary_odd`: a
fully-labelled cell exists.  (Once `boundary_odd` is proved this becomes unconditional and feeds
Brouwer.) -/
theorem kuhn_exists_fullyLabeled_of_boundaryOdd {d N : ℕ} (hd : 2 ≤ d)
    (color : SimplexGrid d N → Fin (d + 1)) (missing : Fin (d + 1))
    (hbo : Odd ((kuhnTriangulationCertificate hd).boundaryRelevantFacets
      color missing).card) :
    ∃ C : KuhnGeometricGridCell d N, Sperner.FullyLabeled color C.vertices :=
  Sperner.combinatorial_sperner
    (kuhnSpernerCertificate_of_boundaryOdd hd color missing hbo)

end BarycentricFreudenthal
end SpernerFreudenthal
end EconLib
