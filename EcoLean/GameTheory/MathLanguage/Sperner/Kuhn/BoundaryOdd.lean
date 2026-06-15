import EcoLean.GameTheory.MathLanguage.Sperner.Kuhn.Certificate

/-! Boundary oddness for the Freudenthal Sperner certificate: the missing-face
deletion/reinsertion bijection, colour transport, the dimension induction, and the 1-dimensional
Sperner base case (`OneDimSperner`). -/

namespace EcoLean
namespace SpernerFreudenthal
namespace BarycentricFreudenthal
open Finset
/-! ### Boundary oddness — reduction to the fixed missing-colour coordinate face

**The exact `boundary_odd` field** (`Sperner.SpernerCertificate`, `Sperner.lean`):
```
boundary_odd : Odd (triangulation.boundaryRelevantFacets color missing).card
```
where, unfolding the abstract certificate definitions (`Sperner.lean`):
```
boundaryRelevantFacets color missing
  = Finset.univ.filter (fun f => boundaryFacet f ∧ relevantFacet color missing f)
relevantFacet color missing f = AlmostFullyLabeled color missing (verticesOfFacet f)
```
So for OUR certificate (`boundaryFacet F := F.IsBoundary`, `verticesOfFacet F := F.vertices`):
• the SET counted is `univ.filter (fun F => F.IsBoundary ∧ AlmostFullyLabeled color missing F.vertices)`
  — the boundary facets that are almost-fully-labelled missing exactly `missing`;
• `boundaryFacet F` is `F.IsBoundary` (= `∃ i, ∀ x ∈ F.vertices, x.1 i = 0`, a coordinate face);
• `AlmostFullyLabeled color missing F.vertices` says every colour EXCEPT `missing` appears on `F.vertices`;
• `Odd` is applied to the CARDINALITY of that filtered facet set.

**The target type** (already the `hbo` hypothesis of `kuhnSpernerCertificate_of_boundaryOdd`
and `kuhn_exists_fullyLabeled_of_boundaryOdd`):
```
Odd ((kuhnTriangulationCertificate hd).boundaryRelevantFacets L missing).card
```
(No separate declaration is added: this IS the obligation those builders consume.) -/

/-- **LOCALIZATION.**  A boundary facet that is almost-fully-labelled for `missing` can only
lie on the coordinate face `missing = 0`: if such an `F` is identically zero on coordinate `i`
(a geometric boundary face), then `i = missing`.  Proof: `boundary_forbids_coordinate_color` (the
Sperner condition forbids the colour of a zero coordinate on the facet) gives `i ∉ F.vertices.image L`,
while `AlmostFullyLabeled` supplies every colour but `missing`; so `i ≠ missing` is impossible. -/
theorem KuhnGeometricGridFacet.boundary_almostFullyLabeled_lies_on_missing_face {d N : ℕ}
    {L : SimplexGrid d N → Fin (d + 1)} (hSperner : GridIsSperner L)
    {missing : Fin (d + 1)} {F : KuhnGeometricGridFacet d N}
    (hbd : F.IsBoundary) (hAF : Sperner.AlmostFullyLabeled L missing F.vertices) :
    ∀ i : Fin (d + 1), (∀ x ∈ F.vertices, x.1 i = 0) → i = missing := by
  intro i hi
  by_contra hne
  exact (F.boundary_forbids_coordinate_color hSperner hi)
    ((Sperner.almostFullyLabeled_iff L missing F.vertices).mp hAF i hne)

/-- The facets lying entirely on the fixed coordinate face `{x | x.1 i = 0}` (every
vertex's `i`-coordinate is zero). -/
noncomputable def kuhnBoundaryFaceFacets (d N : ℕ) (i : Fin (d + 1)) :
    Finset (KuhnGeometricGridFacet d N) := by
  classical
  exact (allKuhnGeometricGridFacets d N).filter fun F => ∀ x ∈ F.vertices, x.1 i = 0

theorem KuhnGeometricGridFacet.mem_boundaryFaceFacets_iff {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (i : Fin (d + 1)) :
    F ∈ kuhnBoundaryFaceFacets d N i ↔ ∀ x ∈ F.vertices, x.1 i = 0 := by
  classical
  rw [kuhnBoundaryFaceFacets, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨F.mem_all, h⟩⟩

/-- **REDUCTION.**  The boundary facets counted by `boundary_odd` for `missing` are EXACTLY
the facets on the coordinate face `missing = 0` that are almost-fully-labelled for `missing`.
Forward: localization forces every relevant boundary facet onto the `missing`-face.
Backward: a `missing`-face facet is a boundary facet with witness `i = missing`.  This converts the
global `boundary_odd` count into a parity question on the single `missing`-coordinate face. -/
theorem kuhnBoundaryOdd_filter_eq_missing_face_filter {d N : ℕ} (hd : 2 ≤ d)
    (L : SimplexGrid d N → Fin (d + 1)) (hSperner : GridIsSperner L) (missing : Fin (d + 1)) :
    (kuhnTriangulationCertificate hd).boundaryRelevantFacets L missing =
      (kuhnBoundaryFaceFacets d N missing).filter
        fun F => Sperner.AlmostFullyLabeled L missing F.vertices := by
  classical
  ext F
  rw [(kuhnTriangulationCertificate hd).mem_boundaryRelevantFacets_iff L missing F,
    Finset.mem_filter, F.mem_boundaryFaceFacets_iff]
  simp only [kuhnTriangulationCertificate,
    Sperner.SpernerTriangulationCertificate.relevantFacet]
  constructor
  · rintro ⟨hbd, hAF⟩
    obtain ⟨i, hi⟩ := hbd
    have hi_eq : i = missing :=
      F.boundary_almostFullyLabeled_lies_on_missing_face hSperner ⟨i, hi⟩ hAF i hi
    refine ⟨?_, hAF⟩
    intro x hx
    rw [← hi_eq]
    exact hi x hx
  · rintro ⟨hface, hAF⟩
    exact ⟨⟨missing, hface⟩, hAF⟩

/-! ### The lower-dimensional induction route

After `boundary_odd` counts ONLY facets on the `missing = 0` coordinate face.  That face is
the `(d-1)`-dimensional sub-simplex `{x : SimplexGrid d N // x.1 missing = 0}`, in bijection with
`SimplexGrid (d-1) N` by DELETING coordinate `missing` (`Fin (d+1) ∖ {missing} ≃ Fin d`, e.g. via
`missing.succAbove`/`finSuccAboveEquiv`; the `∑ = N` constraint persists because the dropped
coordinate is `0`).  Under that bijection:
• a sorted facet `F` lying on the `missing`-face has `d` vertices, all with `x.1 missing = 0`; deleting
  the `missing` coordinate sends them to `d` points of `SimplexGrid (d-1) N`, i.e. a TOP CELL of the
  Kuhn triangulation ONE DIMENSION DOWN (`KuhnGeometricGridCell (d-1) N`);
• `AlmostFullyLabeled L missing F.vertices` (every colour but `missing` appears) becomes
  `Sperner.FullyLabeled L' F'.vertices` for the restricted colouring `L' : SimplexGrid (d-1) N → Fin d`
  (the `d` non-`missing` colours, re-indexed by the same `Fin (d+1) ∖ {missing} ≃ Fin d`).
So `boundary_odd(d)` for `missing` ⟺ `Odd (# fully-labelled top cells of the (d-1)-dim Kuhn
triangulation under L')`.  THAT oddness is the OUTPUT of the abstract parity machinery one dimension
down: `SpernerTriangulationCertificate.exists_cell_odd_relevantFacetsOfCell_of_odd_boundary` gives a
cell with an odd relevant-facet count, and `local_parity(d-1)` (already PROVED:
`kuhnGridLocalParityForCertificate`) identifies the odd-relevant cells with the fully-labelled
ones — the FULL count's parity then follows from `boundary_odd(d-1)` via the relevant-incidence double
count (`relevantIncidences_card_eq_sum_relevantFacetsOfCell` + `odd_sum_iff_odd_card_odd`).  Hence
`boundary_odd` is a genuine INDUCTION on `d` (base `d = 1`/the 1-simplex: boundary = two endpoints,
count directly odd).  The deleting-coordinate cell/facet bijection
`{missing-face facets} ≃ KuhnGeometricGridCell (d-1) N` (and the colour re-indexing) is
constructed below; with it, `boundary_odd` reduces to the `(d-1)`
instance of THIS certificate's fully-labelled-cell parity. -/

/-! ### Coordinate-deletion / reinsertion infrastructure (toward the `boundary_odd` induction)

**Coordinate-deletion equivalence (AUDIT, no new definition).**  Mathlib ALREADY provides
the tuple deletion/insertion maps, so NO bespoke `Fin.deleteEquiv` is defined.  For `missing : Fin (n+1)`:
• `missing.succAbove : Fin n ↪ Fin (n+1)` embeds the remaining coordinates (skips `missing`);
• `Fin.removeNth missing f = fun i => f (missing.succAbove i)` deletes coordinate `missing`;
• `Fin.insertNth missing a g` reinserts value `a` at `missing`;
with inverses `Fin.removeNth_insertNth`, `Fin.insertNth_self_removeNth`, value lemmas
`Fin.insertNth_apply_same`/`Fin.insertNth_apply_succAbove`, and the sum split
`Fin.sum_univ_succAbove f missing : ∑ i, f i = f missing + ∑ i, f (missing.succAbove i)`.
These are used DIRECTLY below.  PARAMETERIZATION (to avoid `d-1`): a vertex of `SimplexGrid (m+1) N`
(coordinates `Fin (m+2)`) with `missing : Fin (m+2)` deletes to `SimplexGrid m N` (coordinates
`Fin (m+1)`).  The `boundary_odd` connection (a later pass) instantiates `m+1 = d`. -/

/-- **Vertex deletion.**  Delete the (zero-valued) coordinate `missing` from a boundary-face
vertex of `SimplexGrid (m+1) N`, yielding a vertex of `SimplexGrid m N`.  The sum is preserved
because the dropped coordinate is `0`. -/
def SimplexGrid.deleteCoord {m N : ℕ} (missing : Fin (m + 2))
    (x : SimplexGrid (m + 1) N) (hx : x.1 missing = 0) : SimplexGrid m N := by
  refine ⟨Fin.removeNth missing x.1, ?_⟩
  have hsum := Fin.sum_univ_succAbove x.1 missing
  have hx2 : (∑ i, x.1 i) = N := x.2
  simp only [Fin.removeNth]
  omega

/-- **Vertex reinsertion.**  Insert a `0` at coordinate `missing`, sending a vertex of
`SimplexGrid m N` to a boundary-face vertex of `SimplexGrid (m+1) N`. -/
def SimplexGrid.insertZeroCoord {m N : ℕ} (missing : Fin (m + 2))
    (y : SimplexGrid m N) : SimplexGrid (m + 1) N := by
  refine ⟨Fin.insertNth missing 0 y.1, ?_⟩
  rw [Fin.sum_univ_succAbove _ missing, Fin.insertNth_apply_same]
  simp only [Fin.insertNth_apply_succAbove]
  simpa using y.2

@[simp] theorem SimplexGrid.insertZeroCoord_coord_missing {m N : ℕ} (missing : Fin (m + 2))
    (y : SimplexGrid m N) : (SimplexGrid.insertZeroCoord missing y).1 missing = 0 :=
  Fin.insertNth_apply_same (α := fun _ => ℕ) missing 0 y.1

/-- **Inverse 1.**  Deleting after reinserting recovers the original lower vertex. -/
theorem SimplexGrid.deleteCoord_insertZeroCoord {m N : ℕ} (missing : Fin (m + 2))
    (y : SimplexGrid m N) :
    SimplexGrid.deleteCoord missing (SimplexGrid.insertZeroCoord missing y)
        (SimplexGrid.insertZeroCoord_coord_missing missing y) = y := by
  apply Subtype.ext
  funext i
  show Fin.insertNth (α := fun _ => ℕ) missing (0 : ℕ) y.1 (missing.succAbove i) = y.1 i
  rw [Fin.insertNth_apply_succAbove]

/-- **Inverse 2.**  Reinserting `0` after deleting a zero coordinate recovers the vertex. -/
theorem SimplexGrid.insertZeroCoord_deleteCoord {m N : ℕ} (missing : Fin (m + 2))
    (x : SimplexGrid (m + 1) N) (hx : x.1 missing = 0) :
    SimplexGrid.insertZeroCoord missing (SimplexGrid.deleteCoord missing x hx) = x := by
  apply Subtype.ext
  show Fin.insertNth missing 0 (Fin.removeNth missing x.1) = x.1
  rw [← hx]
  exact Fin.insertNth_self_removeNth missing x.1

/-- `insertZeroCoord` is injective (left inverse `deleteCoord`). -/
theorem SimplexGrid.insertZeroCoord_injective {m N : ℕ} (missing : Fin (m + 2)) :
    Function.Injective (SimplexGrid.insertZeroCoord (N := N) missing) := by
  intro y y' h
  apply Subtype.ext
  have key : ∀ z : SimplexGrid m N,
      Fin.removeNth missing (SimplexGrid.insertZeroCoord missing z).1 = z.1 :=
    fun z => Fin.removeNth_insertNth (α := fun _ => ℕ) missing 0 z.1
  rw [← key y, ← key y', h]

/-- **Facet deletion.**  Delete coordinate `missing` from every vertex of a facet lying on
the `missing = 0` boundary face, yielding a finite vertex set in `SimplexGrid m N`. -/
noncomputable def KuhnGeometricGridFacet.deleteMissingFace {m N : ℕ} (missing : Fin (m + 2))
    (F : KuhnGeometricGridFacet (m + 1) N)
    (hface : ∀ x ∈ F.vertices, x.1 missing = 0) : Finset (SimplexGrid m N) :=
  F.vertices.attach.image fun p => SimplexGrid.deleteCoord missing p.1 (hface p.1 p.2)

/-- **Cell reinsertion.**  Reinsert a `0` coordinate at `missing` into every vertex of a
lower cell, yielding a finite vertex set on the `missing = 0` face of `SimplexGrid (m+1) N`. -/
noncomputable def KuhnGeometricGridCell.insertZeroFace {m N : ℕ}
    (C : KuhnGeometricGridCell m N) (missing : Fin (m + 2)) :
    Finset (SimplexGrid (m + 1) N) :=
  C.vertices.image (SimplexGrid.insertZeroCoord missing)

/-- The reinserted face has `m+1` vertices — exactly a facet's worth in dimension `m+1`. -/
theorem KuhnGeometricGridCell.insertZeroFace_card {m N : ℕ}
    (C : KuhnGeometricGridCell m N) (missing : Fin (m + 2)) :
    (C.insertZeroFace missing).card = m + 1 := by
  rw [KuhnGeometricGridCell.insertZeroFace,
    Finset.card_image_of_injective _ (SimplexGrid.insertZeroCoord_injective missing),
    C.vertices_card]

/-- The deleted facet has `m+1` vertices — exactly a top cell's worth in dimension `m` (`deleteCoord`
is injective on the face, with left inverse `insertZeroCoord`). -/
theorem KuhnGeometricGridFacet.deleteMissingFace_card {m N : ℕ} (missing : Fin (m + 2))
    (F : KuhnGeometricGridFacet (m + 1) N)
    (hface : ∀ x ∈ F.vertices, x.1 missing = 0) :
    (F.deleteMissingFace missing hface).card = m + 1 := by
  have hinj : Function.Injective
      (fun p : {x // x ∈ F.vertices} =>
        SimplexGrid.deleteCoord missing p.1 (hface p.1 p.2)) := by
    intro p q hpq
    apply Subtype.ext
    rw [← SimplexGrid.insertZeroCoord_deleteCoord missing p.1 (hface p.1 p.2),
        ← SimplexGrid.insertZeroCoord_deleteCoord missing q.1 (hface q.1 q.2)]
    exact congrArg (SimplexGrid.insertZeroCoord missing) hpq
  rw [KuhnGeometricGridFacet.deleteMissingFace,
    Finset.card_image_of_injective _ hinj, Finset.card_attach, F.vertices_card]

/-! ### Deletion preserves the Kuhn structure

The geometric crux: deleting the (absent) coordinate `missing` from `base + χ(S)` is `base' + χ(S')`
for the deleted base `removeNth missing base` and the deleted subset `KSubset.deleteAbsentCoord
missing S` — `χ` of a `missing`-omitting subset transports along `succAbove`. -/

/-- A facet lying on the `missing = 0` boundary face deletes (drop coordinate `missing`)
to a Kuhn top cell one dimension down.  Needs `1 ≤ m` (dim-`0` cells do not exist in this
model: `0 < k < 1` is unsatisfiable). -/
theorem KuhnGeometricGridFacet.deleteMissingFace_isSortedCell {m N : ℕ} (hm : 1 ≤ m)
    (missing : Fin (m + 2)) (F : KuhnGeometricGridFacet (m + 1) N)
    (hface : ∀ x ∈ F.vertices, x.1 missing = 0) :
    IsKuhnGridSmallSimplex (F.deleteMissingFace missing hface) := by
  classical
  obtain ⟨D, S₀, hS₀, hFeq⟩ := F.exists_parent_data
  set W := D.subsets.erase S₀ with hW
  have hWcard : W.card = m + 1 := by
    have hc := D.hsubsets.1
    rw [hW, Finset.card_erase_of_mem hS₀]
    omega
  have hWsorted : KSubsetCollection.IsSorted W := fun I hI J hJ hIJ =>
    D.hsubsets.2 I (Finset.mem_of_mem_erase hI) J (Finset.mem_of_mem_erase hJ) hIJ
  -- per-cell face consequence
  have hpercell : ∀ S ∈ W, D.base missing = 0 ∧ missing ∉ S.1 := by
    intro S hSW
    have hcv : cellVertexMap D S ∈ F.vertices := by
      rw [hFeq, Finset.mem_image]; exact ⟨S, hSW, rfl⟩
    have hsum0 : D.base missing + chi S.1 missing = 0 := hface (cellVertexMap D S) hcv
    have hchi : chi S.1 missing = 0 := by omega
    refine ⟨by omega, ?_⟩
    intro hmem
    simp [chi, hmem] at hchi
  have hWne : W.Nonempty := Finset.card_pos.mp (by rw [hWcard]; omega)
  have hbase : D.base missing = 0 := (hpercell hWne.choose hWne.choose_spec).1
  have hpW : ∀ S ∈ W, missing ∉ S.1 := fun S hS => (hpercell S hS).2
  have hmissing : missing ∈ KSubsetCollection.commonAbsent W :=
    (KSubsetCollection.mem_commonAbsent_iff W missing).mpr hpW
  -- k ≤ m (else only one deleted subset, contradicting card = m+1 ≥ 2)
  have hk : D.k < m + 1 := by
    by_contra hcon
    have hkeq : D.k = m + 1 := by have := D.hk_lt; omega
    have hcard' : (KSubsetCollection.deleteAbsentCoord W missing hmissing).card = m + 1 := by
      rw [KSubsetCollection.card_deleteAbsentCoord]; exact hWcard
    have hall : ∀ S' ∈ KSubsetCollection.deleteAbsentCoord W missing hmissing,
        S'.1 = Finset.univ := by
      intro S' _; apply Finset.eq_univ_of_card; rw [S'.2, hkeq, Fintype.card_fin]
    have hle1 : (KSubsetCollection.deleteAbsentCoord W missing hmissing).card ≤ 1 :=
      Finset.card_le_one.mpr fun a ha b hb => Subtype.ext ((hall a ha).trans (hall b hb).symm)
    omega
  -- the deleted cell datum
  let D' : KuhnGridCellData m N :=
    { base := Fin.removeNth missing D.base
      k := D.k
      hk_pos := D.hk_pos
      hk_lt := hk
      subsets := KSubsetCollection.deleteAbsentCoord W missing hmissing
      hsubsets := ⟨by rw [KSubsetCollection.card_deleteAbsentCoord]; exact hWcard,
        KSubsetCollection.isSorted_deleteAbsentCoord hWsorted hmissing⟩
      sum_base_add_k := by
        have hs := Fin.sum_univ_succAbove D.base missing
        have := D.sum_base_add_k
        simp only [Fin.removeNth]
        omega }
  -- the geometric crux (`.1`-level), with `D'` the specific datum (so `D'.k = D.k`, no cast)
  have crux1 : ∀ (S : KSubset (m + 2) D.k) (hpS : missing ∉ S.1),
      Fin.removeNth missing (cellVertexMap D S).1
        = (cellVertexMap D' (KSubset.deleteAbsentCoord missing S hpS)).1 := by
    intro S hpS
    funext i
    show Fin.removeNth missing (vertexFromSubset D.base S.1) i
       = vertexFromSubset (Fin.removeNth missing D.base) (delSet missing S) i
    simp only [Fin.removeNth, vertexFromSubset, chi]
    by_cases hc : missing.succAbove i ∈ S.1
    · rw [if_pos hc, if_pos ((mem_delSet missing S i).mpr hc)]
    · rw [if_neg hc, if_neg (fun h => hc ((mem_delSet missing S i).mp h))]
  refine ⟨D', ?_⟩
  apply Finset.ext
  intro z
  constructor
  · intro hz
    rw [cellVertexMap_vertices, Finset.mem_image] at hz
    obtain ⟨S', hS', hS'z⟩ := hz
    have hS'mem : S' ∈ KSubsetCollection.deleteAbsentCoord W missing hmissing := hS'
    rw [KSubsetCollection.deleteAbsentCoord, Finset.mem_image] at hS'mem
    obtain ⟨S, _, hSeq⟩ := hS'mem
    have hcvF : cellVertexMap D S.1 ∈ F.vertices := by
      rw [hFeq, Finset.mem_image]; exact ⟨S.1, S.2, rfl⟩
    rw [KuhnGeometricGridFacet.deleteMissingFace, Finset.mem_image]
    refine ⟨⟨cellVertexMap D S.1, hcvF⟩, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    rw [← hS'z]
    show Fin.removeNth missing (cellVertexMap D S.1).1 = (cellVertexMap D' S').1
    rw [← hSeq]
    exact crux1 S.1 (hpW S.1 S.2)
  · intro hz
    rw [KuhnGeometricGridFacet.deleteMissingFace, Finset.mem_image] at hz
    obtain ⟨p, _, hpz⟩ := hz
    obtain ⟨S, hSW, hSeq⟩ := Finset.mem_image.mp
      (show p.1 ∈ W.image (cellVertexMap D) by rw [← hFeq]; exact p.2)
    rw [cellVertexMap_vertices, Finset.mem_image]
    refine ⟨KSubset.deleteAbsentCoord missing S (hpW S hSW), ?_, ?_⟩
    · show KSubset.deleteAbsentCoord missing S (hpW S hSW) ∈
        KSubsetCollection.deleteAbsentCoord W missing hmissing
      rw [KSubsetCollection.deleteAbsentCoord, Finset.mem_image]
      exact ⟨⟨S, hSW⟩, Finset.mem_attach _ _, rfl⟩
    · apply Subtype.ext
      rw [← hpz]
      show (cellVertexMap D' (KSubset.deleteAbsentCoord missing S (hpW S hSW))).1
        = Fin.removeNth missing p.1.1
      have he : Fin.removeNth missing p.1.1 = Fin.removeNth missing (cellVertexMap D S).1 :=
        congrArg (fun x : SimplexGrid (m + 1) N => Fin.removeNth missing x.1) hSeq.symm
      rw [he]
      exact (crux1 S (hpW S hSW)).symm

/-! ### Reinsertion preserves the Kuhn structure

Dual of  Reinserting the (zero, hence absent) coordinate `missing` shifts a sorted collection
in `Fin (m+1)` into `Fin (m+2)` (along `succAbove`), making `missing` the UNIQUE frozen coordinate;
completing that codim-1 wall (the c=1 same-frame extension existence) gives a top cell whose `missing`-vertex
deletion is exactly `insertZeroFace C`. -/

/-- Insert the absent coordinate `missing`: shift a `k`-subset of `Fin (m+1)` into `Fin (m+2)` along
`succAbove` (image avoids `missing`).  Inverse to `KSubset.deleteAbsentCoord missing`. -/
noncomputable def KSubset.insAbsentCoord {m k : ℕ} (missing : Fin (m + 2))
    (S : KSubset (m + 1) k) : KSubset (m + 2) k :=
  ⟨S.1.image missing.succAbove, by
    rw [Finset.card_image_of_injective _ Fin.succAbove_right_injective]; exact S.2⟩

theorem KSubset.mem_insAbsentCoord_iff {m k : ℕ} (missing : Fin (m + 2))
    (S : KSubset (m + 1) k) (j : Fin (m + 2)) :
    j ∈ (KSubset.insAbsentCoord missing S).1 ↔ ∃ i ∈ S.1, missing.succAbove i = j := by
  simp [KSubset.insAbsentCoord]

theorem KSubset.succAbove_mem_insAbsentCoord_iff {m k : ℕ} (missing : Fin (m + 2))
    (S : KSubset (m + 1) k) (i : Fin (m + 1)) :
    missing.succAbove i ∈ (KSubset.insAbsentCoord missing S).1 ↔ i ∈ S.1 := by
  rw [KSubset.mem_insAbsentCoord_iff]
  exact ⟨fun ⟨i', hi', hi'eq⟩ => Fin.succAbove_right_injective hi'eq ▸ hi', fun hi => ⟨i, hi, rfl⟩⟩

theorem KSubset.missing_notMem_insAbsentCoord {m k : ℕ} (missing : Fin (m + 2))
    (S : KSubset (m + 1) k) : missing ∉ (KSubset.insAbsentCoord missing S).1 := by
  rw [KSubset.mem_insAbsentCoord_iff]
  rintro ⟨i, _, hi⟩
  exact (Fin.succAbove_ne missing i) hi

/-- INVERSE: deleting `missing` undoes inserting it. -/
theorem KSubset.delSet_insAbsentCoord {m k : ℕ} (missing : Fin (m + 2))
    (S : KSubset (m + 1) k) :
    delSet missing (KSubset.insAbsentCoord missing S) = S.1 := by
  ext i
  rw [mem_delSet, KSubset.succAbove_mem_insAbsentCoord_iff]

theorem KSubset.insAbsentCoord_injective {m k : ℕ} (missing : Fin (m + 2)) :
    Function.Injective (KSubset.insAbsentCoord (m := m) (k := k) missing) := by
  intro S T h
  apply Subtype.ext
  have h1 : delSet missing (KSubset.insAbsentCoord missing S)
      = delSet missing (KSubset.insAbsentCoord missing T) := by rw [h]
  rwa [KSubset.delSet_insAbsentCoord, KSubset.delSet_insAbsentCoord] at h1

/-- Prefix counts transport along `succAbove`. -/
theorem KSubset.prefixCount_insAbsentCoord_succAbove {m k : ℕ} (missing : Fin (m + 2))
    (S : KSubset (m + 1) k) (t : Fin (m + 1)) :
    KSubset.prefixCount (KSubset.insAbsentCoord missing S) (missing.succAbove t)
      = KSubset.prefixCount S t := by
  show ((S.1.image missing.succAbove).filter (· ≤ missing.succAbove t)).card
     = (S.1.filter (· ≤ t)).card
  rw [Finset.filter_image, Finset.card_image_of_injective _ Fin.succAbove_right_injective]
  apply congrArg
  apply Finset.filter_congr
  intro i _
  exact Fin.succAbove_le_succAbove_iff

/-- `succAbove i ≤ missing` exactly when `i` is strictly below `missing` (the deleted index). -/
theorem KSubset.succAbove_le_missing_iff {m : ℕ} (missing : Fin (m + 2)) (i : Fin (m + 1)) :
    missing.succAbove i ≤ missing ↔ i.val < missing.val := by
  constructor
  · intro hle
    have hlt : missing.succAbove i < missing := lt_of_le_of_ne hle (Fin.succAbove_ne missing i)
    rw [Fin.succAbove_lt_iff_castSucc_lt, Fin.lt_def] at hlt
    simpa using hlt
  · intro hlt
    apply le_of_lt
    rw [Fin.succAbove_lt_iff_castSucc_lt, Fin.lt_def]
    simpa using hlt

/-- Sortedness transfers under inserting an absent coordinate (the `t = missing` case reduces, via
`succAbove i ≤ missing ↔ i.val < missing.val`, to the threshold `missing.val − 1`). -/
theorem KSubset.SortedBefore.insAbsentCoord {m k : ℕ} (missing : Fin (m + 2))
    {S T : KSubset (m + 1) k} (h : KSubset.SortedBefore S T) :
    KSubset.SortedBefore (KSubset.insAbsentCoord missing S) (KSubset.insAbsentCoord missing T) := by
  intro t
  by_cases ht : t = missing
  · rw [ht]
    have key : ∀ U : KSubset (m + 1) k,
        KSubset.prefixCount (KSubset.insAbsentCoord missing U) missing
          = (U.1.filter (fun i => i.val < missing.val)).card := by
      intro U
      show ((U.1.image missing.succAbove).filter (· ≤ missing)).card = _
      rw [Finset.filter_image, Finset.card_image_of_injective _ Fin.succAbove_right_injective]
      apply congrArg
      apply Finset.filter_congr
      intro i _
      exact KSubset.succAbove_le_missing_iff missing i
    rw [key S, key T]
    by_cases hmv : missing.val = 0
    · simp [hmv]
    · have hθ : missing.val - 1 < m + 1 := by have := missing.isLt; omega
      have hpc : ∀ U : KSubset (m + 1) k, (U.1.filter (fun i => i.val < missing.val)).card
          = KSubset.prefixCount U ⟨missing.val - 1, hθ⟩ := by
        intro U
        show _ = (U.1.filter (· ≤ ⟨missing.val - 1, hθ⟩)).card
        apply congrArg
        apply Finset.filter_congr
        intro i _
        rw [Fin.le_def]
        show i.val < missing.val ↔ i.val ≤ missing.val - 1
        omega
      rw [hpc S, hpc T]
      exact h ⟨missing.val - 1, hθ⟩
  · obtain ⟨t', rfl⟩ := Fin.exists_succAbove_eq ht
    rw [KSubset.prefixCount_insAbsentCoord_succAbove, KSubset.prefixCount_insAbsentCoord_succAbove]
    exact h t'

theorem KSubset.IsSortedPair.insAbsentCoord {m k : ℕ} (missing : Fin (m + 2))
    {S T : KSubset (m + 1) k} (h : KSubset.IsSortedPair S T) :
    KSubset.IsSortedPair (KSubset.insAbsentCoord missing S) (KSubset.insAbsentCoord missing T) :=
  h.imp (KSubset.SortedBefore.insAbsentCoord missing) (KSubset.SortedBefore.insAbsentCoord missing)

/-- Reinserting a `0` coordinate at `missing` into a Kuhn cell one dimension
down gives a Kuhn FACET (on the `missing = 0` boundary face).  Needs `1 ≤ m` (so the cell
exists and the parent collection has no frozen coordinate other than `missing`). -/
theorem KuhnGeometricGridCell.insertZeroFace_isSortedFacet {m N : ℕ} (hm : 1 ≤ m)
    (C : KuhnGeometricGridCell m N) (missing : Fin (m + 2)) :
    IsKuhnGridFacet (C.insertZeroFace missing) := by
  classical
  obtain ⟨D, hD⟩ := C.2
  set W'' := D.subsets.image (KSubset.insAbsentCoord missing) with hW''
  -- W'' facts
  have hcard : W''.card = m + 1 := by
    rw [hW'', Finset.card_image_of_injective _ (KSubset.insAbsentCoord_injective missing),
      D.hsubsets.1]
  have hne : W''.Nonempty := by
    have hDne : D.subsets.Nonempty := by rw [← Finset.card_pos, D.hsubsets.1]; omega
    rw [hW'']; exact hDne.image _
  have hsorted : KSubsetCollection.IsSorted W'' := by
    intro I hI J hJ hIJ
    rw [hW'', Finset.mem_image] at hI hJ
    obtain ⟨S, hS, rfl⟩ := hI
    obtain ⟨T', hT', rfl⟩ := hJ
    exact KSubset.IsSortedPair.insAbsentCoord missing
      (D.hsubsets.2 S hS T' hT' (fun h => hIJ (by rw [h])))
  have hcabs : missing ∈ KSubsetCollection.commonAbsent W'' := by
    rw [KSubsetCollection.mem_commonAbsent_iff]
    intro S'' hS''
    rw [hW'', Finset.mem_image] at hS''
    obtain ⟨S, _, rfl⟩ := hS''
    exact KSubset.missing_notMem_insAbsentCoord missing S
  -- the unique frozen coordinate is `missing`
  have hcpEmpty : KSubsetCollection.commonPresent D.subsets = ∅ :=
    KSubsetCollection.commonPresent_eq_empty_of_isMaximalSorted (by omega) D.hsubsets
  have hcaEmpty : KSubsetCollection.commonAbsent D.subsets = ∅ :=
    KSubsetCollection.commonAbsent_eq_empty_of_isMaximalSorted (by omega) D.hsubsets
  have hfroz : KSubsetCollection.frozenCoords W'' = {missing} := by
    apply Finset.Subset.antisymm
    · intro j hj
      rw [Finset.mem_singleton]
      by_contra hjne
      obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hjne
      rw [KSubsetCollection.frozenCoords, Finset.mem_union] at hj
      rcases hj with hcp | hca
      · have hi : i ∈ KSubsetCollection.commonPresent D.subsets := by
          rw [KSubsetCollection.mem_commonPresent_iff]
          intro S hS
          rw [← KSubset.succAbove_mem_insAbsentCoord_iff missing S i]
          exact (KSubsetCollection.mem_commonPresent_iff W'' (missing.succAbove i)).mp hcp
            (KSubset.insAbsentCoord missing S)
            (by rw [hW'']; exact Finset.mem_image_of_mem _ hS)
        rw [hcpEmpty] at hi; exact absurd hi (Finset.notMem_empty i)
      · have hi : i ∈ KSubsetCollection.commonAbsent D.subsets := by
          rw [KSubsetCollection.mem_commonAbsent_iff]
          intro S hS
          rw [← KSubset.succAbove_mem_insAbsentCoord_iff missing S i]
          exact (KSubsetCollection.mem_commonAbsent_iff W'' (missing.succAbove i)).mp hca
            (KSubset.insAbsentCoord missing S)
            (by rw [hW'']; exact Finset.mem_image_of_mem _ hS)
        rw [hcaEmpty] at hi; exact absurd hi (Finset.notMem_empty i)
    · intro j hj
      rw [Finset.mem_singleton] at hj
      rw [hj, KSubsetCollection.frozenCoords, Finset.mem_union]
      exact Or.inr hcabs
  have hone : (KSubsetCollection.frozenCoords W'').card = 1 := by rw [hfroz, Finset.card_singleton]
  -- complete the wall: a same-frame extension exists (one common-absent frozen coordinate)
  obtain ⟨T, hTmem⟩ := KSubsetCollection.sameFrameExtensions_nonempty_of_commonAbsent_oneFrozen
    hsorted hne hcard hcabs hone
  rw [KSubsetCollection.mem_sameFrameExtensions_iff] at hTmem
  -- the completed (dim m+1) cell
  let D'' : KuhnGridCellData (m + 1) N :=
    { base := Fin.insertNth missing 0 D.base
      k := D.k
      hk_pos := D.hk_pos
      hk_lt := by have := D.hk_lt; omega
      subsets := insert T W''
      hsubsets := hTmem.2
      sum_base_add_k := by
        have hs := Fin.sum_univ_succAbove (Fin.insertNth missing (0 : ℕ) D.base) missing
        rw [Fin.insertNth_apply_same] at hs
        simp only [Fin.insertNth_apply_succAbove] at hs
        have hd := D.sum_base_add_k
        omega }
  let C'' : KuhnGeometricGridCell (m + 1) N := ⟨D''.vertices, ⟨D'', rfl⟩⟩
  -- geometric crux: reinserting a vertex = cellVertexMap of the shifted subset
  have crux2 : ∀ S : KSubset (m + 1) D.k,
      cellVertexMap D'' (KSubset.insAbsentCoord missing S)
        = SimplexGrid.insertZeroCoord missing (cellVertexMap D S) := by
    intro S
    apply Subtype.ext
    funext j
    show vertexFromSubset (Fin.insertNth missing 0 D.base) (S.1.image missing.succAbove) j
       = Fin.insertNth (α := fun _ => ℕ) missing (0 : ℕ) (vertexFromSubset D.base S.1) j
    by_cases hj : j = missing
    · rw [hj]
      have hmnotin : missing ∉ S.1.image missing.succAbove := by
        rw [Finset.mem_image]; rintro ⟨i, _, hi⟩; exact Fin.succAbove_ne missing i hi
      simp [vertexFromSubset, chi, Fin.insertNth_apply_same, hmnotin]
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj
      simp only [vertexFromSubset, Fin.insertNth_apply_succAbove, chi]
      by_cases hi : i ∈ S.1
      · rw [if_pos hi, if_pos (Finset.mem_image_of_mem missing.succAbove hi)]
      · have hinmem : missing.succAbove i ∉ S.1.image missing.succAbove := by
          rw [Finset.mem_image]
          rintro ⟨i', hi', hi'eq⟩
          exact hi (Fin.succAbove_right_injective hi'eq ▸ hi')
        rw [if_neg hi, if_neg hinmem]
  -- assemble the facet
  refine ⟨C'', ?_⟩
  rw [KuhnGeometricGridCell.mem_facets_iff]
  refine ⟨cellVertexMap D'' T, ?_, ?_⟩
  · show cellVertexMap D'' T ∈ C''.vertices
    rw [show C''.vertices = D''.vertices from rfl, cellVertexMap_vertices]
    exact Finset.mem_image_of_mem _ (Finset.mem_insert_self T W'')
  · show KuhnGeometricGridCell.insertZeroFace C missing
       = C''.vertices.erase (cellVertexMap D'' T)
    have hTnotin : cellVertexMap D'' T ∉ W''.image (cellVertexMap D'') := by
      rw [Finset.mem_image]
      rintro ⟨S, hS, hSeq⟩
      exact hTmem.1 (cellVertexMap_injective D'' hSeq ▸ hS)
    rw [show C''.vertices = D''.vertices from rfl, cellVertexMap_vertices,
      show D''.subsets = insert T W'' from rfl, Finset.image_insert,
      Finset.erase_insert hTnotin]
    have hLHS : KuhnGeometricGridCell.insertZeroFace C missing
        = D.subsets.image (SimplexGrid.insertZeroCoord missing ∘ cellVertexMap D) := by
      rw [KuhnGeometricGridCell.insertZeroFace,
        show C.vertices = D.subsets.image (cellVertexMap D) by
          rw [KuhnGeometricGridCell.vertices, ← hD]; exact cellVertexMap_vertices D,
        Finset.image_image]
    have hRHS : W''.image (cellVertexMap D'')
        = D.subsets.image (SimplexGrid.insertZeroCoord missing ∘ cellVertexMap D) := by
      rw [hW'', Finset.image_image]
      exact Finset.image_congr (fun S _ => crux2 S)
    rw [hLHS, hRHS]

/-! ### The missing-face facet ↔ lower-cell bijection

Packages the (now mutually-inverse, sortedness-preserving) `deleteMissingFace`/`insertZeroFace` maps
as an `Equiv` between the facets on the `missing = 0` boundary face of dim `m+1` and the top cells of
dim `m`.  This is the bijection the `boundary_odd` induction counts across. -/

/-- Facets of the `missing = 0` boundary face of the dim-`(m+1)` Kuhn triangulation. -/
abbrev KuhnMissingFaceFacet (m N : ℕ) (missing : Fin (m + 2)) : Type :=
  {F : KuhnGeometricGridFacet (m + 1) N // ∀ x ∈ F.vertices, x.1 missing = 0}

/-- A missing-face facet deletes (drop coordinate `missing`) to a sorted top cell one dim down. -/
noncomputable def KuhnMissingFaceFacet.toLowerCell {m N : ℕ} (hm : 1 ≤ m)
    {missing : Fin (m + 2)} (Fm : KuhnMissingFaceFacet m N missing) :
    KuhnGeometricGridCell m N :=
  ⟨KuhnGeometricGridFacet.deleteMissingFace missing Fm.1 Fm.2,
    KuhnGeometricGridFacet.deleteMissingFace_isSortedCell hm missing Fm.1 Fm.2⟩

/-- A lower cell reinserts (a zero at `missing`) to a missing-face facet. -/
noncomputable def KuhnGeometricGridCell.toMissingFaceFacet {m N : ℕ} (hm : 1 ≤ m)
    (C : KuhnGeometricGridCell m N) (missing : Fin (m + 2)) :
    KuhnMissingFaceFacet m N missing :=
  ⟨⟨C.insertZeroFace missing,
      KuhnGeometricGridCell.insertZeroFace_isSortedFacet hm C missing⟩, by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp
      (show x ∈ C.vertices.image (SimplexGrid.insertZeroCoord missing) from hx)
    exact SimplexGrid.insertZeroCoord_coord_missing missing y⟩

/-- INVERSE 1: reinserting after deleting recovers the facet's vertex set. -/
theorem KuhnMissingFaceFacet.insertZeroFace_toLowerCell {m N : ℕ} (hm : 1 ≤ m)
    {missing : Fin (m + 2)} (Fm : KuhnMissingFaceFacet m N missing) :
    (KuhnMissingFaceFacet.toLowerCell hm Fm).insertZeroFace missing = Fm.1.vertices := by
  show (Fm.1.vertices.attach.image (fun p => SimplexGrid.deleteCoord missing p.1 (Fm.2 p.1 p.2))).image
      (SimplexGrid.insertZeroCoord missing) = Fm.1.vertices
  rw [Finset.image_image]
  conv_rhs => rw [← Finset.attach_image_val (s := Fm.1.vertices)]
  apply Finset.image_congr
  intro p _
  exact SimplexGrid.insertZeroCoord_deleteCoord missing p.1 (Fm.2 p.1 p.2)

/-- INVERSE 2: deleting after reinserting recovers the cell's vertex set. -/
theorem KuhnGeometricGridCell.deleteMissingFace_toMissingFaceFacet {m N : ℕ} (hm : 1 ≤ m)
    (C : KuhnGeometricGridCell m N) (missing : Fin (m + 2)) :
    KuhnGeometricGridFacet.deleteMissingFace missing
        (C.toMissingFaceFacet hm missing).1 (C.toMissingFaceFacet hm missing).2 = C.vertices := by
  apply Finset.ext
  intro z
  rw [KuhnGeometricGridFacet.deleteMissingFace, Finset.mem_image]
  constructor
  · rintro ⟨p, _, hpz⟩
    have hp1 : p.1 ∈ C.insertZeroFace missing := p.2
    rw [KuhnGeometricGridCell.insertZeroFace, Finset.mem_image] at hp1
    obtain ⟨y, hy, hyeq⟩ := hp1
    have hzy : z = y := by
      rw [← hpz]
      apply Subtype.ext
      show Fin.removeNth missing p.1.1 = y.1
      have he : Fin.removeNth missing p.1.1
          = Fin.removeNth missing (SimplexGrid.insertZeroCoord missing y).1 :=
        congrArg (fun w : SimplexGrid (m + 1) N => Fin.removeNth missing w.1) hyeq.symm
      rw [he]
      exact Fin.removeNth_insertNth (α := fun _ => ℕ) missing 0 y.1
    rw [hzy]; exact hy
  · intro hz
    refine ⟨⟨SimplexGrid.insertZeroCoord missing z, ?_⟩, Finset.mem_attach _ _, ?_⟩
    · show SimplexGrid.insertZeroCoord missing z ∈ C.insertZeroFace missing
      rw [KuhnGeometricGridCell.insertZeroFace, Finset.mem_image]
      exact ⟨z, hz, rfl⟩
    · exact SimplexGrid.deleteCoord_insertZeroCoord missing z

/-- **THE BIJECTION.**  Facets on the `missing = 0` boundary face of dim `m+1` ≃ top cells of dim
`m`.  Forward = delete coordinate `missing`; inverse = reinsert a `0` at `missing`. -/
noncomputable def missingFaceFacetEquivLowerCell {m N : ℕ} (hm : 1 ≤ m) (missing : Fin (m + 2)) :
    KuhnMissingFaceFacet m N missing ≃ KuhnGeometricGridCell m N where
  toFun Fm := KuhnMissingFaceFacet.toLowerCell hm Fm
  invFun C := KuhnGeometricGridCell.toMissingFaceFacet hm C missing
  left_inv Fm := by
    apply Subtype.ext
    apply Subtype.ext
    exact KuhnMissingFaceFacet.insertZeroFace_toLowerCell hm Fm
  right_inv C := by
    apply Subtype.ext
    exact KuhnGeometricGridCell.deleteMissingFace_toMissingFaceFacet hm C missing

/-! ### Colour reindexing across the missing-face ↔ lower-cell bijection

An upstairs Sperner labelling `L : SimplexGrid (m+1) N → Fin (m+2)` restricts to a downstairs one
`SimplexGrid m N → Fin (m+1)`: reinsert a `0` at `missing`, apply `L` (whose value is never `missing`
on that vertex, by the Sperner condition), and reindex the resulting colour `Fin (m+2)∖{missing}`
to `Fin (m+1)` via `(finSuccAboveEquiv missing).symm`. -/

/-- The downstairs labelling induced by an upstairs Sperner labelling across the `missing`-face. -/
noncomputable def missingFaceRestrictedColor {m N : ℕ} {L : SimplexGrid (m + 1) N → Fin (m + 2)}
    (hSperner : GridIsSperner L) (missing : Fin (m + 2)) :
    SimplexGrid m N → Fin (m + 1) :=
  fun x => (finSuccAboveEquiv missing).symm
    ⟨L (SimplexGrid.insertZeroCoord missing x),
      hSperner.label_ne_missing_of_onBoundaryFace missing (SimplexGrid.insertZeroCoord missing x)
        (SimplexGrid.insertZeroCoord_coord_missing missing x)⟩

/-- KEY: `missing.succAbove` of the reindexed colour recovers the upstairs colour. -/
theorem succAbove_missingFaceRestrictedColor {m N : ℕ} {L : SimplexGrid (m + 1) N → Fin (m + 2)}
    (hSperner : GridIsSperner L) (missing : Fin (m + 2)) (x : SimplexGrid m N) :
    missing.succAbove (missingFaceRestrictedColor hSperner missing x)
      = L (SimplexGrid.insertZeroCoord missing x) := by
  have h := (finSuccAboveEquiv missing).apply_symm_apply
    ⟨L (SimplexGrid.insertZeroCoord missing x),
      hSperner.label_ne_missing_of_onBoundaryFace missing (SimplexGrid.insertZeroCoord missing x)
        (SimplexGrid.insertZeroCoord_coord_missing missing x)⟩
  rw [finSuccAboveEquiv_apply] at h
  exact congrArg Subtype.val h

/-- The restricted labelling is again a Sperner labelling. -/
theorem missingFaceRestrictedColor_sperner {m N : ℕ} {L : SimplexGrid (m + 1) N → Fin (m + 2)}
    (hSperner : GridIsSperner L) (missing : Fin (m + 2)) :
    GridIsSperner (missingFaceRestrictedColor hSperner missing) := by
  intro x
  have hL := hSperner (SimplexGrid.insertZeroCoord missing x)
  have hpos : 0 < (SimplexGrid.insertZeroCoord missing x).1
      (L (SimplexGrid.insertZeroCoord missing x)) := by
    simpa [SimplexGrid.support] using hL
  have hval : (SimplexGrid.insertZeroCoord missing x).1 (L (SimplexGrid.insertZeroCoord missing x))
      = x.1 (missingFaceRestrictedColor hSperner missing x) := by
    rw [← succAbove_missingFaceRestrictedColor hSperner missing x]
    show Fin.insertNth (α := fun _ => ℕ) missing (0 : ℕ) x.1
        (missing.succAbove (missingFaceRestrictedColor hSperner missing x))
       = x.1 (missingFaceRestrictedColor hSperner missing x)
    rw [Fin.insertNth_apply_succAbove]
  rw [hval] at hpos
  simpa [SimplexGrid.support] using hpos

/-- **THE COLOUR BRIDGE.**  An upstairs facet on the `missing`-face is almost-fully-labelled for
`missing` iff the corresponding downstairs cell is fully labelled by the restricted colouring. -/
theorem missingFace_almostFullyLabeled_iff {m N : ℕ} (hm : 1 ≤ m)
    {L : SimplexGrid (m + 1) N → Fin (m + 2)} (hSperner : GridIsSperner L) (missing : Fin (m + 2))
    (C : KuhnGeometricGridCell m N) :
    Sperner.AlmostFullyLabeled L missing ((C.toMissingFaceFacet hm missing).1.vertices)
      ↔ Sperner.FullyLabeled (missingFaceRestrictedColor hSperner missing) C.vertices := by
  rw [Sperner.almostFullyLabeled_iff, Sperner.fullyLabeled_iff,
    show (C.toMissingFaceFacet hm missing).1.vertices
      = C.vertices.image (SimplexGrid.insertZeroCoord missing) from rfl]
  simp only [Sperner.mem_labelsOn_iff, Finset.mem_image]
  constructor
  · intro hAFL i
    obtain ⟨x, ⟨y, hy, hyx⟩, hLx⟩ := hAFL (missing.succAbove i) (Fin.succAbove_ne missing i)
    refine ⟨y, hy, ?_⟩
    apply Fin.succAbove_right_injective (p := missing)
    rw [succAbove_missingFaceRestrictedColor, hyx, hLx]
  · intro hFL c hc
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hc
    obtain ⟨y, hy, hLy⟩ := hFL i
    exact ⟨SimplexGrid.insertZeroCoord missing y, ⟨y, hy, rfl⟩, by
      rw [← succAbove_missingFaceRestrictedColor hSperner missing y, hLy]⟩

open scoped Classical in
/-- **FILTERED COUNT TRANSPORT.**  The number of missing-face facets that are almost-fully-labelled
for `missing` equals the number of lower cells that are fully labelled by the restricted colouring —
the bijection `missingFaceFacetEquivLowerCell` carries the colour predicate (the bridge). -/
theorem missingFace_almostFullyLabeled_count_eq_lower_fullyLabeled_count
    {m N : ℕ} (hm : 1 ≤ m) {L : SimplexGrid (m + 1) N → Fin (m + 2)}
    (hSperner : GridIsSperner L) (missing : Fin (m + 2)) :
    ((Finset.univ : Finset (KuhnMissingFaceFacet m N missing)).filter
      (fun Fm : KuhnMissingFaceFacet m N missing =>
        Sperner.AlmostFullyLabeled L missing Fm.1.vertices)).card
    =
    ((Finset.univ : Finset (KuhnGeometricGridCell m N)).filter
      (fun C : KuhnGeometricGridCell m N =>
        Sperner.FullyLabeled (missingFaceRestrictedColor hSperner missing) C.vertices)).card := by
  classical
  apply Finset.card_equiv (missingFaceFacetEquivLowerCell hm missing)
  intro Fm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hli : KuhnGeometricGridCell.toMissingFaceFacet hm
      (KuhnMissingFaceFacet.toLowerCell hm Fm) missing = Fm :=
    (missingFaceFacetEquivLowerCell hm missing).symm_apply_apply Fm
  have hv : Fm.1.vertices = (KuhnGeometricGridCell.toMissingFaceFacet hm
      (KuhnMissingFaceFacet.toLowerCell hm Fm) missing).1.vertices := by rw [hli]
  rw [hv]
  exact missingFace_almostFullyLabeled_iff hm hSperner missing
    (KuhnMissingFaceFacet.toLowerCell hm Fm)

open scoped Classical in
/-- AMBIENT ↔ SUBTYPE: the AlmostFullyLabelled facets on the `missing`-coordinate face (as an
ambient-facet `Finset`, the form produced by `kuhnBoundaryOdd_filter_eq_missing_face_filter`)
count the same as the AlmostFullyLabelled missing-face facets (as the subtype `univ`). -/
theorem missingFace_boundaryFaceFacets_count_eq_subtype_count {m N : ℕ}
    (L : SimplexGrid (m + 1) N → Fin (m + 2)) (missing : Fin (m + 2)) :
    ((kuhnBoundaryFaceFacets (m + 1) N missing).filter
      (fun F => Sperner.AlmostFullyLabeled L missing F.vertices)).card
    = ((Finset.univ : Finset (KuhnMissingFaceFacet m N missing)).filter
      (fun Fm : KuhnMissingFaceFacet m N missing =>
        Sperner.AlmostFullyLabeled L missing Fm.1.vertices)).card := by
  classical
  apply Finset.card_bij
    (fun F hF => (⟨F, (F.mem_boundaryFaceFacets_iff missing).mp (Finset.mem_filter.mp hF).1⟩
      : KuhnMissingFaceFacet m N missing))
  · intro F hF
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hF).2⟩
  · intro F _ F' _ heq
    exact congrArg Subtype.val heq
  · intro Fm hFm
    refine ⟨Fm.1, ?_, Subtype.ext rfl⟩
    rw [Finset.mem_filter]
    exact ⟨(Fm.1.mem_boundaryFaceFacets_iff missing).mpr Fm.2, (Finset.mem_filter.mp hFm).2⟩

open scoped Classical in
/-- **THE COUNT EQUALITY FOR `boundary_odd`.**  The AlmostFullyLabelled boundary-face facets count the
same as the fully-labelled lower cells (under the restricted colouring).  This is the exact form
combined with `kuhnBoundaryOdd_filter_eq_missing_face_filter` to drive the induction. -/
theorem missingFace_boundaryFaceFacets_count_eq_lower_fullyLabeled_count {m N : ℕ} (hm : 1 ≤ m)
    {L : SimplexGrid (m + 1) N → Fin (m + 2)} (hSperner : GridIsSperner L) (missing : Fin (m + 2)) :
    ((kuhnBoundaryFaceFacets (m + 1) N missing).filter
      (fun F => Sperner.AlmostFullyLabeled L missing F.vertices)).card
    = ((Finset.univ : Finset (KuhnGeometricGridCell m N)).filter
      (fun C : KuhnGeometricGridCell m N =>
        Sperner.FullyLabeled (missingFaceRestrictedColor hSperner missing) C.vertices)).card :=
  (missingFace_boundaryFaceFacets_count_eq_subtype_count L missing).trans
    (missingFace_almostFullyLabeled_count_eq_lower_fullyLabeled_count hm hSperner missing)

/-! ### Assembling `boundary_odd` from the count transport + the abstract parity double-count -/

open scoped Classical in
/-- The boundary-relevant facet count (dim `m+1`) equals the count of fully-labelled
cells one dimension down under the restricted colouring.  Pure chaining of the two count equalities. -/
theorem kuhn_boundaryRelevant_card_eq_lower_fullyLabeled_card {m N : ℕ} (hd : 2 ≤ m + 1)
    (L : SimplexGrid (m + 1) N → Fin (m + 2)) (hSperner : GridIsSperner L) (missing : Fin (m + 2)) :
    ((kuhnTriangulationCertificate hd).boundaryRelevantFacets L missing).card
    = ((Finset.univ : Finset (KuhnGeometricGridCell m N)).filter
        (fun C : KuhnGeometricGridCell m N =>
          Sperner.FullyLabeled (missingFaceRestrictedColor hSperner missing) C.vertices)).card := by
  rw [kuhnBoundaryOdd_filter_eq_missing_face_filter hd L hSperner missing,
    missingFace_boundaryFaceFacets_count_eq_lower_fullyLabeled_count (show 1 ≤ m by omega)
      hSperner missing]

open scoped Classical in
/-- **THE ABSTRACT PARITY BRIDGE** (same dimension): a certificate's boundary-relevant facet count is
odd iff its fully-labelled cell count is odd.  The relevant-incidence double count
(`Sperner.lean`) + the proved `local_parity`. -/
theorem kuhn_boundaryOdd_iff_fullyLabeled_count_odd {d N : ℕ} (hd : 2 ≤ d)
    (L : SimplexGrid d N → Fin (d + 1)) (missing : Fin (d + 1)) :
    Odd ((kuhnTriangulationCertificate hd).boundaryRelevantFacets L missing).card
    ↔ Odd ((Finset.univ : Finset (KuhnGeometricGridCell d N)).filter
        (fun C : KuhnGeometricGridCell d N => Sperner.FullyLabeled L C.vertices)).card := by
  rw [← (kuhnTriangulationCertificate hd).odd_relevantIncidences_iff_boundaryRelevant_odd
        L missing,
    (kuhnTriangulationCertificate hd).relevantIncidences_card_eq_sum_relevantFacetsOfCell
        L missing,
    show (@Finset.univ (KuhnGeometricGridCell d N)
          (kuhnTriangulationCertificate hd).fintypeCell)
        = (Finset.univ : Finset (KuhnGeometricGridCell d N))
      from Finset.ext (fun x => by simp),
    Finset.odd_sum_iff_odd_card_odd]
  simp only [kuhnGridLocalParityForCertificate hd L missing]

/-! ### The Sperner parity induction on dimension (assembly), and `boundary_odd`

The two assembled facts above —
* `kuhn_boundaryOdd_iff_fullyLabeled_count_odd` (same-dimension bridge: boundary count odd
  ⟺ rainbow-cell count odd, the `local_parity` double count), and
* `kuhn_boundaryRelevant_card_eq_lower_fullyLabeled_card` (the missing-face count drop:
  boundary count at dim `m+1` equals the rainbow-cell count at dim `m` under the restricted colour)
— combine into the classical Sperner induction on dimension: the number of fully-labelled top cells
is ODD.  The recursion bottoms out at the genuine 1-dimensional base case (the discrete IVT parity:
the path from the colour-`1` end to the colour-`0` end flips colour an odd number of times), which the
abstract certificate cannot supply (it needs `2 ≤ d`).  We isolate that base case as an explicit
hypothesis `hbase` so the entire higher-dimensional assembly is unconditional. -/

open scoped Classical in
/-- **THE SPERNER PARITY INDUCTION** (conditional only on the 1-dimensional base case `hbase`).
For every Sperner colouring of the dimension-`d` Kuhn grid (`1 ≤ d`), the number of
fully-labelled ("rainbow") top cells is ODD.  The step `d = m+1 ≥ 2` chains the boundary↔rainbow
bridge, the missing-face count equality, and Sperner-preservation
(`missingFaceRestrictedColor_sperner`), reducing dimension `m+1` to `m`. -/
theorem kuhn_fullyLabeled_count_odd_of_base
    (hbase : ∀ (N : ℕ) (L : SimplexGrid 1 N → Fin 2), GridIsSperner L →
      Odd ((Finset.univ : Finset (KuhnGeometricGridCell 1 N)).filter
        (fun C : KuhnGeometricGridCell 1 N => Sperner.FullyLabeled L C.vertices)).card)
    {d : ℕ} (hd : 1 ≤ d) :
    ∀ (N : ℕ) (L : SimplexGrid d N → Fin (d + 1)), GridIsSperner L →
      Odd ((Finset.univ : Finset (KuhnGeometricGridCell d N)).filter
        (fun C : KuhnGeometricGridCell d N => Sperner.FullyLabeled L C.vertices)).card := by
  induction d, hd using Nat.le_induction with
  | base => exact hbase
  | succ m hm ih =>
    intro N L hSperner
    have hd2 : 2 ≤ m + 1 := by omega
    refine (kuhn_boundaryOdd_iff_fullyLabeled_count_odd hd2 L 0).mp ?_
    rw [kuhn_boundaryRelevant_card_eq_lower_fullyLabeled_card hd2 L hSperner 0]
    exact ih N (missingFaceRestrictedColor hSperner 0)
      (missingFaceRestrictedColor_sperner hSperner 0)

open scoped Classical in
/-- **`boundary_odd` for the Kuhn certificate** (conditional only on `hbase`).  The boundary
double count: for any Sperner colouring, the boundary-relevant facet count is odd.  Reduces (via the
missing-face count equality) to the rainbow-cell count one dimension down, which is odd by the parity
induction. -/
theorem kuhn_boundary_odd_of_base
    (hbase : ∀ (N : ℕ) (L : SimplexGrid 1 N → Fin 2), GridIsSperner L →
      Odd ((Finset.univ : Finset (KuhnGeometricGridCell 1 N)).filter
        (fun C : KuhnGeometricGridCell 1 N => Sperner.FullyLabeled L C.vertices)).card)
    {d N : ℕ} (hd : 2 ≤ d) (L : SimplexGrid d N → Fin (d + 1)) (hSperner : GridIsSperner L)
    (missing : Fin (d + 1)) :
    Odd ((kuhnTriangulationCertificate hd).boundaryRelevantFacets L missing).card := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  rw [kuhn_boundaryRelevant_card_eq_lower_fullyLabeled_card hd L hSperner missing]
  exact kuhn_fullyLabeled_count_odd_of_base hbase (by omega : 1 ≤ m) N
    (missingFaceRestrictedColor hSperner missing)
    (missingFaceRestrictedColor_sperner hSperner missing)

open scoped Classical in
/-- **THE SPERNER OUTPUT, conditional only on the 1-dimensional base case `hbase`.**  For every
Sperner colouring of the dimension-`d` (`2 ≤ d`) Kuhn grid, a fully-labelled top cell
exists.  Discharges `boundary_odd` via `kuhn_boundary_odd_of_base`; `local_parity` is already
proved.  Once `hbase` is proved (the 1-dimensional Sperner parity), this is the unconditional finite
Sperner theorem feeding Brouwer. -/
theorem kuhn_exists_fullyLabeled_of_base
    (hbase : ∀ (N : ℕ) (L : SimplexGrid 1 N → Fin 2), GridIsSperner L →
      Odd ((Finset.univ : Finset (KuhnGeometricGridCell 1 N)).filter
        (fun C : KuhnGeometricGridCell 1 N => Sperner.FullyLabeled L C.vertices)).card)
    {d N : ℕ} (hd : 2 ≤ d) (color : SimplexGrid d N → Fin (d + 1)) (hSperner : GridIsSperner color)
    (missing : Fin (d + 1)) :
    ∃ C : KuhnGeometricGridCell d N, Sperner.FullyLabeled color C.vertices :=
  kuhn_exists_fullyLabeled_of_boundaryOdd hd color missing
    (kuhn_boundary_odd_of_base hbase hd color hSperner missing)

/-! ### The 1-dimensional Sperner base case `hbase`

The dimension induction bottoms out at `d = 1`, which the certificate cannot reach (it needs
`2 ≤ d`).  In dimension 1 the Kuhn cells are exactly the `N` edges of the path
`P j = (j, N−j)` (`j = 0,…,N`), a fully-labelled edge is one whose endpoints have different
colours, and the Sperner condition pins `L(P₀) = 1`, `L(P_N) = 0`, so the number of colour changes
along the path is odd.  We build this in three layers: (A) binary path parity (no geometry),
(B) the 1-D vertex parametrisation + Sperner endpoint colours, (C) the 1-D cell enumeration. -/

namespace OneDimSperner

/-! #### Layer A — binary path parity (no geometry) -/

/-- The `Fin 2` per-step parity arithmetic: combining the running flip parity `if a = b then 0 else 1`
with one more step `if b ≠ c then 1 else 0` gives the new endpoint parity `if a = c then 0 else 1`.
Decidable (the `a ≠ b`, `b ≠ c`, `a ≠ c` triple is impossible in `Fin 2`). -/
theorem flip_arith : ∀ a b c : Fin 2,
    ((if a = b then (0 : ℕ) else 1) + if b ≠ c then 1 else 0) % 2 = if a = c then 0 else 1 := by
  decide

/-- One induction step of the path-parity, with the running count abstracted to `m`. -/
theorem step_aux (a b c : Fin 2) (m : ℕ) (hm : m % 2 = if a = b then 0 else 1) :
    (m + if b ≠ c then 1 else 0) % 2 = if a = c then 0 else 1 := by
  have key := flip_arith a b c
  omega

/-- Parity of the adjacent colour changes of a binary sequence `f : ℕ → Fin 2` over `range N`:
it equals `0` if the endpoints agree and `1` if they differ.  Telescoping induction; the per-step
case analysis is the `Fin 2` pigeonhole packaged in `flip_arith`. -/
theorem range_adjacent_ne_card_mod_two (f : ℕ → Fin 2) (N : ℕ) :
    ((Finset.range N).filter (fun j => f j ≠ f (j + 1))).card % 2
      = (if f 0 = f N then 0 else 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.card_filter, Finset.sum_range_succ, ← Finset.card_filter]
    exact step_aux (f 0) (f N) (f (N + 1)) _ ih

/-- The `Fin N`-indexed adjacent-flip count of `g : Fin (N+1) → Fin 2` is odd when the two
endpoints differ.  (Transfers `range_adjacent_ne_card_mod_two` along `Fin.sum_univ_eq_sum_range`.) -/
theorem odd_fin_adjacent_ne {N : ℕ} (g : Fin (N + 1) → Fin 2)
    (hne : g 0 ≠ g (Fin.last N)) :
    Odd ((Finset.univ : Finset (Fin N)).filter
      (fun j => g j.castSucc ≠ g j.succ)).card := by
  classical
  set f : ℕ → Fin 2 := fun n => g ⟨min n N, by omega⟩ with hf
  have hval : ∀ i : Fin (N + 1), f (i : ℕ) = g i := by
    intro i
    have hi := i.isLt
    show g ⟨min (i : ℕ) N, _⟩ = g i
    congr 1
    apply Fin.ext
    show min (i : ℕ) N = (i : ℕ)
    omega
  have h0 : f 0 = g 0 := hval 0
  have hL : f N = g (Fin.last N) := by
    simpa [Fin.val_last] using hval (Fin.last N)
  have hfne : f 0 ≠ f N := by rw [h0, hL]; exact hne
  have hcard : ((Finset.univ : Finset (Fin N)).filter
      (fun j => g j.castSucc ≠ g j.succ)).card
      = ((Finset.range N).filter (fun i => f i ≠ f (i + 1))).card := by
    rw [Finset.card_filter, Finset.card_filter,
      ← Fin.sum_univ_eq_sum_range (fun i => if f i ≠ f (i + 1) then 1 else 0) N]
    apply Finset.sum_congr rfl
    intro j _
    have hc : g j.castSucc = f (j : ℕ) := by
      simpa [Fin.val_castSucc] using (hval j.castSucc).symm
    have hs : g j.succ = f ((j : ℕ) + 1) := by
      simpa [Fin.val_succ] using (hval j.succ).symm
    rw [hc, hs]
  rw [hcard, Nat.odd_iff, range_adjacent_ne_card_mod_two f N, if_neg hfne]

/-! #### Layer B — the 1-D path vertices and Sperner endpoint colours -/

/-- In `Fin 2`, `≠ 0` means `= 1`. -/
theorem fin2_ne_zero_eq_one : ∀ x : Fin 2, x ≠ 0 → x = 1 := by decide

/-- In `Fin 2`, `≠ 1` means `= 0`. -/
theorem fin2_ne_one_eq_zero : ∀ x : Fin 2, x ≠ 1 → x = 0 := by decide

/-- The `j`-th lattice point of the 1-dimensional simplex grid: `P j = (j, N − j)`. -/
def pathVertex (N : ℕ) (j : Fin (N + 1)) : SimplexGrid 1 N :=
  ⟨fun i => if i = 0 then (j : ℕ) else N - (j : ℕ), by
    have hj := j.isLt
    simp [Fin.sum_univ_two]
    omega⟩

@[simp] theorem pathVertex_apply {N : ℕ} (j : Fin (N + 1)) (i : Fin 2) :
    (pathVertex N j).1 i = if i = 0 then (j : ℕ) else N - (j : ℕ) := rfl

/-- The left endpoint `P 0 = (0, N)` has colour `1` (its only positive coordinate is `1`). -/
theorem pathVertex_zero_colour {N : ℕ} (hN : 0 < N) {L : SimplexGrid 1 N → Fin 2}
    (hS : GridIsSperner L) : L (pathVertex N 0) = 1 := by
  apply fin2_ne_zero_eq_one
  intro h0
  have hmem := hS (pathVertex N 0)
  rw [SimplexGrid.support, Finset.mem_filter] at hmem
  have hpos := hmem.2
  rw [h0] at hpos
  simp at hpos

/-- The right endpoint `P N = (N, 0)` has colour `0` (its only positive coordinate is `0`). -/
theorem pathVertex_last_colour {N : ℕ} (hN : 0 < N) {L : SimplexGrid 1 N → Fin 2}
    (hS : GridIsSperner L) : L (pathVertex N (Fin.last N)) = 0 := by
  apply fin2_ne_one_eq_zero
  intro h1
  have hmem := hS (pathVertex N (Fin.last N))
  rw [SimplexGrid.support, Finset.mem_filter] at hmem
  have hpos := hmem.2
  rw [h1] at hpos
  simp [Fin.val_last] at hpos

/-- The two endpoints of the 1-D path have different colours. -/
theorem pathVertex_endpoints_ne {N : ℕ} (hN : 0 < N) {L : SimplexGrid 1 N → Fin 2}
    (hS : GridIsSperner L) :
    L (pathVertex N 0) ≠ L (pathVertex N (Fin.last N)) := by
  rw [pathVertex_zero_colour hN hS, pathVertex_last_colour hN hS]
  decide

theorem pathVertex_coord_zero {N : ℕ} (j : Fin (N + 1)) :
    (pathVertex N j).1 0 = (j : ℕ) := by simp

theorem pathVertex_injective {N : ℕ} : Function.Injective (pathVertex N) := by
  intro a b h
  have hcoord : (pathVertex N a).1 0 = (pathVertex N b).1 0 := by rw [h]
  rw [pathVertex_coord_zero, pathVertex_coord_zero] at hcoord
  exact Fin.ext hcoord

/-! #### Layer C — the 1-D cell enumeration -/

/-- The cell datum of the `j`-th edge: base `(j, N−1−j)`, `k = 1`, all 1-subsets. -/
def edgeCellData {N : ℕ} (j : Fin N) : KuhnGridCellData 1 N where
  base := fun i => if i = 0 then (j : ℕ) else N - 1 - (j : ℕ)
  k := 1
  hk_pos := one_pos
  hk_lt := one_lt_two
  subsets := Finset.univ
  hsubsets := by decide
  sum_base_add_k := by
    have hj := j.isLt
    simp [Fin.sum_univ_two]
    omega

/-- The `j`-th edge cell `{P j₊₁, P j}` of the 1-dimensional triangulation. -/
noncomputable def edgeCell {N : ℕ} (j : Fin N) : KuhnGeometricGridCell 1 N :=
  ⟨(edgeCellData j).vertices, ⟨edgeCellData j, rfl⟩⟩

/-- The two vertices of the `j`-th edge cell are exactly the path points `P (j+1)` and `P j`. -/
theorem edgeCellData_vertices {N : ℕ} (j : Fin N) :
    (edgeCellData j).vertices = {pathVertex N j.succ, pathVertex N j.castSucc} := by
  have hj := j.isLt
  have h0 : ∀ p : ({0} : Finset (Fin 2)).card = 1,
      cellVertexMap (edgeCellData j) ⟨{0}, p⟩ = pathVertex N j.succ := by
    intro p
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [cellVertexMap, vertexFromSubset, chi, edgeCellData, pathVertex, Fin.val_succ] <;> omega
  have h1 : ∀ p : ({1} : Finset (Fin 2)).card = 1,
      cellVertexMap (edgeCellData j) ⟨{1}, p⟩ = pathVertex N j.castSucc := by
    intro p
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [cellVertexMap, vertexFromSubset, chi, edgeCellData, pathVertex, Fin.val_castSucc] <;> omega
  have hne : pathVertex N j.succ ≠ pathVertex N j.castSucc := by
    intro h
    have he := pathVertex_injective h
    have hv : ((j.succ : Fin (N + 1)) : ℕ) = ((j.castSucc : Fin (N + 1)) : ℕ) := congrArg Fin.val he
    rw [Fin.val_succ, Fin.val_castSucc] at hv
    omega
  have hcard2 : ({pathVertex N j.succ, pathVertex N j.castSucc} : Finset (SimplexGrid 1 N)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have hsub : ({pathVertex N j.succ, pathVertex N j.castSucc} : Finset (SimplexGrid 1 N))
      ⊆ (edgeCellData j).vertices := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [cellVertexMap_vertices]
    rcases hx with hx | hx
    · subst hx
      exact Finset.mem_image.mpr ⟨(⟨{0}, by decide⟩ : KSubset 2 1), Finset.mem_univ _, h0 _⟩
    · subst hx
      exact Finset.mem_image.mpr ⟨(⟨{1}, by decide⟩ : KSubset 2 1), Finset.mem_univ _, h1 _⟩
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  have hv : (edgeCellData j).vertices.card = 2 := (edgeCellData j).vertices_card
  omega

@[simp] theorem edgeCell_vertices {N : ℕ} (j : Fin N) :
    (edgeCell j).vertices = {pathVertex N j.succ, pathVertex N j.castSucc} :=
  edgeCellData_vertices j

/-- In `Fin 2`, the whole universe is contained in a pair iff the pair is distinct. -/
theorem fin2_univ_subset_pair : ∀ x y : Fin 2,
    (Finset.univ ⊆ ({x, y} : Finset (Fin 2))) ↔ x ≠ y := by decide

/-- A two-element vertex set is fully labelled (over `Fin 2`) iff its two labels differ. -/
theorem fullyLabeled_pair_iff {N : ℕ} (L : SimplexGrid 1 N → Fin 2)
    (a b : SimplexGrid 1 N) :
    Sperner.FullyLabeled L {a, b} ↔ L a ≠ L b := by
  have himg : Sperner.labelsOn L {a, b} = ({L a, L b} : Finset (Fin 2)) := by
    ext c
    simp only [Sperner.labelsOn, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨a, Or.inl rfl, rfl⟩
      · exact ⟨b, Or.inr rfl, rfl⟩
  rw [Sperner.FullyLabeled, himg]
  exact fin2_univ_subset_pair (L a) (L b)

/-- An edge cell is fully labelled iff its two path endpoints have different colours. -/
theorem edgeCell_fullyLabeled_iff {N : ℕ} (L : SimplexGrid 1 N → Fin 2) (j : Fin N) :
    Sperner.FullyLabeled L (edgeCell j).vertices ↔
      L (pathVertex N j.castSucc) ≠ L (pathVertex N j.succ) := by
  rw [edgeCell_vertices, fullyLabeled_pair_iff]
  exact ne_comm

theorem edgeCell_injective {N : ℕ} : Function.Injective (edgeCell (N := N)) := by
  intro a b h
  have hv : (edgeCell a).vertices = (edgeCell b).vertices :=
    congrArg KuhnGeometricGridCell.vertices h
  rw [edgeCell_vertices, edgeCell_vertices] at hv
  have hmem : pathVertex N a.castSucc
      ∈ ({pathVertex N b.succ, pathVertex N b.castSucc} : Finset (SimplexGrid 1 N)) := by
    rw [← hv]; simp
  rw [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hcs | hcs
  · exfalso
    have he := pathVertex_injective hcs
    have ha : (a : ℕ) = (b : ℕ) + 1 := by
      have := congrArg Fin.val he; rwa [Fin.val_castSucc, Fin.val_succ] at this
    have hmem2 : pathVertex N a.succ
        ∈ ({pathVertex N b.succ, pathVertex N b.castSucc} : Finset (SimplexGrid 1 N)) := by
      rw [← hv]; simp
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem2
    rcases hmem2 with h2 | h2
    · have := congrArg Fin.val (pathVertex_injective h2)
      rw [Fin.val_succ, Fin.val_succ] at this; omega
    · have := congrArg Fin.val (pathVertex_injective h2)
      rw [Fin.val_succ, Fin.val_castSucc] at this; omega
  · have hval := congrArg Fin.val (pathVertex_injective hcs)
    rw [Fin.val_castSucc, Fin.val_castSucc] at hval
    exact Fin.ext hval

theorem edgeCell_surjective {N : ℕ} (C : KuhnGeometricGridCell 1 N) :
    ∃ j : Fin N, edgeCell j = C := by
  obtain ⟨S, D, hD⟩ := C
  obtain ⟨base, k, hkpos, hklt, subsets, hsub, hsum⟩ := D
  have hk1 : k = 1 := by omega
  subst hk1
  have hsubsets : subsets = (Finset.univ : Finset (KSubset 2 1)) :=
    Finset.eq_univ_of_card subsets (by rw [hsub.1]; decide)
  subst hsubsets
  rw [Fin.sum_univ_two] at hsum
  have hbase0 : base 0 < N := by omega
  refine ⟨⟨base 0, hbase0⟩, ?_⟩
  apply Subtype.ext
  show (edgeCellData ⟨base 0, hbase0⟩).vertices = S
  rw [← hD, cellVertexMap_vertices, cellVertexMap_vertices]
  have hbase_eq : (edgeCellData ⟨base 0, hbase0⟩).base = base := by
    funext i
    fin_cases i
    · simp [edgeCellData]
    · simp [edgeCellData]; omega
  apply Finset.image_congr
  intro T _
  apply Subtype.ext
  show vertexFromSubset (edgeCellData ⟨base 0, hbase0⟩).base T.1 = vertexFromSubset base T.1
  rw [hbase_eq]

open scoped Classical in
/-- **THE 1-DIMENSIONAL SPERNER BASE CASE.**  For every Sperner colouring of the 1-D Kuhn
grid, the number of fully-labelled (rainbow) edge cells is odd.  `N = 0` is vacuous (no Sperner
colouring); for `N > 0` the cells biject with the `N` path edges (`edgeCell`) and the rainbow count
is the path's colour-change count, odd by `odd_fin_adjacent_ne`. -/
theorem oneDimensional_base (N : ℕ) (L : SimplexGrid 1 N → Fin 2) (hS : GridIsSperner L) :
    Odd ((Finset.univ : Finset (KuhnGeometricGridCell 1 N)).filter
      (fun C : KuhnGeometricGridCell 1 N => Sperner.FullyLabeled L C.vertices)).card := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; exact absurd hS (not_gridIsSperner_zero_mesh L)
  let e : Fin N ≃ KuhnGeometricGridCell 1 N :=
    Equiv.ofBijective _ ⟨edgeCell_injective, edgeCell_surjective⟩
  have hcount : ((Finset.univ : Finset (KuhnGeometricGridCell 1 N)).filter
        (fun C : KuhnGeometricGridCell 1 N => Sperner.FullyLabeled L C.vertices)).card
      = ((Finset.univ : Finset (Fin N)).filter
        (fun j => L (pathVertex N j.castSucc) ≠ L (pathVertex N j.succ))).card := by
    refine (Finset.card_equiv e ?_).symm
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (edgeCell_fullyLabeled_iff L j).symm
  rw [hcount]
  exact odd_fin_adjacent_ne (fun k => L (pathVertex N k)) (pathVertex_endpoints_ne hN hS)

end OneDimSperner
end BarycentricFreudenthal
end SpernerFreudenthal
end EcoLean
