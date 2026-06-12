import EcoLean.GameTheory.MathLanguage.Sperner.Kuhn.KSubsetCombinatorics

/-! Geometric cells and facets of the Freudenthal simplex grid, the lattice-completion
completions API, and the door property `incidentCells_card_eq_one_or_two` (every facet is shared by
one or two cells).  The boundary ↔ interior degree classification built on top of this is in
`Incidence.lean`. -/

namespace EcoLean
namespace SpernerFreudenthal
namespace BarycentricFreudenthal
open Finset
/-- The cell datum for the Kuhn cells. -/
structure KuhnGridCellData (d N : ℕ) where
  base : Fin (d + 1) → ℕ
  k : ℕ
  hk_pos : 0 < k
  hk_lt : k < d + 1
  subsets : Finset (KSubset (d + 1) k)
  hsubsets : KSubsetCollection.IsMaximalSorted subsets
  sum_base_add_k : (∑ i, base i) + k = N

noncomputable def KuhnGridCellData.vertices {d N : ℕ}
    (D : KuhnGridCellData d N) : Finset (SimplexGrid d N) :=
  D.subsets.image fun S =>
    ⟨vertexFromSubset D.base S.1,
      vertexFromSubset_sum_eq D.base S.1 S.2 D.sum_base_add_k⟩

theorem KuhnGridCellData.vertices_card {d N : ℕ}
    (D : KuhnGridCellData d N) :
    D.vertices.card = d + 1 := by
  rw [KuhnGridCellData.vertices,
    Finset.card_image_of_injective _
      (fun S T h => Subtype.ext
        (vertexFromSubset_injective D.base (Subtype.ext_iff.mp h)))]
  exact D.hsubsets.1

/-- The surviving subset collection after erasing one vertex (the wall, in `D`'s
frame).  The wall-level frozen bound `frozenCoords (erasedSubsets) ≤ 1` is the open
target (see `SortedFrozenStatus`); the previous CONDITIONAL version was removed as it
rested on a false/circular engine. -/
def KuhnGridCellData.erasedSubsets {d N : ℕ}
    (D : KuhnGridCellData d N) (S₀ : KSubset (d + 1) D.k) :
    Finset (KSubset (d + 1) D.k) :=
  D.subsets.erase S₀

/-- Cell-level wall bound (needs `2 ≤ d`, i.e. `3 ≤ d+1`).  UNCONDITIONAL. -/
theorem KuhnGridCellData.erasedSubsets_frozen_card_le_one {d N : ℕ}
    (hd : 2 ≤ d) (D : KuhnGridCellData d N)
    {S₀ : KSubset (d + 1) D.k} (hS₀ : S₀ ∈ D.subsets) :
    (KSubsetCollection.commonPresent (D.erasedSubsets S₀)).card +
      (KSubsetCollection.commonAbsent (D.erasedSubsets S₀)).card ≤ 1 :=
  KSubsetCollection.card_commonPresent_add_commonAbsent_le_one_of_erase_maximalSorted
    (by omega) D.hk_pos D.hk_lt D.hsubsets hS₀

namespace SortedSanity

/-- `{01, 02, 03, 13}` — a maximal sorted collection of 2-subsets of `Fin 4`
(NOT a cyclic-interval family; `{01,23}` and `{03,12}` are the crossing,
non-sorted pairs, both avoided here). Its four `base + χ(S)` vertices are
`(1,1,0,0), (1,0,1,0), (1,0,0,1), (0,1,0,1)` — an honest tetrahedron for the
`d=3, k=2` cell. -/
def tetSubsets : Finset (KSubset 4 2) :=
  {⟨{0, 1}, by decide⟩, ⟨{0, 2}, by decide⟩, ⟨{0, 3}, by decide⟩, ⟨{1, 3}, by decide⟩}

def tetCell : KuhnGridCellData 3 2 where
  base := fun _ => 0
  k := 2
  hk_pos := by norm_num
  hk_lt := by norm_num
  subsets := tetSubsets
  hsubsets := by decide
  sum_base_add_k := by decide

/-- The corrected model represents the `d=3, k=2` tetrahedron that the cyclic
model missed: a genuine cell with four distinct vertices. -/
theorem d3_k2_sorted_tetrahedron_exists :
    ∃ D : KuhnGridCellData 3 2, D.vertices.card = 4 :=
  ⟨tetCell, tetCell.vertices_card⟩

end SortedSanity

/-! ### Theorem-facing layer on the sorted-cell model -/

/-- Theorem-facing sorted small simplex. -/
def IsKuhnGridSmallSimplex {d N : ℕ}
    (S : Finset (SimplexGrid d N)) : Prop :=
  ∃ D : KuhnGridCellData d N, D.vertices = S

/-- Canonical cells of the Kuhn triangulation. -/
abbrev KuhnGeometricGridCell (d N : ℕ) :=
  {S : Finset (SimplexGrid d N) // IsKuhnGridSmallSimplex S}

/-- A vertex coordinate of a sorted cell is `base i` or `base i + 1`. -/
theorem KuhnGridCellData.coord_eq_base_or_base_add_one {d N : ℕ}
    (D : KuhnGridCellData d N) {x : SimplexGrid d N}
    (hx : x ∈ D.vertices) (i : Fin (d + 1)) :
    x.1 i = D.base i ∨ x.1 i = D.base i + 1 := by
  classical
  rw [KuhnGridCellData.vertices, Finset.mem_image] at hx
  obtain ⟨S, -, rfl⟩ := hx
  show vertexFromSubset D.base S.1 i = D.base i ∨
    vertexFromSubset D.base S.1 i = D.base i + 1
  unfold vertexFromSubset chi
  by_cases h : i ∈ S.1 <;> simp [h]

/-- GENERALIZED FRAME IDENTITY: the coordinatewise minimum of `base + χ(S)` over `S` in ANY
nonempty collection is `base + χ(commonPresent)` (used for the erased wall, which is not a cell). -/
theorem min_coord_eq_gen {d k : ℕ} (base : Fin (d + 1) → ℕ)
    (A : Finset (KSubset (d + 1) k)) (hne : A.Nonempty) (i : Fin (d + 1)) :
    (A.image (fun S => base i + chi S.1 i)).min' (hne.image _) =
      base i + (if i ∈ KSubsetCollection.commonPresent A then 1 else 0) := by
  classical
  apply le_antisymm
  · by_cases hi : i ∈ KSubsetCollection.commonPresent A
    · rw [if_pos hi]
      obtain ⟨S, hS⟩ := hne
      have hmem : base i + 1 ∈ A.image (fun S => base i + chi S.1 i) := by
        rw [Finset.mem_image]; refine ⟨S, hS, ?_⟩
        rw [chi, if_pos ((KSubsetCollection.mem_commonPresent_iff A i).mp hi S hS)]
      exact Finset.min'_le _ _ hmem
    · rw [if_neg hi]
      rw [KSubsetCollection.commonPresent, Finset.mem_filter] at hi
      push_neg at hi
      obtain ⟨S, hS, hiS⟩ := hi (Finset.mem_univ i)
      have hmem : base i ∈ A.image (fun S => base i + chi S.1 i) := by
        rw [Finset.mem_image]; exact ⟨S, hS, by simp [chi, hiS]⟩
      exact Finset.min'_le _ _ hmem
  · apply Finset.le_min'
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨S, hS, rfl⟩ := hy
    by_cases hi : i ∈ KSubsetCollection.commonPresent A
    · rw [if_pos hi, chi, if_pos ((KSubsetCollection.mem_commonPresent_iff A i).mp hi S hS)]
    · rw [if_neg hi, chi]; split <;> omega

/-- FRAME IDENTITY: the coordinatewise minimum over a cell's vertices is
`base + χ(commonPresent)` — a coordinate sits one above `base` exactly when it is present in
every subset. -/
theorem KuhnGridCellData.min_coord_eq {d N : ℕ}
    (D : KuhnGridCellData d N) (hne : D.vertices.Nonempty) (i : Fin (d + 1)) :
    (D.vertices.image fun x => x.1 i).min' (hne.image _) =
      D.base i + (if i ∈ KSubsetCollection.commonPresent D.subsets then 1 else 0) := by
  classical
  have himg : ∀ y, y ∈ D.vertices.image (fun x => x.1 i) ↔
      ∃ S ∈ D.subsets, D.base i + chi S.1 i = y := by
    intro y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [KuhnGridCellData.vertices, Finset.mem_image] at hx
      obtain ⟨S, hS, rfl⟩ := hx
      exact ⟨S, hS, rfl⟩
    · rintro ⟨S, hS, rfl⟩
      exact ⟨⟨vertexFromSubset D.base S.1, _⟩, Finset.mem_image_of_mem _ hS, rfl⟩
  have hsubne : D.subsets.Nonempty := by
    rw [← Finset.card_pos, D.hsubsets.1]; omega
  apply le_antisymm
  · by_cases hi : i ∈ KSubsetCollection.commonPresent D.subsets
    · rw [if_pos hi]
      obtain ⟨S, hS⟩ := hsubne
      have hmem : D.base i + 1 ∈ D.vertices.image (fun x => x.1 i) := by
        rw [himg]; refine ⟨S, hS, ?_⟩
        rw [chi, if_pos ((KSubsetCollection.mem_commonPresent_iff D.subsets i).mp hi S hS)]
      exact Finset.min'_le _ _ hmem
    · rw [if_neg hi]
      rw [KSubsetCollection.commonPresent, Finset.mem_filter] at hi
      push_neg at hi
      obtain ⟨S, hS, hiS⟩ := hi (Finset.mem_univ i)
      have hmem : D.base i ∈ D.vertices.image (fun x => x.1 i) := by
        rw [himg]; exact ⟨S, hS, by simp [chi, hiS]⟩
      exact Finset.min'_le _ _ hmem
  · apply Finset.le_min'
    intro y hy
    rw [himg] at hy
    obtain ⟨S, hS, rfl⟩ := hy
    by_cases hi : i ∈ KSubsetCollection.commonPresent D.subsets
    · rw [if_pos hi, chi, if_pos ((KSubsetCollection.mem_commonPresent_iff D.subsets i).mp hi S hS)]
    · rw [if_neg hi, chi]; split <;> omega

theorem IsKuhnGridSmallSimplex.card {d N : ℕ}
    {S : Finset (SimplexGrid d N)}
    (hS : IsKuhnGridSmallSimplex S) :
    S.card = d + 1 := by
  classical
  rcases hS with ⟨D, rfl⟩
  exact D.vertices_card

theorem IsKuhnGridSmallSimplex.mesh {d N : ℕ}
    {S : Finset (SimplexGrid d N)}
    (hS : IsKuhnGridSmallSimplex S) :
    ∀ x ∈ S, ∀ y ∈ S, ∀ i : Fin (d + 1),
      Int.natAbs ((x.1 i : ℤ) - (y.1 i : ℤ)) ≤ 1 := by
  classical
  rcases hS with ⟨D, rfl⟩
  intro x hx y hy i
  rcases D.coord_eq_base_or_base_add_one hx i with hxi | hxi <;>
    rcases D.coord_eq_base_or_base_add_one hy i with hyi | hyi <;>
    rw [hxi, hyi] <;> omega

namespace KuhnGeometricGridCell

def vertices {d N : ℕ} (C : KuhnGeometricGridCell d N) :
    Finset (SimplexGrid d N) := C.1

theorem vertices_card {d N : ℕ} (C : KuhnGeometricGridCell d N) :
    C.vertices.card = d + 1 :=
  IsKuhnGridSmallSimplex.card C.2

theorem mesh {d N : ℕ} (C : KuhnGeometricGridCell d N) :
    ∀ x ∈ C.vertices, ∀ y ∈ C.vertices, ∀ i : Fin (d + 1),
      Int.natAbs ((x.1 i : ℤ) - (y.1 i : ℤ)) ≤ 1 :=
  IsKuhnGridSmallSimplex.mesh C.2

noncomputable def facets {d N : ℕ} (C : KuhnGeometricGridCell d N) :
    Finset (Finset (SimplexGrid d N)) :=
  C.vertices.image fun x => C.vertices.erase x

theorem mem_facets_iff {d N : ℕ} (C : KuhnGeometricGridCell d N)
    (F : Finset (SimplexGrid d N)) :
    F ∈ C.facets ↔ ∃ x ∈ C.vertices, F = C.vertices.erase x := by
  classical
  rw [KuhnGeometricGridCell.facets, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

theorem facet_card {d N : ℕ} (C : KuhnGeometricGridCell d N)
    {F : Finset (SimplexGrid d N)} (hF : F ∈ C.facets) :
    F.card = d := by
  classical
  rcases (C.mem_facets_iff F).mp hF with ⟨x, hx, rfl⟩
  simp [Finset.card_erase_of_mem hx, C.vertices_card]

theorem facet_subset {d N : ℕ} (C : KuhnGeometricGridCell d N)
    {F : Finset (SimplexGrid d N)} (hF : F ∈ C.facets) :
    F ⊆ C.vertices := by
  classical
  rcases (C.mem_facets_iff F).mp hF with ⟨x, hx, rfl⟩
  intro y hy
  exact (Finset.mem_erase.mp hy).2

end KuhnGeometricGridCell

/-- Theorem-facing sorted facets. -/
def IsKuhnGridFacet {d N : ℕ}
    (F : Finset (SimplexGrid d N)) : Prop :=
  ∃ C : KuhnGeometricGridCell d N, F ∈ C.facets

abbrev KuhnGeometricGridFacet (d N : ℕ) :=
  {F : Finset (SimplexGrid d N) // IsKuhnGridFacet F}

namespace KuhnGeometricGridFacet

def vertices {d N : ℕ} (F : KuhnGeometricGridFacet d N) :
    Finset (SimplexGrid d N) := F.1

theorem vertices_card {d N : ℕ} (F : KuhnGeometricGridFacet d N) :
    F.vertices.card = d := by
  classical
  rcases F.2 with ⟨C, hC⟩
  exact C.facet_card hC

end KuhnGeometricGridFacet

/-! ### Finite enumeration and incident cells for sorted cells -/

/-- Finite parameterization of a sorted cell (`k : Fin (d+1)`, bounded base). -/
structure KuhnGridCellParam (d N : ℕ) where
  base : BoundedBaseVec d N
  k : Fin (d + 1)
  hk_pos : 0 < k.val
  subsets : Finset (KSubset (d + 1) k.val)
  hsubsets : KSubsetCollection.IsMaximalSorted subsets
  sum_base_add_k : (∑ i, (base i).val) + k.val = N

noncomputable instance KuhnGridCellParam.instFintype (d N : ℕ) :
    Fintype (KuhnGridCellParam d N) :=
  Fintype.ofInjective
    (fun P : KuhnGridCellParam d N =>
      (P.k, P.base, P.subsets.image Subtype.val))
    (by
      intro P Q h
      obtain ⟨pbase, pk, phpos, psubsets, phsub, psum⟩ := P
      obtain ⟨qbase, qk, qhpos, qsubsets, qhsub, qsum⟩ := Q
      simp only [Prod.mk.injEq] at h
      obtain ⟨hk, hbase, hsub⟩ := h
      subst hk
      subst hbase
      obtain rfl : psubsets = qsubsets :=
        Finset.image_injective Subtype.val_injective hsub
      rfl)

noncomputable def KuhnGridCellParam.toData {d N : ℕ}
    (P : KuhnGridCellParam d N) :
    KuhnGridCellData d N where
  base := fun i => (P.base i).val
  k := P.k.val
  hk_pos := P.hk_pos
  hk_lt := P.k.isLt
  subsets := P.subsets
  hsubsets := P.hsubsets
  sum_base_add_k := P.sum_base_add_k

theorem KuhnGridCellData.base_le_N {d N : ℕ}
    (D : KuhnGridCellData d N) (i : Fin (d + 1)) :
    D.base i ≤ N := by
  have h1 : D.base i ≤ ∑ j, D.base j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h2 := D.sum_base_add_k
  omega

noncomputable def KuhnGridCellData.toParam {d N : ℕ}
    (D : KuhnGridCellData d N) :
    KuhnGridCellParam d N where
  base := fun i => ⟨D.base i, Nat.lt_succ_of_le (D.base_le_N i)⟩
  k := ⟨D.k, D.hk_lt⟩
  hk_pos := D.hk_pos
  subsets := D.subsets
  hsubsets := D.hsubsets
  sum_base_add_k := by simpa using D.sum_base_add_k

theorem KuhnGridCellData.toParam_vertices {d N : ℕ}
    (D : KuhnGridCellData d N) :
    D.toParam.toData.vertices = D.vertices := rfl

noncomputable def allKuhnGeometricGridCells (d N : ℕ) :
    Finset (KuhnGeometricGridCell d N) :=
  Finset.univ.image fun P : KuhnGridCellParam d N =>
    (⟨P.toData.vertices, ⟨P.toData, rfl⟩⟩ : KuhnGeometricGridCell d N)

theorem KuhnGeometricGridCell.mem_all {d N : ℕ}
    (C : KuhnGeometricGridCell d N) :
    C ∈ allKuhnGeometricGridCells d N := by
  classical
  rcases C.2 with ⟨D, hD⟩
  rw [allKuhnGeometricGridCells, Finset.mem_image]
  refine ⟨D.toParam, Finset.mem_univ _, ?_⟩
  apply Subtype.ext
  exact hD

namespace KuhnGeometricGridFacet

noncomputable def incidentCells {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) :
    Finset (KuhnGeometricGridCell d N) :=
  (allKuhnGeometricGridCells d N).filter fun C => F.vertices ∈ C.facets

theorem mem_incidentCells_iff {d N : ℕ}
    (F : KuhnGeometricGridFacet d N)
    (C : KuhnGeometricGridCell d N) :
    C ∈ F.incidentCells ↔ F.vertices ∈ C.facets := by
  classical
  rw [KuhnGeometricGridFacet.incidentCells, Finset.mem_filter]
  exact and_iff_right (KuhnGeometricGridCell.mem_all C)

theorem incidentCells_nonempty {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) :
    F.incidentCells.Nonempty := by
  classical
  rcases F.2 with ⟨C, hC⟩
  exact ⟨C, (F.mem_incidentCells_iff C).mpr hC⟩

end KuhnGeometricGridFacet

/-! ### Why the incidence theorem does NOT reduce to a fixed-`k` sorted extension

The natural reduction — "a grid facet's incident cells are the maximal-sorted extensions of one
`(n-1)`-subset collection, so bound them by extending it by one `k`-subset" — is FALSE.  In the
simplex grid the two cells sharing a facet can have different `k` and base: the Freudenthal
triangulation of `N·Δ^d` glues a `k`-cell to a `(k±1)`-cell across each interior wall.

Machine-checked witness (`d = 2, N = 2`): the central downward triangle (`base 0, k = 2`) and the
corner triangle at `(0,0,2)` (`base e₂, k = 1`) share the edge `{(1,0,1),(0,1,1)}`; that edge lies in
≥ 2 cells (`edgeFacet_two_incident`) while the same-`k` sorted extensions of its downward-frame
collection number exactly one (`extCount_eq_one`).  So `incidentCells.card ≤ 2` is intrinsically the
geometric flip — it crosses `(base, k)` strata and needs the simplex's affine/tiling structure, not a
purely combinatorial fixed-`k` lemma. -/
namespace SortedReductionObstruction

def downSubsets : Finset (KSubset 3 2) :=
  {⟨{0, 1}, by decide⟩, ⟨{0, 2}, by decide⟩, ⟨{1, 2}, by decide⟩}
def cornerSubsets : Finset (KSubset 3 1) :=
  {⟨{0}, by decide⟩, ⟨{1}, by decide⟩, ⟨{2}, by decide⟩}

def downData : KuhnGridCellData 2 2 where
  base := fun _ => 0
  k := 2
  hk_pos := by norm_num
  hk_lt := by norm_num
  subsets := downSubsets
  hsubsets := by decide
  sum_base_add_k := by decide

def cornerData : KuhnGridCellData 2 2 where
  base := fun i => if i = 2 then 1 else 0
  k := 1
  hk_pos := by norm_num
  hk_lt := by norm_num
  subsets := cornerSubsets
  hsubsets := by decide
  sum_base_add_k := by decide

noncomputable def downCell : KuhnGeometricGridCell 2 2 :=
  ⟨downData.vertices, ⟨downData, rfl⟩⟩
noncomputable def cornerCell : KuhnGeometricGridCell 2 2 :=
  ⟨cornerData.vertices, ⟨cornerData, rfl⟩⟩

def pt1 : SimplexGrid 2 2 := ⟨fun i => if i = 1 then 0 else 1, by decide⟩    -- (1,0,1)
def pt2 : SimplexGrid 2 2 := ⟨fun i => if i = 0 then 0 else 1, by decide⟩    -- (0,1,1)
def vtop : SimplexGrid 2 2 := ⟨fun i => if i = 2 then 0 else 1, by decide⟩    -- (1,1,0)
def vcorner : SimplexGrid 2 2 := ⟨fun i => if i = 2 then 2 else 0, by decide⟩  -- (0,0,2)

-- `SimplexGrid` `DecidableEq` is noncomputable, so distinctness is via a coordinate.
theorem pt1_ne_pt2 : pt1 ≠ pt2 := by
  intro h; simpa [pt1, pt2] using congrFun (congrArg Subtype.val h) 0
theorem pt1_ne_vtop : pt1 ≠ vtop := by
  intro h; simpa [pt1, vtop] using congrFun (congrArg Subtype.val h) 1
theorem pt2_ne_vtop : pt2 ≠ vtop := by
  intro h; simpa [pt2, vtop] using congrFun (congrArg Subtype.val h) 2
theorem pt1_ne_vcorner : pt1 ≠ vcorner := by
  intro h; simpa [pt1, vcorner] using congrFun (congrArg Subtype.val h) 0
theorem pt2_ne_vcorner : pt2 ≠ vcorner := by
  intro h; simpa [pt2, vcorner] using congrFun (congrArg Subtype.val h) 1

theorem pt1_mem_down : pt1 ∈ downData.vertices := by
  rw [KuhnGridCellData.vertices, Finset.mem_image]
  exact ⟨⟨{0, 2}, by decide⟩, by decide,
    by apply Subtype.ext; funext i; fin_cases i <;> rfl⟩
theorem pt2_mem_down : pt2 ∈ downData.vertices := by
  rw [KuhnGridCellData.vertices, Finset.mem_image]
  exact ⟨⟨{1, 2}, by decide⟩, by decide,
    by apply Subtype.ext; funext i; fin_cases i <;> rfl⟩
theorem vtop_mem_down : vtop ∈ downData.vertices := by
  rw [KuhnGridCellData.vertices, Finset.mem_image]
  exact ⟨⟨{0, 1}, by decide⟩, by decide,
    by apply Subtype.ext; funext i; fin_cases i <;> rfl⟩

theorem pt1_mem_corner : pt1 ∈ cornerData.vertices := by
  rw [KuhnGridCellData.vertices, Finset.mem_image]
  exact ⟨⟨{0}, by decide⟩, by decide,
    by apply Subtype.ext; funext i; fin_cases i <;> decide⟩
theorem pt2_mem_corner : pt2 ∈ cornerData.vertices := by
  rw [KuhnGridCellData.vertices, Finset.mem_image]
  exact ⟨⟨{1}, by decide⟩, by decide,
    by apply Subtype.ext; funext i; fin_cases i <;> decide⟩
theorem vcorner_mem_corner : vcorner ∈ cornerData.vertices := by
  rw [KuhnGridCellData.vertices, Finset.mem_image]
  exact ⟨⟨{2}, by decide⟩, by decide,
    by apply Subtype.ext; funext i; fin_cases i <;> decide⟩

noncomputable def edge : Finset (SimplexGrid 2 2) := {pt1, pt2}

theorem edge_card : edge.card = 2 := by rw [edge, Finset.card_pair pt1_ne_pt2]

theorem edge_eq_down_erase : edge = downData.vertices.erase vtop := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [edge, Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_erase]
    rcases hx with h | h
    · subst h; exact ⟨pt1_ne_vtop, pt1_mem_down⟩
    · subst h; exact ⟨pt2_ne_vtop, pt2_mem_down⟩
  · rw [Finset.card_erase_of_mem vtop_mem_down, downData.vertices_card, edge_card]

theorem edge_eq_corner_erase : edge = cornerData.vertices.erase vcorner := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [edge, Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_erase]
    rcases hx with h | h
    · subst h; exact ⟨pt1_ne_vcorner, pt1_mem_corner⟩
    · subst h; exact ⟨pt2_ne_vcorner, pt2_mem_corner⟩
  · rw [Finset.card_erase_of_mem vcorner_mem_corner, cornerData.vertices_card, edge_card]

theorem edge_mem_down_facets : edge ∈ downCell.facets :=
  (downCell.mem_facets_iff edge).mpr ⟨vtop, vtop_mem_down, edge_eq_down_erase⟩
theorem edge_mem_corner_facets : edge ∈ cornerCell.facets :=
  (cornerCell.mem_facets_iff edge).mpr ⟨vcorner, vcorner_mem_corner, edge_eq_corner_erase⟩

theorem vtop_not_mem_corner : vtop ∉ cornerData.vertices := by
  intro h
  rcases cornerData.coord_eq_base_or_base_add_one h 2 with hc | hc <;>
    simp [vtop, cornerData] at hc

theorem downCell_ne_cornerCell : downCell ≠ cornerCell := by
  intro h
  have heq : downData.vertices = cornerData.vertices := congrArg Subtype.val h
  exact vtop_not_mem_corner (heq ▸ vtop_mem_down)

noncomputable def edgeFacet : KuhnGeometricGridFacet 2 2 :=
  ⟨edge, ⟨downCell, edge_mem_down_facets⟩⟩

/-- The genuine grid facet `edge` lies in (at least) TWO sorted cells, of
different `k`. -/
theorem edgeFacet_two_incident : 2 ≤ edgeFacet.incidentCells.card := by
  have hsub : ({downCell, cornerCell} : Finset (KuhnGeometricGridCell 2 2)) ⊆
      edgeFacet.incidentCells := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h
    · subst h; exact (edgeFacet.mem_incidentCells_iff downCell).mpr edge_mem_down_facets
    · subst h; exact (edgeFacet.mem_incidentCells_iff cornerCell).mpr edge_mem_corner_facets
  calc 2 = ({downCell, cornerCell} : Finset _).card :=
          (Finset.card_pair downCell_ne_cornerCell).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- In the downward cell's frame the edge is the `k=2` collection `{{0,2},{1,2}}`,
whose same-`k` sorted extensions number exactly ONE — yet the edge is in two grid
cells.  So the fixed-`k` count (1) ≠ grid incidence (2). -/
def A : Finset (KSubset 3 2) := {⟨{0, 2}, by decide⟩, ⟨{1, 2}, by decide⟩}

theorem extCount_eq_one :
    (Finset.univ.filter fun T : KSubset 3 2 =>
      T ∉ A ∧ KSubsetCollection.IsMaximalSorted (insert T A)).card = 1 := by decide

end SortedReductionObstruction

/-! ### Cross-stratum reduction: incidence = lattice completions of the wall

The cross-stratum lattice-completion count:
the completions range over ALL `(base,k)` strata. -/

namespace KuhnGeometricGridFacet

/- Lattice points `v` (any base/`k`) completing the wall `F` to a sorted cell.
Unlike a fixed-`k` extension count (refuted in `SortedReductionObstruction`), this
ranges over all strata, so it counts incident cells exactly. -/
open scoped Classical in
noncomputable def completingOppositeVertices {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) : Finset (SimplexGrid d N) :=
  Finset.univ.filter fun v =>
    v ∉ F.vertices ∧ IsKuhnGridSmallSimplex (insert v F.vertices)

theorem mem_completingOppositeVertices_iff {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (v : SimplexGrid d N) :
    v ∈ F.completingOppositeVertices ↔
      v ∉ F.vertices ∧ IsKuhnGridSmallSimplex (insert v F.vertices) := by
  classical
  simp only [completingOppositeVertices, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The incidence ↔ completion bijection: each incident cell adds exactly one
lattice point to the wall, and conversely.  This is the cross-stratum reduction of
incidence (it does NOT fix `k` or `base`). -/
theorem incidentCells_card_eq_completions_card {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) :
    F.incidentCells.card = F.completingOppositeVertices.card := by
  classical
  symm
  apply Finset.card_bij
    (i := fun v hv => (⟨insert v F.vertices,
        ((F.mem_completingOppositeVertices_iff v).mp hv).2⟩ :
        KuhnGeometricGridCell d N))
  · intro v hv
    rw [F.mem_incidentCells_iff, KuhnGeometricGridCell.mem_facets_iff]
    have hvnot := ((F.mem_completingOppositeVertices_iff v).mp hv).1
    exact ⟨v, Finset.mem_insert_self _ _, (Finset.erase_insert hvnot).symm⟩
  · intro v hv v' hv' h
    have hvnot := ((F.mem_completingOppositeVertices_iff v).mp hv).1
    have heq : insert v F.vertices = insert v' F.vertices := Subtype.ext_iff.mp h
    have hmem : v ∈ insert v' F.vertices := heq ▸ Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hmem with h1 | h1
    · exact h1
    · exact absurd h1 hvnot
  · intro C hC
    rw [F.mem_incidentCells_iff, KuhnGeometricGridCell.mem_facets_iff] at hC
    obtain ⟨x, hx, hFx⟩ := hC
    refine ⟨x, ?_, ?_⟩
    · rw [F.mem_completingOppositeVertices_iff]
      have hxnot : x ∉ F.vertices := by rw [hFx]; exact Finset.notMem_erase x _
      refine ⟨hxnot, ?_⟩
      rw [hFx, Finset.insert_erase hx]
      exact C.2
    · apply Subtype.ext
      show insert x F.vertices = KuhnGeometricGridCell.vertices C
      rw [hFx, Finset.insert_erase hx]

/-! The affine/wall content: completions are coordinate-localized to the
min/max profile of the wall. -/

/-- Coordinatewise minimum of the wall's vertices. -/
noncomputable def coordMin {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (i : Fin (d + 1)) : ℕ :=
  (F.vertices.image fun x => x.1 i).min' (hne.image _)

/-- Coordinatewise maximum of the wall's vertices. -/
noncomputable def coordMax {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (i : Fin (d + 1)) : ℕ :=
  (F.vertices.image fun x => x.1 i).max' (hne.image _)

/-- THE affine localization (proved): each coordinate of a completion is one of
the four values `coordMin`, `coordMax`, `coordMax+1`, `coordMin−1`.  (For a "split"
coordinate `coordMax = coordMin+1` only the first two occur; for an "all-equal"
coordinate `coordMin = coordMax` the dips `±1` open up — this is the cross-stratum
direction.)  Derived purely from the mesh of `insert v F`. -/
theorem completion_coord_cases {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    {v : SimplexGrid d N} (hv : v ∈ F.completingOppositeVertices)
    (hne : F.vertices.Nonempty) (i : Fin (d + 1)) :
    v.1 i = F.coordMin hne i ∨ v.1 i = F.coordMax hne i ∨
      v.1 i = F.coordMax hne i + 1 ∨ v.1 i + 1 = F.coordMin hne i := by
  classical
  have hsimplex := ((F.mem_completingOppositeVertices_iff v).mp hv).2
  have mesh := hsimplex.mesh
  obtain ⟨wmin, hwminF, hwmin⟩ :=
    Finset.mem_image.mp (Finset.min'_mem (F.vertices.image fun x => x.1 i) (hne.image _))
  obtain ⟨wmax, hwmaxF, hwmax⟩ :=
    Finset.mem_image.mp (Finset.max'_mem (F.vertices.image fun x => x.1 i) (hne.image _))
  have hvmem : v ∈ insert v F.vertices := Finset.mem_insert_self _ _
  have hwminmem : wmin ∈ insert v F.vertices := Finset.mem_insert_of_mem hwminF
  have hwmaxmem : wmax ∈ insert v F.vertices := Finset.mem_insert_of_mem hwmaxF
  have h1 := mesh v hvmem wmin hwminmem i
  have h2 := mesh v hvmem wmax hwmaxmem i
  have h3 := mesh wmax hwmaxmem wmin hwminmem i
  have ecmin : F.coordMin hne i = wmin.1 i := hwmin.symm
  have ecmax : F.coordMax hne i = wmax.1 i := hwmax.symm
  have hle : F.coordMin hne i ≤ F.coordMax hne i := Finset.min'_le_max' _ _
  rw [ecmin, ecmax] at hle ⊢
  omega

/-- The coordinate-localized candidate set: lattice points whose every coordinate
hits the wall's min/max profile.  Completions land here (it is the affine envelope);
the sorted/no-crossing condition is what further cuts it to ≤ 2. -/
noncomputable def coordinateCompletionCandidates {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) :
    Finset (SimplexGrid d N) :=
  Finset.univ.filter fun v =>
    ∀ i : Fin (d + 1),
      v.1 i = F.coordMin hne i ∨ v.1 i = F.coordMax hne i ∨
        v.1 i = F.coordMax hne i + 1 ∨ v.1 i + 1 = F.coordMin hne i

theorem completions_subset_coordinateCandidates {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) :
    F.completingOppositeVertices ⊆ F.coordinateCompletionCandidates hne := by
  classical
  intro v hv
  rw [coordinateCompletionCandidates, Finset.mem_filter]
  exact ⟨Finset.mem_univ v, fun i => F.completion_coord_cases hv hne i⟩

/-! ### Side classification of completions (diagnostic; see `SideAudit`)

A completion "dips up" (`coordMax+1`) or "down" (`coordMin−1`) only at a CONSTANT
(frozen) coordinate — at a split coordinate `completion_coord_cases` forces
`{coordMin, coordMax}`.  So a wall with NO frozen coordinate (`c = 0`) has completions
that dip nowhere: they are "in-slice".  Hence side is a TRICHOTOMY, not a dichotomy. -/

/-- A completion that dips up at some coordinate. -/
def IsUpperCompletion {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (v : SimplexGrid d N) : Prop :=
  ∃ i, v.1 i = F.coordMax hne i + 1

/-- A completion that dips down at some coordinate. -/
def IsLowerCompletion {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (v : SimplexGrid d N) : Prop :=
  ∃ i, v.1 i + 1 = F.coordMin hne i

/-- A completion that dips nowhere — every coordinate is `coordMin` or `coordMax`
(the only possibility when there is no frozen coordinate). -/
def IsInSliceCompletion {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (v : SimplexGrid d N) : Prop :=
  ∀ i, v.1 i = F.coordMin hne i ∨ v.1 i = F.coordMax hne i

/-- CORRECTED side classification (the proposed upper/lower DICHOTOMY is false for
`c=0` walls): every completion is upper, lower, OR in-slice.  Proved from
`completion_coord_cases`. -/
theorem completion_upper_lower_or_inslice {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) {v : SimplexGrid d N}
    (hv : v ∈ F.completingOppositeVertices) (hne : F.vertices.Nonempty) :
    F.IsUpperCompletion hne v ∨ F.IsLowerCompletion hne v ∨ F.IsInSliceCompletion hne v := by
  classical
  by_cases hu : ∃ i, v.1 i = F.coordMax hne i + 1
  · exact Or.inl hu
  · by_cases hl : ∃ i, v.1 i + 1 = F.coordMin hne i
    · exact Or.inr (Or.inl hl)
    · refine Or.inr (Or.inr (fun i => ?_))
      rcases F.completion_coord_cases hv hne i with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd ⟨i, h⟩ hu
      · exact absurd ⟨i, h⟩ hl

/-! The three completion classes as filtered finsets, the partition, and the
structural fact that dips occur only at a constant (frozen) coordinate. -/

open scoped Classical in
noncomputable def upperCompletions {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) : Finset (SimplexGrid d N) :=
  F.completingOppositeVertices.filter (F.IsUpperCompletion hne)

open scoped Classical in
noncomputable def lowerCompletions {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) : Finset (SimplexGrid d N) :=
  F.completingOppositeVertices.filter (F.IsLowerCompletion hne)

open scoped Classical in
noncomputable def inSliceCompletions {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) : Finset (SimplexGrid d N) :=
  F.completingOppositeVertices.filter (F.IsInSliceCompletion hne)

theorem mem_upperCompletions {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (v : SimplexGrid d N) :
    v ∈ F.upperCompletions hne ↔
      v ∈ F.completingOppositeVertices ∧ F.IsUpperCompletion hne v := by
  classical
  simp [upperCompletions]

theorem mem_lowerCompletions {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (v : SimplexGrid d N) :
    v ∈ F.lowerCompletions hne ↔
      v ∈ F.completingOppositeVertices ∧ F.IsLowerCompletion hne v := by
  classical
  simp [lowerCompletions]

theorem mem_inSliceCompletions {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (v : SimplexGrid d N) :
    v ∈ F.inSliceCompletions hne ↔
      v ∈ F.completingOppositeVertices ∧ F.IsInSliceCompletion hne v := by
  classical
  simp [inSliceCompletions]

/-- The trichotomy as a `Finset` cover. -/
theorem completions_subset_classes {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) :
    F.completingOppositeVertices ⊆
      F.upperCompletions hne ∪ F.lowerCompletions hne ∪ F.inSliceCompletions hne := by
  classical
  intro v hv
  rw [upperCompletions, lowerCompletions, inSliceCompletions]
  rcases F.completion_upper_lower_or_inslice hv hne with h | h | h
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, h⟩))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv, h⟩))
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv, h⟩)

/-- An upper dip forces a constant (frozen) coordinate.  With the frozen-coordinate
wall lemma (`≤ 1` such coordinate), all dips concentrate at the unique frozen
coordinate; and a wall with NO frozen coordinate (`c = 0`) has no upper completions. -/
theorem isUpper_imp_constant_coord {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    {v : SimplexGrid d N} (hv : v ∈ F.completingOppositeVertices) (hne : F.vertices.Nonempty)
    (huv : F.IsUpperCompletion hne v) :
    ∃ i, F.coordMin hne i = F.coordMax hne i := by
  classical
  obtain ⟨i, hi⟩ := huv
  refine ⟨i, ?_⟩
  have hsimplex := ((F.mem_completingOppositeVertices_iff v).mp hv).2
  obtain ⟨wmin, hwminF, hwmin⟩ :=
    Finset.mem_image.mp (Finset.min'_mem (F.vertices.image fun x => x.1 i) (hne.image _))
  have hmesh := hsimplex.mesh v (Finset.mem_insert_self _ _) wmin (Finset.mem_insert_of_mem hwminF) i
  have hle : F.coordMin hne i ≤ F.coordMax hne i := Finset.min'_le_max' _ _
  have ecmin : F.coordMin hne i = wmin.1 i := hwmin.symm
  rw [ecmin] at hle ⊢; rw [hi] at hmesh; omega

/-- A lower dip likewise forces a constant (frozen) coordinate. -/
theorem isLower_imp_constant_coord {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    {v : SimplexGrid d N} (hv : v ∈ F.completingOppositeVertices) (hne : F.vertices.Nonempty)
    (hlv : F.IsLowerCompletion hne v) :
    ∃ i, F.coordMin hne i = F.coordMax hne i := by
  classical
  obtain ⟨i, hi⟩ := hlv
  refine ⟨i, ?_⟩
  have hsimplex := ((F.mem_completingOppositeVertices_iff v).mp hv).2
  obtain ⟨wmax, hwmaxF, hwmax⟩ :=
    Finset.mem_image.mp (Finset.max'_mem (F.vertices.image fun x => x.1 i) (hne.image _))
  have hmesh := hsimplex.mesh v (Finset.mem_insert_self _ _) wmax (Finset.mem_insert_of_mem hwmaxF) i
  have hle : F.coordMin hne i ≤ F.coordMax hne i := Finset.min'_le_max' _ _
  have ecmax : F.coordMax hne i = wmax.1 i := hwmax.symm
  rw [ecmax] at hle ⊢; omega

/-! ### Same-`coordMin`-frame completions (the fixed-slice class)

`upper ∪ in-slice` lives in the `coordMin` frame (`v_i ∈ {coordMin_i, coordMin_i+1}`);
`lower` (base lowered below `coordMin`) does not.  A same-frame completion is recovered
from its support over `coordMin` (a `KSubset`), so bounding this class is the FIXED-SLICE
problem — the one place fixed-`k` reasoning is legitimate. -/

/-- A completion whose vertex lies in the `coordMin` frame (no coordinate below
`coordMin`, none above `coordMin+1`). -/
def IsSameMinFrameCompletion {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (v : SimplexGrid d N) : Prop :=
  ∀ i, v.1 i = F.coordMin hne i ∨ v.1 i = F.coordMin hne i + 1

open scoped Classical in
noncomputable def sameMinFrameCompletions {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) : Finset (SimplexGrid d N) :=
  F.completingOppositeVertices.filter (F.IsSameMinFrameCompletion hne)

/-- `F`'s own mesh: `coordMax ≤ coordMin + 1`. -/
theorem coordMax_le_coordMin_succ {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (i : Fin (d + 1)) :
    F.coordMax hne i ≤ F.coordMin hne i + 1 := by
  classical
  obtain ⟨C, hC⟩ := F.2
  obtain ⟨wmin, hwminF, hwmin⟩ :=
    Finset.mem_image.mp (Finset.min'_mem (F.vertices.image fun x => x.1 i) (hne.image _))
  obtain ⟨wmax, hwmaxF, hwmax⟩ :=
    Finset.mem_image.mp (Finset.max'_mem (F.vertices.image fun x => x.1 i) (hne.image _))
  have hsub := C.facet_subset hC
  have hmesh := C.mesh wmax (hsub hwmaxF) wmin (hsub hwminF) i
  have ec1 : F.coordMin hne i = wmin.1 i := hwmin.symm
  have ec2 : F.coordMax hne i = wmax.1 i := hwmax.symm
  have hle : F.coordMin hne i ≤ F.coordMax hne i := Finset.min'_le_max' _ _
  rw [ec1, ec2] at hle ⊢; omega

/-- In-slice completions are same-`coordMin`-frame (since `coordMax ≤ coordMin+1`). -/
theorem inSliceCompletions_subset_sameMinFrame {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) :
    F.inSliceCompletions hne ⊆ F.sameMinFrameCompletions hne := by
  classical
  intro v hv
  rw [mem_inSliceCompletions] at hv
  rw [sameMinFrameCompletions, Finset.mem_filter]
  refine ⟨hv.1, fun i => ?_⟩
  rcases hv.2 i with h | h
  · exact Or.inl h
  · have := F.coordMax_le_coordMin_succ hne i
    have hle : F.coordMin hne i ≤ F.coordMax hne i := Finset.min'_le_max' _ _
    rcases Nat.lt_or_ge (F.coordMin hne i) (F.coordMax hne i) with hlt | hge
    · right; omega
    · left; omega

/-- Pointwise version of `isUpper_imp_constant_coord`: a completion that dips UP at a
specific coordinate `i` (`v_i = coordMax_i + 1`) forces that coordinate to be constant. -/
theorem completion_upper_coord_imp_constant {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) {v : SimplexGrid d N}
    (hv : v ∈ F.completingOppositeVertices) (hne : F.vertices.Nonempty) {i : Fin (d + 1)}
    (hi : v.1 i = F.coordMax hne i + 1) : F.coordMin hne i = F.coordMax hne i := by
  classical
  have hsimplex := ((F.mem_completingOppositeVertices_iff v).mp hv).2
  obtain ⟨wmin, hwminF, hwmin⟩ :=
    Finset.mem_image.mp (Finset.min'_mem (F.vertices.image fun x => x.1 i) (hne.image _))
  have hmesh := hsimplex.mesh v (Finset.mem_insert_self _ _) wmin
    (Finset.mem_insert_of_mem hwminF) i
  have hle : F.coordMin hne i ≤ F.coordMax hne i := Finset.min'_le_max' _ _
  have ecmin : F.coordMin hne i = wmin.1 i := hwmin.symm
  rw [ecmin] at hle ⊢; omega

/-- **Partition cover.** Every completion is either same-`coordMin`-frame (no
coordinate below `coordMin`) or a lower completion (some coordinate at `coordMin − 1`).
The only way to leave the frame `[coordMin, coordMin+1]` is a downward dip: upward dips
land at `coordMin+1` (they only occur at constant coordinates, where `coordMax = coordMin`). -/
theorem completions_subset_same_union_lower {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) :
    F.completingOppositeVertices ⊆ F.sameMinFrameCompletions hne ∪ F.lowerCompletions hne := by
  classical
  intro v hv
  rw [Finset.mem_union]
  by_cases hlow : F.IsLowerCompletion hne v
  · exact Or.inr ((F.mem_lowerCompletions hne v).mpr ⟨hv, hlow⟩)
  · refine Or.inl ?_
    rw [sameMinFrameCompletions, Finset.mem_filter]
    refine ⟨hv, fun i => ?_⟩
    have hnodown : ¬ (v.1 i + 1 = F.coordMin hne i) := fun h => hlow ⟨i, h⟩
    have hle : F.coordMin hne i ≤ F.coordMax hne i := Finset.min'_le_max' _ _
    have hmesh := F.coordMax_le_coordMin_succ hne i
    rcases F.completion_coord_cases hv hne i with h | h | h | h
    · exact Or.inl h
    · omega
    · have hconst := F.completion_upper_coord_imp_constant hv hne h; omega
    · exact absurd h hnodown

/-- **Disjointness.** Same-`coordMin`-frame and lower completions are disjoint:
a frame completion has every coordinate `≥ coordMin`, a lower one has a coordinate at
`coordMin − 1`. -/
theorem sameMinFrameCompletions_disjoint_lowerCompletions {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) :
    Disjoint (F.sameMinFrameCompletions hne) (F.lowerCompletions hne) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvs hvl
  rw [sameMinFrameCompletions, Finset.mem_filter] at hvs
  obtain ⟨i, hi⟩ := ((F.mem_lowerCompletions hne v).mp hvl).2
  rcases hvs.2 i with h | h <;> omega

/- The support of a same-frame completion over `coordMin` (a `KSubset` of `Fin (d+1)`). -/
open scoped Classical in
noncomputable def supportOverMin {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (v : SimplexGrid d N) : Finset (Fin (d + 1)) :=
  Finset.univ.filter fun i => v.1 i = F.coordMin hne i + 1

theorem mem_supportOverMin {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (v : SimplexGrid d N) (i : Fin (d + 1)) :
    i ∈ F.supportOverMin hne v ↔ v.1 i = F.coordMin hne i + 1 := by
  classical
  simp [supportOverMin]

/-- In the `coordMin` frame (`coordMin = base + χ(cp)`), a vertex `base + χ(T)`'s support is
`T \ cp` — exactly the common-present reduction. -/
theorem supportOverMin_eq_sdiff {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    {base : Fin (d + 1) → ℕ} {cp : Finset (Fin (d + 1))} {w : SimplexGrid d N}
    {T : Finset (Fin (d + 1))}
    (hframe : ∀ i, F.coordMin hne i = base i + (if i ∈ cp then 1 else 0))
    (hw : ∀ i, w.1 i = base i + chi T i) :
    F.supportOverMin hne w = T \ cp := by
  classical
  ext i
  rw [KuhnGeometricGridFacet.mem_supportOverMin, Finset.mem_sdiff, hw i, hframe i, chi]
  by_cases hiT : i ∈ T <;> by_cases hicp : i ∈ cp <;> simp [hiT, hicp] <;> omega

/-- The facet frame identity: given the per-coordinate image equality from the parent cell,
`coordMin = base + χ(commonPresent W)` for the wall collection `W`. -/
theorem coordMin_eq_base_add_commonPresent {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    {k : ℕ} (base : Fin (d + 1) → ℕ) (W : Finset (KSubset (d + 1) k)) (hWne : W.Nonempty)
    (hFvert : ∀ i, (F.vertices.image fun x => x.1 i) = W.image (fun S => base i + chi S.1 i))
    (i : Fin (d + 1)) :
    F.coordMin hne i = base i + (if i ∈ KSubsetCollection.commonPresent W then 1 else 0) := by
  rw [KuhnGeometricGridFacet.coordMin, ← min_coord_eq_gen base W hWne i]
  congr 1
  exact hFvert i

/-- A same-frame completion is recovered from its support over `coordMin`.  Hence
`sameMinFrameCompletions` injects into supports — bounding it is the fixed-slice
`KSubset`-extension problem. -/
theorem sameMinFrame_eq_of_supportOverMin_eq {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    {v w : SimplexGrid d N} (hv : F.IsSameMinFrameCompletion hne v)
    (hw : F.IsSameMinFrameCompletion hne w)
    (h : F.supportOverMin hne v = F.supportOverMin hne w) : v = w := by
  classical
  apply Subtype.ext; funext i
  have hiff : (v.1 i = F.coordMin hne i + 1) ↔ (w.1 i = F.coordMin hne i + 1) := by
    rw [← mem_supportOverMin, ← mem_supportOverMin, h]
  rcases hv i with hvi | hvi <;> rcases hw i with hwi | hwi <;> simp_all

/-- Support is injective on same-min-frame completions (direct from
`sameMinFrame_eq_of_supportOverMin_eq`). -/
theorem supportOverMin_injOn_sameMinFrameCompletions {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) :
    Set.InjOn (F.supportOverMin hne) (↑(F.sameMinFrameCompletions hne)) := by
  classical
  intro v hv w hw h
  rw [Finset.mem_coe, sameMinFrameCompletions, Finset.mem_filter] at hv hw
  exact F.sameMinFrame_eq_of_supportOverMin_eq hne hv.2 hw.2 h

end KuhnGeometricGridFacet

/-! ### Parent-cell recovery + (wall support image = reduced erased collection) -/

/-- The vertex map of a cell datum, as `SimplexGrid` points. -/
noncomputable def cellVertexMap {d N : ℕ} (D : KuhnGridCellData d N)
    (S : KSubset (d + 1) D.k) : SimplexGrid d N :=
  ⟨vertexFromSubset D.base S.1, vertexFromSubset_sum_eq D.base S.1 S.2 D.sum_base_add_k⟩

theorem cellVertexMap_injective {d N : ℕ} (D : KuhnGridCellData d N) :
    Function.Injective (cellVertexMap D) := by
  intro S T h
  apply Subtype.ext
  have : vertexFromSubset D.base S.1 = vertexFromSubset D.base T.1 := congrArg Subtype.val h
  exact vertexFromSubset_injective D.base this

theorem cellVertexMap_vertices {d N : ℕ} (D : KuhnGridCellData d N) :
    D.vertices = D.subsets.image (cellVertexMap D) := rfl

/-- PARENT-CELL RECOVERY: a facet is the erased-subset image of some cell datum. -/
theorem KuhnGeometricGridFacet.exists_parent_data {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) :
    ∃ (D : KuhnGridCellData d N) (S₀ : KSubset (d + 1) D.k), S₀ ∈ D.subsets ∧
      F.vertices = (D.subsets.erase S₀).image (cellVertexMap D) := by
  classical
  obtain ⟨C, hFC⟩ := F.2
  rw [KuhnGeometricGridCell.mem_facets_iff] at hFC
  obtain ⟨x₀, hx₀, hFeq⟩ := hFC
  obtain ⟨D, hD⟩ := C.2
  have hCV : C.vertices = D.vertices := hD.symm
  rw [hCV] at hx₀ hFeq
  rw [cellVertexMap_vertices, Finset.mem_image] at hx₀
  obtain ⟨S₀, hS₀, hx₀eq⟩ := hx₀
  refine ⟨D, S₀, hS₀, ?_⟩
  show F.1 = (D.subsets.erase S₀).image (cellVertexMap D)
  rw [hFeq, cellVertexMap_vertices, ← hx₀eq, ← Finset.image_erase (cellVertexMap_injective D)]

/-- Pointwise: a completion that dips DOWN at coordinate `j` (`v_j + 1 = coordMin_j`)
forces that coordinate to be constant.  Pointwise form of `isLower_imp_constant_coord`. -/
theorem KuhnGeometricGridFacet.completion_lower_coord_imp_constant {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) {v : SimplexGrid d N}
    (hv : v ∈ F.completingOppositeVertices) (hne : F.vertices.Nonempty) {j : Fin (d + 1)}
    (hj : v.1 j + 1 = F.coordMin hne j) : F.coordMin hne j = F.coordMax hne j := by
  classical
  have hsimplex := ((F.mem_completingOppositeVertices_iff v).mp hv).2
  obtain ⟨wmax, hwmaxF, hwmax⟩ :=
    Finset.mem_image.mp (Finset.max'_mem (F.vertices.image fun x => x.1 j) (hne.image _))
  have hmesh := hsimplex.mesh v (Finset.mem_insert_self _ _) wmax
    (Finset.mem_insert_of_mem hwmaxF) j
  have hle : F.coordMin hne j ≤ F.coordMax hne j := Finset.min'_le_max' _ _
  have ecmax : F.coordMax hne j = wmax.1 j := hwmax.symm
  rw [ecmax] at hle ⊢; omega

/-- **≤ 1 constant coordinate.** At most one coordinate of `F` is constant
(`coordMin = coordMax`).  Bridges the cell-level frozen bound
`erasedSubsets_frozen_card_le_one` (`2 ≤ d`) through parent-cell recovery: a constant
coordinate of `F` is common-present or common-absent across the erased wall collection,
and that union has card `≤ 1`. -/
theorem KuhnGeometricGridFacet.constant_coord_unique {d N : ℕ} (hd : 2 ≤ d)
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) {i j : Fin (d + 1)}
    (hi : F.coordMin hne i = F.coordMax hne i) (hj : F.coordMin hne j = F.coordMax hne j) :
    i = j := by
  classical
  obtain ⟨D, S₀, hS₀, hFeq⟩ := F.exists_parent_data
  have hWne : (D.subsets.erase S₀).Nonempty :=
    Finset.image_nonempty.mp (by rw [← hFeq]; exact hne)
  have hbridge : ∀ p : Fin (d + 1), F.coordMin hne p = F.coordMax hne p →
      p ∈ KSubsetCollection.commonPresent (D.subsets.erase S₀) ∪
            KSubsetCollection.commonAbsent (D.subsets.erase S₀) := by
    intro p hp
    have hsub : ∀ S ∈ D.subsets.erase S₀, D.base p + chi S.1 p = F.coordMin hne p := by
      intro S hSW
      have hxv : cellVertexMap D S ∈ F.vertices := by
        rw [hFeq]; exact Finset.mem_image_of_mem _ hSW
      have h1 : F.coordMin hne p ≤ (cellVertexMap D S).1 p :=
        Finset.min'_le _ _ (Finset.mem_image_of_mem (fun y => y.1 p) hxv)
      have h2 : (cellVertexMap D S).1 p ≤ F.coordMax hne p :=
        Finset.le_max' _ _ (Finset.mem_image_of_mem (fun y => y.1 p) hxv)
      have h3 : (cellVertexMap D S).1 p = D.base p + chi S.1 p := rfl
      omega
    obtain ⟨S₁, hS₁⟩ := hWne
    by_cases hp1 : p ∈ S₁.1
    · refine Finset.mem_union_left _ ((KSubsetCollection.mem_commonPresent_iff _ p).mpr ?_)
      intro S hSW
      have e1 := hsub S₁ hS₁
      have e2 := hsub S hSW
      have c1 : chi S₁.1 p = 1 := by simp [chi, hp1]
      by_contra hpS
      have c2 : chi S.1 p = 0 := by simp [chi, hpS]
      rw [c1] at e1; rw [c2] at e2; omega
    · refine Finset.mem_union_right _ ((KSubsetCollection.mem_commonAbsent_iff _ p).mpr ?_)
      intro S hSW hpS
      have e1 := hsub S₁ hS₁
      have e2 := hsub S hSW
      have c1 : chi S₁.1 p = 0 := by simp [chi, hp1]
      have c2 : chi S.1 p = 1 := by simp [chi, hpS]
      rw [c1] at e1; rw [c2] at e2; omega
  have hbd : (KSubsetCollection.commonPresent (D.subsets.erase S₀)).card +
      (KSubsetCollection.commonAbsent (D.subsets.erase S₀)).card ≤ 1 :=
    D.erasedSubsets_frozen_card_le_one hd hS₀
  have hbound : (KSubsetCollection.commonPresent (D.subsets.erase S₀) ∪
      KSubsetCollection.commonAbsent (D.subsets.erase S₀)).card ≤ 1 :=
    le_trans (Finset.card_union_le _ _) hbd
  exact Finset.card_le_one.mp hbound i (hbridge i hi) j (hbridge j hj)

/-- **Lowering-coordinate uniqueness.** All lower completions dip at the same
coordinate: the lowering coordinate is constant (`isLower_imp_constant_coord`), and there
is at most one constant coordinate (`constant_coord_unique`). -/
theorem KuhnGeometricGridFacet.lowering_coord_unique {d N : ℕ} (hd : 2 ≤ d)
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    {v w : SimplexGrid d N} (hv : v ∈ F.lowerCompletions hne) (hw : w ∈ F.lowerCompletions hne)
    {jv jw : Fin (d + 1)} (hjv : v.1 jv + 1 = F.coordMin hne jv)
    (hjw : w.1 jw + 1 = F.coordMin hne jw) : jv = jw := by
  have hvc := ((F.mem_lowerCompletions hne v).mp hv).1
  have hwc := ((F.mem_lowerCompletions hne w).mp hw).1
  exact F.constant_coord_unique hd hne
    (F.completion_lower_coord_imp_constant hvc hne hjv)
    (F.completion_lower_coord_imp_constant hwc hne hjw)

theorem KSubsetReduction.collRemoveCommon_image_val {n k : ℕ} (A : Finset (KSubset n k)) :
    (KSubsetReduction.collRemoveCommon A).image Subtype.val =
      A.image (fun S => S.1 \ KSubsetCollection.commonPresent A) := by
  classical
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨T, hT, rfl⟩
    rw [KSubsetReduction.collRemoveCommon, Finset.mem_image] at hT
    obtain ⟨S, _, rfl⟩ := hT
    exact ⟨S.1, S.2, rfl⟩
  · rintro ⟨S, hS, rfl⟩
    refine ⟨KSubsetReduction.removeCommon (KSubsetCollection.commonPresent A) S
      (fun i hi => (KSubsetCollection.mem_commonPresent_iff A i).mp hi S hS), ?_, rfl⟩
    rw [KSubsetReduction.collRemoveCommon, Finset.mem_image]
    exact ⟨⟨S, hS⟩, Finset.mem_attach _ _, rfl⟩

/-- The wall's support image is the common-present reduction of the erased collection. -/
theorem KuhnGeometricGridFacet.wall_support_image_eq {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) :
    ∃ (D : KuhnGridCellData d N) (S₀ : KSubset (d + 1) D.k), S₀ ∈ D.subsets ∧
      F.vertices.image (F.supportOverMin hne) =
        (KSubsetReduction.collRemoveCommon (D.subsets.erase S₀)).image Subtype.val := by
  classical
  obtain ⟨D, S₀, hS₀, hFeq⟩ := F.exists_parent_data
  refine ⟨D, S₀, hS₀, ?_⟩
  set W := D.subsets.erase S₀ with hW
  have hWne : W.Nonempty := by
    rw [hFeq] at hne; exact hne.of_image
  have hFvert : ∀ i, (F.vertices.image fun x => x.1 i) = W.image (fun S => D.base i + chi S.1 i) := by
    intro i
    rw [hFeq, Finset.image_image]
    apply Finset.image_congr
    intro S _; rfl
  have hframe : ∀ i, F.coordMin hne i =
      D.base i + (if i ∈ KSubsetCollection.commonPresent W then 1 else 0) :=
    fun i => F.coordMin_eq_base_add_commonPresent hne D.base W hWne hFvert i
  rw [hFeq, Finset.image_image, KSubsetReduction.collRemoveCommon_image_val]
  apply Finset.image_congr
  intro S _
  exact F.supportOverMin_eq_sdiff hne hframe (fun i => rfl)

/-! ### infrastructure: support cardinality + target-typed reduced collection -/

/-- The support of a same-min-frame point has card `N - ∑coordMin`. -/
theorem KuhnGeometricGridFacet.card_supportOverMin {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    {v : SimplexGrid d N} (hv : F.IsSameMinFrameCompletion hne v) :
    (F.supportOverMin hne v).card = N - ∑ i, F.coordMin hne i := by
  classical
  have hpt : ∀ i, v.1 i =
      F.coordMin hne i + (if i ∈ F.supportOverMin hne v then 1 else 0) := by
    intro i
    by_cases hi : i ∈ F.supportOverMin hne v
    · rw [if_pos hi]; rw [F.mem_supportOverMin] at hi; exact hi
    · rw [if_neg hi]
      rw [F.mem_supportOverMin] at hi
      rcases hv i with h | h
      · omega
      · exact absurd h hi
  have hsum : ∑ i : Fin (d + 1), v.1 i = N := v.2
  have hkey : ∑ i : Fin (d + 1), v.1 i =
      (∑ i : Fin (d + 1), F.coordMin hne i) + (F.supportOverMin hne v).card := by
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
  omega

/-- The reduced collection at a chosen target card `m` (type-flexible `collRemoveCommon`). -/
noncomputable def KSubsetReduction.reducedColl {n k : ℕ} (A : Finset (KSubset n k))
    (cp : Finset (Fin n)) (m : ℕ) (hm : ∀ S ∈ A, (S.1 \ cp).card = m) : Finset (KSubset n m) :=
  A.attach.image (fun S => ⟨S.1.1 \ cp, hm S.1 S.2⟩)

theorem KSubsetReduction.reducedColl_isMaximalSorted {n k : ℕ} {A : Finset (KSubset n k)}
    (hA : KSubsetCollection.IsMaximalSorted A) (cp : Finset (Fin n))
    (hcp : ∀ S ∈ A, cp ⊆ S.1) (m : ℕ) (hm : ∀ S ∈ A, (S.1 \ cp).card = m) :
    KSubsetCollection.IsMaximalSorted (KSubsetReduction.reducedColl A cp m hm) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [KSubsetReduction.reducedColl, Finset.card_image_of_injOn, Finset.card_attach, hA.1]
    intro S _ S' _ h
    have hd : S.1.1 \ cp = S'.1.1 \ cp := congrArg Subtype.val h
    apply Subtype.ext; apply Subtype.ext
    calc S.1.1 = (S.1.1 \ cp) ∪ cp := (Finset.sdiff_union_of_subset (hcp S.1 S.2)).symm
      _ = (S'.1.1 \ cp) ∪ cp := by rw [hd]
      _ = S'.1.1 := Finset.sdiff_union_of_subset (hcp S'.1 S'.2)
  · intro I hI J hJ hIJ
    rw [KSubsetReduction.reducedColl, Finset.mem_image] at hI hJ
    obtain ⟨S, _, hSeq⟩ := hI
    obtain ⟨S', _, hS'eq⟩ := hJ
    have hSne : S.1 ≠ S'.1 := by
      intro h; apply hIJ; rw [← hSeq, ← hS'eq]; apply Subtype.ext
      show S.1.1 \ cp = S'.1.1 \ cp
      rw [show S.1.1 = S'.1.1 from congrArg Subtype.val h]
    rw [← hSeq, ← hS'eq]
    have hkey : ∀ (U V : KSubset n k) (hU : U ∈ A) (hV : V ∈ A), KSubset.SortedBefore U V →
        KSubset.SortedBefore (⟨U.1 \ cp, hm U hU⟩ : KSubset n m) ⟨V.1 \ cp, hm V hV⟩ := by
      intro U V hU hV hUV t
      have hpU : KSubset.prefixCount (⟨U.1 \ cp, hm U hU⟩ : KSubset n m) t
          = KSubset.prefixCount U t - KSubsetReduction.pcCommon cp t :=
        KSubsetReduction.prefixCount_sdiff cp U (hcp U hU) t
      have hpV : KSubset.prefixCount (⟨V.1 \ cp, hm V hV⟩ : KSubset n m) t
          = KSubset.prefixCount V t - KSubsetReduction.pcCommon cp t :=
        KSubsetReduction.prefixCount_sdiff cp V (hcp V hV) t
      rw [hpU, hpV]
      have h1 := (hUV t).1
      have h2 := (hUV t).2
      have hc1 := KSubsetReduction.prefixCount_le_of_subset cp U (hcp U hU) t
      have hc2 := KSubsetReduction.prefixCount_le_of_subset cp V (hcp V hV) t
      omega
    rcases hA.2 S.1 S.2 S'.1 S'.2 hSne with hb | hb
    · exact Or.inl (hkey S.1 S'.1 S.2 S'.2 hb)
    · exact Or.inr (hkey S'.1 S.1 S'.2 S.2 hb)

/-- Card of the common-present reduction (non-maximal version): `removeCommon` is injective on the
collection, so the reduced collection has the same cardinality.  (The card half of
`reducedColl_isMaximalSorted`, without the maximality requirement.) -/
theorem KSubsetReduction.reducedColl_card {n k : ℕ} {A : Finset (KSubset n k)}
    (cp : Finset (Fin n)) (hcp : ∀ S ∈ A, cp ⊆ S.1) (m : ℕ)
    (hm : ∀ S ∈ A, (S.1 \ cp).card = m) :
    (KSubsetReduction.reducedColl A cp m hm).card = A.card := by
  classical
  rw [KSubsetReduction.reducedColl, Finset.card_image_of_injOn, Finset.card_attach]
  intro S _ S' _ h
  have hd : S.1.1 \ cp = S'.1.1 \ cp := congrArg Subtype.val h
  apply Subtype.ext; apply Subtype.ext
  calc S.1.1 = (S.1.1 \ cp) ∪ cp := (Finset.sdiff_union_of_subset (hcp S.1 S.2)).symm
    _ = (S'.1.1 \ cp) ∪ cp := by rw [hd]
    _ = S'.1.1 := Finset.sdiff_union_of_subset (hcp S'.1 S'.2)

/-- Sortedness of the common-present reduction (non-maximal version): if `A` is sorted, so is the
reduced collection.  (The sortedness half of `reducedColl_isMaximalSorted`, taking only `IsSorted A`
rather than `IsMaximalSorted A`.) -/
theorem KSubsetReduction.reducedColl_isSorted {n k : ℕ} {A : Finset (KSubset n k)}
    (hA : KSubsetCollection.IsSorted A) (cp : Finset (Fin n))
    (hcp : ∀ S ∈ A, cp ⊆ S.1) (m : ℕ) (hm : ∀ S ∈ A, (S.1 \ cp).card = m) :
    KSubsetCollection.IsSorted (KSubsetReduction.reducedColl A cp m hm) := by
  classical
  intro I hI J hJ hIJ
  rw [KSubsetReduction.reducedColl, Finset.mem_image] at hI hJ
  obtain ⟨S, _, hSeq⟩ := hI
  obtain ⟨S', _, hS'eq⟩ := hJ
  have hSne : S.1 ≠ S'.1 := by
    intro h; apply hIJ; rw [← hSeq, ← hS'eq]; apply Subtype.ext
    show S.1.1 \ cp = S'.1.1 \ cp
    rw [show S.1.1 = S'.1.1 from congrArg Subtype.val h]
  rw [← hSeq, ← hS'eq]
  have hkey : ∀ (U V : KSubset n k) (hU : U ∈ A) (hV : V ∈ A), KSubset.SortedBefore U V →
      KSubset.SortedBefore (⟨U.1 \ cp, hm U hU⟩ : KSubset n m) ⟨V.1 \ cp, hm V hV⟩ := by
    intro U V hU hV hUV t
    have hpU : KSubset.prefixCount (⟨U.1 \ cp, hm U hU⟩ : KSubset n m) t
        = KSubset.prefixCount U t - KSubsetReduction.pcCommon cp t :=
      KSubsetReduction.prefixCount_sdiff cp U (hcp U hU) t
    have hpV : KSubset.prefixCount (⟨V.1 \ cp, hm V hV⟩ : KSubset n m) t
        = KSubset.prefixCount V t - KSubsetReduction.pcCommon cp t :=
      KSubsetReduction.prefixCount_sdiff cp V (hcp V hV) t
    rw [hpU, hpV]
    have h1 := (hUV t).1
    have h2 := (hUV t).2
    have hc1 := KSubsetReduction.prefixCount_le_of_subset cp U (hcp U hU) t
    have hc2 := KSubsetReduction.prefixCount_le_of_subset cp V (hcp V hV) t
    omega
  rcases hA S.1 S.2 S'.1 S'.2 hSne with hb | hb
  · exact Or.inl (hkey S.1 S'.1 S.2 S'.2 hb)
  · exact Or.inr (hkey S'.1 S.1 S'.2 S.2 hb)

/-- `F`'s own vertices are same-min-frame (each coordinate is `coordMin` or `coordMin+1`). -/
theorem KuhnGeometricGridFacet.vertex_isSameMinFrame {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    {w : SimplexGrid d N} (hw : w ∈ F.vertices) : F.IsSameMinFrameCompletion hne w := by
  intro i
  have hmin : F.coordMin hne i ≤ w.1 i :=
    Finset.min'_le _ (w.1 i) (Finset.mem_image_of_mem (fun x => x.1 i) hw)
  have hmax : w.1 i ≤ F.coordMax hne i :=
    Finset.le_max' _ (w.1 i) (Finset.mem_image_of_mem (fun x => x.1 i) hw)
  have hle := F.coordMax_le_coordMin_succ hne i
  omega

/-- For a completion `v`, the cell `insert v F.vertices` realizes the `coordMin` frame:
`coordMin F = base + χ(commonPresent)` (the min is unchanged by `v ≥ coordMin`). -/
theorem KuhnGeometricGridFacet.completion_frame {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) {v : SimplexGrid d N}
    (hv : v ∈ F.completingOppositeVertices) (hvf : F.IsSameMinFrameCompletion hne v) :
    ∃ D : KuhnGridCellData d N, D.vertices = insert v F.vertices ∧
      (∀ i, F.coordMin hne i =
        D.base i + (if i ∈ KSubsetCollection.commonPresent D.subsets then 1 else 0)) := by
  classical
  have hsimplex := ((F.mem_completingOppositeVertices_iff v).mp hv).2
  obtain ⟨D, hD⟩ := hsimplex
  refine ⟨D, hD, fun i => ?_⟩
  have hDne : D.vertices.Nonempty := by rw [hD]; exact ⟨v, Finset.mem_insert_self _ _⟩
  have hmin := D.min_coord_eq hDne i
  have hvge : F.coordMin hne i ≤ v.1 i := by rcases hvf i with h | h <;> omega
  have hcoord : F.coordMin hne i = (D.vertices.image fun x => x.1 i).min' (hDne.image _) := by
    apply le_antisymm
    · apply Finset.le_min'
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [hD, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hvge
      · exact Finset.min'_le _ (x.1 i) (Finset.mem_image_of_mem (fun x => x.1 i) hx)
    · obtain ⟨w, hwF, hweq⟩ :=
        Finset.mem_image.mp (Finset.min'_mem _ (hne.image (fun x => x.1 i)))
      have hwD : w ∈ D.vertices := by rw [hD]; exact Finset.mem_insert_of_mem hwF
      calc (D.vertices.image fun x => x.1 i).min' (hDne.image _)
          ≤ w.1 i := Finset.min'_le _ (w.1 i) (Finset.mem_image_of_mem (fun x => x.1 i) hwD)
        _ = F.coordMin hne i := hweq
  rw [hcoord]; exact hmin

theorem KSubsetReduction.mem_reducedColl {n k : ℕ} {A : Finset (KSubset n k)}
    {cp : Finset (Fin n)} {m : ℕ} {hm : ∀ S ∈ A, (S.1 \ cp).card = m} {T : KSubset n m} :
    T ∈ KSubsetReduction.reducedColl A cp m hm ↔ ∃ S ∈ A, S.1 \ cp = T.1 := by
  classical
  rw [KSubsetReduction.reducedColl, Finset.mem_image]
  constructor
  · rintro ⟨S, _, hS⟩; exact ⟨S.1, S.2, congrArg Subtype.val hS⟩
  · rintro ⟨S, hS, hST⟩; exact ⟨⟨S, hS⟩, Finset.mem_attach _ _, Subtype.ext hST⟩

namespace KuhnGeometricGridFacet

/-- The support-lift collection of a finite set of same-min-frame points, sitting in the
uniform support type `KSubset (d+1) (N − ∑coordMin)`. -/
noncomputable def slift {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (P : Finset (SimplexGrid d N))
    (hP : ∀ w ∈ P, F.IsSameMinFrameCompletion hne w) :
    Finset (KSubset (d + 1) (N - ∑ i, F.coordMin hne i)) :=
  P.attach.image (fun w => ⟨F.supportOverMin hne w.1, F.card_supportOverMin hne (hP w.1 w.2)⟩)

theorem mem_slift {d N : ℕ} (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    {P : Finset (SimplexGrid d N)} {hP : ∀ w ∈ P, F.IsSameMinFrameCompletion hne w}
    {T : KSubset (d + 1) (N - ∑ i, F.coordMin hne i)} :
    T ∈ F.slift hne P hP ↔ ∃ w ∈ P, F.supportOverMin hne w = T.1 := by
  classical
  rw [slift, Finset.mem_image]
  constructor
  · rintro ⟨w, _, hw⟩; exact ⟨w.1, w.2, congrArg Subtype.val hw⟩
  · rintro ⟨w, hw, hwT⟩; exact ⟨⟨w, hw⟩, Finset.mem_attach _ _, Subtype.ext hwT⟩

theorem hP_insert {d N : ℕ} (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    {v : SimplexGrid d N} (hvf : F.IsSameMinFrameCompletion hne v) :
    ∀ w ∈ insert v F.vertices, F.IsSameMinFrameCompletion hne w := by
  intro w hw
  rw [Finset.mem_insert] at hw
  rcases hw with rfl | hw
  · exact hvf
  · exact F.vertex_isSameMinFrame hne hw

/-- Inserting a completion's support-lift recovers the reduced parent collection, hence is
maximal sorted: `slift (insert v F.vertices) = reducedColl D.subsets (commonPresent D.subsets)`. -/
theorem slift_insert_maximal {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) {v : SimplexGrid d N} (hvc : v ∈ F.completingOppositeVertices)
    (hvf : F.IsSameMinFrameCompletion hne v) :
    KSubsetCollection.IsMaximalSorted (F.slift hne (insert v F.vertices) (F.hP_insert hne hvf)) := by
  classical
  obtain ⟨D, hD, hframe⟩ := F.completion_frame hne hvc hvf
  have hcp : ∀ S ∈ D.subsets, KSubsetCollection.commonPresent D.subsets ⊆ S.1 :=
    fun S hS i hi => (KSubsetCollection.mem_commonPresent_iff D.subsets i).mp hi S hS
  have hm : ∀ S ∈ D.subsets,
      (S.1 \ KSubsetCollection.commonPresent D.subsets).card = N - ∑ i, F.coordMin hne i := by
    intro S hS
    have hcard : (S.1 \ KSubsetCollection.commonPresent D.subsets).card
        + (KSubsetCollection.commonPresent D.subsets).card = D.k := by
      rw [← Finset.card_union_of_disjoint Finset.sdiff_disjoint,
        Finset.sdiff_union_of_subset (hcp S hS), S.2]
    have hsumcoord : ∑ i, F.coordMin hne i =
        (∑ i, D.base i) + (KSubsetCollection.commonPresent D.subsets).card := by
      rw [Finset.sum_congr rfl (fun i _ => hframe i), Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
    have hsum := D.sum_base_add_k
    omega
  have hrel : F.slift hne (insert v F.vertices) (F.hP_insert hne hvf)
      = KSubsetReduction.reducedColl D.subsets (KSubsetCollection.commonPresent D.subsets)
          (N - ∑ i, F.coordMin hne i) hm := by
    ext T
    rw [mem_slift, KSubsetReduction.mem_reducedColl]
    have hsupp : ∀ S : KSubset (d + 1) D.k, F.supportOverMin hne (cellVertexMap D S)
        = S.1 \ KSubsetCollection.commonPresent D.subsets :=
      fun S => F.supportOverMin_eq_sdiff hne hframe (fun i => rfl)
    constructor
    · rintro ⟨w, hw, hwT⟩
      rw [← hD, cellVertexMap_vertices, Finset.mem_image] at hw
      obtain ⟨S, hS, rfl⟩ := hw
      exact ⟨S, hS, by rw [← hsupp S]; exact hwT⟩
    · rintro ⟨S, hS, hST⟩
      exact ⟨cellVertexMap D S, by rw [← hD, cellVertexMap_vertices]; exact Finset.mem_image_of_mem _ hS,
        by rw [hsupp S]; exact hST⟩
  rw [hrel]
  exact KSubsetReduction.reducedColl_isMaximalSorted D.hsubsets _ hcp _ hm

/-- The support-lift of `insert v F.vertices` is `insert (supportOverMin v) (slift F.vertices)`. -/
theorem slift_insert_eq_insert {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) {v : SimplexGrid d N} (hvf : F.IsSameMinFrameCompletion hne v)
    (hvnotin : v ∉ F.vertices) :
    F.slift hne (insert v F.vertices) (F.hP_insert hne hvf)
      = insert ⟨F.supportOverMin hne v, F.card_supportOverMin hne hvf⟩
          (F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw)) := by
  classical
  ext T
  rw [Finset.mem_insert, mem_slift, mem_slift]
  constructor
  · rintro ⟨w, hw, hwT⟩
    rw [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · exact Or.inl (Subtype.ext hwT).symm
    · exact Or.inr ⟨w, hw, hwT⟩
  · rintro (rfl | ⟨w, hw, hwT⟩)
    · exact ⟨v, Finset.mem_insert_self _ _, rfl⟩
    · exact ⟨w, Finset.mem_insert_of_mem hw, hwT⟩

/-- A completion's support is a same-frame extension of the wall's support-lift. -/
theorem support_mem_sameFrameExtensions {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) {v : SimplexGrid d N} (hvc : v ∈ F.completingOppositeVertices)
    (hvf : F.IsSameMinFrameCompletion hne v) :
    (⟨F.supportOverMin hne v, F.card_supportOverMin hne hvf⟩ :
        KSubset (d + 1) (N - ∑ i, F.coordMin hne i)) ∈
      KSubsetCollection.sameFrameExtensions
        (F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw)) := by
  classical
  have hvnotin : v ∉ F.vertices := ((F.mem_completingOppositeVertices_iff v).mp hvc).1
  rw [KSubsetCollection.mem_sameFrameExtensions_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_slift]
    rintro ⟨w, hwF, hweq⟩
    apply hvnotin
    have hvw : v = w :=
      F.sameMinFrame_eq_of_supportOverMin_eq hne hvf (F.vertex_isSameMinFrame hne hwF) hweq.symm
    rw [hvw]; exact hwF
  · rw [← F.slift_insert_eq_insert hne hvf hvnotin]
    exact F.slift_insert_maximal hne hvc hvf

/-- (the same-min-frame / fixed-SLICE half of the Freudenthal flip): a facet has at
most two same-min-frame completions.  Lifts the combinatorial fixed-slice milestone
`KSubsetCollection.sameFrame_extensions_card_le_two_of_erase_maximalSorted` through the
`supportOverMin` injection, with the wall realised as `C.erase φ₀` for the maximal collection
`C = slift (insert v₀ F.vertices)` of any one completion `v₀`. -/
theorem sameMinFrameCompletions_card_le_two {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) : (F.sameMinFrameCompletions hne).card ≤ 2 := by
  classical
  set wall := F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw) with hwall
  rcases (F.sameMinFrameCompletions hne).eq_empty_or_nonempty with hemp | ⟨v₀, hv₀⟩
  · rw [hemp]; exact Nat.zero_le 2
  rw [sameMinFrameCompletions, Finset.mem_filter] at hv₀
  obtain ⟨hv₀c, hv₀f⟩ := hv₀
  set φ₀ : KSubset (d + 1) (N - ∑ i, F.coordMin hne i) :=
    ⟨F.supportOverMin hne v₀, F.card_supportOverMin hne hv₀f⟩ with hφ₀
  have hv₀notin : v₀ ∉ F.vertices := ((F.mem_completingOppositeVertices_iff v₀).mp hv₀c).1
  have hC₀ : KSubsetCollection.IsMaximalSorted (insert φ₀ wall) := by
    rw [hφ₀, ← F.slift_insert_eq_insert hne hv₀f hv₀notin]
    exact F.slift_insert_maximal hne hv₀c hv₀f
  have hφ₀notin : φ₀ ∉ wall := by
    rw [hwall, mem_slift]
    rintro ⟨w, hwF, hweq⟩
    apply hv₀notin
    have : v₀ = w :=
      F.sameMinFrame_eq_of_supportOverMin_eq hne hv₀f (F.vertex_isSameMinFrame hne hwF) hweq.symm
    rw [this]; exact hwF
  have hbound : (KSubsetCollection.sameFrameExtensions wall).card ≤ 2 := by
    rw [show wall = (insert φ₀ wall).erase φ₀ from (Finset.erase_insert hφ₀notin).symm]
    exact KSubsetCollection.sameFrame_extensions_card_le_two_of_erase_maximalSorted hC₀
      (Finset.mem_insert_self _ _)
  have hinj : Set.InjOn (F.supportOverMin hne) (↑(F.sameMinFrameCompletions hne)) :=
    F.supportOverMin_injOn_sameMinFrameCompletions hne
  have hsub : (F.sameMinFrameCompletions hne).image (F.supportOverMin hne) ⊆
      (KSubsetCollection.sameFrameExtensions wall).image Subtype.val := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [sameMinFrameCompletions, Finset.mem_filter] at hv
    rw [Finset.mem_image]
    exact ⟨⟨F.supportOverMin hne v, F.card_supportOverMin hne hv.2⟩,
      F.support_mem_sameFrameExtensions hne hv.1 hv.2, rfl⟩
  calc (F.sameMinFrameCompletions hne).card
      = ((F.sameMinFrameCompletions hne).image (F.supportOverMin hne)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((KSubsetCollection.sameFrameExtensions wall).image Subtype.val).card :=
        Finset.card_le_card hsub
    _ ≤ (KSubsetCollection.sameFrameExtensions wall).card := Finset.card_image_le
    _ ≤ 2 := hbound


/-! ### Lowered-frame lift: reduce `lowerCompletions.card ≤ 1` to the pure gap-fill -/


/-- The lowered coordinate frame: `coordMin`, dropped by one at the lowering coordinate `j₀`. -/
noncomputable def lowerFrame {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (j₀ : Fin (d + 1)) : Fin (d + 1) → ℕ :=
  fun i => if i = j₀ then F.coordMin hne i - 1 else F.coordMin hne i

theorem lowerFrame_apply {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (j₀ i : Fin (d + 1)) :
    F.lowerFrame hne j₀ i = if i = j₀ then F.coordMin hne i - 1 else F.coordMin hne i := rfl

/-- Support of a vertex over the lowered frame (a `Finset (Fin (d+1))`). -/
noncomputable def lowerSupport {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (j₀ : Fin (d + 1)) (w : SimplexGrid d N) : Finset (Fin (d + 1)) :=
  Finset.univ.filter fun i => F.lowerFrame hne j₀ i < w.1 i

theorem mem_lowerSupport {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (j₀ : Fin (d + 1)) (w : SimplexGrid d N) (i : Fin (d + 1)) :
    i ∈ F.lowerSupport hne j₀ w ↔ F.lowerFrame hne j₀ i < w.1 i := by
  simp [lowerSupport]

/-- A point lies in the lowered frame band: each coordinate is `lowerFrame` or `lowerFrame + 1`. -/
def IsLowerFrameBand {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (j₀ : Fin (d + 1)) (w : SimplexGrid d N) : Prop :=
  ∀ i, w.1 i = F.lowerFrame hne j₀ i ∨ w.1 i = F.lowerFrame hne j₀ i + 1

/-- In the lowered frame `lowerFrame = base + χ(cp)`, a vertex `base + χ(T)` has support `T \ cp`. -/
theorem lowerSupport_eq_sdiff {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (j₀ : Fin (d + 1)) {base : Fin (d + 1) → ℕ}
    {cp : Finset (Fin (d + 1))} {w : SimplexGrid d N} {T : Finset (Fin (d + 1))}
    (hframe : ∀ i, F.lowerFrame hne j₀ i = base i + (if i ∈ cp then 1 else 0))
    (hw : ∀ i, w.1 i = base i + chi T i) :
    F.lowerSupport hne j₀ w = T \ cp := by
  classical
  ext i
  rw [mem_lowerSupport, Finset.mem_sdiff, hw i, hframe i, chi]
  by_cases hiT : i ∈ T <;> by_cases hicp : i ∈ cp <;> simp [hiT, hicp] <;> omega

/-- A band point's lower support has card `N - ∑ lowerFrame`. -/
theorem card_lowerSupport {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (j₀ : Fin (d + 1)) {w : SimplexGrid d N}
    (hw : F.IsLowerFrameBand hne j₀ w) :
    (F.lowerSupport hne j₀ w).card = N - ∑ i, F.lowerFrame hne j₀ i := by
  classical
  have hpt : ∀ i, w.1 i =
      F.lowerFrame hne j₀ i + (if i ∈ F.lowerSupport hne j₀ w then 1 else 0) := by
    intro i
    by_cases hi : i ∈ F.lowerSupport hne j₀ w
    · rw [if_pos hi]; rw [F.mem_lowerSupport] at hi; rcases hw i with h | h
      · omega
      · omega
    · rw [if_neg hi]; rw [F.mem_lowerSupport] at hi; rcases hw i with h | h
      · exact h
      · omega
  have hsum : ∑ i : Fin (d + 1), w.1 i = N := w.2
  have hkey : ∑ i : Fin (d + 1), w.1 i =
      (∑ i : Fin (d + 1), F.lowerFrame hne j₀ i) + (F.lowerSupport hne j₀ w).card := by
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
  omega

/-- A band point is recovered from its lower support: the lower support map is injective. -/
theorem lowerFrameBand_eq_of_lowerSupport_eq {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (j₀ : Fin (d + 1)) {v w : SimplexGrid d N}
    (hv : F.IsLowerFrameBand hne j₀ v) (hw : F.IsLowerFrameBand hne j₀ w)
    (h : F.lowerSupport hne j₀ v = F.lowerSupport hne j₀ w) : v = w := by
  classical
  apply Subtype.ext; funext i
  have hiff : (F.lowerFrame hne j₀ i < v.1 i) ↔ (F.lowerFrame hne j₀ i < w.1 i) := by
    rw [← mem_lowerSupport, ← mem_lowerSupport, h]
  rcases hv i with hvi | hvi <;> rcases hw i with hwi | hwi <;> omega

/-- From a nonempty lower-completion set, pick the (unique) lowering coordinate
`j₀`; every lower completion dips at `j₀`. -/
theorem exists_unique_lowering_coord_of_lower_nonempty {d N : ℕ} (hd : 2 ≤ d)
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    (hlne : (F.lowerCompletions hne).Nonempty) :
    ∃ j₀ : Fin (d + 1), ∀ v ∈ F.lowerCompletions hne, v.1 j₀ + 1 = F.coordMin hne j₀ := by
  obtain ⟨v₀, hv₀⟩ := hlne
  obtain ⟨j₀, hj₀⟩ := ((F.mem_lowerCompletions hne v₀).mp hv₀).2
  refine ⟨j₀, fun v hv => ?_⟩
  obtain ⟨jv, hjv⟩ := ((F.mem_lowerCompletions hne v).mp hv).2
  have hjeq : jv = j₀ := F.lowering_coord_unique hd hne hv hv₀ hjv hj₀
  rw [← hjeq]; exact hjv

/-- **Wall band.** Every wall vertex lies in the lowered frame band (and equals
`coordMin = lowerFrame + 1` at the frozen `j₀`). -/
theorem vertex_isLowerFrameBand {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (j₀ : Fin (d + 1))
    (hj0const : F.coordMin hne j₀ = F.coordMax hne j₀) (hj0pos : 1 ≤ F.coordMin hne j₀)
    {w : SimplexGrid d N} (hw : w ∈ F.vertices) : F.IsLowerFrameBand hne j₀ w := by
  classical
  intro i
  by_cases hij : i = j₀
  · subst hij
    have h1 : F.coordMin hne i ≤ w.1 i :=
      Finset.min'_le _ (w.1 i) (Finset.mem_image_of_mem (fun x => x.1 i) hw)
    have h2 : w.1 i ≤ F.coordMax hne i :=
      Finset.le_max' _ (w.1 i) (Finset.mem_image_of_mem (fun x => x.1 i) hw)
    right; rw [lowerFrame_apply, if_pos rfl]; omega
  · have hband := F.vertex_isSameMinFrame hne hw i
    rw [lowerFrame_apply, if_neg hij]; exact hband

/-- **Completion band.** A lower completion (dipping at `j₀`) lies in the lowered
frame band: at `j₀` it equals `coordMin − 1 = lowerFrame`; elsewhere `coordMin` or `coordMin+1`. -/
theorem lowerCompletion_isLowerFrameBand {d N : ℕ} (hd : 2 ≤ d)
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) (j₀ : Fin (d + 1))
    (hj0const : F.coordMin hne j₀ = F.coordMax hne j₀) {v : SimplexGrid d N}
    (hvc : v ∈ F.completingOppositeVertices) (hvdip : v.1 j₀ + 1 = F.coordMin hne j₀) :
    F.IsLowerFrameBand hne j₀ v := by
  classical
  intro i
  by_cases hij : i = j₀
  · subst hij; left; rw [lowerFrame_apply, if_pos rfl]; omega
  · rw [lowerFrame_apply, if_neg hij]
    have hnotconst : F.coordMin hne i ≠ F.coordMax hne i := fun hc =>
      hij (F.constant_coord_unique hd hne hc hj0const)
    have hmesh := F.coordMax_le_coordMin_succ hne i
    have hle : F.coordMin hne i ≤ F.coordMax hne i := Finset.min'_le_max' _ _
    rcases F.completion_coord_cases hvc hne i with h | h | h | h
    · left; exact h
    · right; omega
    · exact absurd (F.completion_upper_coord_imp_constant hvc hne h) hnotconst
    · exact absurd (F.completion_lower_coord_imp_constant hvc hne h) hnotconst

/-- **Lowered frame identity.** For a lower completion `v`, the cell `insert v F.vertices`
realizes the lowered frame: `lowerFrame = base + χ(commonPresent)`. -/
theorem lower_completion_frame {d N : ℕ} (hd : 2 ≤ d)
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) (j₀ : Fin (d + 1))
    (hj0const : F.coordMin hne j₀ = F.coordMax hne j₀) (hj0pos : 1 ≤ F.coordMin hne j₀)
    {v : SimplexGrid d N} (hvc : v ∈ F.completingOppositeVertices)
    (hvdip : v.1 j₀ + 1 = F.coordMin hne j₀) :
    ∃ D : KuhnGridCellData d N, D.vertices = insert v F.vertices ∧
      (∀ i, F.lowerFrame hne j₀ i =
        D.base i + (if i ∈ KSubsetCollection.commonPresent D.subsets then 1 else 0)) := by
  classical
  have hsimplex := ((F.mem_completingOppositeVertices_iff v).mp hvc).2
  obtain ⟨D, hD⟩ := hsimplex
  refine ⟨D, hD, fun i => ?_⟩
  have hDne : D.vertices.Nonempty := by rw [hD]; exact ⟨v, Finset.mem_insert_self _ _⟩
  have hmin := D.min_coord_eq hDne i
  have hvband := F.lowerCompletion_isLowerFrameBand hd hne j₀ hj0const hvc hvdip i
  have hcoord : F.lowerFrame hne j₀ i = (D.vertices.image fun x => x.1 i).min' (hDne.image _) := by
    apply le_antisymm
    · apply Finset.le_min'
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [hD, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · rcases hvband with h | h <;> omega
      · have hwband := F.vertex_isLowerFrameBand hne j₀ hj0const hj0pos hx i
        rcases hwband with h | h <;> omega
    · by_cases hij : i = j₀
      · have hvD : v ∈ D.vertices := by rw [hD]; exact Finset.mem_insert_self _ _
        have hle := Finset.min'_le _ (v.1 i) (Finset.mem_image_of_mem (fun x => x.1 i) hvD)
        have hd2 : v.1 i + 1 = F.coordMin hne i := by rw [hij]; exact hvdip
        have hvi : v.1 i = F.lowerFrame hne j₀ i := by rw [lowerFrame_apply, if_pos hij]; omega
        rw [← hvi]; exact hle
      · obtain ⟨w, hwF, hweq⟩ :=
          Finset.mem_image.mp (Finset.min'_mem (F.vertices.image fun x => x.1 i) (hne.image _))
        have hweq' : w.1 i = F.coordMin hne i := hweq
        have hwD : w ∈ D.vertices := by rw [hD]; exact Finset.mem_insert_of_mem hwF
        have hle := Finset.min'_le _ (w.1 i) (Finset.mem_image_of_mem (fun x => x.1 i) hwD)
        have hlf : F.lowerFrame hne j₀ i = F.coordMin hne i := by rw [lowerFrame_apply, if_neg hij]
        rw [hlf, ← hweq']; exact hle
  rw [hcoord]; exact hmin

/-- The lower support-lift of a band set of points, in the uniform type `KSubset (d+1) (N − ∑lowerFrame)`. -/
noncomputable def lowerSlift {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (j₀ : Fin (d + 1)) (P : Finset (SimplexGrid d N))
    (hP : ∀ w ∈ P, F.IsLowerFrameBand hne j₀ w) :
    Finset (KSubset (d + 1) (N - ∑ i, F.lowerFrame hne j₀ i)) :=
  P.attach.image (fun w => ⟨F.lowerSupport hne j₀ w.1, F.card_lowerSupport hne j₀ (hP w.1 w.2)⟩)

theorem mem_lowerSlift {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (j₀ : Fin (d + 1)) {P : Finset (SimplexGrid d N)}
    {hP : ∀ w ∈ P, F.IsLowerFrameBand hne j₀ w}
    {T : KSubset (d + 1) (N - ∑ i, F.lowerFrame hne j₀ i)} :
    T ∈ F.lowerSlift hne j₀ P hP ↔ ∃ w ∈ P, F.lowerSupport hne j₀ w = T.1 := by
  classical
  rw [lowerSlift, Finset.mem_image]
  constructor
  · rintro ⟨w, _, hw⟩; exact ⟨w.1, w.2, congrArg Subtype.val hw⟩
  · rintro ⟨w, hw, hwT⟩; exact ⟨⟨w, hw⟩, Finset.mem_attach _ _, Subtype.ext hwT⟩

theorem hP_lower_insert {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (j₀ : Fin (d + 1)) {v : SimplexGrid d N}
    (hvband : F.IsLowerFrameBand hne j₀ v)
    (hbandF : ∀ w ∈ F.vertices, F.IsLowerFrameBand hne j₀ w) :
    ∀ w ∈ insert v F.vertices, F.IsLowerFrameBand hne j₀ w := by
  intro w hw
  rw [Finset.mem_insert] at hw
  rcases hw with rfl | hw
  · exact hvband
  · exact hbandF w hw

/-- The lower support-lift is injective on bands: its card equals the source card. -/
theorem lowerSlift_card_of_band {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (j₀ : Fin (d + 1)) (P : Finset (SimplexGrid d N))
    (hP : ∀ w ∈ P, F.IsLowerFrameBand hne j₀ w) :
    (F.lowerSlift hne j₀ P hP).card = P.card := by
  classical
  rw [lowerSlift, Finset.card_image_of_injOn (by
    intro a _ b _ hab
    apply Subtype.ext
    exact F.lowerFrameBand_eq_of_lowerSupport_eq hne j₀ (hP a.1 a.2) (hP b.1 b.2)
      (congrArg Subtype.val hab)), Finset.card_attach]

/-- Inserting a lower completion's support-lift recovers the reduced parent collection
(in the lowered frame), hence is maximal sorted. -/
theorem lowerSlift_insert_maximal {d N : ℕ} (hd : 2 ≤ d)
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) (j₀ : Fin (d + 1))
    (hj0const : F.coordMin hne j₀ = F.coordMax hne j₀) (hj0pos : 1 ≤ F.coordMin hne j₀)
    {v : SimplexGrid d N} (hvc : v ∈ F.completingOppositeVertices)
    (hvdip : v.1 j₀ + 1 = F.coordMin hne j₀)
    (hvband : F.IsLowerFrameBand hne j₀ v)
    (hbandF : ∀ w ∈ F.vertices, F.IsLowerFrameBand hne j₀ w) :
    KSubsetCollection.IsMaximalSorted
      (F.lowerSlift hne j₀ (insert v F.vertices) (F.hP_lower_insert hne j₀ hvband hbandF)) := by
  classical
  obtain ⟨D, hD, hframe⟩ := F.lower_completion_frame hd hne j₀ hj0const hj0pos hvc hvdip
  have hcp : ∀ S ∈ D.subsets, KSubsetCollection.commonPresent D.subsets ⊆ S.1 :=
    fun S hS i hi => (KSubsetCollection.mem_commonPresent_iff D.subsets i).mp hi S hS
  have hm : ∀ S ∈ D.subsets,
      (S.1 \ KSubsetCollection.commonPresent D.subsets).card = N - ∑ i, F.lowerFrame hne j₀ i := by
    intro S hS
    have hcard : (S.1 \ KSubsetCollection.commonPresent D.subsets).card
        + (KSubsetCollection.commonPresent D.subsets).card = D.k := by
      rw [← Finset.card_union_of_disjoint Finset.sdiff_disjoint,
        Finset.sdiff_union_of_subset (hcp S hS), S.2]
    have hsumcoord : ∑ i, F.lowerFrame hne j₀ i =
        (∑ i, D.base i) + (KSubsetCollection.commonPresent D.subsets).card := by
      rw [Finset.sum_congr rfl (fun i _ => hframe i), Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
    have hsum := D.sum_base_add_k
    omega
  have hrel : F.lowerSlift hne j₀ (insert v F.vertices) (F.hP_lower_insert hne j₀ hvband hbandF)
      = KSubsetReduction.reducedColl D.subsets (KSubsetCollection.commonPresent D.subsets)
          (N - ∑ i, F.lowerFrame hne j₀ i) hm := by
    ext T
    rw [mem_lowerSlift, KSubsetReduction.mem_reducedColl]
    have hsupp : ∀ S : KSubset (d + 1) D.k, F.lowerSupport hne j₀ (cellVertexMap D S)
        = S.1 \ KSubsetCollection.commonPresent D.subsets :=
      fun S => F.lowerSupport_eq_sdiff hne j₀ hframe (fun i => rfl)
    constructor
    · rintro ⟨w, hw, hwT⟩
      rw [← hD, cellVertexMap_vertices, Finset.mem_image] at hw
      obtain ⟨S, hS, rfl⟩ := hw
      exact ⟨S, hS, by rw [← hsupp S]; exact hwT⟩
    · rintro ⟨S, hS, hST⟩
      exact ⟨cellVertexMap D S, by rw [← hD, cellVertexMap_vertices]; exact Finset.mem_image_of_mem _ hS,
        by rw [hsupp S]; exact hST⟩
  rw [hrel]
  exact KSubsetReduction.reducedColl_isMaximalSorted D.hsubsets _ hcp _ hm

theorem lowerSlift_insert_eq_insert {d N : ℕ} (F : KuhnGeometricGridFacet d N)
    (hne : F.vertices.Nonempty) (j₀ : Fin (d + 1)) {v : SimplexGrid d N}
    (hvband : F.IsLowerFrameBand hne j₀ v)
    (hbandF : ∀ w ∈ F.vertices, F.IsLowerFrameBand hne j₀ w) (hvnotin : v ∉ F.vertices) :
    F.lowerSlift hne j₀ (insert v F.vertices) (F.hP_lower_insert hne j₀ hvband hbandF)
      = insert ⟨F.lowerSupport hne j₀ v, F.card_lowerSupport hne j₀ hvband⟩
          (F.lowerSlift hne j₀ F.vertices hbandF) := by
  classical
  ext T
  rw [Finset.mem_insert, mem_lowerSlift, mem_lowerSlift]
  constructor
  · rintro ⟨w, hw, hwT⟩
    rw [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · exact Or.inl (Subtype.ext hwT).symm
    · exact Or.inr ⟨w, hw, hwT⟩
  · rintro (rfl | ⟨w, hw, hwT⟩)
    · exact ⟨v, Finset.mem_insert_self _ _, rfl⟩
    · exact ⟨w, Finset.mem_insert_of_mem hw, hwT⟩

/-- **The geometric lift.** The lower-completion bound reduces to the pure
combinatorial gap-fill: a facet has at most one lower completion, given the gap-fill theorem. -/
theorem lowerCompletions_card_le_one_of_gapFill {d N : ℕ} (hd : 2 ≤ d)
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    (hgap : ∀ {n k : ℕ} {W : Finset (KSubset n k)} {j₀ : Fin n},
        (∀ S ∈ W, j₀ ∈ S.1) → (KSubsetCollection.lowerGapFillExtensions W j₀).card ≤ 1) :
    (F.lowerCompletions hne).card ≤ 1 := by
  classical
  by_cases hlne : (F.lowerCompletions hne).Nonempty
  · obtain ⟨j₀, hj₀dip⟩ := F.exists_unique_lowering_coord_of_lower_nonempty hd hne hlne
    obtain ⟨v₀, hv₀⟩ := hlne
    have hv₀c : v₀ ∈ F.completingOppositeVertices := ((F.mem_lowerCompletions hne v₀).mp hv₀).1
    have hj0pos : 1 ≤ F.coordMin hne j₀ := by have := hj₀dip v₀ hv₀; omega
    have hj0const : F.coordMin hne j₀ = F.coordMax hne j₀ :=
      F.completion_lower_coord_imp_constant hv₀c hne (hj₀dip v₀ hv₀)
    have hbandF : ∀ w ∈ F.vertices, F.IsLowerFrameBand hne j₀ w :=
      fun w hw => F.vertex_isLowerFrameBand hne j₀ hj0const hj0pos hw
    set wall := F.lowerSlift hne j₀ F.vertices hbandF with hwall
    have hwallj0 : ∀ S ∈ wall, j₀ ∈ S.1 := by
      intro S hS
      rw [hwall, mem_lowerSlift] at hS
      obtain ⟨w, hwF, hwS⟩ := hS
      rw [← hwS, F.mem_lowerSupport, lowerFrame_apply, if_pos rfl]
      have h1 : F.coordMin hne j₀ ≤ w.1 j₀ :=
        Finset.min'_le _ (w.1 j₀) (Finset.mem_image_of_mem (fun x => x.1 j₀) hwF)
      omega
    have hbandL : ∀ v ∈ F.lowerCompletions hne, F.IsLowerFrameBand hne j₀ v := fun v hv =>
      F.lowerCompletion_isLowerFrameBand hd hne j₀ hj0const
        (((F.mem_lowerCompletions hne v).mp hv).1) (hj₀dip v hv)
    have hmapsto : ∀ S ∈ F.lowerSlift hne j₀ (F.lowerCompletions hne) hbandL,
        S ∈ KSubsetCollection.lowerGapFillExtensions wall j₀ := by
      intro S hS
      rw [mem_lowerSlift] at hS
      obtain ⟨v, hv, hvS⟩ := hS
      have hvc := ((F.mem_lowerCompletions hne v).mp hv).1
      have hvdip := hj₀dip v hv
      have hvnotin : v ∉ F.vertices := ((F.mem_completingOppositeVertices_iff v).mp hvc).1
      have hvband := hbandL v hv
      have hj0notin : j₀ ∉ F.lowerSupport hne j₀ v := by
        rw [F.mem_lowerSupport, lowerFrame_apply, if_pos rfl]; omega
      have hj0notinS : j₀ ∉ S.1 := by rw [← hvS]; exact hj0notin
      rw [KSubsetCollection.mem_lowerGapFillExtensions_iff,
        KSubsetCollection.mem_sameFrameExtensions_iff]
      refine ⟨⟨fun hSwall => hj0notinS (hwallj0 S hSwall), ?_⟩, hj0notinS⟩
      have heq : insert S wall = F.lowerSlift hne j₀ (insert v F.vertices)
          (F.hP_lower_insert hne j₀ hvband hbandF) := by
        rw [F.lowerSlift_insert_eq_insert hne j₀ hvband hbandF hvnotin, ← hwall]
        congr 1
        exact Subtype.ext hvS.symm
      rw [heq]
      exact F.lowerSlift_insert_maximal hd hne j₀ hj0const hj0pos hvc hvdip hvband hbandF
    calc (F.lowerCompletions hne).card
        = (F.lowerSlift hne j₀ (F.lowerCompletions hne) hbandL).card :=
          (F.lowerSlift_card_of_band hne j₀ _ hbandL).symm
      _ ≤ (KSubsetCollection.lowerGapFillExtensions wall j₀).card := Finset.card_le_card hmapsto
      _ ≤ 1 := hgap hwallj0
  · rw [Finset.not_nonempty_iff_eq_empty.mp hlne, Finset.card_empty]; exact Nat.zero_le 1

end KuhnGeometricGridFacet

/-! ### Conditional local-flip assembly (on the single pure gap-fill hypothesis)

Packages the pure combinatorial residual as `KSubsetCollection.LowerGapFillHypothesis`,
then proves the full local incidence (`completingOppositeVertices.card ≤ 2`,
`incidentCells.card = 1 ∨ 2`) CONDITIONAL on it.  Includes the complement bridge
(deriving the UPPER gap-fill from the lower hypothesis) and cell non-degeneracy. -/

/-- The pure combinatorial gap-fill residual, packaged as one named hypothesis. -/
def KSubsetCollection.LowerGapFillHypothesis : Prop :=
  ∀ {n k : ℕ} {W : Finset (KSubset n k)} {j₀ : Fin n},
    (∀ S ∈ W, j₀ ∈ S.1) → (KSubsetCollection.lowerGapFillExtensions W j₀).card ≤ 1

/-! ### Complement bridge (to derive the upper gap-fill from the lower hypothesis) -/

/-- Complement of a `k`-subset: an `(n-k)`-subset. -/
def KSubset.compl {n k : ℕ} (S : KSubset n k) : KSubset n (n - k) :=
  ⟨S.1ᶜ, by rw [Finset.card_compl, Fintype.card_fin, S.2]⟩

theorem KSubset.mem_compl {n k : ℕ} (S : KSubset n k) (i : Fin n) :
    i ∈ (KSubset.compl S).1 ↔ i ∉ S.1 := by
  show i ∈ S.1ᶜ ↔ i ∉ S.1
  simp

theorem KSubset.compl_injective {n k : ℕ} : Function.Injective (KSubset.compl (n := n) (k := k)) := by
  intro S T h
  apply Subtype.ext; ext i
  have h1 : i ∈ (KSubset.compl S).1 ↔ i ∈ (KSubset.compl T).1 := by rw [h]
  rw [KSubset.mem_compl, KSubset.mem_compl] at h1
  exact not_iff_not.mp h1

/-- Prefix counts of `S` and its complement sum to a constant (independent of `S`). -/
theorem KSubset.prefixCount_add_compl {n k : ℕ} (S : KSubset n k) (t : Fin n) :
    S.prefixCount t + (KSubset.compl S).prefixCount t
      = (Finset.univ.filter (fun x : Fin n => x ≤ t)).card := by
  classical
  show (S.1.filter (· ≤ t)).card + (S.1ᶜ.filter (· ≤ t)).card
      = (Finset.univ.filter (fun x : Fin n => x ≤ t)).card
  have hdisj : Disjoint (S.1.filter (· ≤ t)) (S.1ᶜ.filter (· ≤ t)) :=
    Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) disjoint_compl_right)
  rw [← Finset.card_union_of_disjoint hdisj, ← Finset.filter_union, Finset.union_compl]

/-- `SortedBefore` is reversed-and-preserved by complement (forward direction). -/
theorem KSubset.SortedBefore_compl {n k : ℕ} {I J : KSubset n k} (h : I.SortedBefore J) :
    (KSubset.compl J).SortedBefore (KSubset.compl I) := by
  intro t
  have hI := KSubset.prefixCount_add_compl I t
  have hJ := KSubset.prefixCount_add_compl J t
  have ht := h t
  omega

theorem KSubset.IsSortedPair_compl {n k : ℕ} {I J : KSubset n k} (h : KSubset.IsSortedPair I J) :
    KSubset.IsSortedPair (KSubset.compl I) (KSubset.compl J) := by
  rcases h with h | h
  · exact Or.inr (KSubset.SortedBefore_compl h)
  · exact Or.inl (KSubset.SortedBefore_compl h)

/-- Image of a collection under complement. -/
theorem KSubsetCollection.isMaximalSorted_image_compl {n k : ℕ} {A : Finset (KSubset n k)}
    (hA : KSubsetCollection.IsMaximalSorted A) :
    KSubsetCollection.IsMaximalSorted (A.image KSubset.compl) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [Finset.card_image_of_injOn (fun a _ b _ h => KSubset.compl_injective h), hA.1]
  · intro I hI J hJ hIJ
    rw [Finset.mem_image] at hI hJ
    obtain ⟨I0, hI0, rfl⟩ := hI
    obtain ⟨J0, hJ0, rfl⟩ := hJ
    have hne : I0 ≠ J0 := fun h => hIJ (by rw [h])
    exact KSubset.IsSortedPair_compl (hA.2 I0 hI0 J0 hJ0 hne)

theorem KSubsetCollection.mem_sameFrameExtensions_compl {n k : ℕ} {W : Finset (KSubset n k)}
    {T : KSubset n k} (hT : T ∈ KSubsetCollection.sameFrameExtensions W) :
    KSubset.compl T ∈ KSubsetCollection.sameFrameExtensions (W.image KSubset.compl) := by
  classical
  rw [KSubsetCollection.mem_sameFrameExtensions_iff] at hT ⊢
  refine ⟨?_, ?_⟩
  · intro hc
    rw [Finset.mem_image] at hc
    obtain ⟨T0, hT0, hT0eq⟩ := hc
    exact hT.1 (KSubset.compl_injective hT0eq ▸ hT0)
  · rw [show insert (KSubset.compl T) (W.image KSubset.compl)
        = (insert T W).image KSubset.compl from (Finset.image_insert _ _ _).symm]
    exact KSubsetCollection.isMaximalSorted_image_compl hT.2

/-- The UPPER gap-fill (`≤ 1` extension INCLUDING `j₀`, when the wall EXCLUDES `j₀`), derived
from the lower hypothesis by complementation. -/
theorem KSubsetCollection.upperGapFill_extensions_card_le_one
    (hgap : KSubsetCollection.LowerGapFillHypothesis)
    {n k : ℕ} {W : Finset (KSubset n k)} {j₀ : Fin n} (hW : ∀ S ∈ W, j₀ ∉ S.1) :
    ((KSubsetCollection.sameFrameExtensions W).filter (fun T => j₀ ∈ T.1)).card ≤ 1 := by
  classical
  have hWc : ∀ S ∈ W.image KSubset.compl, j₀ ∈ S.1 := by
    intro S hS
    rw [Finset.mem_image] at hS
    obtain ⟨S0, hS0, rfl⟩ := hS
    rw [KSubset.mem_compl]; exact hW S0 hS0
  have hbound := hgap (W := W.image KSubset.compl) (j₀ := j₀) hWc
  have hsub : ((KSubsetCollection.sameFrameExtensions W).filter (fun T => j₀ ∈ T.1)).image
        KSubset.compl ⊆ KSubsetCollection.lowerGapFillExtensions (W.image KSubset.compl) j₀ := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨T, hT, rfl⟩ := hx
    rw [Finset.mem_filter] at hT
    rw [KSubsetCollection.mem_lowerGapFillExtensions_iff]
    refine ⟨KSubsetCollection.mem_sameFrameExtensions_compl hT.1, ?_⟩
    rw [KSubset.mem_compl]; exact not_not.mpr hT.2
  calc ((KSubsetCollection.sameFrameExtensions W).filter (fun T => j₀ ∈ T.1)).card
      = (((KSubsetCollection.sameFrameExtensions W).filter (fun T => j₀ ∈ T.1)).image
          KSubset.compl).card :=
        (Finset.card_image_of_injOn (fun a _ b _ h => KSubset.compl_injective h)).symm
    _ ≤ (KSubsetCollection.lowerGapFillExtensions (W.image KSubset.compl) j₀).card :=
        Finset.card_le_card hsub
    _ ≤ 1 := hbound

/-! ### Cell non-degeneracy: a maximal sorted collection has no frozen coordinate -/

theorem KSubsetCollection.commonPresent_eq_empty_of_isMaximalSorted {n k : ℕ} (hn : 0 < n)
    {A : Finset (KSubset (n + 1) k)} (hA : KSubsetCollection.IsMaximalSorted A) :
    KSubsetCollection.commonPresent A = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  have hbound := KSubsetCollection.sorted_card_le_ground_card hn
    (KSubsetCollection.isSorted_deletePresentCoord hA.2 hp)
  rw [KSubsetCollection.card_deletePresentCoord A p hp, hA.1] at hbound
  omega

theorem KSubsetCollection.commonAbsent_eq_empty_of_isMaximalSorted {n k : ℕ} (hn : 0 < n)
    {A : Finset (KSubset (n + 1) k)} (hA : KSubsetCollection.IsMaximalSorted A) :
    KSubsetCollection.commonAbsent A = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  have hbound := KSubsetCollection.sorted_card_le_ground_card hn
    (KSubsetCollection.isSorted_deleteAbsentCoord hA.2 hp)
  rw [KSubsetCollection.card_deleteAbsentCoord A p hp, hA.1] at hbound
  omega

/-- CHARACTERIZATION (the `c = 1` up-side, second structural fact): any same-frame extension `T` of
a common-absent wall MUST CONTAIN the common-absent coordinate `c`.  (Otherwise `c` would be
common-absent in the maximal `insert T W`, contradicting `commonAbsent_eq_empty_of_isMaximalSorted`.)
So — together with `isMaximalSorted_deleteAbsentCoord_of_card_eq` (the wall deletes to maximal) — the
unique extension is exactly the `c`-reinsertion `S \ {e} ∪ {c}` of the deleted maximal collection;
only the (wall-dependent) choice of `e` and the sorted-compatibility proof remain. -/
theorem KSubsetCollection.mem_of_commonAbsent_of_sameFrameExtension {n k : ℕ} (hn : 0 < n)
    {W : Finset (KSubset (n + 1) k)} {c : Fin (n + 1)}
    (hc : c ∈ KSubsetCollection.commonAbsent W)
    {T : KSubset (n + 1) k} (hT : T ∈ KSubsetCollection.sameFrameExtensions W) :
    c ∈ T.1 := by
  classical
  rw [KSubsetCollection.mem_sameFrameExtensions_iff] at hT
  by_contra hcT
  have hca : c ∈ KSubsetCollection.commonAbsent (insert T W) := by
    rw [KSubsetCollection.mem_commonAbsent_iff]
    intro S hS
    rw [Finset.mem_insert] at hS
    rcases hS with rfl | hS
    · exact hcT
    · exact (KSubsetCollection.mem_commonAbsent_iff W c).mp hc S hS
  rw [KSubsetCollection.commonAbsent_eq_empty_of_isMaximalSorted hn hT.2] at hca
  exact absurd hca (Finset.notMem_empty c)

/-! ### DOWN-side: complement-bridge existence (the dual of the up-side capstone)

`sameFrameExtensions`/`IsSortedPair` depend only on the underlying `Finset (Fin n)`, so they
TRANSPORT across the level index (e.g. the `n - (n - k) = k` "double-complement" mismatch).  These
congruence lemmas let us pull a same-frame extension of `W.image compl` (common-absent) back to a
`lowerGapFillExtension` of `W` (common-present), reusing the proven up-side capstone. -/

/-- Prefix count depends only on the underlying set, so it transports across the level index. -/
theorem KSubset.prefixCount_congr {n k k' : ℕ} {I : KSubset n k} {I' : KSubset n k'}
    (h : I.1 = I'.1) (t : Fin n) : I.prefixCount t = I'.prefixCount t := by
  show (I.1.filter (· ≤ t)).card = (I'.1.filter (· ≤ t)).card
  rw [h]

theorem KSubset.sortedBefore_congr {n k k' : ℕ} {I J : KSubset n k} {I' J' : KSubset n k'}
    (hI : I.1 = I'.1) (hJ : J.1 = J'.1) (h : I.SortedBefore J) : I'.SortedBefore J' := by
  intro t
  rw [← KSubset.prefixCount_congr hI t, ← KSubset.prefixCount_congr hJ t]
  exact h t

theorem KSubset.isSortedPair_congr {n k k' : ℕ} {I J : KSubset n k} {I' J' : KSubset n k'}
    (hI : I.1 = I'.1) (hJ : J.1 = J'.1) (h : KSubset.IsSortedPair I J) :
    KSubset.IsSortedPair I' J' := by
  rcases h with h | h
  · exact Or.inl (KSubset.sortedBefore_congr hI hJ h)
  · exact Or.inr (KSubset.sortedBefore_congr hJ hI h)

/-- Complementing the wall swaps common-present ↔ common-absent. -/
theorem KSubsetCollection.commonAbsent_image_compl {n k : ℕ} (W : Finset (KSubset n k)) :
    KSubsetCollection.commonAbsent (W.image KSubset.compl) = KSubsetCollection.commonPresent W := by
  classical
  ext i
  rw [KSubsetCollection.mem_commonAbsent_iff, KSubsetCollection.mem_commonPresent_iff]
  constructor
  · intro h S hS
    have h2 := h (KSubset.compl S) (Finset.mem_image_of_mem _ hS)
    rw [KSubset.mem_compl] at h2; exact not_not.mp h2
  · intro h S' hS'
    rw [Finset.mem_image] at hS'
    obtain ⟨S, hS, rfl⟩ := hS'
    rw [KSubset.mem_compl]; exact not_not.mpr (h S hS)

theorem KSubsetCollection.commonPresent_image_compl {n k : ℕ} (W : Finset (KSubset n k)) :
    KSubsetCollection.commonPresent (W.image KSubset.compl) = KSubsetCollection.commonAbsent W := by
  classical
  ext i
  rw [KSubsetCollection.mem_commonPresent_iff, KSubsetCollection.mem_commonAbsent_iff]
  constructor
  · intro h S hS
    have h2 := h (KSubset.compl S) (Finset.mem_image_of_mem _ hS)
    rw [KSubset.mem_compl] at h2; exact h2
  · intro h S' hS'
    rw [Finset.mem_image] at hS'
    obtain ⟨S, hS, rfl⟩ := hS'
    rw [KSubset.mem_compl]; exact h S hS

theorem KSubsetCollection.frozenCoords_image_compl {n k : ℕ} (W : Finset (KSubset n k)) :
    KSubsetCollection.frozenCoords (W.image KSubset.compl) = KSubsetCollection.frozenCoords W := by
  rw [KSubsetCollection.frozenCoords, KSubsetCollection.frozenCoords,
    KSubsetCollection.commonPresent_image_compl, KSubsetCollection.commonAbsent_image_compl,
    Finset.union_comm]

/-- Sortedness is preserved by complement (the non-maximal half of `isMaximalSorted_image_compl`). -/
theorem KSubsetCollection.isSorted_image_compl {n k : ℕ} {W : Finset (KSubset n k)}
    (hW : KSubsetCollection.IsSorted W) : KSubsetCollection.IsSorted (W.image KSubset.compl) := by
  classical
  intro I hI J hJ hIJ
  rw [Finset.mem_image] at hI hJ
  obtain ⟨I0, hI0, rfl⟩ := hI
  obtain ⟨J0, hJ0, rfl⟩ := hJ
  have hne : I0 ≠ J0 := fun h => hIJ (by rw [h])
  exact KSubset.IsSortedPair_compl (hW I0 hI0 J0 hJ0 hne)

/-- DUAL of `mem_of_commonAbsent_of_sameFrameExtension`: any same-frame extension of a
common-PRESENT wall OMITS the common-present coordinate (else it would be common-present in the
maximal `insert T W`, contradicting `commonPresent_eq_empty_of_isMaximalSorted`). -/
theorem KSubsetCollection.notMem_of_commonPresent_of_sameFrameExtension {n k : ℕ} (hn : 0 < n)
    {W : Finset (KSubset (n + 1) k)} {c : Fin (n + 1)}
    (hc : c ∈ KSubsetCollection.commonPresent W)
    {T : KSubset (n + 1) k} (hT : T ∈ KSubsetCollection.sameFrameExtensions W) :
    c ∉ T.1 := by
  classical
  rw [KSubsetCollection.mem_sameFrameExtensions_iff] at hT
  intro hcT
  have hcp : c ∈ KSubsetCollection.commonPresent (insert T W) := by
    rw [KSubsetCollection.mem_commonPresent_iff]
    intro S hS
    rw [Finset.mem_insert] at hS
    rcases hS with rfl | hS
    · exact hcT
    · exact (KSubsetCollection.mem_commonPresent_iff W c).mp hc S hS
  rw [KSubsetCollection.commonPresent_eq_empty_of_isMaximalSorted hn hT.2] at hcp
  exact absurd hcp (Finset.notMem_empty c)

/-- **DOWN-side combinatorial existence.**  A codimension-one sorted wall whose unique
frozen coordinate `c` is COMMON-PRESENT has a same-frame extension that OMITS `c` (a
`lowerGapFillExtension`).  Proof: the complement `W.image compl` is common-ABSENT one-frozen, so the
proven up-side capstone gives an extension `U`; `mem_of_commonAbsent_…` forces `c ∈ U`; the
underlying-set complement `T = U.1ᶜ` is then a same-frame extension of `W` (via the level-index
`isSortedPair_congr` transport) that omits `c`. -/
theorem KSubsetCollection.lowerGapFillExtensions_nonempty_of_commonPresent_oneFrozen {n k : ℕ}
    (hn : 0 < n) {W : Finset (KSubset (n + 1) k)} (hWsorted : KSubsetCollection.IsSorted W)
    (hWne : W.Nonempty) (hWcard : W.card = n) {c : Fin (n + 1)}
    (hc : c ∈ KSubsetCollection.commonPresent W) (hone : (KSubsetCollection.frozenCoords W).card = 1) :
    (KSubsetCollection.lowerGapFillExtensions W c).Nonempty := by
  classical
  set Wc := W.image KSubset.compl with hWc
  have hWcsorted : KSubsetCollection.IsSorted Wc := KSubsetCollection.isSorted_image_compl hWsorted
  have hWcne : Wc.Nonempty := hWne.image _
  have hWccard : Wc.card = n := by
    rw [hWc, Finset.card_image_of_injOn (fun a _ b _ h => KSubset.compl_injective h), hWcard]
  have hcabs : c ∈ KSubsetCollection.commonAbsent Wc := by
    rw [hWc, KSubsetCollection.commonAbsent_image_compl]; exact hc
  have honeC : (KSubsetCollection.frozenCoords Wc).card = 1 := by
    rw [hWc, KSubsetCollection.frozenCoords_image_compl]; exact hone
  obtain ⟨U, hU⟩ := KSubsetCollection.sameFrameExtensions_nonempty_of_commonAbsent_oneFrozen
    hWcsorted hWcne (hWccard.trans (by omega)) hcabs honeC
  have hcU : c ∈ U.1 := KSubsetCollection.mem_of_commonAbsent_of_sameFrameExtension hn hcabs hU
  have hk_le : k ≤ n + 1 := by
    obtain ⟨S, hS⟩ := hWne
    calc k = S.1.card := S.2.symm
      _ ≤ (Finset.univ : Finset (Fin (n + 1))).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n + 1 := by rw [Finset.card_univ, Fintype.card_fin]
  have hTcard : (U.1ᶜ : Finset (Fin (n + 1))).card = k := by
    rw [Finset.card_compl, Fintype.card_fin, U.2]; omega
  set T : KSubset (n + 1) k := ⟨U.1ᶜ, hTcard⟩ with hT
  have hcnT : c ∉ T.1 := by rw [hT]; show c ∉ U.1ᶜ; rw [Finset.mem_compl]; exact not_not.mpr hcU
  rw [KSubsetCollection.mem_sameFrameExtensions_iff] at hU
  obtain ⟨hUnotin, hUmax⟩ := hU
  have hTnotin : T ∉ W := by
    intro hTW
    refine hUnotin ?_
    rw [hWc, Finset.mem_image]
    exact ⟨T, hTW, Subtype.ext (by show T.1ᶜ = U.1; rw [hT]; exact compl_compl U.1)⟩
  have hTpair : ∀ S ∈ W, KSubset.IsSortedPair T S := by
    intro S hS
    have hcSWc : KSubset.compl S ∈ Wc := by rw [hWc]; exact Finset.mem_image_of_mem _ hS
    have hUneCS : U ≠ KSubset.compl S := fun h => hUnotin (h ▸ hcSWc)
    have hUcS : KSubset.IsSortedPair U (KSubset.compl S) :=
      hUmax.2 U (Finset.mem_insert_self _ _) (KSubset.compl S)
        (Finset.mem_insert_of_mem hcSWc) hUneCS
    refine KSubset.isSortedPair_congr ?_ ?_ (KSubset.IsSortedPair_compl hUcS)
    · exact congrArg Subtype.val hT.symm
    · show (KSubset.compl (KSubset.compl S)).1 = S.1
      exact compl_compl S.1
  have hTWsorted : KSubsetCollection.IsSorted (insert T W) := by
    intro I hI J hJ hIJ
    rw [Finset.mem_insert] at hI hJ
    rcases hI with rfl | hI <;> rcases hJ with rfl | hJ
    · exact absurd rfl hIJ
    · exact hTpair J hJ
    · exact (hTpair I hI).symm
    · exact hWsorted I hI J hJ hIJ
  have hTWcard : (insert T W).card = n + 1 := by
    rw [Finset.card_insert_of_notMem hTnotin, hWcard]
  refine ⟨T, ?_⟩
  rw [KSubsetCollection.mem_lowerGapFillExtensions_iff,
    KSubsetCollection.mem_sameFrameExtensions_iff]
  exact ⟨⟨hTnotin, hTWcard, hTWsorted⟩, hcnT⟩

/-! ### lower-completion wrapper -/

theorem KuhnGeometricGridFacet.lowerCompletions_card_le_one {d N : ℕ} (hd : 2 ≤ d)
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    (hgap : KSubsetCollection.LowerGapFillHypothesis) :
    (F.lowerCompletions hne).card ≤ 1 :=
  F.lowerCompletions_card_le_one_of_gapFill hd hne (fun hW => hgap hW)

/-! ### constant-coordinate discriminant -/

noncomputable def KuhnGeometricGridFacet.constantCoords {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) :
    Finset (Fin (d + 1)) :=
  Finset.univ.filter fun i => F.coordMin hne i = F.coordMax hne i

theorem KuhnGeometricGridFacet.mem_constantCoords_iff {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) (i : Fin (d + 1)) :
    i ∈ F.constantCoords hne ↔ F.coordMin hne i = F.coordMax hne i := by
  simp [KuhnGeometricGridFacet.constantCoords]

theorem KuhnGeometricGridFacet.constantCoords_card_le_one {d N : ℕ} (hd : 2 ≤ d)
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) :
    (F.constantCoords hne).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro i hi j hj
  rw [F.mem_constantCoords_iff] at hi hj
  exact F.constant_coord_unique hd hne hi hj

/-! ### `c = 0` ⟹ no lower completions -/

theorem KuhnGeometricGridFacet.lowerCompletions_eq_empty_of_no_constantCoords {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    (hzero : (F.constantCoords hne).card = 0) : F.lowerCompletions hne = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro v hv
  obtain ⟨hvc, j, hj⟩ := (F.mem_lowerCompletions hne v).mp hv
  have hjmem : j ∈ F.constantCoords hne :=
    (F.mem_constantCoords_iff hne j).mpr (F.completion_lower_coord_imp_constant hvc hne hj)
  have : 0 < (F.constantCoords hne).card := Finset.card_pos.mpr ⟨j, hjmem⟩
  omega

/-! ### `c = 1` ⟹ same-min-frame `≤ 1` -/

/-- In the presence of a constant coordinate `j₀`, a same-min-frame completion must dip UP at
`j₀` (`v_{j₀} = coordMin+1`): `v_{j₀} = coordMin` would make the cell `insert v F.vertices`
coplanar at `j₀` (a frozen coordinate of a maximal cell — impossible by non-degeneracy). -/
theorem KuhnGeometricGridFacet.sameMinFrame_mem_supportOverMin_of_constantCoord
    {d N : ℕ} (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    {j₀ : Fin (d + 1)} (hj0const : F.coordMin hne j₀ = F.coordMax hne j₀)
    {v : SimplexGrid d N} (hvc : v ∈ F.completingOppositeVertices)
    (hvf : F.IsSameMinFrameCompletion hne v) : j₀ ∈ F.supportOverMin hne v := by
  classical
  rw [F.mem_supportOverMin]
  rcases hvf j₀ with hlow | hhigh
  · exfalso
    obtain ⟨D, hD⟩ := ((F.mem_completingOppositeVertices_iff v).mp hvc).2
    have hDsub : ∀ S ∈ D.subsets, D.base j₀ + chi S.1 j₀ = F.coordMin hne j₀ := by
      intro S hS
      have hxv : cellVertexMap D S ∈ D.vertices := by
        rw [cellVertexMap_vertices]; exact Finset.mem_image_of_mem _ hS
      rw [hD, Finset.mem_insert] at hxv
      have hx : (cellVertexMap D S).1 j₀ = F.coordMin hne j₀ := by
        rcases hxv with hxv | hxv
        · rw [hxv]; exact hlow
        · have h1 : F.coordMin hne j₀ ≤ (cellVertexMap D S).1 j₀ :=
            Finset.min'_le _ _ (Finset.mem_image_of_mem (fun y => y.1 j₀) hxv)
          have h2 : (cellVertexMap D S).1 j₀ ≤ F.coordMax hne j₀ :=
            Finset.le_max' _ _ (Finset.mem_image_of_mem (fun y => y.1 j₀) hxv)
          omega
      have h3 : (cellVertexMap D S).1 j₀ = D.base j₀ + chi S.1 j₀ := rfl
      omega
    have hDne : D.subsets.Nonempty := by rw [← Finset.card_pos, D.hsubsets.1]; omega
    obtain ⟨S₁, hS₁⟩ := hDne
    by_cases hp1 : j₀ ∈ S₁.1
    · have hmem : j₀ ∈ KSubsetCollection.commonPresent D.subsets := by
        rw [KSubsetCollection.mem_commonPresent_iff]
        intro S hS
        have e1 := hDsub S₁ hS₁; have e2 := hDsub S hS
        have c1 : chi S₁.1 j₀ = 1 := by simp [chi, hp1]
        by_contra hpS
        have c2 : chi S.1 j₀ = 0 := by simp [chi, hpS]
        rw [c1] at e1; rw [c2] at e2; omega
      rw [KSubsetCollection.commonPresent_eq_empty_of_isMaximalSorted (n := d) (by omega)
        D.hsubsets] at hmem
      exact absurd hmem (Finset.notMem_empty _)
    · have hmem : j₀ ∈ KSubsetCollection.commonAbsent D.subsets := by
        rw [KSubsetCollection.mem_commonAbsent_iff]
        intro S hS hpS
        have e1 := hDsub S₁ hS₁; have e2 := hDsub S hS
        have c1 : chi S₁.1 j₀ = 0 := by simp [chi, hp1]
        have c2 : chi S.1 j₀ = 1 := by simp [chi, hpS]
        rw [c1] at e1; rw [c2] at e2; omega
      rw [KSubsetCollection.commonAbsent_eq_empty_of_isMaximalSorted (n := d) (by omega)
        D.hsubsets] at hmem
      exact absurd hmem (Finset.notMem_empty _)
  · exact hhigh

theorem KuhnGeometricGridFacet.sameMinFrameCompletions_card_le_one_of_constantCoord
    {d N : ℕ} (hd : 2 ≤ d) (hgap : KSubsetCollection.LowerGapFillHypothesis)
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    {j₀ : Fin (d + 1)} (hj0const : F.coordMin hne j₀ = F.coordMax hne j₀) :
    (F.sameMinFrameCompletions hne).card ≤ 1 := by
  classical
  set wall := F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw) with hwall
  have hwallnj0 : ∀ S ∈ wall, j₀ ∉ S.1 := by
    intro S hS
    rw [hwall, mem_slift] at hS
    obtain ⟨w, hwF, hwS⟩ := hS
    rw [← hwS, F.mem_supportOverMin]
    have h1 : F.coordMin hne j₀ ≤ w.1 j₀ :=
      Finset.min'_le _ _ (Finset.mem_image_of_mem (fun y => y.1 j₀) hwF)
    have h2 : w.1 j₀ ≤ F.coordMax hne j₀ :=
      Finset.le_max' _ _ (Finset.mem_image_of_mem (fun y => y.1 j₀) hwF)
    omega
  have hinj : Set.InjOn (F.supportOverMin hne) (↑(F.sameMinFrameCompletions hne)) :=
    F.supportOverMin_injOn_sameMinFrameCompletions hne
  have hsub : (F.sameMinFrameCompletions hne).image (F.supportOverMin hne) ⊆
      ((KSubsetCollection.sameFrameExtensions wall).filter (fun T => j₀ ∈ T.1)).image
        Subtype.val := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [sameMinFrameCompletions, Finset.mem_filter] at hv
    rw [Finset.mem_image]
    refine ⟨⟨F.supportOverMin hne v, F.card_supportOverMin hne hv.2⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨F.support_mem_sameFrameExtensions hne hv.1 hv.2,
      F.sameMinFrame_mem_supportOverMin_of_constantCoord hd hne hj0const hv.1 hv.2⟩
  calc (F.sameMinFrameCompletions hne).card
      = ((F.sameMinFrameCompletions hne).image (F.supportOverMin hne)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (((KSubsetCollection.sameFrameExtensions wall).filter (fun T => j₀ ∈ T.1)).image
          Subtype.val).card := Finset.card_le_card hsub
    _ ≤ ((KSubsetCollection.sameFrameExtensions wall).filter (fun T => j₀ ∈ T.1)).card :=
        Finset.card_image_le
    _ ≤ 1 := KSubsetCollection.upperGapFill_extensions_card_le_one hgap hwallnj0

/-! ### conditional completion bound (the local flip) -/

theorem KuhnGeometricGridFacet.completingOppositeVertices_card_le_two_of_gapFill
    {d N : ℕ} (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N)
    (hgap : KSubsetCollection.LowerGapFillHypothesis) :
    F.completingOppositeVertices.card ≤ 2 := by
  classical
  have hne : F.vertices.Nonempty := by rw [← Finset.card_pos, F.vertices_card]; omega
  have hsub : F.completingOppositeVertices ⊆
      F.sameMinFrameCompletions hne ∪ F.lowerCompletions hne :=
    F.completions_subset_same_union_lower hne
  have hlower : (F.lowerCompletions hne).card ≤ 1 := F.lowerCompletions_card_le_one hd hne hgap
  by_cases hzero : (F.constantCoords hne).card = 0
  · have hlemp := F.lowerCompletions_eq_empty_of_no_constantCoords hne hzero
    calc F.completingOppositeVertices.card
        ≤ (F.sameMinFrameCompletions hne ∪ F.lowerCompletions hne).card := Finset.card_le_card hsub
      _ = (F.sameMinFrameCompletions hne).card := by rw [hlemp, Finset.union_empty]
      _ ≤ 2 := F.sameMinFrameCompletions_card_le_two hne
  · obtain ⟨j₀, hj₀⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)
    have hj0const : F.coordMin hne j₀ = F.coordMax hne j₀ := (F.mem_constantCoords_iff hne j₀).mp hj₀
    have hsame : (F.sameMinFrameCompletions hne).card ≤ 1 :=
      F.sameMinFrameCompletions_card_le_one_of_constantCoord hd hgap hne hj0const
    calc F.completingOppositeVertices.card
        ≤ (F.sameMinFrameCompletions hne ∪ F.lowerCompletions hne).card := Finset.card_le_card hsub
      _ ≤ (F.sameMinFrameCompletions hne).card + (F.lowerCompletions hne).card :=
        Finset.card_union_le _ _
      _ ≤ 2 := by omega

/-! ### conditional incidence -/

theorem KuhnGeometricGridFacet.incidentCells_card_le_two_of_gapFill {d N : ℕ} (hd : 2 ≤ d)
    (F : KuhnGeometricGridFacet d N) (hgap : KSubsetCollection.LowerGapFillHypothesis) :
    F.incidentCells.card ≤ 2 := by
  rw [F.incidentCells_card_eq_completions_card]
  exact F.completingOppositeVertices_card_le_two_of_gapFill hd hgap

theorem KuhnGeometricGridFacet.incidentCells_card_eq_one_or_two_of_gapFill {d N : ℕ}
    (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N)
    (hgap : KSubsetCollection.LowerGapFillHypothesis) :
    F.incidentCells.card = 1 ∨ F.incidentCells.card = 2 := by
  have hpos : 0 < F.incidentCells.card := Finset.card_pos.mpr F.incidentCells_nonempty
  have hle := F.incidentCells_card_le_two_of_gapFill hd hgap
  omega

/-! ### DISCHARGE: the gap-fill hypothesis is now a theorem ⟹ UNCONDITIONAL incidence

`KSubsetCollection.lowerGapFill_extensions_card_le_one` (proved above via the separation
theorem) is exactly the content of `LowerGapFillHypothesis`, so the hypothesis holds and every
`_of_gapFill` incidence consequence becomes unconditional. -/

/-- The packaged combinatorial residual is a THEOREM (no hypotheses). -/
theorem KSubsetCollection.lowerGapFillHypothesis_holds :
    KSubsetCollection.LowerGapFillHypothesis :=
  fun hW => KSubsetCollection.lowerGapFill_extensions_card_le_one hW

/-- THE LOCAL FLIP (unconditional): a Kuhn facet has `≤ 2` completing opposite
vertices. -/
theorem KuhnGeometricGridFacet.completingOppositeVertices_card_le_two {d N : ℕ}
    (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N) :
    F.completingOppositeVertices.card ≤ 2 :=
  F.completingOppositeVertices_card_le_two_of_gapFill hd
    KSubsetCollection.lowerGapFillHypothesis_holds

/-- Incidence `≤ 2` (unconditional): at most two cells meet along a facet. -/
theorem KuhnGeometricGridFacet.incidentCells_card_le_two {d N : ℕ} (hd : 2 ≤ d)
    (F : KuhnGeometricGridFacet d N) : F.incidentCells.card ≤ 2 :=
  F.incidentCells_card_le_two_of_gapFill hd KSubsetCollection.lowerGapFillHypothesis_holds

/-- Incidence `= 1 ∨ = 2` (unconditional): the Sperner door property — every facet is
shared by exactly one or two cells. -/
theorem KuhnGeometricGridFacet.incidentCells_card_eq_one_or_two {d N : ℕ} (hd : 2 ≤ d)
    (F : KuhnGeometricGridFacet d N) :
    F.incidentCells.card = 1 ∨ F.incidentCells.card = 2 :=
  F.incidentCells_card_eq_one_or_two_of_gapFill hd KSubsetCollection.lowerGapFillHypothesis_holds

end BarycentricFreudenthal
end SpernerFreudenthal
end EcoLean
