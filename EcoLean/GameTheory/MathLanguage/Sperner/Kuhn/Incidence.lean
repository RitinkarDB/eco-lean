import EcoLean.GameTheory.MathLanguage.Sperner.Kuhn.Cells

/-! Local pseudomanifold incidence for the Freudenthal triangulation: boundary facets have degree one
and interior facets degree two (`incidentCells_card_eq_two_iff_not_boundary`), via the door property
and the `c = 0` / `c = 1` non-boundary degree-two converses. -/

namespace EcoLean
namespace SpernerFreudenthal
namespace BarycentricFreudenthal
open Finset
/-! ### Boundary classification (the easy half): a boundary facet has exactly one incident cell

A facet of `N • Δ^d` lies on the geometric boundary iff all its vertices share a coordinate
equal to `0` (they lie in a coordinate face `{x_i = 0}`).  Such a facet has NO "downward" flip
across it (the missing cell would need a negative coordinate), so it is incident to exactly one
cell.  This is the boundary ⟹ degree-one direction; the converse (interior ⟹ degree two) is a
separate pass. -/

/-- Each wall vertex coordinate is `≤` the coordinatewise maximum. -/
theorem KuhnGeometricGridFacet.coord_le_coordMax {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    {x : SimplexGrid d N} (hx : x ∈ F.vertices) (i : Fin (d + 1)) :
    x.1 i ≤ F.coordMax hne i :=
  Finset.le_max' _ _ (Finset.mem_image_of_mem (fun y => y.1 i) hx)

/-- The geometric boundary predicate: all vertices share a zero coordinate. -/
def KuhnGeometricGridFacet.IsBoundary {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) : Prop :=
  ∃ i : Fin (d + 1), ∀ x ∈ F.vertices, x.1 i = 0

/-- If all vertices are `0` at coordinate `i`, the coordinatewise maximum there is `0`. -/
theorem KuhnGeometricGridFacet.boundary_coord_coordMax_zero {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) {i : Fin (d + 1)}
    (hi : ∀ x ∈ F.vertices, x.1 i = 0) : F.coordMax hne i = 0 := by
  classical
  refine Nat.le_antisymm ?_ (Nat.zero_le _)
  apply Finset.max'_le
  intro y hy
  obtain ⟨x, hxF, rfl⟩ := Finset.mem_image.mp hy
  exact Nat.le_of_eq (hi x hxF)

/-- If all vertices are `0` at coordinate `i`, the coordinatewise minimum there is `0`. -/
theorem KuhnGeometricGridFacet.boundary_coord_coordMin_zero {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) {i : Fin (d + 1)}
    (hi : ∀ x ∈ F.vertices, x.1 i = 0) : F.coordMin hne i = 0 := by
  have hmax := F.boundary_coord_coordMax_zero hne hi
  have hle : F.coordMin hne i ≤ F.coordMax hne i := Finset.min'_le_max' _ _
  omega

theorem KuhnGeometricGridFacet.isBoundary_iff_coordMax_zero {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) :
    F.IsBoundary ↔ ∃ i : Fin (d + 1), F.coordMax hne i = 0 := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, F.boundary_coord_coordMax_zero hne hi⟩
  · rintro ⟨i, hci⟩
    refine ⟨i, fun x hx => ?_⟩
    have hle := F.coord_le_coordMax hne hx i
    omega

theorem KuhnGeometricGridFacet.isBoundary_iff_coordMin_coordMax_zero {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) :
    F.IsBoundary ↔ ∃ i : Fin (d + 1), F.coordMin hne i = 0 ∧ F.coordMax hne i = 0 := by
  rw [F.isBoundary_iff_coordMax_zero hne]
  constructor
  · rintro ⟨i, hmax⟩
    refine ⟨i, ?_, hmax⟩
    have hle : F.coordMin hne i ≤ F.coordMax hne i := Finset.min'_le_max' _ _
    omega
  · rintro ⟨i, _, hmax⟩
    exact ⟨i, hmax⟩

/-- A boundary coordinate is a constant coordinate (`coordMin = coordMax = 0`). -/
theorem KuhnGeometricGridFacet.boundary_coord_mem_constantCoords {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) {i : Fin (d + 1)}
    (hi : ∀ x ∈ F.vertices, x.1 i = 0) : i ∈ F.constantCoords hne := by
  rw [F.mem_constantCoords_iff]
  rw [F.boundary_coord_coordMin_zero hne hi, F.boundary_coord_coordMax_zero hne hi]

/-- A boundary facet has no lower completions: a downward dip at the boundary
coordinate would need `v.1 i + 1 = coordMin i = 0`, impossible.  (`2 ≤ d` to invoke
`constant_coord_unique`.) -/
theorem KuhnGeometricGridFacet.lowerCompletions_eq_empty_of_boundary {d N : ℕ}
    (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    (hbd : F.IsBoundary) : F.lowerCompletions hne = ∅ := by
  classical
  rcases hbd with ⟨i, hi⟩
  have hmin_i : F.coordMin hne i = 0 := F.boundary_coord_coordMin_zero hne hi
  have hiconst : F.coordMin hne i = F.coordMax hne i := by
    rw [hmin_i, F.boundary_coord_coordMax_zero hne hi]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro v hv
  obtain ⟨hvcomp, j, hj⟩ := (F.mem_lowerCompletions hne v).mp hv
  have hjconst : F.coordMin hne j = F.coordMax hne j :=
    F.completion_lower_coord_imp_constant hvcomp hne hj
  have hji : j = i := F.constant_coord_unique hd hne hjconst hiconst
  rw [hji] at hj
  omega

/-- A boundary facet has `≤ 1` same-min-frame completions (one constant coordinate,
then reuse `sameMinFrameCompletions_card_le_one_of_constantCoord`; the gap-fill hypothesis is
discharged by `lowerGapFillHypothesis_holds`). -/
theorem KuhnGeometricGridFacet.sameMinFrameCompletions_card_le_one_of_boundary {d N : ℕ}
    (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    (hbd : F.IsBoundary) : (F.sameMinFrameCompletions hne).card ≤ 1 := by
  rcases hbd with ⟨i, hi⟩
  have hiconst : F.coordMin hne i = F.coordMax hne i := by
    rw [F.boundary_coord_coordMin_zero hne hi, F.boundary_coord_coordMax_zero hne hi]
  exact F.sameMinFrameCompletions_card_le_one_of_constantCoord hd
    KSubsetCollection.lowerGapFillHypothesis_holds hne hiconst

/-- A boundary facet has `≤ 1` completing opposite vertices: every completion is
same-min-frame (`lower = ∅`), and there is `≤ 1` of those. -/
theorem KuhnGeometricGridFacet.completingOppositeVertices_card_le_one_of_boundary {d N : ℕ}
    (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N) (hbd : F.IsBoundary) :
    F.completingOppositeVertices.card ≤ 1 := by
  classical
  have hne : F.vertices.Nonempty := by rw [← Finset.card_pos, F.vertices_card]; omega
  have hsub := F.completions_subset_same_union_lower hne
  have hlow : F.lowerCompletions hne = ∅ := F.lowerCompletions_eq_empty_of_boundary hd hne hbd
  have hsame : (F.sameMinFrameCompletions hne).card ≤ 1 :=
    F.sameMinFrameCompletions_card_le_one_of_boundary hd hne hbd
  calc F.completingOppositeVertices.card
      ≤ (F.sameMinFrameCompletions hne ∪ F.lowerCompletions hne).card := Finset.card_le_card hsub
    _ = (F.sameMinFrameCompletions hne).card := by rw [hlow, Finset.union_empty]
    _ ≤ 1 := hsame

/-- **— THE BOUNDARY CLASSIFICATION (easy half):** a boundary facet has exactly one
incident cell. -/
theorem KuhnGeometricGridFacet.incidentCells_card_eq_one_of_boundary {d N : ℕ}
    (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N) (hbd : F.IsBoundary) :
    F.incidentCells.card = 1 := by
  classical
  have hpos : 0 < F.incidentCells.card := Finset.card_pos.mpr F.incidentCells_nonempty
  have hle : F.incidentCells.card ≤ 1 := by
    rw [F.incidentCells_card_eq_completions_card]
    exact F.completingOppositeVertices_card_le_one_of_boundary hd hbd
  omega

/-- **Contrapositive.** A facet with two incident cells is not a boundary facet. -/
theorem KuhnGeometricGridFacet.not_boundary_of_incidentCells_card_eq_two {d N : ℕ}
    (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N) (hcard : F.incidentCells.card = 2) :
    ¬ F.IsBoundary := by
  intro hbd
  have h1 := F.incidentCells_card_eq_one_of_boundary hd hbd
  omega

/-! ### Converse classification — case `c = 1`, not boundary (structural setup)

The remaining converse: a facet with exactly ONE constant coordinate that is NOT a boundary
coordinate (its constant value is positive) is incident to two cells.  Below are the structural
facts (the constant-coordinate splitter, extraction, and positivity); the geometric existence of
the two completions is documented after the `c = 0` converse. -/

/-- The constant-coordinate count is `0` or `1` (`constantCoords_card_le_one`). -/
theorem KuhnGeometricGridFacet.constantCoords_card_eq_zero_or_one {d N : ℕ}
    (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) :
    (F.constantCoords hne).card = 0 ∨ (F.constantCoords hne).card = 1 := by
  have hle := F.constantCoords_card_le_one hd hne
  omega

/-- In the `c = 1` case, the unique constant coordinate. -/
theorem KuhnGeometricGridFacet.exists_unique_constantCoord_of_card_eq_one {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    (hone : (F.constantCoords hne).card = 1) :
    ∃ c : Fin (d + 1), c ∈ F.constantCoords hne ∧ ∀ i, i ∈ F.constantCoords hne → i = c := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hone
  exact ⟨c, by rw [hc]; exact Finset.mem_singleton_self c,
    fun i hi => by rw [hc, Finset.mem_singleton] at hi; exact hi⟩

/-- NOT-boundary ⟹ the constant coordinate is POSITIVE.  If `coordMin c = 0`, then (`c` constant)
`coordMax c = 0` too, so all vertices are `0` at `c`, witnessing `IsBoundary`. -/
theorem KuhnGeometricGridFacet.constantCoord_pos_of_not_boundary {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    (hnb : ¬ F.IsBoundary) {c : Fin (d + 1)} (hc : c ∈ F.constantCoords hne) :
    0 < F.coordMin hne c := by
  rw [F.mem_constantCoords_iff] at hc
  by_contra h
  push_neg at h
  have hmin0 : F.coordMin hne c = 0 := by omega
  have hmax0 : F.coordMax hne c = 0 := by rw [← hc]; exact hmin0
  exact hnb ((F.isBoundary_iff_coordMin_coordMax_zero hne).mpr ⟨c, hmin0, hmax0⟩)

/-
The last local incidence theorem: `c = 1`, not boundary ⟹ degree two.  The completions split
disjointly, `completingOppositeVertices = sameMinFrameCompletions ⊔ lowerCompletions`, and in the
`c = 1` case each side has at most one element (`sameMinFrameCompletions_card_le_one_of_constantCoord`,
`lowerCompletions_card_le_one`), so degree two is exactly "both sides nonempty".

Up side (`sameMinFrameCompletions`): always nonempty, and purely combinatorial — it does not use
`¬boundary`.  Geometrically only the common-absent case arises (`commonPresent (slift F) = ∅`), so the
relevant fact is that a codim-1 sorted wall with one common-absent frozen coordinate has a same-frame
extension (`sameFrameExtensions_nonempty_of_commonAbsent_oneFrozen`).  That is proved by a missing-rank
dispatch — `exists_rank_zero_member` makes rank `0` always present, so the missing rank `m ∈ {1,…,n}` —
over four cases (interior non-adjacent gap, interior adjacent gap, and the two endpoint cases), reusing
`descentSwap_isExtension` / `gap_coord_descent_of_interior` and the endpoint above- and below-exterior
constructions.

Down side (`lowerCompletions`): nonempty iff the down-cell exists, which uses `¬boundary` via
`constantCoord_pos_of_not_boundary` (the constant value `p ≥ 1`, so the dip `v_c = p-1 ≥ 0` is a valid
grid point).  This is the cross-stratum flip: the down-cell has `k = k'+1`, base `coordMin - e_{c'}`,
and support a `lowerGapFillExtensions` element, lifted to a geometric completion (mirror of
`exists_completion_of_extension` for the lowered frame).

Assembly: both sides `= 1` (disjoint, `≤ 1`, nonempty) ⟹ `incidentCells = 2`; combined with the
`c = 0` case (`constantCoords_card_eq_zero_or_one`) this gives the full `¬boundary ⟹ degree two`.
-/

/-! ### Converse classification — case `c = 0` (no constant coordinate ⟹ degree two)

The cleaner converse half.  In the `coordMin` frame, "no constant coordinate" is exactly
"the support wall `slift F.vertices` has no frozen coordinate": `commonPresent = ∅` always
(the `coordMin`-achieving vertex sits AT `coordMin`, not above it) and `commonAbsent =
constantCoords` (a coordinate is below every support iff it is constant `coordMin = coordMax`).
So the geometric two-sidedness reduces to the pure combinatorial fixed-slice EXISTENCE: a
codimension-one sorted wall with no frozen coordinate has TWO same-frame extensions. -/

/-- A facet has `d ≥ 2 > 0` vertices, hence a nonempty vertex set. -/
theorem KuhnGeometricGridFacet.vertices_nonempty_of_two_le {d N : ℕ} (hd : 2 ≤ d)
    (F : KuhnGeometricGridFacet d N) : F.vertices.Nonempty := by
  rw [← Finset.card_pos, F.vertices_card]; omega

/-- With no constant coordinate every completion is same-min-frame
(`lowerCompletions = ∅`), so the completion set equals the same-min-frame set. -/
theorem KuhnGeometricGridFacet.completingOppositeVertices_eq_sameMinFrame_of_no_constantCoords
    {d N : ℕ} (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    (hzero : (F.constantCoords hne).card = 0) :
    F.completingOppositeVertices = F.sameMinFrameCompletions hne := by
  classical
  apply Finset.Subset.antisymm
  · intro v hv
    have hsub := F.completions_subset_same_union_lower hne hv
    rw [Finset.mem_union] at hsub
    rcases hsub with h | h
    · exact h
    · rw [F.lowerCompletions_eq_empty_of_no_constantCoords hne hzero] at h
      exact absurd h (Finset.notMem_empty v)
  · intro v hv
    rw [sameMinFrameCompletions, Finset.mem_filter] at hv
    exact hv.1

/-- In the `coordMin` frame the support wall has NO common-present coordinate: the
`coordMin`-achieving vertex sits at `coordMin` there, never `coordMin + 1`. -/
theorem KuhnGeometricGridFacet.commonPresent_slift_eq_empty {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) :
    KSubsetCollection.commonPresent
      (F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw)) = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i hi
  rw [KSubsetCollection.mem_commonPresent_iff] at hi
  obtain ⟨wmin, hwminF, hwmin⟩ :=
    Finset.mem_image.mp (Finset.min'_mem (F.vertices.image fun x => x.1 i) (hne.image _))
  have hmin_eq : wmin.1 i = F.coordMin hne i := hwmin
  have hSmem : (⟨F.supportOverMin hne wmin,
      F.card_supportOverMin hne (F.vertex_isSameMinFrame hne hwminF)⟩ :
        KSubset (d + 1) (N - ∑ j, F.coordMin hne j)) ∈
      F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw) :=
    (F.mem_slift hne).mpr ⟨wmin, hwminF, rfl⟩
  have hmem := hi _ hSmem
  rw [show (⟨F.supportOverMin hne wmin, F.card_supportOverMin hne
    (F.vertex_isSameMinFrame hne hwminF)⟩ : KSubset (d + 1)
      (N - ∑ j, F.coordMin hne j)).1 = F.supportOverMin hne wmin from rfl,
    F.mem_supportOverMin] at hmem
  omega

/-- In the `coordMin` frame the support wall's common-ABSENT coordinates are exactly the
constant coordinates of `F` (`coordMin = coordMax`). -/
theorem KuhnGeometricGridFacet.commonAbsent_slift_eq_constantCoords {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) :
    KSubsetCollection.commonAbsent
      (F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw))
      = F.constantCoords hne := by
  classical
  ext i
  rw [KSubsetCollection.mem_commonAbsent_iff, F.mem_constantCoords_iff]
  constructor
  · intro hi
    obtain ⟨wmax, hwmaxF, hwmax⟩ :=
      Finset.mem_image.mp (Finset.max'_mem (F.vertices.image fun x => x.1 i) (hne.image _))
    have hmax_eq : F.coordMax hne i = wmax.1 i := hwmax.symm
    have hSmem : (⟨F.supportOverMin hne wmax,
        F.card_supportOverMin hne (F.vertex_isSameMinFrame hne hwmaxF)⟩ :
          KSubset (d + 1) (N - ∑ j, F.coordMin hne j)) ∈
        F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw) :=
      (F.mem_slift hne).mpr ⟨wmax, hwmaxF, rfl⟩
    have hnot := hi _ hSmem
    rw [show (⟨F.supportOverMin hne wmax, F.card_supportOverMin hne
      (F.vertex_isSameMinFrame hne hwmaxF)⟩ : KSubset (d + 1)
        (N - ∑ j, F.coordMin hne j)).1 = F.supportOverMin hne wmax from rfl,
      F.mem_supportOverMin] at hnot
    rcases F.vertex_isSameMinFrame hne hwmaxF i with h | h
    · omega
    · exact absurd h hnot
  · intro hconst S hS
    rw [F.mem_slift] at hS
    obtain ⟨w, hwF, hweq⟩ := hS
    rw [← hweq, F.mem_supportOverMin]
    have h2 := F.coord_le_coordMax hne hwF i
    omega

/-- The support wall's frozen coordinates are exactly the constant coordinates of `F`. -/
theorem KuhnGeometricGridFacet.frozenCoords_slift_eq_constantCoords {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) :
    KSubsetCollection.frozenCoords
      (F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw))
      = F.constantCoords hne := by
  rw [KSubsetCollection.frozenCoords, F.commonPresent_slift_eq_empty hne,
    F.commonAbsent_slift_eq_constantCoords hne, Finset.empty_union]

/-! ### Geometric transport: each combinatorial extension realises a completion

This is the surjective side of the `supportOverMin` correspondence (the injective side —
`supportOverMin_injOn_sameMinFrameCompletions` — already gives the upper bound).  It lifts a
combinatorial same-frame extension `T` of the support wall back to an actual lattice
completion `coordMin + χ(T)`, by building the cell `(coordMin, k', insert T wall)`.  Together
with the injection this makes `supportOverMin` a BIJECTION, so the same-min-frame completion
count EQUALS the combinatorial same-frame extension count. -/

/-- A wall vertex coordinate is `≥` the coordinatewise minimum. -/
theorem KuhnGeometricGridFacet.coordMin_le_coord {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    {x : SimplexGrid d N} (hx : x ∈ F.vertices) (i : Fin (d + 1)) :
    F.coordMin hne i ≤ x.1 i :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem (fun y => y.1 i) hx)

/-- The coordinatewise minima sum to at most `N` (bounded by any single vertex's sum). -/
theorem KuhnGeometricGridFacet.sum_coordMin_le {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) :
    (∑ i, F.coordMin hne i) ≤ N := by
  obtain ⟨w, hw⟩ := id hne
  calc (∑ i, F.coordMin hne i)
      ≤ ∑ i, w.1 i := Finset.sum_le_sum (fun i _ => F.coordMin_le_coord hne hw i)
    _ = N := w.2

/-- Roundtrip: in the `coordMin` frame, a same-min-frame point is recovered from its support
(`coordMin + χ(supportOverMin w) = w`). -/
theorem KuhnGeometricGridFacet.vertexFromSubset_supportOverMin {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    {w : SimplexGrid d N} (hw : F.IsSameMinFrameCompletion hne w) :
    vertexFromSubset (F.coordMin hne) (F.supportOverMin hne w) = w.1 := by
  funext i
  simp only [vertexFromSubset, chi]
  by_cases hi : i ∈ F.supportOverMin hne w
  · rw [if_pos hi]; rw [F.mem_supportOverMin] at hi; omega
  · rw [if_neg hi]
    rw [F.mem_supportOverMin] at hi
    rcases hw i with h | h
    · omega
    · exact absurd h hi

/-- SURJECTIVITY: a combinatorial same-frame extension `T` of the support wall is realised by
the lattice completion `coordMin + χ(T)`.  The cell `(coordMin, k', insert T wall)` witnesses
`IsKuhnGridSmallSimplex (insert v F.vertices)`. -/
theorem KuhnGeometricGridFacet.exists_completion_of_extension {d N : ℕ} (hd : 2 ≤ d)
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    {T : KSubset (d + 1) (N - ∑ i, F.coordMin hne i)}
    (hT : T ∈ KSubsetCollection.sameFrameExtensions
      (F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw))) :
    ∃ v, v ∈ F.sameMinFrameCompletions hne ∧ F.supportOverMin hne v = T.1 := by
  classical
  set wall := F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw) with hwall
  rw [KSubsetCollection.mem_sameFrameExtensions_iff] at hT
  obtain ⟨hTnotin, hTmax⟩ := hT
  have hsum_le : (∑ i, F.coordMin hne i) ≤ N := F.sum_coordMin_le hne
  have hsum_add : (∑ i, F.coordMin hne i) + (N - ∑ i, F.coordMin hne i) = N := by omega
  have hcardC : (insert T wall).card = d + 1 := hTmax.1
  have hkpos : 0 < N - ∑ i, F.coordMin hne i := by
    by_contra h
    have hk0 : N - ∑ i, F.coordMin hne i = 0 := by omega
    have hle1 : (insert T wall).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a _ b _
      have hae : a.1 = ∅ := Finset.card_eq_zero.mp (a.2.trans hk0)
      have hbe : b.1 = ∅ := Finset.card_eq_zero.mp (b.2.trans hk0)
      exact Subtype.ext (hae.trans hbe.symm)
    omega
  have hkle : N - ∑ i, F.coordMin hne i ≤ d + 1 := by
    have h2 : T.1.card ≤ d + 1 := by
      calc T.1.card ≤ (Finset.univ : Finset (Fin (d + 1))).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = d + 1 := by rw [Finset.card_univ, Fintype.card_fin]
    rw [T.2] at h2; exact h2
  have hklt : N - ∑ i, F.coordMin hne i < d + 1 := by
    rcases lt_or_eq_of_le hkle with h | h
    · exact h
    · exfalso
      have hle1 : (insert T wall).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a _ b _
        refine Subtype.ext ?_
        have ha : a.1 = Finset.univ :=
          Finset.eq_univ_of_card _ (by rw [a.2, Fintype.card_fin]; exact h)
        have hb : b.1 = Finset.univ :=
          Finset.eq_univ_of_card _ (by rw [b.2, Fintype.card_fin]; exact h)
        rw [ha, hb]
      omega
  let D' : KuhnGridCellData d N :=
    { base := F.coordMin hne
      k := N - ∑ i, F.coordMin hne i
      hk_pos := hkpos
      hk_lt := hklt
      subsets := insert T wall
      hsubsets := hTmax
      sum_base_add_k := hsum_add }
  set v : SimplexGrid d N := ⟨vertexFromSubset (F.coordMin hne) T.1,
    vertexFromSubset_sum_eq (F.coordMin hne) T.1 T.2 hsum_add⟩ with hv
  have hv_coord : ∀ i, v.1 i = F.coordMin hne i + (if i ∈ T.1 then 1 else 0) := by
    intro i
    simp only [hv, vertexFromSubset, chi]
  have hsupp : F.supportOverMin hne v = T.1 := by
    ext i
    rw [F.mem_supportOverMin, hv_coord i]
    constructor
    · intro h
      by_contra hni
      rw [if_neg hni] at h
      omega
    · intro h
      rw [if_pos h]
  have hsmf : F.IsSameMinFrameCompletion hne v := by
    intro i
    rw [hv_coord i]
    by_cases hi : i ∈ T.1
    · right; rw [if_pos hi]
    · left; rw [if_neg hi, Nat.add_zero]
  have hcvT : cellVertexMap D' T = v := rfl
  have hwallimg : wall.image (cellVertexMap D') = F.vertices := by
    ext x
    rw [Finset.mem_image]
    constructor
    · rintro ⟨S, hS, rfl⟩
      rw [hwall, F.mem_slift] at hS
      obtain ⟨w, hwF, hweq⟩ := hS
      have hcv : cellVertexMap D' S = w := by
        refine Subtype.ext ?_
        show vertexFromSubset (F.coordMin hne) S.1 = w.1
        rw [← hweq, F.vertexFromSubset_supportOverMin hne (F.vertex_isSameMinFrame hne hwF)]
      rw [hcv]; exact hwF
    · intro hx
      refine ⟨⟨F.supportOverMin hne x,
        F.card_supportOverMin hne (F.vertex_isSameMinFrame hne hx)⟩, ?_, ?_⟩
      · rw [hwall]; exact (F.mem_slift hne).mpr ⟨x, hx, rfl⟩
      · refine Subtype.ext ?_
        show vertexFromSubset (F.coordMin hne) (F.supportOverMin hne x) = x.1
        exact F.vertexFromSubset_supportOverMin hne (F.vertex_isSameMinFrame hne hx)
  have hDvert : D'.vertices = insert v F.vertices := by
    rw [cellVertexMap_vertices]
    show (insert T wall).image (cellVertexMap D') = insert v F.vertices
    rw [Finset.image_insert, hcvT, hwallimg]
  have hvnotin : v ∉ F.vertices := by
    intro hvF
    apply hTnotin
    rw [hwall]
    exact (F.mem_slift hne).mpr ⟨v, hvF, hsupp⟩
  refine ⟨v, ?_, hsupp⟩
  rw [sameMinFrameCompletions, Finset.mem_filter]
  refine ⟨?_, hsmf⟩
  rw [F.mem_completingOppositeVertices_iff]
  exact ⟨hvnotin, ⟨D', hDvert⟩⟩

/-- The lowered-frame sum is `≤ N` (each `lowerFrame i ≤ coordMin i`). -/
theorem KuhnGeometricGridFacet.sum_lowerFrame_le {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) (j₀ : Fin (d + 1)) :
    (∑ i, F.lowerFrame hne j₀ i) ≤ N := by
  calc (∑ i, F.lowerFrame hne j₀ i) ≤ ∑ i, F.coordMin hne i := by
        apply Finset.sum_le_sum
        intro i _
        rw [lowerFrame_apply]; split <;> omega
    _ ≤ N := F.sum_coordMin_le hne

/-- Roundtrip in the lowered frame: a lower-frame-band point is recovered from its lower support
(`lowerFrame + χ(lowerSupport w) = w`). -/
theorem KuhnGeometricGridFacet.vertexFromSubset_lowerSupport {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) (j₀ : Fin (d + 1))
    {w : SimplexGrid d N} (hw : F.IsLowerFrameBand hne j₀ w) :
    vertexFromSubset (F.lowerFrame hne j₀) (F.lowerSupport hne j₀ w) = w.1 := by
  funext i
  simp only [vertexFromSubset, chi]
  by_cases hi : i ∈ F.lowerSupport hne j₀ w
  · rw [if_pos hi]; rw [F.mem_lowerSupport] at hi; rcases hw i with h | h <;> omega
  · rw [if_neg hi]; rw [F.mem_lowerSupport] at hi; rcases hw i with h | h <;> omega

/-- **DOWN-side geometric lift.**  A `lowerGapFillExtension` `T` of the lower support wall
is realised by the geometric LOWER completion `lowerFrame + χ(T)` (which dips at the constant
coordinate `c`, since `c ∉ T`).  The cell `(lowerFrame, k', insert T wall)` witnesses
`IsKuhnGridSmallSimplex (insert v F.vertices)`.  Mirror of `exists_completion_of_extension`
over the lowered frame. -/
theorem KuhnGeometricGridFacet.exists_lowerCompletion_of_lowerGapFillExtension {d N : ℕ}
    (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    {c : Fin (d + 1)} (hcpos : 1 ≤ F.coordMin hne c)
    (hbandF : ∀ w ∈ F.vertices, F.IsLowerFrameBand hne c w)
    {T : KSubset (d + 1) (N - ∑ i, F.lowerFrame hne c i)}
    (hT : T ∈ KSubsetCollection.lowerGapFillExtensions
        (F.lowerSlift hne c F.vertices hbandF) c) :
    (F.lowerCompletions hne).Nonempty := by
  classical
  set wall := F.lowerSlift hne c F.vertices hbandF with hwall
  rw [KSubsetCollection.mem_lowerGapFillExtensions_iff] at hT
  obtain ⟨hTsfe, hcnT⟩ := hT
  have hTnotin : T ∉ wall := ((KSubsetCollection.mem_sameFrameExtensions_iff wall T).mp hTsfe).1
  have hIMS : KSubsetCollection.IsMaximalSorted (insert T wall) :=
    ((KSubsetCollection.mem_sameFrameExtensions_iff wall T).mp hTsfe).2
  have hsum_le : (∑ i, F.lowerFrame hne c i) ≤ N := F.sum_lowerFrame_le hne c
  have hsum_add : (∑ i, F.lowerFrame hne c i) + (N - ∑ i, F.lowerFrame hne c i) = N := by omega
  have hkpos : 0 < N - ∑ i, F.lowerFrame hne c i := by
    by_contra h
    have hk0 : N - ∑ i, F.lowerFrame hne c i = 0 := by omega
    have hle1 : (insert T wall).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a _ b _
      have hae : a.1 = ∅ := Finset.card_eq_zero.mp (a.2.trans hk0)
      have hbe : b.1 = ∅ := Finset.card_eq_zero.mp (b.2.trans hk0)
      exact Subtype.ext (hae.trans hbe.symm)
    rw [hIMS.1] at hle1; omega
  have hkle : N - ∑ i, F.lowerFrame hne c i ≤ d + 1 := by
    have h2 : T.1.card ≤ d + 1 := by
      calc T.1.card ≤ (Finset.univ : Finset (Fin (d + 1))).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = d + 1 := by rw [Finset.card_univ, Fintype.card_fin]
    rw [T.2] at h2; exact h2
  have hklt : N - ∑ i, F.lowerFrame hne c i < d + 1 := by
    rcases lt_or_eq_of_le hkle with h | h
    · exact h
    · exfalso
      have hle1 : (insert T wall).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a _ b _
        refine Subtype.ext ?_
        have ha : a.1 = Finset.univ :=
          Finset.eq_univ_of_card _ (by rw [a.2, Fintype.card_fin]; exact h)
        have hb : b.1 = Finset.univ :=
          Finset.eq_univ_of_card _ (by rw [b.2, Fintype.card_fin]; exact h)
        rw [ha, hb]
      rw [hIMS.1] at hle1; omega
  let D' : KuhnGridCellData d N :=
    { base := F.lowerFrame hne c
      k := N - ∑ i, F.lowerFrame hne c i
      hk_pos := hkpos
      hk_lt := hklt
      subsets := insert T wall
      hsubsets := hIMS
      sum_base_add_k := hsum_add }
  set v : SimplexGrid d N := ⟨vertexFromSubset (F.lowerFrame hne c) T.1,
    vertexFromSubset_sum_eq (F.lowerFrame hne c) T.1 T.2 hsum_add⟩ with hv
  have hv_coord : ∀ i, v.1 i = F.lowerFrame hne c i + (if i ∈ T.1 then 1 else 0) := by
    intro i; simp only [hv, vertexFromSubset, chi]
  have hvdip : v.1 c + 1 = F.coordMin hne c := by
    rw [hv_coord c, if_neg hcnT, lowerFrame_apply, if_pos rfl]; omega
  have hlsupp : F.lowerSupport hne c v = T.1 := by
    ext i
    rw [F.mem_lowerSupport, hv_coord i]
    constructor
    · intro h; by_contra hi; rw [if_neg hi] at h; omega
    · intro hi; rw [if_pos hi]; omega
  have hcvT : cellVertexMap D' T = v := rfl
  have hwallimg : wall.image (cellVertexMap D') = F.vertices := by
    ext x
    rw [Finset.mem_image]
    constructor
    · rintro ⟨S, hS, rfl⟩
      rw [hwall, F.mem_lowerSlift] at hS
      obtain ⟨w, hwF, hweq⟩ := hS
      have hcv : cellVertexMap D' S = w := by
        refine Subtype.ext ?_
        show vertexFromSubset (F.lowerFrame hne c) S.1 = w.1
        rw [← hweq, F.vertexFromSubset_lowerSupport hne c (hbandF w hwF)]
      rw [hcv]; exact hwF
    · intro hx
      refine ⟨⟨F.lowerSupport hne c x, F.card_lowerSupport hne c (hbandF x hx)⟩, ?_, ?_⟩
      · rw [hwall]; exact (F.mem_lowerSlift hne c).mpr ⟨x, hx, rfl⟩
      · refine Subtype.ext ?_
        show vertexFromSubset (F.lowerFrame hne c) (F.lowerSupport hne c x) = x.1
        exact F.vertexFromSubset_lowerSupport hne c (hbandF x hx)
  have hDvert : D'.vertices = insert v F.vertices := by
    rw [cellVertexMap_vertices]
    show (insert T wall).image (cellVertexMap D') = insert v F.vertices
    rw [Finset.image_insert, hcvT, hwallimg]
  have hvnotin : v ∉ F.vertices := by
    intro hvF
    apply hTnotin
    rw [hwall, F.mem_lowerSlift]
    exact ⟨v, hvF, hlsupp⟩
  refine ⟨v, ?_⟩
  rw [F.mem_lowerCompletions hne]
  refine ⟨?_, ⟨c, hvdip⟩⟩
  rw [F.mem_completingOppositeVertices_iff]
  exact ⟨hvnotin, ⟨D', hDvert⟩⟩

/-! ### Lower support wall facts (for the DOWN-side existence argument)

The lower support wall `lowerSlift F.vertices` is the up-frame support wall `slift F.vertices`
with the constant coordinate `c` inserted into every member (`lowerSupport w = insert c
(supportOverMin w)` for a facet vertex `w`, since dropping the frame by 1 at the constant `c` puts
`c` into the support).  So it inherits sortedness from `slift`, and its frozen coordinate is the
common-PRESENT `c` — the dual of the up-side. -/

/-- Prefix count of `insert c S` (with `c ∉ S`) exceeds that of `S` by `[c ≤ t]`. -/
theorem prefixCount_insert {n : ℕ} (S : Finset (Fin n)) {c : Fin n} (hc : c ∉ S) (t : Fin n) :
    ((insert c S).filter (· ≤ t)).card
      = (S.filter (· ≤ t)).card + (if c ≤ t then 1 else 0) := by
  classical
  rw [Finset.filter_insert]
  by_cases h : c ≤ t
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem
      (fun hmem => hc (Finset.mem_filter.mp hmem).1)]
  · rw [if_neg h, if_neg h, Nat.add_zero]

/-- Inserting a common coordinate `c` into both members preserves `IsSortedPair` (the `[c ≤ t]`
shift cancels), and transports across the level index. -/
theorem KSubset.isSortedPair_insert {n k k' : ℕ} {I J : KSubset n k} {Iup Jup : KSubset n k'}
    {c : Fin n} (hI : I.1 = insert c Iup.1) (hJ : J.1 = insert c Jup.1)
    (hcI : c ∉ Iup.1) (hcJ : c ∉ Jup.1) (h : KSubset.IsSortedPair Iup Jup) :
    KSubset.IsSortedPair I J := by
  have key : ∀ {A B : KSubset n k} {Aup Bup : KSubset n k'}, A.1 = insert c Aup.1 →
      B.1 = insert c Bup.1 → c ∉ Aup.1 → c ∉ Bup.1 →
      Aup.SortedBefore Bup → A.SortedBefore B := by
    intro A B Aup Bup hA hB hcA hcB hAB t
    have hpA : A.prefixCount t = Aup.prefixCount t + (if c ≤ t then 1 else 0) := by
      show (A.1.filter (· ≤ t)).card = (Aup.1.filter (· ≤ t)).card + _
      rw [hA]; exact prefixCount_insert Aup.1 hcA t
    have hpB : B.prefixCount t = Bup.prefixCount t + (if c ≤ t then 1 else 0) := by
      show (B.1.filter (· ≤ t)).card = (Bup.1.filter (· ≤ t)).card + _
      rw [hB]; exact prefixCount_insert Bup.1 hcB t
    have := hAB t
    rw [hpA, hpB]; omega
  rcases h with h | h
  · exact Or.inl (key hI hJ hcI hcJ h)
  · exact Or.inr (key hJ hI hcJ hcI h)

/-- For a facet vertex `w`, the lower support (frame dropped by 1 at the constant coordinate `c`)
is the up-support with `c` inserted. -/
theorem KuhnGeometricGridFacet.lowerSupport_eq_insert_supportOverMin {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) {c : Fin (d + 1)}
    (hj0const : F.coordMin hne c = F.coordMax hne c) (hcpos : 1 ≤ F.coordMin hne c)
    {w : SimplexGrid d N} (hwF : w ∈ F.vertices) :
    F.lowerSupport hne c w = insert c (F.supportOverMin hne w) ∧ c ∉ F.supportOverMin hne w := by
  classical
  have hwc : w.1 c = F.coordMin hne c := by
    have h1 := F.coordMin_le_coord hne hwF c
    have h2 := F.coord_le_coordMax hne hwF c
    omega
  refine ⟨?_, ?_⟩
  · ext i
    rw [F.mem_lowerSupport, lowerFrame_apply, Finset.mem_insert, F.mem_supportOverMin]
    have hband := F.vertex_isSameMinFrame hne hwF i
    by_cases hic : i = c
    · subst hic; rw [if_pos rfl]
      constructor
      · intro _; left; rfl
      · intro _; omega
    · rw [if_neg hic]
      constructor
      · intro h; right; omega
      · rintro (h | h)
        · exact absurd h hic
        · omega
  · rw [F.mem_supportOverMin]; omega

/-- THE BIJECTION (card equality): `supportOverMin` is a bijection between the same-min-frame
completions and the combinatorial same-frame extensions of the support wall (injectivity is the
upper-bound side, surjectivity is `exists_completion_of_extension`).  So the geometric and
combinatorial counts agree. -/
theorem KuhnGeometricGridFacet.sameMinFrameCompletions_card_eq_slift_extensions_card
    {d N : ℕ} (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) :
    (F.sameMinFrameCompletions hne).card =
      (KSubsetCollection.sameFrameExtensions
        (F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw))).card := by
  classical
  set wall := F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw) with hwall
  have himg : (F.sameMinFrameCompletions hne).image (F.supportOverMin hne)
      = (KSubsetCollection.sameFrameExtensions wall).image Subtype.val := by
    ext S
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [sameMinFrameCompletions, Finset.mem_filter] at hv
      exact ⟨⟨F.supportOverMin hne v, F.card_supportOverMin hne hv.2⟩,
        F.support_mem_sameFrameExtensions hne hv.1 hv.2, rfl⟩
    · rintro ⟨T, hT, rfl⟩
      obtain ⟨v, hv, hvs⟩ := F.exists_completion_of_extension hd hne hT
      exact ⟨v, hv, hvs⟩
  have h1 : ((F.sameMinFrameCompletions hne).image (F.supportOverMin hne)).card
      = (F.sameMinFrameCompletions hne).card :=
    Finset.card_image_of_injOn (F.supportOverMin_injOn_sameMinFrameCompletions hne)
  have h2 : ((KSubsetCollection.sameFrameExtensions wall).image Subtype.val).card
      = (KSubsetCollection.sameFrameExtensions wall).card :=
    Finset.card_image_of_injOn (fun a _ b _ h => Subtype.ext h)
  rw [← h1, himg, h2]

/-! ### `c = 1` UP-SIDE GEOMETRIC LIFT

The pure combinatorial `c = 1` up-side existence
(`KSubsetCollection.sameFrameExtensions_nonempty_of_commonAbsent_oneFrozen`) is crossed to the
geometry via the support wall.  The wall is intrinsically a codimension-one SORTED wall of CARD
`d` — it is the common-present reduction of the erased parent collection `D.subsets.erase S₀`
(`exists_parent_data`), which is a sorted (non-maximal) subcollection of the maximal `D.subsets`. -/

/-- The support wall `slift F.vertices` is sorted with card `d`: it equals
`reducedColl (D.subsets.erase S₀) (commonPresent …)` for the parent cell `D` (a sorted,
non-maximal collection of card `d = (d+1) - 1`). -/
theorem KuhnGeometricGridFacet.slift_isSorted_and_card {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) :
    KSubsetCollection.IsSorted
        (F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw))
      ∧ (F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw)).card = d := by
  classical
  obtain ⟨D, S₀, hS₀, hFeq⟩ := F.exists_parent_data
  set W' := D.subsets.erase S₀ with hW'
  have hW'ne : W'.Nonempty := by
    have h := hne; rw [hFeq] at h; exact h.of_image
  have hFvert : ∀ i, (F.vertices.image fun x => x.1 i)
      = W'.image (fun S => D.base i + chi S.1 i) := by
    intro i
    rw [hFeq, Finset.image_image]
    apply Finset.image_congr
    intro S _; rfl
  have hframe : ∀ i, F.coordMin hne i =
      D.base i + (if i ∈ KSubsetCollection.commonPresent W' then 1 else 0) :=
    fun i => F.coordMin_eq_base_add_commonPresent hne D.base W' hW'ne hFvert i
  have hcp : ∀ S ∈ W', KSubsetCollection.commonPresent W' ⊆ S.1 :=
    fun S hS i hi => (KSubsetCollection.mem_commonPresent_iff W' i).mp hi S hS
  have hm : ∀ S ∈ W',
      (S.1 \ KSubsetCollection.commonPresent W').card = N - ∑ i, F.coordMin hne i := by
    intro S hS
    have hcard : (S.1 \ KSubsetCollection.commonPresent W').card
        + (KSubsetCollection.commonPresent W').card = D.k := by
      rw [← Finset.card_union_of_disjoint Finset.sdiff_disjoint,
        Finset.sdiff_union_of_subset (hcp S hS), S.2]
    have hsumcoord : ∑ i, F.coordMin hne i =
        (∑ i, D.base i) + (KSubsetCollection.commonPresent W').card := by
      rw [Finset.sum_congr rfl (fun i _ => hframe i), Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
    have hsum := D.sum_base_add_k
    omega
  have hrel : F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw)
      = KSubsetReduction.reducedColl W' (KSubsetCollection.commonPresent W')
          (N - ∑ i, F.coordMin hne i) hm := by
    ext T
    rw [F.mem_slift hne, KSubsetReduction.mem_reducedColl]
    have hsupp : ∀ S : KSubset (d + 1) D.k,
        F.supportOverMin hne (cellVertexMap D S) = S.1 \ KSubsetCollection.commonPresent W' :=
      fun S => F.supportOverMin_eq_sdiff hne hframe (fun i => rfl)
    constructor
    · rintro ⟨w, hwV, hwT⟩
      rw [hFeq, Finset.mem_image] at hwV
      obtain ⟨S, hS, rfl⟩ := hwV
      exact ⟨S, hS, by rw [← hsupp S]; exact hwT⟩
    · rintro ⟨S, hS, hST⟩
      exact ⟨cellVertexMap D S, by rw [hFeq]; exact Finset.mem_image_of_mem _ hS,
        by rw [hsupp S]; exact hST⟩
  have hW'sorted : KSubsetCollection.IsSorted W' := fun I hI J hJ hIJ =>
    D.hsubsets.2 I (Finset.mem_of_mem_erase hI) J (Finset.mem_of_mem_erase hJ) hIJ
  have hW'card : W'.card = d := by
    rw [hW', Finset.card_erase_of_mem hS₀, D.hsubsets.1]; omega
  rw [hrel]
  refine ⟨KSubsetReduction.reducedColl_isSorted hW'sorted _ hcp _ hm, ?_⟩
  rw [KSubsetReduction.reducedColl_card _ hcp]; exact hW'card

/-- The support wall of a facet with exactly one constant coordinate has a same-frame
extension: the wall is a codim-1 sorted wall whose unique frozen coordinate is common-absent
(`commonPresent (slift) = ∅` always), so the pure `c = 1` up-side existence applies. -/
theorem KuhnGeometricGridFacet.slift_sameFrameExtensions_nonempty_of_constantCoords_card_eq_one
    {d N : ℕ} (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    (hone : (F.constantCoords hne).card = 1) :
    (KSubsetCollection.sameFrameExtensions
      (F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw))).Nonempty := by
  classical
  obtain ⟨hwallsorted, hwallcard⟩ := F.slift_isSorted_and_card hne
  have hwallne : (F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw)).Nonempty :=
    ⟨⟨F.supportOverMin hne hne.choose,
        F.card_supportOverMin hne (F.vertex_isSameMinFrame hne hne.choose_spec)⟩,
      (F.mem_slift hne).mpr ⟨hne.choose, hne.choose_spec, rfl⟩⟩
  have hcp_empty := F.commonPresent_slift_eq_empty hne
  have hfroz_card : (KSubsetCollection.frozenCoords
      (F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw))).card = 1 := by
    rw [F.frozenCoords_slift_eq_constantCoords hne]; exact hone
  have hca_eq : KSubsetCollection.commonAbsent
      (F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw))
      = KSubsetCollection.frozenCoords
        (F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw)) := by
    rw [KSubsetCollection.frozenCoords, hcp_empty, Finset.empty_union]
  obtain ⟨c, hc⟩ : (KSubsetCollection.commonAbsent
      (F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw))).Nonempty := by
    rw [← Finset.card_pos, hca_eq, hfroz_card]; omega
  exact KSubsetCollection.sameFrameExtensions_nonempty_of_commonAbsent_oneFrozen
    hwallsorted hwallne (hwallcard.trans (by omega)) hc hfroz_card

/-- **— THE GEOMETRIC LIFT.** A facet with exactly one constant coordinate has a nonempty
set of same-min-frame completions (the UP-side of the `c = 1` flip; combinatorial, NO `¬boundary`
needed).  Crosses through the `supportOverMin` bijection. -/
theorem KuhnGeometricGridFacet.sameMinFrameCompletions_nonempty_of_constantCoords_card_eq_one
    {d N : ℕ} (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    (hone : (F.constantCoords hne).card = 1) :
    (F.sameMinFrameCompletions hne).Nonempty := by
  classical
  have hslift := F.slift_sameFrameExtensions_nonempty_of_constantCoords_card_eq_one hne hone
  rw [← Finset.card_pos, F.sameMinFrameCompletions_card_eq_slift_extensions_card hd hne]
  exact Finset.card_pos.mpr hslift

/-- A facet with exactly one constant coordinate has EXACTLY ONE same-min-frame
completion (nonempty from ` from `sameMinFrameCompletions_card_le_one_of_constantCoord`
with the now-proved gap-fill hypothesis). -/
theorem KuhnGeometricGridFacet.sameMinFrameCompletions_card_eq_one_of_constantCoords_card_eq_one
    {d N : ℕ} (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    (hone : (F.constantCoords hne).card = 1) :
    (F.sameMinFrameCompletions hne).card = 1 := by
  classical
  have hne_same := F.sameMinFrameCompletions_nonempty_of_constantCoords_card_eq_one hd hne hone
  obtain ⟨c, hc⟩ : ∃ c, F.coordMin hne c = F.coordMax hne c := by
    obtain ⟨c, hc⟩ :=
      Finset.card_pos.mp (show 0 < (F.constantCoords hne).card by rw [hone]; omega)
    exact ⟨c, (F.mem_constantCoords_iff hne c).mp hc⟩
  have hle : (F.sameMinFrameCompletions hne).card ≤ 1 :=
    F.sameMinFrameCompletions_card_le_one_of_constantCoord hd
      KSubsetCollection.lowerGapFillHypothesis_holds hne hc
  have hpos : 0 < (F.sameMinFrameCompletions hne).card := Finset.card_pos.mpr hne_same
  omega

/-- The lower support wall is SORTED (inherited from `slift` via `isSortedPair_insert`). -/
theorem KuhnGeometricGridFacet.lowerSlift_isSorted {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) {c : Fin (d + 1)}
    (hj0const : F.coordMin hne c = F.coordMax hne c) (hcpos : 1 ≤ F.coordMin hne c)
    (hbandF : ∀ w ∈ F.vertices, F.IsLowerFrameBand hne c w) :
    KSubsetCollection.IsSorted (F.lowerSlift hne c F.vertices hbandF) := by
  classical
  have hslift := (F.slift_isSorted_and_card hne).1
  intro I hI J hJ hIJ
  rw [F.mem_lowerSlift] at hI hJ
  obtain ⟨w, hwF, hwI⟩ := hI
  obtain ⟨w', hw'F, hw'J⟩ := hJ
  obtain ⟨hIeq, hcw⟩ := F.lowerSupport_eq_insert_supportOverMin hne hj0const hcpos hwF
  obtain ⟨hJeq, hcw'⟩ := F.lowerSupport_eq_insert_supportOverMin hne hj0const hcpos hw'F
  refine KSubset.isSortedPair_insert
    (Iup := ⟨F.supportOverMin hne w, F.card_supportOverMin hne (F.vertex_isSameMinFrame hne hwF)⟩)
    (Jup := ⟨F.supportOverMin hne w', F.card_supportOverMin hne (F.vertex_isSameMinFrame hne hw'F)⟩)
    (c := c) ?_ ?_ hcw hcw' ?_
  · show I.1 = insert c (F.supportOverMin hne w); rw [← hwI]; exact hIeq
  · show J.1 = insert c (F.supportOverMin hne w'); rw [← hw'J]; exact hJeq
  · refine hslift _ ((F.mem_slift hne).mpr ⟨w, hwF, rfl⟩) _ ((F.mem_slift hne).mpr ⟨w', hw'F, rfl⟩) ?_
    intro h
    apply hIJ
    apply Subtype.ext
    rw [← hwI, ← hw'J, hIeq, hJeq, show F.supportOverMin hne w = F.supportOverMin hne w' from
      congrArg Subtype.val h]

/-- The constant coordinate `c` is COMMON-PRESENT in the lower support wall (every facet vertex's
lower support contains `c`, since the frame dropped by 1 there). -/
theorem KuhnGeometricGridFacet.commonPresent_c_lowerSlift {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) {c : Fin (d + 1)}
    (hcpos : 1 ≤ F.coordMin hne c)
    (hbandF : ∀ w ∈ F.vertices, F.IsLowerFrameBand hne c w) :
    c ∈ KSubsetCollection.commonPresent (F.lowerSlift hne c F.vertices hbandF) := by
  classical
  rw [KSubsetCollection.mem_commonPresent_iff]
  intro S hS
  rw [F.mem_lowerSlift] at hS
  obtain ⟨w, hwF, hwS⟩ := hS
  rw [← hwS, F.mem_lowerSupport, lowerFrame_apply, if_pos rfl]
  have := F.coordMin_le_coord hne hwF c; omega

/-- The lower support wall's frozen coordinates are exactly `F`'s constant coordinates (`c` is
common-present, every other constant coordinate is common-absent).  Dual of
`frozenCoords_slift_eq_constantCoords`. -/
theorem KuhnGeometricGridFacet.frozenCoords_lowerSlift_eq_constantCoords {d N : ℕ}
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty) {c : Fin (d + 1)}
    (hj0const : F.coordMin hne c = F.coordMax hne c) (hcpos : 1 ≤ F.coordMin hne c)
    (hbandF : ∀ w ∈ F.vertices, F.IsLowerFrameBand hne c w) :
    KSubsetCollection.frozenCoords (F.lowerSlift hne c F.vertices hbandF) = F.constantCoords hne := by
  classical
  have hslift_cp := F.commonPresent_slift_eq_empty hne
  have hslift_ca := F.commonAbsent_slift_eq_constantCoords hne
  -- membership of common-present/absent translated to per-vertex conditions
  have hcp_iff : ∀ i, i ∈ KSubsetCollection.commonPresent (F.lowerSlift hne c F.vertices hbandF)
      ↔ ∀ w ∈ F.vertices, i ∈ F.lowerSupport hne c w := by
    intro i
    rw [KSubsetCollection.mem_commonPresent_iff]
    constructor
    · intro h w hw
      exact h ⟨F.lowerSupport hne c w, F.card_lowerSupport hne c (hbandF w hw)⟩
        ((F.mem_lowerSlift hne c).mpr ⟨w, hw, rfl⟩)
    · intro h S hS
      rw [F.mem_lowerSlift] at hS; obtain ⟨w, hw, hwS⟩ := hS
      rw [← hwS]; exact h w hw
  have hca_iff : ∀ i, i ∈ KSubsetCollection.commonAbsent (F.lowerSlift hne c F.vertices hbandF)
      ↔ ∀ w ∈ F.vertices, i ∉ F.lowerSupport hne c w := by
    intro i
    rw [KSubsetCollection.mem_commonAbsent_iff]
    constructor
    · intro h w hw
      exact h ⟨F.lowerSupport hne c w, F.card_lowerSupport hne c (hbandF w hw)⟩
        ((F.mem_lowerSlift hne c).mpr ⟨w, hw, rfl⟩)
    · intro h S hS
      rw [F.mem_lowerSlift] at hS; obtain ⟨w, hw, hwS⟩ := hS
      rw [← hwS]; exact h w hw
  -- per-vertex: i ∈ lowerSupport w ↔ i = c ∨ i ∈ supportOverMin w
  have hmem_low : ∀ {i : Fin (d + 1)} {w : SimplexGrid d N}, w ∈ F.vertices →
      (i ∈ F.lowerSupport hne c w ↔ i = c ∨ i ∈ F.supportOverMin hne w) := by
    intro i w hw
    obtain ⟨hIeq, _⟩ := F.lowerSupport_eq_insert_supportOverMin hne hj0const hcpos hw
    rw [hIeq, Finset.mem_insert]
  ext i
  rw [F.mem_constantCoords_iff]
  simp only [KSubsetCollection.frozenCoords, Finset.mem_union, hcp_iff, hca_iff]
  by_cases hic : i = c
  · constructor
    · intro _; rw [hic]; exact hj0const
    · intro _; left; intro w hw; rw [hmem_low hw]; exact Or.inl hic
  · -- i ≠ c : frozen ⟺ common-absent ⟺ (off c) i constant
    have hca_eq : (∀ w ∈ F.vertices, i ∉ F.lowerSupport hne c w) ↔
        i ∈ F.constantCoords hne := by
      rw [← hslift_ca, KSubsetCollection.mem_commonAbsent_iff]
      constructor
      · intro h S hS
        rw [F.mem_slift] at hS; obtain ⟨w, hw, hwS⟩ := hS
        rw [← hwS]; intro hisup
        exact h w hw ((hmem_low hw).mpr (Or.inr hisup))
      · intro h w hw
        rw [hmem_low hw]; rintro (he | hisup)
        · exact hic he
        · exact h ⟨F.supportOverMin hne w, F.card_supportOverMin hne (F.vertex_isSameMinFrame hne hw)⟩
            ((F.mem_slift hne).mpr ⟨w, hw, rfl⟩) hisup
    rw [F.mem_constantCoords_iff] at hca_eq
    constructor
    · rintro (hp | ha)
      · -- i ≠ c common-present ⟹ i ∈ commonPresent slift = ∅, contradiction
        exfalso
        have hmem : i ∈ KSubsetCollection.commonPresent
            (F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw)) := by
          rw [KSubsetCollection.mem_commonPresent_iff]
          intro S hS
          rw [F.mem_slift] at hS; obtain ⟨w, hw, hwS⟩ := hS
          rw [← hwS]
          rcases (hmem_low hw).mp (hp w hw) with he | hisup
          · exact absurd he hic
          · exact hisup
        rw [hslift_cp] at hmem; exact absurd hmem (Finset.notMem_empty i)
      · exact hca_eq.mp ha
    · intro hconst
      exact Or.inr (hca_eq.mpr hconst)

/-- **DOWN-side existence — the c=1 cross-stratum lower completion.**  A facet with a
POSITIVE constant coordinate `c` (the `¬boundary` condition `coordMin c ≥ 1`) has a lower
completion: the lower support wall is codim-1 sorted, one-frozen with `c` common-present, so the
DOWN-side combinatorial existence gives a `lowerGapFillExtension`, lifted geometrically. -/
theorem KuhnGeometricGridFacet.lowerCompletions_nonempty_of_constantCoord_pos {d N : ℕ}
    (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    {c : Fin (d + 1)} (hc : c ∈ F.constantCoords hne) (hcpos : 0 < F.coordMin hne c) :
    (F.lowerCompletions hne).Nonempty := by
  classical
  have hj0const : F.coordMin hne c = F.coordMax hne c := (F.mem_constantCoords_iff hne c).mp hc
  have hcpos' : 1 ≤ F.coordMin hne c := hcpos
  have hbandF : ∀ w ∈ F.vertices, F.IsLowerFrameBand hne c w :=
    fun w hw => F.vertex_isLowerFrameBand hne c hj0const hcpos' hw
  have hone : (F.constantCoords hne).card = 1 :=
    le_antisymm (F.constantCoords_card_le_one hd hne) (Finset.card_pos.mpr ⟨c, hc⟩)
  have hWne : (F.lowerSlift hne c F.vertices hbandF).Nonempty := by
    rw [← Finset.card_pos, F.lowerSlift_card_of_band hne c F.vertices hbandF, F.vertices_card]
    omega
  have hWcard : (F.lowerSlift hne c F.vertices hbandF).card = d := by
    rw [F.lowerSlift_card_of_band hne c F.vertices hbandF, F.vertices_card]
  obtain ⟨T, hT⟩ := KSubsetCollection.lowerGapFillExtensions_nonempty_of_commonPresent_oneFrozen
    (show 0 < d by omega) (F.lowerSlift_isSorted hne hj0const hcpos' hbandF) hWne hWcard
    (F.commonPresent_c_lowerSlift hne hcpos' hbandF)
    (by rw [F.frozenCoords_lowerSlift_eq_constantCoords hne hj0const hcpos' hbandF]; exact hone)
  exact F.exists_lowerCompletion_of_lowerGapFillExtension hd hne hcpos' hbandF hT

/-- A facet with a positive constant coordinate has EXACTLY ONE lower completion (nonempty from
` from the unconditional `lowerCompletions_card_le_one`). -/
theorem KuhnGeometricGridFacet.lowerCompletions_card_eq_one_of_constantCoord_pos {d N : ℕ}
    (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    {c : Fin (d + 1)} (hc : c ∈ F.constantCoords hne) (hcpos : 0 < F.coordMin hne c) :
    (F.lowerCompletions hne).card = 1 := by
  have hpos : 0 < (F.lowerCompletions hne).card :=
    Finset.card_pos.mpr (F.lowerCompletions_nonempty_of_constantCoord_pos hd hne hc hcpos)
  have hle : (F.lowerCompletions hne).card ≤ 1 :=
    F.lowerCompletions_card_le_one hd hne KSubsetCollection.lowerGapFillHypothesis_holds
  omega

/-! ### The combinatorial lower bound for the `c = 0` converse

A codimension-one sorted wall (one with a same-frame extension) that has NO frozen coordinate has
exactly TWO same-frame extensions.  The `≤ 2` upper bound is
`sameFrame_extensions_card_le_two_of_erase_maximalSorted`; the `≥ 2` lower bound, proved below,
constructs the second extension and is the discrete pseudomanifold property of the sorted/Freudenthal
triangulation.  (Small cases are also checked by axiom-free `decide` in `Sperner/AuditNoFrozen.lean`:
`audit_d2_k1`, `audit_d2_k2`, `audit_d3_k2`.)

Proof structure.  Writing `W = C.erase T₀` with `C := insert T₀ W` maximal sorted (spectrum
`Ico b (b+n)`), split on whether `W`'s weight image is punctured (interior) or consecutive (endpoint),
mirroring the `≤ 2` trichotomy.
• Interior (`W.image` punctured at `w₀`): extensions inject into the two profiles `{L ∪ {γ} : γ ∈ U\L}`,
  with `L = aboveMinProfile S_lo`, `U = aboveMinProfile S_hi`, and `S_lo, S_hi ∈ W` the weight-neighbours
  `w₀ ∓ 1`.  The candidate for `L ∪ {γ}` is the descent swap `(S_lo.1 \ {γ+1}) ∪ {γ}`
  (`prefixCount_swapDescent`), valid when `γ` is a descent of `S_lo`; compatibility with the whole wall
  is by profile nesting (`L ⊆ L∪{γ} ⊆ U`) plus the spectrum gap.  Frozen-freeness forces the two gap
  coordinates non-adjacent (`no_adjacent_gap_of_no_frozen_interior`: an adjacent gap `{γ,γ+1}` would
  freeze the middle coordinate), and then both are descents of `S_lo`, giving the two extensions.
• Endpoint (`W.image` consecutive): the two extensions are the refill `T₀` and one exterior weight
  beyond it; frozen-freeness supplies the exterior one. -/

/-- The lower bound for a frozen-free codimension-one wall: at least two same-frame extensions. -/
def KSubsetCollection.NoFrozenWallHasTwoExtensions : Prop :=
  ∀ {n k : ℕ} {W : Finset (KSubset n k)},
    (KSubsetCollection.sameFrameExtensions W).Nonempty →
    KSubsetCollection.frozenCoords W = ∅ →
    2 ≤ (KSubsetCollection.sameFrameExtensions W).card

/-- **THE COMBINATORIAL LOWER BOUND — UNCONDITIONAL & axiom-clean.**  A frozen-free codimension-one
sorted wall has `≥ 2` same-frame extensions.  PURE DISPATCH (no new construction): from one
extension `V`, `W` is sorted with `|W| = n-1`; its `n-1` ranks are distinct in `{0,…,n-1}` and ALWAYS
include `0` (`exists_rank_zero_member`), so the missing rank `m ∈ {1,…,n-1}` — the MISSING-BOTTOM case
is vacuous.  `m = n-1` (missing top, `hmax`) ⟹ `…endpoint_full`; `1 ≤ m ≤ n-2` (interior gap, with
`n-1 ∈ ranks` ⟹ a rank-`(n-1)` member) ⟹ `…of_no_frozen_interior` with `Slo, Shi` the rank-`(m∓1)`
members. -/
theorem KSubsetCollection.noFrozenWallHasTwoExtensions :
    KSubsetCollection.NoFrozenWallHasTwoExtensions := by
  classical
  intro n k W hne_ext hfrozen
  obtain ⟨V, hVext⟩ := hne_ext
  rw [KSubsetCollection.mem_sameFrameExtensions_iff] at hVext
  obtain ⟨hVnotin, hVmax⟩ := hVext
  have hWsorted : KSubsetCollection.IsSorted W := fun I hI J hJ hIJ =>
    hVmax.2 I (Finset.mem_insert_of_mem hI) J (Finset.mem_insert_of_mem hJ) hIJ
  have hcardVW : (insert V W).card = n := hVmax.1
  have hn1 : 0 < n := hcardVW ▸ Finset.card_pos.mpr ⟨V, Finset.mem_insert_self _ _⟩
  have hWcard : W.card = n - 1 := by
    rw [Finset.card_insert_of_notMem hVnotin] at hcardVW; omega
  have hca : KSubsetCollection.commonAbsent W = ∅ :=
    (Finset.union_eq_empty.mp (by rw [← KSubsetCollection.frozenCoords]; exact hfrozen)).2
  have hWne : W.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h
    have hcae : KSubsetCollection.commonAbsent (∅ : Finset (KSubset n k)) = Finset.univ := by
      rw [Finset.eq_univ_iff_forall]; intro i
      rw [KSubsetCollection.mem_commonAbsent_iff]; intro S hS
      exact absurd hS (Finset.notMem_empty S)
    rw [h, hcae] at hca
    have hmem : (⟨0, hn1⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    rw [hca] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  by_cases hmax : ∀ S ∈ W, (KSubsetCollection.aboveMinProfile W hWne S).card ≤ n - 2
  · exact KSubsetCollection.sameFrameExtensions_two_of_no_frozen_endpoint_full
      hWsorted hWne hWcard hfrozen hmax
  · -- interior dispatch: the missing rank `m` is interior
    push_neg at hmax
    obtain ⟨Sstar, hSstarW, hSstarrank⟩ := hmax
    have hinj : Set.InjOn (fun S => (KSubsetCollection.aboveMinProfile W hWne S).card) (↑W) :=
      KSubsetCollection.aboveMinProfile_card_injective_on hWsorted hWne
    set R : Finset ℕ := W.image (fun S => (KSubsetCollection.aboveMinProfile W hWne S).card)
      with hR
    have hRcard : R.card = n - 1 := by rw [hR, Finset.card_image_of_injOn hinj, hWcard]
    have hRsub : R ⊆ Finset.range n := by
      intro x hx; rw [hR, Finset.mem_image] at hx; obtain ⟨S, _, rfl⟩ := hx
      exact Finset.mem_range.mpr (KSubsetCollection.aboveMinProfile_card_lt hn1 hWne S)
    obtain ⟨S0, hS0W, hS0prof⟩ := KSubsetCollection.exists_rank_zero_member hWsorted hWne
    have h0R : 0 ∈ R := by
      rw [hR, Finset.mem_image]; exact ⟨S0, hS0W, by rw [hS0prof, Finset.card_empty]⟩
    have hSstar_lt : (KSubsetCollection.aboveMinProfile W hWne Sstar).card < n :=
      KSubsetCollection.aboveMinProfile_card_lt hn1 hWne Sstar
    have hn1R : n - 1 ∈ R := by
      rw [hR, Finset.mem_image]; exact ⟨Sstar, hSstarW, by omega⟩
    have hcompl_card : (Finset.range n \ R).card = 1 := by
      rw [Finset.card_sdiff_of_subset hRsub, Finset.card_range, hRcard]; omega
    obtain ⟨m, hm⟩ := Finset.card_eq_one.mp hcompl_card
    have hmmem : m ∈ Finset.range n \ R := by rw [hm]; exact Finset.mem_singleton_self m
    have hmlt : m < n := Finset.mem_range.mp (Finset.mem_sdiff.mp hmmem).1
    have hmnotR : m ∉ R := (Finset.mem_sdiff.mp hmmem).2
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · exfalso; apply hmnotR; rw [h0]; exact h0R
      · exact h0
    have hmn2 : m ≤ n - 2 := by
      by_contra h; push_neg at h
      exact hmnotR ((show m = n - 1 by omega) ▸ hn1R)
    have hm_pred_R : m - 1 ∈ R := by
      by_contra h
      have hx : m - 1 ∈ Finset.range n \ R :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (by omega), h⟩
      rw [hm, Finset.mem_singleton] at hx; omega
    have hm_succ_R : m + 1 ∈ R := by
      by_contra h
      have hx : m + 1 ∈ Finset.range n \ R :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (by omega), h⟩
      rw [hm, Finset.mem_singleton] at hx; omega
    rw [hR, Finset.mem_image] at hm_pred_R hm_succ_R
    obtain ⟨Slo, hSloW, hSlorank⟩ := hm_pred_R
    obtain ⟨Shi, hShiW, hShirank⟩ := hm_succ_R
    have hUcard : (KSubsetCollection.aboveMinProfile W hWne Shi).card
        = (KSubsetCollection.aboveMinProfile W hWne Slo).card + 2 := by
      rw [hSlorank, hShirank]; omega
    have hLU : KSubsetCollection.aboveMinProfile W hWne Slo
        ⊆ KSubsetCollection.aboveMinProfile W hWne Shi := by
      rcases KSubsetCollection.aboveMinProfile_subset_or_superset hWsorted hWne hSloW hShiW
        with h | h
      · exact h
      · exfalso; have hle := Finset.card_le_card h; rw [hSlorank, hShirank] at hle; omega
    have hgap : ∀ S ∈ W, (KSubsetCollection.aboveMinProfile W hWne S).card
        ≠ (KSubsetCollection.aboveMinProfile W hWne Slo).card + 1 := by
      intro S hSW hcon
      rw [hSlorank] at hcon
      apply hmnotR
      rw [hR, Finset.mem_image]
      refine ⟨S, hSW, ?_⟩
      show (KSubsetCollection.aboveMinProfile W hWne S).card = m
      omega
    have hfrozen_card : (KSubsetCollection.frozenCoords W).card = 0 := by
      rw [hfrozen, Finset.card_empty]
    exact KSubsetCollection.sameFrameExtensions_two_of_no_frozen_interior
      hWsorted hWne hWcard hSloW hShiW hLU hUcard hgap hfrozen_card

/-- With no constant coordinate, a facet has exactly two same-min-frame
completions.  (`≤ 2` is `sameMinFrameCompletions_card_le_two`; `≥ 2` comes from the bijection
and the now-UNCONDITIONAL combinatorial frozen-free lower bound `noFrozenWallHasTwoExtensions`.) -/
theorem KuhnGeometricGridFacet.sameMinFrameCompletions_card_eq_two_of_no_constantCoords
    {d N : ℕ} (hd : 2 ≤ d)
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    (hzero : (F.constantCoords hne).card = 0) :
    (F.sameMinFrameCompletions hne).card = 2 := by
  classical
  have hle := F.sameMinFrameCompletions_card_le_two hne
  have heq := F.sameMinFrameCompletions_card_eq_slift_extensions_card hd hne
  -- a completion exists, giving a same-frame extension of the wall
  have hcompne : F.completingOppositeVertices.Nonempty := by
    rw [← Finset.card_pos, ← F.incidentCells_card_eq_completions_card]
    exact Finset.card_pos.mpr F.incidentCells_nonempty
  rw [F.completingOppositeVertices_eq_sameMinFrame_of_no_constantCoords hne hzero] at hcompne
  obtain ⟨v₀, hv₀⟩ := hcompne
  rw [sameMinFrameCompletions, Finset.mem_filter] at hv₀
  have hwallne : (KSubsetCollection.sameFrameExtensions
      (F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw))).Nonempty :=
    ⟨⟨F.supportOverMin hne v₀, F.card_supportOverMin hne hv₀.2⟩,
      F.support_mem_sameFrameExtensions hne hv₀.1 hv₀.2⟩
  have hfrozen : KSubsetCollection.frozenCoords
      (F.slift hne F.vertices (fun w hw => F.vertex_isSameMinFrame hne hw)) = ∅ := by
    rw [F.frozenCoords_slift_eq_constantCoords hne]
    exact Finset.card_eq_zero.mp hzero
  have hge := KSubsetCollection.noFrozenWallHasTwoExtensions hwallne hfrozen
  omega

/-- With no constant coordinate, a facet has exactly two completing opposite
vertices (all completions are same-min-frame). -/
theorem KuhnGeometricGridFacet.completingOppositeVertices_card_eq_two_of_no_constantCoords
    {d N : ℕ} (hd : 2 ≤ d)
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    (hzero : (F.constantCoords hne).card = 0) :
    F.completingOppositeVertices.card = 2 := by
  rw [F.completingOppositeVertices_eq_sameMinFrame_of_no_constantCoords hne hzero]
  exact F.sameMinFrameCompletions_card_eq_two_of_no_constantCoords hd hne hzero

/-- **— THE `c = 0` CONVERSE:** a facet with no constant coordinate is incident to
exactly two cells. -/
theorem KuhnGeometricGridFacet.incidentCells_card_eq_two_of_no_constantCoords
    {d N : ℕ} (hd : 2 ≤ d)
    (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    (hzero : (F.constantCoords hne).card = 0) :
    F.incidentCells.card = 2 := by
  rw [F.incidentCells_card_eq_completions_card]
  exact F.completingOppositeVertices_card_eq_two_of_no_constantCoords hd hne hzero

/-! ### `c = 1`, NOT boundary ⟹ degree two — the final local-incidence assembly -/

/-- A facet with exactly ONE constant coordinate that is NOT a boundary coordinate has
exactly TWO completions: the UP-side same-min-frame completion (`= 1`) and the DOWN-side lower
completion (`= 1`), which are disjoint and partition the completions. -/
theorem KuhnGeometricGridFacet.completingOppositeVertices_card_eq_two_of_constantCoords_card_eq_one_not_boundary
    {d N : ℕ} (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    (hone : (F.constantCoords hne).card = 1) (hnb : ¬ F.IsBoundary) :
    F.completingOppositeVertices.card = 2 := by
  classical
  obtain ⟨c, hc, _⟩ := F.exists_unique_constantCoord_of_card_eq_one hne hone
  have hcpos : 0 < F.coordMin hne c := F.constantCoord_pos_of_not_boundary hne hnb hc
  have hsame : (F.sameMinFrameCompletions hne).card = 1 :=
    F.sameMinFrameCompletions_card_eq_one_of_constantCoords_card_eq_one hd hne hone
  have hlow : (F.lowerCompletions hne).card = 1 :=
    F.lowerCompletions_card_eq_one_of_constantCoord_pos hd hne hc hcpos
  have hdisj := F.sameMinFrameCompletions_disjoint_lowerCompletions hne
  have heq : F.completingOppositeVertices
      = F.sameMinFrameCompletions hne ∪ F.lowerCompletions hne := by
    refine Finset.Subset.antisymm (F.completions_subset_same_union_lower hne) ?_
    refine Finset.union_subset (fun v hv => ?_) (fun v hv => ?_)
    · rw [sameMinFrameCompletions, Finset.mem_filter] at hv; exact hv.1
    · exact ((F.mem_lowerCompletions hne v).mp hv).1
  rw [heq, Finset.card_union_of_disjoint hdisj, hsame, hlow]

/-- A facet with exactly one constant coordinate that is not boundary is incident to
exactly two cells. -/
theorem KuhnGeometricGridFacet.incidentCells_card_eq_two_of_constantCoords_card_eq_one_not_boundary
    {d N : ℕ} (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N) (hne : F.vertices.Nonempty)
    (hone : (F.constantCoords hne).card = 1) (hnb : ¬ F.IsBoundary) :
    F.incidentCells.card = 2 := by
  rw [F.incidentCells_card_eq_completions_card]
  exact F.completingOppositeVertices_card_eq_two_of_constantCoords_card_eq_one_not_boundary
    hd hne hone hnb

/-- **THE `¬boundary` CONVERSE.**  A non-boundary facet of a `≥ 2`-dimensional Kuhn
grid is incident to exactly TWO cells.  Dispatch on the constant-coordinate count:
`c = 0` (no constant coordinate) is the unconditional `incidentCells_card_eq_two_of_no_constantCoords`;
`c = 1` is the up-side + down-side assembly above. -/
theorem KuhnGeometricGridFacet.incidentCells_card_eq_two_of_not_boundary {d N : ℕ}
    (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N) (hnb : ¬ F.IsBoundary) :
    F.incidentCells.card = 2 := by
  classical
  have hne := F.vertices_nonempty_of_two_le hd
  rcases F.constantCoords_card_eq_zero_or_one hd hne with hzero | hone
  · exact F.incidentCells_card_eq_two_of_no_constantCoords hd hne hzero
  · exact F.incidentCells_card_eq_two_of_constantCoords_card_eq_one_not_boundary hd hne hone hnb

/-- **THE LOCAL MANIFOLD-WITH-BOUNDARY CLASSIFICATION (degree one).**  A facet is incident to
exactly one cell iff it is a boundary facet. -/
theorem KuhnGeometricGridFacet.incidentCells_card_eq_one_iff_boundary {d N : ℕ}
    (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N) :
    F.incidentCells.card = 1 ↔ F.IsBoundary := by
  constructor
  · intro h1
    by_contra hnb
    have h2 := F.incidentCells_card_eq_two_of_not_boundary hd hnb
    omega
  · exact F.incidentCells_card_eq_one_of_boundary hd

/-- **THE LOCAL MANIFOLD-WITH-BOUNDARY CLASSIFICATION (degree two).**  A facet is incident to
exactly two cells iff it is an interior (non-boundary) facet. -/
theorem KuhnGeometricGridFacet.incidentCells_card_eq_two_iff_not_boundary {d N : ℕ}
    (hd : 2 ≤ d) (F : KuhnGeometricGridFacet d N) :
    F.incidentCells.card = 2 ↔ ¬ F.IsBoundary := by
  constructor
  · intro h2 hbd
    have h1 := F.incidentCells_card_eq_one_of_boundary hd hbd
    omega
  · exact F.incidentCells_card_eq_two_of_not_boundary hd

/-! ### Stable public API aliases -/

/-- **Interior facets have degree two** (stable public name for
`KuhnGeometricGridFacet.incidentCells_card_eq_two_of_not_boundary`). -/
alias kuhn_interior_facet_two_cells :=
  KuhnGeometricGridFacet.incidentCells_card_eq_two_of_not_boundary

/-- **The local incidence classification** (stable public name for
`KuhnGeometricGridFacet.incidentCells_card_eq_two_iff_not_boundary`): a facet is shared by
two cells iff it is interior. -/
alias kuhn_facet_incidence_classification :=
  KuhnGeometricGridFacet.incidentCells_card_eq_two_iff_not_boundary

end BarycentricFreudenthal
end SpernerFreudenthal
end EcoLean
