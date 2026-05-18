import EcoLean.GameTheory.MathLanguage.SetsFunctionsCorrespondences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.Sequences

namespace EcoLean.GameTheory

namespace Correspondence

universe u v

/--
Integer barycentric grid points of mesh `N` on the standard simplex.

An element is a tuple of natural numbers whose coordinates sum to `N`;
geometrically it represents the point with coordinates `a i / N`.
-/
abbrev SimplexGrid (ι : Type u) [Fintype ι] (N : ℕ) :=
  {a : ι → ℕ // ∑ i, a i = N}

namespace SimplexGrid

variable {ι : Type u} [Fintype ι] {N : ℕ}

/-- The support of an integer barycentric grid point. -/
def support (a : SimplexGrid ι N) : Finset ι :=
  Finset.univ.filter fun i => a.1 i ≠ 0

@[simp] theorem mem_support_iff {a : SimplexGrid ι N} {i : ι} :
    i ∈ support a ↔ a.1 i ≠ 0 := by
  simp [support]

theorem coord_le_mesh (a : SimplexGrid ι N) (i : ι) :
    a.1 i ≤ N := by
  calc
    a.1 i ≤ ∑ j, a.1 j :=
      Finset.single_le_sum (fun j _hj => Nat.zero_le (a.1 j)) (Finset.mem_univ i)
    _ = N := a.2

/-- A bounded-coordinate encoding of the finite simplex grid. -/
def toFinVector (a : SimplexGrid ι N) : ι → Fin (N + 1) :=
  fun i => ⟨a.1 i, Nat.lt_succ_of_le (coord_le_mesh a i)⟩

@[simp] theorem toFinVector_apply_val (a : SimplexGrid ι N) (i : ι) :
    (toFinVector a i : ℕ) = a.1 i :=
  rfl

theorem toFinVector_injective :
    Function.Injective (toFinVector (ι := ι) (N := N)) := by
  intro a b h
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun h i)

/-- The integer barycentric grid is finite. -/
noncomputable instance instFintype : Fintype (SimplexGrid ι N) := by
  classical
  exact Fintype.ofInjective (toFinVector (ι := ι) (N := N)) toFinVector_injective

/-- The mesh-one vertex supported at a single coordinate. -/
def unitVertex [DecidableEq ι] (i : ι) : SimplexGrid ι 1 := by
  refine ⟨fun j => if j = i then 1 else 0, ?_⟩
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [hji]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

@[simp] theorem unitVertex_apply_self [DecidableEq ι] (i : ι) :
    (unitVertex i).1 i = 1 := by
  simp [unitVertex]

@[simp] theorem unitVertex_apply_ne [DecidableEq ι] {i j : ι} (hji : j ≠ i) :
    (unitVertex i).1 j = 0 := by
  simp [unitVertex, hji]

theorem unitVertex_apply_eq_one_or_zero [DecidableEq ι] (i j : ι) :
    (unitVertex i).1 j = 1 ∨ (unitVertex i).1 j = 0 := by
  by_cases hji : j = i
  · exact Or.inl (by simp [hji])
  · exact Or.inr (unitVertex_apply_ne hji)

/--
Extend a grid point on a face `J` to the ambient simplex by filling all
coordinates outside `J` with zero.
-/
noncomputable def extendFace [DecidableEq ι] (J : Finset ι)
    (a : SimplexGrid {i // i ∈ J} N) : SimplexGrid ι N := by
  refine ⟨fun i => if h : i ∈ J then a.1 ⟨i, h⟩ else 0, ?_⟩
  calc
    (∑ i : ι, if h : i ∈ J then a.1 ⟨i, h⟩ else 0)
        = (∑ i ∈ J, if h : i ∈ J then a.1 ⟨i, h⟩ else 0) := by
          exact (Finset.sum_subset (Finset.subset_univ J)
            (fun i _hi hiJ => by simp [hiJ])).symm
    _ = (∑ i : {i // i ∈ J},
          (if h : (i : ι) ∈ J then a.1 ⟨i, h⟩ else 0)) := by
          simpa using
            (Finset.sum_finset_coe
              (fun i => if h : i ∈ J then a.1 ⟨i, h⟩ else 0) J).symm
    _ = N := by
          simpa using a.2

@[simp] theorem extendFace_apply_of_mem [DecidableEq ι] (J : Finset ι)
    (a : SimplexGrid {i // i ∈ J} N) {i : ι} (hi : i ∈ J) :
    (extendFace J a).1 i = a.1 ⟨i, hi⟩ := by
  simp [extendFace, hi]

@[simp] theorem extendFace_apply_of_not_mem [DecidableEq ι] (J : Finset ι)
    (a : SimplexGrid {i // i ∈ J} N) {i : ι} (hi : i ∉ J) :
    (extendFace J a).1 i = 0 := by
  simp [extendFace, hi]

theorem extendFace_support_subset [DecidableEq ι] (J : Finset ι)
    (a : SimplexGrid {i // i ∈ J} N) :
    support (extendFace J a) ⊆ J := by
  intro i hi
  by_contra hiJ
  have hnonzero : (extendFace J a).1 i ≠ 0 := mem_support_iff.mp hi
  exact hnonzero (extendFace_apply_of_not_mem J a hiJ)

theorem extendFace_injective [DecidableEq ι] (J : Finset ι) :
    Function.Injective (extendFace (ι := ι) (N := N) J) := by
  intro a b hab
  apply Subtype.ext
  funext i
  have hcoord := congrArg (fun x : SimplexGrid ι N => x.1 (i : ι)) hab
  simpa using hcoord

/-- Reindex a grid point along an equivalence of coordinate types. -/
def reindex {κ : Type v} [Fintype κ] (e : ι ≃ κ)
    (a : SimplexGrid ι N) : SimplexGrid κ N := by
  refine ⟨fun k => a.1 (e.symm k), ?_⟩
  calc
    (∑ k : κ, a.1 (e.symm k)) = ∑ i : ι, a.1 i := by
      exact Fintype.sum_equiv e.symm
        (fun k : κ => a.1 (e.symm k)) (fun i : ι => a.1 i) (by intro k; simp)
    _ = N := a.2

@[simp] theorem reindex_apply {κ : Type v} [Fintype κ] (e : ι ≃ κ)
    (a : SimplexGrid ι N) (k : κ) :
    (reindex e a).1 k = a.1 (e.symm k) :=
  rfl

@[simp] theorem reindex_symm_reindex {κ : Type v} [Fintype κ] (e : ι ≃ κ)
    (a : SimplexGrid ι N) :
    reindex e.symm (reindex e a) = a := by
  apply Subtype.ext
  funext i
  simp [reindex]

@[simp] theorem reindex_reindex_symm {κ : Type v} [Fintype κ] (e : ι ≃ κ)
    (a : SimplexGrid κ N) :
    reindex e (reindex e.symm a) = a := by
  apply Subtype.ext
  funext k
  simp [reindex]

theorem mem_support_reindex_iff {κ : Type v} [Fintype κ] (e : ι ≃ κ)
    (a : SimplexGrid ι N) {k : κ} :
    k ∈ support (reindex e a) ↔ e.symm k ∈ support a := by
  simp [support, reindex]

theorem support_nonempty {a : SimplexGrid ι N} (hN : 0 < N) :
    (support a).Nonempty := by
  by_contra hsupport
  have hzero : ∀ i, a.1 i = 0 := by
    intro i
    by_contra hi
    exact hsupport ⟨i, by simp [support, hi]⟩
  have hsum_zero : (∑ i, a.1 i) = 0 := by
    simp [hzero]
  have hNzero : N = 0 := by
    rw [← a.2, hsum_zero]
  exact (Nat.ne_of_gt hN) hNzero

/-- The point of the standard simplex represented by an integer grid point. -/
noncomputable def toStdSimplex (hN : 0 < N) (a : SimplexGrid ι N) :
    stdSimplex ℝ ι := by
  refine ⟨fun i => (a.1 i : ℝ) / (N : ℝ), ?_, ?_⟩
  · intro i
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have hNne : (N : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hN)
    have hsum : (∑ i, (a.1 i : ℝ)) = (N : ℝ) := by
      exact_mod_cast a.2
    calc
      (∑ i, (a.1 i : ℝ) / (N : ℝ))
          = (∑ i, (a.1 i : ℝ)) * (N : ℝ)⁻¹ := by
            simp [div_eq_mul_inv, Finset.sum_mul]
      _ = (N : ℝ) * (N : ℝ)⁻¹ := by rw [hsum]
      _ = 1 := mul_inv_cancel₀ hNne

@[simp] theorem toStdSimplex_apply (hN : 0 < N) (a : SimplexGrid ι N) (i : ι) :
    toStdSimplex hN a i = (a.1 i : ℝ) / (N : ℝ) :=
  rfl

theorem toStdSimplex_apply_eq_zero_iff (hN : 0 < N)
    (a : SimplexGrid ι N) (i : ι) :
    toStdSimplex hN a i = 0 ↔ a.1 i = 0 := by
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  rw [toStdSimplex_apply]
  simp [hNne]

theorem toStdSimplex_apply_ne_zero_iff (hN : 0 < N)
    (a : SimplexGrid ι N) (i : ι) :
    toStdSimplex hN a i ≠ 0 ↔ a.1 i ≠ 0 := by
  simpa [not_iff_not] using (toStdSimplex_apply_eq_zero_iff hN a i).not

theorem toStdSimplex_mem_face_support (hN : 0 < N) (a : SimplexGrid ι N) :
    toStdSimplex hN a ∈ stdSimplexFace (support a) := by
  intro i hi
  exact mem_support_iff.mpr ((toStdSimplex_apply_ne_zero_iff hN a i).mp hi)

theorem toStdSimplex_mem_face_iff_support_subset (hN : 0 < N)
    (a : SimplexGrid ι N) {J : Finset ι} :
    toStdSimplex hN a ∈ stdSimplexFace J ↔ support a ⊆ J := by
  constructor
  · intro hx i hi
    exact hx i ((toStdSimplex_apply_ne_zero_iff hN a i).mpr (mem_support_iff.mp hi))
  · intro hsubset
    exact stdSimplexFace_mono hsubset (toStdSimplex_mem_face_support hN a)

theorem extendFace_mem_face [DecidableEq ι] (J : Finset ι)
    (hN : 0 < N) (a : SimplexGrid {i // i ∈ J} N) :
    toStdSimplex hN (extendFace J a) ∈ stdSimplexFace J := by
  rw [toStdSimplex_mem_face_iff_support_subset hN]
  exact extendFace_support_subset J a

theorem toStdSimplex_extendFace [DecidableEq ι] (J : Finset ι)
    (hN : 0 < N) (a : SimplexGrid {i // i ∈ J} N) :
    toStdSimplex hN (extendFace J a) =
      stdSimplexFaceMap J (toStdSimplex hN a) := by
  ext i
  by_cases hi : i ∈ J
  · rw [stdSimplexFaceMap_apply_of_mem J (toStdSimplex hN a) hi,
      toStdSimplex_apply, toStdSimplex_apply, extendFace_apply_of_mem J a hi]
  · rw [stdSimplexFaceMap_apply_of_not_mem J (toStdSimplex hN a) hi,
      toStdSimplex_apply, extendFace_apply_of_not_mem J a hi]
    simp

theorem exists_label_mem_support_and_cover
    {C : ι → Set (stdSimplex ℝ ι)} (hC : StdSimplexKKMCondition C)
    (hN : 0 < N) (a : SimplexGrid ι N) :
    ∃ i ∈ support a, toStdSimplex hN a ∈ C i := by
  exact hC (support a) (support_nonempty hN) (toStdSimplex hN a)
    (toStdSimplex_mem_face_support hN a)

end SimplexGrid

/--
A Sperner labeling of the integer barycentric grid.

The boundary condition says that a grid vertex can only receive a label from
the support of that vertex, i.e. not from a coordinate that is zero there.
-/
structure GridSpernerLabeling (ι : Type u) [Fintype ι] (N : ℕ) where
  label : SimplexGrid ι N → ι
  label_mem_support : ∀ a, label a ∈ SimplexGrid.support a

namespace GridSpernerLabeling

variable {ι : Type u} [Fintype ι] {N : ℕ}

/-- The set of labels attained on a finite family of grid vertices. -/
def labelsOn [DecidableEq ι] (L : GridSpernerLabeling ι N)
    (cell : Finset (SimplexGrid ι N)) : Finset ι :=
  cell.image L.label

@[simp] theorem mem_labelsOn_iff [DecidableEq ι]
    (L : GridSpernerLabeling ι N) (cell : Finset (SimplexGrid ι N)) {i : ι} :
    i ∈ L.labelsOn cell ↔ ∃ a ∈ cell, L.label a = i := by
  simp [labelsOn]

/-- A finite family of grid vertices is fully labeled if it sees every label. -/
def FullyLabeledOn [DecidableEq ι] (L : GridSpernerLabeling ι N)
    (cell : Finset (SimplexGrid ι N)) : Prop :=
  ∀ i : ι, i ∈ L.labelsOn cell

theorem fullyLabeledOn_iff [DecidableEq ι]
    (L : GridSpernerLabeling ι N) (cell : Finset (SimplexGrid ι N)) :
    L.FullyLabeledOn cell ↔ ∀ i : ι, ∃ a ∈ cell, L.label a = i := by
  simp [FullyLabeledOn]

theorem label_ne_of_coord_eq_zero (L : GridSpernerLabeling ι N)
    (a : SimplexGrid ι N) {i : ι} (hi : a.1 i = 0) :
    L.label a ≠ i := by
  intro hlabel
  have hnonzero : a.1 (L.label a) ≠ 0 :=
    SimplexGrid.mem_support_iff.mp (L.label_mem_support a)
  exact hnonzero (by simpa [hlabel] using hi)

theorem label_unitVertex [DecidableEq ι] (L : GridSpernerLabeling ι 1)
    (i : ι) :
    L.label (SimplexGrid.unitVertex i) = i := by
  by_contra hne
  exact L.label_ne_of_coord_eq_zero (SimplexGrid.unitVertex i) (i := L.label (SimplexGrid.unitVertex i))
    (SimplexGrid.unitVertex_apply_ne hne) rfl

theorem label_extendFace_mem [DecidableEq ι] (L : GridSpernerLabeling ι N)
    (J : Finset ι) (a : SimplexGrid {i // i ∈ J} N) :
    L.label (SimplexGrid.extendFace J a) ∈ J := by
  have hnonzero :
      (SimplexGrid.extendFace J a).1 (L.label (SimplexGrid.extendFace J a)) ≠ 0 :=
    SimplexGrid.mem_support_iff.mp (L.label_mem_support (SimplexGrid.extendFace J a))
  by_contra hnot
  exact hnonzero (SimplexGrid.extendFace_apply_of_not_mem J a hnot)

/--
Restrict a Sperner labeling to a face. The ambient boundary condition ensures
that every extended face grid point is labeled by a coordinate belonging to
the face.
-/
noncomputable def restrictFace [DecidableEq ι] (L : GridSpernerLabeling ι N)
    (J : Finset ι) : GridSpernerLabeling {i // i ∈ J} N where
  label := fun a =>
    ⟨L.label (SimplexGrid.extendFace J a), L.label_extendFace_mem J a⟩
  label_mem_support := by
    intro a
    rw [SimplexGrid.mem_support_iff]
    have hnonzero :
        (SimplexGrid.extendFace J a).1 (L.label (SimplexGrid.extendFace J a)) ≠ 0 :=
      SimplexGrid.mem_support_iff.mp (L.label_mem_support (SimplexGrid.extendFace J a))
    change a.1 ⟨L.label (SimplexGrid.extendFace J a), L.label_extendFace_mem J a⟩ ≠ 0
    intro hzero
    exact hnonzero (by
      rw [SimplexGrid.extendFace_apply_of_mem J a (L.label_extendFace_mem J a)]
      exact hzero)

@[simp] theorem restrictFace_label_coe [DecidableEq ι]
    (L : GridSpernerLabeling ι N) (J : Finset ι)
    (a : SimplexGrid {i // i ∈ J} N) :
    ((L.restrictFace J).label a : ι) =
      L.label (SimplexGrid.extendFace J a) :=
  rfl

/-- Transport a Sperner labeling along an equivalence of coordinate types. -/
def reindex {κ : Type v} [Fintype κ] (e : ι ≃ κ)
    (L : GridSpernerLabeling ι N) : GridSpernerLabeling κ N where
  label := fun b => e (L.label (SimplexGrid.reindex e.symm b))
  label_mem_support := by
    intro b
    rw [SimplexGrid.mem_support_iff]
    have hold :
        (SimplexGrid.reindex e.symm b).1
          (L.label (SimplexGrid.reindex e.symm b)) ≠ 0 :=
      SimplexGrid.mem_support_iff.mp
        (L.label_mem_support (SimplexGrid.reindex e.symm b))
    simpa using hold

@[simp] theorem reindex_label {κ : Type v} [Fintype κ] (e : ι ≃ κ)
    (L : GridSpernerLabeling ι N) (b : SimplexGrid κ N) :
    (L.reindex e).label b = e (L.label (SimplexGrid.reindex e.symm b)) :=
  rfl

end GridSpernerLabeling

/--
A small cell in the integer barycentric mesh.

This is the geometric target for the later Kuhn/Freudenthal triangulation:
actual triangulation cells will be instances of this structure. The
`coordinate_span_le_one` field is the reusable mesh-diameter estimate.
-/
structure GridSmallCell (ι : Type u) [Fintype ι] (N : ℕ) where
  vertices : Finset (SimplexGrid ι N)
  nonempty : vertices.Nonempty
  coordinate_span_le_one :
    ∀ ⦃a⦄, a ∈ vertices → ∀ ⦃b⦄, b ∈ vertices → ∀ i : ι,
      a.1 i ≤ b.1 i + 1 ∧ b.1 i ≤ a.1 i + 1

namespace GridSmallCell

variable {ι : Type u} [Fintype ι] {N : ℕ}

instance : Coe (GridSmallCell ι N) (Finset (SimplexGrid ι N)) :=
  ⟨GridSmallCell.vertices⟩

@[simp] theorem mem_coe {cell : GridSmallCell ι N} {a : SimplexGrid ι N} :
    a ∈ (cell : Finset (SimplexGrid ι N)) ↔ a ∈ cell.vertices :=
  Iff.rfl

/-- A small cell is fully labeled when its vertices see every label. -/
def FullyLabeled [DecidableEq ι] (cell : GridSmallCell ι N)
    (L : GridSpernerLabeling ι N) : Prop :=
  L.FullyLabeledOn cell.vertices

theorem fullyLabeled_iff [DecidableEq ι] (cell : GridSmallCell ι N)
    (L : GridSpernerLabeling ι N) :
    cell.FullyLabeled L ↔ ∀ i : ι, ∃ a ∈ cell.vertices, L.label a = i := by
  exact GridSpernerLabeling.fullyLabeledOn_iff L cell.vertices

theorem exists_vertex (cell : GridSmallCell ι N) :
    ∃ a, a ∈ cell.vertices :=
  cell.nonempty

theorem coord_le_add_one (cell : GridSmallCell ι N)
    {a b : SimplexGrid ι N} (ha : a ∈ cell.vertices) (hb : b ∈ cell.vertices)
    (i : ι) :
    a.1 i ≤ b.1 i + 1 :=
  (cell.coordinate_span_le_one ha hb i).1

theorem abs_coord_sub_le_one (cell : GridSmallCell ι N)
    {a b : SimplexGrid ι N} (ha : a ∈ cell.vertices) (hb : b ∈ cell.vertices)
    (i : ι) :
    |(a.1 i : ℝ) - (b.1 i : ℝ)| ≤ 1 := by
  rcases cell.coordinate_span_le_one ha hb i with ⟨hab, hba⟩
  rw [abs_le]
  constructor
  · have hba' : (b.1 i : ℝ) ≤ (a.1 i : ℝ) + 1 := by
      exact_mod_cast hba
    linarith
  · have hab' : (a.1 i : ℝ) ≤ (b.1 i : ℝ) + 1 := by
      exact_mod_cast hab
    linarith

theorem toStdSimplex_coord_abs_sub_le (cell : GridSmallCell ι N)
    (hN : 0 < N) {a b : SimplexGrid ι N}
    (ha : a ∈ cell.vertices) (hb : b ∈ cell.vertices) (i : ι) :
    |SimplexGrid.toStdSimplex hN a i - SimplexGrid.toStdSimplex hN b i| ≤
      (1 : ℝ) / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN
  have hcoord := cell.abs_coord_sub_le_one ha hb i
  rw [SimplexGrid.toStdSimplex_apply, SimplexGrid.toStdSimplex_apply]
  have hdiv :
      (a.1 i : ℝ) / (N : ℝ) - (b.1 i : ℝ) / (N : ℝ) =
        ((a.1 i : ℝ) - (b.1 i : ℝ)) / (N : ℝ) := by
    ring
  rw [hdiv, abs_div, abs_of_pos hNpos]
  exact div_le_div_of_nonneg_right hcoord hNpos.le

end GridSmallCell

/--
Grid vertices lying in one unit coordinate cube.

The lower corner is bounded by `N`; vertices are those grid points whose
coordinates are either `lower i` or `lower i + 1`. These cube slices are the
ambient finite pieces that the later Kuhn/Freudenthal triangulation subdivides.
-/
noncomputable def cubeSliceVertices {ι : Type u} [Fintype ι] (N : ℕ)
    (lower : ι → Fin (N + 1)) : Finset (SimplexGrid ι N) :=
  Finset.univ.filter fun a =>
    ∀ i : ι, a.1 i = (lower i : ℕ) ∨ a.1 i = (lower i : ℕ) + 1

@[simp] theorem mem_cubeSliceVertices_iff {ι : Type u} [Fintype ι]
    {N : ℕ} {lower : ι → Fin (N + 1)} {a : SimplexGrid ι N} :
    a ∈ cubeSliceVertices N lower ↔
      ∀ i : ι, a.1 i = (lower i : ℕ) ∨ a.1 i = (lower i : ℕ) + 1 := by
  simp [cubeSliceVertices]

/-- A nonempty unit-cube slice of the integer barycentric grid. -/
structure GridCubeSlice (ι : Type u) [Fintype ι] (N : ℕ) where
  lower : ι → Fin (N + 1)
  nonempty_vertices : (cubeSliceVertices N lower).Nonempty

namespace GridCubeSlice

variable {ι : Type u} [Fintype ι] {N : ℕ}

@[simp] theorem mem_vertices_iff (S : GridCubeSlice ι N) {a : SimplexGrid ι N} :
    a ∈ cubeSliceVertices N S.lower ↔
      ∀ i : ι, a.1 i = (S.lower i : ℕ) ∨ a.1 i = (S.lower i : ℕ) + 1 :=
  mem_cubeSliceVertices_iff

/-- The cube slice using a grid vertex itself as lower corner. -/
noncomputable def ofVertex (a : SimplexGrid ι N) : GridCubeSlice ι N where
  lower := SimplexGrid.toFinVector a
  nonempty_vertices := by
    refine ⟨a, ?_⟩
    rw [mem_cubeSliceVertices_iff]
    intro i
    exact Or.inl rfl

@[simp] theorem ofVertex_lower (a : SimplexGrid ι N) :
    (ofVertex a).lower = SimplexGrid.toFinVector a :=
  rfl

theorem mem_ofVertex_vertices (a : SimplexGrid ι N) :
    a ∈ cubeSliceVertices N (ofVertex a).lower := by
  rw [mem_cubeSliceVertices_iff]
  intro i
  exact Or.inl rfl

theorem lower_injective [DecidableEq ι] :
    Function.Injective (lower (ι := ι) (N := N)) := by
  intro S T h
  cases S
  cases T
  simp only at h
  subst h
  rfl

noncomputable instance instFintype [DecidableEq ι] :
    Fintype (GridCubeSlice ι N) := by
  classical
  exact Fintype.ofInjective (lower (ι := ι) (N := N)) lower_injective

/-- A cube slice is a small cell: any two vertices differ coordinatewise by at most one. -/
noncomputable def toSmallCell (S : GridCubeSlice ι N) : GridSmallCell ι N where
  vertices := cubeSliceVertices N S.lower
  nonempty := S.nonempty_vertices
  coordinate_span_le_one := by
    intro a ha b hb i
    have hai := (mem_cubeSliceVertices_iff.mp ha) i
    have hbi := (mem_cubeSliceVertices_iff.mp hb) i
    constructor <;> omega

@[simp] theorem toSmallCell_vertices (S : GridCubeSlice ι N) :
    S.toSmallCell.vertices = cubeSliceVertices N S.lower :=
  rfl

theorem mem_toSmallCell_vertices_iff (S : GridCubeSlice ι N) {a : SimplexGrid ι N} :
    a ∈ S.toSmallCell.vertices ↔
      ∀ i : ι, a.1 i = (S.lower i : ℕ) ∨ a.1 i = (S.lower i : ℕ) + 1 :=
  mem_cubeSliceVertices_iff

/-- Reindex a cube slice along an equivalence of coordinate types. -/
noncomputable def reindex {κ : Type v} [Fintype κ] (e : ι ≃ κ)
    (S : GridCubeSlice ι N) : GridCubeSlice κ N where
  lower := fun k => S.lower (e.symm k)
  nonempty_vertices := by
    rcases S.nonempty_vertices with ⟨a, ha⟩
    refine ⟨SimplexGrid.reindex e a, ?_⟩
    rw [mem_cubeSliceVertices_iff] at ha ⊢
    intro k
    simpa using ha (e.symm k)

theorem mem_reindex_vertices_iff {κ : Type v} [Fintype κ] (e : ι ≃ κ)
    (S : GridCubeSlice ι N) (a : SimplexGrid ι N) :
    SimplexGrid.reindex e a ∈ cubeSliceVertices N (S.reindex e).lower ↔
      a ∈ cubeSliceVertices N S.lower := by
  rw [mem_cubeSliceVertices_iff, mem_cubeSliceVertices_iff]
  constructor
  · intro h i
    simpa [GridCubeSlice.reindex] using h (e i)
  · intro h k
    simpa [GridCubeSlice.reindex] using h (e.symm k)

end GridCubeSlice

namespace FinTwoGrid

/-- The `k`th grid point on the one-dimensional simplex indexed by `Fin 2`. -/
def point (N : ℕ) (k : Fin (N + 1)) : SimplexGrid (Fin 2) N := by
  refine ⟨fun i => if i = 0 then (k : ℕ) else N - (k : ℕ), ?_⟩
  rw [Fin.sum_univ_two]
  simp [Nat.add_sub_of_le (Nat.le_of_lt_succ k.2)]

@[simp] theorem point_zero_apply (N : ℕ) (k : Fin (N + 1)) :
    (point N k).1 0 = (k : ℕ) := by
  simp [point]

@[simp] theorem point_one_apply (N : ℕ) (k : Fin (N + 1)) :
    (point N k).1 1 = N - (k : ℕ) := by
  simp [point]

/-- The same point, indexed by a natural number with an explicit bound. -/
def pointNat (N k : ℕ) (hk : k ≤ N) : SimplexGrid (Fin 2) N :=
  point N ⟨k, Nat.lt_succ_of_le hk⟩

@[simp] theorem pointNat_zero_apply (N k : ℕ) (hk : k ≤ N) :
    (pointNat N k hk).1 0 = k := by
  simp [pointNat]

@[simp] theorem pointNat_one_apply (N k : ℕ) (hk : k ≤ N) :
    (pointNat N k hk).1 1 = N - k := by
  simp [pointNat]

theorem pointNat_congr {N k l : ℕ} (hkl : k = l)
    (hk : k ≤ N) (hl : l ≤ N) :
    pointNat N k hk = pointNat N l hl := by
  subst hkl
  apply Subtype.ext
  funext i
  fin_cases i <;> simp

theorem left_endpoint_label
    (L : GridSpernerLabeling (Fin 2) N) (hN : 0 < N) :
    L.label (pointNat N 0 hN.le) = 1 := by
  have hne : L.label (pointNat N 0 hN.le) ≠ 0 :=
    L.label_ne_of_coord_eq_zero (pointNat N 0 hN.le) (i := 0) (by simp)
  exact Fin.eq_one_of_ne_zero (L.label (pointNat N 0 hN.le)) hne

theorem right_endpoint_label
    (L : GridSpernerLabeling (Fin 2) N) :
    L.label (pointNat N N le_rfl) = 0 := by
  have hne : L.label (pointNat N N le_rfl) ≠ 1 :=
    L.label_ne_of_coord_eq_zero (pointNat N N le_rfl) (i := 1) (by simp)
  by_contra hzero
  exact hne (Fin.eq_one_of_ne_zero (L.label (pointNat N N le_rfl)) hzero)

theorem exists_adjacent_label_transition
    (L : GridSpernerLabeling (Fin 2) N) (hN : 0 < N) :
    ∃ p, ∃ hp : p < N,
      L.label (pointNat N p hp.le) = 1 ∧
        L.label (pointNat N (p + 1) (Nat.succ_le_of_lt hp)) = 0 := by
  classical
  let P : ℕ → Prop := fun k =>
    ∃ hk : k ≤ N, L.label (pointNat N k hk) = 0
  have hP : ∃ k, P k := ⟨N, le_rfl, right_endpoint_label L⟩
  let k := Nat.find hP
  have hkP : P k := Nat.find_spec hP
  rcases hkP with ⟨hkN, hkLabel⟩
  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    have hpoint :
        pointNat N k hkN = pointNat N 0 hN.le :=
      pointNat_congr hk0 hkN hN.le
    have hkLabel0 : L.label (pointNat N 0 hN.le) = 0 := by
      simpa [hpoint] using hkLabel
    have hleft := left_endpoint_label L hN
    norm_num [hleft] at hkLabel0
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk_ne_zero
  let p := k - 1
  have hp_lt_k : p < k := by
    dsimp [p]
    omega
  have hp_le_N : p ≤ N := (Nat.pred_le k).trans hkN
  have hp_notP : ¬ P p := Nat.find_min hP hp_lt_k
  have hpLabel_ne_zero : L.label (pointNat N p hp_le_N) ≠ 0 := by
    intro hpLabel
    exact hp_notP ⟨hp_le_N, hpLabel⟩
  have hpLabel_one : L.label (pointNat N p hp_le_N) = 1 :=
    Fin.eq_one_of_ne_zero _ hpLabel_ne_zero
  have hp_lt_N : p < N := by
    omega
  refine ⟨p, hp_lt_N, ?_, ?_⟩
  · have hpoint :
        pointNat N p hp_le_N = pointNat N p hp_lt_N.le :=
      pointNat_congr rfl hp_le_N hp_lt_N.le
    simpa [hpoint] using hpLabel_one
  · have hp_succ_eq : p + 1 = k := by
      omega
    have hpoint :
        pointNat N (p + 1) (Nat.succ_le_of_lt hp_lt_N) = pointNat N k hkN :=
      pointNat_congr hp_succ_eq (Nat.succ_le_of_lt hp_lt_N) hkN
    simpa [hpoint] using hkLabel

end FinTwoGrid

/--
A triangulation-level package for the integer barycentric grid.

The concrete Kuhn/Freudenthal construction will provide the `cells`; the
separate `HasSpernerProperty` predicate records the combinatorial theorem
that every Sperner labeling has a fully labeled cell.
-/
structure GridTriangulation (ι : Type u) [Fintype ι] (N : ℕ) where
  cells : Finset (GridSmallCell ι N)

namespace GridTriangulation

variable {ι : Type u} [Fintype ι] {N : ℕ}

/-- The Sperner conclusion for a chosen grid triangulation. -/
def HasSpernerProperty [DecidableEq ι] (T : GridTriangulation ι N) : Prop :=
  ∀ L : GridSpernerLabeling ι N,
    ∃ cell ∈ T.cells, cell.FullyLabeled L

/-- The cubical Sperner theorem for the integer simplex grid at mesh `N`. -/
def CubicalSpernerProperty [DecidableEq ι] (N : ℕ) : Prop :=
  ∀ L : GridSpernerLabeling ι N,
    ∃ S : GridCubeSlice ι N, S.toSmallCell.FullyLabeled L

/-- The cubical Sperner theorem uniformly over every positive mesh. -/
def CubicalSpernerPropertyAllMeshes [DecidableEq ι] : Prop :=
  ∀ N : ℕ, 0 < N → CubicalSpernerProperty (ι := ι) N

/--
The finite subdivision whose cells are all nonempty unit-cube slices.

The later Kuhn/Freudenthal triangulation will refine these cube slices into
simplices; this object is already enough for the compactness side of KKM once
the corresponding cubical Sperner statement is proved.
-/
noncomputable def cubeSlices [DecidableEq ι] : GridTriangulation ι N := by
  classical
  exact
    { cells := (Finset.univ : Finset (GridCubeSlice ι N)).image GridCubeSlice.toSmallCell }

theorem cubeSlice_toSmallCell_mem [DecidableEq ι] (S : GridCubeSlice ι N) :
    S.toSmallCell ∈ (cubeSlices (ι := ι) (N := N)).cells := by
  classical
  simp [cubeSlices]

theorem mem_cubeSlices_iff [DecidableEq ι] {cell : GridSmallCell ι N} :
    cell ∈ (cubeSlices (ι := ι) (N := N)).cells ↔
      ∃ S : GridCubeSlice ι N, S.toSmallCell = cell := by
  classical
  simp [cubeSlices]

/-- The concrete cubical Sperner target for the all-cube-slices subdivision. -/
theorem cubeSlices_hasSpernerProperty_iff [DecidableEq ι] :
    (cubeSlices (ι := ι) (N := N)).HasSpernerProperty ↔
      CubicalSpernerProperty (ι := ι) N := by
  classical
  constructor
  · intro h L
    rcases h L with ⟨cell, hcell, hfull⟩
    rcases (mem_cubeSlices_iff.mp hcell) with ⟨S, hS⟩
    refine ⟨S, ?_⟩
    simpa [hS] using hfull
  · intro h L
    rcases h L with ⟨S, hfull⟩
    exact ⟨S.toSmallCell, cubeSlice_toSmallCell_mem S, hfull⟩

/-- The zero-dimensional/nonempty subsingleton case of cubical Sperner. -/
theorem cubicalSpernerProperty_subsingleton [DecidableEq ι]
    [Nonempty ι] [Subsingleton ι] :
    CubicalSpernerProperty (ι := ι) N := by
  classical
  intro L
  let i₀ : ι := Classical.arbitrary ι
  let a : SimplexGrid ι N :=
    ⟨fun _ => N, by
      haveI : Unique ι := ⟨⟨i₀⟩, fun x => Subsingleton.elim x i₀⟩
      simp⟩
  refine ⟨GridCubeSlice.ofVertex a, ?_⟩
  rw [GridSmallCell.fullyLabeled_iff]
  intro i
  refine ⟨a, ?_, Subsingleton.elim (L.label a) i⟩
  exact GridCubeSlice.mem_ofVertex_vertices a

/-- The zero-dimensional/nonempty subsingleton case at every positive mesh. -/
theorem cubicalSpernerPropertyAllMeshes_subsingleton [DecidableEq ι]
    [Nonempty ι] [Subsingleton ι] :
    CubicalSpernerPropertyAllMeshes (ι := ι) := by
  intro N _hN
  exact cubicalSpernerProperty_subsingleton (ι := ι) (N := N)

/-- The one-dimensional cubical Sperner theorem. -/
theorem cubicalSpernerProperty_fin_two (hN : 0 < N) :
    CubicalSpernerProperty (ι := Fin 2) N := by
  intro L
  rcases FinTwoGrid.exists_adjacent_label_transition L hN with
    ⟨p, hp, hpLabel, hnextLabel⟩
  let lower : Fin 2 → Fin (N + 1) := fun i =>
    if i = 0 then ⟨p, Nat.lt_succ_of_le hp.le⟩
    else ⟨N - (p + 1), Nat.lt_succ_of_le (Nat.sub_le N (p + 1))⟩
  have hprev_mem :
      FinTwoGrid.pointNat N p hp.le ∈ cubeSliceVertices N lower := by
    rw [mem_cubeSliceVertices_iff]
    intro i
    fin_cases i
    · exact Or.inl (by simp [lower])
    · exact Or.inr (by simp [lower]; omega)
  have hnext_mem :
      FinTwoGrid.pointNat N (p + 1) (Nat.succ_le_of_lt hp) ∈
        cubeSliceVertices N lower := by
    rw [mem_cubeSliceVertices_iff]
    intro i
    fin_cases i
    · exact Or.inr (by simp [lower])
    · exact Or.inl (by simp [lower])
  let S : GridCubeSlice (Fin 2) N :=
    { lower := lower
      nonempty_vertices := ⟨FinTwoGrid.pointNat N p hp.le, hprev_mem⟩ }
  refine ⟨S, ?_⟩
  rw [GridSmallCell.fullyLabeled_iff]
  intro i
  fin_cases i
  · exact ⟨FinTwoGrid.pointNat N (p + 1) (Nat.succ_le_of_lt hp),
      by simpa [S, GridCubeSlice.toSmallCell] using hnext_mem, hnextLabel⟩
  · exact ⟨FinTwoGrid.pointNat N p hp.le,
      by simpa [S, GridCubeSlice.toSmallCell] using hprev_mem, hpLabel⟩

/-- The one-dimensional cubical Sperner theorem at every positive mesh. -/
theorem cubicalSpernerPropertyAllMeshes_fin_two :
    CubicalSpernerPropertyAllMeshes (ι := Fin 2) := by
  intro N hN
  exact cubicalSpernerProperty_fin_two (N := N) hN

/-- Cubical Sperner transfers across an equivalence of finite coordinate types. -/
theorem cubicalSpernerProperty_congr {κ : Type v} [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ)
    (hκ : CubicalSpernerProperty (ι := κ) N) :
    CubicalSpernerProperty (ι := ι) N := by
  intro L
  rcases hκ (L.reindex e) with ⟨Sκ, hfullκ⟩
  refine ⟨Sκ.reindex e.symm, ?_⟩
  rw [GridSmallCell.fullyLabeled_iff] at hfullκ ⊢
  intro i
  rcases hfullκ (e i) with ⟨b, hb, hlabel⟩
  refine ⟨SimplexGrid.reindex e.symm b, ?_, ?_⟩
  · have hb' : b ∈ cubeSliceVertices N Sκ.lower := by
      simpa [GridCubeSlice.toSmallCell] using hb
    rw [GridCubeSlice.toSmallCell_vertices, mem_cubeSliceVertices_iff]
    intro j
    have hj := (mem_cubeSliceVertices_iff.mp hb') (e j)
    simpa [GridCubeSlice.reindex] using hj
  · apply e.injective
    simpa [GridSpernerLabeling.reindex]
      using hlabel

/-- The all-mesh cubical Sperner theorem is invariant under reindexing. -/
theorem cubicalSpernerPropertyAllMeshes_congr {κ : Type v} [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ)
    (hκ : CubicalSpernerPropertyAllMeshes (ι := κ)) :
    CubicalSpernerPropertyAllMeshes (ι := ι) := by
  intro N hN
  exact cubicalSpernerProperty_congr (ι := ι) (κ := κ) (N := N) e (hκ N hN)

/--
It is enough to prove cubical Sperner for the canonical finite coordinate type
`Fin (Fintype.card ι)`.
-/
theorem cubicalSpernerPropertyAllMeshes_of_fin_card [DecidableEq ι]
    (hfin : CubicalSpernerPropertyAllMeshes (ι := Fin (Fintype.card ι))) :
    CubicalSpernerPropertyAllMeshes (ι := ι) := by
  exact cubicalSpernerPropertyAllMeshes_congr
    (ι := ι) (κ := Fin (Fintype.card ι)) (Fintype.equivFin ι) hfin

/-- At mesh one, the whole simplex is one cube slice containing all vertices. -/
theorem cubicalSpernerProperty_mesh_one [DecidableEq ι] [Nonempty ι] :
    CubicalSpernerProperty (ι := ι) 1 := by
  classical
  intro L
  let lower : ι → Fin 2 := fun _ => ⟨0, by norm_num⟩
  have hnonempty : (cubeSliceVertices 1 lower).Nonempty := by
    let i₀ : ι := Classical.arbitrary ι
    refine ⟨SimplexGrid.unitVertex i₀, ?_⟩
    rw [mem_cubeSliceVertices_iff]
    intro j
    rcases SimplexGrid.unitVertex_apply_eq_one_or_zero i₀ j with hcoord | hcoord
    · exact Or.inr (by simp [lower, hcoord])
    · exact Or.inl (by simp [lower, hcoord])
  let S : GridCubeSlice ι 1 :=
    { lower := lower
      nonempty_vertices := hnonempty }
  refine ⟨S, ?_⟩
  rw [GridSmallCell.fullyLabeled_iff]
  intro i
  refine ⟨SimplexGrid.unitVertex i, ?_, L.label_unitVertex i⟩
  rw [GridCubeSlice.toSmallCell_vertices, mem_cubeSliceVertices_iff]
  intro j
  rcases SimplexGrid.unitVertex_apply_eq_one_or_zero i j with hcoord | hcoord
  · exact Or.inr (by simp [S, lower, hcoord])
  · exact Or.inl (by simp [S, lower, hcoord])

end GridTriangulation

/--
A grid labeling chosen from a KKM cover. Besides satisfying Sperner's boundary
condition, every grid point lies in the cover set indexed by its label.
-/
structure KKMGridLabeling (ι : Type u) [Fintype ι] (N : ℕ)
    (C : ι → Set (stdSimplex ℝ ι)) (hN : 0 < N) where
  label : GridSpernerLabeling ι N
  label_mem_cover :
    ∀ a, SimplexGrid.toStdSimplex hN a ∈ C (label.label a)

namespace KKMGridLabeling

variable {ι : Type u} [Fintype ι] {N : ℕ}

/--
Every KKM cover induces a Sperner-compatible labeling on every positive
integer barycentric grid.
-/
noncomputable def ofKKMCondition {C : ι → Set (stdSimplex ℝ ι)}
    (hC : StdSimplexKKMCondition C) (hN : 0 < N) :
    KKMGridLabeling ι N C hN where
  label :=
    { label := fun a => Classical.choose
        (SimplexGrid.exists_label_mem_support_and_cover hC hN a)
      label_mem_support := by
        intro a
        exact (Classical.choose_spec
          (SimplexGrid.exists_label_mem_support_and_cover hC hN a)).1 }
  label_mem_cover := by
    intro a
    exact (Classical.choose_spec
      (SimplexGrid.exists_label_mem_support_and_cover hC hN a)).2

theorem exists_grid_point_mem_cover_of_fullyLabeledOn [DecidableEq ι]
    {C : ι → Set (stdSimplex ℝ ι)} {hN : 0 < N}
    (L : KKMGridLabeling ι N C hN) {cell : Finset (SimplexGrid ι N)}
    (hfull : L.label.FullyLabeledOn cell) :
    ∀ i : ι, ∃ a ∈ cell, SimplexGrid.toStdSimplex hN a ∈ C i := by
  intro i
  rcases (GridSpernerLabeling.fullyLabeledOn_iff L.label cell).mp hfull i with
    ⟨a, ha, hlabel⟩
  refine ⟨a, ha, ?_⟩
  simpa [hlabel] using L.label_mem_cover a

theorem exists_grid_point_mem_cover_of_fullyLabeledCell [DecidableEq ι]
    {C : ι → Set (stdSimplex ℝ ι)} {hN : 0 < N}
    (L : KKMGridLabeling ι N C hN) {cell : GridSmallCell ι N}
    (hfull : cell.FullyLabeled L.label) :
    ∀ i : ι, ∃ a ∈ cell.vertices, SimplexGrid.toStdSimplex hN a ∈ C i :=
  L.exists_grid_point_mem_cover_of_fullyLabeledOn hfull

theorem exists_clustered_cover_witnesses_of_fullyLabeledCell [DecidableEq ι]
    {C : ι → Set (stdSimplex ℝ ι)} {hN : 0 < N}
    (L : KKMGridLabeling ι N C hN) {cell : GridSmallCell ι N}
    (hfull : cell.FullyLabeled L.label) :
    ∃ anchor ∈ cell.vertices,
      ∀ i : ι, ∃ a ∈ cell.vertices,
        SimplexGrid.toStdSimplex hN a ∈ C i ∧
          ∀ j : ι,
            |SimplexGrid.toStdSimplex hN a j -
              SimplexGrid.toStdSimplex hN anchor j| ≤ (1 : ℝ) / (N : ℝ) := by
  rcases cell.exists_vertex with ⟨anchor, hanchor⟩
  refine ⟨anchor, hanchor, ?_⟩
  intro i
  rcases L.exists_grid_point_mem_cover_of_fullyLabeledCell hfull i with
    ⟨a, ha, haC⟩
  exact ⟨a, ha, haC, fun j =>
    cell.toStdSimplex_coord_abs_sub_le hN ha hanchor j⟩

end KKMGridLabeling

namespace GridTriangulation

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {N : ℕ}

/--
A packaged mesh-level KKM witness.

For a positive mesh, this records one cube-slice cell, one anchor grid point,
and for every cover label a grid point in the same cell whose image lies in
the corresponding closed set. The final field is the mesh-diameter estimate
that drives the later compactness argument.
-/
structure MeshClusteredCoverWitnesses
    (C : ι → Set (stdSimplex ℝ ι)) (hN : 0 < N) where
  cell : GridSmallCell ι N
  cell_mem_cubeSlices : cell ∈ (cubeSlices (ι := ι) (N := N)).cells
  anchor : SimplexGrid ι N
  anchor_mem_cell : anchor ∈ cell.vertices
  witness : ι → SimplexGrid ι N
  witness_mem_cell : ∀ i, witness i ∈ cell.vertices
  witness_mem_cover : ∀ i, SimplexGrid.toStdSimplex hN (witness i) ∈ C i
  witness_close :
    ∀ i j,
      |SimplexGrid.toStdSimplex hN (witness i) j -
        SimplexGrid.toStdSimplex hN anchor j| ≤ (1 : ℝ) / (N : ℝ)

/--
If a grid triangulation satisfies Sperner's lemma, then every KKM cover has
one small cell containing cover witnesses for every label.

This is the finite combinatorial-to-analytic bridge used in the KKM proof:
the mesh diameter estimate is supplied by `GridSmallCell`.
-/
theorem exists_clustered_cover_witnesses_of_kkm
    {C : ι → Set (stdSimplex ℝ ι)} {hN : 0 < N}
    (T : GridTriangulation ι N) (hT : T.HasSpernerProperty)
    (hC : StdSimplexKKMCondition C) :
    ∃ cell ∈ T.cells, ∃ anchor ∈ cell.vertices,
      ∀ i : ι, ∃ a ∈ cell.vertices,
        SimplexGrid.toStdSimplex hN a ∈ C i ∧
          ∀ j : ι,
            |SimplexGrid.toStdSimplex hN a j -
              SimplexGrid.toStdSimplex hN anchor j| ≤ (1 : ℝ) / (N : ℝ) := by
  let L : KKMGridLabeling ι N C hN := KKMGridLabeling.ofKKMCondition hC hN
  rcases hT L.label with ⟨cell, hcellT, hfull⟩
  rcases L.exists_clustered_cover_witnesses_of_fullyLabeledCell hfull with
    ⟨anchor, hanchor, hwitness⟩
  exact ⟨cell, hcellT, anchor, hanchor, hwitness⟩

/--
Cube-slice version of the KKM bridge.

This packages the remaining finite combinatorial obligation as the cubical
Sperner statement on `GridCubeSlice`s.
-/
theorem cubeSlices_exists_clustered_cover_witnesses_of_kkm
    {C : ι → Set (stdSimplex ℝ ι)} {hN : 0 < N}
    (hCubicalSperner :
      ∀ L : GridSpernerLabeling ι N,
        ∃ S : GridCubeSlice ι N, S.toSmallCell.FullyLabeled L)
    (hC : StdSimplexKKMCondition C) :
    ∃ cell ∈ (cubeSlices (ι := ι) (N := N)).cells, ∃ anchor ∈ cell.vertices,
      ∀ i : ι, ∃ a ∈ cell.vertices,
        SimplexGrid.toStdSimplex hN a ∈ C i ∧
          ∀ j : ι,
            |SimplexGrid.toStdSimplex hN a j -
              SimplexGrid.toStdSimplex hN anchor j| ≤ (1 : ℝ) / (N : ℝ) := by
  exact exists_clustered_cover_witnesses_of_kkm
    (T := cubeSlices (ι := ι) (N := N))
    ((cubeSlices_hasSpernerProperty_iff (ι := ι) (N := N)).mpr hCubicalSperner)
    hC

/--
Packaged cube-slice version of the KKM bridge.

This is the API most later compactness proofs should use: it exposes named
fields for the anchor, witnesses, cover-membership facts, and mesh-diameter
bound instead of a tower of nested existentials.
-/
noncomputable def cubeSlices_meshClusteredCoverWitnesses_of_kkm
    {C : ι → Set (stdSimplex ℝ ι)} {hN : 0 < N}
    (hCubicalSperner : CubicalSpernerProperty (ι := ι) N)
    (hC : StdSimplexKKMCondition C) :
    MeshClusteredCoverWitnesses (ι := ι) (N := N) C hN := by
  classical
  let hExists := cubeSlices_exists_clustered_cover_witnesses_of_kkm
      (ι := ι) (N := N) (C := C) (hN := hN) hCubicalSperner hC
  let cell : GridSmallCell ι N := Classical.choose hExists
  have hcell :
      cell ∈ (cubeSlices (ι := ι) (N := N)).cells ∧
        ∃ anchor ∈ cell.vertices,
          ∀ i : ι, ∃ a ∈ cell.vertices,
            SimplexGrid.toStdSimplex hN a ∈ C i ∧
              ∀ j : ι,
                |SimplexGrid.toStdSimplex hN a j -
                  SimplexGrid.toStdSimplex hN anchor j| ≤ (1 : ℝ) / (N : ℝ) :=
    Classical.choose_spec hExists
  let anchor : SimplexGrid ι N := Classical.choose hcell.2
  have hanchor :
      anchor ∈ cell.vertices ∧
        ∀ i : ι, ∃ a ∈ cell.vertices,
          SimplexGrid.toStdSimplex hN a ∈ C i ∧
            ∀ j : ι,
              |SimplexGrid.toStdSimplex hN a j -
                SimplexGrid.toStdSimplex hN anchor j| ≤ (1 : ℝ) / (N : ℝ) :=
    Classical.choose_spec hcell.2
  exact
    { cell := cell
      cell_mem_cubeSlices := hcell.1
      anchor := anchor
      anchor_mem_cell := hanchor.1
      witness := fun i => Classical.choose (hanchor.2 i)
      witness_mem_cell := fun i => (Classical.choose_spec (hanchor.2 i)).1
      witness_mem_cover := fun i => (Classical.choose_spec (hanchor.2 i)).2.1
      witness_close := fun i => (Classical.choose_spec (hanchor.2 i)).2.2 }

/--
Every all-mesh cubical Sperner theorem supplies clustered KKM witnesses at
any requested positive mesh.
-/
noncomputable def cubeSlices_meshClusteredCoverWitnesses_of_allMeshes
    {C : ι → Set (stdSimplex ℝ ι)} {hN : 0 < N}
    (hCubicalSperner : CubicalSpernerPropertyAllMeshes (ι := ι))
    (hC : StdSimplexKKMCondition C) :
    MeshClusteredCoverWitnesses (ι := ι) (N := N) C hN :=
  cubeSlices_meshClusteredCoverWitnesses_of_kkm
    (ι := ι) (N := N) (C := C) (hN := hN)
    (hCubicalSperner N hN) hC

/--
All positive-mesh cubical Sperner implies the closed KKM intersection
property on the standard simplex.

The proof chooses clustered witnesses on meshes `n + 1`, takes a convergent
subsequence of the anchor points by compactness of the simplex, and uses the
`1 / (n + 1)` mesh-diameter bound to show that each cover-witness subsequence
converges to the same limit point. Closedness then puts the limit in every
member of the KKM cover.
-/
theorem stdSimplexKKMProperty_of_cubicalSpernerPropertyAllMeshes
    (hCubicalSperner : CubicalSpernerPropertyAllMeshes (ι := ι)) :
    StdSimplexKKMProperty ι := by
  classical
  intro C hclosed hcond
  let W : (n : ℕ) →
      MeshClusteredCoverWitnesses (ι := ι) (N := n.succ) C (Nat.succ_pos n) :=
    fun n =>
      cubeSlices_meshClusteredCoverWitnesses_of_allMeshes
        (ι := ι) (N := n.succ) (C := C) (hN := Nat.succ_pos n)
        hCubicalSperner hcond
  let anchorSeq : ℕ → stdSimplex ℝ ι := fun n =>
    SimplexGrid.toStdSimplex (Nat.succ_pos n) (W n).anchor
  let witnessSeq : ι → ℕ → stdSimplex ℝ ι := fun i n =>
    SimplexGrid.toStdSimplex (Nat.succ_pos n) ((W n).witness i)
  rcases CompactSpace.tendsto_subseq anchorSeq with ⟨x, φ, hφmono, hanchor⟩
  refine ⟨x, ?_⟩
  intro i
  have hwitness_tendsto :
      Filter.Tendsto (fun n => witnessSeq i (φ n)) Filter.atTop (nhds x) := by
    have hwitness_ambient :
        Filter.Tendsto (fun n => (witnessSeq i (φ n) : ι → ℝ)) Filter.atTop
          (nhds (x : ι → ℝ)) := by
      rw [tendsto_pi_nhds]
      intro j
      have hanchor_coord :
          Filter.Tendsto (fun n => anchorSeq (φ n) j) Filter.atTop (nhds (x j)) := by
        have hcoord_cont : Continuous fun y : stdSimplex ℝ ι => y j :=
          (continuous_apply j).comp continuous_subtype_val
        exact hcoord_cont.tendsto x |>.comp hanchor
      have hdist_zero :
          Filter.Tendsto
            (fun n => dist (anchorSeq (φ n) j) (witnessSeq i (φ n) j))
            Filter.atTop (nhds 0) := by
        refine squeeze_zero
          (g := fun n => (1 : ℝ) / ((φ n).succ : ℝ))
          (fun n => dist_nonneg) ?_ ?_
        · intro n
          have hclose := (W (φ n)).witness_close i j
          simpa [anchorSeq, witnessSeq, Real.dist_eq, abs_sub_comm] using hclose
        · have hmesh_tendsto :
              Filter.Tendsto (fun n => (1 : ℝ) / ((φ n).succ : ℝ)) Filter.atTop
                (nhds 0) := by
            have hbase :=
              (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
                hφmono.tendsto_atTop
            simpa [Nat.cast_succ] using hbase
          exact hmesh_tendsto
      exact hanchor_coord.congr_dist hdist_zero
    exact tendsto_subtype_rng.mpr hwitness_ambient
  exact (hclosed i).mem_of_tendsto hwitness_tendsto
    (Filter.Eventually.of_forall fun n => by
      simpa [witnessSeq] using (W (φ n)).witness_mem_cover i)

/--
All positive-mesh cubical Sperner implies Brouwer's fixed-point property on
the standard simplex, via the closed KKM theorem.
-/
theorem brouwerFixedPointProperty_stdSimplex_of_cubicalSpernerPropertyAllMeshes
    (hCubicalSperner : CubicalSpernerPropertyAllMeshes (ι := ι)) :
    BrouwerFixedPointProperty (stdSimplex ℝ ι) :=
  brouwerFixedPointProperty_stdSimplex_of_kkm
    (stdSimplexKKMProperty_of_cubicalSpernerPropertyAllMeshes
      (ι := ι) hCubicalSperner)

end GridTriangulation

end Correspondence

end EcoLean.GameTheory
