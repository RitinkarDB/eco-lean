import EcoLean.GameTheory.MathLanguage.SetsFunctionsCorrespondences
import Mathlib.Data.Fintype.Pi

namespace EcoLean.GameTheory

namespace Correspondence

universe u

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

end GridTriangulation

end Correspondence

end EcoLean.GameTheory
