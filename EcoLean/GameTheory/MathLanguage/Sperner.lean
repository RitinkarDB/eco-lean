import EcoLean.GameTheory.MathLanguage.SetsFunctionsCorrespondences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Fin
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.Nat.ModEq
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

/--
A finite family of grid vertices contains every label except possibly
`missing`.

This is the label pattern counted by the usual Sperner pivot/parity proof.
It intentionally does not assert that `missing` is absent: fully labeled cells
also satisfy this predicate.
-/
def AlmostFullyLabeledOn [DecidableEq ι] (L : GridSpernerLabeling ι N)
    (cell : Finset (SimplexGrid ι N)) (missing : ι) : Prop :=
  ∀ i : ι, i ≠ missing → i ∈ L.labelsOn cell

theorem almostFullyLabeledOn_iff [DecidableEq ι]
    (L : GridSpernerLabeling ι N) (cell : Finset (SimplexGrid ι N))
    (missing : ι) :
    L.AlmostFullyLabeledOn cell missing ↔
      ∀ i : ι, i ≠ missing → ∃ a ∈ cell, L.label a = i := by
  simp [AlmostFullyLabeledOn]

theorem not_almostFullyLabeledOn_empty [DecidableEq ι] [Nontrivial ι]
    (L : GridSpernerLabeling ι N) (missing : ι) :
    ¬ L.AlmostFullyLabeledOn ∅ missing := by
  intro halmost
  rcases exists_ne missing with ⟨i, hi⟩
  have hi_labels : i ∈ L.labelsOn ∅ := halmost i hi
  simp [labelsOn] at hi_labels

theorem FullyLabeledOn.almostFullyLabeledOn [DecidableEq ι]
    {L : GridSpernerLabeling ι N} {cell : Finset (SimplexGrid ι N)}
    (hfull : L.FullyLabeledOn cell) (missing : ι) :
    L.AlmostFullyLabeledOn cell missing := by
  intro i _hi
  exact hfull i

theorem fullyLabeledOn_iff_almostFullyLabeledOn_and_missing [DecidableEq ι]
    (L : GridSpernerLabeling ι N) (cell : Finset (SimplexGrid ι N))
    (missing : ι) :
    L.FullyLabeledOn cell ↔
      L.AlmostFullyLabeledOn cell missing ∧ missing ∈ L.labelsOn cell := by
  constructor
  · intro hfull
    exact ⟨hfull.almostFullyLabeledOn missing, hfull missing⟩
  · intro h i
    by_cases hi : i = missing
    · simpa [hi] using h.2
    · exact h.1 i hi

theorem AlmostFullyLabeledOn.fullyLabeledOn_of_missing_mem [DecidableEq ι]
    {L : GridSpernerLabeling ι N} {cell : Finset (SimplexGrid ι N)}
    {missing : ι} (halmost : L.AlmostFullyLabeledOn cell missing)
    (hmissing : missing ∈ L.labelsOn cell) :
    L.FullyLabeledOn cell :=
  (fullyLabeledOn_iff_almostFullyLabeledOn_and_missing
    L cell missing).mpr ⟨halmost, hmissing⟩

theorem AlmostFullyLabeledOn.fullyLabeledOn_or_missing_notMem [DecidableEq ι]
    {L : GridSpernerLabeling ι N} {cell : Finset (SimplexGrid ι N)}
    {missing : ι} (halmost : L.AlmostFullyLabeledOn cell missing) :
    L.FullyLabeledOn cell ∨ missing ∉ L.labelsOn cell := by
  by_cases hmissing : missing ∈ L.labelsOn cell
  · exact Or.inl (halmost.fullyLabeledOn_of_missing_mem hmissing)
  · exact Or.inr hmissing

theorem label_ne_of_coord_eq_zero (L : GridSpernerLabeling ι N)
    (a : SimplexGrid ι N) {i : ι} (hi : a.1 i = 0) :
    L.label a ≠ i := by
  intro hlabel
  have hnonzero : a.1 (L.label a) ≠ 0 :=
    SimplexGrid.mem_support_iff.mp (L.label_mem_support a)
  exact hnonzero (by simpa [hlabel] using hi)

theorem label_notMem_labelsOn_of_coord_eq_zero [DecidableEq ι]
    (L : GridSpernerLabeling ι N) (cell : Finset (SimplexGrid ι N)) {i : ι}
    (hzero : ∀ a ∈ cell, a.1 i = 0) :
    i ∉ L.labelsOn cell := by
  rw [mem_labelsOn_iff]
  rintro ⟨a, ha, hlabel⟩
  exact L.label_ne_of_coord_eq_zero a (hzero a ha) hlabel

theorem not_fullyLabeledOn_of_coord_eq_zero [DecidableEq ι]
    (L : GridSpernerLabeling ι N) (cell : Finset (SimplexGrid ι N)) {i : ι}
    (hzero : ∀ a ∈ cell, a.1 i = 0) :
    ¬ L.FullyLabeledOn cell := by
  intro hfull
  exact L.label_notMem_labelsOn_of_coord_eq_zero cell hzero (hfull i)

theorem labelsOn_eq_univ_of_fullyLabeledOn [DecidableEq ι]
    (L : GridSpernerLabeling ι N) {cell : Finset (SimplexGrid ι N)}
    (hfull : L.FullyLabeledOn cell) :
    L.labelsOn cell = Finset.univ := by
  ext i
  constructor
  · intro _hi
    exact Finset.mem_univ i
  · intro _hi
    exact hfull i

theorem labelsOn_card_eq_univ_of_fullyLabeledOn [DecidableEq ι]
    (L : GridSpernerLabeling ι N) {cell : Finset (SimplexGrid ι N)}
    (hfull : L.FullyLabeledOn cell) :
    (L.labelsOn cell).card = Fintype.card ι := by
  rw [L.labelsOn_eq_univ_of_fullyLabeledOn hfull, Finset.card_univ]

theorem injOn_label_of_fullyLabeledOn_card_eq [DecidableEq ι]
    (L : GridSpernerLabeling ι N) {cell : Finset (SimplexGrid ι N)}
    (hfull : L.FullyLabeledOn cell) (hcard : cell.card = Fintype.card ι) :
    Set.InjOn L.label cell := by
  classical
  rw [← Finset.card_image_iff]
  rw [← labelsOn, L.labelsOn_card_eq_univ_of_fullyLabeledOn hfull, hcard]

theorem eq_of_mem_of_label_eq_of_fullyLabeledOn_card_eq [DecidableEq ι]
    (L : GridSpernerLabeling ι N) {cell : Finset (SimplexGrid ι N)}
    (hfull : L.FullyLabeledOn cell) (hcard : cell.card = Fintype.card ι)
    {a b : SimplexGrid ι N} (ha : a ∈ cell) (hb : b ∈ cell)
    (hlabel : L.label a = L.label b) :
    a = b :=
  L.injOn_label_of_fullyLabeledOn_card_eq hfull hcard ha hb hlabel

theorem labelsOn_eq_univ_erase_of_almostFullyLabeledOn_notMem
    [DecidableEq ι]
    (L : GridSpernerLabeling ι N) {cell : Finset (SimplexGrid ι N)}
    {missing : ι} (halmost : L.AlmostFullyLabeledOn cell missing)
    (hmissing : missing ∉ L.labelsOn cell) :
    L.labelsOn cell = Finset.univ.erase missing := by
  ext i
  constructor
  · intro hi
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ i⟩
    intro himissing
    exact hmissing (by simpa [himissing] using hi)
  · intro hi
    exact halmost i (Finset.mem_erase.mp hi).1

theorem labelsOn_card_eq_univ_erase_of_almostFullyLabeledOn_notMem
    [DecidableEq ι]
    (L : GridSpernerLabeling ι N) {cell : Finset (SimplexGrid ι N)}
    {missing : ι} (halmost : L.AlmostFullyLabeledOn cell missing)
    (hmissing : missing ∉ L.labelsOn cell) :
    (L.labelsOn cell).card = Fintype.card ι - 1 := by
  rw [L.labelsOn_eq_univ_erase_of_almostFullyLabeledOn_notMem halmost hmissing,
    Finset.card_erase_of_mem (Finset.mem_univ missing), Finset.card_univ]

theorem injOn_label_of_almostFullyLabeledOn_notMem_card_eq
    [DecidableEq ι]
    (L : GridSpernerLabeling ι N) {cell : Finset (SimplexGrid ι N)}
    {missing : ι} (halmost : L.AlmostFullyLabeledOn cell missing)
    (hmissing : missing ∉ L.labelsOn cell)
    (hcard : cell.card = Fintype.card ι - 1) :
    Set.InjOn L.label cell := by
  classical
  rw [← Finset.card_image_iff]
  rw [← labelsOn,
    L.labelsOn_card_eq_univ_erase_of_almostFullyLabeledOn_notMem
      halmost hmissing,
    hcard]

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

@[ext] theorem ext {cell cell' : GridSmallCell ι N}
    (hvertices : cell.vertices = cell'.vertices) :
    cell = cell' := by
  cases cell
  cases cell'
  cases hvertices
  congr

/-- A small cell is fully labeled when its vertices see every label. -/
def FullyLabeled [DecidableEq ι] (cell : GridSmallCell ι N)
    (L : GridSpernerLabeling ι N) : Prop :=
  L.FullyLabeledOn cell.vertices

theorem fullyLabeled_iff [DecidableEq ι] (cell : GridSmallCell ι N)
    (L : GridSpernerLabeling ι N) :
    cell.FullyLabeled L ↔ ∀ i : ι, ∃ a ∈ cell.vertices, L.label a = i := by
  exact GridSpernerLabeling.fullyLabeledOn_iff L cell.vertices

/-- A small cell contains every label except possibly `missing`. -/
def AlmostFullyLabeled [DecidableEq ι] (cell : GridSmallCell ι N)
    (L : GridSpernerLabeling ι N) (missing : ι) : Prop :=
  L.AlmostFullyLabeledOn cell.vertices missing

theorem almostFullyLabeled_iff [DecidableEq ι] (cell : GridSmallCell ι N)
    (L : GridSpernerLabeling ι N) (missing : ι) :
    cell.AlmostFullyLabeled L missing ↔
      ∀ i : ι, i ≠ missing → ∃ a ∈ cell.vertices, L.label a = i := by
  exact GridSpernerLabeling.almostFullyLabeledOn_iff L cell.vertices missing

theorem FullyLabeled.almostFullyLabeled [DecidableEq ι]
    {cell : GridSmallCell ι N} {L : GridSpernerLabeling ι N}
    (hfull : cell.FullyLabeled L) (missing : ι) :
    cell.AlmostFullyLabeled L missing :=
  hfull.almostFullyLabeledOn missing

theorem fullyLabeled_iff_almostFullyLabeled_and_missing [DecidableEq ι]
    (cell : GridSmallCell ι N) (L : GridSpernerLabeling ι N)
    (missing : ι) :
    cell.FullyLabeled L ↔
      cell.AlmostFullyLabeled L missing ∧
        missing ∈ L.labelsOn cell.vertices := by
  exact GridSpernerLabeling.fullyLabeledOn_iff_almostFullyLabeledOn_and_missing
    L cell.vertices missing

theorem AlmostFullyLabeled.fullyLabeled_of_missing_mem [DecidableEq ι]
    {cell : GridSmallCell ι N} {L : GridSpernerLabeling ι N}
    {missing : ι} (halmost : cell.AlmostFullyLabeled L missing)
    (hmissing : missing ∈ L.labelsOn cell.vertices) :
    cell.FullyLabeled L :=
  (fullyLabeled_iff_almostFullyLabeled_and_missing cell L missing).mpr
    ⟨halmost, hmissing⟩

theorem AlmostFullyLabeled.fullyLabeled_or_missing_notMem [DecidableEq ι]
    {cell : GridSmallCell ι N} {L : GridSpernerLabeling ι N}
    {missing : ι} (halmost : cell.AlmostFullyLabeled L missing) :
    cell.FullyLabeled L ∨ missing ∉ L.labelsOn cell.vertices := by
  by_cases hmissing : missing ∈ L.labelsOn cell.vertices
  · exact Or.inl (halmost.fullyLabeled_of_missing_mem hmissing)
  · exact Or.inr hmissing

theorem label_notMem_of_coord_eq_zero [DecidableEq ι]
    (cell : GridSmallCell ι N) (L : GridSpernerLabeling ι N) {i : ι}
    (hzero : ∀ a ∈ cell.vertices, a.1 i = 0) :
    i ∉ L.labelsOn cell.vertices :=
  L.label_notMem_labelsOn_of_coord_eq_zero cell.vertices hzero

theorem not_fullyLabeled_of_coord_eq_zero [DecidableEq ι]
    (cell : GridSmallCell ι N) (L : GridSpernerLabeling ι N) {i : ι}
    (hzero : ∀ a ∈ cell.vertices, a.1 i = 0) :
    ¬ cell.FullyLabeled L :=
  L.not_fullyLabeledOn_of_coord_eq_zero cell.vertices hzero

theorem labelsOn_eq_univ_of_fullyLabeled [DecidableEq ι]
    (cell : GridSmallCell ι N) (L : GridSpernerLabeling ι N)
    (hfull : cell.FullyLabeled L) :
    L.labelsOn cell.vertices = Finset.univ :=
  L.labelsOn_eq_univ_of_fullyLabeledOn hfull

theorem injOn_label_of_fullyLabeled_card_eq [DecidableEq ι]
    (cell : GridSmallCell ι N) (L : GridSpernerLabeling ι N)
    (hfull : cell.FullyLabeled L)
    (hcard : cell.vertices.card = Fintype.card ι) :
    Set.InjOn L.label cell.vertices :=
  L.injOn_label_of_fullyLabeledOn_card_eq hfull hcard

theorem eq_of_mem_of_label_eq_of_fullyLabeled_card_eq [DecidableEq ι]
    (cell : GridSmallCell ι N) (L : GridSpernerLabeling ι N)
    (hfull : cell.FullyLabeled L)
    (hcard : cell.vertices.card = Fintype.card ι)
    {a b : SimplexGrid ι N} (ha : a ∈ cell.vertices) (hb : b ∈ cell.vertices)
    (hlabel : L.label a = L.label b) :
    a = b :=
  cell.injOn_label_of_fullyLabeled_card_eq L hfull hcard ha hb hlabel

/-- A finite face shared by two small grid cells. -/
structure SharedFace (cell cell' : GridSmallCell ι N)
    (face : Finset (SimplexGrid ι N)) : Prop where
  nonempty : face.Nonempty
  subset_left : face ⊆ cell.vertices
  subset_right : face ⊆ cell'.vertices

namespace SharedFace

variable {cell cell' : GridSmallCell ι N}
    {face : Finset (SimplexGrid ι N)}

/-- Shared faces are symmetric in the two cells. -/
theorem symm (h : SharedFace cell cell' face) :
    SharedFace cell' cell face where
  nonempty := h.nonempty
  subset_left := h.subset_right
  subset_right := h.subset_left

end SharedFace

/--
Two distinct cells share a pivot face for the label `missing` if they have a
common nonempty face containing every label except possibly `missing`.
-/
def SharesAlmostFullyLabeledFace [DecidableEq ι]
    (cell cell' : GridSmallCell ι N) (L : GridSpernerLabeling ι N)
    (missing : ι) : Prop :=
  cell ≠ cell' ∧ ∃ face : Finset (SimplexGrid ι N),
    cell.SharedFace cell' face ∧ L.AlmostFullyLabeledOn face missing

theorem SharesAlmostFullyLabeledFace.symm [DecidableEq ι]
    {cell cell' : GridSmallCell ι N} {L : GridSpernerLabeling ι N}
    {missing : ι}
    (h : cell.SharesAlmostFullyLabeledFace cell' L missing) :
    cell'.SharesAlmostFullyLabeledFace cell L missing := by
  rcases h with ⟨hne, face, hface, halmost⟩
  exact ⟨fun hcell => hne hcell.symm, face, hface.symm, halmost⟩

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

/-- The coordinates where a cube-slice vertex is at the upper endpoint. -/
def raisedSet (S : GridCubeSlice ι N) (a : SimplexGrid ι N) : Finset ι :=
  Finset.univ.filter fun i => a.1 i = (S.lower i : ℕ) + 1

@[simp] theorem mem_raisedSet_iff (S : GridCubeSlice ι N)
    (a : SimplexGrid ι N) {i : ι} :
    i ∈ S.raisedSet a ↔ a.1 i = (S.lower i : ℕ) + 1 := by
  simp [raisedSet]

theorem coord_eq_lower_of_not_mem_raisedSet (S : GridCubeSlice ι N)
    {a : SimplexGrid ι N} (ha : a ∈ S.toSmallCell.vertices) {i : ι}
    (hi : i ∉ S.raisedSet a) :
    a.1 i = (S.lower i : ℕ) := by
  rcases (S.mem_toSmallCell_vertices_iff.mp ha i) with hcoord | hcoord
  · exact hcoord
  · exact False.elim (hi ((S.mem_raisedSet_iff a).mpr hcoord))

theorem coord_eq_lower_add_raised_indicator [DecidableEq ι] (S : GridCubeSlice ι N)
    {a : SimplexGrid ι N} (ha : a ∈ S.toSmallCell.vertices) (i : ι) :
    a.1 i = (S.lower i : ℕ) + if i ∈ S.raisedSet a then 1 else 0 := by
  by_cases hi : i ∈ S.raisedSet a
  · rw [(S.mem_raisedSet_iff a).mp hi]
    simp [hi]
  · rw [S.coord_eq_lower_of_not_mem_raisedSet ha hi]
    simp [hi]

/-- The sum of the lower corner coordinates of a cube slice. -/
def lowerSum (S : GridCubeSlice ι N) : ℕ :=
  ∑ i, (S.lower i : ℕ)

theorem lowerSum_add_raisedSet_card_eq [DecidableEq ι] (S : GridCubeSlice ι N)
    {a : SimplexGrid ι N} (ha : a ∈ S.toSmallCell.vertices) :
    S.lowerSum + (S.raisedSet a).card = N := by
  classical
  have hsum :
      (∑ i, a.1 i) =
        ∑ i, ((S.lower i : ℕ) +
          if i ∈ S.raisedSet a then 1 else 0) := by
    exact Finset.sum_congr rfl fun i _ =>
      S.coord_eq_lower_add_raised_indicator ha i
  have hindicator :
      (∑ i, (if i ∈ S.raisedSet a then 1 else 0 : ℕ)) =
        (S.raisedSet a).card := by
    calc
      (∑ i, (if i ∈ S.raisedSet a then 1 else 0 : ℕ))
          = ((Finset.univ : Finset ι).filter fun i => i ∈ S.raisedSet a).card := by
            simpa only [Finset.mem_univ, true_and] using
              (Finset.sum_boole (fun i => i ∈ S.raisedSet a)
                (Finset.univ : Finset ι) : (∑ i ∈ (Finset.univ : Finset ι),
                  if i ∈ S.raisedSet a then (1 : ℕ) else 0) =
                    ((Finset.univ : Finset ι).filter fun i => i ∈ S.raisedSet a).card)
      _ = (S.raisedSet a).card := by
            congr 1
            ext i
            simp [raisedSet]
  calc
    S.lowerSum + (S.raisedSet a).card
        = (∑ i, (S.lower i : ℕ)) +
            ∑ i, (if i ∈ S.raisedSet a then 1 else 0 : ℕ) := by
          rw [lowerSum, hindicator]
    _ = ∑ i, ((S.lower i : ℕ) +
          if i ∈ S.raisedSet a then 1 else 0) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ i, a.1 i := hsum.symm
    _ = N := a.2

/-- The number of raised coordinates in every vertex of a cube slice. -/
def rank (S : GridCubeSlice ι N) : ℕ :=
  N - S.lowerSum

theorem lowerSum_le_mesh [DecidableEq ι] (S : GridCubeSlice ι N) :
    S.lowerSum ≤ N := by
  rcases S.nonempty_vertices with ⟨a, ha⟩
  have haCell : a ∈ S.toSmallCell.vertices := by
    simpa [GridCubeSlice.toSmallCell] using ha
  have hsum := S.lowerSum_add_raisedSet_card_eq haCell
  omega

theorem lowerSum_add_rank_eq [DecidableEq ι] (S : GridCubeSlice ι N) :
    S.lowerSum + S.rank = N := by
  rw [rank]
  exact Nat.add_sub_of_le S.lowerSum_le_mesh

theorem raisedSet_card_eq_rank [DecidableEq ι] (S : GridCubeSlice ι N)
    {a : SimplexGrid ι N} (ha : a ∈ S.toSmallCell.vertices) :
    (S.raisedSet a).card = S.rank := by
  have hsum := S.lowerSum_add_raisedSet_card_eq ha
  have hrank := S.lowerSum_add_rank_eq
  omega

theorem rank_le_card [DecidableEq ι] (S : GridCubeSlice ι N) :
    S.rank ≤ Fintype.card ι := by
  rcases S.nonempty_vertices with ⟨a, ha⟩
  have haCell : a ∈ S.toSmallCell.vertices := by
    simpa [GridCubeSlice.toSmallCell] using ha
  rw [← S.raisedSet_card_eq_rank haCell]
  exact Finset.card_le_univ _

theorem raisedSet_card_eq_of_mem [DecidableEq ι] (S : GridCubeSlice ι N)
    {a b : SimplexGrid ι N}
    (ha : a ∈ S.toSmallCell.vertices) (hb : b ∈ S.toSmallCell.vertices) :
    (S.raisedSet a).card = (S.raisedSet b).card := by
  have ha' := S.lowerSum_add_raisedSet_card_eq ha
  have hb' := S.lowerSum_add_raisedSet_card_eq hb
  omega

theorem ext_of_raisedSet_eq [DecidableEq ι] (S : GridCubeSlice ι N)
    {a b : SimplexGrid ι N}
    (ha : a ∈ S.toSmallCell.vertices) (hb : b ∈ S.toSmallCell.vertices)
    (hsets : S.raisedSet a = S.raisedSet b) :
    a = b := by
  apply Subtype.ext
  funext i
  by_cases hi : i ∈ S.raisedSet a
  · have hi' : i ∈ S.raisedSet b := by simpa [hsets] using hi
    exact ((S.mem_raisedSet_iff a).mp hi).trans
      (((S.mem_raisedSet_iff b).mp hi').symm)
  · have hi' : i ∉ S.raisedSet b := by simpa [hsets] using hi
    rw [S.coord_eq_lower_of_not_mem_raisedSet ha hi,
      S.coord_eq_lower_of_not_mem_raisedSet hb hi']

/--
The cube-slice vertex associated to a set of raised coordinates of the
correct rank.
-/
noncomputable def vertexOfRaisedSet [DecidableEq ι]
    (S : GridCubeSlice ι N) (R : Finset ι) (hR : S.lowerSum + R.card = N) :
    SimplexGrid ι N := by
  refine ⟨fun i => (S.lower i : ℕ) + if i ∈ R then 1 else 0, ?_⟩
  classical
  have hindicator :
      (∑ i, (if i ∈ R then 1 else 0 : ℕ)) = R.card := by
    calc
      (∑ i, (if i ∈ R then 1 else 0 : ℕ))
          = ((Finset.univ : Finset ι).filter fun i => i ∈ R).card := by
            simpa only [Finset.mem_univ, true_and] using
              (Finset.sum_boole (fun i => i ∈ R)
                (Finset.univ : Finset ι) : (∑ i ∈ (Finset.univ : Finset ι),
                  if i ∈ R then (1 : ℕ) else 0) =
                    ((Finset.univ : Finset ι).filter fun i => i ∈ R).card)
      _ = R.card := by
            congr 1
            ext i
            simp
  calc
    (∑ i, ((S.lower i : ℕ) + if i ∈ R then 1 else 0))
        = (∑ i, (S.lower i : ℕ)) +
            ∑ i, (if i ∈ R then 1 else 0 : ℕ) := by
          rw [Finset.sum_add_distrib]
    _ = S.lowerSum + R.card := by
          rw [lowerSum, hindicator]
    _ = N := hR

theorem vertexOfRaisedSet_apply [DecidableEq ι]
    (S : GridCubeSlice ι N) (R : Finset ι) (hR : S.lowerSum + R.card = N)
    (i : ι) :
    (S.vertexOfRaisedSet R hR).1 i =
      (S.lower i : ℕ) + if i ∈ R then 1 else 0 :=
  rfl

theorem vertexOfRaisedSet_coord_eq_zero_of_lower_eq_zero_of_not_mem
    [DecidableEq ι]
    (S : GridCubeSlice ι N) {R : Finset ι} {hR : S.lowerSum + R.card = N}
    {i : ι} (hlower : (S.lower i : ℕ) = 0) (hi : i ∉ R) :
    (S.vertexOfRaisedSet R hR).1 i = 0 := by
  rw [vertexOfRaisedSet_apply, hlower]
  simp [hi]

theorem vertexOfRaisedSet_mem_vertices [DecidableEq ι]
    (S : GridCubeSlice ι N) (R : Finset ι) (hR : S.lowerSum + R.card = N) :
    S.vertexOfRaisedSet R hR ∈ S.toSmallCell.vertices := by
  rw [GridCubeSlice.toSmallCell_vertices, mem_cubeSliceVertices_iff]
  intro i
  by_cases hi : i ∈ R
  · exact Or.inr (by simp [vertexOfRaisedSet_apply, hi])
  · exact Or.inl (by simp [vertexOfRaisedSet_apply, hi])

@[simp] theorem raisedSet_vertexOfRaisedSet [DecidableEq ι]
    (S : GridCubeSlice ι N) (R : Finset ι) (hR : S.lowerSum + R.card = N) :
    S.raisedSet (S.vertexOfRaisedSet R hR) = R := by
  ext i
  by_cases hi : i ∈ R
  · simp [hi, vertexOfRaisedSet_apply]
  · simp [hi, vertexOfRaisedSet_apply]

theorem vertexOfRaisedSet_raisedSet [DecidableEq ι]
    (S : GridCubeSlice ι N) {a : SimplexGrid ι N}
    (ha : a ∈ S.toSmallCell.vertices) :
    S.vertexOfRaisedSet (S.raisedSet a)
      (S.lowerSum_add_raisedSet_card_eq ha) = a := by
  apply Subtype.ext
  funext i
  rw [vertexOfRaisedSet_apply]
  exact (S.coord_eq_lower_add_raised_indicator ha i).symm

/--
Vertices of a cube slice are equivalently subsets of coordinates of the
slice rank. This is the hypersimplex model used by Freudenthal/Kuhn-style
triangulations.
-/
noncomputable def vertexEquivRankedSubsets [DecidableEq ι]
    (S : GridCubeSlice ι N) :
    {a : SimplexGrid ι N // a ∈ S.toSmallCell.vertices} ≃
      {R : Finset ι // R.card = S.rank} where
  toFun a := ⟨S.raisedSet a.1, S.raisedSet_card_eq_rank a.2⟩
  invFun R :=
    ⟨S.vertexOfRaisedSet R.1 (by
        rw [R.2]
        exact S.lowerSum_add_rank_eq),
      S.vertexOfRaisedSet_mem_vertices R.1 (by
        rw [R.2]
        exact S.lowerSum_add_rank_eq)⟩
  left_inv a := by
    apply Subtype.ext
    exact S.vertexOfRaisedSet_raisedSet a.2
  right_inv R := by
    apply Subtype.ext
    simp

/--
The grid vertices associated to a finite family of ranked subsets of a cube
slice.

This is the common-face representation used by path-cell pivot arguments.
-/
noncomputable def verticesOfRankedSubsets [DecidableEq ι]
    (S : GridCubeSlice ι N)
    (subsets : Finset {R : Finset ι // R.card = S.rank}) :
    Finset (SimplexGrid ι N) := by
  classical
  exact subsets.image fun R =>
    S.vertexOfRaisedSet R.1 (by
      rw [R.2]
      exact S.lowerSum_add_rank_eq)

theorem mem_verticesOfRankedSubsets_iff [DecidableEq ι]
    (S : GridCubeSlice ι N)
    (subsets : Finset {R : Finset ι // R.card = S.rank})
    {a : SimplexGrid ι N} :
    a ∈ S.verticesOfRankedSubsets subsets ↔
      ∃ R ∈ subsets,
        S.vertexOfRaisedSet R.1 (by
          rw [R.2]
          exact S.lowerSum_add_rank_eq) = a := by
  classical
  simp [verticesOfRankedSubsets]

theorem vertexOfRankedSubset_mem_verticesOfRankedSubsets [DecidableEq ι]
    (S : GridCubeSlice ι N)
    {subsets : Finset {R : Finset ι // R.card = S.rank}}
    {R : {R : Finset ι // R.card = S.rank}} (hR : R ∈ subsets) :
    S.vertexOfRaisedSet R.1 (by
      rw [R.2]
      exact S.lowerSum_add_rank_eq) ∈ S.verticesOfRankedSubsets subsets := by
  classical
  rw [mem_verticesOfRankedSubsets_iff]
  exact ⟨R, hR, rfl⟩

theorem mem_of_vertexOfRankedSubset_mem_verticesOfRankedSubsets [DecidableEq ι]
    (S : GridCubeSlice ι N)
    {subsets : Finset {R : Finset ι // R.card = S.rank}}
    {R : {R : Finset ι // R.card = S.rank}}
    (hR :
      S.vertexOfRaisedSet R.1 (by
        rw [R.2]
        exact S.lowerSum_add_rank_eq) ∈ S.verticesOfRankedSubsets subsets) :
    R ∈ subsets := by
  classical
  rw [mem_verticesOfRankedSubsets_iff] at hR
  rcases hR with ⟨Q, hQ, hQR⟩
  have hsets := congrArg S.raisedSet hQR
  have hQR' : Q = R := by
    apply Subtype.ext
    simpa using hsets
  simpa [hQR'] using hQ

theorem verticesOfRankedSubsets_eq_iff [DecidableEq ι]
    (S : GridCubeSlice ι N)
    (subsets subsets' : Finset {R : Finset ι // R.card = S.rank}) :
    S.verticesOfRankedSubsets subsets = S.verticesOfRankedSubsets subsets' ↔
      subsets = subsets' := by
  classical
  constructor
  · intro hvertices
    ext R
    constructor
    · intro hR
      exact S.mem_of_vertexOfRankedSubset_mem_verticesOfRankedSubsets
        (by
          rw [← hvertices]
          exact S.vertexOfRankedSubset_mem_verticesOfRankedSubsets hR)
    · intro hR
      exact S.mem_of_vertexOfRankedSubset_mem_verticesOfRankedSubsets
        (by
          rw [hvertices]
          exact S.vertexOfRankedSubset_mem_verticesOfRankedSubsets hR)
  · intro h
    rw [h]

theorem verticesOfRankedSubsets_coord_eq_zero_of_lower_eq_zero_of_not_mem
    [DecidableEq ι]
    (S : GridCubeSlice ι N)
    {subsets : Finset {R : Finset ι // R.card = S.rank}} {i : ι}
    (hlower : (S.lower i : ℕ) = 0)
    (hnot : ∀ R ∈ subsets, i ∉ R.1) :
    ∀ a ∈ S.verticesOfRankedSubsets subsets, a.1 i = 0 := by
  classical
  intro a ha
  rw [mem_verticesOfRankedSubsets_iff] at ha
  rcases ha with ⟨R, hR, rfl⟩
  exact S.vertexOfRaisedSet_coord_eq_zero_of_lower_eq_zero_of_not_mem
    hlower (hnot R hR)

theorem verticesOfRankedSubsets_nonempty [DecidableEq ι]
    (S : GridCubeSlice ι N)
    {subsets : Finset {R : Finset ι // R.card = S.rank}}
    (hsubsets : subsets.Nonempty) :
    (S.verticesOfRankedSubsets subsets).Nonempty := by
  classical
  rcases hsubsets with ⟨R, hR⟩
  refine ⟨S.vertexOfRaisedSet R.1 (by
    rw [R.2]
    exact S.lowerSum_add_rank_eq), ?_⟩
  rw [mem_verticesOfRankedSubsets_iff]
  exact ⟨R, hR, rfl⟩

theorem verticesOfRankedSubsets_subset_toSmallCell [DecidableEq ι]
    (S : GridCubeSlice ι N)
    (subsets : Finset {R : Finset ι // R.card = S.rank}) :
    S.verticesOfRankedSubsets subsets ⊆ S.toSmallCell.vertices := by
  classical
  intro a ha
  rw [mem_verticesOfRankedSubsets_iff] at ha
  rcases ha with ⟨R, _hR, rfl⟩
  exact S.vertexOfRaisedSet_mem_vertices R.1 (by
    rw [R.2]
    exact S.lowerSum_add_rank_eq)

theorem verticesOfRankedSubsets_card_eq [DecidableEq ι]
    (S : GridCubeSlice ι N)
    (subsets : Finset {R : Finset ι // R.card = S.rank}) :
    (S.verticesOfRankedSubsets subsets).card = subsets.card := by
  classical
  rw [verticesOfRankedSubsets]
  refine Finset.card_image_of_injective _ ?_
  intro R Q hRQ
  apply Subtype.ext
  have hsets := congrArg S.raisedSet hRQ
  simpa using hsets

/--
A directed elementary move between ranked subsets: drop one coordinate and add
one coordinate. These are the edges used by path/alcove descriptions of
Freudenthal/Kuhn cells inside a cube slice.
-/
def RankedSubsetStep [DecidableEq ι] (R Q : Finset ι) : Prop :=
  ∃ drop, drop ∈ R ∧ ∃ add, add ∉ R ∧ Q = insert add (R.erase drop)

/--
The cyclic embedding `k ↦ start + k (mod d)` from `Fin r` into `Fin d`.

For `r ≤ d`, this enumerates a cyclic block of length `r` without repetition.
These cyclic blocks are the ranked subsets used by the standard
Freudenthal/Kuhn alcove triangulation of a hypersimplex.
-/
def cyclicIndexEmbedding (d r start : ℕ) (hd : 0 < d) (hr : r ≤ d) :
    Fin r ↪ Fin d where
  toFun k := ⟨(start + k.1) % d, Nat.mod_lt _ hd⟩
  inj' := by
    intro k l hkl
    apply Fin.ext
    have hval :
        (start + k.1) % d = (start + l.1) % d := by
      exact congrArg Fin.val hkl
    have hmod :
        start + k.1 ≡ start + l.1 [MOD d] := by
      exact hval
    have hklmod : k.1 ≡ l.1 [MOD d] :=
      Nat.ModEq.add_left_cancel' start hmod
    exact hklmod.eq_of_lt_of_lt
      (lt_of_lt_of_le k.2 hr) (lt_of_lt_of_le l.2 hr)

/--
The cyclic interval of length `r` in `Fin d` starting at `start`.
-/
def cyclicWindow (d r start : ℕ) (hd : 0 < d) (hr : r ≤ d) :
    Finset (Fin d) :=
  (Finset.univ : Finset (Fin r)).map (cyclicIndexEmbedding d r start hd hr)

theorem mem_cyclicWindow_iff (d r start : ℕ) (hd : 0 < d) (hr : r ≤ d)
    {i : Fin d} :
    i ∈ cyclicWindow d r start hd hr ↔
      ∃ k : ℕ, k < r ∧ i.1 = (start + k) % d := by
  constructor
  · intro hi
    rw [cyclicWindow] at hi
    rcases Finset.mem_map.mp hi with ⟨k, _hk, hk⟩
    refine ⟨k.1, k.2, ?_⟩
    exact (congrArg Fin.val hk).symm
  · rintro ⟨k, hk, hi⟩
    rw [cyclicWindow]
    refine Finset.mem_map.mpr ⟨⟨k, hk⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext hi.symm

@[simp] theorem card_cyclicWindow (d r start : ℕ)
    (hd : 0 < d) (hr : r ≤ d) :
    (cyclicWindow d r start hd hr).card = r := by
  simp [cyclicWindow]

theorem cyclicWindow_start_mem (d r start : ℕ)
    (hd : 0 < d) (hr : r ≤ d) (hrpos : 0 < r) :
    (⟨start % d, Nat.mod_lt _ hd⟩ : Fin d) ∈
      cyclicWindow d r start hd hr := by
  rw [mem_cyclicWindow_iff]
  exact ⟨0, hrpos, by simp⟩

theorem cyclicWindow_end_notMem (d r start : ℕ)
    (hd : 0 < d) (hrlt : r < d) :
    (⟨(start + r) % d, Nat.mod_lt _ hd⟩ : Fin d) ∉
      cyclicWindow d r start hd hrlt.le := by
  intro hend
  rw [mem_cyclicWindow_iff] at hend
  rcases hend with ⟨k, hk, hval⟩
  have hmod :
      start + r ≡ start + k [MOD d] := by
    exact hval
  have hrk : r ≡ k [MOD d] :=
    Nat.ModEq.add_left_cancel' start hmod
  have hklt : k < d := lt_trans hk hrlt
  have hEq : r = k := hrk.eq_of_lt_of_lt hrlt hklt
  omega

/--
A cyclic window, bundled as a ranked subset of a `Fin d` cube slice.
-/
noncomputable def cyclicWindowRankedSubset
    {d : ℕ} (S : GridCubeSlice (Fin d) N) (hd : 0 < d) (start : ℕ) :
    {R : Finset (Fin d) // R.card = S.rank} := by
  classical
  have hr : S.rank ≤ d := by
    simpa [Fintype.card_fin] using S.rank_le_card
  exact ⟨cyclicWindow d S.rank start hd hr, card_cyclicWindow d S.rank start hd hr⟩

/--
The cyclic-window chain associated to a `Fin d` cube slice.

In the interior-rank case `0 < S.rank < d`, successive entries are elementary
ranked-subset steps. Proving this chain has no duplicates is the remaining
piece needed to package it as a maximal Kuhn path cell.
-/
noncomputable def cyclicWindowChain
    {d : ℕ} (S : GridCubeSlice (Fin d) N) (hd : 0 < d) :
    List {R : Finset (Fin d) // R.card = S.rank} :=
  List.ofFn fun t : Fin d => S.cyclicWindowRankedSubset hd t.1

@[simp] theorem length_cyclicWindowChain
    {d : ℕ} (S : GridCubeSlice (Fin d) N) (hd : 0 < d) :
    (S.cyclicWindowChain hd).length = d := by
  simp [cyclicWindowChain]

theorem cyclicWindowChain_nonempty
    {d : ℕ} (S : GridCubeSlice (Fin d) N) (hd : 0 < d) :
    S.cyclicWindowChain hd ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  simp [length_cyclicWindowChain S hd, Nat.ne_of_gt hd] at hlen

theorem cyclicWindowRankedSubset_mem_chain
    {d : ℕ} (S : GridCubeSlice (Fin d) N) (hd : 0 < d)
    (t : Fin d) :
    S.cyclicWindowRankedSubset hd t.1 ∈ S.cyclicWindowChain hd := by
  classical
  simp [cyclicWindowChain]

/--
Successive cyclic windows differ by one elementary ranked-subset step.

This is the local combinatorial move followed by the Freudenthal/Kuhn pivot
path.
-/
theorem rankedSubsetStep_cyclicWindow (d r start : ℕ)
    (hd : 0 < d) (hrpos : 0 < r) (hrlt : r < d) :
    RankedSubsetStep
      (cyclicWindow d r start hd hrlt.le)
      (cyclicWindow d r (start + 1) hd hrlt.le) := by
  classical
  let drop : Fin d := ⟨start % d, Nat.mod_lt _ hd⟩
  let add : Fin d := ⟨(start + r) % d, Nat.mod_lt _ hd⟩
  refine ⟨drop, ?_, add, ?_, ?_⟩
  · exact cyclicWindow_start_mem d r start hd hrlt.le hrpos
  · exact cyclicWindow_end_notMem d r start hd hrlt
  · ext i
    constructor
    · intro hi
      rw [Finset.mem_insert, Finset.mem_erase]
      rw [mem_cyclicWindow_iff] at hi
      rcases hi with ⟨k, hk, hi⟩
      by_cases hlast : k + 1 = r
      · left
        apply Fin.ext
        calc
          i.1 = (start + 1 + k) % d := hi
          _ = (start + r) % d := by
                congr 1
                omega
      · right
        have hkstep : k + 1 < r := by omega
        constructor
        · intro hidrop
          have hval := congrArg Fin.val hidrop
          have hmod :
              start + (k + 1) ≡ start + 0 [MOD d] := by
            calc
              (start + (k + 1)) % d = (start + 1 + k) % d := by
                    congr 1
                    omega
              _ = i.1 := hi.symm
              _ = start % d := hval
              _ = (start + 0) % d := by simp
          have hkmod : k + 1 ≡ 0 [MOD d] :=
            Nat.ModEq.add_left_cancel' start hmod
          have hklt : k + 1 < d := lt_trans hkstep hrlt
          have hzero : k + 1 = 0 :=
            hkmod.eq_of_lt_of_lt hklt hd
          omega
        · rw [mem_cyclicWindow_iff]
          refine ⟨k + 1, hkstep, ?_⟩
          calc
            i.1 = (start + 1 + k) % d := hi
            _ = (start + (k + 1)) % d := by
                  congr 1
                  omega
    · intro hi
      rw [Finset.mem_insert, Finset.mem_erase] at hi
      rcases hi with hadd | ⟨hidrop, hiR⟩
      · rw [mem_cyclicWindow_iff]
        refine ⟨r - 1, by omega, ?_⟩
        have hval := congrArg Fin.val hadd
        calc
          i.1 = (start + r) % d := hval
          _ = (start + 1 + (r - 1)) % d := by
                congr 1
                omega
      · rw [mem_cyclicWindow_iff] at hiR
        rcases hiR with ⟨k, hk, hi⟩
        have hkpos : 0 < k := by
          by_contra hkzero
          have hk0 : k = 0 := Nat.eq_zero_of_not_pos hkzero
          apply hidrop
          apply Fin.ext
          calc
            i.1 = (start + k) % d := hi
            _ = start % d := by simp [hk0]
        rw [mem_cyclicWindow_iff]
        refine ⟨k - 1, by omega, ?_⟩
        calc
          i.1 = (start + k) % d := hi
          _ = (start + 1 + (k - 1)) % d := by
                congr 1
                omega

theorem cyclicWindowChain_isChain
    {d : ℕ} (S : GridCubeSlice (Fin d) N) (hd : 0 < d)
    (hrpos : 0 < S.rank) (hrlt : S.rank < d) :
    (S.cyclicWindowChain hd).IsChain fun R Q =>
      RankedSubsetStep R.1 Q.1 := by
  classical
  rw [cyclicWindowChain, List.isChain_ofFn]
  intro i hi
  have hstep :=
    rankedSubsetStep_cyclicWindow d S.rank i hd hrpos hrlt
  simpa [cyclicWindowRankedSubset] using hstep

theorem cyclicWindowRankedSubset_injective
    {d : ℕ} (S : GridCubeSlice (Fin d) N) (hd : 0 < d)
    (hrpos : 0 < S.rank) (hrlt : S.rank < d) :
    Function.Injective fun t : Fin d => S.cyclicWindowRankedSubset hd t.1 := by
  classical
  intro a b hab
  apply Fin.ext
  have hset :
      cyclicWindow d S.rank a.1 hd hrlt.le =
        cyclicWindow d S.rank b.1 hd hrlt.le :=
    congrArg Subtype.val hab
  let startB : Fin d := ⟨b.1 % d, Nat.mod_lt _ hd⟩
  have hbmemB :
      startB ∈ cyclicWindow d S.rank b.1 hd hrlt.le :=
    cyclicWindow_start_mem d S.rank b.1 hd hrlt.le hrpos
  have hbmemA :
      startB ∈ cyclicWindow d S.rank a.1 hd hrlt.le := by
    simpa [hset] using hbmemB
  rw [mem_cyclicWindow_iff] at hbmemA
  rcases hbmemA with ⟨k, hk, hbk⟩
  by_cases hk0 : k = 0
  · have hbval : b.1 = a.1 := by
      have hbmod : b.1 % d = b.1 := Nat.mod_eq_of_lt b.2
      have hbk' : b.1 = (a.1 + 0) % d := by
        simpa [startB, hbmod, hk0] using hbk
      calc
        b.1 = (a.1 + 0) % d := hbk'
        _ = a.1 := by simpa using Nat.mod_eq_of_lt a.2
    exact hbval.symm
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    let endA : Fin d := ⟨(a.1 + S.rank) % d, Nat.mod_lt _ hd⟩
    have hnotA :
        endA ∉ cyclicWindow d S.rank a.1 hd hrlt.le :=
      cyclicWindow_end_notMem d S.rank a.1 hd hrlt
    have hnotB :
        endA ∉ cyclicWindow d S.rank b.1 hd hrlt.le := by
      intro hendB
      exact hnotA (by simpa [hset] using hendB)
    have hbMod : b.1 ≡ a.1 + k [MOD d] := by
      have hbmod : b.1 % d = b.1 := Nat.mod_eq_of_lt b.2
      change b.1 % d = (a.1 + k) % d
      simpa [startB, hbmod] using hbk
    have hendB :
        endA ∈ cyclicWindow d S.rank b.1 hd hrlt.le := by
      rw [mem_cyclicWindow_iff]
      refine ⟨S.rank - k, by omega, ?_⟩
      have hsumMod :
          b.1 + (S.rank - k) ≡ a.1 + S.rank [MOD d] := by
        have h1 := hbMod.add_right (S.rank - k)
        have hright : (a.1 + k) + (S.rank - k) = a.1 + S.rank := by
          omega
        simpa [hright, Nat.add_assoc] using h1
      exact hsumMod.symm
    exact False.elim (hnotB hendB)

theorem cyclicWindowChain_nodup
    {d : ℕ} (S : GridCubeSlice (Fin d) N) (hd : 0 < d)
    (hrpos : 0 < S.rank) (hrlt : S.rank < d) :
    (S.cyclicWindowChain hd).Nodup := by
  classical
  rw [cyclicWindowChain]
  exact List.nodup_ofFn_ofInjective
    (cyclicWindowRankedSubset_injective S hd hrpos hrlt)

omit [Fintype ι] in
theorem rankedSubsetStep_card_eq [DecidableEq ι] {R Q : Finset ι}
    (h : RankedSubsetStep R Q) :
    Q.card = R.card := by
  rcases h with ⟨drop, hdrop, add, hadd, rfl⟩
  have haddErase : add ∉ R.erase drop := by
    simp [hadd]
  rw [Finset.card_insert_of_notMem haddErase, Finset.card_erase_of_mem hdrop]
  have hRpos : 0 < R.card := Finset.card_pos.mpr ⟨drop, hdrop⟩
  omega

omit [Fintype ι] in
theorem rankedSubsetStep_symm [DecidableEq ι] {R Q : Finset ι}
    (h : RankedSubsetStep R Q) :
    RankedSubsetStep Q R := by
  rcases h with ⟨drop, hdrop, add, hadd, rfl⟩
  have hne : drop ≠ add := by
    intro hdropadd
    exact hadd (hdropadd ▸ hdrop)
  have haddErase : add ∉ R.erase drop := by
    simp [hadd]
  refine ⟨add, ?_, drop, ?_, ?_⟩
  · simp
  · simp [Finset.mem_erase, hne, hdrop]
  · rw [Finset.erase_insert haddErase, Finset.insert_erase hdrop]

omit [Fintype ι] in
theorem rankedSubsetStep_ne [DecidableEq ι] {R Q : Finset ι}
    (h : RankedSubsetStep R Q) :
    R ≠ Q := by
  rcases h with ⟨drop, hdrop, add, hadd, rfl⟩
  intro hsame
  have haddTarget : add ∈ insert add (R.erase drop) := Finset.mem_insert_self _ _
  have haddR : add ∈ R := by
    rw [hsame]
    exact haddTarget
  exact hadd haddR

omit [Fintype ι] in
theorem rankedSubsetStep_map {κ : Type v} [DecidableEq ι] [DecidableEq κ]
    (e : ι ↪ κ) {R Q : Finset ι}
    (h : RankedSubsetStep R Q) :
    RankedSubsetStep (R.map e) (Q.map e) := by
  rcases h with ⟨drop, hdrop, add, hadd, rfl⟩
  refine ⟨e drop, Finset.mem_map_of_mem e hdrop, e add, ?_, ?_⟩
  · intro hmem
    exact hadd ((Finset.mem_map' e).mp hmem)
  · simp

omit [Fintype ι] in
theorem rankedSubsetStep_target_mem_iff [DecidableEq ι]
    {R : Finset ι} {drop add k : ι} :
    k ∈ insert add (R.erase drop) ↔
      k = add ∨ (k ∈ R ∧ k ≠ drop) := by
  simp [Finset.mem_erase, and_comm]

theorem vertexOfRaisedSet_swap_drop_apply [DecidableEq ι]
    (S : GridCubeSlice ι N) {R : Finset ι} {drop add : ι}
    (hdrop : drop ∈ R) (hadd : add ∉ R)
    (hQ : S.lowerSum + (insert add (R.erase drop)).card = N) :
    (S.vertexOfRaisedSet (insert add (R.erase drop)) hQ).1 drop =
      (S.lower drop : ℕ) := by
  have hne : drop ≠ add := by
    intro hdropadd
    exact hadd (hdropadd ▸ hdrop)
  rw [vertexOfRaisedSet_apply]
  simp [hne, hdrop]

theorem vertexOfRaisedSet_swap_add_apply [DecidableEq ι]
    (S : GridCubeSlice ι N) {R : Finset ι} {drop add : ι}
    (_hdrop : drop ∈ R) (_hadd : add ∉ R)
    (hQ : S.lowerSum + (insert add (R.erase drop)).card = N) :
    (S.vertexOfRaisedSet (insert add (R.erase drop)) hQ).1 add =
      (S.lower add : ℕ) + 1 := by
  rw [vertexOfRaisedSet_apply]
  simp

theorem vertexOfRaisedSet_swap_apply_of_ne [DecidableEq ι]
    (S : GridCubeSlice ι N) {R : Finset ι} {drop add k : ι}
    (_hdrop : drop ∈ R) (_hadd : add ∉ R)
    (hkdrop : k ≠ drop) (hkadd : k ≠ add)
    (hR : S.lowerSum + R.card = N)
    (hQ : S.lowerSum + (insert add (R.erase drop)).card = N) :
    (S.vertexOfRaisedSet (insert add (R.erase drop)) hQ).1 k =
      (S.vertexOfRaisedSet R hR).1 k := by
  rw [vertexOfRaisedSet_apply, vertexOfRaisedSet_apply]
  have htarget :
      k ∈ insert add (R.erase drop) ↔ k ∈ R := by
    rw [rankedSubsetStep_target_mem_iff]
    constructor
    · intro hk
      rcases hk with hk | ⟨hkR, _⟩
      · exact False.elim (hkadd hk)
      · exact hkR
    · intro hkR
      exact Or.inr ⟨hkR, hkdrop⟩
  by_cases hkR : k ∈ R <;> simp [hkR, htarget]

/--
A combinatorial cell inside a cube slice, described as a finite nonempty
family of ranked subsets. Freudenthal/Kuhn cells will be instances of this
structure.
-/
structure RankedSubsetCell (S : GridCubeSlice ι N) where
  subsets : Finset {R : Finset ι // R.card = S.rank}
  nonempty : subsets.Nonempty

/--
A path-shaped ranked-subset cell. This is not yet the full Freudenthal/Kuhn
construction, but it gives that construction a concrete target: a noduplicate
nonempty list of ranked subsets whose consecutive vertices differ by one
elementary swap.
-/
structure RankedSubsetPathCell [DecidableEq ι] (S : GridCubeSlice ι N) where
  chain : List {R : Finset ι // R.card = S.rank}
  nonempty : chain ≠ []
  nodup : chain.Nodup
  step_chain :
    chain.IsChain fun R Q => RankedSubsetStep R.1 Q.1

namespace RankedSubsetPathCell

variable [DecidableEq ι] {S : GridCubeSlice ι N}

/-- Forget the ordering data of a path cell and keep its ranked-subset cell. -/
noncomputable def toRankedSubsetCell
    (P : RankedSubsetPathCell S) : RankedSubsetCell S where
  subsets := P.chain.toFinset
  nonempty := by
    exact (List.toFinset_nonempty_iff P.chain).mpr P.nonempty

@[simp] theorem toRankedSubsetCell_subsets
    (P : RankedSubsetPathCell S) :
    P.toRankedSubsetCell.subsets = P.chain.toFinset :=
  rfl

theorem chain_subset_toRankedSubsetCell
    (P : RankedSubsetPathCell S) {R : {R : Finset ι // R.card = S.rank}}
    (hR : R ∈ P.chain) :
    R ∈ P.toRankedSubsetCell.subsets := by
  simpa [toRankedSubsetCell] using hR

/-- The one-vertex path cell associated to a ranked subset. -/
def singleton
    (S : GridCubeSlice ι N)
    (R : {R : Finset ι // R.card = S.rank}) :
    RankedSubsetPathCell S where
  chain := [R]
  nonempty := by simp
  nodup := by simp
  step_chain := by simp

@[simp] theorem singleton_chain_length
    (S : GridCubeSlice ι N)
    (R : {R : Finset ι // R.card = S.rank}) :
    (singleton S R).chain.length = 1 := by
  simp [singleton]

/-- The two-vertex path cell associated to one elementary ranked-subset step. -/
def pair
    (S : GridCubeSlice ι N)
    (R Q : {R : Finset ι // R.card = S.rank})
    (hstep : RankedSubsetStep R.1 Q.1) :
    RankedSubsetPathCell S where
  chain := [R, Q]
  nonempty := by simp
  nodup := by
    have hne : R ≠ Q := by
      intro hRQ
      exact rankedSubsetStep_ne hstep (congrArg Subtype.val hRQ)
    simp [hne]
  step_chain := by
    simp [hstep]

/--
The identity cyclic-window Freudenthal/Kuhn path cell in an interior-rank
`Fin d` cube slice.

Permuting coordinates will give the remaining cells of the standard
Freudenthal/Kuhn triangulation.
-/
noncomputable def cyclicWindow
    {d : ℕ} (S : GridCubeSlice (Fin d) N) (hd : 0 < d)
    (hrpos : 0 < S.rank) (hrlt : S.rank < d) :
    RankedSubsetPathCell S where
  chain := S.cyclicWindowChain hd
  nonempty := S.cyclicWindowChain_nonempty hd
  nodup := S.cyclicWindowChain_nodup hd hrpos hrlt
  step_chain := S.cyclicWindowChain_isChain hd hrpos hrlt

@[simp] theorem cyclicWindow_chain_length
    {d : ℕ} (S : GridCubeSlice (Fin d) N) (hd : 0 < d)
    (hrpos : 0 < S.rank) (hrlt : S.rank < d) :
    (cyclicWindow S hd hrpos hrlt).chain.length = d := by
  simp [cyclicWindow, GridCubeSlice.length_cyclicWindowChain]

theorem cyclicWindow_chain_mem
    {d : ℕ} (S : GridCubeSlice (Fin d) N) (hd : 0 < d)
    (hrpos : 0 < S.rank) (hrlt : S.rank < d) (t : Fin d) :
    S.cyclicWindowRankedSubset hd t.1 ∈
      (cyclicWindow S hd hrpos hrlt).chain := by
  exact S.cyclicWindowRankedSubset_mem_chain hd t

end RankedSubsetPathCell

namespace RankedSubsetCell

variable {S : GridCubeSlice ι N}

/-- Interpret a ranked-subset cell as a small grid cell. -/
noncomputable def toSmallCell [DecidableEq ι]
    (C : RankedSubsetCell S) : GridSmallCell ι N where
  vertices := C.subsets.image fun R =>
    S.vertexOfRaisedSet R.1 (by
      rw [R.2]
      exact S.lowerSum_add_rank_eq)
  nonempty := by
    rcases C.nonempty with ⟨R, hR⟩
    exact ⟨S.vertexOfRaisedSet R.1 (by
      rw [R.2]
      exact S.lowerSum_add_rank_eq), Finset.mem_image.mpr ⟨R, hR, rfl⟩⟩
  coordinate_span_le_one := by
    classical
    intro a ha b hb i
    rcases Finset.mem_image.mp ha with ⟨R, hR, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨Q, hQ, rfl⟩
    rw [S.vertexOfRaisedSet_apply, S.vertexOfRaisedSet_apply]
    by_cases hiR : i ∈ R.1 <;> by_cases hiQ : i ∈ Q.1 <;>
      simp [hiR, hiQ] <;> omega

@[simp] theorem toSmallCell_vertices [DecidableEq ι]
    (C : RankedSubsetCell S) :
    C.toSmallCell.vertices = C.subsets.image fun R =>
      S.vertexOfRaisedSet R.1 (by
        rw [R.2]
        exact S.lowerSum_add_rank_eq) :=
  rfl

theorem toSmallCell_vertices_subset_cubeSlice [DecidableEq ι]
    (C : RankedSubsetCell S) :
    C.toSmallCell.vertices ⊆ S.toSmallCell.vertices := by
  classical
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨R, hR, rfl⟩
  exact S.vertexOfRaisedSet_mem_vertices R.1 (by
    rw [R.2]
    exact S.lowerSum_add_rank_eq)

theorem sharedFace_of_commonSubsets [DecidableEq ι]
    (C D : RankedSubsetCell S)
    {subsets : Finset {R : Finset ι // R.card = S.rank}}
    (hsubsets : subsets.Nonempty)
    (hC : subsets ⊆ C.subsets) (hD : subsets ⊆ D.subsets) :
    GridSmallCell.SharedFace C.toSmallCell D.toSmallCell
      (S.verticesOfRankedSubsets subsets) := by
  classical
  refine ⟨S.verticesOfRankedSubsets_nonempty hsubsets, ?_, ?_⟩
  · intro a ha
    rw [GridCubeSlice.mem_verticesOfRankedSubsets_iff] at ha
    rcases ha with ⟨R, hR, rfl⟩
    rw [toSmallCell_vertices]
    exact Finset.mem_image.mpr ⟨R, hC hR, rfl⟩
  · intro a ha
    rw [GridCubeSlice.mem_verticesOfRankedSubsets_iff] at ha
    rcases ha with ⟨R, hR, rfl⟩
    rw [toSmallCell_vertices]
    exact Finset.mem_image.mpr ⟨R, hD hR, rfl⟩

theorem fullyLabeled_toSmallCell_iff [DecidableEq ι]
    (C : RankedSubsetCell S) (L : GridSpernerLabeling ι N) :
    C.toSmallCell.FullyLabeled L ↔
      ∀ i : ι, ∃ R ∈ C.subsets,
        L.label (S.vertexOfRaisedSet R.1 (by
          rw [R.2]
          exact S.lowerSum_add_rank_eq)) = i := by
  classical
  rw [GridSmallCell.fullyLabeled_iff]
  constructor
  · intro hfull i
    rcases hfull i with ⟨a, ha, hlabel⟩
    rw [toSmallCell_vertices] at ha
    rcases Finset.mem_image.mp ha with ⟨R, hR, haeq⟩
    refine ⟨R, hR, ?_⟩
    simpa [haeq] using hlabel
  · intro hfull i
    rcases hfull i with ⟨R, hR, hlabel⟩
    refine ⟨S.vertexOfRaisedSet R.1 (by
      rw [R.2]
      exact S.lowerSum_add_rank_eq), ?_, hlabel⟩
    rw [toSmallCell_vertices]
    exact Finset.mem_image.mpr ⟨R, hR, rfl⟩

theorem almostFullyLabeled_toSmallCell_iff [DecidableEq ι]
    (C : RankedSubsetCell S) (L : GridSpernerLabeling ι N)
    (missing : ι) :
    C.toSmallCell.AlmostFullyLabeled L missing ↔
      ∀ i : ι, i ≠ missing → ∃ R ∈ C.subsets,
        L.label (S.vertexOfRaisedSet R.1 (by
          rw [R.2]
          exact S.lowerSum_add_rank_eq)) = i := by
  classical
  rw [GridSmallCell.almostFullyLabeled_iff]
  constructor
  · intro halmost i hi
    rcases halmost i hi with ⟨a, ha, hlabel⟩
    rw [toSmallCell_vertices] at ha
    rcases Finset.mem_image.mp ha with ⟨R, hR, haeq⟩
    refine ⟨R, hR, ?_⟩
    simpa [haeq] using hlabel
  · intro halmost i hi
    rcases halmost i hi with ⟨R, hR, hlabel⟩
    refine ⟨S.vertexOfRaisedSet R.1 (by
      rw [R.2]
      exact S.lowerSum_add_rank_eq), ?_, hlabel⟩
    rw [toSmallCell_vertices]
    exact Finset.mem_image.mpr ⟨R, hR, rfl⟩

/-- The ranked-subset cell containing every vertex of a cube slice. -/
noncomputable def full [DecidableEq ι] (S : GridCubeSlice ι N) :
    RankedSubsetCell S where
  subsets := Finset.univ
  nonempty := by
    rcases S.nonempty_vertices with ⟨a, ha⟩
    have haCell : a ∈ S.toSmallCell.vertices := by
      simpa [GridCubeSlice.toSmallCell] using ha
    exact ⟨⟨S.raisedSet a, S.raisedSet_card_eq_rank haCell⟩, Finset.mem_univ _⟩

theorem full_toSmallCell_vertices [DecidableEq ι] (S : GridCubeSlice ι N) :
    (full S).toSmallCell.vertices = S.toSmallCell.vertices := by
  classical
  ext a
  constructor
  · intro ha
    exact toSmallCell_vertices_subset_cubeSlice (full S) ha
  · intro ha
    rw [toSmallCell_vertices]
    refine Finset.mem_image.mpr ?_
    refine ⟨⟨S.raisedSet a, S.raisedSet_card_eq_rank ha⟩, Finset.mem_univ _, ?_⟩
    exact S.vertexOfRaisedSet_raisedSet ha

@[simp] theorem full_toSmallCell [DecidableEq ι] (S : GridCubeSlice ι N) :
    (full S).toSmallCell = S.toSmallCell := by
  exact GridSmallCell.ext (full_toSmallCell_vertices S)

end RankedSubsetCell

namespace RankedSubsetPathCell

variable [DecidableEq ι] {S : GridCubeSlice ι N}

/-- The vertices of the induced small cell, expressed directly from the chain. -/
noncomputable def vertices
    (P : RankedSubsetPathCell S) : Finset (SimplexGrid ι N) :=
  S.verticesOfRankedSubsets P.chain.toFinset

@[simp] theorem vertices_eq_toSmallCell_vertices
    (P : RankedSubsetPathCell S) :
    P.vertices = P.toRankedSubsetCell.toSmallCell.vertices := by
  classical
  ext a
  simp [vertices, GridCubeSlice.mem_verticesOfRankedSubsets_iff,
    RankedSubsetCell.toSmallCell_vertices, toRankedSubsetCell]

/-- A path cell has as many geometric vertices as entries in its chain. -/
theorem vertices_card_eq_chain_length
    (P : RankedSubsetPathCell S) :
    P.vertices.card = P.chain.length := by
  classical
  rw [vertices, GridCubeSlice.verticesOfRankedSubsets_card_eq]
  exact List.toFinset_card_of_nodup P.nodup

theorem toSmallCell_vertices_card_eq_chain_length
    (P : RankedSubsetPathCell S) :
    P.toRankedSubsetCell.toSmallCell.vertices.card = P.chain.length := by
  rw [← P.vertices_eq_toSmallCell_vertices, P.vertices_card_eq_chain_length]

theorem injOn_label_vertices_of_fullyLabeled_chain_length_eq_card
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N)
    (hfull : P.toRankedSubsetCell.toSmallCell.FullyLabeled L)
    (hlen : P.chain.length = Fintype.card ι) :
    Set.InjOn L.label P.vertices := by
  classical
  have hfull_vertices : L.FullyLabeledOn P.vertices := by
    simpa [P.vertices_eq_toSmallCell_vertices] using hfull
  have hcard : P.vertices.card = Fintype.card ι := by
    rw [P.vertices_card_eq_chain_length, hlen]
  exact L.injOn_label_of_fullyLabeledOn_card_eq hfull_vertices hcard

theorem eq_of_mem_vertices_of_label_eq_of_fullyLabeled_chain_length_eq_card
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N)
    (hfull : P.toRankedSubsetCell.toSmallCell.FullyLabeled L)
    (hlen : P.chain.length = Fintype.card ι)
    {a b : SimplexGrid ι N} (ha : a ∈ P.vertices) (hb : b ∈ P.vertices)
    (hlabel : L.label a = L.label b) :
    a = b :=
  P.injOn_label_vertices_of_fullyLabeled_chain_length_eq_card
    L hfull hlen ha hb hlabel

/-- The `i`th ranked subset in a path cell. -/
def chainVertex
    (P : RankedSubsetPathCell S) (i : Fin P.chain.length) :
    {R : Finset ι // R.card = S.rank} :=
  P.chain.get i

theorem chainVertex_mem
    (P : RankedSubsetPathCell S) (i : Fin P.chain.length) :
    P.chainVertex i ∈ P.chain := by
  exact List.get_mem _ _

theorem chainVertex_injective
    (P : RankedSubsetPathCell S) :
    Function.Injective P.chainVertex := by
  intro i j hij
  exact P.nodup.injective_get hij

@[simp] theorem cyclicWindow_chainVertex
    {d : ℕ} (S : GridCubeSlice (Fin d) N) (hd : 0 < d)
    (hrpos : 0 < S.rank) (hrlt : S.rank < d)
    (i : Fin (cyclicWindow S hd hrpos hrlt).chain.length) :
    (cyclicWindow S hd hrpos hrlt).chainVertex i =
      S.cyclicWindowRankedSubset hd i.1 := by
  simp [chainVertex, cyclicWindow, GridCubeSlice.cyclicWindowChain]

theorem exists_chainVertex_eq_of_mem
    (P : RankedSubsetPathCell S)
    {R : {R : Finset ι // R.card = S.rank}} (hR : R ∈ P.chain) :
    ∃ i : Fin P.chain.length, P.chainVertex i = R := by
  rw [List.mem_iff_get] at hR
  rcases hR with ⟨i, hi⟩
  exact ⟨i, hi⟩

theorem mem_vertices_iff_exists_chainVertex
    (P : RankedSubsetPathCell S) {a : SimplexGrid ι N} :
    a ∈ P.vertices ↔
      ∃ i : Fin P.chain.length,
        S.vertexOfRaisedSet (P.chainVertex i).1 (by
          rw [(P.chainVertex i).2]
          exact S.lowerSum_add_rank_eq) = a := by
  classical
  constructor
  · intro ha
    rw [vertices, GridCubeSlice.mem_verticesOfRankedSubsets_iff] at ha
    rcases ha with ⟨R, hR, hvertex⟩
    have hRchain : R ∈ P.chain := by simpa using hR
    rcases P.exists_chainVertex_eq_of_mem hRchain with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simpa [hi] using hvertex
  · rintro ⟨i, hvertex⟩
    rw [vertices, GridCubeSlice.mem_verticesOfRankedSubsets_iff]
    refine ⟨P.chainVertex i, ?_, hvertex⟩
    simpa using P.chainVertex_mem i

/-- Ranked subsets common to two path cells in the same cube slice. -/
noncomputable def commonSubsets
    (P Q : RankedSubsetPathCell S) :
    Finset {R : Finset ι // R.card = S.rank} :=
  P.chain.toFinset ∩ Q.chain.toFinset

@[simp] theorem mem_commonSubsets_iff
    (P Q : RankedSubsetPathCell S)
    {R : {R : Finset ι // R.card = S.rank}} :
    R ∈ P.commonSubsets Q ↔ R ∈ P.chain ∧ R ∈ Q.chain := by
  classical
  simp [commonSubsets]

theorem commonSubsets_subset_left
    (P Q : RankedSubsetPathCell S) :
    P.commonSubsets Q ⊆ P.toRankedSubsetCell.subsets := by
  classical
  intro R hR
  rw [toRankedSubsetCell_subsets]
  simpa using ((P.mem_commonSubsets_iff Q).mp hR).1

theorem commonSubsets_subset_right
    (P Q : RankedSubsetPathCell S) :
    P.commonSubsets Q ⊆ Q.toRankedSubsetCell.subsets := by
  classical
  intro R hR
  rw [toRankedSubsetCell_subsets]
  simpa using ((P.mem_commonSubsets_iff Q).mp hR).2

theorem sharedFace_of_subsets
    (P Q : RankedSubsetPathCell S)
    {subsets : Finset {R : Finset ι // R.card = S.rank}}
    (hsubsets : subsets.Nonempty)
    (hP : subsets ⊆ P.chain.toFinset)
    (hQ : subsets ⊆ Q.chain.toFinset) :
    GridSmallCell.SharedFace
      P.toRankedSubsetCell.toSmallCell Q.toRankedSubsetCell.toSmallCell
      (S.verticesOfRankedSubsets subsets) := by
  classical
  exact RankedSubsetCell.sharedFace_of_commonSubsets
    P.toRankedSubsetCell Q.toRankedSubsetCell hsubsets
    (by intro R hR; simpa [toRankedSubsetCell] using hP hR)
    (by intro R hR; simpa [toRankedSubsetCell] using hQ hR)

theorem sharedFace_of_commonSubsets
    (P Q : RankedSubsetPathCell S)
    (hcommon : (P.commonSubsets Q).Nonempty) :
    GridSmallCell.SharedFace
      P.toRankedSubsetCell.toSmallCell Q.toRankedSubsetCell.toSmallCell
      (S.verticesOfRankedSubsets (P.commonSubsets Q)) :=
  RankedSubsetCell.sharedFace_of_commonSubsets
    P.toRankedSubsetCell Q.toRankedSubsetCell hcommon
    (P.commonSubsets_subset_left Q) (P.commonSubsets_subset_right Q)

theorem sharesAlmostFullyLabeledFace_of_commonSubsets
    (P Q : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N)
    (missing : ι)
    (hne :
      P.toRankedSubsetCell.toSmallCell ≠ Q.toRankedSubsetCell.toSmallCell)
    (hcommon : (P.commonSubsets Q).Nonempty)
    (halmost :
      L.AlmostFullyLabeledOn
        (S.verticesOfRankedSubsets (P.commonSubsets Q)) missing) :
    P.toRankedSubsetCell.toSmallCell.SharesAlmostFullyLabeledFace
      Q.toRankedSubsetCell.toSmallCell L missing := by
  exact ⟨hne, S.verticesOfRankedSubsets (P.commonSubsets Q),
    P.sharedFace_of_commonSubsets Q hcommon, halmost⟩

/-- The ranked subsets left after deleting one chain vertex. -/
noncomputable def deleteSubsets
    (P : RankedSubsetPathCell S)
    (R : {R : Finset ι // R.card = S.rank}) :
    Finset {R : Finset ι // R.card = S.rank} :=
  P.chain.toFinset.erase R

theorem deleteSubsets_subset_chain
    (P : RankedSubsetPathCell S)
    (R : {R : Finset ι // R.card = S.rank}) :
    P.deleteSubsets R ⊆ P.chain.toFinset := by
  classical
  intro Q hQ
  exact (Finset.mem_erase.mp hQ).2

theorem deleteSubsets_card_eq
    (P : RankedSubsetPathCell S)
    {R : {R : Finset ι // R.card = S.rank}}
    (hR : R ∈ P.chain) :
    (P.deleteSubsets R).card = P.chain.length - 1 := by
  classical
  rw [deleteSubsets, Finset.card_erase_of_mem]
  · rw [List.toFinset_card_of_nodup P.nodup]
  · simpa using hR

theorem deleteSubsets_nonempty_of_one_lt_length
    (P : RankedSubsetPathCell S)
    {R : {R : Finset ι // R.card = S.rank}}
    (hR : R ∈ P.chain) (hlen : 1 < P.chain.length) :
    (P.deleteSubsets R).Nonempty := by
  classical
  rw [← Finset.card_pos]
  rw [P.deleteSubsets_card_eq hR]
  omega

theorem deleteSubsets_eq_iff
    (P : RankedSubsetPathCell S)
    {R R' : {R : Finset ι // R.card = S.rank}}
    (hR : R ∈ P.chain) :
    P.deleteSubsets R = P.deleteSubsets R' ↔ R = R' := by
  classical
  constructor
  · intro hdelete
    by_contra hne
    have hmemR' : R ∈ P.deleteSubsets R' := by
      rw [deleteSubsets]
      exact Finset.mem_erase.mpr ⟨hne, by simpa using hR⟩
    have hmemR : R ∈ P.deleteSubsets R := by
      simpa [hdelete] using hmemR'
    simp [deleteSubsets] at hmemR
  · intro h
    rw [h]

/-- The face of a path cell obtained by deleting one chain vertex. -/
noncomputable def faceAfterDeleting
    (P : RankedSubsetPathCell S)
    (R : {R : Finset ι // R.card = S.rank}) :
    Finset (SimplexGrid ι N) :=
  S.verticesOfRankedSubsets (P.deleteSubsets R)

theorem faceAfterDeleting_eq_iff
    (P : RankedSubsetPathCell S)
    (R R' : {R : Finset ι // R.card = S.rank}) :
    P.faceAfterDeleting R = P.faceAfterDeleting R' ↔
      P.deleteSubsets R = P.deleteSubsets R' := by
  rw [faceAfterDeleting, faceAfterDeleting,
    S.verticesOfRankedSubsets_eq_iff]

theorem faceAfterDeleting_subset_toSmallCell
    (P : RankedSubsetPathCell S)
    (R : {R : Finset ι // R.card = S.rank}) :
    P.faceAfterDeleting R ⊆ P.toRankedSubsetCell.toSmallCell.vertices := by
  classical
  intro a ha
  rw [faceAfterDeleting, GridCubeSlice.mem_verticesOfRankedSubsets_iff] at ha
  rcases ha with ⟨Q, hQ, rfl⟩
  rw [RankedSubsetCell.toSmallCell_vertices]
  refine Finset.mem_image.mpr ⟨Q, ?_, rfl⟩
  rw [toRankedSubsetCell_subsets]
  exact P.deleteSubsets_subset_chain R hQ

theorem faceAfterDeleting_card_eq
    (P : RankedSubsetPathCell S)
    {R : {R : Finset ι // R.card = S.rank}}
    (hR : R ∈ P.chain) :
    (P.faceAfterDeleting R).card = P.chain.length - 1 := by
  classical
  rw [faceAfterDeleting, GridCubeSlice.verticesOfRankedSubsets_card_eq,
    P.deleteSubsets_card_eq hR]

theorem faceAfterDeleting_nonempty_of_one_lt_length
    (P : RankedSubsetPathCell S)
    {R : {R : Finset ι // R.card = S.rank}}
    (hR : R ∈ P.chain) (hlen : 1 < P.chain.length) :
    (P.faceAfterDeleting R).Nonempty := by
  classical
  rw [← Finset.card_pos]
  rw [P.faceAfterDeleting_card_eq hR]
  omega

theorem faceAfterDeleting_chainVertex_card_eq
    (P : RankedSubsetPathCell S) (i : Fin P.chain.length) :
    (P.faceAfterDeleting (P.chainVertex i)).card = P.chain.length - 1 :=
  P.faceAfterDeleting_card_eq (P.chainVertex_mem i)

theorem faceAfterDeleting_chainVertex_nonempty_of_one_lt_length
    (P : RankedSubsetPathCell S) (i : Fin P.chain.length)
    (hlen : 1 < P.chain.length) :
    (P.faceAfterDeleting (P.chainVertex i)).Nonempty :=
  P.faceAfterDeleting_nonempty_of_one_lt_length (P.chainVertex_mem i) hlen

/--
A codimension-one face of a path cell, represented by the index of the chain
vertex that is omitted.
-/
structure DeletionFacet (P : RankedSubsetPathCell S) where
  omitted : Fin P.chain.length

instance instDecidableEqDeletionFacet (P : RankedSubsetPathCell S) :
    DecidableEq (DeletionFacet P) := by
  intro F G
  by_cases h : F.omitted = G.omitted
  · exact isTrue (by
      cases F
      cases G
      simp at h ⊢
      exact h)
  · exact isFalse fun hFG => h (congrArg DeletionFacet.omitted hFG)

namespace DeletionFacet

variable {P : RankedSubsetPathCell S}

/-- Deletion facets are equivalent to the finite index set of chain vertices. -/
def equivFin (P : RankedSubsetPathCell S) :
    DeletionFacet P ≃ Fin P.chain.length where
  toFun F := F.omitted
  invFun i := ⟨i⟩
  left_inv F := by
    cases F
    rfl
  right_inv i := rfl

noncomputable instance instFintype (P : RankedSubsetPathCell S) :
    Fintype (DeletionFacet P) :=
  Fintype.ofEquiv (Fin P.chain.length) (equivFin P).symm

@[simp] theorem card_fintype (P : RankedSubsetPathCell S) :
    Fintype.card (DeletionFacet P) = P.chain.length := by
  classical
  rw [← Fintype.card_fin P.chain.length]
  exact Fintype.card_congr (equivFin P)

/-- The ranked subset omitted from this facet. -/
def omittedSubset (F : DeletionFacet P) :
    {R : Finset ι // R.card = S.rank} :=
  P.chainVertex F.omitted

@[simp] theorem cyclicWindow_omittedSubset
    {d : ℕ} {S : GridCubeSlice (Fin d) N}
    {hd : 0 < d} {hrpos : 0 < S.rank} {hrlt : S.rank < d}
    (F : DeletionFacet (cyclicWindow S hd hrpos hrlt)) :
    F.omittedSubset = S.cyclicWindowRankedSubset hd F.omitted.1 := by
  simp [omittedSubset]

/-- The grid vertex opposite this deletion facet. -/
noncomputable def omittedVertex (F : DeletionFacet P) :
    SimplexGrid ι N :=
  S.vertexOfRaisedSet F.omittedSubset.1 (by
    rw [F.omittedSubset.2]
    exact S.lowerSum_add_rank_eq)

theorem omittedVertex_mem_cell (F : DeletionFacet P) :
    F.omittedVertex ∈ P.toRankedSubsetCell.toSmallCell.vertices := by
  classical
  rw [omittedVertex, RankedSubsetCell.toSmallCell_vertices]
  refine Finset.mem_image.mpr ⟨F.omittedSubset, ?_, rfl⟩
  rw [toRankedSubsetCell_subsets]
  simpa using P.chainVertex_mem F.omitted

theorem omittedVertex_mem_vertices (F : DeletionFacet P) :
    F.omittedVertex ∈ P.vertices := by
  simpa [P.vertices_eq_toSmallCell_vertices] using F.omittedVertex_mem_cell

theorem eq_of_omittedVertex_eq (F G : DeletionFacet P)
    (homitted : F.omittedVertex = G.omittedVertex) :
    F = G := by
  classical
  have hsubsets : F.omittedSubset = G.omittedSubset := by
    apply Subtype.ext
    have hraised := congrArg S.raisedSet homitted
    simpa [omittedVertex, omittedSubset] using hraised
  have hindex : F.omitted = G.omitted :=
    P.chainVertex_injective hsubsets
  cases F
  cases G
  simp at hindex ⊢
  exact hindex

/-- The ranked subsets remaining in this facet. -/
noncomputable def subsets (F : DeletionFacet P) :
    Finset {R : Finset ι // R.card = S.rank} :=
  P.deleteSubsets F.omittedSubset

@[simp] theorem cyclicWindow_subsets
    {d : ℕ} {S : GridCubeSlice (Fin d) N}
    {hd : 0 < d} {hrpos : 0 < S.rank} {hrlt : S.rank < d}
    (F : DeletionFacet (cyclicWindow S hd hrpos hrlt)) :
    F.subsets =
      (cyclicWindow S hd hrpos hrlt).chain.toFinset.erase
        (S.cyclicWindowRankedSubset hd F.omitted.1) := by
  simp [subsets, deleteSubsets]

/-- In a fixed path cell, a deletion facet is determined by its ranked subsets. -/
theorem subsets_eq_iff (F G : DeletionFacet P) :
    F.subsets = G.subsets ↔ F = G := by
  classical
  constructor
  · intro hsubsets
    have homitted : F.omittedSubset = G.omittedSubset :=
      (P.deleteSubsets_eq_iff (P.chainVertex_mem F.omitted)).mp
        (by simpa [subsets, omittedSubset] using hsubsets)
    have hindex : F.omitted = G.omitted :=
      P.chainVertex_injective homitted
    cases F
    cases G
    simp at hindex ⊢
    exact hindex
  · intro h
    rw [h]

/-- The grid vertices of this facet. -/
noncomputable def vertices (F : DeletionFacet P) :
    Finset (SimplexGrid ι N) :=
  P.faceAfterDeleting F.omittedSubset

theorem mem_vertices_of_mem_cell_vertices_ne_omitted
    (F : DeletionFacet P) {a : SimplexGrid ι N}
    (ha : a ∈ P.vertices) (hne : a ≠ F.omittedVertex) :
    a ∈ F.vertices := by
  classical
  rw [RankedSubsetPathCell.vertices,
    GridCubeSlice.mem_verticesOfRankedSubsets_iff] at ha
  rcases ha with ⟨R, hR, hvertex⟩
  rw [vertices, faceAfterDeleting, GridCubeSlice.mem_verticesOfRankedSubsets_iff]
  refine ⟨R, ?_, hvertex⟩
  rw [deleteSubsets]
  refine Finset.mem_erase.mpr ⟨?_, hR⟩
  intro hRomit
  have homitted : F.omittedVertex = a := by
    simpa [omittedVertex, omittedSubset, hRomit] using hvertex
  exact hne homitted.symm

theorem omittedVertex_notMem_vertices (F : DeletionFacet P) :
    F.omittedVertex ∉ F.vertices := by
  classical
  intro hmem
  rw [vertices, faceAfterDeleting,
    GridCubeSlice.mem_verticesOfRankedSubsets_iff] at hmem
  rcases hmem with ⟨R, hR, hvertex⟩
  have hRomitted : R = F.omittedSubset := by
    apply Subtype.ext
    have hraised := congrArg S.raisedSet hvertex
    simpa [omittedVertex, omittedSubset] using hraised
  have hnot : R ≠ F.omittedSubset := (Finset.mem_erase.mp hR).1
  exact hnot hRomitted

/-- Boundary-coordinate criterion for all vertices of a deletion facet. -/
theorem vertices_coord_eq_zero_of_lower_eq_zero_of_not_mem
    (F : DeletionFacet P) {i : ι}
    (hlower : (S.lower i : ℕ) = 0)
    (hnot : ∀ R ∈ F.subsets, i ∉ R.1) :
    ∀ a ∈ F.vertices, a.1 i = 0 := by
  classical
  simpa [vertices, faceAfterDeleting, subsets] using
    S.verticesOfRankedSubsets_coord_eq_zero_of_lower_eq_zero_of_not_mem
      hlower hnot

/-- A Sperner label is absent from a deletion facet lying in `i = 0`. -/
theorem label_notMem_of_boundary_coord
    (F : DeletionFacet P) (L : GridSpernerLabeling ι N) {i : ι}
    (hlower : (S.lower i : ℕ) = 0)
    (hnot : ∀ R ∈ F.subsets, i ∉ R.1) :
    i ∉ L.labelsOn F.vertices :=
  L.label_notMem_labelsOn_of_coord_eq_zero F.vertices
    (F.vertices_coord_eq_zero_of_lower_eq_zero_of_not_mem hlower hnot)

/--
For path cells in the same cube slice, deletion facets have the same geometric
face exactly when their remaining ranked subsets agree.
-/
theorem vertices_eq_iff_subsets_eq_same_slice
    {P Q : RankedSubsetPathCell S}
    (F : DeletionFacet P) (G : DeletionFacet Q) :
    F.vertices = G.vertices ↔ F.subsets = G.subsets := by
  rw [vertices, vertices, faceAfterDeleting, faceAfterDeleting,
    subsets, subsets, S.verticesOfRankedSubsets_eq_iff]

/-- In a fixed path cell, a deletion facet is determined by its grid face. -/
theorem vertices_eq_iff (F G : DeletionFacet P) :
    F.vertices = G.vertices ↔ F = G := by
  classical
  constructor
  · intro hvertices
    have hsubsets : F.subsets = G.subsets := by
      have hdelete :
          P.deleteSubsets F.omittedSubset =
            P.deleteSubsets G.omittedSubset :=
        (P.faceAfterDeleting_eq_iff F.omittedSubset G.omittedSubset).mp
          (by simpa [vertices] using hvertices)
      simpa [subsets] using hdelete
    exact (subsets_eq_iff F G).mp hsubsets
  · intro h
    rw [h]

theorem subsets_card_eq (F : DeletionFacet P) :
    F.subsets.card = P.chain.length - 1 :=
  P.deleteSubsets_card_eq (P.chainVertex_mem F.omitted)

theorem subsets_nonempty_of_one_lt_length
    (F : DeletionFacet P) (hlen : 1 < P.chain.length) :
    F.subsets.Nonempty := by
  classical
  rw [← Finset.card_pos]
  rw [F.subsets_card_eq]
  omega

theorem vertices_card_eq (F : DeletionFacet P) :
    F.vertices.card = P.chain.length - 1 :=
  P.faceAfterDeleting_chainVertex_card_eq F.omitted

theorem vertices_subset_cell (F : DeletionFacet P) :
    F.vertices ⊆ P.toRankedSubsetCell.toSmallCell.vertices :=
  P.faceAfterDeleting_subset_toSmallCell F.omittedSubset

theorem vertices_nonempty_of_one_lt_length
    (F : DeletionFacet P) (hlen : 1 < P.chain.length) :
    F.vertices.Nonempty :=
  P.faceAfterDeleting_chainVertex_nonempty_of_one_lt_length F.omitted hlen

theorem sharedFace_self
    (F : DeletionFacet P) (hlen : 1 < P.chain.length) :
    GridSmallCell.SharedFace
      P.toRankedSubsetCell.toSmallCell P.toRankedSubsetCell.toSmallCell
      F.vertices where
  nonempty := F.vertices_nonempty_of_one_lt_length hlen
  subset_left := F.vertices_subset_cell
  subset_right := F.vertices_subset_cell

/-- A deletion facet contains every label except possibly `missing`. -/
def AlmostFullyLabeled
    (F : DeletionFacet P) (L : GridSpernerLabeling ι N) (missing : ι) :
    Prop :=
  L.AlmostFullyLabeledOn F.vertices missing

theorem not_almostFullyLabeled_of_chain_length_eq_one [Nontrivial ι]
    (F : DeletionFacet P) (L : GridSpernerLabeling ι N) (missing : ι)
    (hlen : P.chain.length = 1) :
    ¬ F.AlmostFullyLabeled L missing := by
  classical
  intro halmost
  have hcard : F.vertices.card = 0 := by
    rw [F.vertices_card_eq, hlen]
  have hempty : F.vertices = ∅ := Finset.card_eq_zero.mp hcard
  exact L.not_almostFullyLabeledOn_empty missing (by
    simpa [AlmostFullyLabeled, hempty] using halmost)

/-- The deletion facets of a path cell that are almost fully labeled. -/
noncomputable def almostFullyLabeledFacets
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N) (missing : ι) :
    Finset (DeletionFacet P) := by
  classical
  exact Finset.univ.filter fun F => F.AlmostFullyLabeled L missing

theorem mem_almostFullyLabeledFacets_iff
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N) (missing : ι)
    {F : DeletionFacet P} :
    F ∈ almostFullyLabeledFacets P L missing ↔
      F.AlmostFullyLabeled L missing := by
  classical
  simp [almostFullyLabeledFacets]

/-- Number of almost fully labeled deletion facets in a path cell. -/
noncomputable def almostFullyLabeledFacetCount
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N) (missing : ι) :
    ℕ :=
  (almostFullyLabeledFacets P L missing).card

theorem almostFullyLabeledFacetCount_eq_card
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N) (missing : ι) :
    almostFullyLabeledFacetCount P L missing =
      (almostFullyLabeledFacets P L missing).card :=
  rfl

theorem fullyLabeled_cell_of_almostFullyLabeled_omitted_label
    (F : DeletionFacet P) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : F.AlmostFullyLabeled L missing)
    (hlabel : L.label F.omittedVertex = missing) :
    P.toRankedSubsetCell.toSmallCell.FullyLabeled L := by
  classical
  rw [GridSmallCell.fullyLabeled_iff]
  intro i
  by_cases hi : i = missing
  · refine ⟨F.omittedVertex, F.omittedVertex_mem_cell, ?_⟩
    simpa [hi] using hlabel
  · rcases (GridSpernerLabeling.almostFullyLabeledOn_iff
      L F.vertices missing).mp halmost i hi with
      ⟨a, ha, hlabela⟩
    exact ⟨a, F.vertices_subset_cell ha, hlabela⟩

theorem omitted_label_ne_of_almostFullyLabeled_not_full
    (F : DeletionFacet P) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : F.AlmostFullyLabeled L missing)
    (hnot_full : ¬ P.toRankedSubsetCell.toSmallCell.FullyLabeled L) :
    L.label F.omittedVertex ≠ missing := by
  intro hlabel
  exact hnot_full
    (F.fullyLabeled_cell_of_almostFullyLabeled_omitted_label
      L missing halmost hlabel)

theorem missing_notMem_labelsOn_of_almostFullyLabeled_not_full
    (F : DeletionFacet P) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : F.AlmostFullyLabeled L missing)
    (hnot_full : ¬ P.toRankedSubsetCell.toSmallCell.FullyLabeled L) :
    missing ∉ L.labelsOn F.vertices := by
  intro hmissing
  have hfullFacet :
      L.FullyLabeledOn F.vertices :=
    halmost.fullyLabeledOn_of_missing_mem hmissing
  exact hnot_full (by
    rw [GridSmallCell.fullyLabeled_iff]
    intro i
    rcases (GridSpernerLabeling.fullyLabeledOn_iff
        L F.vertices).mp hfullFacet i with
      ⟨a, ha, hlabela⟩
    exact ⟨a, F.vertices_subset_cell ha, hlabela⟩)

theorem injOn_label_vertices_of_almostFullyLabeled_not_full_chain_length_eq_card
    (F : DeletionFacet P) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : F.AlmostFullyLabeled L missing)
    (hnot_full : ¬ P.toRankedSubsetCell.toSmallCell.FullyLabeled L)
    (hlen : P.chain.length = Fintype.card ι) :
    Set.InjOn L.label F.vertices := by
  classical
  have hmissing :=
    F.missing_notMem_labelsOn_of_almostFullyLabeled_not_full
      L missing halmost hnot_full
  have hcard : F.vertices.card = Fintype.card ι - 1 := by
    rw [F.vertices_card_eq, hlen]
  exact L.injOn_label_of_almostFullyLabeledOn_notMem_card_eq
    halmost hmissing hcard

theorem sharedFace_of_subsets_eq
    {P Q : RankedSubsetPathCell S}
    (F : DeletionFacet P) (G : DeletionFacet Q)
    (hne : F.subsets.Nonempty)
    (hsubsets : F.subsets = G.subsets) :
    GridSmallCell.SharedFace
      P.toRankedSubsetCell.toSmallCell Q.toRankedSubsetCell.toSmallCell
      F.vertices := by
  classical
  rw [vertices, faceAfterDeleting]
  exact P.sharedFace_of_subsets Q hne
    (by
      intro A hA
      simpa [subsets, omittedSubset] using
        P.deleteSubsets_subset_chain F.omittedSubset hA)
    (by
      intro A hA
      have hAG : A ∈ G.subsets := by
        simpa [← hsubsets] using hA
      simpa [subsets, omittedSubset] using
        Q.deleteSubsets_subset_chain G.omittedSubset hAG)

theorem sharedFace_of_subsets_eq_of_one_lt_length
    {P Q : RankedSubsetPathCell S}
    (F : DeletionFacet P) (G : DeletionFacet Q)
    (hlen : 1 < P.chain.length)
    (hsubsets : F.subsets = G.subsets) :
    GridSmallCell.SharedFace
      P.toRankedSubsetCell.toSmallCell Q.toRankedSubsetCell.toSmallCell
      F.vertices :=
  F.sharedFace_of_subsets_eq G
    (F.subsets_nonempty_of_one_lt_length hlen) hsubsets

theorem sharesAlmostFullyLabeledFace_of_subsets_eq
    {P Q : RankedSubsetPathCell S}
    (F : DeletionFacet P) (G : DeletionFacet Q)
    (L : GridSpernerLabeling ι N) (missing : ι)
    (hne_cells :
      P.toRankedSubsetCell.toSmallCell ≠ Q.toRankedSubsetCell.toSmallCell)
    (hne : F.subsets.Nonempty)
    (hsubsets : F.subsets = G.subsets)
    (halmost : L.AlmostFullyLabeledOn F.vertices missing) :
    P.toRankedSubsetCell.toSmallCell.SharesAlmostFullyLabeledFace
      Q.toRankedSubsetCell.toSmallCell L missing := by
  classical
  exact ⟨hne_cells, F.vertices,
    F.sharedFace_of_subsets_eq G hne hsubsets, halmost⟩

end DeletionFacet

/-- The deletion facets of a path cell that are almost fully labeled. -/
noncomputable abbrev almostFullyLabeledFacets
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N) (missing : ι) :
    Finset (DeletionFacet P) :=
  DeletionFacet.almostFullyLabeledFacets P L missing

theorem mem_almostFullyLabeledFacets_iff
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N) (missing : ι)
    {F : DeletionFacet P} :
    F ∈ P.almostFullyLabeledFacets L missing ↔
      F.AlmostFullyLabeled L missing :=
  DeletionFacet.mem_almostFullyLabeledFacets_iff P L missing

/-- Number of almost fully labeled deletion facets in a path cell. -/
noncomputable abbrev almostFullyLabeledFacetCount
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N) (missing : ι) :
    ℕ :=
  DeletionFacet.almostFullyLabeledFacetCount P L missing

theorem almostFullyLabeledFacetCount_eq_card
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N) (missing : ι) :
    P.almostFullyLabeledFacetCount L missing =
      (P.almostFullyLabeledFacets L missing).card :=
  rfl

theorem exists_almostFullyLabeledFacet_omitted_label
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N) (missing : ι)
    (hfull : P.toRankedSubsetCell.toSmallCell.FullyLabeled L) :
    ∃ F : DeletionFacet P,
      F.AlmostFullyLabeled L missing ∧ L.label F.omittedVertex = missing := by
  classical
  rcases (GridSmallCell.fullyLabeled_iff
      P.toRankedSubsetCell.toSmallCell L).mp hfull missing with
    ⟨a, haCell, hlabela⟩
  have haVertices : a ∈ P.vertices := by
    simpa [P.vertices_eq_toSmallCell_vertices] using haCell
  rcases P.mem_vertices_iff_exists_chainVertex.mp haVertices with ⟨i, hvertex⟩
  let F : DeletionFacet P := ⟨i⟩
  have homitted : F.omittedVertex = a := by
    simpa [F, DeletionFacet.omittedVertex, DeletionFacet.omittedSubset] using hvertex
  have hlabel_omitted : L.label F.omittedVertex = missing := by
    simpa [homitted] using hlabela
  refine ⟨F, ?_, hlabel_omitted⟩
  rw [DeletionFacet.AlmostFullyLabeled,
    GridSpernerLabeling.almostFullyLabeledOn_iff]
  intro j hj
  rcases (GridSmallCell.fullyLabeled_iff
      P.toRankedSubsetCell.toSmallCell L).mp hfull j with
    ⟨b, hbCell, hlabelb⟩
  have hbVertices : b ∈ P.vertices := by
    simpa [P.vertices_eq_toSmallCell_vertices] using hbCell
  have hb_ne : b ≠ F.omittedVertex := by
    intro hb_eq
    have hlabel_missing : L.label b = missing := by
      simpa [hb_eq] using hlabel_omitted
    exact hj (hlabelb.symm.trans hlabel_missing)
  exact ⟨b, F.mem_vertices_of_mem_cell_vertices_ne_omitted hbVertices hb_ne,
    hlabelb⟩

theorem deletionFacet_eq_of_omitted_label_eq_of_fullyLabeled_chain_length_eq_card
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N)
    (hfull : P.toRankedSubsetCell.toSmallCell.FullyLabeled L)
    (hlen : P.chain.length = Fintype.card ι)
    {F G : DeletionFacet P} {label : ι}
    (hF : L.label F.omittedVertex = label)
    (hG : L.label G.omittedVertex = label) :
    F = G := by
  classical
  have homitted :
      F.omittedVertex = G.omittedVertex :=
    P.eq_of_mem_vertices_of_label_eq_of_fullyLabeled_chain_length_eq_card
      L hfull hlen F.omittedVertex_mem_vertices G.omittedVertex_mem_vertices
      (hF.trans hG.symm)
  exact F.eq_of_omittedVertex_eq G homitted

theorem omitted_label_eq_of_almostFullyLabeled_of_fullyLabeled_chain_length_eq_card
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N)
    (missing : ι)
    (hfull : P.toRankedSubsetCell.toSmallCell.FullyLabeled L)
    (hlen : P.chain.length = Fintype.card ι)
    {F : DeletionFacet P} (halmost : F.AlmostFullyLabeled L missing) :
    L.label F.omittedVertex = missing := by
  classical
  by_contra hne
  rcases (GridSpernerLabeling.almostFullyLabeledOn_iff
      L F.vertices missing).mp halmost (L.label F.omittedVertex) hne with
    ⟨a, haF, hlabela⟩
  have haP : a ∈ P.vertices := by
    have haCell : a ∈ P.toRankedSubsetCell.toSmallCell.vertices :=
      F.vertices_subset_cell haF
    simpa [P.vertices_eq_toSmallCell_vertices] using haCell
  have ha_omitted :
      a = F.omittedVertex :=
    P.eq_of_mem_vertices_of_label_eq_of_fullyLabeled_chain_length_eq_card
      L hfull hlen haP F.omittedVertex_mem_vertices hlabela
  exact F.omittedVertex_notMem_vertices (by simpa [ha_omitted] using haF)

theorem deletionFacet_eq_of_almostFullyLabeled_of_fullyLabeled_chain_length_eq_card
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N)
    (missing : ι)
    (hfull : P.toRankedSubsetCell.toSmallCell.FullyLabeled L)
    (hlen : P.chain.length = Fintype.card ι)
    {F G : DeletionFacet P}
    (hF : F.AlmostFullyLabeled L missing)
    (hG : G.AlmostFullyLabeled L missing) :
    F = G := by
  classical
  exact P.deletionFacet_eq_of_omitted_label_eq_of_fullyLabeled_chain_length_eq_card
    L hfull hlen
    (P.omitted_label_eq_of_almostFullyLabeled_of_fullyLabeled_chain_length_eq_card
      L missing hfull hlen hF)
    (P.omitted_label_eq_of_almostFullyLabeled_of_fullyLabeled_chain_length_eq_card
      L missing hfull hlen hG)

theorem almostFullyLabeledFacetCount_eq_one_of_fullyLabeled_chain_length_eq_card
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N)
    (missing : ι)
    (hfull : P.toRankedSubsetCell.toSmallCell.FullyLabeled L)
    (hlen : P.chain.length = Fintype.card ι) :
    P.almostFullyLabeledFacetCount L missing = 1 := by
  classical
  rcases P.exists_almostFullyLabeledFacet_omitted_label L missing hfull with
    ⟨F, hF, _hlabelF⟩
  have hfacets : P.almostFullyLabeledFacets L missing = {F} := by
    ext G
    rw [mem_almostFullyLabeledFacets_iff]
    constructor
    · intro hG
      exact Finset.mem_singleton.mpr
        (P.deletionFacet_eq_of_almostFullyLabeled_of_fullyLabeled_chain_length_eq_card
          L missing hfull hlen hG hF)
    · intro hG
      have hGF : G = F := Finset.mem_singleton.mp hG
      simpa [hGF] using hF
  rw [almostFullyLabeledFacetCount_eq_card, hfacets, Finset.card_singleton]

theorem exists_ne_almostFullyLabeledFacet_of_almostFullyLabeled_not_full
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N)
    (missing : ι) {F : DeletionFacet P}
    (halmost : F.AlmostFullyLabeled L missing)
    (hnot_full : ¬ P.toRankedSubsetCell.toSmallCell.FullyLabeled L) :
    ∃ G : DeletionFacet P, G ≠ F ∧ G.AlmostFullyLabeled L missing := by
  classical
  let repeatedLabel := L.label F.omittedVertex
  have hrepeated_ne_missing : repeatedLabel ≠ missing :=
    F.omitted_label_ne_of_almostFullyLabeled_not_full
      L missing halmost hnot_full
  rcases (GridSpernerLabeling.almostFullyLabeledOn_iff
      L F.vertices missing).mp halmost repeatedLabel hrepeated_ne_missing with
    ⟨a, haF, hlabela⟩
  have haP : a ∈ P.vertices := by
    have haCell : a ∈ P.toRankedSubsetCell.toSmallCell.vertices :=
      F.vertices_subset_cell haF
    simpa [P.vertices_eq_toSmallCell_vertices] using haCell
  rcases P.mem_vertices_iff_exists_chainVertex.mp haP with ⟨i, hvertex⟩
  let G : DeletionFacet P := ⟨i⟩
  have hG_omitted : G.omittedVertex = a := by
    simpa [G, DeletionFacet.omittedVertex, DeletionFacet.omittedSubset] using hvertex
  have hF_omitted_ne_a : F.omittedVertex ≠ a := by
    intro hFa
    exact F.omittedVertex_notMem_vertices (by simpa [hFa] using haF)
  have hG_ne_F : G ≠ F := by
    intro hGF
    exact hF_omitted_ne_a (by simpa [hGF] using hG_omitted)
  refine ⟨G, hG_ne_F, ?_⟩
  rw [DeletionFacet.AlmostFullyLabeled,
    GridSpernerLabeling.almostFullyLabeledOn_iff]
  intro j hj
  by_cases hjrepeated : j = repeatedLabel
  · refine ⟨F.omittedVertex, ?_, ?_⟩
    · exact G.mem_vertices_of_mem_cell_vertices_ne_omitted
        F.omittedVertex_mem_vertices (by
          intro hEq
          exact hF_omitted_ne_a (by simpa [hG_omitted] using hEq))
    · simp [repeatedLabel, hjrepeated]
  · rcases (GridSpernerLabeling.almostFullyLabeledOn_iff
      L F.vertices missing).mp halmost j hj with
      ⟨b, hbF, hlabelb⟩
    have hbP : b ∈ P.vertices := by
      have hbCell : b ∈ P.toRankedSubsetCell.toSmallCell.vertices :=
        F.vertices_subset_cell hbF
      simpa [P.vertices_eq_toSmallCell_vertices] using hbCell
    refine ⟨b, ?_, hlabelb⟩
    exact G.mem_vertices_of_mem_cell_vertices_ne_omitted hbP (by
      intro hbG
      have hb_a : b = a := by simpa [hG_omitted] using hbG
      have hj_eq_repeated : j = repeatedLabel := by
        calc
          j = L.label b := hlabelb.symm
          _ = L.label a := by rw [hb_a]
          _ = repeatedLabel := hlabela
      exact hjrepeated hj_eq_repeated)

theorem omitted_label_eq_of_almostFullyLabeled_of_reference_not_full_chain_length_eq_card
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N)
    (missing : ι) {F H : DeletionFacet P}
    (hF : F.AlmostFullyLabeled L missing)
    (hH : H.AlmostFullyLabeled L missing)
    (hnot_full : ¬ P.toRankedSubsetCell.toSmallCell.FullyLabeled L)
    (hlen : P.chain.length = Fintype.card ι) :
    L.label H.omittedVertex = L.label F.omittedVertex := by
  classical
  by_contra hne
  have hH_label_ne_missing : L.label H.omittedVertex ≠ missing :=
    H.omitted_label_ne_of_almostFullyLabeled_not_full
      L missing hH hnot_full
  rcases (GridSpernerLabeling.almostFullyLabeledOn_iff
      L H.vertices missing).mp hH
      (L.label H.omittedVertex) hH_label_ne_missing with
    ⟨a, haH, hlabela⟩
  have haP : a ∈ P.vertices := by
    have haCell : a ∈ P.toRankedSubsetCell.toSmallCell.vertices :=
      H.vertices_subset_cell haH
    simpa [P.vertices_eq_toSmallCell_vertices] using haCell
  have hH_omitted_ne_F : H.omittedVertex ≠ F.omittedVertex := by
    intro hEq
    exact hne (by simp [hEq])
  have ha_ne_F : a ≠ F.omittedVertex := by
    intro hEq
    exact hne (by
      calc
        L.label H.omittedVertex = L.label a := hlabela.symm
        _ = L.label F.omittedVertex := by rw [hEq])
  have hH_in_F : H.omittedVertex ∈ F.vertices :=
    F.mem_vertices_of_mem_cell_vertices_ne_omitted
      H.omittedVertex_mem_vertices hH_omitted_ne_F
  have ha_in_F : a ∈ F.vertices :=
    F.mem_vertices_of_mem_cell_vertices_ne_omitted haP ha_ne_F
  have hinj :=
    F.injOn_label_vertices_of_almostFullyLabeled_not_full_chain_length_eq_card
      L missing hF hnot_full hlen
  have ha_eq_H : a = H.omittedVertex :=
    hinj ha_in_F hH_in_F hlabela
  exact H.omittedVertex_notMem_vertices (by simpa [ha_eq_H] using haH)

theorem two_le_almostFullyLabeledFacetCount_of_almostFullyLabeled_not_full
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N)
    (missing : ι) {F : DeletionFacet P}
    (halmost : F.AlmostFullyLabeled L missing)
    (hnot_full : ¬ P.toRankedSubsetCell.toSmallCell.FullyLabeled L) :
    2 ≤ P.almostFullyLabeledFacetCount L missing := by
  classical
  rcases P.exists_ne_almostFullyLabeledFacet_of_almostFullyLabeled_not_full
      L missing halmost hnot_full with
    ⟨G, hG_ne_F, hG⟩
  have hpair_subset :
      ({F, G} : Finset (DeletionFacet P)) ⊆
        P.almostFullyLabeledFacets L missing := by
    intro H hH
    rw [Finset.mem_insert, Finset.mem_singleton] at hH
    rw [mem_almostFullyLabeledFacets_iff]
    rcases hH with hHF | hHG
    · simpa [hHF] using halmost
    · simpa [hHG] using hG
  have hpair_card : ({F, G} : Finset (DeletionFacet P)).card = 2 := by
    simp [hG_ne_F.symm]
  have hle :=
    Finset.card_le_card hpair_subset
  rw [hpair_card] at hle
  simpa [almostFullyLabeledFacetCount_eq_card] using hle

theorem almostFullyLabeledFacetCount_eq_two_of_almostFullyLabeled_not_full_chain_length_eq_card
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N)
    (missing : ι) {F : DeletionFacet P}
    (halmost : F.AlmostFullyLabeled L missing)
    (hnot_full : ¬ P.toRankedSubsetCell.toSmallCell.FullyLabeled L)
    (hlen : P.chain.length = Fintype.card ι) :
    P.almostFullyLabeledFacetCount L missing = 2 := by
  classical
  rcases P.exists_ne_almostFullyLabeledFacet_of_almostFullyLabeled_not_full
      L missing halmost hnot_full with
    ⟨G, hG_ne_F, hG⟩
  have hF_ne_G : F ≠ G := fun hFG => hG_ne_F hFG.symm
  have hfacets :
      P.almostFullyLabeledFacets L missing = {F, G} := by
    ext H
    rw [mem_almostFullyLabeledFacets_iff]
    constructor
    · intro hH
      rw [Finset.mem_insert, Finset.mem_singleton]
      by_cases hH_eq_F : H = F
      · exact Or.inl hH_eq_F
      · right
        have hH_omitted_ne_F : H.omittedVertex ≠ F.omittedVertex := by
          intro hvertex
          exact hH_eq_F (H.eq_of_omittedVertex_eq F hvertex)
        have hG_omitted_ne_F : G.omittedVertex ≠ F.omittedVertex := by
          intro hvertex
          exact hG_ne_F (G.eq_of_omittedVertex_eq F hvertex)
        have hH_in_F : H.omittedVertex ∈ F.vertices :=
          F.mem_vertices_of_mem_cell_vertices_ne_omitted
            H.omittedVertex_mem_vertices hH_omitted_ne_F
        have hG_in_F : G.omittedVertex ∈ F.vertices :=
          F.mem_vertices_of_mem_cell_vertices_ne_omitted
            G.omittedVertex_mem_vertices hG_omitted_ne_F
        have hHlabel :
            L.label H.omittedVertex = L.label F.omittedVertex :=
          P.omitted_label_eq_of_almostFullyLabeled_of_reference_not_full_chain_length_eq_card
            L missing halmost hH hnot_full hlen
        have hGlabel :
            L.label G.omittedVertex = L.label F.omittedVertex :=
          P.omitted_label_eq_of_almostFullyLabeled_of_reference_not_full_chain_length_eq_card
            L missing halmost hG hnot_full hlen
        have hinj :=
          F.injOn_label_vertices_of_almostFullyLabeled_not_full_chain_length_eq_card
            L missing halmost hnot_full hlen
        have hvertices : H.omittedVertex = G.omittedVertex :=
          hinj hH_in_F hG_in_F (hHlabel.trans hGlabel.symm)
        exact H.eq_of_omittedVertex_eq G hvertices
    · intro hH
      rw [Finset.mem_insert, Finset.mem_singleton] at hH
      rcases hH with hHF | hHG
      · simpa [hHF] using halmost
      · simpa [hHG] using hG
  rw [almostFullyLabeledFacetCount_eq_card, hfacets]
  simp [hF_ne_G]

theorem fullyLabeled_of_almostFullyLabeledFacetCount_eq_one
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N)
    (missing : ι)
    (hcount : P.almostFullyLabeledFacetCount L missing = 1) :
    P.toRankedSubsetCell.toSmallCell.FullyLabeled L := by
  classical
  by_contra hnot_full
  have hpos : 0 < (P.almostFullyLabeledFacets L missing).card := by
    rw [← P.almostFullyLabeledFacetCount_eq_card L missing, hcount]
    norm_num
  rcases Finset.card_pos.mp hpos with ⟨F, hFmem⟩
  have halmost : F.AlmostFullyLabeled L missing :=
    (P.mem_almostFullyLabeledFacets_iff L missing).mp hFmem
  have htwo :=
    P.two_le_almostFullyLabeledFacetCount_of_almostFullyLabeled_not_full
      L missing halmost hnot_full
  omega

theorem fullyLabeled_iff_almostFullyLabeledFacetCount_eq_one_of_chain_length_eq_card
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N)
    (missing : ι) (hlen : P.chain.length = Fintype.card ι) :
    P.toRankedSubsetCell.toSmallCell.FullyLabeled L ↔
      P.almostFullyLabeledFacetCount L missing = 1 := by
  constructor
  · intro hfull
    exact P.almostFullyLabeledFacetCount_eq_one_of_fullyLabeled_chain_length_eq_card
      L missing hfull hlen
  · intro hcount
    exact P.fullyLabeled_of_almostFullyLabeledFacetCount_eq_one
      L missing hcount

theorem fullyLabeled_of_odd_almostFullyLabeledFacetCount_chain_length_eq_card
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N)
    (missing : ι) (hlen : P.chain.length = Fintype.card ι)
    (hodd : Odd (P.almostFullyLabeledFacetCount L missing)) :
    P.toRankedSubsetCell.toSmallCell.FullyLabeled L := by
  classical
  by_contra hnot_full
  by_cases hpos : 0 < P.almostFullyLabeledFacetCount L missing
  · have hfacet_pos : 0 < (P.almostFullyLabeledFacets L missing).card := by
      simpa [P.almostFullyLabeledFacetCount_eq_card L missing] using hpos
    rcases Finset.card_pos.mp hfacet_pos with ⟨F, hFmem⟩
    have hF : F.AlmostFullyLabeled L missing :=
      (P.mem_almostFullyLabeledFacets_iff L missing).mp hFmem
    have htwo :=
      P.almostFullyLabeledFacetCount_eq_two_of_almostFullyLabeled_not_full_chain_length_eq_card
        L missing hF hnot_full hlen
    rw [htwo] at hodd
    rcases hodd with ⟨k, hk⟩
    omega
  · have hzero : P.almostFullyLabeledFacetCount L missing = 0 := by
      omega
    rw [hzero] at hodd
    rcases hodd with ⟨k, hk⟩
    omega

theorem odd_almostFullyLabeledFacetCount_iff_fullyLabeled_of_chain_length_eq_card
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N)
    (missing : ι) (hlen : P.chain.length = Fintype.card ι) :
    Odd (P.almostFullyLabeledFacetCount L missing) ↔
      P.toRankedSubsetCell.toSmallCell.FullyLabeled L := by
  constructor
  · intro hodd
    exact P.fullyLabeled_of_odd_almostFullyLabeledFacetCount_chain_length_eq_card
      L missing hlen hodd
  · intro hfull
    rw [P.almostFullyLabeledFacetCount_eq_one_of_fullyLabeled_chain_length_eq_card
      L missing hfull hlen]
    norm_num

theorem cyclicWindow_faceAfterDeleting_card_eq
    {d : ℕ} (S : GridCubeSlice (Fin d) N) (hd : 0 < d)
    (hrpos : 0 < S.rank) (hrlt : S.rank < d) (t : Fin d) :
    ((cyclicWindow S hd hrpos hrlt).faceAfterDeleting
      (S.cyclicWindowRankedSubset hd t.1)).card = d - 1 := by
  classical
  rw [faceAfterDeleting_card_eq
    (P := cyclicWindow S hd hrpos hrlt)
    (R := S.cyclicWindowRankedSubset hd t.1)
    (cyclicWindow_chain_mem S hd hrpos hrlt t)]
  simp

theorem cyclicWindow_faceAfterDeleting_nonempty
    {d : ℕ} (S : GridCubeSlice (Fin d) N) (hd : 0 < d)
    (hrpos : 0 < S.rank) (hrlt : S.rank < d)
    (hdim : 1 < d) (t : Fin d) :
    ((cyclicWindow S hd hrpos hrlt).faceAfterDeleting
      (S.cyclicWindowRankedSubset hd t.1)).Nonempty := by
  classical
  exact (cyclicWindow S hd hrpos hrlt).faceAfterDeleting_nonempty_of_one_lt_length
    (cyclicWindow_chain_mem S hd hrpos hrlt t) (by simpa using hdim)

theorem sharedFace_of_deleteSubsets_eq
    (P Q : RankedSubsetPathCell S)
    {R R' : {R : Finset ι // R.card = S.rank}}
    (hne : (P.deleteSubsets R).Nonempty)
    (hdelete : P.deleteSubsets R = Q.deleteSubsets R') :
    GridSmallCell.SharedFace
      P.toRankedSubsetCell.toSmallCell Q.toRankedSubsetCell.toSmallCell
      (P.faceAfterDeleting R) := by
  classical
  rw [faceAfterDeleting]
  exact P.sharedFace_of_subsets Q hne
    (P.deleteSubsets_subset_chain R)
    (by
      intro A hA
      have hA' : A ∈ Q.deleteSubsets R' := by
        simpa [hdelete] using hA
      exact Q.deleteSubsets_subset_chain R' hA')

theorem sharesAlmostFullyLabeledFace_of_deleteSubsets_eq
    (P Q : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N)
    (missing : ι)
    {R R' : {R : Finset ι // R.card = S.rank}}
    (hne_cells :
      P.toRankedSubsetCell.toSmallCell ≠ Q.toRankedSubsetCell.toSmallCell)
    (hne_face : (P.deleteSubsets R).Nonempty)
    (hdelete : P.deleteSubsets R = Q.deleteSubsets R')
    (halmost : L.AlmostFullyLabeledOn (P.faceAfterDeleting R) missing) :
    P.toRankedSubsetCell.toSmallCell.SharesAlmostFullyLabeledFace
      Q.toRankedSubsetCell.toSmallCell L missing := by
  exact ⟨hne_cells, P.faceAfterDeleting R,
    P.sharedFace_of_deleteSubsets_eq Q hne_face hdelete, halmost⟩

theorem fullyLabeled_toSmallCell_iff
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N) :
    P.toRankedSubsetCell.toSmallCell.FullyLabeled L ↔
      ∀ i : ι, ∃ R ∈ P.chain,
        L.label (S.vertexOfRaisedSet R.1 (by
          rw [R.2]
          exact S.lowerSum_add_rank_eq)) = i := by
  classical
  rw [RankedSubsetCell.fullyLabeled_toSmallCell_iff]
  constructor
  · intro hfull i
    rcases hfull i with ⟨R, hR, hlabel⟩
    exact ⟨R, by simpa [toRankedSubsetCell] using hR, hlabel⟩
  · intro hfull i
    rcases hfull i with ⟨R, hR, hlabel⟩
    exact ⟨R, by simpa [toRankedSubsetCell] using hR, hlabel⟩

theorem almostFullyLabeled_toSmallCell_iff
    (P : RankedSubsetPathCell S) (L : GridSpernerLabeling ι N)
    (missing : ι) :
    P.toRankedSubsetCell.toSmallCell.AlmostFullyLabeled L missing ↔
      ∀ i : ι, i ≠ missing → ∃ R ∈ P.chain,
        L.label (S.vertexOfRaisedSet R.1 (by
          rw [R.2]
          exact S.lowerSum_add_rank_eq)) = i := by
  classical
  rw [RankedSubsetCell.almostFullyLabeled_toSmallCell_iff]
  constructor
  · intro halmost i hi
    rcases halmost i hi with ⟨R, hR, hlabel⟩
    exact ⟨R, by simpa [toRankedSubsetCell] using hR, hlabel⟩
  · intro halmost i hi
    rcases halmost i hi with ⟨R, hR, hlabel⟩
    exact ⟨R, by simpa [toRankedSubsetCell] using hR, hlabel⟩

end RankedSubsetPathCell

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

@[simp] theorem reindex_lower {κ : Type v} [Fintype κ] (e : ι ≃ κ)
    (S : GridCubeSlice ι N) (k : κ) :
    (S.reindex e).lower k = S.lower (e.symm k) :=
  rfl

@[simp] theorem lowerSum_reindex {κ : Type v} [Fintype κ] (e : ι ≃ κ)
    (S : GridCubeSlice ι N) :
    (S.reindex e).lowerSum = S.lowerSum := by
  simpa [lowerSum] using
    Fintype.sum_equiv e.symm
      (fun k : κ => (S.lower (e.symm k) : ℕ))
      (fun i : ι => (S.lower i : ℕ))
      (by intro k; simp)

@[simp] theorem rank_reindex {κ : Type v} [Fintype κ] (e : ι ≃ κ)
    (S : GridCubeSlice ι N) :
    (S.reindex e).rank = S.rank := by
  simp [rank]

@[simp] theorem reindex_symm_reindex {κ : Type v} [Fintype κ] (e : ι ≃ κ)
    (S : GridCubeSlice ι N) :
    (S.reindex e).reindex e.symm = S := by
  cases S
  simp [reindex]

@[simp] theorem reindex_reindex_symm {κ : Type v} [Fintype κ] (e : ι ≃ κ)
    (S : GridCubeSlice κ N) :
    (S.reindex e.symm).reindex e = S := by
  cases S
  simp [reindex]

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

@[simp] theorem raisedSet_reindex {κ : Type v} [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ)
    (S : GridCubeSlice ι N) (a : SimplexGrid ι N) :
    (S.reindex e).raisedSet (SimplexGrid.reindex e a) =
      (S.raisedSet a).map e.toEmbedding := by
  ext k
  rw [mem_raisedSet_iff, Finset.mem_map_equiv, mem_raisedSet_iff]
  simp

/-- Transport a ranked subset of a cube slice along a coordinate equivalence. -/
noncomputable def reindexRankedSubset {κ : Type v} [Fintype κ]
    (e : ι ≃ κ) (S : GridCubeSlice ι N)
    (R : {R : Finset ι // R.card = S.rank}) :
    {R : Finset κ // R.card = (S.reindex e).rank} :=
  ⟨R.1.map e.toEmbedding, by simp [R.2]⟩

@[simp] theorem reindexRankedSubset_val {κ : Type v} [Fintype κ]
    (e : ι ≃ κ) (S : GridCubeSlice ι N)
    (R : {R : Finset ι // R.card = S.rank}) :
    (S.reindexRankedSubset e R).1 = R.1.map e.toEmbedding :=
  rfl

theorem reindexRankedSubset_injective {κ : Type v} [Fintype κ]
    (e : ι ≃ κ) (S : GridCubeSlice ι N) :
    Function.Injective (S.reindexRankedSubset e) := by
  intro R Q hRQ
  apply Subtype.ext
  have hval := congrArg Subtype.val hRQ
  have hback :
      ((R.1.map e.toEmbedding).map e.symm.toEmbedding) =
        ((Q.1.map e.toEmbedding).map e.symm.toEmbedding) := by
    simpa using congrArg (fun T : Finset κ => T.map e.symm.toEmbedding) hval
  simpa [Finset.map_map] using hback

namespace RankedSubsetPathCell

variable [DecidableEq ι] {S : GridCubeSlice ι N}

/-- Transport a path-shaped ranked-subset cell along a coordinate equivalence. -/
noncomputable def reindex {κ : Type v} [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (P : RankedSubsetPathCell S) :
    RankedSubsetPathCell (S.reindex e) where
  chain := P.chain.map (S.reindexRankedSubset e)
  nonempty := by
    intro hnil
    exact P.nonempty (by simpa using hnil)
  nodup := P.nodup.map (S.reindexRankedSubset_injective e)
  step_chain := by
    exact List.isChain_map_of_isChain (S.reindexRankedSubset e)
      (fun R Q hstep => by
        simpa using rankedSubsetStep_map e.toEmbedding hstep)
      P.step_chain

@[simp] theorem reindex_chain {κ : Type v} [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (P : RankedSubsetPathCell S) :
    (P.reindex e).chain = P.chain.map (S.reindexRankedSubset e) :=
  rfl

@[simp] theorem reindex_chain_length {κ : Type v} [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (P : RankedSubsetPathCell S) :
    (P.reindex e).chain.length = P.chain.length := by
  simp [reindex]

/--
A canonical one-vertex path cell obtained by choosing any vertex of the cube
slice. This supplies the degenerate rank `0` and full-rank pieces of the Kuhn
subdivision.
-/
noncomputable def singletonOfSlice
    (S : GridCubeSlice ι N) :
    RankedSubsetPathCell S := by
  classical
  let a : SimplexGrid ι N := Classical.choose S.nonempty_vertices
  have ha : a ∈ cubeSliceVertices N S.lower :=
    Classical.choose_spec S.nonempty_vertices
  have haCell : a ∈ S.toSmallCell.vertices := by
    simpa [GridCubeSlice.toSmallCell] using ha
  exact RankedSubsetPathCell.singleton S
    ⟨S.raisedSet a, S.raisedSet_card_eq_rank haCell⟩

@[simp] theorem singletonOfSlice_chain_length
    (S : GridCubeSlice ι N) :
    (singletonOfSlice S).chain.length = 1 := by
  classical
  unfold singletonOfSlice
  simp

/--
The cyclic-window Freudenthal/Kuhn path cell associated to a chosen coordinate
order `Fin d ≃ κ` on an interior-rank cube slice.
-/
noncomputable def cyclicWindowOfEquiv
    {d : ℕ} {κ : Type v} [Fintype κ] [DecidableEq κ]
    (S : GridCubeSlice κ N) (e : Fin d ≃ κ) (hd : 0 < d)
    (hrpos : 0 < S.rank) (hrlt : S.rank < d) :
    RankedSubsetPathCell S := by
  classical
  let Sfin : GridCubeSlice (Fin d) N := S.reindex e.symm
  let P : RankedSubsetPathCell Sfin :=
    RankedSubsetPathCell.cyclicWindow Sfin hd
      (by simpa [Sfin] using hrpos) (by simpa [Sfin] using hrlt)
  let mapR :
      {R : Finset (Fin d) // R.card = Sfin.rank} →
        {R : Finset κ // R.card = S.rank} :=
    fun R => ⟨R.1.map e.toEmbedding, by simpa [Sfin] using R.2⟩
  have hmapR_inj : Function.Injective mapR := by
    intro R Q hRQ
    apply Subtype.ext
    have hval := congrArg Subtype.val hRQ
    have hback :
        ((R.1.map e.toEmbedding).map e.symm.toEmbedding) =
          ((Q.1.map e.toEmbedding).map e.symm.toEmbedding) := by
      exact congrArg (fun T : Finset κ => T.map e.symm.toEmbedding) hval
    simpa [Finset.map_map] using hback
  exact
    { chain := P.chain.map mapR
      nonempty := by
        intro hnil
        exact P.nonempty (by simpa using hnil)
      nodup := P.nodup.map hmapR_inj
      step_chain := by
        exact List.isChain_map_of_isChain mapR
          (fun R Q hstep => by
            simpa [mapR] using rankedSubsetStep_map e.toEmbedding hstep)
          P.step_chain }

@[simp] theorem cyclicWindowOfEquiv_chain_length
    {d : ℕ} {κ : Type v} [Fintype κ] [DecidableEq κ]
    (S : GridCubeSlice κ N) (e : Fin d ≃ κ) (hd : 0 < d)
    (hrpos : 0 < S.rank) (hrlt : S.rank < d) :
    (cyclicWindowOfEquiv S e hd hrpos hrlt).chain.length = d := by
  unfold cyclicWindowOfEquiv
  simp

@[simp] theorem cyclicWindowOfEquiv_vertices_card
    {d : ℕ} {κ : Type v} [Fintype κ] [DecidableEq κ]
    (S : GridCubeSlice κ N) (e : Fin d ≃ κ) (hd : 0 < d)
    (hrpos : 0 < S.rank) (hrlt : S.rank < d) :
    (cyclicWindowOfEquiv S e hd hrpos hrlt).vertices.card = d := by
  rw [vertices_card_eq_chain_length, cyclicWindowOfEquiv_chain_length]

theorem cyclicWindowOfEquiv_chain_length_eq_card
    {κ : Type v} [Fintype κ] [DecidableEq κ]
    (S : GridCubeSlice κ N) (e : Fin (Fintype.card κ) ≃ κ)
    (hcard : 0 < Fintype.card κ)
    (hrpos : 0 < S.rank) (hrlt : S.rank < Fintype.card κ) :
    (cyclicWindowOfEquiv S e hcard hrpos hrlt).chain.length =
      Fintype.card κ := by
  simp [cyclicWindowOfEquiv_chain_length]

theorem cyclicWindowOfEquiv_odd_almostFullyLabeledFacetCount_iff_fullyLabeled
    {d : ℕ} {κ : Type v} [Fintype κ] [DecidableEq κ]
    (S : GridCubeSlice κ N) (e : Fin d ≃ κ) (hd : 0 < d)
    (hrpos : 0 < S.rank) (hrlt : S.rank < d)
    (L : GridSpernerLabeling κ N) (missing : κ) :
    Odd ((cyclicWindowOfEquiv S e hd hrpos hrlt).almostFullyLabeledFacetCount
      L missing) ↔
      GridSmallCell.FullyLabeled
        ((cyclicWindowOfEquiv S e hd hrpos hrlt).toRankedSubsetCell.toSmallCell)
        L := by
  classical
  have hcard : d = Fintype.card κ := by
    simpa [Fintype.card_fin] using Fintype.card_congr e
  exact odd_almostFullyLabeledFacetCount_iff_fullyLabeled_of_chain_length_eq_card
    (P := cyclicWindowOfEquiv S e hd hrpos hrlt)
    L missing (by rw [cyclicWindowOfEquiv_chain_length, hcard])

end RankedSubsetPathCell

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

@[ext] theorem ext {T T' : GridTriangulation ι N}
    (hcells : T.cells = T'.cells) :
    T = T' := by
  cases T
  cases T'
  cases hcells
  rfl

/-- The Sperner conclusion for a chosen grid triangulation. -/
def HasSpernerProperty [DecidableEq ι] (T : GridTriangulation ι N) : Prop :=
  ∀ L : GridSpernerLabeling ι N,
    ∃ cell ∈ T.cells, cell.FullyLabeled L

/--
The canonical pivot graph whose vertices are cells of a triangulation and
whose edges connect distinct cells sharing an almost fully labeled face.

The hard Sperner work for a concrete triangulation is to prove the local degree
facts for this graph: one boundary endpoint is odd, and every other odd
endpoint is fully labeled.
-/
def almostFacePivotGraph [DecidableEq ι] (T : GridTriangulation ι N)
    (L : GridSpernerLabeling ι N) (missing : ι) :
    SimpleGraph {cell : GridSmallCell ι N // cell ∈ T.cells} where
  Adj cell cell' :=
    cell.1.SharesAlmostFullyLabeledFace cell'.1 L missing
  symm := by
    intro cell cell' h
    exact h.symm
  loopless := ⟨fun cell h => h.1 rfl⟩

/-- The degree in `almostFacePivotGraph`, with decidability hidden classically. -/
noncomputable def almostFacePivotDegree [DecidableEq ι]
    (T : GridTriangulation ι N) (L : GridSpernerLabeling ι N)
    (missing : ι) (cell : {cell : GridSmallCell ι N // cell ∈ T.cells}) :
    ℕ := by
  classical
  exact (T.almostFacePivotGraph L missing).degree cell

/--
A reusable parity certificate for proving the Sperner conclusion from a pivot
graph.

The vertices of `graph` are combinatorial states carrying cells of `T`.
There is one distinguished boundary state with odd degree. By the handshaking
lemma, another odd-degree state exists; the final field says every such
non-boundary state carries a fully labeled cell.
-/
structure PivotGraphCertificate [DecidableEq ι] (T : GridTriangulation ι N)
    (L : GridSpernerLabeling ι N) (V : Type v) [Fintype V] where
  graph : SimpleGraph V
  decidableAdj : DecidableRel graph.Adj
  cellOf : V → GridSmallCell ι N
  cell_mem : ∀ v, cellOf v ∈ T.cells
  boundary : V → Prop
  start : V
  start_boundary : boundary start
  start_odd : Odd (graph.degree start)
  boundary_unique : ∀ v, boundary v → v = start
  odd_nonboundary_full :
    ∀ v, Odd (graph.degree v) → ¬ boundary v → (cellOf v).FullyLabeled L

namespace PivotGraphCertificate

variable [DecidableEq ι] {T : GridTriangulation ι N}
    {L : GridSpernerLabeling ι N} {V : Type v} [Fintype V]

/--
The abstract parity step in Sperner's lemma: an odd boundary endpoint forces
another odd endpoint, and a pivot certificate identifies that endpoint with a
fully labeled cell.
-/
theorem exists_fullyLabeled (C : PivotGraphCertificate T L V) :
    ∃ cell ∈ T.cells, cell.FullyLabeled L := by
  letI := C.decidableAdj
  rcases C.graph.exists_ne_odd_degree_of_exists_odd_degree
      C.start C.start_odd with
    ⟨v, hv_ne, hv_odd⟩
  have hv_not_boundary : ¬ C.boundary v := by
    intro hv_boundary
    exact hv_ne (C.boundary_unique v hv_boundary)
  exact ⟨C.cellOf v, C.cell_mem v,
    C.odd_nonboundary_full v hv_odd hv_not_boundary⟩

end PivotGraphCertificate

/--
A pivot certificate specialized to the canonical almost-labeled shared-face
graph of a triangulation.
-/
structure AlmostFacePivotCertificate [DecidableEq ι]
    (T : GridTriangulation ι N) (L : GridSpernerLabeling ι N)
    (missing : ι) where
  boundary : {cell : GridSmallCell ι N // cell ∈ T.cells} → Prop
  start : {cell : GridSmallCell ι N // cell ∈ T.cells}
  start_boundary : boundary start
  start_odd : Odd (T.almostFacePivotDegree L missing start)
  boundary_unique : ∀ v, boundary v → v = start
  odd_nonboundary_full :
    ∀ v, Odd (T.almostFacePivotDegree L missing v) →
      ¬ boundary v → v.1.FullyLabeled L

namespace AlmostFacePivotCertificate

variable [DecidableEq ι] {T : GridTriangulation ι N}
    {L : GridSpernerLabeling ι N} {missing : ι}

/-- Forget the specialized graph choice and view the data as a generic pivot certificate. -/
noncomputable def toPivotGraphCertificate
    (C : AlmostFacePivotCertificate T L missing) :
    PivotGraphCertificate T L {cell : GridSmallCell ι N // cell ∈ T.cells} := by
  classical
  let G := T.almostFacePivotGraph L missing
  exact
    { graph := G
      decidableAdj := inferInstance
      cellOf := fun cell => cell.1
      cell_mem := fun cell => cell.2
      boundary := C.boundary
      start := C.start
      start_boundary := C.start_boundary
      start_odd := by
        simpa [almostFacePivotDegree, G] using C.start_odd
      boundary_unique := C.boundary_unique
      odd_nonboundary_full := by
        intro v hv_odd hv_boundary
        exact C.odd_nonboundary_full v
          (by simpa [almostFacePivotDegree, G] using hv_odd)
          hv_boundary }

/--
The canonical almost-face pivot certificate produces a fully labeled cell.
-/
theorem exists_fullyLabeled
    (C : AlmostFacePivotCertificate T L missing) :
    ∃ cell ∈ T.cells, cell.FullyLabeled L :=
  C.toPivotGraphCertificate.exists_fullyLabeled

end AlmostFacePivotCertificate

/--
A triangulation has canonical almost-face pivot certificates if every labeling
admits one for some choice of pivot-missing label.
-/
def HasAlmostFacePivotCertificates [DecidableEq ι]
    (T : GridTriangulation ι N) : Prop :=
  ∀ L : GridSpernerLabeling ι N,
    ∃ missing : ι, Nonempty (AlmostFacePivotCertificate T L missing)

/--
A triangulation has pivot certificates if every Sperner labeling admits a
finite pivot graph certificate. This is the reusable target for a constructive
Sperner proof: later geometry only has to build the graph and verify the local
degree facts.
-/
def HasPivotGraphCertificates [DecidableEq ι]
    (T : GridTriangulation ι N) : Prop :=
  ∀ L : GridSpernerLabeling ι N,
    ∃ V : Type u, ∃ _ : Fintype V,
      Nonempty (PivotGraphCertificate T L V)

/--
Canonical almost-face pivot certificates are enough to supply abstract pivot
graph certificates.
-/
theorem hasPivotGraphCertificates_of_almostFacePivotCertificates [DecidableEq ι]
    {T : GridTriangulation ι N}
    (hT : T.HasAlmostFacePivotCertificates) :
    T.HasPivotGraphCertificates := by
  classical
  intro L
  rcases hT L with ⟨missing, hC⟩
  rcases hC with ⟨C⟩
  exact ⟨{cell : GridSmallCell ι N // cell ∈ T.cells}, inferInstance,
    ⟨C.toPivotGraphCertificate⟩⟩

/--
Any triangulation with pivot certificates satisfies Sperner's lemma.
-/
theorem hasSpernerProperty_of_pivotGraphCertificates [DecidableEq ι]
    {T : GridTriangulation ι N}
    (hT : T.HasPivotGraphCertificates) :
    T.HasSpernerProperty := by
  intro L
  rcases hT L with ⟨V, hV, hC⟩
  letI : Fintype V := hV
  rcases hC with ⟨C⟩
  exact C.exists_fullyLabeled

/--
Any triangulation with canonical almost-face pivot certificates satisfies
Sperner's lemma.
-/
theorem hasSpernerProperty_of_almostFacePivotCertificates [DecidableEq ι]
    {T : GridTriangulation ι N}
    (hT : T.HasAlmostFacePivotCertificates) :
    T.HasSpernerProperty :=
  hasSpernerProperty_of_pivotGraphCertificates
    (hasPivotGraphCertificates_of_almostFacePivotCertificates hT)

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

/--
A grid triangulation refines the cube-slice subdivision if every cell is
contained in the vertex set of some nonempty unit-cube slice.
-/
def RefinesCubeSlices [DecidableEq ι] (T : GridTriangulation ι N) : Prop :=
  ∀ cell ∈ T.cells, ∃ S : GridCubeSlice ι N,
    cell.vertices ⊆ S.toSmallCell.vertices

theorem cubeSlices_refinesCubeSlices [DecidableEq ι] :
    (cubeSlices (ι := ι) (N := N)).RefinesCubeSlices := by
  intro cell hcell
  rcases (mem_cubeSlices_iff.mp hcell) with ⟨S, hS⟩
  refine ⟨S, ?_⟩
  intro a ha
  simpa [hS] using ha

/--
A global subdivision whose cells are given combinatorially inside individual
cube slices by ranked-subset cells.
-/
structure CubeSliceRankedSubdivision (ι : Type u) [Fintype ι] (N : ℕ) where
  cells : Finset (Σ S : GridCubeSlice ι N, GridCubeSlice.RankedSubsetCell S)

namespace CubeSliceRankedSubdivision

variable {ι : Type u} [Fintype ι] {N : ℕ}

/-- Forget the ranked-subset descriptions and keep the induced small cells. -/
noncomputable def toTriangulation [DecidableEq ι]
    (U : CubeSliceRankedSubdivision ι N) : GridTriangulation ι N := by
  classical
  exact
    { cells := U.cells.image fun C => C.2.toSmallCell }

theorem toTriangulation_refinesCubeSlices [DecidableEq ι]
    (U : CubeSliceRankedSubdivision ι N) :
    U.toTriangulation.RefinesCubeSlices := by
  classical
  intro cell hcell
  rcases Finset.mem_image.mp hcell with ⟨C, hC, rfl⟩
  exact ⟨C.1, C.2.toSmallCell_vertices_subset_cubeSlice⟩

/-- The ranked-subset presentation of the original all-cube-slices subdivision. -/
noncomputable def full [DecidableEq ι] : CubeSliceRankedSubdivision ι N := by
  classical
  exact
    { cells := (Finset.univ : Finset (GridCubeSlice ι N)).image
        fun S => ⟨S, GridCubeSlice.RankedSubsetCell.full S⟩ }

@[simp] theorem full_toTriangulation [DecidableEq ι] :
    (full (ι := ι) (N := N)).toTriangulation =
      cubeSlices (ι := ι) (N := N) := by
  classical
  apply GridTriangulation.ext
  ext cell
  simp [full, toTriangulation, cubeSlices]

end CubeSliceRankedSubdivision

/--
A global subdivision whose cells are path-shaped ranked-subset cells inside
individual cube slices.

This is the natural output shape for the upcoming Freudenthal/Kuhn
construction: ordered chains carry the pivot/parity combinatorics, while the
forgetful maps below expose the already-built geometric API.
-/
structure CubeSlicePathSubdivision (ι : Type u) [Fintype ι] [DecidableEq ι]
    (N : ℕ) where
  cells : Finset (Σ S : GridCubeSlice ι N, GridCubeSlice.RankedSubsetPathCell S)

namespace CubeSlicePathSubdivision

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- Forget path ordering data and keep the ranked-subset cells. -/
noncomputable def toRankedSubdivision
    (U : CubeSlicePathSubdivision ι N) : CubeSliceRankedSubdivision ι N := by
  classical
  exact
    { cells := U.cells.image fun C =>
        ⟨C.1, C.2.toRankedSubsetCell⟩ }

/-- Forget all combinatorial data and keep the induced small-cell triangulation. -/
noncomputable def toTriangulation
    (U : CubeSlicePathSubdivision ι N) : GridTriangulation ι N :=
  U.toRankedSubdivision.toTriangulation

theorem toTriangulation_refinesCubeSlices
    (U : CubeSlicePathSubdivision ι N) :
    U.toTriangulation.RefinesCubeSlices :=
  U.toRankedSubdivision.toTriangulation_refinesCubeSlices

/--
A facet state of a path subdivision: a path cell belonging to the subdivision
together with one deletion facet of that path cell.
-/
structure FacetState (U : CubeSlicePathSubdivision ι N) where
  cell : Σ S : GridCubeSlice ι N, GridCubeSlice.RankedSubsetPathCell S
  cell_mem : cell ∈ U.cells
  facet : GridCubeSlice.RankedSubsetPathCell.DeletionFacet cell.2

namespace FacetState

/-- A finite sigma-type presentation of subdivision facet states. -/
def equivSigma (U : CubeSlicePathSubdivision ι N) :
    FacetState U ≃
      Σ C : {C : Σ S : GridCubeSlice ι N,
          GridCubeSlice.RankedSubsetPathCell S // C ∈ U.cells},
        GridCubeSlice.RankedSubsetPathCell.DeletionFacet C.1.2 where
  toFun st := ⟨⟨st.cell, st.cell_mem⟩, st.facet⟩
  invFun st := ⟨st.1.1, st.1.2, st.2⟩
  left_inv st := by
    cases st
    rfl
  right_inv st := by
    cases st with
    | mk C F =>
      cases C
      rfl

noncomputable instance instFintype (U : CubeSlicePathSubdivision ι N) :
    Fintype (FacetState U) :=
  Fintype.ofEquiv
    (Σ C : {C : Σ S : GridCubeSlice ι N,
          GridCubeSlice.RankedSubsetPathCell S // C ∈ U.cells},
        GridCubeSlice.RankedSubsetPathCell.DeletionFacet C.1.2)
    (equivSigma U).symm

/-- The small grid cell carried by a facet state. -/
noncomputable def smallCell {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) : GridSmallCell ι N :=
  st.cell.2.toRankedSubsetCell.toSmallCell

theorem smallCell_eq_of_cell_eq {U : CubeSlicePathSubdivision ι N}
    {st st' : FacetState U} (hcell : st.cell = st'.cell) :
    st.smallCell = st'.smallCell := by
  cases st
  cases st'
  cases hcell
  rfl

theorem smallCell_mem_toTriangulation {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) :
    st.smallCell ∈ U.toTriangulation.cells := by
  classical
  rw [toTriangulation, toRankedSubdivision,
    CubeSliceRankedSubdivision.toTriangulation]
  refine Finset.mem_image.mpr ?_
  refine ⟨⟨st.cell.1, st.cell.2.toRankedSubsetCell⟩, ?_, rfl⟩
  exact Finset.mem_image.mpr ⟨st.cell, st.cell_mem, rfl⟩

/-- The grid face carried by a facet state. -/
noncomputable def face {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) : Finset (SimplexGrid ι N) :=
  st.facet.vertices

theorem face_subset_smallCell {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) :
    st.face ⊆ st.smallCell.vertices :=
  st.facet.vertices_subset_cell

theorem face_nonempty_of_one_lt_chain_length
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (hlen : 1 < st.cell.2.chain.length) :
    st.face.Nonempty :=
  st.facet.vertices_nonempty_of_one_lt_length hlen

/-- A facet state contains every label except possibly `missing`. -/
def AlmostFullyLabeled {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι) :
    Prop :=
  st.facet.AlmostFullyLabeled L missing

theorem not_almostFullyLabeled_of_chain_length_eq_one
    {U : CubeSlicePathSubdivision ι N} [Nontrivial ι]
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (hlen : st.cell.2.chain.length = 1) :
    ¬ st.AlmostFullyLabeled L missing :=
  st.facet.not_almostFullyLabeled_of_chain_length_eq_one L missing hlen

theorem full_cell_of_almostFullyLabeled_omitted_label
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : st.AlmostFullyLabeled L missing)
    (hlabel : L.label st.facet.omittedVertex = missing) :
    st.smallCell.FullyLabeled L :=
  st.facet.fullyLabeled_cell_of_almostFullyLabeled_omitted_label
    L missing halmost hlabel

theorem omitted_label_ne_of_almostFullyLabeled_not_full
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : st.AlmostFullyLabeled L missing)
    (hnot_full : ¬ st.smallCell.FullyLabeled L) :
    L.label st.facet.omittedVertex ≠ missing :=
  st.facet.omitted_label_ne_of_almostFullyLabeled_not_full
    L missing halmost hnot_full

/-- Local almost-facet count of the path cell underlying a facet state. -/
noncomputable def localAlmostFacetCount {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι) :
    ℕ :=
  st.cell.2.almostFullyLabeledFacetCount L missing

theorem full_cell_of_odd_localAlmostFacetCount
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (hlen : st.cell.2.chain.length = Fintype.card ι)
    (hodd : Odd (st.localAlmostFacetCount L missing)) :
    st.smallCell.FullyLabeled L :=
  st.cell.2.fullyLabeled_of_odd_almostFullyLabeledFacetCount_chain_length_eq_card
    L missing hlen hodd

/-- Turn another deletion facet of the same underlying path cell into a state. -/
def sameCellState {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U)
    (F : GridCubeSlice.RankedSubsetPathCell.DeletionFacet st.cell.2) :
    FacetState U :=
  ⟨st.cell, st.cell_mem, F⟩

theorem sameCellState_injective {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) :
    Function.Injective st.sameCellState := by
  intro F G hFG
  cases hFG
  rfl

/-- The embedding that inserts a deletion facet as a state of the same cell. -/
def sameCellStateEmbedding {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) :
    GridCubeSlice.RankedSubsetPathCell.DeletionFacet st.cell.2 ↪ FacetState U where
  toFun := st.sameCellState
  inj' := st.sameCellState_injective

/--
Two facet states match when they carry the same nonempty grid face but belong
to distinct induced small cells.
-/
def Matches {U : CubeSlicePathSubdivision ι N}
    (st st' : FacetState U) : Prop :=
  st.smallCell ≠ st'.smallCell ∧ st.face.Nonempty ∧ st.face = st'.face

theorem Matches.symm {U : CubeSlicePathSubdivision ι N}
    {st st' : FacetState U} (hmatch : st.Matches st') :
    st'.Matches st := by
  refine ⟨fun hcell => hmatch.1 hcell.symm, ?_, hmatch.2.2.symm⟩
  simpa [← hmatch.2.2] using hmatch.2.1

/--
The within-cell pivot between two almost fully labeled deletion facets of the
same path cell. This is the second edge type in the usual Sperner path graph:
non-solution cells pair their two almost facets internally.
-/
def LocalPivot {U : CubeSlicePathSubdivision ι N}
    (st st' : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι) :
    Prop :=
  st.cell = st'.cell ∧ st.face ≠ st'.face ∧
    st.AlmostFullyLabeled L missing ∧ st'.AlmostFullyLabeled L missing

theorem LocalPivot.symm {U : CubeSlicePathSubdivision ι N}
    {st st' : FacetState U} {L : GridSpernerLabeling ι N} {missing : ι}
    (hpivot : st.LocalPivot st' L missing) :
    st'.LocalPivot st L missing := by
  exact ⟨hpivot.1.symm, fun hface => hpivot.2.1 hface.symm,
    hpivot.2.2.2, hpivot.2.2.1⟩

theorem localPivot_sameCellState_iff {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U)
    (F : GridCubeSlice.RankedSubsetPathCell.DeletionFacet st.cell.2)
    (L : GridSpernerLabeling ι N) (missing : ι) :
    st.LocalPivot (st.sameCellState F) L missing ↔
      F ≠ st.facet ∧ st.AlmostFullyLabeled L missing ∧
        F.AlmostFullyLabeled L missing := by
  classical
  constructor
  · intro hpivot
    refine ⟨?_, hpivot.2.2.1, hpivot.2.2.2⟩
    intro hF
    exact hpivot.2.1 (by simp [face, sameCellState, hF])
  · rintro ⟨hF, hst, hFalmost⟩
    refine ⟨rfl, ?_, hst, hFalmost⟩
    intro hface
    have hfacet :
        st.facet = F :=
      (GridCubeSlice.RankedSubsetPathCell.DeletionFacet.vertices_eq_iff
        st.facet F).mp (by simpa [face, sameCellState] using hface)
    exact hF hfacet.symm

/--
The same-cell local pivot partners generated by the other almost-labeled
deletion facets of the path cell.
-/
noncomputable def localPivotPartnerStates {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι) :
    Finset (FacetState U) :=
  ((st.cell.2.almostFullyLabeledFacets L missing).erase st.facet).map
    st.sameCellStateEmbedding

theorem localPivot_of_mem_localPivotPartnerStates
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : st.AlmostFullyLabeled L missing)
    {st' : FacetState U}
    (hst' : st' ∈ st.localPivotPartnerStates L missing) :
    st.LocalPivot st' L missing := by
  classical
  rw [localPivotPartnerStates] at hst'
  rcases Finset.mem_map.mp hst' with ⟨F, hF, rfl⟩
  have hF_ne : F ≠ st.facet := (Finset.mem_erase.mp hF).1
  have hF_almost : F.AlmostFullyLabeled L missing :=
    (st.cell.2.mem_almostFullyLabeledFacets_iff L missing).mp
      (Finset.mem_erase.mp hF).2
  exact (st.localPivot_sameCellState_iff F L missing).mpr
    ⟨hF_ne, halmost, hF_almost⟩

theorem mem_localPivotPartnerStates_of_localPivot
    {U : CubeSlicePathSubdivision ι N}
    {st st' : FacetState U} {L : GridSpernerLabeling ι N} {missing : ι}
    (hpivot : st.LocalPivot st' L missing) :
    st' ∈ st.localPivotPartnerStates L missing := by
  classical
  rcases st with ⟨C, hC, F⟩
  rcases st' with ⟨C', hC', F'⟩
  rcases hpivot with ⟨hcell, hface_ne, _halmost, hF'_almost⟩
  cases hcell
  rw [localPivotPartnerStates]
  refine Finset.mem_map.mpr ⟨F', ?_, ?_⟩
  · refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro hF
      exact hface_ne (by subst hF; simp [face])
    · exact (C.2.mem_almostFullyLabeledFacets_iff L missing).mpr hF'_almost
  · dsimp [sameCellStateEmbedding, sameCellState]

theorem localPivotPartnerStates_card_eq_localAlmostFacetCount_sub_one
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : st.AlmostFullyLabeled L missing) :
    (st.localPivotPartnerStates L missing).card =
      st.localAlmostFacetCount L missing - 1 := by
  classical
  have hfacet_mem :
      st.facet ∈ st.cell.2.almostFullyLabeledFacets L missing :=
    (st.cell.2.mem_almostFullyLabeledFacets_iff L missing).mpr halmost
  rw [localPivotPartnerStates,
    Finset.card_map,
    Finset.card_erase_of_mem hfacet_mem,
    localAlmostFacetCount,
    st.cell.2.almostFullyLabeledFacetCount_eq_card]

theorem localPivotPartnerStates_card_eq_one_of_almostFullyLabeled_not_full_chain_length_eq_card
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : st.AlmostFullyLabeled L missing)
    (hnot_full : ¬ st.smallCell.FullyLabeled L)
    (hlen : st.cell.2.chain.length = Fintype.card ι) :
    (st.localPivotPartnerStates L missing).card = 1 := by
  classical
  have hfacet_mem :
      st.facet ∈ st.cell.2.almostFullyLabeledFacets L missing :=
    (st.cell.2.mem_almostFullyLabeledFacets_iff L missing).mpr halmost
  have hcount :
      st.cell.2.almostFullyLabeledFacetCount L missing = 2 :=
    st.cell.2.almostFullyLabeledFacetCount_eq_two_of_almostFullyLabeled_not_full_chain_length_eq_card
      L missing halmost hnot_full hlen
  rw [localPivotPartnerStates,
    Finset.card_map,
    Finset.card_erase_of_mem hfacet_mem,
    ← st.cell.2.almostFullyLabeledFacetCount_eq_card L missing,
    hcount]

/--
Geometric cross-cell partners of a facet state, independent of labels. These
are the states carrying the same nonempty face in a distinct induced small
cell.
-/
noncomputable def matchPartnerStates {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) : Finset (FacetState U) := by
  classical
  exact (Finset.univ : Finset (FacetState U)).filter fun st' =>
    st.Matches st'

theorem mem_matchPartnerStates_iff
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) {st' : FacetState U} :
    st' ∈ st.matchPartnerStates ↔ st.Matches st' := by
  classical
  simp [matchPartnerStates]

theorem matchPartnerStates_card_eq_zero_iff
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) :
    st.matchPartnerStates.card = 0 ↔
      ∀ st' : FacetState U, ¬ st.Matches st' := by
  classical
  rw [Finset.card_eq_zero]
  constructor
  · intro hzero st' hmatch
    have hmem : st' ∈ st.matchPartnerStates :=
      (st.mem_matchPartnerStates_iff).mpr hmatch
    simp [hzero] at hmem
  · intro hno
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro st' hmem
    exact hno st' ((st.mem_matchPartnerStates_iff).mp hmem)

theorem matchPartnerStates_card_eq_one_iff_existsUnique_matches
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) :
    st.matchPartnerStates.card = 1 ↔
      ∃! st' : FacetState U, st.Matches st' := by
  classical
  rw [Finset.card_eq_one, st.matchPartnerStates.singleton_iff_unique_mem]
  simp [st.mem_matchPartnerStates_iff]

/--
The active same-cell partners of a state. They are empty unless the state
itself is almost fully labeled, matching the actual graph adjacency relation.
-/
noncomputable def activeLocalPivotPartnerStates {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι) :
    Finset (FacetState U) := by
  classical
  exact if st.AlmostFullyLabeled L missing then
    st.localPivotPartnerStates L missing
  else
    ∅

theorem mem_activeLocalPivotPartnerStates_iff
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    {st' : FacetState U} :
    st' ∈ st.activeLocalPivotPartnerStates L missing ↔
      st.AlmostFullyLabeled L missing ∧
        st' ∈ st.localPivotPartnerStates L missing := by
  classical
  by_cases halmost : st.AlmostFullyLabeled L missing
  · simp [activeLocalPivotPartnerStates, halmost]
  · simp [activeLocalPivotPartnerStates, halmost]

theorem mem_activeLocalPivotPartnerStates_iff_localPivot
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    {st' : FacetState U} :
    st' ∈ st.activeLocalPivotPartnerStates L missing ↔
      st.LocalPivot st' L missing := by
  constructor
  · intro hst'
    rcases (st.mem_activeLocalPivotPartnerStates_iff L missing).mp hst' with
      ⟨halmost, hlocal⟩
    exact st.localPivot_of_mem_localPivotPartnerStates L missing halmost hlocal
  · intro hpivot
    exact (st.mem_activeLocalPivotPartnerStates_iff L missing).mpr
      ⟨hpivot.2.2.1, mem_localPivotPartnerStates_of_localPivot hpivot⟩

theorem activeLocalPivotPartnerStates_card_eq
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : st.AlmostFullyLabeled L missing) :
    (st.activeLocalPivotPartnerStates L missing).card =
      (st.localPivotPartnerStates L missing).card := by
  classical
  simp [activeLocalPivotPartnerStates, halmost]

/--
Cross-cell matching partners of a facet state. These are the neighboring states
across the same geometric face; same-cell local pivots are tracked separately by
`localPivotPartnerStates`.
-/
noncomputable def crossMatchPartnerStates {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι) :
    Finset (FacetState U) := by
  classical
  exact (Finset.univ : Finset (FacetState U)).filter fun st' =>
    st.Matches st' ∧ st.AlmostFullyLabeled L missing

theorem mem_crossMatchPartnerStates_iff
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    {st' : FacetState U} :
    st' ∈ st.crossMatchPartnerStates L missing ↔
      st.Matches st' ∧ st.AlmostFullyLabeled L missing := by
  classical
  simp [crossMatchPartnerStates]

theorem mem_crossMatchPartnerStates_iff_matches_of_almostFullyLabeled
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : st.AlmostFullyLabeled L missing)
    {st' : FacetState U} :
    st' ∈ st.crossMatchPartnerStates L missing ↔ st.Matches st' := by
  rw [st.mem_crossMatchPartnerStates_iff L missing]
  simp [halmost]

theorem crossMatchPartnerStates_eq_matchPartnerStates_of_almostFullyLabeled
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : st.AlmostFullyLabeled L missing) :
    st.crossMatchPartnerStates L missing = st.matchPartnerStates := by
  classical
  ext st'
  rw [st.mem_crossMatchPartnerStates_iff_matches_of_almostFullyLabeled
    L missing halmost, st.mem_matchPartnerStates_iff]

theorem crossMatchPartnerStates_card_eq_matchPartnerStates_card_of_almostFullyLabeled
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : st.AlmostFullyLabeled L missing) :
    (st.crossMatchPartnerStates L missing).card =
      st.matchPartnerStates.card := by
  rw [st.crossMatchPartnerStates_eq_matchPartnerStates_of_almostFullyLabeled
    L missing halmost]

theorem crossMatchPartnerStates_eq_empty_of_not_almostFullyLabeled
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : ¬ st.AlmostFullyLabeled L missing) :
    st.crossMatchPartnerStates L missing = ∅ := by
  classical
  ext st'
  rw [st.mem_crossMatchPartnerStates_iff L missing]
  simp [halmost]

theorem mem_crossMatchPartnerStates_symm
    {U : CubeSlicePathSubdivision ι N}
    {st st' : FacetState U} {L : GridSpernerLabeling ι N} {missing : ι}
    (hst' : st' ∈ st.crossMatchPartnerStates L missing) :
    st ∈ st'.crossMatchPartnerStates L missing := by
  rcases (st.mem_crossMatchPartnerStates_iff L missing).mp hst' with
    ⟨hmatch, halmost⟩
  have halmost' : st'.AlmostFullyLabeled L missing := by
    have hvertices : st.facet.vertices = st'.facet.vertices := by
      simpa [face] using hmatch.2.2
    rw [AlmostFullyLabeled,
      GridCubeSlice.RankedSubsetPathCell.DeletionFacet.AlmostFullyLabeled] at halmost ⊢
    simpa [hvertices] using halmost
  exact (st'.mem_crossMatchPartnerStates_iff L missing).mpr
    ⟨hmatch.symm, halmost'⟩

/--
All graph partners of a facet state, split into same-cell local pivots and
cross-cell matches.
-/
noncomputable def pivotPartnerStates {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι) :
    Finset (FacetState U) := by
  classical
  exact st.activeLocalPivotPartnerStates L missing ∪
    st.crossMatchPartnerStates L missing

theorem disjoint_activeLocalPivotPartnerStates_crossMatchPartnerStates
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι) :
    Disjoint (st.activeLocalPivotPartnerStates L missing)
      (st.crossMatchPartnerStates L missing) := by
  classical
  rw [Finset.disjoint_left]
  intro st' hlocal hcross
  have hpivot :
      st.LocalPivot st' L missing :=
    (st.mem_activeLocalPivotPartnerStates_iff_localPivot L missing).mp hlocal
  have hmatch :
      st.Matches st' :=
    ((st.mem_crossMatchPartnerStates_iff L missing).mp hcross).1
  exact hmatch.1 (smallCell_eq_of_cell_eq hpivot.1)

theorem pivotPartnerStates_card_eq
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι) :
    (st.pivotPartnerStates L missing).card =
      (st.activeLocalPivotPartnerStates L missing).card +
        (st.crossMatchPartnerStates L missing).card := by
  classical
  rw [pivotPartnerStates,
    Finset.card_union_of_disjoint
      (st.disjoint_activeLocalPivotPartnerStates_crossMatchPartnerStates L missing)]

theorem exists_localPivot_of_almostFullyLabeled_not_full
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : st.AlmostFullyLabeled L missing)
    (hnot_full : ¬ st.smallCell.FullyLabeled L) :
    ∃ st' : FacetState U, st.LocalPivot st' L missing := by
  classical
  rcases st.cell.2.exists_ne_almostFullyLabeledFacet_of_almostFullyLabeled_not_full
      L missing halmost hnot_full with
    ⟨G, hG_ne, hG⟩
  let st' : FacetState U := ⟨st.cell, st.cell_mem, G⟩
  refine ⟨st', ?_⟩
  have hface_ne : st.face ≠ st'.face := by
    intro hface
    have hfacet : st.facet = G :=
      (GridCubeSlice.RankedSubsetPathCell.DeletionFacet.vertices_eq_iff
        st.facet G).mp (by simpa [face, st'] using hface)
    exact hG_ne hfacet.symm
  exact ⟨rfl, hface_ne, halmost, hG⟩

theorem sharedFace_of_matches {U : CubeSlicePathSubdivision ι N}
    {st st' : FacetState U} (hmatch : st.Matches st') :
    GridSmallCell.SharedFace st.smallCell st'.smallCell st.face where
  nonempty := hmatch.2.1
  subset_left := st.face_subset_smallCell
  subset_right := by
    intro a ha
    exact st'.face_subset_smallCell (by simpa [hmatch.2.2] using ha)

theorem almostFullyLabeled_of_face_eq {U : CubeSlicePathSubdivision ι N}
    {st st' : FacetState U} {L : GridSpernerLabeling ι N} {missing : ι}
    (halmost : st.AlmostFullyLabeled L missing)
    (hface : st.face = st'.face) :
    st'.AlmostFullyLabeled L missing := by
  have hvertices : st.facet.vertices = st'.facet.vertices := by
    simpa [face] using hface
  rw [AlmostFullyLabeled,
    GridCubeSlice.RankedSubsetPathCell.DeletionFacet.AlmostFullyLabeled] at halmost ⊢
  simpa [hvertices] using halmost

theorem sharesAlmostFullyLabeledFace_of_matches
    {U : CubeSlicePathSubdivision ι N}
    {st st' : FacetState U} (L : GridSpernerLabeling ι N) (missing : ι)
    (hmatch : st.Matches st')
    (halmost : st.AlmostFullyLabeled L missing) :
    st.smallCell.SharesAlmostFullyLabeledFace st'.smallCell L missing := by
  exact ⟨hmatch.1, st.face, st.sharedFace_of_matches hmatch, halmost⟩

/--
The actual facet-state Sperner pivot graph. Edges either cross a shared
almost-labeled face into a neighboring cell, or pivot inside the same cell
between its two almost-labeled facets.
-/
def spernerFacetPivotGraph
    (U : CubeSlicePathSubdivision ι N)
    (L : GridSpernerLabeling ι N) (missing : ι) :
    SimpleGraph (FacetState U) where
  Adj st st' :=
    st.LocalPivot st' L missing ∨
      (st.Matches st' ∧ st.AlmostFullyLabeled L missing)
  symm := by
    intro st st' hadj
    rcases hadj with hpivot | hmatch
    · exact Or.inl hpivot.symm
    · exact Or.inr ⟨hmatch.1.symm,
        st.almostFullyLabeled_of_face_eq hmatch.2 hmatch.1.2.2⟩
  loopless := ⟨fun st hadj => by
    rcases hadj with hpivot | hmatch
    · exact hpivot.2.1 rfl
    · exact hmatch.1.1 rfl⟩

theorem spernerFacetPivotGraph_adj_of_localPivot
    {U : CubeSlicePathSubdivision ι N}
    {L : GridSpernerLabeling ι N} {missing : ι}
    {st st' : FacetState U}
    (hpivot : st.LocalPivot st' L missing) :
    (spernerFacetPivotGraph U L missing).Adj st st' :=
  Or.inl hpivot

theorem spernerFacetPivotGraph_adj_of_matches
    {U : CubeSlicePathSubdivision ι N}
    {L : GridSpernerLabeling ι N} {missing : ι}
    {st st' : FacetState U}
    (hmatch : st.Matches st') (halmost : st.AlmostFullyLabeled L missing) :
    (spernerFacetPivotGraph U L missing).Adj st st' :=
  Or.inr ⟨hmatch, halmost⟩

theorem spernerFacetPivotGraph_adj_of_mem_crossMatchPartnerStates
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    {st' : FacetState U}
    (hst' : st' ∈ st.crossMatchPartnerStates L missing) :
    (spernerFacetPivotGraph U L missing).Adj st st' := by
  rcases (st.mem_crossMatchPartnerStates_iff L missing).mp hst' with
    ⟨hmatch, halmost⟩
  exact spernerFacetPivotGraph_adj_of_matches hmatch halmost

theorem spernerFacetPivotGraph_adj_of_mem_localPivotPartnerStates
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : st.AlmostFullyLabeled L missing)
    {st' : FacetState U}
    (hst' : st' ∈ st.localPivotPartnerStates L missing) :
    (spernerFacetPivotGraph U L missing).Adj st st' :=
  spernerFacetPivotGraph_adj_of_localPivot
    (st.localPivot_of_mem_localPivotPartnerStates L missing halmost hst')

theorem mem_pivotPartnerStates_iff_spernerFacetPivotGraph_adj
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    {st' : FacetState U} :
    st' ∈ st.pivotPartnerStates L missing ↔
      (spernerFacetPivotGraph U L missing).Adj st st' := by
  classical
  simp [pivotPartnerStates,
    mem_activeLocalPivotPartnerStates_iff_localPivot,
    mem_crossMatchPartnerStates_iff,
    spernerFacetPivotGraph]

theorem neighborFinset_spernerFacetPivotGraph
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    [Fintype ((spernerFacetPivotGraph U L missing).neighborSet st)] :
    (spernerFacetPivotGraph U L missing).neighborFinset st =
      st.pivotPartnerStates L missing := by
  classical
  ext st'
  rw [SimpleGraph.mem_neighborFinset,
    (st.mem_pivotPartnerStates_iff_spernerFacetPivotGraph_adj L missing).symm]

theorem exists_spernerFacetPivotGraph_adj_of_almostFullyLabeled_not_full
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : st.AlmostFullyLabeled L missing)
    (hnot_full : ¬ st.smallCell.FullyLabeled L) :
    ∃ st' : FacetState U,
      (spernerFacetPivotGraph U L missing).Adj st st' := by
  rcases st.exists_localPivot_of_almostFullyLabeled_not_full
      L missing halmost hnot_full with
    ⟨st', hpivot⟩
  exact ⟨st', spernerFacetPivotGraph_adj_of_localPivot hpivot⟩

/-- Degree in the actual two-edge-type facet-state Sperner pivot graph. -/
noncomputable def spernerFacetPivotDegree
    (U : CubeSlicePathSubdivision ι N)
    (L : GridSpernerLabeling ι N) (missing : ι)
    (st : FacetState U) : ℕ := by
  classical
  exact (spernerFacetPivotGraph U L missing).degree st

theorem spernerFacetPivotDegree_eq_card_pivotPartnerStates
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι) :
    spernerFacetPivotDegree U L missing st =
      (st.pivotPartnerStates L missing).card := by
  classical
  rw [spernerFacetPivotDegree, SimpleGraph.degree,
    neighborFinset_spernerFacetPivotGraph]

theorem spernerFacetPivotDegree_eq_activeLocal_add_cross
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι) :
    spernerFacetPivotDegree U L missing st =
      (st.activeLocalPivotPartnerStates L missing).card +
        (st.crossMatchPartnerStates L missing).card := by
  rw [spernerFacetPivotDegree_eq_card_pivotPartnerStates,
    pivotPartnerStates_card_eq]

theorem spernerFacetPivotDegree_eq_localPivot_add_cross_of_almostFullyLabeled
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : st.AlmostFullyLabeled L missing) :
    spernerFacetPivotDegree U L missing st =
      (st.localPivotPartnerStates L missing).card +
        (st.crossMatchPartnerStates L missing).card := by
  rw [spernerFacetPivotDegree_eq_activeLocal_add_cross,
    st.activeLocalPivotPartnerStates_card_eq L missing halmost]

theorem spernerFacetPivotDegree_eq_localAlmostFacetCount_of_cross_card_eq_one
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : st.AlmostFullyLabeled L missing)
    (hcross : (st.crossMatchPartnerStates L missing).card = 1) :
    spernerFacetPivotDegree U L missing st =
      st.localAlmostFacetCount L missing := by
  classical
  have hlocal :
      (st.localPivotPartnerStates L missing).card =
        st.localAlmostFacetCount L missing - 1 :=
    st.localPivotPartnerStates_card_eq_localAlmostFacetCount_sub_one
      L missing halmost
  have hfacet_mem :
      st.facet ∈ st.cell.2.almostFullyLabeledFacets L missing :=
    (st.cell.2.mem_almostFullyLabeledFacets_iff L missing).mpr halmost
  have hcount_pos : 0 < st.localAlmostFacetCount L missing := by
    rw [localAlmostFacetCount,
      st.cell.2.almostFullyLabeledFacetCount_eq_card]
    exact Finset.card_pos.mpr ⟨st.facet, hfacet_mem⟩
  rw [st.spernerFacetPivotDegree_eq_localPivot_add_cross_of_almostFullyLabeled
    L missing halmost, hlocal, hcross]
  omega

theorem spernerFacetPivotDegree_eq_localPivot_of_cross_card_eq_zero
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : st.AlmostFullyLabeled L missing)
    (hcross : (st.crossMatchPartnerStates L missing).card = 0) :
    spernerFacetPivotDegree U L missing st =
      (st.localPivotPartnerStates L missing).card := by
  rw [st.spernerFacetPivotDegree_eq_localPivot_add_cross_of_almostFullyLabeled
    L missing halmost, hcross, Nat.add_zero]

theorem odd_spernerFacetPivotDegree_of_cross_card_eq_zero_local_card_eq_one
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : st.AlmostFullyLabeled L missing)
    (hcross : (st.crossMatchPartnerStates L missing).card = 0)
    (hlocal : (st.localPivotPartnerStates L missing).card = 1) :
    Odd (spernerFacetPivotDegree U L missing st) := by
  rw [st.spernerFacetPivotDegree_eq_localPivot_of_cross_card_eq_zero
    L missing halmost hcross, hlocal]
  exact odd_one

theorem odd_spernerFacetPivotDegree_of_almostFullyLabeled_not_full_cross_card_eq_zero
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : st.AlmostFullyLabeled L missing)
    (hnot_full : ¬ st.smallCell.FullyLabeled L)
    (hlen : st.cell.2.chain.length = Fintype.card ι)
    (hcross : (st.crossMatchPartnerStates L missing).card = 0) :
    Odd (spernerFacetPivotDegree U L missing st) := by
  exact st.odd_spernerFacetPivotDegree_of_cross_card_eq_zero_local_card_eq_one
    L missing halmost hcross
    (st.localPivotPartnerStates_card_eq_one_of_almostFullyLabeled_not_full_chain_length_eq_card
      L missing halmost hnot_full hlen)

theorem almostFullyLabeled_of_spernerFacetPivotGraph_adj
    {U : CubeSlicePathSubdivision ι N}
    {L : GridSpernerLabeling ι N} {missing : ι}
    {st st' : FacetState U}
    (hadj : (spernerFacetPivotGraph U L missing).Adj st st') :
    st.AlmostFullyLabeled L missing := by
  rcases hadj with hpivot | hmatch
  · exact hpivot.2.2.1
  · exact hmatch.2

theorem almostFullyLabeled_of_spernerFacetPivotDegree_pos
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (hpos : 0 < spernerFacetPivotDegree U L missing st) :
    st.AlmostFullyLabeled L missing := by
  classical
  let G := spernerFacetPivotGraph U L missing
  have hposG : 0 < G.degree st := by
    simpa [spernerFacetPivotDegree, G] using hpos
  rcases (G.degree_pos_iff_exists_adj st).mp hposG with ⟨st', hadj⟩
  exact almostFullyLabeled_of_spernerFacetPivotGraph_adj hadj

theorem almostFullyLabeled_of_odd_spernerFacetPivotDegree
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (hodd : Odd (spernerFacetPivotDegree U L missing st)) :
    st.AlmostFullyLabeled L missing := by
  have hpos : 0 < spernerFacetPivotDegree U L missing st := by
    rcases hodd with ⟨k, hk⟩
    omega
  exact st.almostFullyLabeled_of_spernerFacetPivotDegree_pos L missing hpos

theorem full_cell_of_odd_spernerFacetPivotDegree_of_cross_card_eq_one
    {U : CubeSlicePathSubdivision ι N}
    (st : FacetState U) (L : GridSpernerLabeling ι N) (missing : ι)
    (hcross : (st.crossMatchPartnerStates L missing).card = 1)
    (hlen : st.cell.2.chain.length = Fintype.card ι)
    (hodd : Odd (spernerFacetPivotDegree U L missing st)) :
    st.smallCell.FullyLabeled L := by
  have halmost :
      st.AlmostFullyLabeled L missing :=
    st.almostFullyLabeled_of_odd_spernerFacetPivotDegree L missing hodd
  have hdegree :
      spernerFacetPivotDegree U L missing st =
        st.localAlmostFacetCount L missing :=
    st.spernerFacetPivotDegree_eq_localAlmostFacetCount_of_cross_card_eq_one
      L missing halmost hcross
  exact st.full_cell_of_odd_localAlmostFacetCount L missing hlen
    (by simpa [hdegree] using hodd)

/--
The cross-cell matching graph: edges pair matching nonempty deletion facets that
are almost fully labeled. The actual Sperner pivot graph is
`spernerFacetPivotGraph`, which also includes same-cell local pivots.
-/
def almostLabeledFacetGraph
    (U : CubeSlicePathSubdivision ι N)
    (L : GridSpernerLabeling ι N) (missing : ι) :
    SimpleGraph (FacetState U) where
  Adj st st' :=
    st.Matches st' ∧ st.AlmostFullyLabeled L missing
  symm := by
    intro st st' hadj
    exact ⟨hadj.1.symm,
      st.almostFullyLabeled_of_face_eq hadj.2 hadj.1.2.2⟩
  loopless := ⟨fun st hadj => hadj.1.1 rfl⟩

theorem almostFacePivotGraph_adj_of_facetGraph_adj
    {U : CubeSlicePathSubdivision ι N}
    {L : GridSpernerLabeling ι N} {missing : ι}
    {st st' : FacetState U}
    (hadj : (almostLabeledFacetGraph U L missing).Adj st st') :
    (U.toTriangulation.almostFacePivotGraph L missing).Adj
      ⟨st.smallCell, st.smallCell_mem_toTriangulation⟩
      ⟨st'.smallCell, st'.smallCell_mem_toTriangulation⟩ := by
  exact st.sharesAlmostFullyLabeledFace_of_matches L missing hadj.1 hadj.2

end FacetState

/-- Degree in the cross-cell almost-labeled facet matching graph. -/
noncomputable def almostLabeledFacetDegree
    (U : CubeSlicePathSubdivision ι N)
    (L : GridSpernerLabeling ι N) (missing : ι)
    (st : FacetState U) : ℕ := by
  classical
  exact (FacetState.almostLabeledFacetGraph U L missing).degree st

/--
A parity certificate for the concrete facet-state pivot graph of a
path-shaped subdivision.
-/
structure FacetPivotCertificate
    (U : CubeSlicePathSubdivision ι N)
    (L : GridSpernerLabeling ι N) (missing : ι) where
  boundary : FacetState U → Prop
  start : FacetState U
  start_boundary : boundary start
  start_odd : Odd (FacetState.spernerFacetPivotDegree U L missing start)
  boundary_unique : ∀ st, boundary st → st = start
  odd_nonboundary_full :
    ∀ st, Odd (FacetState.spernerFacetPivotDegree U L missing st) →
      ¬ boundary st → st.smallCell.FullyLabeled L

namespace FacetPivotCertificate

/--
View a concrete facet-state certificate as the abstract pivot graph
certificate used by the existing Sperner bridge.
-/
noncomputable def toPivotGraphCertificate
    {U : CubeSlicePathSubdivision ι N}
    {L : GridSpernerLabeling ι N} {missing : ι}
    (C : FacetPivotCertificate U L missing) :
    PivotGraphCertificate U.toTriangulation L (FacetState U) := by
  classical
  let G := FacetState.spernerFacetPivotGraph U L missing
  exact
    { graph := G
      decidableAdj := inferInstance
      cellOf := fun st => st.smallCell
      cell_mem := fun st => st.smallCell_mem_toTriangulation
      boundary := C.boundary
      start := C.start
      start_boundary := C.start_boundary
      start_odd := by
        simpa [FacetState.spernerFacetPivotDegree, G] using C.start_odd
      boundary_unique := C.boundary_unique
      odd_nonboundary_full := by
        intro st hodd hboundary
        exact C.odd_nonboundary_full st
          (by simpa [FacetState.spernerFacetPivotDegree, G] using hodd)
          hboundary }

theorem exists_fullyLabeled
    {U : CubeSlicePathSubdivision ι N}
    {L : GridSpernerLabeling ι N} {missing : ι}
    (C : FacetPivotCertificate U L missing) :
    ∃ cell ∈ U.toTriangulation.cells, cell.FullyLabeled L :=
  C.toPivotGraphCertificate.exists_fullyLabeled

end FacetPivotCertificate

/--
Incidence data sufficient to build a concrete facet-pivot certificate.

This is the reusable bridge we want for Kuhn/Sperner: after the subdivision
proves that relevant non-boundary almost facets have a unique cross-cell mate
and lie in maximal path cells, the local parity theorem identifies every odd
non-boundary graph state with a fully labeled cell.
-/
structure FacetIncidenceCertificate
    (U : CubeSlicePathSubdivision ι N)
    (L : GridSpernerLabeling ι N) (missing : ι) where
  boundary : FacetState U → Prop
  start : FacetState U
  start_boundary : boundary start
  start_odd : Odd (FacetState.spernerFacetPivotDegree U L missing start)
  boundary_unique : ∀ st, boundary st → st = start
  nonboundary_cross_card_eq_one :
    ∀ st, st.AlmostFullyLabeled L missing → ¬ boundary st →
      (st.crossMatchPartnerStates L missing).card = 1
  nonboundary_chain_length :
    ∀ st, st.AlmostFullyLabeled L missing → ¬ boundary st →
      st.cell.2.chain.length = Fintype.card ι

namespace FacetIncidenceCertificate

/--
Convert incidence-and-local-parity data into the concrete graph certificate
used by the existing Sperner bridge.
-/
noncomputable def toFacetPivotCertificate
    {U : CubeSlicePathSubdivision ι N}
    {L : GridSpernerLabeling ι N} {missing : ι}
    (C : FacetIncidenceCertificate U L missing) :
    FacetPivotCertificate U L missing where
  boundary := C.boundary
  start := C.start
  start_boundary := C.start_boundary
  start_odd := C.start_odd
  boundary_unique := C.boundary_unique
  odd_nonboundary_full := by
    intro st hodd hboundary
    have halmost :
        st.AlmostFullyLabeled L missing :=
      st.almostFullyLabeled_of_odd_spernerFacetPivotDegree L missing hodd
    exact st.full_cell_of_odd_spernerFacetPivotDegree_of_cross_card_eq_one
      L missing
      (C.nonboundary_cross_card_eq_one st halmost hboundary)
      (C.nonboundary_chain_length st halmost hboundary)
      hodd

theorem exists_fullyLabeled
    {U : CubeSlicePathSubdivision ι N}
    {L : GridSpernerLabeling ι N} {missing : ι}
    (C : FacetIncidenceCertificate U L missing) :
    ∃ cell ∈ U.toTriangulation.cells, cell.FullyLabeled L :=
  C.toFacetPivotCertificate.exists_fullyLabeled

end FacetIncidenceCertificate

/--
Counting-style incidence data. This is closer to what a concrete Kuhn
construction should prove: the start boundary facet has no cross mate and one
internal pivot partner, while every relevant non-boundary almost facet has one
cross mate.
-/
structure FacetCountingIncidenceCertificate
    (U : CubeSlicePathSubdivision ι N)
    (L : GridSpernerLabeling ι N) (missing : ι) where
  boundary : FacetState U → Prop
  start : FacetState U
  start_boundary : boundary start
  start_almost : start.AlmostFullyLabeled L missing
  start_not_full : ¬ start.smallCell.FullyLabeled L
  start_cross_card_eq_zero :
    (start.crossMatchPartnerStates L missing).card = 0
  start_chain_length : start.cell.2.chain.length = Fintype.card ι
  boundary_unique : ∀ st, boundary st → st = start
  nonboundary_cross_card_eq_one :
    ∀ st, st.AlmostFullyLabeled L missing → ¬ boundary st →
      (st.crossMatchPartnerStates L missing).card = 1
  nonboundary_chain_length :
    ∀ st, st.AlmostFullyLabeled L missing → ¬ boundary st →
      st.cell.2.chain.length = Fintype.card ι

namespace FacetCountingIncidenceCertificate

/-- Convert purely counting-style incidence data into a graph-incidence certificate. -/
noncomputable def toFacetIncidenceCertificate
    {U : CubeSlicePathSubdivision ι N}
    {L : GridSpernerLabeling ι N} {missing : ι}
    (C : FacetCountingIncidenceCertificate U L missing) :
    FacetIncidenceCertificate U L missing where
  boundary := C.boundary
  start := C.start
  start_boundary := C.start_boundary
  start_odd :=
    C.start.odd_spernerFacetPivotDegree_of_almostFullyLabeled_not_full_cross_card_eq_zero
      L missing C.start_almost C.start_not_full C.start_chain_length
      C.start_cross_card_eq_zero
  boundary_unique := C.boundary_unique
  nonboundary_cross_card_eq_one := C.nonboundary_cross_card_eq_one
  nonboundary_chain_length := C.nonboundary_chain_length

noncomputable def toFacetPivotCertificate
    {U : CubeSlicePathSubdivision ι N}
    {L : GridSpernerLabeling ι N} {missing : ι}
    (C : FacetCountingIncidenceCertificate U L missing) :
    FacetPivotCertificate U L missing :=
  C.toFacetIncidenceCertificate.toFacetPivotCertificate

theorem exists_fullyLabeled
    {U : CubeSlicePathSubdivision ι N}
    {L : GridSpernerLabeling ι N} {missing : ι}
    (C : FacetCountingIncidenceCertificate U L missing) :
    ∃ cell ∈ U.toTriangulation.cells, cell.FullyLabeled L :=
  C.toFacetPivotCertificate.exists_fullyLabeled

end FacetCountingIncidenceCertificate

/--
A path subdivision has concrete facet-pivot certificates if every labeling
admits a parity certificate for its facet-state graph.
-/
def HasFacetPivotCertificates
    (U : CubeSlicePathSubdivision ι N) : Prop :=
  ∀ L : GridSpernerLabeling ι N,
    ∃ missing : ι, Nonempty (FacetPivotCertificate U L missing)

theorem hasPivotGraphCertificates_of_facetPivotCertificates
    {U : CubeSlicePathSubdivision ι N}
    (hU : U.HasFacetPivotCertificates) :
    U.toTriangulation.HasPivotGraphCertificates := by
  classical
  intro L
  rcases hU L with ⟨missing, hC⟩
  rcases hC with ⟨C⟩
  exact ⟨FacetState U, inferInstance, ⟨C.toPivotGraphCertificate⟩⟩

/--
A path subdivision has facet-incidence certificates if every labeling admits
the incidence data needed to construct a concrete facet-pivot certificate.
-/
def HasFacetIncidenceCertificates
    (U : CubeSlicePathSubdivision ι N) : Prop :=
  ∀ L : GridSpernerLabeling ι N,
    ∃ missing : ι, Nonempty (FacetIncidenceCertificate U L missing)

theorem hasFacetPivotCertificates_of_facetIncidenceCertificates
    {U : CubeSlicePathSubdivision ι N}
    (hU : U.HasFacetIncidenceCertificates) :
    U.HasFacetPivotCertificates := by
  intro L
  rcases hU L with ⟨missing, hC⟩
  rcases hC with ⟨C⟩
  exact ⟨missing, ⟨C.toFacetPivotCertificate⟩⟩

/--
A path subdivision has counting-style facet-incidence certificates if every
labeling admits the purely combinatorial degree-count data.
-/
def HasFacetCountingIncidenceCertificates
    (U : CubeSlicePathSubdivision ι N) : Prop :=
  ∀ L : GridSpernerLabeling ι N,
    ∃ missing : ι, Nonempty (FacetCountingIncidenceCertificate U L missing)

theorem hasFacetIncidenceCertificates_of_facetCountingIncidenceCertificates
    {U : CubeSlicePathSubdivision ι N}
    (hU : U.HasFacetCountingIncidenceCertificates) :
    U.HasFacetIncidenceCertificates := by
  intro L
  rcases hU L with ⟨missing, hC⟩
  rcases hC with ⟨C⟩
  exact ⟨missing, ⟨C.toFacetIncidenceCertificate⟩⟩

theorem hasFacetPivotCertificates_of_facetCountingIncidenceCertificates
    {U : CubeSlicePathSubdivision ι N}
    (hU : U.HasFacetCountingIncidenceCertificates) :
    U.HasFacetPivotCertificates :=
  hasFacetPivotCertificates_of_facetIncidenceCertificates
    (hasFacetIncidenceCertificates_of_facetCountingIncidenceCertificates hU)

/--
The finite family of interior cyclic-window Kuhn cells generated by a finite
set of coordinate orders `Fin d ≃ ι`.

Rank `0` and rank `d` cube slices are deliberately omitted here: they are
degenerate one-vertex hypersimplex slices and will be added by the boundary
case constructor rather than by cyclic windows.
-/
noncomputable def cyclicWindowCellsOfOrders
    {d : ℕ} (orders : Finset (Fin d ≃ ι)) (hd : 0 < d) :
    CubeSlicePathSubdivision ι N := by
  classical
  exact
    { cells := (Finset.univ : Finset (GridCubeSlice ι N)).biUnion fun S =>
        if hrpos : 0 < S.rank then
          if hrlt : S.rank < d then
            orders.image fun e =>
              ⟨S, GridCubeSlice.RankedSubsetPathCell.cyclicWindowOfEquiv
                S e hd hrpos hrlt⟩
          else ∅
        else ∅ }

theorem mem_cyclicWindowCellsOfOrders_of_mem
    {d : ℕ} {orders : Finset (Fin d ≃ ι)} {hd : 0 < d}
    (S : GridCubeSlice ι N) {e : Fin d ≃ ι}
    (he : e ∈ orders) (hrpos : 0 < S.rank) (hrlt : S.rank < d) :
    (⟨S, GridCubeSlice.RankedSubsetPathCell.cyclicWindowOfEquiv
      S e hd hrpos hrlt⟩ :
        Σ S : GridCubeSlice ι N, GridCubeSlice.RankedSubsetPathCell S) ∈
      (cyclicWindowCellsOfOrders (ι := ι) (N := N) orders hd).cells := by
  classical
  rw [cyclicWindowCellsOfOrders]
  refine Finset.mem_biUnion.mpr ⟨S, Finset.mem_univ S, ?_⟩
  simp [hrpos, hrlt]
  refine ⟨e, he, ?_⟩
  congr

/--
All interior cyclic-window Kuhn cells, using every equivalence
`Fin (Fintype.card ι) ≃ ι` as a coordinate order.
-/
noncomputable def allInteriorCyclicWindowCells
    (hcard : 0 < Fintype.card ι) :
    CubeSlicePathSubdivision ι N :=
  cyclicWindowCellsOfOrders
    (ι := ι) (N := N)
    (orders := (Finset.univ : Finset (Fin (Fintype.card ι) ≃ ι)))
    hcard

theorem mem_allInteriorCyclicWindowCells
    (hcard : 0 < Fintype.card ι)
    (S : GridCubeSlice ι N) (e : Fin (Fintype.card ι) ≃ ι)
    (hrpos : 0 < S.rank) (hrlt : S.rank < Fintype.card ι) :
    (⟨S, GridCubeSlice.RankedSubsetPathCell.cyclicWindowOfEquiv
      S e hcard hrpos hrlt⟩ :
        Σ S : GridCubeSlice ι N, GridCubeSlice.RankedSubsetPathCell S) ∈
      (allInteriorCyclicWindowCells (ι := ι) (N := N) hcard).cells := by
  classical
  exact mem_cyclicWindowCellsOfOrders_of_mem
    (S := S) (e := e) (Finset.mem_univ e) hrpos hrlt

/--
The finite candidate Kuhn subdivision generated by coordinate orders.

Interior cube slices contribute one cyclic-window path cell for every supplied
order. Degenerate rank slices contribute a canonical singleton cell.
-/
noncomputable def kuhnCandidateCellsOfOrders
    {d : ℕ} (orders : Finset (Fin d ≃ ι)) (hd : 0 < d) :
    CubeSlicePathSubdivision ι N := by
  classical
  exact
    { cells := (Finset.univ : Finset (GridCubeSlice ι N)).biUnion fun S =>
        if hrpos : 0 < S.rank then
          if hrlt : S.rank < d then
            orders.image fun e =>
              ⟨S, GridCubeSlice.RankedSubsetPathCell.cyclicWindowOfEquiv
                S e hd hrpos hrlt⟩
          else
            {⟨S, GridCubeSlice.RankedSubsetPathCell.singletonOfSlice S⟩}
        else
          {⟨S, GridCubeSlice.RankedSubsetPathCell.singletonOfSlice S⟩} }

theorem mem_kuhnCandidateCellsOfOrders_cyclic
    {d : ℕ} {orders : Finset (Fin d ≃ ι)} {hd : 0 < d}
    (S : GridCubeSlice ι N) {e : Fin d ≃ ι}
    (he : e ∈ orders) (hrpos : 0 < S.rank) (hrlt : S.rank < d) :
    (⟨S, GridCubeSlice.RankedSubsetPathCell.cyclicWindowOfEquiv
      S e hd hrpos hrlt⟩ :
        Σ S : GridCubeSlice ι N, GridCubeSlice.RankedSubsetPathCell S) ∈
      (kuhnCandidateCellsOfOrders (ι := ι) (N := N) orders hd).cells := by
  classical
  rw [kuhnCandidateCellsOfOrders]
  refine Finset.mem_biUnion.mpr ⟨S, Finset.mem_univ S, ?_⟩
  simp [hrpos, hrlt]
  refine ⟨e, he, ?_⟩
  congr

theorem mem_kuhnCandidateCellsOfOrders_singleton_of_not_rank_pos
    {d : ℕ} {orders : Finset (Fin d ≃ ι)} {hd : 0 < d}
    (S : GridCubeSlice ι N) (hrpos : ¬ 0 < S.rank) :
    (⟨S, GridCubeSlice.RankedSubsetPathCell.singletonOfSlice S⟩ :
        Σ S : GridCubeSlice ι N, GridCubeSlice.RankedSubsetPathCell S) ∈
      (kuhnCandidateCellsOfOrders (ι := ι) (N := N) orders hd).cells := by
  classical
  rw [kuhnCandidateCellsOfOrders]
  refine Finset.mem_biUnion.mpr ⟨S, Finset.mem_univ S, ?_⟩
  simp [hrpos]

theorem mem_kuhnCandidateCellsOfOrders_singleton_of_not_rank_lt
    {d : ℕ} {orders : Finset (Fin d ≃ ι)} {hd : 0 < d}
    (S : GridCubeSlice ι N) (hrpos : 0 < S.rank) (hrlt : ¬ S.rank < d) :
    (⟨S, GridCubeSlice.RankedSubsetPathCell.singletonOfSlice S⟩ :
        Σ S : GridCubeSlice ι N, GridCubeSlice.RankedSubsetPathCell S) ∈
      (kuhnCandidateCellsOfOrders (ι := ι) (N := N) orders hd).cells := by
  classical
  rw [kuhnCandidateCellsOfOrders]
  refine Finset.mem_biUnion.mpr ⟨S, Finset.mem_univ S, ?_⟩
  simp [hrpos, hrlt]

theorem mem_kuhnCandidateCellsOfOrders_iff
    {d : ℕ} {orders : Finset (Fin d ≃ ι)} {hd : 0 < d}
    {C : Σ S : GridCubeSlice ι N, GridCubeSlice.RankedSubsetPathCell S} :
    C ∈ (kuhnCandidateCellsOfOrders (ι := ι) (N := N) orders hd).cells ↔
      (∃ (S : GridCubeSlice ι N) (hrpos : 0 < S.rank)
          (hrlt : S.rank < d) (e : Fin d ≃ ι), e ∈ orders ∧
            C = ⟨S, GridCubeSlice.RankedSubsetPathCell.cyclicWindowOfEquiv
              S e hd hrpos hrlt⟩) ∨
      (∃ S : GridCubeSlice ι N, ¬ 0 < S.rank ∧
        C = ⟨S, GridCubeSlice.RankedSubsetPathCell.singletonOfSlice S⟩) ∨
      (∃ S : GridCubeSlice ι N, 0 < S.rank ∧ ¬ S.rank < d ∧
          C = ⟨S, GridCubeSlice.RankedSubsetPathCell.singletonOfSlice S⟩) := by
  classical
  constructor
  · intro hC
    rw [kuhnCandidateCellsOfOrders] at hC
    rcases Finset.mem_biUnion.mp hC with ⟨S, _hS, hC⟩
    by_cases hrpos : 0 < S.rank
    · by_cases hrlt : S.rank < d
      · left
        simp [hrpos, hrlt] at hC
        rcases hC with ⟨e, he, hCeq⟩
        exact ⟨S, hrpos, hrlt, e, he, hCeq.symm⟩
      · right
        right
        simp [hrpos, hrlt] at hC
        exact ⟨S, hrpos, hrlt, hC⟩
    · right
      left
      simp [hrpos] at hC
      exact ⟨S, hrpos, hC⟩
  · rintro (⟨S, hrpos, hrlt, e, he, rfl⟩ | ⟨S, hrpos, rfl⟩ |
      ⟨S, hrpos, hrlt, rfl⟩)
    · exact mem_kuhnCandidateCellsOfOrders_cyclic
        (S := S) (e := e) he hrpos hrlt
    · exact mem_kuhnCandidateCellsOfOrders_singleton_of_not_rank_pos
        (S := S) (orders := orders) hrpos
    · exact mem_kuhnCandidateCellsOfOrders_singleton_of_not_rank_lt
        (S := S) (orders := orders) hrpos hrlt

/--
The all-orders candidate Kuhn subdivision for a nonempty coordinate type.
-/
noncomputable def allKuhnCandidateCells
    (hcard : 0 < Fintype.card ι) :
    CubeSlicePathSubdivision ι N :=
  kuhnCandidateCellsOfOrders
    (ι := ι) (N := N)
    (orders := (Finset.univ : Finset (Fin (Fintype.card ι) ≃ ι)))
    hcard

theorem mem_allKuhnCandidateCells_iff
    (hcard : 0 < Fintype.card ι)
    {C : Σ S : GridCubeSlice ι N, GridCubeSlice.RankedSubsetPathCell S} :
    C ∈ (allKuhnCandidateCells (ι := ι) (N := N) hcard).cells ↔
      (∃ (S : GridCubeSlice ι N) (hrpos : 0 < S.rank)
          (hrlt : S.rank < Fintype.card ι)
          (e : Fin (Fintype.card ι) ≃ ι),
            C = ⟨S, GridCubeSlice.RankedSubsetPathCell.cyclicWindowOfEquiv
              S e hcard hrpos hrlt⟩) ∨
      (∃ S : GridCubeSlice ι N, ¬ 0 < S.rank ∧
        C = ⟨S, GridCubeSlice.RankedSubsetPathCell.singletonOfSlice S⟩) ∨
      (∃ S : GridCubeSlice ι N, 0 < S.rank ∧
        ¬ S.rank < Fintype.card ι ∧
          C = ⟨S, GridCubeSlice.RankedSubsetPathCell.singletonOfSlice S⟩) := by
  classical
  simpa [allKuhnCandidateCells] using
    (mem_kuhnCandidateCellsOfOrders_iff
      (ι := ι) (N := N)
      (orders := (Finset.univ :
        Finset (Fin (Fintype.card ι) ≃ ι)))
      (hd := hcard) (C := C))

theorem chain_length_eq_card_or_eq_one_of_mem_allKuhnCandidateCells
    (hcard : 0 < Fintype.card ι)
    {C : Σ S : GridCubeSlice ι N, GridCubeSlice.RankedSubsetPathCell S}
    (hC : C ∈ (allKuhnCandidateCells (ι := ι) (N := N) hcard).cells) :
    C.2.chain.length = Fintype.card ι ∨ C.2.chain.length = 1 := by
  classical
  rw [mem_allKuhnCandidateCells_iff hcard] at hC
  rcases hC with
    ⟨S, hrpos, hrlt, e, rfl⟩ | ⟨S, _hrpos, rfl⟩ |
      ⟨S, _hrpos, _hrlt, rfl⟩
  · left
    exact GridCubeSlice.RankedSubsetPathCell.cyclicWindowOfEquiv_chain_length_eq_card
      S e hcard hrpos hrlt
  · right
    simp
  · right
    simp

theorem chain_length_eq_card_of_almostFullyLabeled_allKuhnCandidateCells
    [Nontrivial ι]
    (hcard : 0 < Fintype.card ι)
    (st : FacetState (allKuhnCandidateCells (ι := ι) (N := N) hcard))
    (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : st.AlmostFullyLabeled L missing) :
    st.cell.2.chain.length = Fintype.card ι := by
  rcases chain_length_eq_card_or_eq_one_of_mem_allKuhnCandidateCells
      (ι := ι) (N := N) hcard st.cell_mem with hlen | hlen
  · exact hlen
  · exact False.elim
      ((st.not_almostFullyLabeled_of_chain_length_eq_one L missing hlen)
        halmost)

theorem face_nonempty_of_almostFullyLabeled_allKuhnCandidateCells
    [Nontrivial ι]
    (hcard : 0 < Fintype.card ι)
    (st : FacetState (allKuhnCandidateCells (ι := ι) (N := N) hcard))
    (L : GridSpernerLabeling ι N) (missing : ι)
    (halmost : st.AlmostFullyLabeled L missing) :
    st.face.Nonempty := by
  have hlen :
      st.cell.2.chain.length = Fintype.card ι :=
    chain_length_eq_card_of_almostFullyLabeled_allKuhnCandidateCells
      hcard st L missing halmost
  exact st.face_nonempty_of_one_lt_chain_length (by
    rw [hlen]
    exact Fintype.one_lt_card)

/--
The reduced incidence-count data still needed for the all-orders Kuhn
candidate family. Maximality of relevant cells is supplied automatically by
`chain_length_eq_card_of_almostFullyLabeled_allKuhnCandidateCells`.
-/
structure AllKuhnIncidenceCountCertificate
    [Nontrivial ι]
    (hcard : 0 < Fintype.card ι)
    (L : GridSpernerLabeling ι N) (missing : ι) where
  boundary : FacetState (allKuhnCandidateCells (ι := ι) (N := N) hcard) → Prop
  start : FacetState (allKuhnCandidateCells (ι := ι) (N := N) hcard)
  start_boundary : boundary start
  start_almost : start.AlmostFullyLabeled L missing
  start_not_full : ¬ start.smallCell.FullyLabeled L
  start_cross_card_eq_zero :
    (start.crossMatchPartnerStates L missing).card = 0
  boundary_unique : ∀ st, boundary st → st = start
  nonboundary_cross_card_eq_one :
    ∀ st, st.AlmostFullyLabeled L missing → ¬ boundary st →
      (st.crossMatchPartnerStates L missing).card = 1

namespace AllKuhnIncidenceCountCertificate

noncomputable def toFacetCountingIncidenceCertificate
    [Nontrivial ι]
    {hcard : 0 < Fintype.card ι}
    {L : GridSpernerLabeling ι N} {missing : ι}
    (C : AllKuhnIncidenceCountCertificate
      (ι := ι) (N := N) hcard L missing) :
    FacetCountingIncidenceCertificate
      (allKuhnCandidateCells (ι := ι) (N := N) hcard) L missing where
  boundary := C.boundary
  start := C.start
  start_boundary := C.start_boundary
  start_almost := C.start_almost
  start_not_full := C.start_not_full
  start_cross_card_eq_zero := C.start_cross_card_eq_zero
  start_chain_length :=
    chain_length_eq_card_of_almostFullyLabeled_allKuhnCandidateCells
      hcard C.start L missing C.start_almost
  boundary_unique := C.boundary_unique
  nonboundary_cross_card_eq_one := C.nonboundary_cross_card_eq_one
  nonboundary_chain_length := by
    intro st halmost _hboundary
    exact chain_length_eq_card_of_almostFullyLabeled_allKuhnCandidateCells
      hcard st L missing halmost

noncomputable def toFacetPivotCertificate
    [Nontrivial ι]
    {hcard : 0 < Fintype.card ι}
    {L : GridSpernerLabeling ι N} {missing : ι}
    (C : AllKuhnIncidenceCountCertificate
      (ι := ι) (N := N) hcard L missing) :
    FacetPivotCertificate
      (allKuhnCandidateCells (ι := ι) (N := N) hcard) L missing :=
  C.toFacetCountingIncidenceCertificate.toFacetPivotCertificate

end AllKuhnIncidenceCountCertificate

/--
Geometric version of `AllKuhnIncidenceCountCertificate`: the cross-incidence
fields are stated using label-free `matchPartnerStates`.
-/
structure AllKuhnGeometricIncidenceCountCertificate
    [Nontrivial ι]
    (hcard : 0 < Fintype.card ι)
    (L : GridSpernerLabeling ι N) (missing : ι) where
  boundary : FacetState (allKuhnCandidateCells (ι := ι) (N := N) hcard) → Prop
  start : FacetState (allKuhnCandidateCells (ι := ι) (N := N) hcard)
  start_boundary : boundary start
  start_almost : start.AlmostFullyLabeled L missing
  start_not_full : ¬ start.smallCell.FullyLabeled L
  start_match_card_eq_zero : start.matchPartnerStates.card = 0
  boundary_unique : ∀ st, boundary st → st = start
  nonboundary_match_card_eq_one :
    ∀ st, st.AlmostFullyLabeled L missing → ¬ boundary st →
      st.matchPartnerStates.card = 1

namespace AllKuhnGeometricIncidenceCountCertificate

noncomputable def toAllKuhnIncidenceCountCertificate
    [Nontrivial ι]
    {hcard : 0 < Fintype.card ι}
    {L : GridSpernerLabeling ι N} {missing : ι}
    (C : AllKuhnGeometricIncidenceCountCertificate
      (ι := ι) (N := N) hcard L missing) :
    AllKuhnIncidenceCountCertificate
      (ι := ι) (N := N) hcard L missing where
  boundary := C.boundary
  start := C.start
  start_boundary := C.start_boundary
  start_almost := C.start_almost
  start_not_full := C.start_not_full
  start_cross_card_eq_zero := by
    rw [C.start.crossMatchPartnerStates_card_eq_matchPartnerStates_card_of_almostFullyLabeled
      L missing C.start_almost]
    exact C.start_match_card_eq_zero
  boundary_unique := C.boundary_unique
  nonboundary_cross_card_eq_one := by
    intro st halmost hboundary
    rw [st.crossMatchPartnerStates_card_eq_matchPartnerStates_card_of_almostFullyLabeled
      L missing halmost]
    exact C.nonboundary_match_card_eq_one st halmost hboundary

end AllKuhnGeometricIncidenceCountCertificate

/--
Geometric incidence data in logical form: the start state has no geometric
match, and every relevant non-boundary almost facet has a unique geometric
match.
-/
structure AllKuhnGeometricIncidenceCertificate
    [Nontrivial ι]
    (hcard : 0 < Fintype.card ι)
    (L : GridSpernerLabeling ι N) (missing : ι) where
  boundary : FacetState (allKuhnCandidateCells (ι := ι) (N := N) hcard) → Prop
  start : FacetState (allKuhnCandidateCells (ι := ι) (N := N) hcard)
  start_boundary : boundary start
  start_almost : start.AlmostFullyLabeled L missing
  start_not_full : ¬ start.smallCell.FullyLabeled L
  start_no_match :
    ∀ st : FacetState (allKuhnCandidateCells (ι := ι) (N := N) hcard),
      ¬ start.Matches st
  boundary_unique : ∀ st, boundary st → st = start
  nonboundary_existsUnique_match :
    ∀ st, st.AlmostFullyLabeled L missing → ¬ boundary st →
      ∃! st' : FacetState (allKuhnCandidateCells (ι := ι) (N := N) hcard),
        st.Matches st'

namespace AllKuhnGeometricIncidenceCertificate

noncomputable def toGeometricIncidenceCountCertificate
    [Nontrivial ι]
    {hcard : 0 < Fintype.card ι}
    {L : GridSpernerLabeling ι N} {missing : ι}
    (C : AllKuhnGeometricIncidenceCertificate
      (ι := ι) (N := N) hcard L missing) :
    AllKuhnGeometricIncidenceCountCertificate
      (ι := ι) (N := N) hcard L missing where
  boundary := C.boundary
  start := C.start
  start_boundary := C.start_boundary
  start_almost := C.start_almost
  start_not_full := C.start_not_full
  start_match_card_eq_zero :=
    (C.start.matchPartnerStates_card_eq_zero_iff).mpr C.start_no_match
  boundary_unique := C.boundary_unique
  nonboundary_match_card_eq_one := by
    intro st halmost hboundary
    exact (st.matchPartnerStates_card_eq_one_iff_existsUnique_matches).mpr
      (C.nonboundary_existsUnique_match st halmost hboundary)

end AllKuhnGeometricIncidenceCertificate

/--
All-orders Kuhn candidate cells have reduced incidence-count certificates if
every labeling admits the remaining boundary/cross-match data.
-/
def HasAllKuhnIncidenceCountCertificates
    [Nontrivial ι]
    (hcard : 0 < Fintype.card ι) : Prop :=
  ∀ L : GridSpernerLabeling ι N,
    ∃ missing : ι,
      Nonempty (AllKuhnIncidenceCountCertificate
        (ι := ι) (N := N) hcard L missing)

theorem hasFacetCountingIncidenceCertificates_allKuhnCandidateCells
    [Nontrivial ι]
    (hcard : 0 < Fintype.card ι)
    (hU : HasAllKuhnIncidenceCountCertificates
      (ι := ι) (N := N) hcard) :
    (allKuhnCandidateCells (ι := ι) (N := N) hcard).HasFacetCountingIncidenceCertificates := by
  intro L
  rcases hU L with ⟨missing, hC⟩
  rcases hC with ⟨C⟩
  exact ⟨missing, ⟨C.toFacetCountingIncidenceCertificate⟩⟩

/--
All-orders Kuhn candidate cells have geometric incidence-count certificates if
every labeling admits the remaining label-free face-match counts.
-/
def HasAllKuhnGeometricIncidenceCountCertificates
    [Nontrivial ι]
    (hcard : 0 < Fintype.card ι) : Prop :=
  ∀ L : GridSpernerLabeling ι N,
    ∃ missing : ι,
      Nonempty (AllKuhnGeometricIncidenceCountCertificate
        (ι := ι) (N := N) hcard L missing)

theorem hasAllKuhnIncidenceCountCertificates_of_geometric
    [Nontrivial ι]
    (hcard : 0 < Fintype.card ι)
    (hU : HasAllKuhnGeometricIncidenceCountCertificates
      (ι := ι) (N := N) hcard) :
    HasAllKuhnIncidenceCountCertificates
      (ι := ι) (N := N) hcard := by
  intro L
  rcases hU L with ⟨missing, hC⟩
  rcases hC with ⟨C⟩
  exact ⟨missing, ⟨C.toAllKuhnIncidenceCountCertificate⟩⟩

/--
All-orders Kuhn candidate cells have logical geometric incidence certificates
if every labeling admits no-match/unique-match face-incidence data.
-/
def HasAllKuhnGeometricIncidenceCertificates
    [Nontrivial ι]
    (hcard : 0 < Fintype.card ι) : Prop :=
  ∀ L : GridSpernerLabeling ι N,
    ∃ missing : ι,
      Nonempty (AllKuhnGeometricIncidenceCertificate
        (ι := ι) (N := N) hcard L missing)

theorem hasAllKuhnGeometricIncidenceCountCertificates_of_geometric
    [Nontrivial ι]
    (hcard : 0 < Fintype.card ι)
    (hU : HasAllKuhnGeometricIncidenceCertificates
      (ι := ι) (N := N) hcard) :
    HasAllKuhnGeometricIncidenceCountCertificates
      (ι := ι) (N := N) hcard := by
  intro L
  rcases hU L with ⟨missing, hC⟩
  rcases hC with ⟨C⟩
  exact ⟨missing, ⟨C.toGeometricIncidenceCountCertificate⟩⟩

theorem exists_cell_over_slice_allKuhnCandidateCells
    (hcard : 0 < Fintype.card ι) (S : GridCubeSlice ι N) :
    ∃ P : GridCubeSlice.RankedSubsetPathCell S,
      (⟨S, P⟩ :
        Σ S : GridCubeSlice ι N, GridCubeSlice.RankedSubsetPathCell S) ∈
        (allKuhnCandidateCells (ι := ι) (N := N) hcard).cells := by
  classical
  by_cases hrpos : 0 < S.rank
  · by_cases hrlt : S.rank < Fintype.card ι
    · let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
      refine ⟨GridCubeSlice.RankedSubsetPathCell.cyclicWindowOfEquiv
        S e hcard hrpos hrlt, ?_⟩
      simpa [allKuhnCandidateCells] using
        mem_kuhnCandidateCellsOfOrders_cyclic
          (S := S) (e := e) (Finset.mem_univ e) hrpos hrlt
    · refine ⟨GridCubeSlice.RankedSubsetPathCell.singletonOfSlice S, ?_⟩
      simpa [allKuhnCandidateCells] using
        mem_kuhnCandidateCellsOfOrders_singleton_of_not_rank_lt
          (S := S) (orders := (Finset.univ :
            Finset (Fin (Fintype.card ι) ≃ ι))) hrpos hrlt
  · refine ⟨GridCubeSlice.RankedSubsetPathCell.singletonOfSlice S, ?_⟩
    simpa [allKuhnCandidateCells] using
      mem_kuhnCandidateCellsOfOrders_singleton_of_not_rank_pos
        (S := S) (orders := (Finset.univ :
          Finset (Fin (Fintype.card ι) ≃ ι))) hrpos

theorem allKuhnCandidateCells_refinesCubeSlices
    (hcard : 0 < Fintype.card ι) :
    (allKuhnCandidateCells (ι := ι) (N := N) hcard).toTriangulation.RefinesCubeSlices :=
  (allKuhnCandidateCells (ι := ι) (N := N) hcard).toTriangulation_refinesCubeSlices

end CubeSlicePathSubdivision

/--
Any Sperner triangulation refining the cube-slice subdivision proves the
cubical Sperner theorem.
-/
theorem cubicalSpernerProperty_of_refining_triangulation [DecidableEq ι]
    (T : GridTriangulation ι N) (hT : T.HasSpernerProperty)
    (hrefine : T.RefinesCubeSlices) :
    CubicalSpernerProperty (ι := ι) N := by
  intro L
  rcases hT L with ⟨cell, hcell, hfull⟩
  rcases hrefine cell hcell with ⟨S, hsubset⟩
  refine ⟨S, ?_⟩
  rw [GridSmallCell.fullyLabeled_iff] at hfull ⊢
  intro i
  rcases hfull i with ⟨a, ha, hlabel⟩
  exact ⟨a, hsubset ha, hlabel⟩

/--
A refining triangulation with pivot certificates proves cubical Sperner.
-/
theorem cubicalSpernerProperty_of_refining_pivotGraphCertificates [DecidableEq ι]
    (T : GridTriangulation ι N) (hT : T.HasPivotGraphCertificates)
    (hrefine : T.RefinesCubeSlices) :
    CubicalSpernerProperty (ι := ι) N :=
  cubicalSpernerProperty_of_refining_triangulation
    T (hasSpernerProperty_of_pivotGraphCertificates hT) hrefine

/--
A refining triangulation with canonical almost-face pivot certificates proves
cubical Sperner.
-/
theorem cubicalSpernerProperty_of_refining_almostFacePivotCertificates
    [DecidableEq ι]
    (T : GridTriangulation ι N) (hT : T.HasAlmostFacePivotCertificates)
    (hrefine : T.RefinesCubeSlices) :
    CubicalSpernerProperty (ι := ι) N :=
  cubicalSpernerProperty_of_refining_pivotGraphCertificates
    T (hasPivotGraphCertificates_of_almostFacePivotCertificates hT) hrefine

/--
All-mesh version of `cubicalSpernerProperty_of_refining_triangulation`.
-/
theorem cubicalSpernerPropertyAllMeshes_of_refining_triangulations
    [DecidableEq ι]
    (T : ∀ N : ℕ, 0 < N → GridTriangulation ι N)
    (hT : ∀ N hN, (T N hN).HasSpernerProperty)
    (hrefine : ∀ N hN, (T N hN).RefinesCubeSlices) :
    CubicalSpernerPropertyAllMeshes (ι := ι) := by
  intro N hN
  exact cubicalSpernerProperty_of_refining_triangulation
    (T N hN) (hT N hN) (hrefine N hN)

/--
All-mesh version of
`cubicalSpernerProperty_of_refining_pivotGraphCertificates`.
-/
theorem cubicalSpernerPropertyAllMeshes_of_refining_pivotGraphCertificates
    [DecidableEq ι]
    (T : ∀ N : ℕ, 0 < N → GridTriangulation ι N)
    (hT : ∀ N hN, (T N hN).HasPivotGraphCertificates)
    (hrefine : ∀ N hN, (T N hN).RefinesCubeSlices) :
    CubicalSpernerPropertyAllMeshes (ι := ι) := by
  intro N hN
  exact cubicalSpernerProperty_of_refining_pivotGraphCertificates
    (T N hN) (hT N hN) (hrefine N hN)

/--
All-mesh version of
`cubicalSpernerProperty_of_refining_almostFacePivotCertificates`.
-/
theorem cubicalSpernerPropertyAllMeshes_of_refining_almostFacePivotCertificates
    [DecidableEq ι]
    (T : ∀ N : ℕ, 0 < N → GridTriangulation ι N)
    (hT : ∀ N hN, (T N hN).HasAlmostFacePivotCertificates)
    (hrefine : ∀ N hN, (T N hN).RefinesCubeSlices) :
    CubicalSpernerPropertyAllMeshes (ι := ι) := by
  intro N hN
  exact cubicalSpernerProperty_of_refining_almostFacePivotCertificates
    (T N hN) (hT N hN) (hrefine N hN)

/--
A ranked-subset subdivision proves cubical Sperner as soon as its induced
small-cell triangulation satisfies Sperner's lemma.
-/
theorem cubicalSpernerProperty_of_ranked_subdivision [DecidableEq ι]
    (U : CubeSliceRankedSubdivision ι N)
    (hU : U.toTriangulation.HasSpernerProperty) :
    CubicalSpernerProperty (ι := ι) N :=
  cubicalSpernerProperty_of_refining_triangulation
    U.toTriangulation hU U.toTriangulation_refinesCubeSlices

/-- All-mesh version of `cubicalSpernerProperty_of_ranked_subdivision`. -/
theorem cubicalSpernerPropertyAllMeshes_of_ranked_subdivisions
    [DecidableEq ι]
    (U : ∀ N : ℕ, 0 < N → CubeSliceRankedSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasSpernerProperty) :
    CubicalSpernerPropertyAllMeshes (ι := ι) := by
  intro N hN
  exact cubicalSpernerProperty_of_ranked_subdivision
    (U N hN) (hU N hN)

/--
A ranked-subset subdivision proves cubical Sperner as soon as its induced
small-cell triangulation has pivot certificates.
-/
theorem cubicalSpernerProperty_of_ranked_subdivision_pivotGraphCertificates
    [DecidableEq ι]
    (U : CubeSliceRankedSubdivision ι N)
    (hU : U.toTriangulation.HasPivotGraphCertificates) :
    CubicalSpernerProperty (ι := ι) N :=
  cubicalSpernerProperty_of_ranked_subdivision U
    (hasSpernerProperty_of_pivotGraphCertificates hU)

/--
A ranked-subset subdivision proves cubical Sperner as soon as its induced
small-cell triangulation has canonical almost-face pivot certificates.
-/
theorem cubicalSpernerProperty_of_ranked_subdivision_almostFacePivotCertificates
    [DecidableEq ι]
    (U : CubeSliceRankedSubdivision ι N)
    (hU : U.toTriangulation.HasAlmostFacePivotCertificates) :
    CubicalSpernerProperty (ι := ι) N :=
  cubicalSpernerProperty_of_ranked_subdivision U
    (hasSpernerProperty_of_almostFacePivotCertificates hU)

/--
All-mesh version of
`cubicalSpernerProperty_of_ranked_subdivision_pivotGraphCertificates`.
-/
theorem cubicalSpernerPropertyAllMeshes_of_ranked_subdivision_pivotGraphCertificates
    [DecidableEq ι]
    (U : ∀ N : ℕ, 0 < N → CubeSliceRankedSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasPivotGraphCertificates) :
    CubicalSpernerPropertyAllMeshes (ι := ι) := by
  intro N hN
  exact cubicalSpernerProperty_of_ranked_subdivision_pivotGraphCertificates
    (U N hN) (hU N hN)

/--
All-mesh version of
`cubicalSpernerProperty_of_ranked_subdivision_almostFacePivotCertificates`.
-/
theorem cubicalSpernerPropertyAllMeshes_of_ranked_subdivision_almostFacePivotCertificates
    [DecidableEq ι]
    (U : ∀ N : ℕ, 0 < N → CubeSliceRankedSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasAlmostFacePivotCertificates) :
    CubicalSpernerPropertyAllMeshes (ι := ι) := by
  intro N hN
  exact cubicalSpernerProperty_of_ranked_subdivision_almostFacePivotCertificates
    (U N hN) (hU N hN)

/--
A path-shaped ranked-subset subdivision proves cubical Sperner as soon as its
induced small-cell triangulation satisfies Sperner's lemma.
-/
theorem cubicalSpernerProperty_of_path_subdivision [DecidableEq ι]
    (U : CubeSlicePathSubdivision ι N)
    (hU : U.toTriangulation.HasSpernerProperty) :
    CubicalSpernerProperty (ι := ι) N :=
  cubicalSpernerProperty_of_ranked_subdivision
    U.toRankedSubdivision hU

/-- All-mesh version of `cubicalSpernerProperty_of_path_subdivision`. -/
theorem cubicalSpernerPropertyAllMeshes_of_path_subdivisions
    [DecidableEq ι]
    (U : ∀ N : ℕ, 0 < N → CubeSlicePathSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasSpernerProperty) :
    CubicalSpernerPropertyAllMeshes (ι := ι) := by
  intro N hN
  exact cubicalSpernerProperty_of_path_subdivision
    (U N hN) (hU N hN)

/--
A path-shaped ranked-subset subdivision proves cubical Sperner as soon as its
induced small-cell triangulation has pivot certificates.
-/
theorem cubicalSpernerProperty_of_path_subdivision_pivotGraphCertificates
    [DecidableEq ι]
    (U : CubeSlicePathSubdivision ι N)
    (hU : U.toTriangulation.HasPivotGraphCertificates) :
    CubicalSpernerProperty (ι := ι) N :=
  cubicalSpernerProperty_of_path_subdivision U
    (hasSpernerProperty_of_pivotGraphCertificates hU)

/--
A path-shaped ranked-subset subdivision proves cubical Sperner as soon as its
concrete facet-state graph has parity certificates.
-/
theorem cubicalSpernerProperty_of_path_subdivision_facetPivotCertificates
    [DecidableEq ι]
    (U : CubeSlicePathSubdivision ι N)
    (hU : U.HasFacetPivotCertificates) :
    CubicalSpernerProperty (ι := ι) N :=
  cubicalSpernerProperty_of_path_subdivision_pivotGraphCertificates U
    (CubeSlicePathSubdivision.hasPivotGraphCertificates_of_facetPivotCertificates hU)

/--
A path-shaped ranked-subset subdivision proves cubical Sperner as soon as its
facet-state incidence data constructs concrete facet-pivot certificates.
-/
theorem cubicalSpernerProperty_of_path_subdivision_facetIncidenceCertificates
    [DecidableEq ι]
    (U : CubeSlicePathSubdivision ι N)
    (hU : U.HasFacetIncidenceCertificates) :
    CubicalSpernerProperty (ι := ι) N :=
  cubicalSpernerProperty_of_path_subdivision_facetPivotCertificates U
    (CubeSlicePathSubdivision.hasFacetPivotCertificates_of_facetIncidenceCertificates hU)

/--
A path-shaped ranked-subset subdivision proves cubical Sperner from the
counting-style incidence data expected from the Kuhn construction.
-/
theorem cubicalSpernerProperty_of_path_subdivision_facetCountingIncidenceCertificates
    [DecidableEq ι]
    (U : CubeSlicePathSubdivision ι N)
    (hU : U.HasFacetCountingIncidenceCertificates) :
    CubicalSpernerProperty (ι := ι) N :=
  cubicalSpernerProperty_of_path_subdivision_facetPivotCertificates U
    (CubeSlicePathSubdivision.hasFacetPivotCertificates_of_facetCountingIncidenceCertificates hU)

/--
The all-orders Kuhn candidate family proves cubical Sperner once its remaining
boundary/cross-match incidence counts are supplied.
-/
theorem cubicalSpernerProperty_of_allKuhnCandidateCells_incidenceCounts
    [DecidableEq ι] [Nontrivial ι]
    (hcard : 0 < Fintype.card ι)
    (hU : CubeSlicePathSubdivision.HasAllKuhnIncidenceCountCertificates
      (ι := ι) (N := N) hcard) :
    CubicalSpernerProperty (ι := ι) N :=
  cubicalSpernerProperty_of_path_subdivision_facetCountingIncidenceCertificates
    (CubeSlicePathSubdivision.allKuhnCandidateCells (ι := ι) (N := N) hcard)
    (CubeSlicePathSubdivision.hasFacetCountingIncidenceCertificates_allKuhnCandidateCells
      hcard hU)

/--
The all-orders Kuhn candidate family proves cubical Sperner once its remaining
boundary data and label-free face-match counts are supplied.
-/
theorem cubicalSpernerProperty_of_allKuhnCandidateCells_geometricIncidenceCounts
    [DecidableEq ι] [Nontrivial ι]
    (hcard : 0 < Fintype.card ι)
    (hU : CubeSlicePathSubdivision.HasAllKuhnGeometricIncidenceCountCertificates
      (ι := ι) (N := N) hcard) :
    CubicalSpernerProperty (ι := ι) N :=
  cubicalSpernerProperty_of_allKuhnCandidateCells_incidenceCounts
    hcard
    (CubeSlicePathSubdivision.hasAllKuhnIncidenceCountCertificates_of_geometric
      hcard hU)

/--
The all-orders Kuhn candidate family proves cubical Sperner once its remaining
boundary data and logical no-match/unique-match face-incidence data are
supplied.
-/
theorem cubicalSpernerProperty_of_allKuhnCandidateCells_geometricIncidence
    [DecidableEq ι] [Nontrivial ι]
    (hcard : 0 < Fintype.card ι)
    (hU : CubeSlicePathSubdivision.HasAllKuhnGeometricIncidenceCertificates
      (ι := ι) (N := N) hcard) :
    CubicalSpernerProperty (ι := ι) N :=
  cubicalSpernerProperty_of_allKuhnCandidateCells_geometricIncidenceCounts
    hcard
    (CubeSlicePathSubdivision.hasAllKuhnGeometricIncidenceCountCertificates_of_geometric
      hcard hU)

/--
A path-shaped ranked-subset subdivision proves cubical Sperner as soon as its
induced small-cell triangulation has canonical almost-face pivot certificates.
-/
theorem cubicalSpernerProperty_of_path_subdivision_almostFacePivotCertificates
    [DecidableEq ι]
    (U : CubeSlicePathSubdivision ι N)
    (hU : U.toTriangulation.HasAlmostFacePivotCertificates) :
    CubicalSpernerProperty (ι := ι) N :=
  cubicalSpernerProperty_of_path_subdivision U
    (hasSpernerProperty_of_almostFacePivotCertificates hU)

/--
All-mesh version of
`cubicalSpernerProperty_of_path_subdivision_pivotGraphCertificates`.
-/
theorem cubicalSpernerPropertyAllMeshes_of_path_subdivision_pivotGraphCertificates
    [DecidableEq ι]
    (U : ∀ N : ℕ, 0 < N → CubeSlicePathSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasPivotGraphCertificates) :
    CubicalSpernerPropertyAllMeshes (ι := ι) := by
  intro N hN
  exact cubicalSpernerProperty_of_path_subdivision_pivotGraphCertificates
    (U N hN) (hU N hN)

/--
All-mesh version of
`cubicalSpernerProperty_of_path_subdivision_facetPivotCertificates`.
-/
theorem cubicalSpernerPropertyAllMeshes_of_path_subdivision_facetPivotCertificates
    [DecidableEq ι]
    (U : ∀ N : ℕ, 0 < N → CubeSlicePathSubdivision ι N)
    (hU : ∀ N hN, (U N hN).HasFacetPivotCertificates) :
    CubicalSpernerPropertyAllMeshes (ι := ι) := by
  intro N hN
  exact cubicalSpernerProperty_of_path_subdivision_facetPivotCertificates
    (U N hN) (hU N hN)

/--
All-mesh version of
`cubicalSpernerProperty_of_path_subdivision_facetIncidenceCertificates`.
-/
theorem cubicalSpernerPropertyAllMeshes_of_path_subdivision_facetIncidenceCertificates
    [DecidableEq ι]
    (U : ∀ N : ℕ, 0 < N → CubeSlicePathSubdivision ι N)
    (hU : ∀ N hN, (U N hN).HasFacetIncidenceCertificates) :
    CubicalSpernerPropertyAllMeshes (ι := ι) := by
  intro N hN
  exact cubicalSpernerProperty_of_path_subdivision_facetIncidenceCertificates
    (U N hN) (hU N hN)

/--
All-mesh version of
`cubicalSpernerProperty_of_path_subdivision_facetCountingIncidenceCertificates`.
-/
theorem cubicalSpernerPropertyAllMeshes_of_path_subdivision_facetCountingIncidenceCertificates
    [DecidableEq ι]
    (U : ∀ N : ℕ, 0 < N → CubeSlicePathSubdivision ι N)
    (hU : ∀ N hN, (U N hN).HasFacetCountingIncidenceCertificates) :
    CubicalSpernerPropertyAllMeshes (ι := ι) := by
  intro N hN
  exact cubicalSpernerProperty_of_path_subdivision_facetCountingIncidenceCertificates
    (U N hN) (hU N hN)

/--
All-mesh all-orders Kuhn candidate family version of
`cubicalSpernerProperty_of_allKuhnCandidateCells_incidenceCounts`.
-/
theorem cubicalSpernerPropertyAllMeshes_of_allKuhnCandidateCells_incidenceCounts
    [DecidableEq ι] [Nontrivial ι]
    (hcard : 0 < Fintype.card ι)
    (hU : ∀ N : ℕ, 0 < N →
      CubeSlicePathSubdivision.HasAllKuhnIncidenceCountCertificates
        (ι := ι) (N := N) hcard) :
    CubicalSpernerPropertyAllMeshes (ι := ι) := by
  intro N hN
  exact cubicalSpernerProperty_of_allKuhnCandidateCells_incidenceCounts
    (N := N) hcard (hU N hN)

/--
All-mesh all-orders Kuhn candidate family version of
`cubicalSpernerProperty_of_allKuhnCandidateCells_geometricIncidenceCounts`.
-/
theorem cubicalSpernerPropertyAllMeshes_of_allKuhnCandidateCells_geometricIncidenceCounts
    [DecidableEq ι] [Nontrivial ι]
    (hcard : 0 < Fintype.card ι)
    (hU : ∀ N : ℕ, 0 < N →
      CubeSlicePathSubdivision.HasAllKuhnGeometricIncidenceCountCertificates
        (ι := ι) (N := N) hcard) :
    CubicalSpernerPropertyAllMeshes (ι := ι) := by
  intro N hN
  exact cubicalSpernerProperty_of_allKuhnCandidateCells_geometricIncidenceCounts
    (N := N) hcard (hU N hN)

/--
All-mesh all-orders Kuhn candidate family version of
`cubicalSpernerProperty_of_allKuhnCandidateCells_geometricIncidence`.
-/
theorem cubicalSpernerPropertyAllMeshes_of_allKuhnCandidateCells_geometricIncidence
    [DecidableEq ι] [Nontrivial ι]
    (hcard : 0 < Fintype.card ι)
    (hU : ∀ N : ℕ, 0 < N →
      CubeSlicePathSubdivision.HasAllKuhnGeometricIncidenceCertificates
        (ι := ι) (N := N) hcard) :
    CubicalSpernerPropertyAllMeshes (ι := ι) := by
  intro N hN
  exact cubicalSpernerProperty_of_allKuhnCandidateCells_geometricIncidence
    (N := N) hcard (hU N hN)

/--
All-mesh version of
`cubicalSpernerProperty_of_path_subdivision_almostFacePivotCertificates`.
-/
theorem cubicalSpernerPropertyAllMeshes_of_path_subdivision_almostFacePivotCertificates
    [DecidableEq ι]
    (U : ∀ N : ℕ, 0 < N → CubeSlicePathSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasAlmostFacePivotCertificates) :
    CubicalSpernerPropertyAllMeshes (ι := ι) := by
  intro N hN
  exact cubicalSpernerProperty_of_path_subdivision_almostFacePivotCertificates
    (U N hN) (hU N hN)

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

/--
Cubical Sperner plus approximate selections for every Kakutani correspondence
imply Kakutani's fixed-point property on the standard simplex.

The remaining analytic task is precisely the construction of the approximate
selections from Kakutani's hypotheses.
-/
theorem kakutaniFixedPointProperty_stdSimplex_of_cubicalSpernerPropertyAllMeshes
    (hCubicalSperner : CubicalSpernerPropertyAllMeshes (ι := ι))
    (hApprox :
      ∀ F : Correspondence (ι → ℝ) (ι → ℝ),
        KakutaniPremises (stdSimplex ℝ ι) F →
          ∀ n : ℕ,
            ApproximateKakutaniSelection
              (stdSimplex ℝ ι) F ((1 : ℝ) / ((n.succ : ℕ) : ℝ))) :
    KakutaniFixedPointProperty (stdSimplex ℝ ι) :=
  KakutaniFixedPointProperty.of_brouwer_approximateSelections
    (brouwerFixedPointProperty_stdSimplex_of_cubicalSpernerPropertyAllMeshes
      (ι := ι) hCubicalSperner)
    hApprox

/--
All-mesh ranked-subset subdivisions with Sperner's lemma imply the closed KKM
property on the standard simplex.
-/
theorem stdSimplexKKMProperty_of_ranked_subdivisions
    (U : ∀ N : ℕ, 0 < N → CubeSliceRankedSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasSpernerProperty) :
    StdSimplexKKMProperty ι :=
  stdSimplexKKMProperty_of_cubicalSpernerPropertyAllMeshes
    (cubicalSpernerPropertyAllMeshes_of_ranked_subdivisions U hU)

/--
All-mesh ranked-subset subdivisions with Sperner's lemma imply Brouwer's
fixed-point property on the standard simplex.
-/
theorem brouwerFixedPointProperty_stdSimplex_of_ranked_subdivisions
    (U : ∀ N : ℕ, 0 < N → CubeSliceRankedSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasSpernerProperty) :
    BrouwerFixedPointProperty (stdSimplex ℝ ι) :=
  brouwerFixedPointProperty_stdSimplex_of_cubicalSpernerPropertyAllMeshes
    (cubicalSpernerPropertyAllMeshes_of_ranked_subdivisions U hU)

/--
Ranked-subset subdivisions with Sperner's lemma plus approximate selections
imply Kakutani's fixed-point property on the standard simplex.
-/
theorem kakutaniFixedPointProperty_stdSimplex_of_ranked_subdivisions
    (U : ∀ N : ℕ, 0 < N → CubeSliceRankedSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasSpernerProperty)
    (hApprox :
      ∀ F : Correspondence (ι → ℝ) (ι → ℝ),
        KakutaniPremises (stdSimplex ℝ ι) F →
          ∀ n : ℕ,
            ApproximateKakutaniSelection
              (stdSimplex ℝ ι) F ((1 : ℝ) / ((n.succ : ℕ) : ℝ))) :
    KakutaniFixedPointProperty (stdSimplex ℝ ι) :=
  kakutaniFixedPointProperty_stdSimplex_of_cubicalSpernerPropertyAllMeshes
    (cubicalSpernerPropertyAllMeshes_of_ranked_subdivisions U hU)
    hApprox

/--
All-mesh ranked-subset subdivisions with pivot certificates imply the closed
KKM property on the standard simplex.
-/
theorem stdSimplexKKMProperty_of_ranked_subdivision_pivotGraphCertificates
    (U : ∀ N : ℕ, 0 < N → CubeSliceRankedSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasPivotGraphCertificates) :
    StdSimplexKKMProperty ι :=
  stdSimplexKKMProperty_of_cubicalSpernerPropertyAllMeshes
    (cubicalSpernerPropertyAllMeshes_of_ranked_subdivision_pivotGraphCertificates
      U hU)

/--
All-mesh ranked-subset subdivisions with pivot certificates imply Brouwer's
fixed-point property on the standard simplex.
-/
theorem brouwerFixedPointProperty_stdSimplex_of_ranked_subdivision_pivotGraphCertificates
    (U : ∀ N : ℕ, 0 < N → CubeSliceRankedSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasPivotGraphCertificates) :
    BrouwerFixedPointProperty (stdSimplex ℝ ι) :=
  brouwerFixedPointProperty_stdSimplex_of_cubicalSpernerPropertyAllMeshes
    (cubicalSpernerPropertyAllMeshes_of_ranked_subdivision_pivotGraphCertificates
      U hU)

/--
Ranked-subset subdivisions with pivot certificates plus approximate selections
imply Kakutani's fixed-point property on the standard simplex.
-/
theorem kakutaniFixedPointProperty_stdSimplex_of_ranked_subdivision_pivotGraphCertificates
    (U : ∀ N : ℕ, 0 < N → CubeSliceRankedSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasPivotGraphCertificates)
    (hApprox :
      ∀ F : Correspondence (ι → ℝ) (ι → ℝ),
        KakutaniPremises (stdSimplex ℝ ι) F →
          ∀ n : ℕ,
            ApproximateKakutaniSelection
              (stdSimplex ℝ ι) F ((1 : ℝ) / ((n.succ : ℕ) : ℝ))) :
    KakutaniFixedPointProperty (stdSimplex ℝ ι) :=
  kakutaniFixedPointProperty_stdSimplex_of_cubicalSpernerPropertyAllMeshes
    (cubicalSpernerPropertyAllMeshes_of_ranked_subdivision_pivotGraphCertificates
      U hU)
    hApprox

/--
All-mesh ranked-subset subdivisions with canonical almost-face pivot
certificates imply the closed KKM property on the standard simplex.
-/
theorem stdSimplexKKMProperty_of_ranked_subdivision_almostFacePivotCertificates
    (U : ∀ N : ℕ, 0 < N → CubeSliceRankedSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasAlmostFacePivotCertificates) :
    StdSimplexKKMProperty ι :=
  stdSimplexKKMProperty_of_cubicalSpernerPropertyAllMeshes
    (cubicalSpernerPropertyAllMeshes_of_ranked_subdivision_almostFacePivotCertificates
      U hU)

/--
All-mesh ranked-subset subdivisions with canonical almost-face pivot
certificates imply Brouwer's fixed-point property on the standard simplex.
-/
theorem brouwerFixedPointProperty_stdSimplex_of_ranked_subdivision_almostFacePivotCertificates
    (U : ∀ N : ℕ, 0 < N → CubeSliceRankedSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasAlmostFacePivotCertificates) :
    BrouwerFixedPointProperty (stdSimplex ℝ ι) :=
  brouwerFixedPointProperty_stdSimplex_of_cubicalSpernerPropertyAllMeshes
    (cubicalSpernerPropertyAllMeshes_of_ranked_subdivision_almostFacePivotCertificates
      U hU)

/--
Ranked-subset subdivisions with canonical almost-face pivot certificates plus
approximate selections imply Kakutani's fixed-point property on the standard
simplex.
-/
theorem kakutaniFixedPointProperty_stdSimplex_of_ranked_subdivision_almostFacePivotCertificates
    (U : ∀ N : ℕ, 0 < N → CubeSliceRankedSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasAlmostFacePivotCertificates)
    (hApprox :
      ∀ F : Correspondence (ι → ℝ) (ι → ℝ),
        KakutaniPremises (stdSimplex ℝ ι) F →
          ∀ n : ℕ,
            ApproximateKakutaniSelection
              (stdSimplex ℝ ι) F ((1 : ℝ) / ((n.succ : ℕ) : ℝ))) :
    KakutaniFixedPointProperty (stdSimplex ℝ ι) :=
  kakutaniFixedPointProperty_stdSimplex_of_cubicalSpernerPropertyAllMeshes
    (cubicalSpernerPropertyAllMeshes_of_ranked_subdivision_almostFacePivotCertificates
      U hU)
    hApprox

set_option linter.unusedSectionVars false

/--
All-mesh path-shaped ranked-subset subdivisions with Sperner's lemma imply the
closed KKM property on the standard simplex.
-/
theorem stdSimplexKKMProperty_of_path_subdivisions [DecidableEq ι]
    (U : ∀ N : ℕ, 0 < N → CubeSlicePathSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasSpernerProperty) :
    StdSimplexKKMProperty ι :=
  stdSimplexKKMProperty_of_cubicalSpernerPropertyAllMeshes
    (cubicalSpernerPropertyAllMeshes_of_path_subdivisions U hU)

/--
All-mesh path-shaped ranked-subset subdivisions with Sperner's lemma imply
Brouwer's fixed-point property on the standard simplex.
-/
theorem brouwerFixedPointProperty_stdSimplex_of_path_subdivisions [DecidableEq ι]
    (U : ∀ N : ℕ, 0 < N → CubeSlicePathSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasSpernerProperty) :
    BrouwerFixedPointProperty (stdSimplex ℝ ι) :=
  brouwerFixedPointProperty_stdSimplex_of_cubicalSpernerPropertyAllMeshes
    (cubicalSpernerPropertyAllMeshes_of_path_subdivisions U hU)

/--
Path-shaped ranked-subset subdivisions with Sperner's lemma plus approximate
selections imply Kakutani's fixed-point property on the standard simplex.
-/
theorem kakutaniFixedPointProperty_stdSimplex_of_path_subdivisions
    [DecidableEq ι]
    (U : ∀ N : ℕ, 0 < N → CubeSlicePathSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasSpernerProperty)
    (hApprox :
      ∀ F : Correspondence (ι → ℝ) (ι → ℝ),
        KakutaniPremises (stdSimplex ℝ ι) F →
          ∀ n : ℕ,
            ApproximateKakutaniSelection
              (stdSimplex ℝ ι) F ((1 : ℝ) / ((n.succ : ℕ) : ℝ))) :
    KakutaniFixedPointProperty (stdSimplex ℝ ι) :=
  kakutaniFixedPointProperty_stdSimplex_of_cubicalSpernerPropertyAllMeshes
    (cubicalSpernerPropertyAllMeshes_of_path_subdivisions U hU)
    hApprox

/--
All-mesh path-shaped ranked-subset subdivisions with pivot certificates imply
the closed KKM property on the standard simplex.
-/
theorem stdSimplexKKMProperty_of_path_subdivision_pivotGraphCertificates
    [DecidableEq ι]
    (U : ∀ N : ℕ, 0 < N → CubeSlicePathSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasPivotGraphCertificates) :
    StdSimplexKKMProperty ι :=
  stdSimplexKKMProperty_of_cubicalSpernerPropertyAllMeshes
    (cubicalSpernerPropertyAllMeshes_of_path_subdivision_pivotGraphCertificates
      U hU)

/--
All-mesh path-shaped ranked-subset subdivisions with pivot certificates imply
Brouwer's fixed-point property on the standard simplex.
-/
theorem brouwerFixedPointProperty_stdSimplex_of_path_subdivision_pivotGraphCertificates
    [DecidableEq ι]
    (U : ∀ N : ℕ, 0 < N → CubeSlicePathSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasPivotGraphCertificates) :
    BrouwerFixedPointProperty (stdSimplex ℝ ι) :=
  brouwerFixedPointProperty_stdSimplex_of_cubicalSpernerPropertyAllMeshes
    (cubicalSpernerPropertyAllMeshes_of_path_subdivision_pivotGraphCertificates
      U hU)

/--
Path-shaped ranked-subset subdivisions with pivot certificates plus
approximate selections imply Kakutani's fixed-point property on the standard
simplex.
-/
theorem kakutaniFixedPointProperty_stdSimplex_of_path_subdivision_pivotGraphCertificates
    [DecidableEq ι]
    (U : ∀ N : ℕ, 0 < N → CubeSlicePathSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasPivotGraphCertificates)
    (hApprox :
      ∀ F : Correspondence (ι → ℝ) (ι → ℝ),
        KakutaniPremises (stdSimplex ℝ ι) F →
          ∀ n : ℕ,
            ApproximateKakutaniSelection
              (stdSimplex ℝ ι) F ((1 : ℝ) / ((n.succ : ℕ) : ℝ))) :
    KakutaniFixedPointProperty (stdSimplex ℝ ι) :=
  kakutaniFixedPointProperty_stdSimplex_of_cubicalSpernerPropertyAllMeshes
    (cubicalSpernerPropertyAllMeshes_of_path_subdivision_pivotGraphCertificates
      U hU)
    hApprox

/--
All-mesh path-shaped ranked-subset subdivisions with canonical almost-face
pivot certificates imply the closed KKM property on the standard simplex.
-/
theorem stdSimplexKKMProperty_of_path_subdivision_almostFacePivotCertificates
    [DecidableEq ι]
    (U : ∀ N : ℕ, 0 < N → CubeSlicePathSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasAlmostFacePivotCertificates) :
    StdSimplexKKMProperty ι :=
  stdSimplexKKMProperty_of_cubicalSpernerPropertyAllMeshes
    (cubicalSpernerPropertyAllMeshes_of_path_subdivision_almostFacePivotCertificates
      U hU)

/--
All-mesh path-shaped ranked-subset subdivisions with canonical almost-face
pivot certificates imply Brouwer's fixed-point property on the standard
simplex.
-/
theorem brouwerFixedPointProperty_stdSimplex_of_path_subdivision_almostFacePivotCertificates
    [DecidableEq ι]
    (U : ∀ N : ℕ, 0 < N → CubeSlicePathSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasAlmostFacePivotCertificates) :
    BrouwerFixedPointProperty (stdSimplex ℝ ι) :=
  brouwerFixedPointProperty_stdSimplex_of_cubicalSpernerPropertyAllMeshes
    (cubicalSpernerPropertyAllMeshes_of_path_subdivision_almostFacePivotCertificates
      U hU)

/--
Path-shaped ranked-subset subdivisions with canonical almost-face pivot
certificates plus approximate selections imply Kakutani's fixed-point property
on the standard simplex.
-/
theorem kakutaniFixedPointProperty_stdSimplex_of_path_subdivision_almostFacePivotCertificates
    [DecidableEq ι]
    (U : ∀ N : ℕ, 0 < N → CubeSlicePathSubdivision ι N)
    (hU : ∀ N hN, (U N hN).toTriangulation.HasAlmostFacePivotCertificates)
    (hApprox :
      ∀ F : Correspondence (ι → ℝ) (ι → ℝ),
        KakutaniPremises (stdSimplex ℝ ι) F →
          ∀ n : ℕ,
            ApproximateKakutaniSelection
              (stdSimplex ℝ ι) F ((1 : ℝ) / ((n.succ : ℕ) : ℝ))) :
    KakutaniFixedPointProperty (stdSimplex ℝ ι) :=
  kakutaniFixedPointProperty_stdSimplex_of_cubicalSpernerPropertyAllMeshes
    (cubicalSpernerPropertyAllMeshes_of_path_subdivision_almostFacePivotCertificates
      U hU)
    hApprox

set_option linter.unusedSectionVars true

end GridTriangulation

end Correspondence

end EcoLean.GameTheory
