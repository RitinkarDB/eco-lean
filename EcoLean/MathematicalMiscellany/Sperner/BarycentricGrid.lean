import EcoLean.MathematicalMiscellany.Sperner

/-!
# Freudenthal data for n-dimensional Sperner

This file starts the concrete direction requested by rjwalters/lean-genius
issue #7965: n-dimensional Sperner's lemma via the Freudenthal triangulation.

The abstract parity theorem remains in `Sperner.lean`.  Here we only introduce
the concrete grid, simplex, facet, and colouring objects, plus the first basic
lemmas.  The full boundary induction and door-counting proof are deliberately
left as future work.
-/

namespace EconLib
namespace SpernerFreudenthal

open scoped BigOperators

/-- Grid points in the `d`-dimensional integer simplex of mesh `N`. -/
abbrev GridPoint (d N : ℕ) :=
  {x : Fin d → ℕ // ∑ i, x i ≤ N}

namespace GridPoint

/-- The implicit zeroth barycentric coordinate. -/
def zeroCoord {d N : ℕ} (x : GridPoint d N) : ℕ :=
  N - ∑ i, x.1 i

/-- Explicit coordinates that are positive.  This is useful for coverage audits. -/
noncomputable def positiveCoordSupport {d N : ℕ} (x : GridPoint d N) :
    Finset (Fin d) := by
  classical
  exact Finset.univ.filter fun i => 0 < x.1 i

/-- Increment one explicit coordinate as a raw coordinate vector. -/
def raise {d N : ℕ} (x : GridPoint d N) (i : Fin d) : Fin d → ℕ :=
  Function.update x.1 i (x.1 i + 1)

theorem sum_update_add_one {d : ℕ} (x : Fin d → ℕ) (i : Fin d) :
    (∑ j, Function.update x i (x i + 1) j) = (∑ j, x j) + 1 := by
  classical
  have h := Finset.sum_update_of_mem (s := (Finset.univ : Finset (Fin d)))
    (i := i) (f := x) (b := x i + 1) (by simp)
  have hsdiff : ((Finset.univ : Finset (Fin d)) \ {i}) = Finset.univ.erase i := by
    ext j
    simp
  simp [hsdiff] at h
  rw [h]
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin d)) x
    (Finset.mem_univ i)
  omega

theorem sum_update_sub_one {d : ℕ} (x : Fin d → ℕ) (i : Fin d)
    (h : 0 < x i) :
    (∑ j, Function.update x i (x i - 1) j) + 1 = (∑ j, x j) := by
  classical
  have hsum_update := Finset.sum_update_of_mem
    (s := (Finset.univ : Finset (Fin d))) (i := i) (f := x)
    (b := x i - 1) (by simp)
  have hsdiff : ((Finset.univ : Finset (Fin d)) \ {i}) = Finset.univ.erase i := by
    ext j
    simp
  simp [hsdiff] at hsum_update
  rw [hsum_update]
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin d)) x
    (Finset.mem_univ i)
  omega

def raiseOfSumLt {d N : ℕ}
    (x : GridPoint d N) (i : Fin d)
    (h : (∑ j, x.1 j) < N) :
    GridPoint d N := by
  refine ⟨Function.update x.1 i (x.1 i + 1), ?_⟩
  rw [sum_update_add_one]
  omega

def lowerOfPositive {d N : ℕ}
    (x : GridPoint d N) (i : Fin d)
    (h : 0 < x.1 i) :
    GridPoint d N := by
  refine ⟨Function.update x.1 i (x.1 i - 1), ?_⟩
  have hsum := sum_update_sub_one x.1 i h
  have hx := x.2
  omega

@[simp] theorem raiseOfSumLt_apply_same
    {d N : ℕ} (x : GridPoint d N) (i : Fin d)
    (h : (∑ j, x.1 j) < N) :
    (raiseOfSumLt x i h).1 i = x.1 i + 1 := by
  simp [raiseOfSumLt]

theorem raiseOfSumLt_apply_ne
    {d N : ℕ} (x : GridPoint d N) {i j : Fin d}
    (h : (∑ k, x.1 k) < N) (hij : j ≠ i) :
    (raiseOfSumLt x i h).1 j = x.1 j := by
  simp [raiseOfSumLt, Function.update, hij]

@[simp] theorem lowerOfPositive_apply_same
    {d N : ℕ} (x : GridPoint d N) (i : Fin d)
    (h : 0 < x.1 i) :
    (lowerOfPositive x i h).1 i = x.1 i - 1 := by
  simp [lowerOfPositive]

theorem lowerOfPositive_apply_ne
    {d N : ℕ} (x : GridPoint d N) {i j : Fin d}
    (h : 0 < x.1 i) (hij : j ≠ i) :
    (lowerOfPositive x i h).1 j = x.1 j := by
  simp [lowerOfPositive, Function.update, hij]

theorem coord_le_sum {d : ℕ} (x : Fin d → ℕ) (i : Fin d) :
    x i ≤ ∑ j, x j := by
  classical
  exact Finset.single_le_sum (by intro _j _hj; exact Nat.zero_le _) (by simp)

/-- All grid points, enumerated through bounded coordinate functions. -/
noncomputable def all (d N : ℕ) : Finset (GridPoint d N) := by
  classical
  exact ((Finset.univ : Finset (Fin d → Fin (N + 1))).filter fun x =>
      (∑ i : Fin d, (x i).val) ≤ N).attach.image fun x =>
    ⟨fun i => (x.1 i).val, by
      exact (Finset.mem_filter.mp x.2).2⟩

theorem mem_all {d N : ℕ} (x : GridPoint d N) : x ∈ all d N := by
  classical
  let bx : Fin d → Fin (N + 1) := fun i =>
    ⟨x.1 i, by
      have hle : x.1 i ≤ ∑ j, x.1 j := coord_le_sum x.1 i
      exact Nat.lt_succ_of_le (le_trans hle x.2)⟩
  have hbx : bx ∈ (Finset.univ.filter fun y : Fin d → Fin (N + 1) =>
      (∑ i : Fin d, (y i).val) ≤ N) := by
    simp [bx, x.2]
  refine Finset.mem_image.mpr ⟨⟨bx, hbx⟩, Finset.mem_attach _ _, ?_⟩
  ext i
  rfl

noncomputable instance instFintype (d N : ℕ) : Fintype (GridPoint d N) :=
  ⟨all d N, mem_all⟩

end GridPoint

/-- Labels for the `d`-dimensional simplex: one implicit label plus `d` explicit labels. -/
abbrev Label (d : ℕ) :=
  Fin (d + 1)

/--
A Freudenthal simplex is given by a base grid point and an order of the `d`
coordinate directions.  The admissibility condition ensures all prefix-raised
vertices remain in the grid.
-/
structure FreudenthalSimplex (d N : ℕ) where
  base : GridPoint d N
  perm : Equiv.Perm (Fin d)
  admissible : (∑ i, base.1 i) + d ≤ N

/-
Coverage issue:
The current `FreudenthalSimplex` family is the full-cube subcomplex inside the
explicit-coordinate simplex.  A covered point `x` must satisfy the necessary
condition in `covered_grid_point_has_rank_obstruction`: for some rank `k`,
`k ≤ positiveCoordSupport x.card` and `∑ xᵢ + d ≤ N + k`.  Thus points on the
slanted boundary with too few positive explicit coordinates are missed.  For
example, when `d = 2`, `N = 2`, the grid point `(2,0)` would require rank
`k = 2` by the sum inequality, but has only one positive explicit coordinate.

For full n-dimensional Sperner on the whole simplex, the cleaner repair is to
switch the concrete Freudenthal development to barycentric coordinates
`{x : Fin (d+1) → ℕ // ∑ i, x i = N}` and make Freudenthal moves transfer mass
between coordinates.  Alternatively, keep this file as a theorem for the
full-cube subcomplex and rename statements accordingly.
-/

namespace FreudenthalSimplex

/-- Coordinates raised in the first `k` steps of the simplex order. -/
def prefixRaisedCoords {d N : ℕ} (σ : FreudenthalSimplex d N)
    (k : Fin (d + 1)) : Finset (Fin d) :=
  Finset.univ.filter fun i => (σ.perm.symm i).val < k.val

theorem mem_prefixRaisedCoords_perm_iff {d N : ℕ}
    (σ : FreudenthalSimplex d N) (k : Fin (d + 1)) (j : Fin d) :
    σ.perm j ∈ σ.prefixRaisedCoords k ↔ j.val < k.val := by
  simp [prefixRaisedCoords]

theorem prefixRaisedCoords_card {d N : ℕ} (σ : FreudenthalSimplex d N)
    (j : Fin (d + 1)) :
    (σ.prefixRaisedCoords j).card = j.val := by
  classical
  let e : {i : Fin d // i ∈ σ.prefixRaisedCoords j} ≃ Fin j.val :=
    { toFun := fun i => ⟨(σ.perm.symm i.1).val, by
        have hi : i.1 ∈
            (Finset.univ.filter fun p : Fin d => (σ.perm.symm p).val < j.val) := by
          simpa [prefixRaisedCoords] using i.2
        exact (Finset.mem_filter.mp hi).2⟩
      invFun := fun r =>
        ⟨σ.perm ⟨r.val, by omega⟩, by
          rw [σ.mem_prefixRaisedCoords_perm_iff]
          exact r.isLt⟩
      left_inv := by
        intro i
        apply Subtype.ext
        simp
      right_inv := by
        intro r
        apply Fin.ext
        simp }
  calc
    (σ.prefixRaisedCoords j).card =
        Fintype.card {i : Fin d // i ∈ σ.prefixRaisedCoords j} := by
          exact (Fintype.card_coe (σ.prefixRaisedCoords j)).symm
    _ = Fintype.card (Fin j.val) := Fintype.card_congr e
    _ = j.val := Fintype.card_fin j.val

/-- The `k`th vertex of a Freudenthal simplex. -/
def vertex {d N : ℕ} (σ : FreudenthalSimplex d N) :
    Fin (d + 1) → GridPoint d N := by
  intro k
  refine
    ⟨fun i => σ.base.1 i + if i ∈ σ.prefixRaisedCoords k then 1 else 0, ?_⟩
  have hbonus :
      (∑ i : Fin d, (if i ∈ σ.prefixRaisedCoords k then 1 else 0 : ℕ)) ≤ d := by
    calc
      (∑ i : Fin d, (if i ∈ σ.prefixRaisedCoords k then 1 else 0 : ℕ))
          ≤ ∑ _i : Fin d, (1 : ℕ) := by
            refine Finset.sum_le_sum ?_
            intro i _hi
            by_cases hmem : i ∈ σ.prefixRaisedCoords k <;> simp [hmem]
      _ = d := by simp
  calc
    (∑ i : Fin d,
        (σ.base.1 i + if i ∈ σ.prefixRaisedCoords k then 1 else 0 : ℕ))
        =
        (∑ i : Fin d, σ.base.1 i) +
          ∑ i : Fin d, (if i ∈ σ.prefixRaisedCoords k then 1 else 0 : ℕ) := by
          rw [Finset.sum_add_distrib]
    _ ≤ (∑ i : Fin d, σ.base.1 i) + d := by
          exact Nat.add_le_add_left hbonus _
    _ ≤ N := σ.admissible

@[simp] theorem vertex_apply {d N : ℕ} (σ : FreudenthalSimplex d N)
    (k : Fin (d + 1)) (i : Fin d) :
    (σ.vertex k).1 i =
      σ.base.1 i + if i ∈ σ.prefixRaisedCoords k then 1 else 0 :=
  rfl

theorem vertex_sum {d N : ℕ} (σ : FreudenthalSimplex d N)
    (k : Fin (d + 1)) :
    (∑ i : Fin d, (σ.vertex k).1 i) =
      (∑ i : Fin d, σ.base.1 i) + k.val := by
  classical
  have hbonus :
      (∑ i : Fin d,
        (if i ∈ σ.prefixRaisedCoords k then 1 else 0 : ℕ)) =
        (σ.prefixRaisedCoords k).card := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
    simp [prefixRaisedCoords]
  calc
    (∑ i : Fin d, (σ.vertex k).1 i)
        =
        ∑ i : Fin d,
          (σ.base.1 i + if i ∈ σ.prefixRaisedCoords k then 1 else 0 : ℕ) := by
          rfl
    _ = (∑ i : Fin d, σ.base.1 i) +
          ∑ i : Fin d,
            (if i ∈ σ.prefixRaisedCoords k then 1 else 0 : ℕ) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i : Fin d, σ.base.1 i) + (σ.prefixRaisedCoords k).card := by
          rw [hbonus]
    _ = (∑ i : Fin d, σ.base.1 i) + k.val := by
          rw [σ.prefixRaisedCoords_card k]

theorem prefixRaisedCoords_subset_positiveCoordSupport {d N : ℕ}
    (σ : FreudenthalSimplex d N) (k : Fin (d + 1)) :
    σ.prefixRaisedCoords k ⊆ GridPoint.positiveCoordSupport (σ.vertex k) := by
  classical
  intro i hi
  rw [GridPoint.positiveCoordSupport]
  simp [hi]

theorem vertex_rank_le_positiveCoordSupport_card {d N : ℕ}
    (σ : FreudenthalSimplex d N) (k : Fin (d + 1)) :
    k.val ≤ (GridPoint.positiveCoordSupport (σ.vertex k)).card := by
  classical
  have hsubset := σ.prefixRaisedCoords_subset_positiveCoordSupport k
  have hcard := Finset.card_le_card hsubset
  simpa [σ.prefixRaisedCoords_card k] using hcard

@[simp] theorem vertex_zero {d N : ℕ} (σ : FreudenthalSimplex d N) :
    σ.vertex 0 = σ.base := by
  ext i
  simp [vertex, prefixRaisedCoords]

/-- A coordinate formula for successor vertices. -/
theorem vertex_succ_apply {d N : ℕ} (σ : FreudenthalSimplex d N)
    (k : Fin d) (i : Fin d) :
    (σ.vertex ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩).1 i =
      σ.base.1 i +
        if (σ.perm.symm i).val < k.val + 1 then 1 else 0 := by
  simp [vertex, prefixRaisedCoords]

theorem base_le_vertex {d N : ℕ} (σ : FreudenthalSimplex d N)
    (j : Fin (d + 1)) (i : Fin d) :
    σ.base.1 i ≤ (σ.vertex j).1 i := by
  rw [vertex_apply]
  by_cases h : i ∈ σ.prefixRaisedCoords j <;> simp [h]

/-- The top vertex is the vertex after all explicit coordinate directions are raised. -/
def topVertex {d N : ℕ} (σ : FreudenthalSimplex d N) : GridPoint d N :=
  σ.vertex ⟨d, by omega⟩

theorem topVertex_apply {d N : ℕ} (σ : FreudenthalSimplex d N) (i : Fin d) :
    σ.topVertex.1 i = σ.base.1 i + 1 := by
  rw [topVertex, vertex_apply]
  have htop : i ∈ σ.prefixRaisedCoords ⟨d, by omega⟩ := by
    rw [prefixRaisedCoords]
    simp
  simp [htop]

theorem base_ne_topVertex_of_pos {d N : ℕ} (σ : FreudenthalSimplex d N)
    (hd : 0 < d) :
    σ.base ≠ σ.topVertex := by
  intro h
  let i : Fin d := ⟨0, hd⟩
  have hcoord : σ.base.1 i = σ.topVertex.1 i := by
    simpa using congrArg (fun x : GridPoint d N => x.1 i) h
  have htop := σ.topVertex_apply i
  rw [htop] at hcoord
  omega

theorem vertex_le_top {d N : ℕ} (σ : FreudenthalSimplex d N)
    (j : Fin (d + 1)) (i : Fin d) :
    (σ.vertex j).1 i ≤ (σ.topVertex).1 i := by
  rw [topVertex, vertex_apply, vertex_apply]
  have htop : i ∈ σ.prefixRaisedCoords ⟨d, by omega⟩ := by
    rw [prefixRaisedCoords]
    simp
  by_cases hj : i ∈ σ.prefixRaisedCoords j <;> simp [hj, htop]

def firstCoordIndex (d : ℕ) (hd : 0 < d) : Fin d :=
  ⟨0, hd⟩

def lastCoordIndex (d : ℕ) (hd : 0 < d) : Fin d :=
  ⟨d - 1, by omega⟩

theorem vertex_one_le_of_pos_index {d N : ℕ} (σ : FreudenthalSimplex d N)
    (hd : 0 < d) {j : Fin (d + 1)} (hj : 0 < j.val) (i : Fin d) :
    (σ.vertex ⟨1, by omega⟩).1 i ≤ (σ.vertex j).1 i := by
  classical
  rw [vertex_apply, vertex_apply]
  by_cases hfirst : i ∈ σ.prefixRaisedCoords ⟨1, by omega⟩
  · have hjmem : i ∈ σ.prefixRaisedCoords j := by
      rw [prefixRaisedCoords] at hfirst ⊢
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hfirst ⊢
      omega
    simp [hfirst, hjmem]
  · by_cases hjmem : i ∈ σ.prefixRaisedCoords j <;> simp [hfirst, hjmem]

theorem vertex_one_apply {d N : ℕ} (σ : FreudenthalSimplex d N)
    (hd : 0 < d) (i : Fin d) :
    (σ.vertex ⟨1, by omega⟩).1 i =
      if i = σ.perm (firstCoordIndex d hd) then σ.base.1 i + 1 else σ.base.1 i := by
  classical
  rw [vertex_apply]
  by_cases hi : i = σ.perm (firstCoordIndex d hd)
  · have hmem : i ∈ σ.prefixRaisedCoords ⟨1, by omega⟩ := by
      have hmem_first :
          σ.perm (firstCoordIndex d hd) ∈ σ.prefixRaisedCoords ⟨1, by omega⟩ := by
        exact (σ.mem_prefixRaisedCoords_perm_iff ⟨1, by omega⟩
          (firstCoordIndex d hd)).mpr (by simp [firstCoordIndex])
      simpa [hi] using hmem_first
    rw [if_pos hmem, if_pos hi]
  · have hnot : i ∉ σ.prefixRaisedCoords ⟨1, by omega⟩ := by
      intro hmem
      rw [prefixRaisedCoords] at hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      have hsymm : σ.perm.symm i = firstCoordIndex d hd := by
        apply Fin.ext
        simp [firstCoordIndex]
        omega
      apply hi
      calc
        i = σ.perm (σ.perm.symm i) := by simp
        _ = σ.perm (firstCoordIndex d hd) := by rw [hsymm]
    rw [if_neg hnot, if_neg hi]
    simp

theorem vertex_one_sum {d N : ℕ} (σ : FreudenthalSimplex d N)
    (hd : 0 < d) :
    (∑ i : Fin d, (σ.vertex ⟨1, by omega⟩).1 i) =
      (∑ i : Fin d, σ.base.1 i) + 1 := by
  classical
  calc
    (∑ i : Fin d, (σ.vertex ⟨1, by omega⟩).1 i)
        = ∑ i : Fin d,
            Function.update σ.base.1
              (σ.perm (firstCoordIndex d hd))
              (σ.base.1 (σ.perm (firstCoordIndex d hd)) + 1) i := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [vertex_one_apply σ hd i]
          by_cases h : i = σ.perm (firstCoordIndex d hd) <;> simp [Function.update, h]
    _ = (∑ i : Fin d, σ.base.1 i) + 1 := by
          exact GridPoint.sum_update_add_one σ.base.1
            (σ.perm (firstCoordIndex d hd))

theorem vertex_one_eq_raiseOfSumLt {d N : ℕ} (σ : FreudenthalSimplex d N)
    (hd : 0 < d) (hsumlt : (∑ i, σ.base.1 i) < N) :
    σ.vertex ⟨1, by omega⟩ =
      GridPoint.raiseOfSumLt σ.base (σ.perm (firstCoordIndex d hd)) hsumlt := by
  classical
  ext i
  rw [vertex_one_apply σ hd i]
  by_cases h : i = σ.perm (firstCoordIndex d hd)
  · simp [GridPoint.raiseOfSumLt, Function.update, h]
  · simp [GridPoint.raiseOfSumLt, Function.update, h]

theorem vertexRankRelative_vertex_succ_from_vertex_one {d N : ℕ}
    (σ : FreudenthalSimplex d N)
    (r : Fin (d + 1)) (hr : r.val < d) :
    (∑ i : Fin d,
        ((σ.vertex ⟨r.val + 1, Nat.succ_lt_succ hr⟩).1 i -
          (σ.vertex ⟨1, by omega⟩).1 i)) = r.val := by
  classical
  let k : Fin (d + 1) := ⟨r.val + 1, Nat.succ_lt_succ hr⟩
  let one : Fin (d + 1) := ⟨1, by omega⟩
  have hsubset : σ.prefixRaisedCoords one ⊆ σ.prefixRaisedCoords k := by
    intro i hi
    rw [prefixRaisedCoords] at hi ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    dsimp [one, k] at hi ⊢
    omega
  calc
    (∑ i : Fin d, ((σ.vertex k).1 i - (σ.vertex one).1 i))
        = ∑ i : Fin d,
            (if i ∈ σ.prefixRaisedCoords k \ σ.prefixRaisedCoords one then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [vertex_apply, vertex_apply]
          by_cases hik : i ∈ σ.prefixRaisedCoords k
          · by_cases hi1 : i ∈ σ.prefixRaisedCoords one
            · simp [hik, hi1]
            · simp [hik, hi1]
          · have hi1 : i ∉ σ.prefixRaisedCoords one := fun hi1 => hik (hsubset hi1)
            simp [hik, hi1]
    _ = (σ.prefixRaisedCoords k \ σ.prefixRaisedCoords one).card := by
          rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
          congr 1
          ext i
          simp
    _ = r.val := by
          have hcard :
              (σ.prefixRaisedCoords k \ σ.prefixRaisedCoords one).card =
                (σ.prefixRaisedCoords k).card - (σ.prefixRaisedCoords one).card :=
            Finset.card_sdiff_of_subset hsubset
          rw [hcard, σ.prefixRaisedCoords_card k, σ.prefixRaisedCoords_card one]
          dsimp [k, one]

def vertexRankRelative {d N : ℕ} (σ : FreudenthalSimplex d N)
    (x : GridPoint d N) : ℕ :=
  ∑ i : Fin d, (x.1 i - σ.base.1 i)

theorem vertexRankRelative_vertex {d N : ℕ} (σ : FreudenthalSimplex d N)
    (j : Fin (d + 1)) :
    σ.vertexRankRelative (σ.vertex j) = j.val := by
  classical
  calc
    σ.vertexRankRelative (σ.vertex j)
        = ∑ i : Fin d, (if i ∈ σ.prefixRaisedCoords j then 1 else 0 : ℕ) := by
          unfold vertexRankRelative
          apply Finset.sum_congr rfl
          intro i _hi
          rw [vertex_apply]
          by_cases hmem : i ∈ σ.prefixRaisedCoords j <;> simp [hmem]
    _ = (σ.prefixRaisedCoords j).card := by
          rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
          simp [prefixRaisedCoords]
    _ = j.val := σ.prefixRaisedCoords_card j

theorem vertexRankRelative_eq_of_base_eq {d N : ℕ}
    {σ τ : FreudenthalSimplex d N} (hbase : τ.base = σ.base)
    (x : GridPoint d N) :
    τ.vertexRankRelative x = σ.vertexRankRelative x := by
  simp [vertexRankRelative, hbase]

theorem vertex_eq_of_rank_eq {d N : ℕ} (σ : FreudenthalSimplex d N)
    {j l : Fin (d + 1)} (h : j.val = l.val) :
    σ.vertex j = σ.vertex l := by
  exact congrArg σ.vertex (Fin.ext h)

theorem vertex_rank_eq_iff_index_eq {d N : ℕ} (σ : FreudenthalSimplex d N)
    {j l : Fin (d + 1)} :
    σ.vertexRankRelative (σ.vertex j) =
      σ.vertexRankRelative (σ.vertex l) ↔ j = l := by
  constructor
  · intro h
    rw [vertexRankRelative_vertex, vertexRankRelative_vertex] at h
    exact Fin.ext h
  · intro h
    subst h
    rfl

theorem prefixRaisedCoords_eq_of_same_base_vertex_eq {d N : ℕ}
    {σ τ : FreudenthalSimplex d N} {r : Fin (d + 1)}
    (hbase : τ.base = σ.base) (hvertex : τ.vertex r = σ.vertex r) :
    τ.prefixRaisedCoords r = σ.prefixRaisedCoords r := by
  classical
  ext i
  have hcoord : (τ.vertex r).1 i = (σ.vertex r).1 i := by
    simpa using congrArg (fun x : GridPoint d N => x.1 i) hvertex
  rw [vertex_apply, vertex_apply] at hcoord
  rw [hbase] at hcoord
  by_cases hτ : i ∈ τ.prefixRaisedCoords r
  · by_cases hσ : i ∈ σ.prefixRaisedCoords r
    · simp [hτ, hσ]
    · simp [hτ, hσ] at hcoord
  · by_cases hσ : i ∈ σ.prefixRaisedCoords r
    · simp [hτ, hσ] at hcoord
    · simp [hτ, hσ]

theorem eq_perm_of_mem_prefix_succ_not_mem_prefix {d N : ℕ}
    (σ : FreudenthalSimplex d N) (r : Fin d) {i : Fin d}
    (hin :
      i ∈ σ.prefixRaisedCoords ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩)
    (hnot : i ∉ σ.prefixRaisedCoords ⟨r.val, by omega⟩) :
    i = σ.perm r := by
  classical
  have hlt : (σ.perm.symm i).val < r.val + 1 := by
    have hin' : i ∈
        (Finset.univ.filter fun p : Fin d =>
          (σ.perm.symm p).val < r.val + 1) := by
      simpa [prefixRaisedCoords] using hin
    exact (Finset.mem_filter.mp hin').2
  have hnlt : ¬ (σ.perm.symm i).val < r.val := by
    intro hlt'
    apply hnot
    rw [prefixRaisedCoords]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt'⟩
  have hval : (σ.perm.symm i).val = r.val := by omega
  have hsymm : σ.perm.symm i = r := Fin.ext hval
  have happ := congrArg σ.perm hsymm
  simpa using happ

theorem perm_eq_of_prefix_consecutive_eq {d N : ℕ}
    (σ τ : FreudenthalSimplex d N) (r : Fin d)
    (hpre :
      τ.prefixRaisedCoords ⟨r.val, by omega⟩ =
        σ.prefixRaisedCoords ⟨r.val, by omega⟩)
    (hsucc :
      τ.prefixRaisedCoords ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ =
        σ.prefixRaisedCoords ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩) :
    τ.perm r = σ.perm r := by
  classical
  have hinτ :
      τ.perm r ∈
        τ.prefixRaisedCoords ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ := by
    rw [τ.mem_prefixRaisedCoords_perm_iff]
    exact Nat.lt_succ_self r.val
  have hnotτ : τ.perm r ∉ τ.prefixRaisedCoords ⟨r.val, by omega⟩ := by
    rw [τ.mem_prefixRaisedCoords_perm_iff]
    exact Nat.lt_irrefl r.val
  have hinσ :
      τ.perm r ∈
        σ.prefixRaisedCoords ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ := by
    simpa [hsucc] using hinτ
  have hnotσ : τ.perm r ∉ σ.prefixRaisedCoords ⟨r.val, by omega⟩ := by
    simpa [hpre] using hnotτ
  exact eq_perm_of_mem_prefix_succ_not_mem_prefix σ r hinσ hnotσ

theorem perm_eq_of_consecutive_vertex_eq {d N : ℕ}
    (σ τ : FreudenthalSimplex d N) (r s : Fin d)
    (h0 :
      τ.vertex ⟨r.val, by omega⟩ =
        σ.vertex ⟨s.val, by omega⟩)
    (h1 :
      τ.vertex ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ =
        σ.vertex ⟨s.val + 1, Nat.succ_lt_succ s.isLt⟩) :
    τ.perm r = σ.perm s := by
  classical
  let i : Fin d := τ.perm r
  have hτnot : i ∉ τ.prefixRaisedCoords ⟨r.val, by omega⟩ := by
    rw [τ.mem_prefixRaisedCoords_perm_iff]
    exact Nat.lt_irrefl r.val
  have hτin : i ∈ τ.prefixRaisedCoords ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ := by
    rw [τ.mem_prefixRaisedCoords_perm_iff]
    exact Nat.lt_succ_self r.val
  have hcoord0 := congrArg (fun x : GridPoint d N => x.1 i) h0
  have hcoord1 := congrArg (fun x : GridPoint d N => x.1 i) h1
  change (τ.vertex ⟨r.val, by omega⟩).1 i =
      (σ.vertex ⟨s.val, by omega⟩).1 i at hcoord0
  change (τ.vertex ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩).1 i =
      (σ.vertex ⟨s.val + 1, Nat.succ_lt_succ s.isLt⟩).1 i at hcoord1
  rw [vertex_apply, vertex_apply] at hcoord0 hcoord1
  simp [hτnot] at hcoord0
  simp [hτin] at hcoord1
  have hinσ : i ∈ σ.prefixRaisedCoords ⟨s.val + 1, Nat.succ_lt_succ s.isLt⟩ := by
    by_contra hnot
    simp [hnot] at hcoord1
    by_cases hpre : i ∈ σ.prefixRaisedCoords ⟨s.val, by omega⟩
    · simp [hpre] at hcoord0
      omega
    · simp [hpre] at hcoord0
      omega
  have hcoord1' := hcoord1
  simp [hinσ] at hcoord1'
  have hnotσ : i ∉ σ.prefixRaisedCoords ⟨s.val, by omega⟩ := by
    intro hin
    simp [hin] at hcoord0
    have hcoord1'' := hcoord1'
    omega
  have hi : i = σ.perm s :=
    eq_perm_of_mem_prefix_succ_not_mem_prefix σ s hinσ hnotσ
  simpa [i] using hi

theorem vertex_injective {d N : ℕ} (σ : FreudenthalSimplex d N) :
    Function.Injective σ.vertex := by
  intro k l h
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hkl | hlk
  · have hk_d : k.val < d :=
      Nat.lt_of_lt_of_le hkl (Nat.le_of_lt_succ l.isLt)
    let i : Fin d := ⟨k.val, hk_d⟩
    have hcoord := congrArg (fun x : GridPoint d N => x.1 (σ.perm i)) h
    have hnot : ¬ σ.perm i ∈ σ.prefixRaisedCoords k := by
      rw [σ.mem_prefixRaisedCoords_perm_iff k i]
      exact Nat.lt_irrefl _
    have hin : σ.perm i ∈ σ.prefixRaisedCoords l := by
      rw [σ.mem_prefixRaisedCoords_perm_iff l i]
      exact hkl
    simp [hnot, hin] at hcoord
  · have hl_d : l.val < d :=
      Nat.lt_of_lt_of_le hlk (Nat.le_of_lt_succ k.isLt)
    let i : Fin d := ⟨l.val, hl_d⟩
    have hcoord := congrArg (fun x : GridPoint d N => x.1 (σ.perm i)) h
    have hin : σ.perm i ∈ σ.prefixRaisedCoords k := by
      rw [σ.mem_prefixRaisedCoords_perm_iff k i]
      exact hlk
    have hnot : ¬ σ.perm i ∈ σ.prefixRaisedCoords l := by
      rw [σ.mem_prefixRaisedCoords_perm_iff l i]
      exact Nat.lt_irrefl _
    simp [hnot, hin] at hcoord

/-- The vertex set of a Freudenthal simplex. -/
noncomputable def vertices {d N : ℕ} (σ : FreudenthalSimplex d N) :
    Finset (GridPoint d N) := by
  classical
  exact Finset.univ.image σ.vertex

/-- A finite vertex set is one of the currently represented Freudenthal cells. -/
def IsFreudenthalCellVertexSet {d N : ℕ} (S : Finset (GridPoint d N)) : Prop :=
  ∃ σ : FreudenthalSimplex d N, σ.vertices = S

theorem mem_vertices_iff {d N : ℕ} (σ : FreudenthalSimplex d N)
    (v : GridPoint d N) :
    v ∈ σ.vertices ↔ ∃ k : Fin (d + 1), σ.vertex k = v := by
  classical
  simp [vertices]

theorem every_freudenthal_vertex_in_grid {d N : ℕ}
    (σ : FreudenthalSimplex d N) (v : GridPoint d N)
    (_hv : v ∈ σ.vertices) :
    True := by
  trivial

theorem every_grid_point_mem_some_freudenthal_simplex_of_room {d N : ℕ}
    (x : GridPoint d N)
    (hroom : (∑ i, x.1 i) + d ≤ N) :
    ∃ σ : FreudenthalSimplex d N, x ∈ σ.vertices := by
  classical
  let σ : FreudenthalSimplex d N :=
    { base := x
      perm := Equiv.refl (Fin d)
      admissible := hroom }
  refine ⟨σ, ?_⟩
  rw [σ.mem_vertices_iff]
  exact ⟨0, σ.vertex_zero⟩

theorem covered_grid_point_has_rank_obstruction {d N : ℕ}
    (σ : FreudenthalSimplex d N) (x : GridPoint d N)
    (hx : x ∈ σ.vertices) :
    ∃ k : Fin (d + 1),
      k.val ≤ (GridPoint.positiveCoordSupport x).card ∧
      (∑ i : Fin d, x.1 i) + d ≤ N + k.val := by
  classical
  rcases (σ.mem_vertices_iff x).mp hx with ⟨k, hkx⟩
  refine ⟨k, ?_, ?_⟩
  · have hle := σ.vertex_rank_le_positiveCoordSupport_card k
    simpa [hkx] using hle
  · have hxsum :
        (∑ i : Fin d, x.1 i) =
          ∑ i : Fin d, (σ.vertex k).1 i := by
      rw [← hkx]
    rw [hxsum, σ.vertex_sum k]
    have hadm := σ.admissible
    omega

theorem eq_base_of_vertex_le_all_vertices {d N : ℕ} (σ : FreudenthalSimplex d N)
    (x : GridPoint d N) (hxmem : x ∈ σ.vertices)
    (hle : ∀ y ∈ σ.vertices, ∀ i : Fin d, x.1 i ≤ y.1 i) :
    x = σ.base := by
  classical
  rcases (σ.mem_vertices_iff x).mp hxmem with ⟨j, hj⟩
  ext i
  have hbase_mem : σ.base ∈ σ.vertices := by
    rw [σ.mem_vertices_iff]
    exact ⟨0, σ.vertex_zero⟩
  have hx_le_base := hle σ.base hbase_mem i
  have hbase_le_x : σ.base.1 i ≤ x.1 i := by
    rw [← hj]
    exact σ.base_le_vertex j i
  omega

theorem eq_top_of_all_vertices_le {d N : ℕ} (σ : FreudenthalSimplex d N)
    (x : GridPoint d N) (hxmem : x ∈ σ.vertices)
    (hle : ∀ y ∈ σ.vertices, ∀ i : Fin d, y.1 i ≤ x.1 i) :
    x = σ.topVertex := by
  classical
  rcases (σ.mem_vertices_iff x).mp hxmem with ⟨j, hj⟩
  ext i
  have htop_mem : σ.topVertex ∈ σ.vertices := by
    rw [σ.mem_vertices_iff]
    exact ⟨⟨d, by omega⟩, rfl⟩
  have htop_le_x := hle σ.topVertex htop_mem i
  have hx_le_top : x.1 i ≤ σ.topVertex.1 i := by
    rw [← hj]
    exact σ.vertex_le_top j i
  omega

noncomputable instance instDecidableEq (d N : ℕ) :
    DecidableEq (FreudenthalSimplex d N) :=
  Classical.decEq _

/-- All admissible Freudenthal simplices for the current representation. -/
noncomputable def all (d N : ℕ) : Finset (FreudenthalSimplex d N) := by
  classical
  exact (((Finset.univ : Finset (GridPoint d N)).product
      (Finset.univ : Finset (Equiv.Perm (Fin d)))).filter fun bp =>
        (∑ i, bp.1.1 i) + d ≤ N).attach.image fun bp =>
    { base := bp.1.1
      perm := bp.1.2
      admissible := by exact (Finset.mem_filter.mp bp.2).2 }

theorem mem_all {d N : ℕ} (σ : FreudenthalSimplex d N) : σ ∈ all d N := by
  classical
  have hbp : (σ.base, σ.perm) ∈
      (((Finset.univ : Finset (GridPoint d N)).product
        (Finset.univ : Finset (Equiv.Perm (Fin d)))).filter fun bp =>
          (∑ i, bp.1.1 i) + d ≤ N) := by
    simp [σ.admissible]
  refine Finset.mem_image.mpr ⟨⟨(σ.base, σ.perm), hbp⟩, Finset.mem_attach _ _, ?_⟩
  cases σ
  rfl

noncomputable instance instFintype (d N : ℕ) : Fintype (FreudenthalSimplex d N) :=
  ⟨all d N, mem_all⟩

end FreudenthalSimplex

/-- A facet of a Freudenthal simplex, represented by the omitted vertex. -/
structure FreudenthalFacet (d N : ℕ) where
  simplex : FreudenthalSimplex d N
  omitted : Fin (d + 1)

namespace FreudenthalFacet

/-- Vertices of a facet, obtained by deleting one simplex vertex. -/
noncomputable def vertices {d N : ℕ} (F : FreudenthalFacet d N) :
    Finset (GridPoint d N) := by
  classical
  exact (Finset.univ.erase F.omitted).image F.simplex.vertex

theorem mem_vertices_iff {d N : ℕ} (F : FreudenthalFacet d N)
    (v : GridPoint d N) :
    v ∈ F.vertices ↔
      ∃ k : Fin (d + 1), k ≠ F.omitted ∧ F.simplex.vertex k = v := by
  classical
  simp [vertices]

theorem vertices_subset_simplex_vertices {d N : ℕ} (F : FreudenthalFacet d N) :
    F.vertices ⊆ F.simplex.vertices := by
  classical
  intro v hv
  rcases (F.mem_vertices_iff v).mp hv with ⟨k, _hk, rfl⟩
  rw [F.simplex.mem_vertices_iff]
  exact ⟨k, rfl⟩

/-- The geometric key of a facet is its vertex set. -/
noncomputable def key {d N : ℕ} (F : FreudenthalFacet d N) : Finset (GridPoint d N) :=
  F.vertices

/-- Geometric equality of syntactic facets. -/
def GeomEq {d N : ℕ} (F G : FreudenthalFacet d N) : Prop :=
  F.key = G.key

theorem geomEq_iff {d N : ℕ} (F G : FreudenthalFacet d N) :
    F.GeomEq G ↔ F.vertices = G.vertices := by
  rfl

theorem geomEq_refl {d N : ℕ} (F : FreudenthalFacet d N) :
    F.GeomEq F := by
  rfl

theorem geomEq_symm {d N : ℕ} {F G : FreudenthalFacet d N}
    (h : F.GeomEq G) : G.GeomEq F := by
  exact h.symm

theorem geomEq_trans {d N : ℕ} {F G H : FreudenthalFacet d N}
    (hFG : F.GeomEq G) (hGH : G.GeomEq H) : F.GeomEq H := by
  exact hFG.trans hGH

noncomputable instance instDecidableEq (d N : ℕ) :
    DecidableEq (FreudenthalFacet d N) :=
  Classical.decEq _

/-- All syntactic Freudenthal facets. -/
noncomputable def all (d N : ℕ) : Finset (FreudenthalFacet d N) := by
  classical
  exact ((Finset.univ : Finset (FreudenthalSimplex d N)).product
    (Finset.univ : Finset (Fin (d + 1)))).image fun sk =>
      ⟨sk.1, sk.2⟩

theorem mem_all {d N : ℕ} (F : FreudenthalFacet d N) : F ∈ all d N := by
  classical
  refine Finset.mem_image.mpr ?_
  refine ⟨(F.simplex, F.omitted), by simp, ?_⟩
  cases F
  rfl

noncomputable instance instFintype (d N : ℕ) : Fintype (FreudenthalFacet d N) :=
  ⟨all d N, mem_all⟩

end FreudenthalFacet

/-- A geometric Freudenthal facet is a vertex-set key known to arise from a syntactic facet. -/
abbrev FreudenthalGeomFacet (d N : ℕ) :=
  {K : Finset (GridPoint d N) // ∃ F : FreudenthalFacet d N, F.vertices = K}

namespace FreudenthalFacet

/-- Forget the syntactic owner and omitted index, keeping only the geometric facet key. -/
noncomputable def toGeomFacet {d N : ℕ} (F : FreudenthalFacet d N) :
    FreudenthalGeomFacet d N :=
  ⟨F.vertices, ⟨F, rfl⟩⟩

theorem toGeomFacet_eq_iff {d N : ℕ} (F G : FreudenthalFacet d N) :
    F.toGeomFacet = G.toGeomFacet ↔ F.GeomEq G := by
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact h

end FreudenthalFacet

namespace FreudenthalSimplex

/-- The facet of a simplex obtained by omitting one vertex. -/
def facet {d N : ℕ} (σ : FreudenthalSimplex d N)
    (k : Fin (d + 1)) : FreudenthalFacet d N :=
  ⟨σ, k⟩

theorem facet_vertices_subset {d N : ℕ} (σ : FreudenthalSimplex d N)
    (k : Fin (d + 1)) :
    (σ.facet k).vertices ⊆ σ.vertices :=
  (σ.facet k).vertices_subset_simplex_vertices

/-- The geometric facets of a simplex, forgetting omitted-index syntax. -/
noncomputable def geomFacets {d N : ℕ} (σ : FreudenthalSimplex d N) :
    Finset (FreudenthalGeomFacet d N) := by
  classical
  exact Finset.univ.image fun k : Fin (d + 1) =>
    (FreudenthalFacet.mk σ k).toGeomFacet

theorem mem_geomFacets_iff {d N : ℕ}
    (σ : FreudenthalSimplex d N) (K : FreudenthalGeomFacet d N) :
    K ∈ σ.geomFacets ↔
      ∃ k : Fin (d + 1), (FreudenthalFacet.mk σ k).toGeomFacet = K := by
  classical
  simp [geomFacets]

/-- Cyclically shift finite coordinates left: `0 ↦ 1 ↦ ... ↦ 0`. -/
noncomputable def shiftLeftIndex (d : ℕ) : Equiv.Perm (Fin d) :=
  finRotate d

/-- Cyclically shift finite coordinates right. -/
noncomputable def shiftRightIndex (d : ℕ) : Equiv.Perm (Fin d) :=
  (finRotate d).symm

theorem first_perm_mem_prefix_of_pos {d N : ℕ} (σ : FreudenthalSimplex d N)
    (hd : 0 < d) {j : Fin (d + 1)} (hj : 0 < j.val) :
    σ.perm (firstCoordIndex d hd) ∈ σ.prefixRaisedCoords j := by
  rw [σ.mem_prefixRaisedCoords_perm_iff]
  dsimp [firstCoordIndex]
  exact hj

theorem last_perm_not_mem_prefix_of_lt_last {d N : ℕ} (σ : FreudenthalSimplex d N)
    (hd : 0 < d) {j : Fin (d + 1)} (hj : j.val < d) :
    σ.perm (lastCoordIndex d hd) ∉ σ.prefixRaisedCoords j := by
  rw [σ.mem_prefixRaisedCoords_perm_iff]
  dsimp [lastCoordIndex]
  omega

theorem shiftLeftIndex_apply_of_lt {d : ℕ} {j : Fin d}
    (h : j.val + 1 < d) :
    shiftLeftIndex d j = ⟨j.val + 1, h⟩ := by
  cases d with
  | zero => omega
  | succ n =>
      ext
      simp [shiftLeftIndex, finRotate_succ_apply, Fin.add_def, Nat.mod_eq_of_lt h]

theorem shiftLeftIndex_apply_last {d : ℕ} (hd : 0 < d) :
    shiftLeftIndex d (lastCoordIndex d hd) = firstCoordIndex d hd := by
  cases d with
  | zero => omega
  | succ n =>
      change finRotate (n + 1) ⟨n, by omega⟩ = ⟨0, by omega⟩
      simpa using (finRotate_last' (n := n))

theorem shiftRightIndex_apply_of_pos {d : ℕ} {j : Fin d}
    (h : 0 < j.val) :
    shiftRightIndex d j =
      ⟨j.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ := by
  cases d with
  | zero => omega
  | succ n =>
      ext
      have hj : j ≠ 0 := by
        intro hj0
        have hv : j.val = 0 := by simpa using congrArg Fin.val hj0
        omega
      rw [show (shiftRightIndex (n + 1) j).val = ((finRotate (n + 1)).symm j).val by
        rfl]
      haveI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
      rw [coe_finRotate_symm_of_ne_zero hj]

theorem shiftRightIndex_apply_zero {d : ℕ} (hd : 0 < d) :
    shiftRightIndex d (firstCoordIndex d hd) = lastCoordIndex d hd := by
  cases d with
  | zero => omega
  | succ n =>
      change (finRotate (n + 1)).symm ⟨0, by omega⟩ = ⟨n, by omega⟩
      rw [Equiv.symm_apply_eq]
      symm
      simpa using (finRotate_last' (n := n))

/-- Endpoint upper neighbour order: drop the first direction to the end. -/
noncomputable def upperShiftPerm {d N : ℕ}
    (σ : FreudenthalSimplex d N) : Equiv.Perm (Fin d) :=
  (shiftLeftIndex d).trans σ.perm

/-- Endpoint lower neighbour order: move the last direction to the front. -/
noncomputable def lowerShiftPerm {d N : ℕ}
    (σ : FreudenthalSimplex d N) : Equiv.Perm (Fin d) :=
  (shiftRightIndex d).trans σ.perm

theorem upperShift_prefix_mem_iff {d N : ℕ} (σ : FreudenthalSimplex d N)
    (l : Fin (d + 1)) (hl : l.val < d) (i : Fin d) :
    i ∈ ({ σ with perm := σ.upperShiftPerm } : FreudenthalSimplex d N).prefixRaisedCoords l
      ↔
    0 < (σ.perm.symm i).val ∧ (σ.perm.symm i).val < l.val + 1 := by
  rw [prefixRaisedCoords]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [show (({ σ with perm := σ.upperShiftPerm } : FreudenthalSimplex d N).perm.symm i) =
      shiftRightIndex d (σ.perm.symm i) by
    rfl]
  constructor
  · intro h
    by_cases hq0 : (σ.perm.symm i).val = 0
    · have hd : 0 < d :=
        Nat.lt_of_le_of_lt (Nat.zero_le _) (σ.perm.symm i).isLt
      have hq : σ.perm.symm i = firstCoordIndex d hd := by
        ext
        exact hq0
      rw [hq, shiftRightIndex_apply_zero hd] at h
      dsimp [lastCoordIndex] at h
      omega
    · have hpos : 0 < (σ.perm.symm i).val := Nat.pos_of_ne_zero hq0
      have hs := shiftRightIndex_apply_of_pos (d := d)
        (j := σ.perm.symm i) hpos
      rw [hs] at h
      constructor
      · exact hpos
      · have hsub : (σ.perm.symm i).val - 1 < l.val := by
          simpa using h
        omega
  · intro h
    rcases h with ⟨hpos, hlt⟩
    have hs := shiftRightIndex_apply_of_pos (d := d)
      (j := σ.perm.symm i) hpos
    rw [hs]
    have : (σ.perm.symm i).val - 1 < l.val := by omega
    simpa using this

theorem lowerShift_prefix_mem_iff {d N : ℕ} (σ : FreudenthalSimplex d N)
    (hd : 0 < d) (l : Fin (d + 1)) (hl0 : 0 < l.val) (i : Fin d) :
    i ∈ ({ σ with perm := σ.lowerShiftPerm } : FreudenthalSimplex d N).prefixRaisedCoords l
      ↔
    σ.perm.symm i = lastCoordIndex d hd ∨
      (σ.perm.symm i).val + 1 < l.val := by
  rw [prefixRaisedCoords]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [show (({ σ with perm := σ.lowerShiftPerm } : FreudenthalSimplex d N).perm.symm i) =
      shiftLeftIndex d (σ.perm.symm i) by
    rfl]
  constructor
  · intro h
    by_cases hlast : σ.perm.symm i = lastCoordIndex d hd
    · exact Or.inl hlast
    · right
      have hlt_index : (σ.perm.symm i).val + 1 < d := by
        by_contra hnot
        have hle : d ≤ (σ.perm.symm i).val + 1 := Nat.le_of_not_lt hnot
        have hval : (σ.perm.symm i).val = d - 1 := by omega
        apply hlast
        ext
        dsimp [lastCoordIndex]
        exact hval
      have hs := shiftLeftIndex_apply_of_lt (d := d)
        (j := σ.perm.symm i) hlt_index
      rw [hs] at h
      simpa using h
  · intro h
    rcases h with hlast | hlt
    · rw [hlast, shiftLeftIndex_apply_last hd]
      dsimp [firstCoordIndex]
      exact hl0
    · have hs := shiftLeftIndex_apply_of_lt (d := d)
        (j := σ.perm.symm i) (by omega)
      rw [hs]
      simpa using hlt

/--
Endpoint neighbour across the facet omitting vertex `0`, when the raised base
still satisfies the current admissibility condition.
-/
noncomputable def upperNeighbor? {d N : ℕ}
    (σ : FreudenthalSimplex d N) : Option (FreudenthalSimplex d N) := by
  classical
  by_cases hd : 0 < d
  · let first : Fin d := firstCoordIndex d hd
    by_cases h : (∑ i, σ.base.1 i) + d < N
    · have hsumlt : (∑ i, σ.base.1 i) < N := by omega
      exact some
        { base := GridPoint.raiseOfSumLt σ.base (σ.perm first) hsumlt
          perm := σ.upperShiftPerm
          admissible := by
            dsimp [GridPoint.raiseOfSumLt]
            rw [GridPoint.sum_update_add_one]
            omega }
    · exact none
  · exact none

/--
Endpoint neighbour across the facet omitting the last vertex, when the base can
be lowered in the final permutation direction.
-/
noncomputable def lowerNeighbor? {d N : ℕ}
    (σ : FreudenthalSimplex d N) : Option (FreudenthalSimplex d N) := by
  classical
  by_cases hd : 0 < d
  · let last : Fin d := lastCoordIndex d hd
    by_cases hpos : 0 < σ.base.1 (σ.perm last)
    · exact some
        { base := GridPoint.lowerOfPositive σ.base (σ.perm last) hpos
          perm := σ.lowerShiftPerm
          admissible := by
            dsimp [GridPoint.lowerOfPositive]
            have hsum := GridPoint.sum_update_sub_one σ.base.1 (σ.perm last) hpos
            have hadm := σ.admissible
            omega }
    · exact none
  · exact none

/-- The left position involved in the adjacent swap for a middle facet. -/
def middleLeftIndex {d N : ℕ} (σ : FreudenthalSimplex d N)
    (k : Fin (d + 1)) (hk0 : 0 < k.val) (hkd : k.val < d) : Fin d :=
  ⟨k.val - 1, by omega⟩

/-- The right position involved in the adjacent swap for a middle facet. -/
def middleRightIndex {d N : ℕ} (σ : FreudenthalSimplex d N)
    (k : Fin (d + 1)) (_hk0 : 0 < k.val) (hkd : k.val < d) : Fin d :=
  ⟨k.val, hkd⟩

@[simp] theorem middleLeftIndex_val {d N : ℕ} (σ : FreudenthalSimplex d N)
    (k : Fin (d + 1)) (hk0 : 0 < k.val) (hkd : k.val < d) :
    (σ.middleLeftIndex k hk0 hkd).val = k.val - 1 :=
  rfl

@[simp] theorem middleRightIndex_val {d N : ℕ} (σ : FreudenthalSimplex d N)
    (k : Fin (d + 1)) (hk0 : 0 < k.val) (hkd : k.val < d) :
    (σ.middleRightIndex k hk0 hkd).val = k.val :=
  rfl

/-- Swap the two adjacent order positions around a middle omitted vertex. -/
noncomputable def swapMiddlePerm {d N : ℕ} (σ : FreudenthalSimplex d N)
    (k : Fin (d + 1)) (hk0 : 0 < k.val) (hkd : k.val < d) :
    Equiv.Perm (Fin d) :=
  (Equiv.swap (σ.middleLeftIndex k hk0 hkd)
      (σ.middleRightIndex k hk0 hkd)).trans σ.perm

/-- The Freudenthal neighbour across a middle facet. -/
noncomputable def middleNeighbor {d N : ℕ} (σ : FreudenthalSimplex d N)
    (k : Fin (d + 1)) (hk0 : 0 < k.val) (hkd : k.val < d) :
    FreudenthalSimplex d N where
  base := σ.base
  perm := σ.swapMiddlePerm k hk0 hkd
  admissible := σ.admissible

theorem swapMiddle_lt_iff_of_ne {d N : ℕ} (σ : FreudenthalSimplex d N)
    (k l : Fin (d + 1)) (hk0 : 0 < k.val) (hkd : k.val < d)
    (hl : l ≠ k) (p : Fin d) :
    ((Equiv.swap (σ.middleLeftIndex k hk0 hkd)
        (σ.middleRightIndex k hk0 hkd) p).val < l.val
      ↔ p.val < l.val) := by
  classical
  have hlval : l.val ≠ k.val := by
    intro h
    exact hl (Fin.ext h)
  let a := σ.middleLeftIndex k hk0 hkd
  let b := σ.middleRightIndex k hk0 hkd
  by_cases hpa : p = a
  · subst p
    have hswap : Equiv.swap a b a = b := Equiv.swap_apply_left a b
    rw [hswap]
    dsimp [a, b]
    constructor <;> intro h <;> omega
  · by_cases hpb : p = b
    · subst p
      have hswap : Equiv.swap a b b = a := Equiv.swap_apply_right a b
      rw [hswap]
      dsimp [a, b]
      constructor <;> intro h <;> omega
    · have hswap : Equiv.swap a b p = p :=
        Equiv.swap_apply_of_ne_of_ne hpa hpb
      rw [hswap]

theorem middleNeighbor_prefixRaisedCoords_eq_of_ne {d N : ℕ}
    (σ : FreudenthalSimplex d N)
    (k l : Fin (d + 1)) (hk0 : 0 < k.val) (hkd : k.val < d)
    (hl : l ≠ k) :
    (σ.middleNeighbor k hk0 hkd).prefixRaisedCoords l =
      σ.prefixRaisedCoords l := by
  classical
  ext i
  simp [prefixRaisedCoords, middleNeighbor, swapMiddlePerm,
    swapMiddle_lt_iff_of_ne σ k l hk0 hkd hl (σ.perm.symm i)]

theorem middleNeighbor_vertex_eq_of_ne {d N : ℕ}
    (σ : FreudenthalSimplex d N)
    (k l : Fin (d + 1)) (hk0 : 0 < k.val) (hkd : k.val < d)
    (hl : l ≠ k) :
    (σ.middleNeighbor k hk0 hkd).vertex l = σ.vertex l := by
  have hp :=
    middleNeighbor_prefixRaisedCoords_eq_of_ne σ k l hk0 hkd hl
  ext i
  rw [vertex_apply, vertex_apply, hp]
  simp [middleNeighbor]

theorem middleNeighbor_facet_vertices_eq {d N : ℕ}
    (σ : FreudenthalSimplex d N)
    (k : Fin (d + 1)) (hk0 : 0 < k.val) (hkd : k.val < d) :
    (FreudenthalFacet.mk σ k).vertices =
    (FreudenthalFacet.mk
      (σ.middleNeighbor k hk0 hkd) k).vertices := by
  classical
  unfold FreudenthalFacet.vertices
  apply Finset.image_congr
  intro l hl
  have hl_ne : l ≠ k := by
    simpa using hl
  exact (middleNeighbor_vertex_eq_of_ne σ k l hk0 hkd hl_ne).symm

theorem upperNeighbor_vertex_eq {d N : ℕ} (σ τ : FreudenthalSimplex d N)
    (hτ : σ.upperNeighbor? = some τ)
    (l : Fin (d + 1)) (hl : l.val < d) :
    τ.vertex l = σ.vertex ⟨l.val + 1, Nat.succ_lt_succ hl⟩ := by
  classical
  have hdata : ∃ (hd : 0 < d) (h : (∑ i, σ.base.1 i) + d < N),
      τ = { base := GridPoint.raiseOfSumLt σ.base (σ.perm (firstCoordIndex d hd)) (by omega),
            perm := σ.upperShiftPerm,
            admissible := by
              dsimp [GridPoint.raiseOfSumLt]
              rw [GridPoint.sum_update_add_one]
              omega } := by
    unfold FreudenthalSimplex.upperNeighbor? at hτ
    split at hτ
    next hd =>
      dsimp at hτ
      split at hτ
      next h =>
        refine ⟨hd, h, ?_⟩
        injection hτ with ht
        exact ht.symm
      next _h => cases hτ
    next _hd => cases hτ
  rcases hdata with ⟨hd, _h, hτeq⟩
  subst τ
  let first : Fin d := firstCoordIndex d hd
  let τc : FreudenthalSimplex d N :=
    { base := GridPoint.raiseOfSumLt σ.base (σ.perm first) (by omega),
      perm := σ.upperShiftPerm,
      admissible := by
        dsimp [GridPoint.raiseOfSumLt]
        rw [GridPoint.sum_update_add_one]
        omega }
  ext i
  change (τc.vertex l).1 i = (σ.vertex ⟨l.val + 1, Nat.succ_lt_succ hl⟩).1 i
  have hmem_new : i ∈ τc.prefixRaisedCoords l
        ↔ 0 < (σ.perm.symm i).val ∧ (σ.perm.symm i).val < l.val + 1 := by
    dsimp [τc]
    simpa [prefixRaisedCoords, first] using upperShift_prefix_mem_iff σ l hl i
  by_cases hq0 : (σ.perm.symm i).val = 0
  · have hifirst : i = σ.perm first := by
      calc
        i = σ.perm (σ.perm.symm i) := by simp
        _ = σ.perm first := by
          congr
          ext
          dsimp [first, firstCoordIndex]
          exact hq0
    have hnew_not : ¬ i ∈ τc.prefixRaisedCoords l := by
      rw [hmem_new]
      omega
    have hold_first :
        σ.perm first ∈ σ.prefixRaisedCoords ⟨l.val + 1, Nat.succ_lt_succ hl⟩ := by
      rw [σ.mem_prefixRaisedCoords_perm_iff]
      dsimp [first, firstCoordIndex]
      omega
    have hold_i : i ∈ σ.prefixRaisedCoords ⟨l.val + 1, Nat.succ_lt_succ hl⟩ := by
      simpa [hifirst] using hold_first
    have hbase : τc.base.1 i = σ.base.1 i + 1 := by
      simp [τc, GridPoint.raiseOfSumLt, Function.update, hifirst, first]
    rw [vertex_apply, vertex_apply, hbase]
    simp [hnew_not, hold_i]
  · have hpos : 0 < (σ.perm.symm i).val := Nat.pos_of_ne_zero hq0
    have hine : i ≠ σ.perm first := by
      intro hi
      have hs : σ.perm.symm i = first := by
        simpa [hi]
      have hv : (σ.perm.symm i).val = 0 := by
        simpa [first, firstCoordIndex] using congrArg Fin.val hs
      omega
    by_cases hq_lt : (σ.perm.symm i).val < l.val + 1
    · have hnew : i ∈ τc.prefixRaisedCoords l := by
        rw [hmem_new]
        exact ⟨hpos, hq_lt⟩
      have hold : i ∈ σ.prefixRaisedCoords ⟨l.val + 1, Nat.succ_lt_succ hl⟩ := by
        rw [prefixRaisedCoords]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hq_lt
      have hbase : τc.base.1 i = σ.base.1 i := by
        simp [τc, GridPoint.raiseOfSumLt, Function.update, hine]
      rw [vertex_apply, vertex_apply, hbase]
      simp [hnew, hold]
    · have hnew : ¬ i ∈ τc.prefixRaisedCoords l := by
        rw [hmem_new]
        intro hh
        exact hq_lt hh.2
      have hold : ¬ i ∈ σ.prefixRaisedCoords ⟨l.val + 1, Nat.succ_lt_succ hl⟩ := by
        rw [prefixRaisedCoords]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hq_lt
      have hbase : τc.base.1 i = σ.base.1 i := by
        simp [τc, GridPoint.raiseOfSumLt, Function.update, hine]
      rw [vertex_apply, vertex_apply, hbase]
      simp [hnew, hold]

theorem upperNeighbor_facet_vertices_eq {d N : ℕ} (σ τ : FreudenthalSimplex d N)
    (hτ : σ.upperNeighbor? = some τ) :
    (FreudenthalFacet.mk σ 0).vertices =
    (FreudenthalFacet.mk τ ⟨d, by omega⟩).vertices := by
  classical
  unfold FreudenthalFacet.vertices
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨k, hk, hkv⟩
    have hk_ne_zero : k ≠ 0 := by simpa using hk
    have hk_pos : 0 < k.val := by
      by_contra hz
      have hk0 : k = 0 := by
        apply Fin.ext
        exact Nat.eq_zero_of_not_pos hz
      exact hk_ne_zero hk0
    let l : Fin (d + 1) := ⟨k.val - 1, by omega⟩
    have hl : l.val < d := by
      dsimp [l]
      omega
    have hk_eq : k = ⟨l.val + 1, Nat.succ_lt_succ hl⟩ := by
      apply Fin.ext
      dsimp [l]
      omega
    refine Finset.mem_image.mpr ?_
    refine ⟨l, ?_, ?_⟩
    · simp
      intro hlast
      have : l.val = d := congrArg Fin.val hlast
      omega
    · rw [← hkv]
      rw [hk_eq]
      exact upperNeighbor_vertex_eq σ τ hτ l hl
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨l, hlmem, hlv⟩
    have hl_ne_last : l ≠ ⟨d, by omega⟩ := by simpa using hlmem
    have hl : l.val < d := by
      by_contra hnot
      have hle : l.val ≤ d := Nat.le_of_lt_succ l.isLt
      have hval : l.val = d := le_antisymm hle (Nat.le_of_not_lt hnot)
      exact hl_ne_last (Fin.ext hval)
    let k : Fin (d + 1) := ⟨l.val + 1, Nat.succ_lt_succ hl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨k, ?_, ?_⟩
    · simp [k]
    · rw [← hlv]
      exact (upperNeighbor_vertex_eq σ τ hτ l hl).symm

theorem lowerNeighbor_vertex_eq {d N : ℕ} (σ τ : FreudenthalSimplex d N)
    (hτ : σ.lowerNeighbor? = some τ)
    (l : Fin (d + 1)) (hl0 : 0 < l.val) :
    τ.vertex l = σ.vertex ⟨l.val - 1, by omega⟩ := by
  classical
  have hdata : ∃ (hd : 0 < d)
      (hpos : 0 < σ.base.1 (σ.perm (lastCoordIndex d hd))),
      τ = { base := GridPoint.lowerOfPositive σ.base (σ.perm (lastCoordIndex d hd)) hpos,
            perm := σ.lowerShiftPerm,
            admissible := by
              dsimp [GridPoint.lowerOfPositive]
              have hsum :=
                GridPoint.sum_update_sub_one σ.base.1
                  (σ.perm (lastCoordIndex d hd)) hpos
              have hadm := σ.admissible
              omega } := by
    unfold FreudenthalSimplex.lowerNeighbor? at hτ
    split at hτ
    next hd =>
      dsimp at hτ
      split at hτ
      next hpos =>
        refine ⟨hd, hpos, ?_⟩
        injection hτ with ht
        exact ht.symm
      next _h => cases hτ
    next _hd => cases hτ
  rcases hdata with ⟨hd, hpos_last, hτeq⟩
  subst τ
  let last : Fin d := lastCoordIndex d hd
  let τc : FreudenthalSimplex d N :=
    { base := GridPoint.lowerOfPositive σ.base (σ.perm last) hpos_last,
      perm := σ.lowerShiftPerm,
      admissible := by
        dsimp [GridPoint.lowerOfPositive]
        have hsum := GridPoint.sum_update_sub_one σ.base.1 (σ.perm last) hpos_last
        have hadm := σ.admissible
        omega }
  ext i
  change (τc.vertex l).1 i = (σ.vertex ⟨l.val - 1, by omega⟩).1 i
  have hmem_new : i ∈ τc.prefixRaisedCoords l
        ↔ σ.perm.symm i = last ∨ (σ.perm.symm i).val + 1 < l.val := by
    dsimp [τc]
    simpa [prefixRaisedCoords, last] using lowerShift_prefix_mem_iff σ hd l hl0 i
  by_cases hqlast : σ.perm.symm i = last
  · have hilast : i = σ.perm last := by
      calc
        i = σ.perm (σ.perm.symm i) := by simp
        _ = σ.perm last := by rw [hqlast]
    have hnew : i ∈ τc.prefixRaisedCoords l := by
      rw [hmem_new]
      exact Or.inl hqlast
    have hold_not : ¬ i ∈ σ.prefixRaisedCoords ⟨l.val - 1, by omega⟩ := by
      rw [prefixRaisedCoords]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hqval : (σ.perm.symm i).val = d - 1 := by
        rw [hqlast]
        rfl
      omega
    have hbase : τc.base.1 i = σ.base.1 i - 1 := by
      simp [τc, GridPoint.lowerOfPositive, Function.update, hilast, last]
    have hpos_i : 0 < σ.base.1 i := by
      simpa [hilast] using hpos_last
    rw [vertex_apply, vertex_apply, hbase]
    simp [hnew, hold_not]
    omega
  · have hine : i ≠ σ.perm last := by
      intro hi
      have hs : σ.perm.symm i = last := by
        simpa [hi]
      exact hqlast hs
    by_cases hq_lt : (σ.perm.symm i).val + 1 < l.val
    · have hnew : i ∈ τc.prefixRaisedCoords l := by
        rw [hmem_new]
        exact Or.inr hq_lt
      have hold : i ∈ σ.prefixRaisedCoords ⟨l.val - 1, by omega⟩ := by
        rw [prefixRaisedCoords]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      have hbase : τc.base.1 i = σ.base.1 i := by
        simp [τc, GridPoint.lowerOfPositive, Function.update, hine]
      rw [vertex_apply, vertex_apply, hbase]
      simp [hnew, hold]
    · have hnew : ¬ i ∈ τc.prefixRaisedCoords l := by
        rw [hmem_new]
        intro hh
        rcases hh with hh | hh
        · exact hqlast hh
        · exact hq_lt hh
      have hold : ¬ i ∈ σ.prefixRaisedCoords ⟨l.val - 1, by omega⟩ := by
        rw [prefixRaisedCoords]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      have hbase : τc.base.1 i = σ.base.1 i := by
        simp [τc, GridPoint.lowerOfPositive, Function.update, hine]
      rw [vertex_apply, vertex_apply, hbase]
      simp [hnew, hold]

theorem lowerNeighbor_facet_vertices_eq {d N : ℕ} (σ τ : FreudenthalSimplex d N)
    (hτ : σ.lowerNeighbor? = some τ) :
    (FreudenthalFacet.mk σ ⟨d, by omega⟩).vertices =
    (FreudenthalFacet.mk τ 0).vertices := by
  classical
  unfold FreudenthalFacet.vertices
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨k, hk, hkv⟩
    have hk_ne_last : k ≠ ⟨d, by omega⟩ := by simpa using hk
    have hk_lt : k.val < d := by
      by_contra hnot
      have hle : k.val ≤ d := Nat.le_of_lt_succ k.isLt
      have hval : k.val = d := le_antisymm hle (Nat.le_of_not_lt hnot)
      exact hk_ne_last (Fin.ext hval)
    let l : Fin (d + 1) := ⟨k.val + 1, Nat.succ_lt_succ hk_lt⟩
    have hl0 : 0 < l.val := by
      dsimp [l]
      omega
    have hk_eq : k = ⟨l.val - 1, by omega⟩ := by
      apply Fin.ext
      dsimp [l]
    refine Finset.mem_image.mpr ?_
    refine ⟨l, ?_, ?_⟩
    · simp [l]
    · rw [← hkv]
      rw [hk_eq]
      exact lowerNeighbor_vertex_eq σ τ hτ l hl0
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨l, hlmem, hlv⟩
    have hl_ne_zero : l ≠ 0 := by simpa using hlmem
    have hl0 : 0 < l.val := by
      by_contra hnot
      have hval : l.val = 0 := Nat.eq_zero_of_not_pos hnot
      exact hl_ne_zero (Fin.ext hval)
    let k : Fin (d + 1) := ⟨l.val - 1, by omega⟩
    have hk_ne_last : k ≠ ⟨d, by omega⟩ := by
      intro hk
      have hval : k.val = d := congrArg Fin.val hk
      dsimp [k] at hval
      omega
    refine Finset.mem_image.mpr ?_
    refine ⟨k, ?_, ?_⟩
    · simp [hk_ne_last]
    · rw [← hlv]
      exact (lowerNeighbor_vertex_eq σ τ hτ l hl0).symm

end FreudenthalSimplex

namespace FreudenthalFacet

def isFirstFacet {d N : ℕ} (F : FreudenthalFacet d N) : Prop :=
  F.omitted.val = 0

def isLastFacet {d N : ℕ} (F : FreudenthalFacet d N) : Prop :=
  F.omitted.val = d

def isMiddleFacet {d N : ℕ} (F : FreudenthalFacet d N) : Prop :=
  0 < F.omitted.val ∧ F.omitted.val < d

def boundary {d N : ℕ} (F : FreudenthalFacet d N) : Prop :=
  (F.isFirstFacet ∧ F.simplex.upperNeighbor? = none) ∨
  (F.isLastFacet ∧ F.simplex.lowerNeighbor? = none)

theorem middle_contains_base {d N : ℕ} (F : FreudenthalFacet d N)
    (hmid : F.isMiddleFacet) :
    F.simplex.base ∈ F.vertices := by
  rw [mem_vertices_iff]
  refine ⟨0, ?_, ?_⟩
  · intro h0
    have : F.omitted.val = 0 := congrArg Fin.val h0.symm
    exact (Nat.ne_of_gt hmid.1) this
  · exact F.simplex.vertex_zero

theorem middle_contains_top {d N : ℕ} (F : FreudenthalFacet d N)
    (hmid : F.isMiddleFacet) :
    F.simplex.topVertex ∈ F.vertices := by
  rw [mem_vertices_iff]
  refine ⟨⟨d, by omega⟩, ?_, rfl⟩
  intro hlast
  have : F.omitted.val = d := congrArg Fin.val hlast.symm
  exact (Nat.ne_of_lt hmid.2) this

theorem first_not_contains_base {d N : ℕ} (F : FreudenthalFacet d N)
    (hfirst : F.isFirstFacet) :
    F.simplex.base ∉ F.vertices := by
  intro hmem
  rcases (mem_vertices_iff F F.simplex.base).mp hmem with ⟨j, hjne, hj⟩
  have hj0 : j = 0 := F.simplex.vertex_injective (by simpa using hj)
  have homit0 : F.omitted = 0 := by
    apply Fin.ext
    exact hfirst
  exact hjne (by rw [homit0, hj0])

theorem last_not_contains_top {d N : ℕ} (F : FreudenthalFacet d N)
    (hlast : F.isLastFacet) :
    F.simplex.topVertex ∉ F.vertices := by
  intro hmem
  rcases (mem_vertices_iff F F.simplex.topVertex).mp hmem with ⟨j, hjne, hj⟩
  have hjlast : j = ⟨d, by omega⟩ :=
    F.simplex.vertex_injective (by simpa [FreudenthalSimplex.topVertex] using hj)
  have homitlast : F.omitted = ⟨d, by omega⟩ := by
    apply Fin.ext
    exact hlast
  exact hjne (by rw [homitlast, hjlast])

theorem middle_base_unique {d N : ℕ} (F : FreudenthalFacet d N)
    (hmid : F.isMiddleFacet) (x : GridPoint d N) (hx : x ∈ F.vertices)
    (hmin : ∀ y ∈ F.vertices, ∀ i : Fin d, x.1 i ≤ y.1 i) :
    x = F.simplex.base := by
  classical
  ext i
  have hbase_mem := F.middle_contains_base hmid
  have hx_le_base := hmin F.simplex.base hbase_mem i
  have hx_simplex : x ∈ F.simplex.vertices := F.vertices_subset_simplex_vertices hx
  rcases (F.simplex.mem_vertices_iff x).mp hx_simplex with ⟨j, hj⟩
  have hbase_le_x : F.simplex.base.1 i ≤ x.1 i := by
    rw [← hj]
    exact F.simplex.base_le_vertex j i
  omega

theorem middle_top_unique {d N : ℕ} (F : FreudenthalFacet d N)
    (hmid : F.isMiddleFacet) (x : GridPoint d N) (hx : x ∈ F.vertices)
    (hmax : ∀ y ∈ F.vertices, ∀ i : Fin d, y.1 i ≤ x.1 i) :
    x = F.simplex.topVertex := by
  classical
  ext i
  have htop_mem := F.middle_contains_top hmid
  have htop_le_x := hmax F.simplex.topVertex htop_mem i
  have hx_simplex : x ∈ F.simplex.vertices := F.vertices_subset_simplex_vertices hx
  rcases (F.simplex.mem_vertices_iff x).mp hx_simplex with ⟨j, hj⟩
  have hx_le_top : x.1 i ≤ F.simplex.topVertex.1 i := by
    rw [← hj]
    exact F.simplex.vertex_le_top j i
  omega

theorem middle_shared_geomEq_base_eq_of_middle {d N : ℕ}
    (F G : FreudenthalFacet d N)
    (hmidF : F.isMiddleFacet) (hmidG : G.isMiddleFacet)
    (hgeom : G.GeomEq F) :
    G.simplex.base = F.simplex.base := by
  classical
  have hverts : G.vertices = F.vertices := hgeom
  apply F.middle_base_unique hmidF
  · rw [← hverts]
    exact G.middle_contains_base hmidG
  · intro y hy i
    have hyG : y ∈ G.vertices := by
      simpa [hverts] using hy
    have hyGs : y ∈ G.simplex.vertices := G.vertices_subset_simplex_vertices hyG
    rcases (G.simplex.mem_vertices_iff y).mp hyGs with ⟨j, hj⟩
    rw [← hj]
    exact G.simplex.base_le_vertex j i

theorem firstFacet_fixed_coord {d N : ℕ} (F : FreudenthalFacet d N)
    (hd : 0 < d) (hfirst : F.isFirstFacet) :
    ∃ i : Fin d, ∃ n : ℕ, ∀ x ∈ F.vertices, x.1 i = n := by
  classical
  let p : Fin d := F.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd)
  refine ⟨p, F.simplex.base.1 p + 1, ?_⟩
  intro x hx
  rcases (F.mem_vertices_iff x).mp hx with ⟨j, hjne, hjx⟩
  have hjpos : 0 < j.val := by
    by_contra hnot
    have hjzero : j.val = 0 := Nat.eq_zero_of_not_pos hnot
    have hj_eq_omit : j = F.omitted := by
      apply Fin.ext
      rw [hjzero, hfirst]
    exact hjne hj_eq_omit
  have hp : p ∈ F.simplex.prefixRaisedCoords j := by
    simpa [p] using
      (FreudenthalSimplex.first_perm_mem_prefix_of_pos F.simplex hd hjpos)
  rw [← hjx, FreudenthalSimplex.vertex_apply]
  simp [hp]

theorem lastFacet_fixed_coord {d N : ℕ} (F : FreudenthalFacet d N)
    (hd : 0 < d) (hlast : F.isLastFacet) :
    ∃ i : Fin d, ∃ n : ℕ, ∀ x ∈ F.vertices, x.1 i = n := by
  classical
  let p : Fin d := F.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd)
  refine ⟨p, F.simplex.base.1 p, ?_⟩
  intro x hx
  rcases (F.mem_vertices_iff x).mp hx with ⟨j, hjne, hjx⟩
  have hjlt : j.val < d := by
    by_contra hnot
    have hle : j.val ≤ d := Nat.le_of_lt_succ j.isLt
    have hjval : j.val = d := le_antisymm hle (Nat.le_of_not_lt hnot)
    have hj_eq_omit : j = F.omitted := by
      apply Fin.ext
      rw [hjval, hlast]
    exact hjne hj_eq_omit
  have hpnot : p ∉ F.simplex.prefixRaisedCoords j := by
    simpa [p] using
      (FreudenthalSimplex.last_perm_not_mem_prefix_of_lt_last F.simplex hd hjlt)
  rw [← hjx, FreudenthalSimplex.vertex_apply]
  simp [hpnot]

theorem firstFacet_fixed_coord_eq_perm_first {d N : ℕ} (F : FreudenthalFacet d N)
    (hd : 0 < d) (hfirst : F.isFirstFacet)
    {i : Fin d} {n : ℕ}
    (hfixed : ∀ x ∈ F.vertices, x.1 i = n) :
    i = F.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) := by
  classical
  let q : Fin d := F.simplex.perm.symm i
  have hiq : i = F.simplex.perm q := by
    simp [q]
  by_cases hq0 : q.val = 0
  · rw [hiq]
    congr
    apply Fin.ext
    exact hq0
  · have hqpos : 0 < q.val := Nat.pos_of_ne_zero hq0
    let j0 : Fin (d + 1) := ⟨q.val, by omega⟩
    let j1 : Fin (d + 1) := ⟨q.val + 1, Nat.succ_lt_succ q.isLt⟩
    have hj0_ne : j0 ≠ F.omitted := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [j0] at hv
      rw [hfirst] at hv
      omega
    have hj1_ne : j1 ≠ F.omitted := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [j1] at hv
      rw [hfirst] at hv
      omega
    have hj0_mem : F.simplex.vertex j0 ∈ F.vertices :=
      (F.mem_vertices_iff (F.simplex.vertex j0)).mpr ⟨j0, hj0_ne, rfl⟩
    have hj1_mem : F.simplex.vertex j1 ∈ F.vertices :=
      (F.mem_vertices_iff (F.simplex.vertex j1)).mpr ⟨j1, hj1_ne, rfl⟩
    have h0 := hfixed (F.simplex.vertex j0) hj0_mem
    have h1 := hfixed (F.simplex.vertex j1) hj1_mem
    have hnot : i ∉ F.simplex.prefixRaisedCoords j0 := by
      rw [hiq, F.simplex.mem_prefixRaisedCoords_perm_iff]
      dsimp [j0]
      exact Nat.lt_irrefl q.val
    have hin : i ∈ F.simplex.prefixRaisedCoords j1 := by
      rw [hiq, F.simplex.mem_prefixRaisedCoords_perm_iff]
      dsimp [j1]
      exact Nat.lt_succ_self q.val
    rw [FreudenthalSimplex.vertex_apply] at h0 h1
    simp [hnot] at h0
    simp [hin] at h1
    omega

theorem lastFacet_fixed_coord_eq_perm_last {d N : ℕ} (F : FreudenthalFacet d N)
    (hd : 0 < d) (hlast : F.isLastFacet)
    {i : Fin d} {n : ℕ}
    (hfixed : ∀ x ∈ F.vertices, x.1 i = n) :
    i = F.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd) := by
  classical
  let q : Fin d := F.simplex.perm.symm i
  have hiq : i = F.simplex.perm q := by
    simp [q]
  by_cases hqlast : q = FreudenthalSimplex.lastCoordIndex d hd
  · rw [hiq, hqlast]
  · have hq_lt_last : q.val < d - 1 := by
      by_contra hnot
      have hle : q.val ≤ d - 1 := by
        omega
      have hqval : q.val = d - 1 := le_antisymm hle (Nat.le_of_not_lt hnot)
      apply hqlast
      apply Fin.ext
      simpa [FreudenthalSimplex.lastCoordIndex] using hqval
    let j0 : Fin (d + 1) := ⟨q.val, by omega⟩
    let j1 : Fin (d + 1) := ⟨q.val + 1, by omega⟩
    have hj0_ne : j0 ≠ F.omitted := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [j0] at hv
      rw [hlast] at hv
      omega
    have hj1_ne : j1 ≠ F.omitted := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [j1] at hv
      rw [hlast] at hv
      omega
    have hj0_mem : F.simplex.vertex j0 ∈ F.vertices :=
      (F.mem_vertices_iff (F.simplex.vertex j0)).mpr ⟨j0, hj0_ne, rfl⟩
    have hj1_mem : F.simplex.vertex j1 ∈ F.vertices :=
      (F.mem_vertices_iff (F.simplex.vertex j1)).mpr ⟨j1, hj1_ne, rfl⟩
    have h0 := hfixed (F.simplex.vertex j0) hj0_mem
    have h1 := hfixed (F.simplex.vertex j1) hj1_mem
    have hnot : i ∉ F.simplex.prefixRaisedCoords j0 := by
      rw [hiq, F.simplex.mem_prefixRaisedCoords_perm_iff]
      dsimp [j0]
      exact Nat.lt_irrefl q.val
    have hin : i ∈ F.simplex.prefixRaisedCoords j1 := by
      rw [hiq, F.simplex.mem_prefixRaisedCoords_perm_iff]
      dsimp [j1]
      exact Nat.lt_succ_self q.val
    rw [FreudenthalSimplex.vertex_apply] at h0 h1
    simp [hnot] at h0
    simp [hin] at h1
    omega

theorem firstFacet_fixed_coord_unique {d N : ℕ} (F : FreudenthalFacet d N)
    (hfirst : F.isFirstFacet)
    {i j : Fin d} {ni nj : ℕ}
    (hi : ∀ x ∈ F.vertices, x.1 i = ni)
    (hj : ∀ x ∈ F.vertices, x.1 j = nj) :
    i = j := by
  classical
  by_cases hd : 0 < d
  · rw [F.firstFacet_fixed_coord_eq_perm_first hd hfirst hi,
      F.firstFacet_fixed_coord_eq_perm_first hd hfirst hj]
  · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    exact Fin.elim0 i

theorem lastFacet_fixed_coord_unique {d N : ℕ} (F : FreudenthalFacet d N)
    (hlast : F.isLastFacet)
    {i j : Fin d} {ni nj : ℕ}
    (hi : ∀ x ∈ F.vertices, x.1 i = ni)
    (hj : ∀ x ∈ F.vertices, x.1 j = nj) :
    i = j := by
  classical
  by_cases hd : 0 < d
  · rw [F.lastFacet_fixed_coord_eq_perm_last hd hlast hi,
      F.lastFacet_fixed_coord_eq_perm_last hd hlast hj]
  · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    exact Fin.elim0 i

theorem firstFacet_min_unique {d N : ℕ} (F : FreudenthalFacet d N)
    (hd : 0 < d) (hfirst : F.isFirstFacet)
    (x : GridPoint d N) (hx : x ∈ F.vertices)
    (hmin : ∀ y ∈ F.vertices, ∀ i : Fin d, x.1 i ≤ y.1 i) :
    x = F.simplex.vertex ⟨1, by omega⟩ := by
  classical
  rcases (F.mem_vertices_iff x).mp hx with ⟨j, hjne, hjx⟩
  ext i
  let one : Fin (d + 1) := ⟨1, by omega⟩
  have hone_ne : one ≠ F.omitted := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [one] at hv
    rw [hfirst] at hv
    omega
  have hone_mem : F.simplex.vertex one ∈ F.vertices :=
    (F.mem_vertices_iff (F.simplex.vertex one)).mpr ⟨one, hone_ne, rfl⟩
  have hx_le_one := hmin (F.simplex.vertex one) hone_mem i
  have hjpos : 0 < j.val := by
    by_contra hnot
    have hjzero : j.val = 0 := Nat.eq_zero_of_not_pos hnot
    apply hjne
    apply Fin.ext
    rw [hfirst]
    exact hjzero
  have hone_le_x : (F.simplex.vertex one).1 i ≤ x.1 i := by
    rw [← hjx]
    exact F.simplex.vertex_one_le_of_pos_index hd hjpos i
  exact le_antisymm hx_le_one hone_le_x

theorem lastFacet_min_unique {d N : ℕ} (F : FreudenthalFacet d N)
    (hd : 0 < d) (hlast : F.isLastFacet)
    (x : GridPoint d N) (hx : x ∈ F.vertices)
    (hmin : ∀ y ∈ F.vertices, ∀ i : Fin d, x.1 i ≤ y.1 i) :
    x = F.simplex.base := by
  classical
  rcases (F.mem_vertices_iff x).mp hx with ⟨j, _hjne, hjx⟩
  ext i
  have hzero_ne : (0 : Fin (d + 1)) ≠ F.omitted := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    rw [hlast] at hv
    omega
  have hbase_mem : F.simplex.base ∈ F.vertices :=
    (F.mem_vertices_iff F.simplex.base).mpr ⟨0, hzero_ne, F.simplex.vertex_zero⟩
  have hx_le_base := hmin F.simplex.base hbase_mem i
  have hbase_le_x : F.simplex.base.1 i ≤ x.1 i := by
    rw [← hjx]
    exact F.simplex.base_le_vertex j i
  omega

theorem middleFacet_no_fixed_coord {d N : ℕ} (F : FreudenthalFacet d N)
    (hmid : F.isMiddleFacet) :
    ¬ ∃ i : Fin d, ∃ n : ℕ, ∀ x ∈ F.vertices, x.1 i = n := by
  classical
  intro h
  rcases h with ⟨i, n, hfixed⟩
  have hbase : F.simplex.base.1 i = n :=
    hfixed F.simplex.base (F.middle_contains_base hmid)
  have htop : F.simplex.topVertex.1 i = n :=
    hfixed F.simplex.topVertex (F.middle_contains_top hmid)
  have htop_apply := F.simplex.topVertex_apply i
  omega

theorem not_first_of_geomEq_middle {d N : ℕ} (F G : FreudenthalFacet d N)
    (hmidF : F.isMiddleFacet) (hgeom : G.GeomEq F) :
    ¬ G.isFirstFacet := by
  classical
  intro hfirstG
  have hd : 0 < d := Nat.lt_trans hmidF.1 hmidF.2
  rcases G.firstFacet_fixed_coord hd hfirstG with ⟨i, n, hfixedG⟩
  have hverts : G.vertices = F.vertices := hgeom
  have hfixedF : ∀ x ∈ F.vertices, x.1 i = n := by
    intro x hx
    have hxG : x ∈ G.vertices := by
      simpa [hverts] using hx
    exact hfixedG x hxG
  exact F.middleFacet_no_fixed_coord hmidF ⟨i, n, hfixedF⟩

theorem not_last_of_geomEq_middle {d N : ℕ} (F G : FreudenthalFacet d N)
    (hmidF : F.isMiddleFacet) (hgeom : G.GeomEq F) :
    ¬ G.isLastFacet := by
  classical
  intro hlastG
  have hd : 0 < d := Nat.lt_trans hmidF.1 hmidF.2
  rcases G.lastFacet_fixed_coord hd hlastG with ⟨i, n, hfixedG⟩
  have hverts : G.vertices = F.vertices := hgeom
  have hfixedF : ∀ x ∈ F.vertices, x.1 i = n := by
    intro x hx
    have hxG : x ∈ G.vertices := by
      simpa [hverts] using hx
    exact hfixedG x hxG
  exact F.middleFacet_no_fixed_coord hmidF ⟨i, n, hfixedF⟩

theorem geomEq_middle_implies_middle {d N : ℕ} (F G : FreudenthalFacet d N)
    (hmidF : F.isMiddleFacet) (hgeom : G.GeomEq F) :
    G.isMiddleFacet := by
  constructor
  · by_contra hnot
    have hzero : G.omitted.val = 0 := Nat.eq_zero_of_not_pos hnot
    exact (not_first_of_geomEq_middle F G hmidF hgeom) hzero
  · by_contra hnot
    have hle : G.omitted.val ≤ d := Nat.le_of_lt_succ G.omitted.isLt
    have hlast : G.omitted.val = d := le_antisymm hle (Nat.le_of_not_lt hnot)
    exact (not_last_of_geomEq_middle F G hmidF hgeom) hlast

theorem middle_shared_geomEq_base_eq {d N : ℕ} (F G : FreudenthalFacet d N)
    (hmidF : F.isMiddleFacet) (hgeom : G.GeomEq F) :
    G.simplex.base = F.simplex.base := by
  have hmidG : G.isMiddleFacet := F.geomEq_middle_implies_middle G hmidF hgeom
  exact FreudenthalFacet.middle_shared_geomEq_base_eq_of_middle F G hmidF hmidG hgeom

theorem rank_mem_facet_vertices_iff {d N : ℕ} (F : FreudenthalFacet d N)
    (r : Fin (d + 1)) :
    (∃ x ∈ F.vertices, F.simplex.vertexRankRelative x = r.val) ↔
      r ≠ F.omitted := by
  classical
  constructor
  · intro h
    rcases h with ⟨x, hx, hr⟩
    rcases (F.mem_vertices_iff x).mp hx with ⟨j, hjne, hjx⟩
    rw [← hjx, FreudenthalSimplex.vertexRankRelative_vertex] at hr
    intro hro
    have hjr : j = r := Fin.ext hr
    exact hjne (hjr.trans hro)
  · intro hr
    refine ⟨F.simplex.vertex r, ?_, ?_⟩
    · exact (F.mem_vertices_iff (F.simplex.vertex r)).mpr ⟨r, hr, rfl⟩
    · rw [FreudenthalSimplex.vertexRankRelative_vertex]

theorem omitted_eq_of_same_base_geomEq_middle {d N : ℕ}
    (F G : FreudenthalFacet d N)
    (_hmidF : F.isMiddleFacet) (_hmidG : G.isMiddleFacet)
    (hbase : G.simplex.base = F.simplex.base)
    (hgeom : G.GeomEq F) :
    G.omitted = F.omitted := by
  classical
  by_contra hne
  have hverts : G.vertices = F.vertices := hgeom
  have hGF : G.omitted ≠ F.omitted := hne
  rcases (F.rank_mem_facet_vertices_iff G.omitted).mpr hGF with ⟨x, hxF, hrF⟩
  have hxG : x ∈ G.vertices := by
    simpa [hverts] using hxF
  have hrG : G.simplex.vertexRankRelative x = G.omitted.val := by
    rw [FreudenthalSimplex.vertexRankRelative_eq_of_base_eq hbase x]
    exact hrF
  have hnot := (G.rank_mem_facet_vertices_iff G.omitted).mp ⟨x, hxG, hrG⟩
  exact hnot rfl

theorem vertex_eq_of_same_base_geomEq_rank_ne_omitted {d N : ℕ}
    (F G : FreudenthalFacet d N)
    (hbase : G.simplex.base = F.simplex.base)
    (homit : G.omitted = F.omitted)
    (hgeom : G.GeomEq F)
    (r : Fin (d + 1)) (hr : r ≠ F.omitted) :
    G.simplex.vertex r = F.simplex.vertex r := by
  classical
  have hrG : r ≠ G.omitted := by
    intro h
    exact hr (h.trans homit)
  have hxG : G.simplex.vertex r ∈ G.vertices :=
    (G.mem_vertices_iff (G.simplex.vertex r)).mpr ⟨r, hrG, rfl⟩
  have hverts : G.vertices = F.vertices := hgeom
  have hxF : G.simplex.vertex r ∈ F.vertices := by
    simpa [hverts] using hxG
  rcases (F.mem_vertices_iff (G.simplex.vertex r)).mp hxF with ⟨j, _hjne, hjx⟩
  have hrankF : F.simplex.vertexRankRelative (G.simplex.vertex r) = r.val := by
    rw [← FreudenthalSimplex.vertexRankRelative_eq_of_base_eq hbase
      (G.simplex.vertex r)]
    exact G.simplex.vertexRankRelative_vertex r
  rw [← hjx, FreudenthalSimplex.vertexRankRelative_vertex] at hrankF
  have hjr : j = r := Fin.ext hrankF
  rw [← hjx, hjr]

theorem prefixRaisedCoords_eq_of_same_base_geomEq_rank_ne_omitted {d N : ℕ}
    (F G : FreudenthalFacet d N)
    (hbase : G.simplex.base = F.simplex.base)
    (homit : G.omitted = F.omitted)
    (hgeom : G.GeomEq F)
    (r : Fin (d + 1)) (hr : r ≠ F.omitted) :
    G.simplex.prefixRaisedCoords r = F.simplex.prefixRaisedCoords r := by
  exact FreudenthalSimplex.prefixRaisedCoords_eq_of_same_base_vertex_eq hbase
    (F.vertex_eq_of_same_base_geomEq_rank_ne_omitted G hbase homit hgeom r hr)

theorem perm_eq_away_from_middle_pair {d N : ℕ}
    (F G : FreudenthalFacet d N)
    (_hmidF : F.isMiddleFacet) (_hmidG : G.isMiddleFacet)
    (hbase : G.simplex.base = F.simplex.base)
    (homit : G.omitted = F.omitted)
    (hgeom : G.GeomEq F)
    (r : Fin d)
    (hr_left : r.val + 1 ≠ F.omitted.val)
    (hr_right : r.val ≠ F.omitted.val) :
    G.simplex.perm r = F.simplex.perm r := by
  classical
  let r0 : Fin (d + 1) := ⟨r.val, by omega⟩
  let r1 : Fin (d + 1) := ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩
  have hr0 : r0 ≠ F.omitted := by
    intro h
    exact hr_right (by simpa [r0] using congrArg Fin.val h)
  have hr1 : r1 ≠ F.omitted := by
    intro h
    exact hr_left (by simpa [r1] using congrArg Fin.val h)
  have hpre :
      G.simplex.prefixRaisedCoords ⟨r.val, by omega⟩ =
        F.simplex.prefixRaisedCoords ⟨r.val, by omega⟩ := by
    simpa [r0] using
      F.prefixRaisedCoords_eq_of_same_base_geomEq_rank_ne_omitted
        G hbase homit hgeom r0 hr0
  have hsucc :
      G.simplex.prefixRaisedCoords ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ =
        F.simplex.prefixRaisedCoords ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ := by
    simpa [r1] using
      F.prefixRaisedCoords_eq_of_same_base_geomEq_rank_ne_omitted
        G hbase homit hgeom r1 hr1
  exact FreudenthalSimplex.perm_eq_of_prefix_consecutive_eq
    F.simplex G.simplex r hpre hsucc

theorem middle_pair_eq_or_swap {d N : ℕ}
    (F G : FreudenthalFacet d N)
    (hmidF : F.isMiddleFacet) (hmidG : G.isMiddleFacet)
    (hbase : G.simplex.base = F.simplex.base)
    (homit : G.omitted = F.omitted)
    (hgeom : G.GeomEq F) :
    (G.simplex.perm = F.simplex.perm) ∨
    (G.simplex.perm =
      F.simplex.swapMiddlePerm F.omitted hmidF.1 hmidF.2) := by
  classical
  let a : Fin d := F.simplex.middleLeftIndex F.omitted hmidF.1 hmidF.2
  let b : Fin d := F.simplex.middleRightIndex F.omitted hmidF.1 hmidF.2
  have hab : a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    have ha_val : a.val = F.omitted.val - 1 := by
      simp [a, FreudenthalSimplex.middleLeftIndex]
    have hb_val : b.val = F.omitted.val := by
      simp [b, FreudenthalSimplex.middleRightIndex]
    have hlt : a.val < b.val := by
      rw [ha_val, hb_val]
      exact Nat.pred_lt (Nat.ne_of_gt hmidF.1)
    exact (Nat.ne_of_lt hlt) hv
  have haway : ∀ r : Fin d, r ≠ a → r ≠ b →
      G.simplex.perm r = F.simplex.perm r := by
    intro r hra hrb
    exact F.perm_eq_away_from_middle_pair G hmidF hmidG hbase homit hgeom r
      (by
        intro h
        apply hra
        apply Fin.ext
        dsimp [a]
        omega)
      (by
        intro h
        apply hrb
        apply Fin.ext
        dsimp [b]
        omega)
  have hpair_image : ∀ t : Fin d, t = a ∨ t = b →
      G.simplex.perm t = F.simplex.perm a ∨
        G.simplex.perm t = F.simplex.perm b := by
    intro t ht
    let s : Fin d := F.simplex.perm.symm (G.simplex.perm t)
    have hs : F.simplex.perm s = G.simplex.perm t := by
      simp [s]
    by_cases hsa : s = a
    · left
      rw [← hs, hsa]
    · by_cases hsb : s = b
      · right
        rw [← hs, hsb]
      · have hsaway := haway s hsa hsb
        have hGt : G.simplex.perm s = G.simplex.perm t := by
          rw [hsaway, hs]
        have hst : s = t := G.simplex.perm.injective hGt
        rcases ht with ht | ht
        · exact False.elim (hsa (hst.trans ht))
        · exact False.elim (hsb (hst.trans ht))
  have ha_image := hpair_image a (Or.inl rfl)
  rcases ha_image with ha_same | ha_swap
  · have hb_same : G.simplex.perm b = F.simplex.perm b := by
      rcases hpair_image b (Or.inr rfl) with hb_a | hb_b
      · have hGbGa : G.simplex.perm b = G.simplex.perm a := by
          rw [hb_a, ha_same]
        exact False.elim (hab ((G.simplex.perm.injective hGbGa).symm))
      · exact hb_b
    left
    apply Equiv.ext
    intro r
    by_cases hra : r = a
    · subst hra
      exact ha_same
    · by_cases hrb : r = b
      · subst hrb
        exact hb_same
      · exact haway r hra hrb
  · have hb_swap : G.simplex.perm b = F.simplex.perm a := by
      rcases hpair_image b (Or.inr rfl) with hb_a | hb_b
      · exact hb_a
      · have hGbGa : G.simplex.perm b = G.simplex.perm a := by
          rw [hb_b, ha_swap]
        exact False.elim (hab ((G.simplex.perm.injective hGbGa).symm))
    right
    apply Equiv.ext
    intro r
    by_cases hra : r = a
    · subst hra
      rw [ha_swap]
      simp [FreudenthalSimplex.swapMiddlePerm, a, b]
    · by_cases hrb : r = b
      · subst hrb
        rw [hb_swap]
        simp [FreudenthalSimplex.swapMiddlePerm, a, b]
      · have hswap : Equiv.swap a b r = r :=
          Equiv.swap_apply_of_ne_of_ne hra hrb
        rw [haway r hra hrb]
        simp [FreudenthalSimplex.swapMiddlePerm, a, b, hswap]

instance instDecidableIsFirstFacet {d N : ℕ} (F : FreudenthalFacet d N) :
    Decidable F.isFirstFacet := by
  unfold isFirstFacet
  infer_instance

instance instDecidableIsLastFacet {d N : ℕ} (F : FreudenthalFacet d N) :
    Decidable F.isLastFacet := by
  unfold isLastFacet
  infer_instance

instance instDecidableIsMiddleFacet {d N : ℕ} (F : FreudenthalFacet d N) :
    Decidable F.isMiddleFacet := by
  unfold isMiddleFacet
  infer_instance

/--
The at-most-two candidate set associated to a syntactic facet: the owning
simplex and, when it exists, the explicit middle/upper/lower neighbour.
-/
noncomputable def possibleIncidentSimplices {d N : ℕ} (F : FreudenthalFacet d N) :
    Finset (FreudenthalSimplex d N) :=
  if hmid : F.isMiddleFacet then
    {F.simplex, F.simplex.middleNeighbor F.omitted hmid.1 hmid.2}
  else if _hfirst : F.isFirstFacet then
    match F.simplex.upperNeighbor? with
    | some υ => {F.simplex, υ}
    | none => {F.simplex}
  else if _hlast : F.isLastFacet then
    match F.simplex.lowerNeighbor? with
    | some υ => {F.simplex, υ}
    | none => {F.simplex}
  else
    {F.simplex}

theorem card_pair_le_two {α : Type*} [DecidableEq α] (a b : α) :
    ({a, b} : Finset α).card ≤ 2 := by
  by_cases h : a = b
  · subst h
    simp
  · simp [h]

theorem possibleIncidentSimplices_card_le_two {d N : ℕ} (F : FreudenthalFacet d N) :
    F.possibleIncidentSimplices.card ≤ 2 := by
  classical
  unfold possibleIncidentSimplices
  by_cases hmid : F.isMiddleFacet
  · simp [hmid, card_pair_le_two]
  · simp [hmid]
    by_cases hfirst : F.isFirstFacet
    · simp [hfirst]
      cases hU : F.simplex.upperNeighbor? with
      | none => simp
      | some υ => simpa [hU] using card_pair_le_two F.simplex υ
    · simp [hfirst]
      by_cases hlast : F.isLastFacet
      · simp [hlast]
        cases hL : F.simplex.lowerNeighbor? with
        | none => simp
        | some υ => simpa [hL] using card_pair_le_two F.simplex υ
      · simp [hlast]

end FreudenthalFacet

namespace FreudenthalSimplex

theorem perm_eq_or_swap_of_same_middle_facet {d N : ℕ}
    (σ τ : FreudenthalSimplex d N)
    (k l : Fin (d + 1))
    (hk : 0 < k.val ∧ k.val < d)
    (hl : 0 < l.val ∧ l.val < d)
    (hbase : τ.base = σ.base)
    (hgeom :
      (FreudenthalFacet.mk τ l).vertices =
      (FreudenthalFacet.mk σ k).vertices) :
    τ = σ ∨ τ = σ.middleNeighbor k hk.1 hk.2 := by
  classical
  let F : FreudenthalFacet d N := ⟨σ, k⟩
  let G : FreudenthalFacet d N := ⟨τ, l⟩
  have hmidF : F.isMiddleFacet := hk
  have hmidG : G.isMiddleFacet := hl
  have hgeom' : G.GeomEq F := hgeom
  have homit : G.omitted = F.omitted :=
    FreudenthalFacet.omitted_eq_of_same_base_geomEq_middle
      F G hmidF hmidG hbase hgeom'
  have hperm :
      τ.perm = σ.perm ∨
      τ.perm = σ.swapMiddlePerm k hk.1 hk.2 := by
    simpa [F, G] using
      FreudenthalFacet.middle_pair_eq_or_swap
        F G hmidF hmidG hbase homit hgeom'
  rcases hperm with hperm | hperm
  · left
    cases σ
    cases τ
    simp at hbase hperm ⊢
    exact ⟨hbase, hperm⟩
  · right
    cases σ
    cases τ
    simp [middleNeighbor] at hbase hperm ⊢
    exact ⟨hbase, hperm⟩

end FreudenthalSimplex

namespace FreudenthalFacet

theorem middle_incident_simplex_eq_self_or_neighbor {d N : ℕ}
    (F : FreudenthalFacet d N)
    (hmid : F.isMiddleFacet)
    (τ : FreudenthalSimplex d N)
    (hτ : ∃ k : Fin (d + 1),
      (FreudenthalFacet.mk τ k).GeomEq F) :
    τ = F.simplex ∨
      τ = F.simplex.middleNeighbor F.omitted hmid.1 hmid.2 := by
  classical
  rcases hτ with ⟨l, hgeom⟩
  have hmidG : (FreudenthalFacet.mk τ l).isMiddleFacet :=
    F.geomEq_middle_implies_middle (FreudenthalFacet.mk τ l) hmid hgeom
  have hbase : τ.base = F.simplex.base :=
    F.middle_shared_geomEq_base_eq (FreudenthalFacet.mk τ l) hmid hgeom
  exact FreudenthalSimplex.perm_eq_or_swap_of_same_middle_facet
    F.simplex τ F.omitted l hmid hmidG hbase hgeom

theorem omitted_first_or_middle_or_last {d N : ℕ} (F : FreudenthalFacet d N) :
    F.isFirstFacet ∨ F.isMiddleFacet ∨ F.isLastFacet := by
  classical
  unfold isFirstFacet isMiddleFacet isLastFacet
  by_cases hzero : F.omitted.val = 0
  · exact Or.inl hzero
  · by_cases hlt : F.omitted.val < d
    · exact Or.inr (Or.inl ⟨Nat.pos_of_ne_zero hzero, hlt⟩)
    · right
      right
      have hle : F.omitted.val ≤ d := Nat.le_of_lt_succ F.omitted.isLt
      omega

theorem not_middle_of_geomEq_first {d N : ℕ} (F G : FreudenthalFacet d N)
    (hfirstF : F.isFirstFacet) (hgeom : G.GeomEq F) :
    ¬ G.isMiddleFacet := by
  classical
  intro hmidG
  have hd : 0 < d := Nat.lt_trans hmidG.1 hmidG.2
  rcases F.firstFacet_fixed_coord hd hfirstF with ⟨i, n, hfixedF⟩
  have hverts : G.vertices = F.vertices := hgeom
  have hfixedG : ∀ x ∈ G.vertices, x.1 i = n := by
    intro x hx
    have hxF : x ∈ F.vertices := by
      simpa [hverts] using hx
    exact hfixedF x hxF
  exact G.middleFacet_no_fixed_coord hmidG ⟨i, n, hfixedG⟩

theorem not_middle_of_geomEq_last {d N : ℕ} (F G : FreudenthalFacet d N)
    (hlastF : F.isLastFacet) (hgeom : G.GeomEq F) :
    ¬ G.isMiddleFacet := by
  classical
  intro hmidG
  have hd : 0 < d := Nat.lt_trans hmidG.1 hmidG.2
  rcases F.lastFacet_fixed_coord hd hlastF with ⟨i, n, hfixedF⟩
  have hverts : G.vertices = F.vertices := hgeom
  have hfixedG : ∀ x ∈ G.vertices, x.1 i = n := by
    intro x hx
    have hxF : x ∈ F.vertices := by
      simpa [hverts] using hx
    exact hfixedF x hxF
  exact G.middleFacet_no_fixed_coord hmidG ⟨i, n, hfixedG⟩

theorem geomEq_first_implies_endpoint {d N : ℕ} (F G : FreudenthalFacet d N)
    (hfirstF : F.isFirstFacet) (hgeom : G.GeomEq F) :
    G.isFirstFacet ∨ G.isLastFacet := by
  classical
  rcases G.omitted_first_or_middle_or_last with hfirst | hmid_or_last
  · exact Or.inl hfirst
  rcases hmid_or_last with hmid | hlast
  · exact False.elim ((F.not_middle_of_geomEq_first G hfirstF hgeom) hmid)
  · exact Or.inr hlast

theorem geomEq_last_implies_endpoint {d N : ℕ} (F G : FreudenthalFacet d N)
    (hlastF : F.isLastFacet) (hgeom : G.GeomEq F) :
    G.isFirstFacet ∨ G.isLastFacet := by
  classical
  rcases G.omitted_first_or_middle_or_last with hfirst | hmid_or_last
  · exact Or.inl hfirst
  rcases hmid_or_last with hmid | hlast
  · exact False.elim ((F.not_middle_of_geomEq_last G hlastF hgeom) hmid)
  · exact Or.inr hlast

theorem first_last_geomEq_shift_coord_of_pos {d N : ℕ} (F G : FreudenthalFacet d N)
    (hd : 0 < d) (hfirstF : F.isFirstFacet) (hlastG : G.isLastFacet)
    (hgeom : G.GeomEq F) :
    F.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) =
      G.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd) := by
  classical
  rcases F.firstFacet_fixed_coord hd hfirstF with ⟨iF, nF, hfixedF⟩
  rcases G.lastFacet_fixed_coord hd hlastG with ⟨iG, nG, hfixedG⟩
  have hiF :
      iF = F.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) :=
    F.firstFacet_fixed_coord_eq_perm_first hd hfirstF hfixedF
  have hiG :
      iG = G.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd) :=
    G.lastFacet_fixed_coord_eq_perm_last hd hlastG hfixedG
  have hverts : G.vertices = F.vertices := hgeom
  have hfixedG_on_F : ∀ x ∈ F.vertices, x.1 iG = nG := by
    intro x hx
    have hxG : x ∈ G.vertices := by
      simpa [hverts] using hx
    exact hfixedG x hxG
  have hcoord : iF = iG :=
    F.firstFacet_fixed_coord_unique hfirstF hfixedF hfixedG_on_F
  rw [← hiF, ← hiG]
  exact hcoord

theorem last_first_geomEq_shift_coord_of_pos {d N : ℕ} (F G : FreudenthalFacet d N)
    (hd : 0 < d) (hlastF : F.isLastFacet) (hfirstG : G.isFirstFacet)
    (hgeom : G.GeomEq F) :
    F.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd) =
      G.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) := by
  classical
  rcases F.lastFacet_fixed_coord hd hlastF with ⟨iF, nF, hfixedF⟩
  rcases G.firstFacet_fixed_coord hd hfirstG with ⟨iG, nG, hfixedG⟩
  have hiF :
      iF = F.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd) :=
    F.lastFacet_fixed_coord_eq_perm_last hd hlastF hfixedF
  have hiG :
      iG = G.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) :=
    G.firstFacet_fixed_coord_eq_perm_first hd hfirstG hfixedG
  have hverts : G.vertices = F.vertices := hgeom
  have hfixedG_on_F : ∀ x ∈ F.vertices, x.1 iG = nG := by
    intro x hx
    have hxG : x ∈ G.vertices := by
      simpa [hverts] using hx
    exact hfixedG x hxG
  have hcoord : iF = iG :=
    F.lastFacet_fixed_coord_unique hlastF hfixedF hfixedG_on_F
  rw [← hiF, ← hiG]
  exact hcoord

theorem first_last_geomEq_base_eq_vertex_one {d N : ℕ} (F G : FreudenthalFacet d N)
    (hd : 0 < d) (hfirstF : F.isFirstFacet) (hlastG : G.isLastFacet)
    (hgeom : G.GeomEq F) :
    G.simplex.base = F.simplex.vertex ⟨1, by omega⟩ := by
  classical
  apply F.firstFacet_min_unique hd hfirstF
  · have hzero_ne : (0 : Fin (d + 1)) ≠ G.omitted := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      rw [hlastG] at hv
      omega
    have hbaseG : G.simplex.base ∈ G.vertices :=
      (G.mem_vertices_iff G.simplex.base).mpr ⟨0, hzero_ne, G.simplex.vertex_zero⟩
    have hverts : G.vertices = F.vertices := hgeom
    simpa [hverts] using hbaseG
  · intro y hy i
    have hverts : G.vertices = F.vertices := hgeom
    have hyG : y ∈ G.vertices := by
      simpa [hverts] using hy
    rcases (G.mem_vertices_iff y).mp hyG with ⟨j, _hj, rfl⟩
    exact G.simplex.base_le_vertex j i

theorem last_first_geomEq_base_eq_vertex_one {d N : ℕ} (F G : FreudenthalFacet d N)
    (hd : 0 < d) (hlastF : F.isLastFacet) (hfirstG : G.isFirstFacet)
    (hgeom : G.GeomEq F) :
    F.simplex.base = G.simplex.vertex ⟨1, by omega⟩ := by
  classical
  apply G.firstFacet_min_unique hd hfirstG
  · have hzero_ne : (0 : Fin (d + 1)) ≠ F.omitted := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      rw [hlastF] at hv
      omega
    have hbaseF : F.simplex.base ∈ F.vertices :=
      (F.mem_vertices_iff F.simplex.base).mpr ⟨0, hzero_ne, F.simplex.vertex_zero⟩
    have hverts : G.vertices = F.vertices := hgeom
    simpa [hverts] using hbaseF
  · intro y hy i
    have hverts : G.vertices = F.vertices := hgeom
    have hyF : y ∈ F.vertices := by
      simpa [hverts] using hy
    rcases (F.mem_vertices_iff y).mp hyF with ⟨j, _hj, rfl⟩
    exact F.simplex.base_le_vertex j i

theorem first_last_geomEq_base_eq_raise_of_pos {d N : ℕ} (F G : FreudenthalFacet d N)
    (hd : 0 < d) (hfirstF : F.isFirstFacet) (hlastG : G.isLastFacet)
    (hgeom : G.GeomEq F) :
    ∃ hsumlt : (∑ i, F.simplex.base.1 i) < N,
      G.simplex.base =
        GridPoint.raiseOfSumLt F.simplex.base
          (F.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd)) hsumlt := by
  classical
  have hbase_vertex :=
    F.first_last_geomEq_base_eq_vertex_one G hd hfirstF hlastG hgeom
  have hadm :
      (∑ i : Fin d, (F.simplex.vertex ⟨1, by omega⟩).1 i) + d ≤ N := by
    simpa [hbase_vertex] using G.simplex.admissible
  rw [F.simplex.vertex_one_sum hd] at hadm
  have hsumlt : (∑ i, F.simplex.base.1 i) < N := by
    omega
  refine ⟨hsumlt, ?_⟩
  rw [hbase_vertex]
  exact F.simplex.vertex_one_eq_raiseOfSumLt hd hsumlt

theorem first_last_rank_relative {d N : ℕ} (F G : FreudenthalFacet d N)
    (hd : 0 < d) (hfirstF : F.isFirstFacet) (hlastG : G.isLastFacet)
    (hgeom : G.GeomEq F)
    (r : Fin (d + 1)) (hr : r.val < d) :
    G.simplex.vertexRankRelative
      (F.simplex.vertex ⟨r.val + 1, Nat.succ_lt_succ hr⟩) = r.val := by
  classical
  have hbase := F.first_last_geomEq_base_eq_vertex_one G hd hfirstF hlastG hgeom
  unfold FreudenthalSimplex.vertexRankRelative
  rw [hbase]
  exact F.simplex.vertexRankRelative_vertex_succ_from_vertex_one r hr

theorem first_last_vertex_correspondence {d N : ℕ} (F G : FreudenthalFacet d N)
    (hd : 0 < d) (hfirstF : F.isFirstFacet) (hlastG : G.isLastFacet)
    (hgeom : G.GeomEq F)
    (r : Fin (d + 1)) (hr : r.val < d) :
    G.simplex.vertex r =
      F.simplex.vertex ⟨r.val + 1, Nat.succ_lt_succ hr⟩ := by
  classical
  let k : Fin (d + 1) := ⟨r.val + 1, Nat.succ_lt_succ hr⟩
  have hk_ne : k ≠ F.omitted := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [k] at hv
    rw [hfirstF] at hv
    omega
  have hxF : F.simplex.vertex k ∈ F.vertices :=
    (F.mem_vertices_iff (F.simplex.vertex k)).mpr ⟨k, hk_ne, rfl⟩
  have hverts : G.vertices = F.vertices := hgeom
  have hxG : F.simplex.vertex k ∈ G.vertices := by
    simpa [hverts] using hxF
  rcases (G.mem_vertices_iff (F.simplex.vertex k)).mp hxG with ⟨s, hsne, hsx⟩
  have hslt : s.val < d := by
    by_contra hnot
    have hle : s.val ≤ d := Nat.le_of_lt_succ s.isLt
    have hsval : s.val = d := le_antisymm hle (Nat.le_of_not_lt hnot)
    apply hsne
    apply Fin.ext
    rw [hlastG]
    exact hsval
  have hrank :
      G.simplex.vertexRankRelative (F.simplex.vertex k) = r.val := by
    simpa [k] using F.first_last_rank_relative G hd hfirstF hlastG hgeom r hr
  rw [← hsx, G.simplex.vertexRankRelative_vertex] at hrank
  have hsr : s = r := Fin.ext hrank
  rw [← hsx, hsr]

theorem first_last_geomEq_perm_eq_upperShift {d N : ℕ} (F G : FreudenthalFacet d N)
    (hd : 0 < d) (hfirstF : F.isFirstFacet) (hlastG : G.isLastFacet)
    (hgeom : G.GeomEq F) :
    G.simplex.perm = F.simplex.upperShiftPerm := by
  classical
  ext r
  by_cases hlast : r = FreudenthalSimplex.lastCoordIndex d hd
  · subst r
    have hshift := F.first_last_geomEq_shift_coord_of_pos G hd hfirstF hlastG hgeom
    have hrot :
        FreudenthalSimplex.shiftLeftIndex d (FreudenthalSimplex.lastCoordIndex d hd) =
          FreudenthalSimplex.firstCoordIndex d hd :=
      FreudenthalSimplex.shiftLeftIndex_apply_last hd
    simp [FreudenthalSimplex.upperShiftPerm, hrot, hshift.symm]
  · have hlt : r.val + 1 < d := by
      by_contra hnot
      have hval : r.val = d - 1 := by omega
      apply hlast
      apply Fin.ext
      simpa [FreudenthalSimplex.lastCoordIndex] using hval
    let s : Fin d := ⟨r.val + 1, hlt⟩
    let r0 : Fin (d + 1) := ⟨r.val, by omega⟩
    let r1 : Fin (d + 1) := ⟨r.val + 1, by omega⟩
    have hv0 :
        G.simplex.vertex ⟨r.val, by omega⟩ =
          F.simplex.vertex ⟨s.val, by omega⟩ := by
      simpa [s, r0] using
        F.first_last_vertex_correspondence G hd hfirstF hlastG hgeom r0 (by
          dsimp [r0]
          exact r.isLt)
    have hv1 :
        G.simplex.vertex ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ =
          F.simplex.vertex ⟨s.val + 1, Nat.succ_lt_succ s.isLt⟩ := by
      simpa [s, r1] using
        F.first_last_vertex_correspondence G hd hfirstF hlastG hgeom r1 hlt
    have hperm :
        G.simplex.perm r = F.simplex.perm s :=
      FreudenthalSimplex.perm_eq_of_consecutive_vertex_eq
        F.simplex G.simplex r s hv0 hv1
    have hrot :
        FreudenthalSimplex.shiftLeftIndex d r = s := by
      exact FreudenthalSimplex.shiftLeftIndex_apply_of_lt hlt
    rw [hperm]
    simp [FreudenthalSimplex.upperShiftPerm, hrot]

theorem first_last_geomEq_upper_branch {d N : ℕ} (F G : FreudenthalFacet d N)
    (hd : 0 < d) (hfirstF : F.isFirstFacet) (hlastG : G.isLastFacet)
    (hgeom : G.GeomEq F) :
    (∑ i, F.simplex.base.1 i) + d < N := by
  classical
  have hbase_vertex :=
    F.first_last_geomEq_base_eq_vertex_one G hd hfirstF hlastG hgeom
  have hadm :
      (∑ i : Fin d, (F.simplex.vertex ⟨1, by omega⟩).1 i) + d ≤ N := by
    simpa [hbase_vertex] using G.simplex.admissible
  rw [F.simplex.vertex_one_sum hd] at hadm
  omega

theorem first_last_geomEq_upperNeighbor {d N : ℕ} (F G : FreudenthalFacet d N)
    (hd : 0 < d) (hfirstF : F.isFirstFacet) (hlastG : G.isLastFacet)
    (hgeom : G.GeomEq F) :
    ∃ υ : FreudenthalSimplex d N,
      F.simplex.upperNeighbor? = some υ ∧ G.simplex = υ := by
  classical
  have hbranch := F.first_last_geomEq_upper_branch G hd hfirstF hlastG hgeom
  rcases F.first_last_geomEq_base_eq_raise_of_pos G hd hfirstF hlastG hgeom
    with ⟨hsumlt, hbase⟩
  have hperm :
      G.simplex.perm = F.simplex.upperShiftPerm :=
    F.first_last_geomEq_perm_eq_upperShift G hd hfirstF hlastG hgeom
  refine ⟨G.simplex, ?_, rfl⟩
  unfold FreudenthalSimplex.upperNeighbor?
  split
  · next hd' =>
      dsimp
      split
      · next h =>
          apply congrArg some
          cases hGsimplex : G.simplex with
          | mk gbase gperm gadm =>
              simp [hGsimplex] at hbase hperm
              have hidx :
                  F.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd') =
                    F.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) := by
                exact congrArg F.simplex.perm (Fin.ext rfl)
              change gbase =
                  GridPoint.raiseOfSumLt F.simplex.base
                    (F.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd)) hsumlt at hbase
              change gperm = F.simplex.upperShiftPerm at hperm
              have hbase' :
                  GridPoint.raiseOfSumLt F.simplex.base
                    (F.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd')) (by omega) =
                    gbase := by
                rw [hbase]
              have hperm' : F.simplex.upperShiftPerm = gperm := hperm.symm
              subst gperm
              cases hbase'
              simp
      · next h =>
          exact False.elim (h hbranch)
  · next h =>
      exact False.elim (h hd)

theorem last_first_geomEq_base_eq_lower_of_pos {d N : ℕ} (F G : FreudenthalFacet d N)
    (hd : 0 < d) (hlastF : F.isLastFacet) (hfirstG : G.isFirstFacet)
    (hgeom : G.GeomEq F) :
    ∃ hpos : 0 < F.simplex.base.1
        (F.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd)),
      G.simplex.base =
        GridPoint.lowerOfPositive F.simplex.base
          (F.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd)) hpos := by
  classical
  let p : Fin d := F.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd)
  have hp :
      p = G.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) := by
    dsimp [p]
    exact F.last_first_geomEq_shift_coord_of_pos G hd hlastF hfirstG hgeom
  have hbase_vertex :=
    F.last_first_geomEq_base_eq_vertex_one G hd hlastF hfirstG hgeom
  have hpcoord := congrArg (fun x : GridPoint d N => x.1 p) hbase_vertex
  have hpcoord' : F.simplex.base.1 p = G.simplex.base.1 p + 1 := by
    change F.simplex.base.1 p = (G.simplex.vertex ⟨1, by omega⟩).1 p at hpcoord
    rw [G.simplex.vertex_one_apply hd p] at hpcoord
    simpa [hp] using hpcoord
  have hpos : 0 < F.simplex.base.1 p := by
    omega
  refine ⟨hpos, ?_⟩
  ext q
  have hcoord := congrArg (fun x : GridPoint d N => x.1 q) hbase_vertex
  change F.simplex.base.1 q = (G.simplex.vertex ⟨1, by omega⟩).1 q at hcoord
  rw [G.simplex.vertex_one_apply hd q] at hcoord
  by_cases hq : q = p
  · subst q
    rw [GridPoint.lowerOfPositive_apply_same]
    change G.simplex.base.1 p = F.simplex.base.1 p - 1
    omega
  · have hqG : q ≠ G.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) := by
      intro h
      apply hq
      rw [hp, h]
    have hcoord' : F.simplex.base.1 q = G.simplex.base.1 q := by
      simpa [hqG] using hcoord
    rw [GridPoint.lowerOfPositive_apply_ne F.simplex.base hpos hq]
    exact hcoord'.symm

theorem last_first_vertex_correspondence {d N : ℕ} (F G : FreudenthalFacet d N)
    (hd : 0 < d) (hlastF : F.isLastFacet) (hfirstG : G.isFirstFacet)
    (hgeom : G.GeomEq F)
    (r : Fin (d + 1)) (hr0 : 0 < r.val) :
    G.simplex.vertex r =
      F.simplex.vertex ⟨r.val - 1, by omega⟩ := by
  classical
  let r0 : Fin (d + 1) := ⟨r.val - 1, by omega⟩
  have hr0lt : r0.val < d := by
    dsimp [r0]
    omega
  have hcorr :=
    G.first_last_vertex_correspondence F hd hfirstG hlastF hgeom.symm r0 hr0lt
  have hidx : (⟨r0.val + 1, Nat.succ_lt_succ hr0lt⟩ : Fin (d + 1)) = r := by
    apply Fin.ext
    dsimp [r0]
    omega
  simpa [r0, hidx] using hcorr.symm

theorem last_first_geomEq_perm_eq_lowerShift {d N : ℕ} (F G : FreudenthalFacet d N)
    (hd : 0 < d) (hlastF : F.isLastFacet) (hfirstG : G.isFirstFacet)
    (hgeom : G.GeomEq F) :
    G.simplex.perm = F.simplex.lowerShiftPerm := by
  classical
  have hupper :
      F.simplex.perm = G.simplex.upperShiftPerm :=
    G.first_last_geomEq_perm_eq_upperShift F hd hfirstG hlastF hgeom.symm
  ext r
  by_cases hzero : r.val = 0
  · have hr : r = FreudenthalSimplex.firstCoordIndex d hd := by
      apply Fin.ext
      simpa [FreudenthalSimplex.firstCoordIndex] using hzero
    subst r
    have hshift := F.last_first_geomEq_shift_coord_of_pos G hd hlastF hfirstG hgeom
    have hrot :
        FreudenthalSimplex.shiftRightIndex d (FreudenthalSimplex.firstCoordIndex d hd) =
          FreudenthalSimplex.lastCoordIndex d hd :=
      FreudenthalSimplex.shiftRightIndex_apply_zero hd
    simp [FreudenthalSimplex.lowerShiftPerm, hrot, hshift.symm]
  · have hpos : 0 < r.val := Nat.pos_of_ne_zero hzero
    let s : Fin d := ⟨r.val - 1, by omega⟩
    have hs_succ : s.val + 1 < d := by
      dsimp [s]
      omega
    have hleft : FreudenthalSimplex.shiftLeftIndex d s = r := by
      have hs := FreudenthalSimplex.shiftLeftIndex_apply_of_lt (d := d) (j := s) hs_succ
      apply Fin.ext
      have hv := congrArg Fin.val hs
      dsimp [s] at hv ⊢
      omega
    have hright : FreudenthalSimplex.shiftRightIndex d r = s := by
      exact FreudenthalSimplex.shiftRightIndex_apply_of_pos hpos
    have hupper_s := congrArg (fun e : Equiv.Perm (Fin d) => e s) hupper
    simp [FreudenthalSimplex.upperShiftPerm, hleft] at hupper_s
    have hfin : G.simplex.perm r = F.simplex.lowerShiftPerm r := by
      calc
        G.simplex.perm r = F.simplex.perm s := hupper_s.symm
        _ = F.simplex.lowerShiftPerm r := by
          simp [FreudenthalSimplex.lowerShiftPerm, hright]
    exact congrArg Fin.val hfin

theorem last_first_geomEq_lowerNeighbor {d N : ℕ} (F G : FreudenthalFacet d N)
    (hd : 0 < d) (hlastF : F.isLastFacet) (hfirstG : G.isFirstFacet)
    (hgeom : G.GeomEq F) :
    ∃ υ : FreudenthalSimplex d N,
      F.simplex.lowerNeighbor? = some υ ∧ G.simplex = υ := by
  classical
  rcases F.last_first_geomEq_base_eq_lower_of_pos G hd hlastF hfirstG hgeom
    with ⟨hpos, hbase⟩
  have hperm :
      G.simplex.perm = F.simplex.lowerShiftPerm :=
    F.last_first_geomEq_perm_eq_lowerShift G hd hlastF hfirstG hgeom
  refine ⟨G.simplex, ?_, rfl⟩
  unfold FreudenthalSimplex.lowerNeighbor?
  split
  · next hd' =>
      dsimp
      split
      · next hpos' =>
          apply congrArg some
          cases hGsimplex : G.simplex with
          | mk gbase gperm gadm =>
              simp [hGsimplex] at hbase hperm
              have hidx :
                  F.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd') =
                    F.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd) := by
                exact congrArg F.simplex.perm (Fin.ext rfl)
              change gbase =
                  GridPoint.lowerOfPositive F.simplex.base
                    (F.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd)) hpos at hbase
              change gperm = F.simplex.lowerShiftPerm at hperm
              have hbase' :
                  GridPoint.lowerOfPositive F.simplex.base
                    (F.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd')) hpos' =
                    gbase := by
                rw [hbase]
              have hperm' : F.simplex.lowerShiftPerm = gperm := hperm.symm
              subst gperm
              cases hbase'
              simp
      · next hnot =>
          have hidx :
              F.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd') =
                F.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd) := by
            exact congrArg F.simplex.perm (Fin.ext rfl)
          exact False.elim (hnot (by simpa [hidx] using hpos))
  · next h =>
      exact False.elim (h hd)

theorem first_first_geomEq_base_eq {d N : ℕ} (F G : FreudenthalFacet d N)
    (hfirstF : F.isFirstFacet) (hfirstG : G.isFirstFacet)
    (hgeom : G.GeomEq F) :
    G.simplex.base = F.simplex.base := by
  classical
  by_cases hd : 0 < d
  · let one : Fin (d + 1) := ⟨1, by omega⟩
    have hG_one_mem_G : G.simplex.vertex one ∈ G.vertices := by
      have hone_ne : one ≠ G.omitted := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [one] at hv
        rw [hfirstG] at hv
        omega
      exact (G.mem_vertices_iff (G.simplex.vertex one)).mpr ⟨one, hone_ne, rfl⟩
    have hverts : G.vertices = F.vertices := hgeom
    have hG_one_mem_F : G.simplex.vertex one ∈ F.vertices := by
      simpa [hverts] using hG_one_mem_G
    have hG_one_min_F :
        ∀ y ∈ F.vertices, ∀ i : Fin d, (G.simplex.vertex one).1 i ≤ y.1 i := by
      intro y hy i
      have hyG : y ∈ G.vertices := by
        simpa [hverts] using hy
      rcases (G.mem_vertices_iff y).mp hyG with ⟨j, hjne, rfl⟩
      have hjpos : 0 < j.val := by
        by_contra hnot
        have hjzero : j.val = 0 := Nat.eq_zero_of_not_pos hnot
        apply hjne
        apply Fin.ext
        rw [hfirstG]
        exact hjzero
      exact G.simplex.vertex_one_le_of_pos_index hd hjpos i
    have hone_eq :
        G.simplex.vertex one = F.simplex.vertex one :=
      F.firstFacet_min_unique hd hfirstF
        (G.simplex.vertex one) hG_one_mem_F hG_one_min_F
    rcases F.firstFacet_fixed_coord hd hfirstF with ⟨iF, nF, hfixedF⟩
    rcases G.firstFacet_fixed_coord hd hfirstG with ⟨iG, nG, hfixedG⟩
    have hiF :
        iF = F.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) :=
      F.firstFacet_fixed_coord_eq_perm_first hd hfirstF hfixedF
    have hiG :
        iG = G.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) :=
      G.firstFacet_fixed_coord_eq_perm_first hd hfirstG hfixedG
    have hfixedG_on_F : ∀ x ∈ F.vertices, x.1 iG = nG := by
      intro x hx
      have hxG : x ∈ G.vertices := by
        simpa [hverts] using hx
      exact hfixedG x hxG
    have hp :
        F.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) =
          G.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) := by
      have hcoord : iF = iG :=
        F.firstFacet_fixed_coord_unique hfirstF hfixedF hfixedG_on_F
      rw [← hiF, ← hiG]
      exact hcoord
    ext q
    have hcoord := congrArg (fun x : GridPoint d N => x.1 q) hone_eq
    change (G.simplex.vertex one).1 q = (F.simplex.vertex one).1 q at hcoord
    rw [G.simplex.vertex_one_apply hd q, F.simplex.vertex_one_apply hd q] at hcoord
    by_cases hqF : q = F.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd)
    · have hqG : q = G.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) := by
        simpa [hp] using hqF
      have hcoord' :
          G.simplex.base.1 q + 1 = F.simplex.base.1 q + 1 := by
        simpa [hqF, hqG, hp] using hcoord
      omega
    · have hqG : q ≠ G.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) := by
        intro hqG
        exact hqF (by simpa [hp] using hqG)
      simpa [hqF, hqG] using hcoord
  · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    ext i
    exact Fin.elim0 i

theorem first_first_geomEq_perm_eq {d N : ℕ} (F G : FreudenthalFacet d N)
    (hfirstF : F.isFirstFacet) (hfirstG : G.isFirstFacet)
    (hgeom : G.GeomEq F) :
    G.simplex.perm = F.simplex.perm := by
  classical
  by_cases hd : 0 < d
  · have hbase : G.simplex.base = F.simplex.base :=
      F.first_first_geomEq_base_eq G hfirstF hfirstG hgeom
    have homit : G.omitted = F.omitted := by
      apply Fin.ext
      rw [hfirstG, hfirstF]
    rcases F.firstFacet_fixed_coord hd hfirstF with ⟨iF, nF, hfixedF⟩
    rcases G.firstFacet_fixed_coord hd hfirstG with ⟨iG, nG, hfixedG⟩
    have hiF :
        iF = F.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) :=
      F.firstFacet_fixed_coord_eq_perm_first hd hfirstF hfixedF
    have hiG :
        iG = G.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) :=
      G.firstFacet_fixed_coord_eq_perm_first hd hfirstG hfixedG
    have hverts : G.vertices = F.vertices := hgeom
    have hfixedG_on_F : ∀ x ∈ F.vertices, x.1 iG = nG := by
      intro x hx
      have hxG : x ∈ G.vertices := by
        simpa [hverts] using hx
      exact hfixedG x hxG
    have hfirst_perm :
        G.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) =
          F.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) := by
      have hcoord : iF = iG :=
        F.firstFacet_fixed_coord_unique hfirstF hfixedF hfixedG_on_F
      calc
        G.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) = iG := hiG.symm
        _ = iF := hcoord.symm
        _ = F.simplex.perm (FreudenthalSimplex.firstCoordIndex d hd) := hiF
    ext r
    by_cases hr0 : r.val = 0
    · have hr : r = FreudenthalSimplex.firstCoordIndex d hd := by
        apply Fin.ext
        simpa [FreudenthalSimplex.firstCoordIndex] using hr0
      exact congrArg Fin.val (by simpa [hr] using hfirst_perm)
    · have hpos : 0 < r.val := Nat.pos_of_ne_zero hr0
      let r0 : Fin (d + 1) := ⟨r.val, by omega⟩
      let r1 : Fin (d + 1) := ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩
      have hr0_ne : r0 ≠ F.omitted := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [r0] at hv
        rw [hfirstF] at hv
        omega
      have hr1_ne : r1 ≠ F.omitted := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [r1] at hv
        rw [hfirstF] at hv
        omega
      have hpre :
          G.simplex.prefixRaisedCoords ⟨r.val, by omega⟩ =
            F.simplex.prefixRaisedCoords ⟨r.val, by omega⟩ := by
        simpa [r0] using
          F.prefixRaisedCoords_eq_of_same_base_geomEq_rank_ne_omitted
            G hbase homit hgeom r0 hr0_ne
      have hsucc :
          G.simplex.prefixRaisedCoords ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ =
            F.simplex.prefixRaisedCoords ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ := by
        simpa [r1] using
          F.prefixRaisedCoords_eq_of_same_base_geomEq_rank_ne_omitted
            G hbase homit hgeom r1 hr1_ne
      exact congrArg Fin.val
        (FreudenthalSimplex.perm_eq_of_prefix_consecutive_eq
          F.simplex G.simplex r hpre hsucc)
  · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    ext i
    exact Fin.elim0 i

theorem first_first_geomEq_simplex_eq {d N : ℕ} (F G : FreudenthalFacet d N)
    (hfirstF : F.isFirstFacet) (hfirstG : G.isFirstFacet)
    (hgeom : G.GeomEq F) :
    G.simplex = F.simplex := by
  classical
  have hbase := F.first_first_geomEq_base_eq G hfirstF hfirstG hgeom
  have hperm := F.first_first_geomEq_perm_eq G hfirstF hfirstG hgeom
  cases hFsimplex : F.simplex with
  | mk fbase fperm fadm =>
      cases hGsimplex : G.simplex with
      | mk gbase gperm gadm =>
          simp [hFsimplex, hGsimplex] at hbase hperm ⊢
          cases hbase
          cases hperm
          simp

theorem last_last_geomEq_base_eq {d N : ℕ} (F G : FreudenthalFacet d N)
    (hlastF : F.isLastFacet) (hlastG : G.isLastFacet)
    (hgeom : G.GeomEq F) :
    G.simplex.base = F.simplex.base := by
  classical
  by_cases hd : 0 < d
  · have hzero_ne_G : (0 : Fin (d + 1)) ≠ G.omitted := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      rw [hlastG] at hv
      omega
    have hbaseG_mem_G : G.simplex.base ∈ G.vertices :=
      (G.mem_vertices_iff G.simplex.base).mpr ⟨0, hzero_ne_G, G.simplex.vertex_zero⟩
    have hverts : G.vertices = F.vertices := hgeom
    have hbaseG_mem_F : G.simplex.base ∈ F.vertices := by
      simpa [hverts] using hbaseG_mem_G
    have hbaseG_min_F :
        ∀ y ∈ F.vertices, ∀ i : Fin d, G.simplex.base.1 i ≤ y.1 i := by
      intro y hy i
      have hyG : y ∈ G.vertices := by
        simpa [hverts] using hy
      rcases (G.mem_vertices_iff y).mp hyG with ⟨j, _hjne, rfl⟩
      exact G.simplex.base_le_vertex j i
    exact F.lastFacet_min_unique hd hlastF
      G.simplex.base hbaseG_mem_F hbaseG_min_F
  · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    ext i
    exact Fin.elim0 i

theorem last_last_geomEq_perm_eq {d N : ℕ} (F G : FreudenthalFacet d N)
    (hlastF : F.isLastFacet) (hlastG : G.isLastFacet)
    (hgeom : G.GeomEq F) :
    G.simplex.perm = F.simplex.perm := by
  classical
  by_cases hd : 0 < d
  · have hbase : G.simplex.base = F.simplex.base :=
      F.last_last_geomEq_base_eq G hlastF hlastG hgeom
    have homit : G.omitted = F.omitted := by
      apply Fin.ext
      rw [hlastG, hlastF]
    rcases F.lastFacet_fixed_coord hd hlastF with ⟨iF, nF, hfixedF⟩
    rcases G.lastFacet_fixed_coord hd hlastG with ⟨iG, nG, hfixedG⟩
    have hiF :
        iF = F.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd) :=
      F.lastFacet_fixed_coord_eq_perm_last hd hlastF hfixedF
    have hiG :
        iG = G.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd) :=
      G.lastFacet_fixed_coord_eq_perm_last hd hlastG hfixedG
    have hverts : G.vertices = F.vertices := hgeom
    have hfixedG_on_F : ∀ x ∈ F.vertices, x.1 iG = nG := by
      intro x hx
      have hxG : x ∈ G.vertices := by
        simpa [hverts] using hx
      exact hfixedG x hxG
    have hlast_perm :
        G.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd) =
          F.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd) := by
      have hcoord : iF = iG :=
        F.lastFacet_fixed_coord_unique hlastF hfixedF hfixedG_on_F
      calc
        G.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd) = iG := hiG.symm
        _ = iF := hcoord.symm
        _ = F.simplex.perm (FreudenthalSimplex.lastCoordIndex d hd) := hiF
    ext r
    by_cases hlast : r = FreudenthalSimplex.lastCoordIndex d hd
    · exact congrArg Fin.val (by simpa [hlast] using hlast_perm)
    · have hlt : r.val + 1 < d := by
        by_contra hnot
        have hval : r.val = d - 1 := by omega
        apply hlast
        apply Fin.ext
        simpa [FreudenthalSimplex.lastCoordIndex] using hval
      let r0 : Fin (d + 1) := ⟨r.val, by omega⟩
      let r1 : Fin (d + 1) := ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩
      have hr0_ne : r0 ≠ F.omitted := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [r0] at hv
        rw [hlastF] at hv
        omega
      have hr1_ne : r1 ≠ F.omitted := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [r1] at hv
        rw [hlastF] at hv
        omega
      have hpre :
          G.simplex.prefixRaisedCoords ⟨r.val, by omega⟩ =
            F.simplex.prefixRaisedCoords ⟨r.val, by omega⟩ := by
        simpa [r0] using
          F.prefixRaisedCoords_eq_of_same_base_geomEq_rank_ne_omitted
            G hbase homit hgeom r0 hr0_ne
      have hsucc :
          G.simplex.prefixRaisedCoords ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ =
            F.simplex.prefixRaisedCoords ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ := by
        simpa [r1] using
          F.prefixRaisedCoords_eq_of_same_base_geomEq_rank_ne_omitted
            G hbase homit hgeom r1 hr1_ne
      exact congrArg Fin.val
        (FreudenthalSimplex.perm_eq_of_prefix_consecutive_eq
          F.simplex G.simplex r hpre hsucc)
  · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    ext i
    exact Fin.elim0 i

theorem last_last_geomEq_simplex_eq {d N : ℕ} (F G : FreudenthalFacet d N)
    (hlastF : F.isLastFacet) (hlastG : G.isLastFacet)
    (hgeom : G.GeomEq F) :
    G.simplex = F.simplex := by
  classical
  have hbase := F.last_last_geomEq_base_eq G hlastF hlastG hgeom
  have hperm := F.last_last_geomEq_perm_eq G hlastF hlastG hgeom
  cases hFsimplex : F.simplex with
  | mk fbase fperm fadm =>
      cases hGsimplex : G.simplex with
      | mk gbase gperm gadm =>
          simp [hFsimplex, hGsimplex] at hbase hperm ⊢
          cases hbase
          cases hperm
          simp

theorem upper_incident_simplex_eq_self_or_neighbor {d N : ℕ}
    (F : FreudenthalFacet d N) (hfirst : F.isFirstFacet)
    (τ : FreudenthalSimplex d N)
    (hτ : ∃ k : Fin (d + 1), (FreudenthalFacet.mk τ k).GeomEq F) :
    τ = F.simplex ∨
      ∃ υ : FreudenthalSimplex d N,
        F.simplex.upperNeighbor? = some υ ∧ τ = υ := by
  classical
  rcases hτ with ⟨k, hgeom⟩
  let G : FreudenthalFacet d N := ⟨τ, k⟩
  by_cases hzero : G.omitted.val = 0
  · have hfirstG : G.isFirstFacet := hzero
    left
    simpa [G] using F.first_first_geomEq_simplex_eq G hfirst hfirstG hgeom
  · by_cases hlt : G.omitted.val < d
    · have hmidG : G.isMiddleFacet := ⟨Nat.pos_of_ne_zero hzero, hlt⟩
      exact False.elim ((F.not_middle_of_geomEq_first G hfirst hgeom) hmidG)
    · have hlastG : G.isLastFacet := by
        dsimp [isLastFacet]
        have hle : G.omitted.val ≤ d := Nat.le_of_lt_succ G.omitted.isLt
        have hdle : d ≤ G.omitted.val := Nat.le_of_not_lt hlt
        omega
      right
      have hd : 0 < d := by omega
      rcases F.first_last_geomEq_upperNeighbor G hd hfirst hlastG hgeom with
        ⟨υ, hU, hGυ⟩
      exact ⟨υ, hU, by simpa [G] using hGυ⟩

theorem lower_incident_simplex_eq_self_or_neighbor {d N : ℕ}
    (F : FreudenthalFacet d N) (hlast : F.isLastFacet)
    (τ : FreudenthalSimplex d N)
    (hτ : ∃ k : Fin (d + 1), (FreudenthalFacet.mk τ k).GeomEq F) :
    τ = F.simplex ∨
      ∃ υ : FreudenthalSimplex d N,
        F.simplex.lowerNeighbor? = some υ ∧ τ = υ := by
  classical
  rcases hτ with ⟨k, hgeom⟩
  let G : FreudenthalFacet d N := ⟨τ, k⟩
  by_cases hzero : G.omitted.val = 0
  · have hfirstG : G.isFirstFacet := hzero
    by_cases hd : 0 < d
    · right
      rcases F.last_first_geomEq_lowerNeighbor G hd hlast hfirstG hgeom with
        ⟨υ, hL, hGυ⟩
      exact ⟨υ, hL, by simpa [G] using hGυ⟩
    · left
      have hlastG : G.isLastFacet := by
        have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
        dsimp [isLastFacet]
        omega
      simpa [G] using F.last_last_geomEq_simplex_eq G hlast hlastG hgeom
  · by_cases hlt : G.omitted.val < d
    · have hmidG : G.isMiddleFacet := ⟨Nat.pos_of_ne_zero hzero, hlt⟩
      exact False.elim ((F.not_middle_of_geomEq_last G hlast hgeom) hmidG)
    · have hlastG : G.isLastFacet := by
        dsimp [isLastFacet]
        have hle : G.omitted.val ≤ d := Nat.le_of_lt_succ G.omitted.isLt
        have hdle : d ≤ G.omitted.val := Nat.le_of_not_lt hlt
        omega
      left
      simpa [G] using F.last_last_geomEq_simplex_eq G hlast hlastG hgeom

end FreudenthalFacet

namespace FreudenthalSimplex

theorem toGeomFacet_injective {d N : ℕ} (σ : FreudenthalSimplex d N) :
    Function.Injective fun k : Fin (d + 1) =>
      (FreudenthalFacet.mk σ k).toGeomFacet := by
  classical
  intro k l h
  let Fk : FreudenthalFacet d N := ⟨σ, k⟩
  let Fl : FreudenthalFacet d N := ⟨σ, l⟩
  have hgeom : Fk.GeomEq Fl := by
    exact (FreudenthalFacet.toGeomFacet_eq_iff Fk Fl).mp h
  by_contra hne
  have hlk : k ≠ l := hne
  rcases (Fl.rank_mem_facet_vertices_iff k).mpr hlk with ⟨x, hxFl, hr⟩
  have hverts : Fk.vertices = Fl.vertices := hgeom
  have hxFk : x ∈ Fk.vertices := by
    rw [hverts]
    exact hxFl
  have hnot := (Fk.rank_mem_facet_vertices_iff k).mp ⟨x, hxFk, hr⟩
  exact hnot rfl

theorem geomFacets_card {d N : ℕ} (σ : FreudenthalSimplex d N) :
    σ.geomFacets.card = Fintype.card (Fin (d + 1)) := by
  classical
  rw [geomFacets]
  simpa using
    Finset.card_image_of_injective
      (Finset.univ : Finset (Fin (d + 1)))
      (FreudenthalSimplex.toGeomFacet_injective σ)

end FreudenthalSimplex

namespace FreudenthalGeomFacet

noncomputable instance instDecidableEq (d N : ℕ) :
    DecidableEq (FreudenthalGeomFacet d N) :=
  inferInstance

noncomputable instance instFintype (d N : ℕ) : Fintype (FreudenthalGeomFacet d N) :=
  inferInstance

end FreudenthalGeomFacet

/-- Explicit finite universe of currently represented Freudenthal simplices. -/
noncomputable def allFreudenthalSimplices (d N : ℕ) :
    Finset (FreudenthalSimplex d N) :=
  FreudenthalSimplex.all d N

/-- Explicit finite universe of geometric Freudenthal facets. -/
noncomputable def allFreudenthalFacets (d N : ℕ) :
    Finset (FreudenthalGeomFacet d N) := by
  classical
  exact (allFreudenthalSimplices d N).biUnion fun σ =>
    (Finset.univ : Finset (Fin (d + 1))).image fun k =>
      (FreudenthalFacet.mk σ k).toGeomFacet

theorem mem_allFreudenthalFacets_iff {d N : ℕ} (K : FreudenthalGeomFacet d N) :
    K ∈ allFreudenthalFacets d N ↔
      ∃ σ : FreudenthalSimplex d N, ∃ k : Fin (d + 1),
        (FreudenthalFacet.mk σ k).toGeomFacet = K := by
  classical
  simp [allFreudenthalFacets, allFreudenthalSimplices, FreudenthalSimplex.mem_all]

namespace FreudenthalGeomFacet

/-- Simplices incident to a geometric facet key. -/
noncomputable def incidentSimplices {d N : ℕ} (K : FreudenthalGeomFacet d N) :
    Finset (FreudenthalSimplex d N) := by
  classical
  exact (allFreudenthalSimplices d N).filter fun σ =>
    ∃ k : Fin (d + 1), (FreudenthalFacet.mk σ k).toGeomFacet = K

theorem mem_incidentSimplices_iff {d N : ℕ} (K : FreudenthalGeomFacet d N)
    (σ : FreudenthalSimplex d N) :
    σ ∈ K.incidentSimplices ↔
      ∃ k : Fin (d + 1), (FreudenthalFacet.mk σ k).toGeomFacet = K := by
  classical
  simp [incidentSimplices, allFreudenthalSimplices, FreudenthalSimplex.mem_all]

theorem mem_incidentSimplices_iff_geomEq_witness {d N : ℕ}
    (K : FreudenthalGeomFacet d N) (F : FreudenthalFacet d N)
    (hF : F.vertices = K.1) (τ : FreudenthalSimplex d N) :
    τ ∈ K.incidentSimplices ↔
      ∃ k : Fin (d + 1), (FreudenthalFacet.mk τ k).GeomEq F := by
  classical
  rw [mem_incidentSimplices_iff]
  constructor
  · intro h
    rcases h with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hval : (FreudenthalFacet.mk τ k).vertices = K.1 :=
      congrArg Subtype.val hk
    exact hval.trans hF.symm
  · intro h
    rcases h with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    exact hk.trans hF

end FreudenthalGeomFacet

namespace FreudenthalFacet

theorem incident_subset_possible {d N : ℕ}
    (K : FreudenthalGeomFacet d N) (F : FreudenthalFacet d N)
    (hF : F.vertices = K.1) :
    K.incidentSimplices ⊆ F.possibleIncidentSimplices := by
  classical
  intro τ hτ
  rw [FreudenthalGeomFacet.mem_incidentSimplices_iff_geomEq_witness K F hF τ] at hτ
  unfold possibleIncidentSimplices
  by_cases hmid : F.isMiddleFacet
  · have hrec := F.middle_incident_simplex_eq_self_or_neighbor hmid τ hτ
    rcases hrec with hself | hneigh
    · simp [hmid, hself]
    · simp [hmid, hneigh]
  · simp [hmid]
    by_cases hfirst : F.isFirstFacet
    · have hrec := F.upper_incident_simplex_eq_self_or_neighbor hfirst τ hτ
      cases hU : F.simplex.upperNeighbor? with
      | none =>
          rcases hrec with hself | hneigh
          · simp [hfirst, hself]
          · rcases hneigh with ⟨υ, hU', _hτ⟩
            rw [hU] at hU'
            cases hU'
      | some υ =>
          rcases hrec with hself | hneigh
          · simp [hfirst, hself]
          · rcases hneigh with ⟨υ', hU', hτeq⟩
            rw [hU] at hU'
            cases hU'
            simp [hfirst, hτeq]
    · simp [hfirst]
      by_cases hlast : F.isLastFacet
      · have hrec := F.lower_incident_simplex_eq_self_or_neighbor hlast τ hτ
        cases hL : F.simplex.lowerNeighbor? with
        | none =>
            rcases hrec with hself | hneigh
            · simp [hlast, hself]
            · rcases hneigh with ⟨υ, hL', _hτ⟩
              rw [hL] at hL'
              cases hL'
        | some υ =>
            rcases hrec with hself | hneigh
            · simp [hlast, hself]
            · rcases hneigh with ⟨υ', hL', hτeq⟩
              rw [hL] at hL'
              cases hL'
              simp [hlast, hτeq]
      · exact False.elim (by
          rcases F.omitted_first_or_middle_or_last with hfirst' | hmid_or_last
          · exact hfirst hfirst'
          · rcases hmid_or_last with hmid' | hlast'
            · exact hmid hmid'
            · exact hlast hlast')

end FreudenthalFacet

namespace FreudenthalGeomFacet

/--
For the geometric-key development, boundary currently means "has exactly one
incident simplex".  The non-circular syntactic endpoint predicate remains
`FreudenthalFacet.boundary`; connecting the two requires the
neighbour-uniqueness argument.
-/
def boundary {d N : ℕ} (K : FreudenthalGeomFacet d N) : Prop :=
  K.incidentSimplices.card = 1

theorem incidentSimplices_nonempty {d N : ℕ} (K : FreudenthalGeomFacet d N) :
    K.incidentSimplices.Nonempty := by
  classical
  rcases K.2 with ⟨F, hF⟩
  refine ⟨F.simplex, ?_⟩
  rw [mem_incidentSimplices_iff]
  refine ⟨F.omitted, ?_⟩
  apply Subtype.ext
  exact hF

theorem one_le_incident_card {d N : ℕ} (K : FreudenthalGeomFacet d N) :
    1 ≤ K.incidentSimplices.card := by
  have hpos : 0 < K.incidentSimplices.card := by
    rw [Finset.card_pos]
    exact incidentSimplices_nonempty K
  omega

theorem boundary_incident_card {d N : ℕ} (K : FreudenthalGeomFacet d N)
    (h : K.boundary) :
    K.incidentSimplices.card = 1 :=
  h

theorem incidentSimplices_card_le_two {d N : ℕ} (K : FreudenthalGeomFacet d N) :
    K.incidentSimplices.card ≤ 2 := by
  classical
  rcases K.2 with ⟨F, hF⟩
  have hsubset : K.incidentSimplices ⊆ F.possibleIncidentSimplices :=
    FreudenthalFacet.incident_subset_possible K F hF
  exact le_trans (Finset.card_le_card hsubset)
    (FreudenthalFacet.possibleIncidentSimplices_card_le_two F)

theorem incident_card_eq_one_or_two {d N : ℕ} (K : FreudenthalGeomFacet d N) :
    K.incidentSimplices.card = 1 ∨ K.incidentSimplices.card = 2 := by
  have hge : 1 ≤ K.incidentSimplices.card := K.one_le_incident_card
  have hle : K.incidentSimplices.card ≤ 2 := K.incidentSimplices_card_le_two
  omega

theorem interior_incident_card {d N : ℕ} (K : FreudenthalGeomFacet d N)
    (h : ¬ K.boundary) :
    K.incidentSimplices.card = 2 := by
  rcases K.incident_card_eq_one_or_two with h1 | h2
  · exact False.elim (h h1)
  · exact h2

theorem incident_iff_geomFacet {d N : ℕ}
    (K : FreudenthalGeomFacet d N) (σ : FreudenthalSimplex d N) :
    σ ∈ K.incidentSimplices ↔ K ∈ σ.geomFacets := by
  classical
  rw [FreudenthalGeomFacet.mem_incidentSimplices_iff]
  rw [FreudenthalSimplex.mem_geomFacets_iff]

end FreudenthalGeomFacet

namespace FreudenthalSimplex

theorem geomFacet_vertices_subset {d N : ℕ}
    {σ : FreudenthalSimplex d N} {K : FreudenthalGeomFacet d N}
    (hK : K ∈ σ.geomFacets) :
    K.1 ⊆ σ.vertices := by
  classical
  rcases (FreudenthalSimplex.mem_geomFacets_iff σ K).mp hK with ⟨k, hk⟩
  have hval := congrArg Subtype.val hk
  intro x hx
  have hxFacet : x ∈ (FreudenthalFacet.mk σ k).vertices := by
    simpa [hval.symm] using hx
  exact (FreudenthalFacet.mk σ k).vertices_subset_simplex_vertices hxFacet

end FreudenthalSimplex

noncomputable def baryFreudenthalTriangulationCertificate (d N : ℕ) :
    Sperner.SpernerTriangulationCertificate
      (GridPoint d N)
      (FreudenthalSimplex d N)
      (FreudenthalGeomFacet d N) :=
  { fintypeCell := inferInstance
    fintypeFacet := inferInstance
    decCell := inferInstance
    decFacet := inferInstance
    verticesOfCell := fun σ => σ.vertices
    verticesOfFacet := fun K => K.1
    facetsOfCell := fun σ => σ.geomFacets
    incidentCells := fun K => K.incidentSimplices
    incident_iff := by
      intro σ K
      exact FreudenthalGeomFacet.incident_iff_geomFacet K σ
    facet_vertices_subset := by
      intro σ K hK
      exact FreudenthalSimplex.geomFacet_vertices_subset hK
    boundaryFacet := fun K => K.boundary
    boundary_incident_card := by
      intro K hK
      exact hK
    interior_incident_card := by
      intro K hK
      exact FreudenthalGeomFacet.interior_incident_card K hK }

/-- A colouring of Freudenthal grid points by simplex labels. -/
structure Coloring (d N : ℕ) where
  color : GridPoint d N → Label d

namespace GridPoint

/-- The barycentric support of a grid point, including the implicit coordinate. -/
noncomputable def support {d N : ℕ} (x : GridPoint d N) :
    Finset (Label d) := by
  classical
  exact Finset.univ.filter fun k =>
    0 < Fin.cases x.zeroCoord (fun i : Fin d => x.1 i) k

end GridPoint

/-- The Sperner boundary condition for grid colourings. -/
def IsSperner {d N : ℕ} (C : Coloring d N) : Prop :=
  ∀ x : GridPoint d N, C.color x ∈ x.support

/-- A Freudenthal simplex is fully coloured when all labels occur on its vertices. -/
def IsFullyColored {d N : ℕ}
    (C : Coloring d N) (σ : FreudenthalSimplex d N) : Prop :=
  Sperner.FullyLabeled C.color σ.vertices

namespace FreudenthalSimplex

/-- The label of the `k`th vertex of a Freudenthal simplex. -/
def labelAt {d N : ℕ} (σ : FreudenthalSimplex d N)
    (C : Coloring d N) (k : Fin (d + 1)) : Label d :=
  C.color (σ.vertex k)

/--
Omitted vertex indices whose deletion facet contains every label except
`missing`.
-/
noncomputable def relevantOmittedIndices {d N : ℕ}
    (σ : FreudenthalSimplex d N) (C : Coloring d N)
    (missing : Label d) : Finset (Fin (d + 1)) := by
  classical
  exact Finset.univ.filter fun k =>
    EconLib.Sperner.AlmostFullyLabeled
      C.color missing
      (({ simplex := σ, omitted := k } : FreudenthalFacet d N).vertices)

theorem mem_relevantOmittedIndices_iff {d N : ℕ}
    (σ : FreudenthalSimplex d N) (C : Coloring d N)
    (missing : Label d) (k : Fin (d + 1)) :
    k ∈ σ.relevantOmittedIndices C missing
      ↔
    EconLib.Sperner.AlmostFullyLabeled
      C.color missing
      (({ simplex := σ, omitted := k } : FreudenthalFacet d N).vertices) := by
  classical
  simp [relevantOmittedIndices]

end FreudenthalSimplex

namespace LocalDeletionParity

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Labels with their finite fibres under a vertex-labelling map. -/
def fiber (f : α → α) (a : α) : Finset α :=
  Finset.univ.filter fun i => f i = a

theorem mem_fiber_iff (f : α → α) (a i : α) :
    i ∈ fiber f a ↔ f i = a := by
  classical
  simp [fiber]

/--
Omissions that leave every non-missing label visible among the remaining
vertices.
-/
def relevantOmissions (f : α → α) (missing : α) : Finset α :=
  Finset.univ.filter fun k : α =>
    ∀ a : α, a ≠ missing → ∃ i : α, i ≠ k ∧ f i = a

theorem mem_relevantOmissions_iff (f : α → α) (missing k : α) :
    k ∈ relevantOmissions f missing
      ↔
    ∀ a : α, a ≠ missing → ∃ i : α, i ≠ k ∧ f i = a := by
  classical
  simp [relevantOmissions]

omit [DecidableEq α] in
theorem injective_of_surjective_self
    (f : α → α) (hsurj : Function.Surjective f) :
    Function.Injective f := by
  exact (Finite.injective_iff_surjective (f := f)).2 hsurj

theorem exists_unique_preimage_of_surjective
    (f : α → α) (hsurj : Function.Surjective f) (a : α) :
    ∃! i : α, f i = a := by
  classical
  rcases hsurj a with ⟨i, hi⟩
  refine ⟨i, hi, ?_⟩
  intro j hj
  have hji : f j = f i := by simp [hi, hj]
  exact injective_of_surjective_self f hsurj hji

theorem relevantOmissions_eq_fiber_missing_of_surjective
    (f : α → α) (missing : α)
    (hsurj : Function.Surjective f) :
    relevantOmissions f missing = fiber f missing := by
  classical
  ext k
  rw [mem_relevantOmissions_iff, mem_fiber_iff]
  constructor
  · intro hk
    by_contra hk_missing
    have hinj := injective_of_surjective_self f hsurj
    rcases hk (f k) hk_missing with ⟨i, hik, hif⟩
    exact hik (hinj hif)
  · intro hk_missing
    intro a ha
    rcases exists_unique_preimage_of_surjective f hsurj a with ⟨i, hi, _huniq⟩
    refine ⟨i, ?_, hi⟩
    intro hik
    subst hik
    have : a = missing := by
      rw [← hi, hk_missing]
    exact ha this

theorem relevantOmissions_card_eq_one_of_surjective
    (f : α → α) (missing : α)
    (hsurj : Function.Surjective f) :
    (relevantOmissions f missing).card = 1 := by
  classical
  rw [relevantOmissions_eq_fiber_missing_of_surjective f missing hsurj]
  rcases exists_unique_preimage_of_surjective f hsurj missing with ⟨i, hi, huniq⟩
  have hfiber : fiber f missing = {i} := by
    ext j
    rw [mem_fiber_iff]
    constructor
    · intro hj
      exact Finset.mem_singleton.mpr (huniq j hj)
    · intro hj
      have hji : j = i := by simpa using hj
      rw [hji]
      exact hi
  simp [hfiber]

theorem mem_relevantOmissions_iff_fibers_after_delete
    (f : α → α) (missing k : α) :
    k ∈ relevantOmissions f missing
      ↔
    ∀ a : α, a ≠ missing → ∃ i ∈ fiber f a, i ≠ k := by
  classical
  rw [mem_relevantOmissions_iff]
  constructor
  · intro h a ha
    rcases h a ha with ⟨i, hik, hfi⟩
    exact ⟨i, by simpa [mem_fiber_iff] using hfi, hik⟩
  · intro h a ha
    rcases h a ha with ⟨i, hi_fiber, hik⟩
    exact ⟨i, hik, by simpa [mem_fiber_iff] using hi_fiber⟩

theorem relevantOmissions_eq_empty_of_absent_nonmissing
    (f : α → α) (missing a : α)
    (ha : a ≠ missing)
    (habsent : fiber f a = ∅) :
    relevantOmissions f missing = ∅ := by
  classical
  ext k
  constructor
  · intro hk
    rw [mem_relevantOmissions_iff_fibers_after_delete] at hk
    rcases hk a ha with ⟨i, hi, _⟩
    rw [habsent] at hi
    simpa using hi
  · intro hk_empty
    simpa using hk_empty

theorem relevantOmissions_card_eq_zero_of_absent_nonmissing
    (f : α → α) (missing a : α)
    (ha : a ≠ missing)
    (habsent : fiber f a = ∅) :
    (relevantOmissions f missing).card = 0 := by
  simp [relevantOmissions_eq_empty_of_absent_nonmissing f missing a ha habsent]

/-- Indices whose colour fibre has at least two elements. -/
def duplicatedFiberIndices (f : α → α) : Finset α :=
  Finset.univ.filter fun k => 1 < (fiber f (f k)).card

theorem relevantOmissions_eq_pair_of_only_missing_absent
    (f : α → α) (missing : α)
    (hmissing_empty : fiber f missing = ∅)
    (hnonmissing_nonempty :
      ∀ a : α, a ≠ missing → (fiber f a).Nonempty) :
    ∃ x y : α, x ≠ y ∧ relevantOmissions f missing = {x, y} := by
  classical
  let β := {a : α // a ≠ missing}
  let rep : β → α := fun b =>
    Classical.choose (hnonmissing_nonempty b.1 b.2)
  have hrep_mem : ∀ b : β, rep b ∈ fiber f b.1 := by
    intro b
    exact Classical.choose_spec (hnonmissing_nonempty b.1 b.2)
  have hrep : ∀ b : β, f (rep b) = b.1 := by
    intro b
    exact (mem_fiber_iff f b.1 (rep b)).mp (hrep_mem b)
  have hrep_inj : Function.Injective rep := by
    intro b c hbc
    apply Subtype.ext
    calc
      b.1 = f (rep b) := (hrep b).symm
      _ = f (rep c) := by rw [hbc]
      _ = c.1 := hrep c
  let R : Finset α := (Finset.univ : Finset β).image rep
  have hcardR : R.card = Fintype.card β := by
    simpa [R] using
      Finset.card_image_of_injective (Finset.univ : Finset β) hrep_inj
  have hβcard : Fintype.card β = Fintype.card α - 1 := by
    have h := Fintype.card_subtype_compl (fun x : α => x = missing)
    simpa [β, Fintype.card_subtype_eq] using h
  have hcard_compl : ((Finset.univ : Finset α) \ R).card = 1 := by
    rw [Finset.card_sdiff]
    have hpos : 0 < Fintype.card α :=
      Fintype.card_pos_iff.mpr ⟨missing⟩
    simp [hcardR, hβcard]
    omega
  rcases Finset.card_eq_one.mp hcard_compl with ⟨extra, hcomp_eq⟩
  have hextra_not_R : extra ∉ R := by
    have hextra_mem : extra ∈ ((Finset.univ : Finset α) \ R) := by
      rw [hcomp_eq]
      simp
    simpa using hextra_mem
  have hextra_ne_missing : f extra ≠ missing := by
    intro h
    have hextra_fiber : extra ∈ fiber f missing := by
      rw [mem_fiber_iff]
      exact h
    rw [hmissing_empty] at hextra_fiber
    simpa using hextra_fiber
  let b0 : β := ⟨f extra, hextra_ne_missing⟩
  let y : α := rep b0
  have hy_R : y ∈ R := by
    dsimp [R, y]
    exact Finset.mem_image.mpr ⟨b0, by simp, rfl⟩
  have hy_ne_extra : y ≠ extra := by
    intro h
    exact hextra_not_R (by simpa [h] using hy_R)
  refine ⟨extra, y, hy_ne_extra.symm, ?_⟩
  ext k
  rw [mem_relevantOmissions_iff]
  constructor
  · intro hk
    by_cases hkR : k ∈ R
    · rcases Finset.mem_image.mp hkR with ⟨b, _hb_univ, hb⟩
      have hb_eq_b0 : b = b0 := by
        by_contra hb_ne
        rcases hk b.1 b.2 with ⟨i, hik, hfi⟩
        by_cases hiR : i ∈ R
        · rcases Finset.mem_image.mp hiR with ⟨c, _hc_univ, hc⟩
          have hc_eq_b : c = b := by
            apply Subtype.ext
            calc
              c.1 = f (rep c) := (hrep c).symm
              _ = f i := by rw [hc]
              _ = b.1 := hfi
          have hi_eq_k : i = k := by
            calc
              i = rep c := hc.symm
              _ = rep b := by rw [hc_eq_b]
              _ = k := hb
          exact hik hi_eq_k
        · have hi_extra : i = extra := by
            have hi_comp : i ∈ ((Finset.univ : Finset α) \ R) := by
              simp [hiR]
            have : i ∈ ({extra} : Finset α) := by
              simpa [hcomp_eq] using hi_comp
            simpa using this
          have hb_eq : b = b0 := by
            apply Subtype.ext
            calc
              b.1 = f i := hfi.symm
              _ = f extra := by rw [hi_extra]
              _ = b0.1 := rfl
          exact hb_ne hb_eq
      have hk_y : k = y := by
        calc
          k = rep b := hb.symm
          _ = rep b0 := by rw [hb_eq_b0]
          _ = y := rfl
      simp [hk_y]
    · have hk_extra : k = extra := by
        have hk_comp : k ∈ ((Finset.univ : Finset α) \ R) := by
          simp [hkR]
        have : k ∈ ({extra} : Finset α) := by
          simpa [hcomp_eq] using hk_comp
        simpa using this
      simp [hk_extra]
  · intro hk_pair
    rw [Finset.mem_insert, Finset.mem_singleton] at hk_pair
    rcases hk_pair with hk_extra | hk_y
    · subst hk_extra
      intro a ha
      by_cases ha0 : a = b0.1
      · refine ⟨y, hy_ne_extra, ?_⟩
        rw [ha0]
        exact hrep b0
      · let b : β := ⟨a, ha⟩
        refine ⟨rep b, ?_, hrep b⟩
        intro hrep_extra
        have hbR : rep b ∈ R := by
          dsimp [R]
          exact Finset.mem_image.mpr ⟨b, by simp, rfl⟩
        exact hextra_not_R (by simpa [hrep_extra] using hbR)
    · subst hk_y
      intro a ha
      by_cases ha0 : a = b0.1
      · refine ⟨extra, hy_ne_extra.symm, ?_⟩
        exact ha0.symm
      · let b : β := ⟨a, ha⟩
        refine ⟨rep b, ?_, hrep b⟩
        intro hrep_y
        have hb_eq_b0 : b = b0 := hrep_inj hrep_y
        have hval : b.1 = b0.1 := congrArg Subtype.val hb_eq_b0
        exact ha0 (by simpa [b] using hval)

theorem relevantOmissions_card_eq_two_of_only_missing_absent
    (f : α → α) (missing : α)
    (hmissing_empty : fiber f missing = ∅)
    (hnonmissing_nonempty :
      ∀ a : α, a ≠ missing → (fiber f a).Nonempty) :
    (relevantOmissions f missing).card = 2 := by
  classical
  rcases relevantOmissions_eq_pair_of_only_missing_absent
      f missing hmissing_empty hnonmissing_nonempty with ⟨x, y, hxy, hset⟩
  rw [hset]
  simp [hxy]

theorem even_relevantOmissions_of_not_surjective
    (f : α → α) (missing : α)
    (hnot : ¬ Function.Surjective f) :
    Even (relevantOmissions f missing).card := by
  classical
  by_cases h_absent_nonmissing :
      ∃ a : α, a ≠ missing ∧ fiber f a = ∅
  · rcases h_absent_nonmissing with ⟨a, ha, habs⟩
    rw [relevantOmissions_card_eq_zero_of_absent_nonmissing f missing a ha habs]
    exact ⟨0, rfl⟩
  · have hnonmissing_nonempty :
        ∀ a : α, a ≠ missing → (fiber f a).Nonempty := by
      intro a ha
      by_contra hne
      apply h_absent_nonmissing
      refine ⟨a, ha, ?_⟩
      exact Finset.not_nonempty_iff_eq_empty.mp hne
    have hmissing_empty : fiber f missing = ∅ := by
      ext i
      constructor
      · intro hi
        exfalso
        apply hnot
        intro a
        by_cases ha : a = missing
        · subst ha
          exact ⟨i, by simpa [mem_fiber_iff] using hi⟩
        · rcases hnonmissing_nonempty a ha with ⟨j, hj⟩
          exact ⟨j, by simpa [mem_fiber_iff] using hj⟩
      · intro hi_empty
        simpa using hi_empty
    rw [relevantOmissions_card_eq_two_of_only_missing_absent
      f missing hmissing_empty hnonmissing_nonempty]
    exact even_two

theorem odd_relevant_omissions_iff_surjective
    (f : α → α) (missing : α) :
    Odd ((relevantOmissions f missing).card)
      ↔ Function.Surjective f := by
  classical
  constructor
  · intro hodd
    by_contra hnot
    have hnotodd : ¬ Odd (relevantOmissions f missing).card :=
      (Nat.not_odd_iff_even).2
        (even_relevantOmissions_of_not_surjective f missing hnot)
    exact hnotodd hodd
  · intro hsurj
    rw [relevantOmissions_card_eq_one_of_surjective f missing hsurj]
    norm_num

end LocalDeletionParity

namespace FreudenthalSimplex

theorem isFullyColored_iff_labelAt_surjective {d N : ℕ}
    (C : Coloring d N) (σ : FreudenthalSimplex d N) :
    IsFullyColored C σ
      ↔
    Function.Surjective (fun k : Fin (d + 1) => C.color (σ.vertex k)) := by
  classical
  rw [IsFullyColored, Sperner.fullyLabeled_iff]
  constructor
  · intro h a
    have ha : a ∈ Sperner.labelsOn C.color σ.vertices := h a
    rcases (Sperner.mem_labelsOn_iff C.color σ.vertices a).mp ha with
      ⟨v, hv, hcolor⟩
    rcases (σ.mem_vertices_iff v).mp hv with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa [hk] using hcolor
  · intro h a
    rcases h a with ⟨k, hk⟩
    apply (Sperner.mem_labelsOn_iff C.color σ.vertices a).mpr
    refine ⟨σ.vertex k, ?_, hk⟩
    exact (σ.mem_vertices_iff (σ.vertex k)).mpr ⟨k, rfl⟩

theorem local_parity {d N : ℕ}
    (C : Coloring d N)
    (σ : FreudenthalSimplex d N)
    (missing : Label d) :
    Odd (σ.relevantOmittedIndices C missing).card
      ↔
    IsFullyColored C σ := by
  classical
  let f : Fin (d + 1) → Fin (d + 1) :=
    fun k => C.color (σ.vertex k)
  have hset :
      σ.relevantOmittedIndices C missing =
        LocalDeletionParity.relevantOmissions f missing := by
    ext k
    rw [FreudenthalSimplex.mem_relevantOmittedIndices_iff,
      LocalDeletionParity.mem_relevantOmissions_iff]
    constructor
    · intro h a ha
      have ha_mem := h a ha
      rcases (Sperner.mem_labelsOn_iff C.color
          ((FreudenthalFacet.mk σ k).vertices) a).mp ha_mem with
        ⟨v, hv, hcolor⟩
      rcases (FreudenthalFacet.mem_vertices_iff (FreudenthalFacet.mk σ k) v).mp hv with
        ⟨i, hik, hiv⟩
      refine ⟨i, hik, ?_⟩
      simpa [f, hiv] using hcolor
    · intro h a ha
      rcases h a ha with ⟨i, hik, hfi⟩
      apply (Sperner.mem_labelsOn_iff C.color
        ((FreudenthalFacet.mk σ k).vertices) a).mpr
      refine ⟨σ.vertex i, ?_, hfi⟩
      exact (FreudenthalFacet.mem_vertices_iff (FreudenthalFacet.mk σ k)
        (σ.vertex i)).mpr ⟨i, hik, rfl⟩
  rw [hset]
  rw [LocalDeletionParity.odd_relevant_omissions_iff_surjective]
  exact (isFullyColored_iff_labelAt_surjective C σ).symm

theorem local_parity_facets {d N : ℕ}
    (C : Coloring d N)
    (σ : FreudenthalSimplex d N)
    (missing : Label d) :
    Odd
      (((by
          classical
          exact Finset.univ.filter fun k : Fin (d + 1) =>
            EconLib.Sperner.AlmostFullyLabeled
              C.color missing
              ((FreudenthalFacet.mk σ k).vertices)) :
          Finset (Fin (d + 1))).card)
      ↔
    IsFullyColored C σ := by
  classical
  simpa [FreudenthalSimplex.relevantOmittedIndices]
    using σ.local_parity C missing

theorem relevantGeomFacets_card_eq_relevantOmittedIndices {d N : ℕ}
    (C : Coloring d N) (missing : Label d)
    (σ : FreudenthalSimplex d N) :
    (((baryFreudenthalTriangulationCertificate d N).relevantFacetsOfCell
      C.color missing σ).card)
      =
    (σ.relevantOmittedIndices C missing).card := by
  classical
  let T := baryFreudenthalTriangulationCertificate d N
  let toGeom : Fin (d + 1) → FreudenthalGeomFacet d N :=
    fun k => (FreudenthalFacet.mk σ k).toGeomFacet
  have hset :
      T.relevantFacetsOfCell C.color missing σ =
        (σ.relevantOmittedIndices C missing).image toGeom := by
    ext K
    rw [T.mem_relevantFacetsOfCell_iff]
    constructor
    · intro h
      rcases h with ⟨hK, hrel⟩
      rcases (FreudenthalSimplex.mem_geomFacets_iff σ K).mp hK with ⟨k, hk⟩
      refine Finset.mem_image.mpr ⟨k, ?_, hk⟩
      rw [FreudenthalSimplex.mem_relevantOmittedIndices_iff]
      have hval := congrArg Subtype.val hk
      change (FreudenthalFacet.mk σ k).vertices = K.1 at hval
      dsimp [T, baryFreudenthalTriangulationCertificate,
        Sperner.SpernerTriangulationCertificate.relevantFacet] at hrel
      change Sperner.AlmostFullyLabeled C.color missing
        (FreudenthalFacet.mk σ k).vertices
      rw [hval]
      exact hrel
    · intro h
      rcases Finset.mem_image.mp h with ⟨k, hkrel, hk⟩
      constructor
      · exact (FreudenthalSimplex.mem_geomFacets_iff σ K).mpr ⟨k, hk⟩
      · rw [FreudenthalSimplex.mem_relevantOmittedIndices_iff] at hkrel
        have hval := congrArg Subtype.val hk
        change (FreudenthalFacet.mk σ k).vertices = K.1 at hval
        dsimp [T, baryFreudenthalTriangulationCertificate,
          Sperner.SpernerTriangulationCertificate.relevantFacet]
        change Sperner.AlmostFullyLabeled C.color missing K.1
        rw [← hval]
        exact hkrel
  rw [hset]
  simpa [toGeom] using
    Finset.card_image_of_injective
      (σ.relevantOmittedIndices C missing)
      (FreudenthalSimplex.toGeomFacet_injective σ)

theorem local_parity_for_certificate {d N : ℕ}
    (C : Coloring d N) (missing : Label d)
    (σ : FreudenthalSimplex d N) :
    Odd
      (((baryFreudenthalTriangulationCertificate d N).relevantFacetsOfCell
        C.color missing σ).card)
      ↔
    IsFullyColored C σ := by
  classical
  rw [FreudenthalSimplex.relevantGeomFacets_card_eq_relevantOmittedIndices]
  exact σ.local_parity C missing

end FreudenthalSimplex

noncomputable def FreudenthalBoundaryRelevantFacets {d N : ℕ}
    (C : Coloring d N) (missing : Label d) :
    Finset (FreudenthalGeomFacet d N) :=
  (baryFreudenthalTriangulationCertificate d N).boundaryRelevantFacets
    C.color missing

/-
This theorem applies to the explicit-coordinate full-cube Freudenthal subcomplex
defined above.  The coverage audit shows this is not yet the full simplex-grid
Freudenthal triangulation.  The full n-dimensional Sperner theorem should use
the barycentric development below.
-/
theorem baryFreudenthal_sperner_of_boundary_odd {d N : ℕ}
    (C : Coloring d N) (missing : Label d)
    (boundary_odd :
      Odd (FreudenthalBoundaryRelevantFacets C missing).card) :
    ∃ σ : FreudenthalSimplex d N, IsFullyColored C σ := by
  classical
  let T := baryFreudenthalTriangulationCertificate d N
  have h :
      ∃ σ : FreudenthalSimplex d N,
        Sperner.FullyLabeled C.color (T.verticesOfCell σ) :=
    T.abstract_sperner C.color missing boundary_odd
      (FreudenthalSimplex.local_parity_for_certificate C missing)
  simpa [T, baryFreudenthalTriangulationCertificate, IsFullyColored] using h

/-!
## Local deletion-facet parity

For a simplex with exactly one vertex indexed by each label, the fixed-missing
local parity theorem is true: the number of deletion facets containing all
labels except `missing` is odd iff the simplex is fully labelled.  If a
non-missing label is absent, no deletion facet is relevant; if only `missing` is
absent, the relevant facets come in a pair from the duplicated non-missing
label.
-/

namespace BarycentricFreudenthal

/-- Barycentric grid points on the `d`-simplex with mesh `N`. -/
abbrev SimplexGrid (d N : ℕ) :=
  {x : Fin (d + 1) → ℕ // ∑ i, x i = N}

namespace SimplexGrid

/-- Coordinates with positive barycentric mass. -/
noncomputable def support {d N : ℕ} (x : SimplexGrid d N) :
    Finset (Fin (d + 1)) := by
  classical
  exact Finset.univ.filter fun i => 0 < x.1 i

theorem coord_le_N {d N : ℕ} (x : SimplexGrid d N)
    (i : Fin (d + 1)) :
    x.1 i ≤ N := by
  classical
  have hle_sum : x.1 i ≤ ∑ j : Fin (d + 1), x.1 j :=
    Finset.single_le_sum (by intro _ _; exact Nat.zero_le _)
      (by simp)
  simpa [x.2] using hle_sum

/--
Move one unit of barycentric mass from `src` to `dst`.

When `src = dst`, the two updates cancel; in Freudenthal steps the coordinates
come from adjacent entries of a permutation, so they are distinct.
-/
def transfer {d N : ℕ} (x : SimplexGrid d N)
    (src dst : Fin (d + 1)) (hpos : 0 < x.1 src) :
    SimplexGrid d N := by
  let lowered : Fin (d + 1) → ℕ :=
    Function.update x.1 src (x.1 src - 1)
  refine ⟨Function.update lowered dst (lowered dst + 1), ?_⟩
  have hdown :
      (∑ j : Fin (d + 1), lowered j) + 1 =
        ∑ j : Fin (d + 1), x.1 j := by
    simpa [lowered] using
      GridPoint.sum_update_sub_one x.1 src hpos
  have hup :
      (∑ j : Fin (d + 1),
          Function.update lowered dst (lowered dst + 1) j) =
        (∑ j : Fin (d + 1), lowered j) + 1 := by
    simpa using GridPoint.sum_update_add_one lowered dst
  rw [hup]
  exact hdown.trans x.2

theorem transfer_apply_src_of_ne {d N : ℕ} (x : SimplexGrid d N)
    {src dst : Fin (d + 1)} (hpos : 0 < x.1 src)
    (hne : src ≠ dst) :
    (transfer x src dst hpos).1 src = x.1 src - 1 := by
  simp [transfer, Function.update, hne]

theorem transfer_apply_dst_of_ne {d N : ℕ} (x : SimplexGrid d N)
    {src dst : Fin (d + 1)} (hpos : 0 < x.1 src)
    (hne : src ≠ dst) :
    (transfer x src dst hpos).1 dst = x.1 dst + 1 := by
  simp [transfer, Function.update, hne.symm]

theorem transfer_apply_ne {d N : ℕ} (x : SimplexGrid d N)
    {src dst i : Fin (d + 1)} (hpos : 0 < x.1 src)
    (hsrc : i ≠ src) (hdst : i ≠ dst) :
    (transfer x src dst hpos).1 i = x.1 i := by
  simp [transfer, Function.update, hsrc, hdst]

/-- `y` is obtained from `x` by moving one unit from `src` to `tgt`. -/
def IsDirectedTransfer {d N : ℕ}
    (x y : SimplexGrid d N)
    (src tgt : Fin (d + 1)) : Prop :=
  src ≠ tgt ∧
  y.1 src + 1 = x.1 src ∧
  y.1 tgt = x.1 tgt + 1 ∧
  ∀ i, i ≠ src → i ≠ tgt → y.1 i = x.1 i

theorem isDirectedTransfer_transfer {d N : ℕ}
    (x : SimplexGrid d N)
    (src tgt : Fin (d + 1))
    (hneq : src ≠ tgt)
    (hpos : 0 < x.1 src) :
    IsDirectedTransfer x (transfer x src tgt hpos) src tgt := by
  classical
  refine ⟨hneq, ?_, ?_, ?_⟩
  · rw [transfer_apply_src_of_ne x hpos hneq]
    omega
  · exact transfer_apply_dst_of_ne x hpos hneq
  · intro i hsrc htgt
    exact transfer_apply_ne x hpos hsrc htgt

theorem IsDirectedTransfer.unique {d N : ℕ}
    {x y : SimplexGrid d N}
    {src₁ tgt₁ src₂ tgt₂ : Fin (d + 1)}
    (h₁ : IsDirectedTransfer x y src₁ tgt₁)
    (h₂ : IsDirectedTransfer x y src₂ tgt₂) :
    src₁ = src₂ ∧ tgt₁ = tgt₂ := by
  classical
  rcases h₁ with ⟨hneq₁, hsrc₁, htgt₁, hsame₁⟩
  rcases h₂ with ⟨hneq₂, hsrc₂, htgt₂, hsame₂⟩
  have hsrc : src₁ = src₂ := by
    by_contra hne
    by_cases hsrc₁_tgt₂ : src₁ = tgt₂
    · subst hsrc₁_tgt₂
      omega
    · have hsame := hsame₂ src₁ hne hsrc₁_tgt₂
      omega
  have htgt : tgt₁ = tgt₂ := by
    by_contra hne
    have htgt₁_ne_src₂ : tgt₁ ≠ src₂ := by
      intro h
      apply hneq₁
      exact hsrc.trans h.symm
    have hsame := hsame₂ tgt₁ htgt₁_ne_src₂ hne
    omega
  exact ⟨hsrc, htgt⟩

/-- Coordinates where two barycentric grid points differ. -/
noncomputable def diffSupport {d N : ℕ}
    (x y : SimplexGrid d N) : Finset (Fin (d + 1)) :=
  Finset.univ.filter fun i => x.1 i ≠ y.1 i

theorem diffSupport_transfer_eq_pair {d N : ℕ}
    (x : SimplexGrid d N)
    (src dst : Fin (d + 1))
    (hneq : src ≠ dst)
    (hpos : 0 < x.1 src) :
    diffSupport x (transfer x src dst hpos) =
      ({src, dst} : Finset (Fin (d + 1))) := by
  classical
  ext i
  by_cases hsrc : i = src
  · subst i
    have hcoord := transfer_apply_src_of_ne x hpos hneq
    have hchanged : x.1 src ≠ x.1 src - 1 := by
      omega
    simpa [diffSupport, hcoord, hneq] using hchanged
  · by_cases hdst : i = dst
    · subst i
      have hcoord := transfer_apply_dst_of_ne x hpos hneq
      have hchanged : x.1 dst ≠ x.1 dst + 1 := by
        omega
      simpa [diffSupport, hcoord, hsrc, hneq.symm] using hchanged
    · have hcoord := transfer_apply_ne x hpos hsrc hdst
      simp [diffSupport, hcoord, hsrc, hdst]

theorem diffSupport_transfer {d N : ℕ}
    (x : SimplexGrid d N)
    (src dst : Fin (d + 1))
    (hneq : src ≠ dst)
    (hpos : 0 < x.1 src) :
    (diffSupport x (transfer x src dst hpos)).card = 2 := by
  classical
  rw [diffSupport_transfer_eq_pair x src dst hneq hpos]
  simp [hneq]

theorem diffSupport_comm {d N : ℕ}
    (x y : SimplexGrid d N) :
    diffSupport x y = diffSupport y x := by
  classical
  ext i
  simp [diffSupport, ne_comm]

/-- All barycentric grid points, enumerated through bounded coordinate functions. -/
noncomputable def all (d N : ℕ) : Finset (SimplexGrid d N) := by
  classical
  exact ((Finset.univ : Finset (Fin (d + 1) → Fin (N + 1))).filter fun x =>
      (∑ i : Fin (d + 1), (x i).val) = N).attach.image fun x =>
    ⟨fun i => (x.1 i).val, by
      exact (Finset.mem_filter.mp x.2).2⟩

theorem mem_all {d N : ℕ} (x : SimplexGrid d N) : x ∈ all d N := by
  classical
  let bx : Fin (d + 1) → Fin (N + 1) := fun i =>
    ⟨x.1 i, Nat.lt_succ_of_le (x.coord_le_N i)⟩
  have hbx : bx ∈ (Finset.univ.filter fun y : Fin (d + 1) → Fin (N + 1) =>
      (∑ i : Fin (d + 1), (y i).val) = N) := by
    simp [bx, x.2]
  refine Finset.mem_image.mpr ⟨⟨bx, hbx⟩, Finset.mem_attach _ _, ?_⟩
  ext i
  rfl

noncomputable instance instFintype (d N : ℕ) : Fintype (SimplexGrid d N) :=
  ⟨all d N, mem_all⟩

noncomputable instance instDecidableEq (d N : ℕ) :
    DecidableEq (SimplexGrid d N) :=
  Classical.decEq _

end SimplexGrid

/-- The source index for the `r`th transfer in a barycentric Freudenthal chain. -/
def stepFromIndex {d : ℕ} (r : Fin d) : Fin (d + 1) :=
  ⟨r.val, Nat.lt_trans r.isLt (Nat.lt_succ_self d)⟩

/-- The target index for the `r`th transfer in a barycentric Freudenthal chain. -/
def stepToIndex {d : ℕ} (r : Fin d) : Fin (d + 1) :=
  ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩

theorem stepFromIndex_ne_stepToIndex {d : ℕ} (r : Fin d) :
    stepFromIndex r ≠ stepToIndex r := by
  intro h
  have hval := congrArg Fin.val h
  simp [stepFromIndex, stepToIndex] at hval

/-- Number of prefix transfers, before vertex `k`, leaving coordinate `i`. -/
def outgoingCount {d : ℕ}
    (p : Equiv.Perm (Fin (d + 1)))
    (k : Fin (d + 1))
    (i : Fin (d + 1)) : ℕ :=
  ((Finset.univ : Finset (Fin k.val)).filter fun r =>
    p ⟨r.val, by omega⟩ = i).card

/-- Number of prefix transfers, before vertex `k`, entering coordinate `i`. -/
def incomingCount {d : ℕ}
    (p : Equiv.Perm (Fin (d + 1)))
    (k : Fin (d + 1))
    (i : Fin (d + 1)) : ℕ :=
  ((Finset.univ : Finset (Fin k.val)).filter fun r =>
    p ⟨r.val + 1, by omega⟩ = i).card

theorem sum_outgoingCount {d : ℕ}
    (p : Equiv.Perm (Fin (d + 1)))
    (k : Fin (d + 1)) :
    (∑ i : Fin (d + 1), outgoingCount p k i) = k.val := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (s := (Finset.univ : Finset (Fin k.val)))
    (t := (Finset.univ : Finset (Fin (d + 1))))
    (g := fun r : Fin k.val => p ⟨r.val, by omega⟩)
  simpa [outgoingCount] using h

theorem sum_incomingCount {d : ℕ}
    (p : Equiv.Perm (Fin (d + 1)))
    (k : Fin (d + 1)) :
    (∑ i : Fin (d + 1), incomingCount p k i) = k.val := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (s := (Finset.univ : Finset (Fin k.val)))
    (t := (Finset.univ : Finset (Fin (d + 1))))
    (g := fun r : Fin k.val => p ⟨r.val + 1, by omega⟩)
  simpa [incomingCount] using h

theorem outgoingCount_eq_ite {d : ℕ}
    (p : Equiv.Perm (Fin (d + 1)))
    (k : Fin (d + 1))
    (i : Fin (d + 1)) :
    outgoingCount p k i =
      if (p.symm i).val < k.val then 1 else 0 := by
  classical
  by_cases hlt : (p.symm i).val < k.val
  · have hfilter :
        ((Finset.univ : Finset (Fin k.val)).filter fun r =>
            p ⟨r.val, by omega⟩ = i) =
          {⟨(p.symm i).val, hlt⟩} := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hr
        have ha : (⟨r.val, by omega⟩ : Fin (d + 1)) = p.symm i := by
          apply p.injective
          simpa using hr
        exact Fin.ext (congrArg (fun x : Fin (d + 1) => x.val) ha)
      · intro hr
        subst hr
        simpa using Equiv.apply_symm_apply p i
    simp [outgoingCount, hfilter, hlt]
  · have hfilter :
        ((Finset.univ : Finset (Fin k.val)).filter fun r =>
            p ⟨r.val, by omega⟩ = i) = ∅ := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hr
        exfalso
        have ha : (⟨r.val, by omega⟩ : Fin (d + 1)) = p.symm i := by
          apply p.injective
          simpa using hr
        have : (p.symm i).val < k.val := by
          rw [← congrArg (fun x : Fin (d + 1) => x.val) ha]
          exact r.isLt
        exact hlt this
      · intro hfalse
        simpa using hfalse
    simp [outgoingCount, hfilter, hlt]

theorem incomingCount_eq_ite {d : ℕ}
    (p : Equiv.Perm (Fin (d + 1)))
    (k : Fin (d + 1))
    (i : Fin (d + 1)) :
    incomingCount p k i =
      if 0 < (p.symm i).val ∧ (p.symm i).val ≤ k.val then 1 else 0 := by
  classical
  by_cases hcond : 0 < (p.symm i).val ∧ (p.symm i).val ≤ k.val
  · have hpred : (p.symm i).val - 1 < k.val := by omega
    have hfilter :
        ((Finset.univ : Finset (Fin k.val)).filter fun r =>
            p ⟨r.val + 1, by omega⟩ = i) =
          {⟨(p.symm i).val - 1, hpred⟩} := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hr
        have ha : (⟨r.val + 1, by omega⟩ : Fin (d + 1)) = p.symm i := by
          apply p.injective
          simpa using hr
        have hval : r.val + 1 = (p.symm i).val :=
          congrArg (fun x : Fin (d + 1) => x.val) ha
        apply Fin.ext
        change r.val = (p.symm i).val - 1
        omega
      · intro hr
        subst hr
        have hfin :
            (⟨(p.symm i).val - 1 + 1, by omega⟩ : Fin (d + 1)) =
              p.symm i := by
          apply Fin.ext
          change (p.symm i).val - 1 + 1 = (p.symm i).val
          omega
        rw [hfin]
        exact Equiv.apply_symm_apply p i
    simp [incomingCount, hfilter, hcond]
  · have hfilter :
        ((Finset.univ : Finset (Fin k.val)).filter fun r =>
            p ⟨r.val + 1, by omega⟩ = i) = ∅ := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hr
        exfalso
        have ha : (⟨r.val + 1, by omega⟩ : Fin (d + 1)) = p.symm i := by
          apply p.injective
          simpa using hr
        have hval : r.val + 1 = (p.symm i).val :=
          congrArg (fun x : Fin (d + 1) => x.val) ha
        have : 0 < (p.symm i).val ∧ (p.symm i).val ≤ k.val := by
          constructor <;> omega
        exact hcond this
      · intro hfalse
        simpa using hfalse
    rw [incomingCount, hfilter, if_neg hcond]
    simp

theorem outgoingCount_succ_same {d : ℕ}
    (p : Equiv.Perm (Fin (d + 1)))
    (r : Fin d) :
    outgoingCount p (stepToIndex r) (p (stepFromIndex r)) =
      outgoingCount p (stepFromIndex r) (p (stepFromIndex r)) + 1 := by
  rw [outgoingCount_eq_ite, outgoingCount_eq_ite]
  have hsymm : p.symm (p (stepFromIndex r)) = stepFromIndex r :=
    Equiv.symm_apply_apply p (stepFromIndex r)
  simp [hsymm, stepFromIndex, stepToIndex]

theorem outgoingCount_succ_ne {d : ℕ}
    (p : Equiv.Perm (Fin (d + 1)))
    (r : Fin d)
    {i : Fin (d + 1)}
    (hi : i ≠ p (stepFromIndex r)) :
    outgoingCount p (stepToIndex r) i =
      outgoingCount p (stepFromIndex r) i := by
  rw [outgoingCount_eq_ite, outgoingCount_eq_ite]
  have hqne : (p.symm i).val ≠ (stepFromIndex r).val := by
    intro hval
    apply hi
    calc
      i = p (p.symm i) := (Equiv.apply_symm_apply p i).symm
      _ = p (stepFromIndex r) := by rw [Fin.ext hval]
  by_cases hlt : (p.symm i).val < (stepFromIndex r).val
  · have hlt' : (p.symm i).val < (stepToIndex r).val := by
      simp [stepFromIndex, stepToIndex] at hlt ⊢
      omega
    simp [hlt, hlt']
  · have hlt' : ¬ (p.symm i).val < (stepToIndex r).val := by
      intro h
      apply hqne
      simp [stepFromIndex, stepToIndex] at hlt h ⊢
      omega
    simp [hlt, hlt']

theorem incomingCount_succ_same {d : ℕ}
    (p : Equiv.Perm (Fin (d + 1)))
    (r : Fin d) :
    incomingCount p (stepToIndex r) (p (stepToIndex r)) =
      incomingCount p (stepFromIndex r) (p (stepToIndex r)) + 1 := by
  rw [incomingCount_eq_ite, incomingCount_eq_ite]
  have hsymm : p.symm (p (stepToIndex r)) = stepToIndex r :=
    Equiv.symm_apply_apply p (stepToIndex r)
  simp [hsymm, stepFromIndex, stepToIndex]

theorem incomingCount_succ_ne {d : ℕ}
    (p : Equiv.Perm (Fin (d + 1)))
    (r : Fin d)
    {i : Fin (d + 1)}
    (hi : i ≠ p (stepToIndex r)) :
    incomingCount p (stepToIndex r) i =
      incomingCount p (stepFromIndex r) i := by
  rw [incomingCount_eq_ite, incomingCount_eq_ite]
  have hqne : (p.symm i).val ≠ (stepToIndex r).val := by
    intro hval
    apply hi
    calc
      i = p (p.symm i) := (Equiv.apply_symm_apply p i).symm
      _ = p (stepToIndex r) := by rw [Fin.ext hval]
  by_cases hfrom : 0 < (p.symm i).val ∧
      (p.symm i).val ≤ (stepFromIndex r).val
  · have hto : 0 < (p.symm i).val ∧
        (p.symm i).val ≤ (stepToIndex r).val := by
      simp [stepFromIndex, stepToIndex] at hfrom ⊢
      omega
    rw [if_pos hto, if_pos hfrom]
  · have hto : ¬ (0 < (p.symm i).val ∧
        (p.symm i).val ≤ (stepToIndex r).val) := by
      intro h
      apply hfrom
      constructor
      · exact h.1
      · by_contra hle
        apply hqne
        simp [stepFromIndex, stepToIndex] at h hle ⊢
        omega
    rw [if_neg hto, if_neg hfrom]

/-- The closed-form prefix-transfer formula stays in `ℕ`. -/
def PrefixTransferAdmissible {d N : ℕ}
    (base : SimplexGrid d N)
    (p : Equiv.Perm (Fin (d + 1))) : Prop :=
  (∀ k : Fin (d + 1), ∀ i : Fin (d + 1),
    outgoingCount p k i ≤ base.1 i + incomingCount p k i)
  ∧
  (∀ r : Fin d,
    outgoingCount p (stepFromIndex r) (p (stepFromIndex r)) <
      base.1 (p (stepFromIndex r)) +
        incomingCount p (stepFromIndex r) (p (stepFromIndex r)))

theorem sum_add_sub_eq_of_pointwise_le {α : Type*} [Fintype α]
    (a b c : α → ℕ)
    (hle : ∀ i, c i ≤ a i + b i) :
    (∑ i, (a i + b i - c i)) =
      (∑ i, a i) + (∑ i, b i) - (∑ i, c i) := by
  classical
  have h := Finset.sum_tsub_distrib
    (s := (Finset.univ : Finset α))
    (f := fun i => a i + b i)
    (g := c)
    (by intro i _hi; exact hle i)
  simpa [Finset.sum_add_distrib] using h

/-- Closed-form vertex after the first `k` barycentric transfers. -/
noncomputable def baryVertex {d N : ℕ}
    (base : SimplexGrid d N)
    (p : Equiv.Perm (Fin (d + 1)))
    (h : PrefixTransferAdmissible base p)
    (k : Fin (d + 1)) :
    SimplexGrid d N := by
  refine ⟨fun i => base.1 i + incomingCount p k i - outgoingCount p k i, ?_⟩
  rw [sum_add_sub_eq_of_pointwise_le base.1
    (incomingCount p k) (outgoingCount p k) (h.1 k)]
  rw [base.2, sum_incomingCount p k, sum_outgoingCount p k]
  omega

theorem baryVertex_source_positive {d N : ℕ}
    (base : SimplexGrid d N)
    (p : Equiv.Perm (Fin (d + 1)))
    (h : PrefixTransferAdmissible base p)
    (r : Fin d) :
    0 <
      (baryVertex base p h (stepFromIndex r)).1
        (p (stepFromIndex r)) := by
  dsimp [baryVertex]
  exact Nat.sub_pos_of_lt (h.2 r)

def BaryDatumRealizable {d N : ℕ}
    (bp : SimplexGrid d N × Equiv.Perm (Fin (d + 1))) : Prop :=
  ∃ h : PrefixTransferAdmissible bp.1 bp.2,
    (∀ r : Fin d,
      baryVertex bp.1 bp.2 h (stepToIndex r) =
        SimplexGrid.transfer
          (baryVertex bp.1 bp.2 h (stepFromIndex r))
          (bp.2 (stepFromIndex r))
          (bp.2 (stepToIndex r))
          (baryVertex_source_positive bp.1 bp.2 h r))
    ∧
    Function.Injective (fun k : Fin (d + 1) =>
      baryVertex bp.1 bp.2 h k)

end BarycentricFreudenthal

end SpernerFreudenthal
end EconLib
