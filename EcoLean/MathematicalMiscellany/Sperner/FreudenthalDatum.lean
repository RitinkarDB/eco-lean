import EcoLean.MathematicalMiscellany.Sperner.BarycentricGrid

namespace EconLib
namespace SpernerFreudenthal

open scoped BigOperators

namespace BarycentricFreudenthal

/--
Barycentric Freudenthal simplex data.

In this barycentric formulation, the chain of vertices is stored explicitly.
The `step` field says consecutive vertices are obtained by transferring one
unit of mass along adjacent entries of `perm`.  This avoids baking a difficult
recursive positivity proof into the definition; finite enumeration of the
base-plus-permutation representation can be added after the geometry is stable.
-/
structure BaryFreudenthalSimplex (d N : ℕ) where
  vertex : Fin (d + 1) → SimplexGrid d N
  perm : Equiv.Perm (Fin (d + 1))
  stepPositive :
    ∀ r : Fin d, 0 < (vertex (stepFromIndex r)).1 (perm (stepFromIndex r))
  step :
    ∀ r : Fin d,
      vertex (stepToIndex r) =
        SimplexGrid.transfer
          (vertex (stepFromIndex r))
          (perm (stepFromIndex r))
          (perm (stepToIndex r))
          (stepPositive r)
  vertex_injective : Function.Injective vertex

namespace BaryFreudenthalSimplex

noncomputable def vertices {d N : ℕ} (σ : BaryFreudenthalSimplex d N) :
    Finset (SimplexGrid d N) :=
  Finset.univ.image σ.vertex

theorem mem_vertices_iff {d N : ℕ} (σ : BaryFreudenthalSimplex d N)
    (x : SimplexGrid d N) :
    x ∈ σ.vertices ↔ ∃ k : Fin (d + 1), σ.vertex k = x := by
  classical
  simp [vertices]

end BaryFreudenthalSimplex

/-- A syntactic deletion facet of a barycentric Freudenthal simplex. -/
structure BaryFreudenthalFacet (d N : ℕ) where
  simplex : BaryFreudenthalSimplex d N
  omitted : Fin (d + 1)

namespace BaryFreudenthalFacet

noncomputable def vertices {d N : ℕ} (F : BaryFreudenthalFacet d N) :
    Finset (SimplexGrid d N) :=
  (Finset.univ.erase F.omitted).image F.simplex.vertex

theorem mem_vertices_iff {d N : ℕ} (F : BaryFreudenthalFacet d N)
    (x : SimplexGrid d N) :
    x ∈ F.vertices ↔
      ∃ k : Fin (d + 1), k ≠ F.omitted ∧ F.simplex.vertex k = x := by
  classical
  simp [vertices]

theorem vertices_subset_simplex_vertices {d N : ℕ}
    (F : BaryFreudenthalFacet d N) :
    F.vertices ⊆ F.simplex.vertices := by
  classical
  intro x hx
  rcases (F.mem_vertices_iff x).mp hx with ⟨k, _hk, hkx⟩
  rw [F.simplex.mem_vertices_iff]
  exact ⟨k, hkx⟩

end BaryFreudenthalFacet

/-- Finite base-plus-permutation data for barycentric Freudenthal cells. -/
structure BaryFreudenthalDatum (d N : ℕ) where
  base : SimplexGrid d N
  perm : Equiv.Perm (Fin (d + 1))
  admissible : PrefixTransferAdmissible base perm
  step :
    ∀ r : Fin d,
      baryVertex base perm admissible (stepToIndex r) =
        SimplexGrid.transfer
          (baryVertex base perm admissible (stepFromIndex r))
          (perm (stepFromIndex r))
          (perm (stepToIndex r))
          (baryVertex_source_positive base perm admissible r)
  vertex_injective :
    Function.Injective (fun k : Fin (d + 1) =>
      baryVertex base perm admissible k)

namespace BaryFreudenthalDatum

/-- The closed-form vertex function associated to finite barycentric data. -/
noncomputable def vertex {d N : ℕ} (D : BaryFreudenthalDatum d N)
    (k : Fin (d + 1)) : SimplexGrid d N :=
  baryVertex D.base D.perm D.admissible k

theorem vertex_eq_iff {d N : ℕ}
    (D : BaryFreudenthalDatum d N)
    (i j : Fin (d + 1)) :
    D.vertex i = D.vertex j ↔ i = j := by
  constructor
  · intro h
    exact D.vertex_injective h
  · intro h
    subst h
    rfl

noncomputable def toSimplex {d N : ℕ}
    (D : BaryFreudenthalDatum d N) :
    BaryFreudenthalSimplex d N :=
  { vertex := D.vertex
    perm := D.perm
    stepPositive := fun r =>
      baryVertex_source_positive D.base D.perm D.admissible r
    step := fun r => D.step r
    vertex_injective := D.vertex_injective }

theorem vertex_succ_eq_transfer {d N : ℕ}
    (D : BaryFreudenthalDatum d N)
    (r : Fin d) :
    D.vertex (stepToIndex r) =
      SimplexGrid.transfer
        (D.vertex (stepFromIndex r))
        (D.perm (stepFromIndex r))
        (D.perm (stepToIndex r))
        (baryVertex_source_positive D.base D.perm D.admissible r) := by
  exact D.step r

theorem vertex_succ {d N : ℕ}
    (D : BaryFreudenthalDatum d N)
    (r : Fin d) :
    D.vertex ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ =
      SimplexGrid.transfer
        (D.vertex ⟨r.val, Nat.lt_trans r.isLt (Nat.lt_succ_self d)⟩)
        (D.perm ⟨r.val, Nat.lt_trans r.isLt (Nat.lt_succ_self d)⟩)
        (D.perm ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩)
        (baryVertex_source_positive D.base D.perm D.admissible r) := by
  exact D.vertex_succ_eq_transfer r

theorem transfer_source_coord {d N : ℕ}
    (D : BaryFreudenthalDatum d N)
    (r : Fin d) :
    (D.vertex (stepToIndex r)).1 (D.perm (stepFromIndex r)) + 1 =
      (D.vertex (stepFromIndex r)).1 (D.perm (stepFromIndex r)) := by
  classical
  have hstep := congrArg
    (fun x : SimplexGrid d N => x.1 (D.perm (stepFromIndex r)))
    (D.vertex_succ_eq_transfer r)
  have hstep' :
      (D.vertex (stepToIndex r)).1 (D.perm (stepFromIndex r)) =
        (SimplexGrid.transfer
          (D.vertex (stepFromIndex r))
          (D.perm (stepFromIndex r))
          (D.perm (stepToIndex r))
          (baryVertex_source_positive D.base D.perm D.admissible r)).1
          (D.perm (stepFromIndex r)) := by
    simpa using hstep
  have hneq :
      D.perm (stepFromIndex r) ≠ D.perm (stepToIndex r) := by
    intro h
    exact stepFromIndex_ne_stepToIndex r (D.perm.injective h)
  have hcoord :
      (SimplexGrid.transfer
          (D.vertex (stepFromIndex r))
          (D.perm (stepFromIndex r))
          (D.perm (stepToIndex r))
          (baryVertex_source_positive D.base D.perm D.admissible r)).1
          (D.perm (stepFromIndex r)) =
        (D.vertex (stepFromIndex r)).1 (D.perm (stepFromIndex r)) - 1 :=
    SimplexGrid.transfer_apply_src_of_ne
      (D.vertex (stepFromIndex r))
      (baryVertex_source_positive D.base D.perm D.admissible r)
      hneq
  have hpos :
      0 < (D.vertex (stepFromIndex r)).1 (D.perm (stepFromIndex r)) :=
    baryVertex_source_positive D.base D.perm D.admissible r
  rw [hstep', hcoord]
  omega

theorem transfer_target_coord {d N : ℕ}
    (D : BaryFreudenthalDatum d N)
    (r : Fin d) :
    (D.vertex (stepToIndex r)).1 (D.perm (stepToIndex r)) =
      (D.vertex (stepFromIndex r)).1 (D.perm (stepToIndex r)) + 1 := by
  classical
  have hstep := congrArg
    (fun x : SimplexGrid d N => x.1 (D.perm (stepToIndex r)))
    (D.vertex_succ_eq_transfer r)
  have hneq :
      D.perm (stepFromIndex r) ≠ D.perm (stepToIndex r) := by
    intro h
    exact stepFromIndex_ne_stepToIndex r (D.perm.injective h)
  have hcoord :
      (SimplexGrid.transfer
          (D.vertex (stepFromIndex r))
          (D.perm (stepFromIndex r))
          (D.perm (stepToIndex r))
          (baryVertex_source_positive D.base D.perm D.admissible r)).1
          (D.perm (stepToIndex r)) =
        (D.vertex (stepFromIndex r)).1 (D.perm (stepToIndex r)) + 1 :=
    SimplexGrid.transfer_apply_dst_of_ne
      (D.vertex (stepFromIndex r))
      (baryVertex_source_positive D.base D.perm D.admissible r)
      hneq
  exact hstep.trans hcoord

theorem consecutive_perm_eq_of_vertices_eq {d N : ℕ}
    (D E : BaryFreudenthalDatum d N)
    (r : Fin d)
    (h₀ : D.vertex (stepFromIndex r) = E.vertex (stepFromIndex r))
    (h₁ : D.vertex (stepToIndex r) = E.vertex (stepToIndex r)) :
    D.perm (stepFromIndex r) = E.perm (stepFromIndex r) ∧
      D.perm (stepToIndex r) = E.perm (stepToIndex r) := by
  classical
  have hDneq :
      D.perm (stepFromIndex r) ≠ D.perm (stepToIndex r) := by
    intro h
    exact stepFromIndex_ne_stepToIndex r (D.perm.injective h)
  have hEneq :
      E.perm (stepFromIndex r) ≠ E.perm (stepToIndex r) := by
    intro h
    exact stepFromIndex_ne_stepToIndex r (E.perm.injective h)
  have hDdir :
      SimplexGrid.IsDirectedTransfer
        (D.vertex (stepFromIndex r))
        (D.vertex (stepToIndex r))
        (D.perm (stepFromIndex r))
        (D.perm (stepToIndex r)) := by
    simpa [D.vertex_succ_eq_transfer r] using
      SimplexGrid.isDirectedTransfer_transfer
        (D.vertex (stepFromIndex r))
        (D.perm (stepFromIndex r))
        (D.perm (stepToIndex r))
        hDneq
        (baryVertex_source_positive D.base D.perm D.admissible r)
  have hEdir :
      SimplexGrid.IsDirectedTransfer
        (D.vertex (stepFromIndex r))
        (D.vertex (stepToIndex r))
        (E.perm (stepFromIndex r))
        (E.perm (stepToIndex r)) := by
    have hEdir₀ :
        SimplexGrid.IsDirectedTransfer
          (E.vertex (stepFromIndex r))
          (E.vertex (stepToIndex r))
          (E.perm (stepFromIndex r))
          (E.perm (stepToIndex r)) := by
      simpa [E.vertex_succ_eq_transfer r] using
        SimplexGrid.isDirectedTransfer_transfer
          (E.vertex (stepFromIndex r))
          (E.perm (stepFromIndex r))
          (E.perm (stepToIndex r))
          hEneq
          (baryVertex_source_positive E.base E.perm E.admissible r)
    simpa [h₀, h₁] using hEdir₀
  exact SimplexGrid.IsDirectedTransfer.unique hDdir hEdir

theorem diffSupport_consecutive {d N : ℕ}
    (D : BaryFreudenthalDatum d N)
    (r : Fin d) :
    SimplexGrid.diffSupport
        (D.vertex (stepFromIndex r))
        (D.vertex (stepToIndex r))
      =
      ({D.perm (stepFromIndex r), D.perm (stepToIndex r)} :
        Finset (Fin (d + 1))) := by
  classical
  rw [D.vertex_succ_eq_transfer r]
  have hidx : stepFromIndex r ≠ stepToIndex r :=
    stepFromIndex_ne_stepToIndex r
  have hneq :
      D.perm (stepFromIndex r) ≠ D.perm (stepToIndex r) := by
    intro h
    exact hidx (D.perm.injective h)
  exact SimplexGrid.diffSupport_transfer_eq_pair
    (D.vertex (stepFromIndex r))
    (D.perm (stepFromIndex r))
    (D.perm (stepToIndex r))
    hneq
    (baryVertex_source_positive D.base D.perm D.admissible r)

theorem vertex_ne_of_perm_symm_eq_left {d N : ℕ}
    (D : BaryFreudenthalDatum d N)
    {a b : Fin (d + 1)}
    (hab : a.val < b.val)
    (i : Fin (d + 1))
    (hq : D.perm.symm i = a) :
    (D.vertex a).1 i ≠ (D.vertex b).1 i := by
  classical
  have houta : outgoingCount D.perm a i = 0 := by
    rw [outgoingCount_eq_ite]
    simp [hq]
  have houtb : outgoingCount D.perm b i = 1 := by
    rw [outgoingCount_eq_ite]
    simp [hq, hab]
  have hin : incomingCount D.perm a i = incomingCount D.perm b i := by
    rw [incomingCount_eq_ite, incomingCount_eq_ite]
    by_cases ha0 : 0 < a.val
    · have hca :
          0 < (D.perm.symm i).val ∧ (D.perm.symm i).val ≤ a.val := by
        simp [hq, ha0]
      have hcb :
          0 < (D.perm.symm i).val ∧ (D.perm.symm i).val ≤ b.val := by
        simp [hq, ha0, le_of_lt hab]
      rw [if_pos hca, if_pos hcb]
    · have hca :
          ¬ (0 < (D.perm.symm i).val ∧ (D.perm.symm i).val ≤ a.val) := by
        simp [hq, ha0]
      have hcb :
          ¬ (0 < (D.perm.symm i).val ∧ (D.perm.symm i).val ≤ b.val) := by
        simp [hq, ha0]
      rw [if_neg hca, if_neg hcb]
  have hle := D.admissible.1 b i
  rw [houtb] at hle
  dsimp [BaryFreudenthalDatum.vertex, baryVertex]
  rw [houta, houtb, hin]
  omega

theorem vertex_ne_of_perm_symm_eq_right {d N : ℕ}
    (D : BaryFreudenthalDatum d N)
    {a b : Fin (d + 1)}
    (hab : a.val < b.val)
    (i : Fin (d + 1))
    (hq : D.perm.symm i = b) :
    (D.vertex a).1 i ≠ (D.vertex b).1 i := by
  classical
  have hb0 : 0 < b.val := by omega
  have houta : outgoingCount D.perm a i = 0 := by
    rw [outgoingCount_eq_ite]
    simp [hq]
    omega
  have houtb : outgoingCount D.perm b i = 0 := by
    rw [outgoingCount_eq_ite]
    simp [hq]
  have hina : incomingCount D.perm a i = 0 := by
    rw [incomingCount_eq_ite]
    have hc :
        ¬ (0 < (D.perm.symm i).val ∧ (D.perm.symm i).val ≤ a.val) := by
      simp [hq]
      omega
    rw [if_neg hc]
  have hinb : incomingCount D.perm b i = 1 := by
    rw [incomingCount_eq_ite]
    have hc :
        0 < (D.perm.symm i).val ∧ (D.perm.symm i).val ≤ b.val := by
      simp [hq, hb0]
    rw [if_pos hc]
  dsimp [BaryFreudenthalDatum.vertex, baryVertex]
  rw [houta, houtb, hina, hinb]
  omega

theorem vertex_eq_of_perm_symm_ne_endpoints {d N : ℕ}
    (D : BaryFreudenthalDatum d N)
    {a b : Fin (d + 1)}
    (hab : a.val < b.val)
    (i : Fin (d + 1))
    (hqa : D.perm.symm i ≠ a)
    (hqb : D.perm.symm i ≠ b) :
    (D.vertex a).1 i = (D.vertex b).1 i := by
  classical
  let q := D.perm.symm i
  have hqaval : q.val ≠ a.val := by
    intro h
    exact hqa (Fin.ext h)
  have hqbval : q.val ≠ b.val := by
    intro h
    exact hqb (Fin.ext h)
  by_cases hltqa : q.val < a.val
  · have houta : outgoingCount D.perm a i = 1 := by
      rw [outgoingCount_eq_ite]
      have : (D.perm.symm i).val < a.val := hltqa
      simp [this]
    have houtb : outgoingCount D.perm b i = 1 := by
      rw [outgoingCount_eq_ite]
      have : (D.perm.symm i).val < b.val := by omega
      simp [this]
    have hin : incomingCount D.perm a i = incomingCount D.perm b i := by
      rw [incomingCount_eq_ite, incomingCount_eq_ite]
      by_cases hq0 : 0 < (D.perm.symm i).val
      · have hca :
            0 < (D.perm.symm i).val ∧ (D.perm.symm i).val ≤ a.val := by
          omega
        have hcb :
            0 < (D.perm.symm i).val ∧ (D.perm.symm i).val ≤ b.val := by
          omega
        rw [if_pos hca, if_pos hcb]
      · have hca :
            ¬ (0 < (D.perm.symm i).val ∧ (D.perm.symm i).val ≤ a.val) := by
          omega
        have hcb :
            ¬ (0 < (D.perm.symm i).val ∧ (D.perm.symm i).val ≤ b.val) := by
          omega
        rw [if_neg hca, if_neg hcb]
    dsimp [BaryFreudenthalDatum.vertex, baryVertex]
    rw [houta, houtb, hin]
  · by_cases hltqb : q.val < b.val
    · have houta : outgoingCount D.perm a i = 0 := by
        rw [outgoingCount_eq_ite]
        have : ¬ (D.perm.symm i).val < a.val := hltqa
        rw [if_neg this]
      have houtb : outgoingCount D.perm b i = 1 := by
        rw [outgoingCount_eq_ite]
        have : (D.perm.symm i).val < b.val := hltqb
        rw [if_pos this]
      have hina : incomingCount D.perm a i = 0 := by
        rw [incomingCount_eq_ite]
        have hc :
            ¬ (0 < (D.perm.symm i).val ∧ (D.perm.symm i).val ≤ a.val) := by
          omega
        rw [if_neg hc]
      have hinb : incomingCount D.perm b i = 1 := by
        rw [incomingCount_eq_ite]
        have hc :
            0 < (D.perm.symm i).val ∧ (D.perm.symm i).val ≤ b.val := by
          omega
        rw [if_pos hc]
      dsimp [BaryFreudenthalDatum.vertex, baryVertex]
      rw [houta, houtb, hina, hinb]
      omega
    · have houta : outgoingCount D.perm a i = 0 := by
        rw [outgoingCount_eq_ite]
        have : ¬ (D.perm.symm i).val < a.val := hltqa
        rw [if_neg this]
      have houtb : outgoingCount D.perm b i = 0 := by
        rw [outgoingCount_eq_ite]
        have : ¬ (D.perm.symm i).val < b.val := hltqb
        rw [if_neg this]
      have hin : incomingCount D.perm a i = incomingCount D.perm b i := by
        rw [incomingCount_eq_ite, incomingCount_eq_ite]
        have hca :
            ¬ (0 < (D.perm.symm i).val ∧ (D.perm.symm i).val ≤ a.val) := by
          omega
        have hcb :
            ¬ (0 < (D.perm.symm i).val ∧ (D.perm.symm i).val ≤ b.val) := by
          omega
        rw [if_neg hca, if_neg hcb]
      dsimp [BaryFreudenthalDatum.vertex, baryVertex]
      rw [houta, houtb, hin]

theorem vertex_diffSupport_eq_pair_of_lt {d N : ℕ}
    (D : BaryFreudenthalDatum d N)
    {a b : Fin (d + 1)}
    (hab : a.val < b.val) :
    SimplexGrid.diffSupport (D.vertex a) (D.vertex b) =
      ({D.perm a, D.perm b} : Finset (Fin (d + 1))) := by
  classical
  ext i
  simp only [SimplexGrid.diffSupport, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hdiff
    by_cases hqa : D.perm.symm i = a
    · left
      calc
        i = D.perm (D.perm.symm i) := (Equiv.apply_symm_apply D.perm i).symm
        _ = D.perm a := by rw [hqa]
    · by_cases hqb : D.perm.symm i = b
      · right
        calc
          i = D.perm (D.perm.symm i) := (Equiv.apply_symm_apply D.perm i).symm
          _ = D.perm b := by rw [hqb]
      · exact False.elim
          (hdiff (D.vertex_eq_of_perm_symm_ne_endpoints hab i hqa hqb))
  · intro hmem
    rcases hmem with hi | hi
    · have hq : D.perm.symm i = a := by
        calc
          D.perm.symm i = D.perm.symm (D.perm a) := by rw [hi]
          _ = a := Equiv.symm_apply_apply D.perm a
      exact D.vertex_ne_of_perm_symm_eq_left hab i hq
    · have hq : D.perm.symm i = b := by
        calc
          D.perm.symm i = D.perm.symm (D.perm b) := by rw [hi]
          _ = b := Equiv.symm_apply_apply D.perm b
      exact D.vertex_ne_of_perm_symm_eq_right hab i hq

theorem vertex_coord_int_eq_base_or_sub_one_of_perm_symm_zero {d N : ℕ}
    (D : BaryFreudenthalDatum d N)
    (k i : Fin (d + 1))
    (hq0 : (D.perm.symm i).val = 0) :
    ((D.vertex k).1 i : ℤ) = (D.base.1 i : ℤ) ∨
      ((D.vertex k).1 i : ℤ) = (D.base.1 i : ℤ) - 1 := by
  classical
  dsimp [BaryFreudenthalDatum.vertex, baryVertex]
  rw [outgoingCount_eq_ite, incomingCount_eq_ite]
  have hnotIn :
      ¬ (0 < (D.perm.symm i).val ∧ (D.perm.symm i).val ≤ k.val) := by
    omega
  rw [if_neg hnotIn]
  by_cases hout : (D.perm.symm i).val < k.val
  · rw [if_pos hout]
    right
    have hle := D.admissible.1 k i
    rw [outgoingCount_eq_ite, incomingCount_eq_ite, if_pos hout,
      if_neg hnotIn] at hle
    omega
  · rw [if_neg hout]
    left
    omega

theorem vertex_coord_int_eq_base_or_add_one_of_perm_symm_pos {d N : ℕ}
    (D : BaryFreudenthalDatum d N)
    (k i : Fin (d + 1))
    (hqpos : 0 < (D.perm.symm i).val) :
    ((D.vertex k).1 i : ℤ) = (D.base.1 i : ℤ) ∨
      ((D.vertex k).1 i : ℤ) = (D.base.1 i : ℤ) + 1 := by
  classical
  dsimp [BaryFreudenthalDatum.vertex, baryVertex]
  rw [outgoingCount_eq_ite, incomingCount_eq_ite]
  by_cases hkq : k.val = (D.perm.symm i).val
  · have hin :
        0 < (D.perm.symm i).val ∧ (D.perm.symm i).val ≤ k.val := by
      omega
    have hout : ¬ (D.perm.symm i).val < k.val := by
      omega
    rw [if_pos hin, if_neg hout]
    right
    omega
  · by_cases hlt : (D.perm.symm i).val < k.val
    · have hin :
          0 < (D.perm.symm i).val ∧ (D.perm.symm i).val ≤ k.val := by
        omega
      rw [if_pos hin, if_pos hlt]
      left
      omega
    · have hin :
          ¬ (0 < (D.perm.symm i).val ∧ (D.perm.symm i).val ≤ k.val) := by
        omega
      rw [if_neg hin, if_neg hlt]
      left
      omega

theorem vertex_coord_diff_abs_le_one {d N : ℕ}
    (D : BaryFreudenthalDatum d N)
    (a b : Fin (d + 1))
    (i : Fin (d + 1)) :
    |((D.vertex a).1 i : ℤ) - ((D.vertex b).1 i : ℤ)| ≤ 1 := by
  classical
  by_cases hq0 : (D.perm.symm i).val = 0
  · rcases D.vertex_coord_int_eq_base_or_sub_one_of_perm_symm_zero a i hq0 with
      ha | ha
    · rcases D.vertex_coord_int_eq_base_or_sub_one_of_perm_symm_zero b i hq0 with
        hb | hb
      · rw [ha, hb]
        norm_num
      · rw [ha, hb]
        norm_num
    · rcases D.vertex_coord_int_eq_base_or_sub_one_of_perm_symm_zero b i hq0 with
        hb | hb
      · rw [ha, hb]
        norm_num
      · rw [ha, hb]
        norm_num
  · have hqpos : 0 < (D.perm.symm i).val := by omega
    rcases D.vertex_coord_int_eq_base_or_add_one_of_perm_symm_pos a i hqpos with
      ha | ha
    · rcases D.vertex_coord_int_eq_base_or_add_one_of_perm_symm_pos b i hqpos with
        hb | hb
      · rw [ha, hb]
        norm_num
      · rw [ha, hb]
        norm_num
    · rcases D.vertex_coord_int_eq_base_or_add_one_of_perm_symm_pos b i hqpos with
        hb | hb
      · rw [ha, hb]
        norm_num
      · rw [ha, hb]
        norm_num

/-- The vertex set of a generated barycentric datum-cell. -/
noncomputable def vertices {d N : ℕ}
    (D : BaryFreudenthalDatum d N) :
    Finset (SimplexGrid d N) :=
  D.toSimplex.vertices

theorem mem_vertices_iff {d N : ℕ}
    (D : BaryFreudenthalDatum d N)
    (x : SimplexGrid d N) :
    x ∈ D.vertices ↔ ∃ k : Fin (d + 1), D.vertex k = x := by
  classical
  simp [vertices, toSimplex, BaryFreudenthalSimplex.mem_vertices_iff]

theorem ext_of_base_perm {d N : ℕ}
    (D E : BaryFreudenthalDatum d N)
    (hbase : D.base = E.base)
    (hperm : D.perm = E.perm) :
    D = E := by
  cases D with
  | mk baseD permD admD stepD injD =>
    cases E with
    | mk baseE permE admE stepE injE =>
      dsimp at hbase hperm
      subst baseE
      subst permE
      simp

noncomputable instance instDecidableEq (d N : ℕ) :
    DecidableEq (BaryFreudenthalDatum d N) :=
  Classical.decEq _

/-- All admissible barycentric base-plus-permutation data. -/
noncomputable def all (d N : ℕ) : Finset (BaryFreudenthalDatum d N) := by
  classical
  exact (((Finset.univ : Finset (SimplexGrid d N)).product
      (Finset.univ : Finset (Equiv.Perm (Fin (d + 1))))).filter fun bp =>
        BaryDatumRealizable bp).attach.image fun bp => by
    let bp0 : SimplexGrid d N × Equiv.Perm (Fin (d + 1)) := bp.1
    have hreal : BaryDatumRealizable bp0 := by
      simpa [bp0] using (Finset.mem_filter.mp bp.2).2
    let h : PrefixTransferAdmissible bp0.1 bp0.2 := Classical.choose hreal
    have hspec :
        (∀ r : Fin d,
          baryVertex bp0.1 bp0.2 h (stepToIndex r) =
            SimplexGrid.transfer
              (baryVertex bp0.1 bp0.2 h (stepFromIndex r))
              (bp0.2 (stepFromIndex r))
              (bp0.2 (stepToIndex r))
              (baryVertex_source_positive bp0.1 bp0.2 h r))
        ∧
        Function.Injective (fun k : Fin (d + 1) =>
          baryVertex bp0.1 bp0.2 h k) :=
      Classical.choose_spec hreal
    exact
      { base := bp0.1
        perm := bp0.2
        admissible := h
        step := hspec.1
        vertex_injective := hspec.2 }

theorem mem_all {d N : ℕ} (D : BaryFreudenthalDatum d N) :
    D ∈ all d N := by
  classical
  have hbp : (D.base, D.perm) ∈
      (((Finset.univ : Finset (SimplexGrid d N)).product
        (Finset.univ : Finset (Equiv.Perm (Fin (d + 1))))).filter fun bp =>
          BaryDatumRealizable bp) := by
    simp [BaryDatumRealizable, D.admissible, D.step, D.vertex_injective]
  refine Finset.mem_image.mpr ⟨⟨(D.base, D.perm), hbp⟩, Finset.mem_attach _ _, ?_⟩
  cases D
  simp

noncomputable instance instFintype (d N : ℕ) :
    Fintype (BaryFreudenthalDatum d N) :=
  ⟨all d N, mem_all⟩

end BaryFreudenthalDatum

/-- The finite universe of barycentric Freudenthal base-plus-permutation data. -/
noncomputable def allBaryFreudenthalData (d N : ℕ) :
    Finset (BaryFreudenthalDatum d N) :=
  Finset.univ

noncomputable instance instBaryFreudenthalSimplexDecidableEq (d N : ℕ) :
    DecidableEq (BaryFreudenthalSimplex d N) :=
  Classical.decEq _

/-- The finite family of explicit-chain simplices generated by barycentric data. -/
noncomputable def allBaryFreudenthalSimplices (d N : ℕ) :
    Finset (BaryFreudenthalSimplex d N) :=
  (allBaryFreudenthalData d N).image BaryFreudenthalDatum.toSimplex

theorem mem_allBaryFreudenthalSimplices_iff {d N : ℕ}
    (σ : BaryFreudenthalSimplex d N) :
    σ ∈ allBaryFreudenthalSimplices d N
      ↔
    ∃ D : BaryFreudenthalDatum d N, D.toSimplex = σ := by
  classical
  simp [allBaryFreudenthalSimplices, allBaryFreudenthalData]

namespace BaryFreudenthalFacet

theorem vertex_mem_vertices_iff {d N : ℕ}
    (σ : BaryFreudenthalSimplex d N)
    (omitIdx i : Fin (d + 1)) :
    σ.vertex i ∈ (BaryFreudenthalFacet.mk σ omitIdx).vertices
      ↔ i ≠ omitIdx := by
  classical
  rw [BaryFreudenthalFacet.mem_vertices_iff]
  constructor
  · intro h
    rcases h with ⟨j, hjne, hji⟩
    intro hi
    have hji' : σ.vertex j = σ.vertex omitIdx := by
      rw [← hi]
      simpa using hji
    have hj : j = omitIdx := σ.vertex_injective hji'
    exact hjne hj
  · intro hi
    exact ⟨i, hi, rfl⟩

end BaryFreudenthalFacet

namespace BaryFreudenthalSimplex

theorem deletionFacet_vertices_eq_iff {d N : ℕ}
    (σ : BaryFreudenthalSimplex d N)
    (k l : Fin (d + 1)) :
    (BaryFreudenthalFacet.mk σ k).vertices =
      (BaryFreudenthalFacet.mk σ l).vertices
      ↔ k = l := by
  classical
  constructor
  · intro h
    by_contra hne
    have hl_mem_left :
        σ.vertex l ∈ (BaryFreudenthalFacet.mk σ k).vertices := by
      rw [BaryFreudenthalFacet.vertex_mem_vertices_iff]
      exact fun hlk => hne hlk.symm
    have hl_mem_right :
        σ.vertex l ∈ (BaryFreudenthalFacet.mk σ l).vertices := by
      simpa [h] using hl_mem_left
    have hnot := (BaryFreudenthalFacet.vertex_mem_vertices_iff σ l l).mp
      hl_mem_right
    exact hnot rfl
  · intro h
    subst h
    rfl

theorem erase_vertex_eq_deletionFacet_vertices {d N : ℕ}
    (σ : BaryFreudenthalSimplex d N)
    (k : Fin (d + 1)) :
    σ.vertices.erase (σ.vertex k) =
      (BaryFreudenthalFacet.mk σ k).vertices := by
  classical
  ext x
  rw [Finset.mem_erase, BaryFreudenthalFacet.mem_vertices_iff]
  constructor
  · intro hx
    rcases (σ.mem_vertices_iff x).mp hx.2 with ⟨j, hjx⟩
    refine ⟨j, ?_, hjx⟩
    intro hjk
    exact hx.1 (by rw [← hjx, hjk])
  · intro hx
    rcases hx with ⟨j, hjne, hjx⟩
    constructor
    · intro hxk
      apply hjne
      apply σ.vertex_injective
      rw [hjx, hxk]
    · exact (σ.mem_vertices_iff x).mpr ⟨j, hjx⟩

end BaryFreudenthalSimplex

/-- A deletion facet of a generated barycentric datum-cell. -/
structure BaryFreudenthalDatumFacet (d N : ℕ) where
  datum : BaryFreudenthalDatum d N
  omitted : Fin (d + 1)

namespace BaryFreudenthalDatumFacet

noncomputable def simplex {d N : ℕ}
    (F : BaryFreudenthalDatumFacet d N) :
    BaryFreudenthalSimplex d N :=
  F.datum.toSimplex

noncomputable def toChainFacet {d N : ℕ}
    (F : BaryFreudenthalDatumFacet d N) :
    BaryFreudenthalFacet d N :=
  BaryFreudenthalFacet.mk F.simplex F.omitted

noncomputable def vertices {d N : ℕ}
    (F : BaryFreudenthalDatumFacet d N) :
    Finset (SimplexGrid d N) :=
  F.toChainFacet.vertices

theorem mem_vertices_iff {d N : ℕ}
    (F : BaryFreudenthalDatumFacet d N)
    (x : SimplexGrid d N) :
    x ∈ F.vertices ↔
      ∃ k : Fin (d + 1), k ≠ F.omitted ∧ F.datum.vertex k = x := by
  classical
  simp [vertices, toChainFacet, simplex, BaryFreudenthalFacet.mem_vertices_iff,
    BaryFreudenthalDatum.toSimplex]

def GeomEq {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N) : Prop :=
  F.vertices = G.vertices

def IsSelfIncident {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N) : Prop :=
  G.datum = F.datum

def IsAlternateIncident {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N) : Prop :=
  G.datum ≠ F.datum ∧ G.GeomEq F

theorem datum_eq_of_selfIncident {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N)
    (hself : F.IsSelfIncident G) :
    G.datum = F.datum :=
  hself

theorem ne_datum_of_alternateIncident {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N)
    (halt : F.IsAlternateIncident G) :
    G.datum ≠ F.datum :=
  halt.1

theorem geomEq_of_alternateIncident {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N)
    (halt : F.IsAlternateIncident G) :
    G.GeomEq F :=
  halt.2

/-- The ordered index type of vertices retained by a datum deletion facet. -/
abbrev IndexSet {d N : ℕ} (F : BaryFreudenthalDatumFacet d N) :=
  {i : Fin (d + 1) // i ≠ F.omitted}

def indexVal {d N : ℕ} {F : BaryFreudenthalDatumFacet d N}
    (i : F.IndexSet) : ℕ :=
  i.1.val

theorem vertices_eq_iff_omitted_eq_same_datum {d N : ℕ}
    (D : BaryFreudenthalDatum d N)
    (k l : Fin (d + 1)) :
    (BaryFreudenthalDatumFacet.mk D k).vertices =
        (BaryFreudenthalDatumFacet.mk D l).vertices
      ↔ k = l := by
  classical
  simpa [vertices, toChainFacet, simplex] using
    BaryFreudenthalSimplex.deletionFacet_vertices_eq_iff D.toSimplex k l

theorem same_datum_geomEq_iff_omitted_eq {d N : ℕ}
    (D : BaryFreudenthalDatum d N)
    (k l : Fin (d + 1)) :
    (BaryFreudenthalDatumFacet.mk D k).GeomEq
        (BaryFreudenthalDatumFacet.mk D l)
      ↔ k = l := by
  exact vertices_eq_iff_omitted_eq_same_datum D k l

theorem omitted_eq_of_same_datum_geomEq {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N)
    (hdatum : G.datum = F.datum)
    (hgeom : G.GeomEq F) :
    G.omitted = F.omitted := by
  classical
  cases F with
  | mk Fdatum Fomitted =>
    cases G with
    | mk Gdatum Gomitted =>
      dsimp at hdatum
      subst Gdatum
      exact
        (vertices_eq_iff_omitted_eq_same_datum
          Fdatum Gomitted Fomitted).mp hgeom

theorem omitted_eq_of_selfIncident {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N)
    (hself : F.IsSelfIncident G)
    (hgeom : G.GeomEq F) :
    G.omitted = F.omitted := by
  classical
  exact BaryFreudenthalDatumFacet.omitted_eq_of_same_datum_geomEq
    F G hself hgeom

theorem shared_facet_vertices {d N : ℕ}
    (F : BaryFreudenthalDatumFacet d N)
    (D : BaryFreudenthalDatum d N)
    (hD : ∃ k : Fin (d + 1),
      (BaryFreudenthalDatumFacet.mk D k).GeomEq F) :
    ∃ k : Fin (d + 1),
      ∀ x : SimplexGrid d N,
        x ∈ (BaryFreudenthalDatumFacet.mk D k).vertices ↔
          x ∈ F.vertices := by
  classical
  rcases hD with ⟨k, hk⟩
  change (BaryFreudenthalDatumFacet.mk D k).vertices = F.vertices at hk
  exact ⟨k, by intro x; simpa [hk]⟩

theorem exists_matchIndex {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N)
    (hgeom : G.GeomEq F)
    (i : {i : Fin (d + 1) // i ≠ F.omitted}) :
    ∃ j : Fin (d + 1),
      j ≠ G.omitted ∧ G.datum.vertex j = F.datum.vertex i.1 := by
  classical
  have hi_mem : F.datum.vertex i.1 ∈ F.vertices := by
    rw [BaryFreudenthalDatumFacet.mem_vertices_iff]
    exact ⟨i.1, i.2, rfl⟩
  have hverts : G.vertices = F.vertices := hgeom
  have hi_mem_G : F.datum.vertex i.1 ∈ G.vertices := by
    simpa [hverts] using hi_mem
  rcases (BaryFreudenthalDatumFacet.mem_vertices_iff
      G (F.datum.vertex i.1)).mp hi_mem_G with ⟨j, hj_ne, hj_eq⟩
  exact ⟨j, hj_ne, hj_eq⟩

noncomputable def matchIndex {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N)
    (hgeom : G.GeomEq F)
    (i : {i : Fin (d + 1) // i ≠ F.omitted}) :
    {j : Fin (d + 1) // j ≠ G.omitted} :=
  ⟨Classical.choose (exists_matchIndex F G hgeom i),
    (Classical.choose_spec (exists_matchIndex F G hgeom i)).1⟩

theorem matchIndex_spec {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N)
    (hgeom : G.GeomEq F)
    (i : {i : Fin (d + 1) // i ≠ F.omitted}) :
    G.datum.vertex ((F.matchIndex G hgeom i).1) =
      F.datum.vertex i.1 :=
  (Classical.choose_spec (exists_matchIndex F G hgeom i)).2

noncomputable def matchIndexVal {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N)
    (hgeom : G.GeomEq F)
    (i : F.IndexSet) : Fin (d + 1) :=
  (F.matchIndex G hgeom i).1

theorem matchIndexVal_ne_omitted {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N)
    (hgeom : G.GeomEq F)
    (i : F.IndexSet) :
    F.matchIndexVal G hgeom i ≠ G.omitted :=
  (F.matchIndex G hgeom i).2

theorem matchIndexVal_spec {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N)
    (hgeom : G.GeomEq F)
    (i : F.IndexSet) :
    G.datum.vertex (F.matchIndexVal G hgeom i) =
      F.datum.vertex i.1 := by
  simpa [matchIndexVal] using F.matchIndex_spec G hgeom i

theorem matchIndex_unique {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N)
    (hgeom : G.GeomEq F)
    (i : {i : Fin (d + 1) // i ≠ F.omitted})
    (j : {j : Fin (d + 1) // j ≠ G.omitted})
    (h : G.datum.vertex j.1 = F.datum.vertex i.1) :
    j = F.matchIndex G hgeom i := by
  apply Subtype.ext
  apply G.datum.vertex_injective
  calc
    G.datum.vertex j.1 = F.datum.vertex i.1 := h
    _ = G.datum.vertex ((F.matchIndex G hgeom i).1) :=
      (F.matchIndex_spec G hgeom i).symm

theorem matchIndex_bijective {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N)
    (hgeom : G.GeomEq F) :
    Function.Bijective (F.matchIndex G hgeom) := by
  constructor
  · intro i₁ i₂ h
    apply Subtype.ext
    apply F.datum.vertex_injective
    calc
      F.datum.vertex i₁.1 =
          G.datum.vertex ((F.matchIndex G hgeom i₁).1) :=
        (F.matchIndex_spec G hgeom i₁).symm
      _ = G.datum.vertex ((F.matchIndex G hgeom i₂).1) := by
        rw [h]
      _ = F.datum.vertex i₂.1 :=
        F.matchIndex_spec G hgeom i₂
  · intro j
    have hj_mem : G.datum.vertex j.1 ∈ G.vertices := by
      rw [BaryFreudenthalDatumFacet.mem_vertices_iff]
      exact ⟨j.1, j.2, rfl⟩
    have hverts : G.vertices = F.vertices := hgeom
    have hj_mem_F : G.datum.vertex j.1 ∈ F.vertices := by
      simpa [hverts] using hj_mem
    rcases (BaryFreudenthalDatumFacet.mem_vertices_iff
        F (G.datum.vertex j.1)).mp hj_mem_F with ⟨i, hi_ne, hi_eq⟩
    refine ⟨⟨i, hi_ne⟩, ?_⟩
    apply Subtype.ext
    apply G.datum.vertex_injective
    calc
      G.datum.vertex ((F.matchIndex G hgeom ⟨i, hi_ne⟩).1) =
          F.datum.vertex i :=
        F.matchIndex_spec G hgeom ⟨i, hi_ne⟩
      _ = G.datum.vertex j.1 := hi_eq

theorem matchIndex_preserves_diffSupport {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N)
    (hgeom : G.GeomEq F)
    (i j : F.IndexSet) :
    SimplexGrid.diffSupport
        (F.datum.vertex i.1)
        (F.datum.vertex j.1)
      =
      SimplexGrid.diffSupport
        (G.datum.vertex (F.matchIndex G hgeom i).1)
        (G.datum.vertex (F.matchIndex G hgeom j).1) := by
  rw [F.matchIndex_spec G hgeom i, F.matchIndex_spec G hgeom j]

theorem vertex_eq_of_matchIndex {d N : ℕ}
    (F G H : BaryFreudenthalDatumFacet d N)
    (hG : G.GeomEq F)
    (hH : H.GeomEq F)
    (i : F.IndexSet) :
    G.datum.vertex ((F.matchIndex G hG i).1) =
      H.datum.vertex ((F.matchIndex H hH i).1) := by
  calc
    G.datum.vertex ((F.matchIndex G hG i).1) =
        F.datum.vertex i.1 :=
      F.matchIndex_spec G hG i
    _ = H.datum.vertex ((F.matchIndex H hH i).1) :=
      (F.matchIndex_spec H hH i).symm

theorem matchIndex_preserves_endpoint_pairs {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N)
    (hgeom : G.GeomEq F)
    (i j : F.IndexSet)
    (hij : i.1.val < j.1.val) :
    ({F.datum.perm i.1, F.datum.perm j.1} : Finset (Fin (d + 1))) =
      ({G.datum.perm (F.matchIndex G hgeom i).1,
        G.datum.perm (F.matchIndex G hgeom j).1} :
        Finset (Fin (d + 1))) := by
  classical
  let mi := F.matchIndex G hgeom i
  let mj := F.matchIndex G hgeom j
  have hF :
      SimplexGrid.diffSupport
          (F.datum.vertex i.1) (F.datum.vertex j.1) =
        ({F.datum.perm i.1, F.datum.perm j.1} :
          Finset (Fin (d + 1))) :=
    F.datum.vertex_diffSupport_eq_pair_of_lt hij
  have hpres := F.matchIndex_preserves_diffSupport G hgeom i j
  have hmi_ne_mj : mi.1 ≠ mj.1 := by
    intro hval
    have hsub : mi = mj := Subtype.ext hval
    have hij_eq : i = j := (F.matchIndex_bijective G hgeom).1 hsub
    have hvalij : i.1.val = j.1.val := congrArg (fun x : F.IndexSet => x.1.val) hij_eq
    omega
  have hG :
      SimplexGrid.diffSupport
          (G.datum.vertex mi.1) (G.datum.vertex mj.1) =
        ({G.datum.perm mi.1, G.datum.perm mj.1} :
          Finset (Fin (d + 1))) := by
    by_cases hlt : mi.1.val < mj.1.val
    · exact G.datum.vertex_diffSupport_eq_pair_of_lt hlt
    · have hgt : mj.1.val < mi.1.val := by
        have hne_val : mi.1.val ≠ mj.1.val := by
          intro h
          exact hmi_ne_mj (Fin.ext h)
        omega
      have hrev :
          SimplexGrid.diffSupport
              (G.datum.vertex mj.1) (G.datum.vertex mi.1) =
            ({G.datum.perm mj.1, G.datum.perm mi.1} :
              Finset (Fin (d + 1))) :=
        G.datum.vertex_diffSupport_eq_pair_of_lt hgt
      calc
        SimplexGrid.diffSupport
            (G.datum.vertex mi.1) (G.datum.vertex mj.1)
            =
            SimplexGrid.diffSupport
              (G.datum.vertex mj.1) (G.datum.vertex mi.1) :=
          SimplexGrid.diffSupport_comm _ _
        _ = ({G.datum.perm mj.1, G.datum.perm mi.1} :
              Finset (Fin (d + 1))) := hrev
        _ = ({G.datum.perm mi.1, G.datum.perm mj.1} :
              Finset (Fin (d + 1))) := by
          ext x
          simp [or_comm]
  calc
    ({F.datum.perm i.1, F.datum.perm j.1} : Finset (Fin (d + 1)))
        =
        SimplexGrid.diffSupport
          (F.datum.vertex i.1) (F.datum.vertex j.1) := hF.symm
    _ =
        SimplexGrid.diffSupport
          (G.datum.vertex (F.matchIndex G hgeom i).1)
          (G.datum.vertex (F.matchIndex G hgeom j).1) := hpres
    _ = ({G.datum.perm (F.matchIndex G hgeom i).1,
          G.datum.perm (F.matchIndex G hgeom j).1} :
          Finset (Fin (d + 1))) := by
      simpa [mi, mj] using hG

theorem matchIndexVal_preserves_endpoint_pairs {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N)
    (hgeom : G.GeomEq F)
    (i j : F.IndexSet)
    (hij : i.1.val < j.1.val) :
    ({F.datum.perm i.1, F.datum.perm j.1} : Finset (Fin (d + 1))) =
      ({G.datum.perm (F.matchIndexVal G hgeom i),
        G.datum.perm (F.matchIndexVal G hgeom j)} :
        Finset (Fin (d + 1))) := by
  classical
  simpa [matchIndexVal] using
    F.matchIndex_preserves_endpoint_pairs G hgeom i j hij

def SameUnderlyingMatching {d N : ℕ}
    (F G H : BaryFreudenthalDatumFacet d N)
    (hG : G.GeomEq F)
    (hH : H.GeomEq F) : Prop :=
  ∀ i : F.IndexSet,
    F.matchIndexVal G hG i = F.matchIndexVal H hH i

theorem vertex_eq_of_sameUnderlyingMatching {d N : ℕ}
    (F G H : BaryFreudenthalDatumFacet d N)
    (hG : G.GeomEq F)
    (hH : H.GeomEq F)
    (hmatch : F.SameUnderlyingMatching G H hG hH)
    (i : F.IndexSet) :
    G.datum.vertex (F.matchIndexVal G hG i) =
      H.datum.vertex (F.matchIndexVal H hH i) := by
  have _h := hmatch i
  calc
    G.datum.vertex (F.matchIndexVal G hG i) =
        F.datum.vertex i.1 :=
      F.matchIndexVal_spec G hG i
    _ = H.datum.vertex (F.matchIndexVal H hH i) :=
      (F.matchIndexVal_spec H hH i).symm

theorem visible_vertices_eq_of_sameUnderlyingMatching {d N : ℕ}
    (F G H : BaryFreudenthalDatumFacet d N)
    (hG : G.GeomEq F)
    (hH : H.GeomEq F)
    (hmatch : F.SameUnderlyingMatching G H hG hH)
    (i : F.IndexSet) :
    G.datum.vertex (F.matchIndexVal G hG i) =
      H.datum.vertex (F.matchIndexVal H hH i) := by
  exact F.vertex_eq_of_sameUnderlyingMatching G H hG hH hmatch i

theorem visible_vertices_eq_on_nonomitted_of_sameUnderlyingMatching {d N : ℕ}
    (F G H : BaryFreudenthalDatumFacet d N)
    (hG : G.GeomEq F)
    (hH : H.GeomEq F)
    (homit : G.omitted = H.omitted)
    (hmatch : F.SameUnderlyingMatching G H hG hH)
    (j : Fin (d + 1))
    (hj : j ≠ G.omitted) :
    G.datum.vertex j = H.datum.vertex j := by
  classical
  have _hjH : j ≠ H.omitted := by
    simpa [← homit] using hj
  let jG : {j : Fin (d + 1) // j ≠ G.omitted} := ⟨j, hj⟩
  rcases (F.matchIndex_bijective G hG).2 jG with ⟨i, hi⟩
  have hGval : F.matchIndexVal G hG i = j := by
    exact congrArg Subtype.val hi
  have hHval : F.matchIndexVal H hH i = j := by
    calc
      F.matchIndexVal H hH i = F.matchIndexVal G hG i := (hmatch i).symm
      _ = j := hGval
  simpa [hGval, hHval] using
    F.visible_vertices_eq_of_sameUnderlyingMatching G H hG hH hmatch i

theorem perm_eq_of_visible_consecutive {d N : ℕ}
    (G H : BaryFreudenthalDatumFacet d N)
    (homit : G.omitted = H.omitted)
    (hvis :
      ∀ j : Fin (d + 1), j ≠ G.omitted →
        G.datum.vertex j = H.datum.vertex j)
    (r : Fin d)
    (hr₀ : stepFromIndex r ≠ G.omitted)
    (hr₁ : stepToIndex r ≠ G.omitted) :
    G.datum.perm (stepFromIndex r) = H.datum.perm (stepFromIndex r) ∧
      G.datum.perm (stepToIndex r) = H.datum.perm (stepToIndex r) := by
  classical
  have _hr₀H : stepFromIndex r ≠ H.omitted := by
    simpa [← homit] using hr₀
  have _hr₁H : stepToIndex r ≠ H.omitted := by
    simpa [← homit] using hr₁
  exact
    BaryFreudenthalDatum.consecutive_perm_eq_of_vertices_eq
      G.datum H.datum r
      (hvis (stepFromIndex r) hr₀)
      (hvis (stepToIndex r) hr₁)

theorem perm_eq_of_visible_consecutive_of_matching {d N : ℕ}
    (F G H : BaryFreudenthalDatumFacet d N)
    (hG : G.GeomEq F)
    (hH : H.GeomEq F)
    (homit : G.omitted = H.omitted)
    (hmatch : F.SameUnderlyingMatching G H hG hH)
    (r : Fin d)
    (hr₀ : stepFromIndex r ≠ G.omitted)
    (hr₁ : stepToIndex r ≠ G.omitted) :
    G.datum.perm (stepFromIndex r) = H.datum.perm (stepFromIndex r) ∧
      G.datum.perm (stepToIndex r) = H.datum.perm (stepToIndex r) := by
  classical
  have hvis :
      ∀ j : Fin (d + 1), j ≠ G.omitted →
        G.datum.vertex j = H.datum.vertex j :=
    F.visible_vertices_eq_on_nonomitted_of_sameUnderlyingMatching
      G H hG hH homit hmatch
  exact
    BaryFreudenthalDatumFacet.perm_eq_of_visible_consecutive
      G H homit hvis r hr₀ hr₁

theorem vertices_subset_simplex_vertices {d N : ℕ}
    (F : BaryFreudenthalDatumFacet d N) :
    F.vertices ⊆ F.simplex.vertices := by
  classical
  simpa [vertices, toChainFacet, simplex] using
    BaryFreudenthalFacet.vertices_subset_simplex_vertices F.toChainFacet

theorem vertices_subset_datum_vertices {d N : ℕ}
    (F : BaryFreudenthalDatumFacet d N) :
    F.vertices ⊆ F.datum.vertices := by
  classical
  intro x hx
  rw [BaryFreudenthalDatumFacet.mem_vertices_iff] at hx
  rcases hx with ⟨k, _hk_ne, hkx⟩
  rw [BaryFreudenthalDatum.mem_vertices_iff]
  exact ⟨k, hkx⟩

theorem dim_one_facet_singleton {N : ℕ}
    (F : BaryFreudenthalDatumFacet 1 N) :
    ∃ x : SimplexGrid 1 N, F.vertices = {x} := by
  classical
  have hcard_domain :
      ((Finset.univ.erase F.omitted) : Finset (Fin (1 + 1))).card = 1 := by
    rw [Finset.card_erase_of_mem]
    · simp
    · simp
  have hcard : F.vertices.card = 1 := by
    rw [BaryFreudenthalDatumFacet.vertices,
      BaryFreudenthalDatumFacet.toChainFacet, BaryFreudenthalFacet.vertices]
    rw [Finset.card_image_of_injective]
    · exact hcard_domain
    · intro a b hab
      exact F.simplex.vertex_injective hab
  exact Finset.card_eq_one.mp hcard

noncomputable instance instDecidableEq (d N : ℕ) :
    DecidableEq (BaryFreudenthalDatumFacet d N) :=
  Classical.decEq _

noncomputable def all (d N : ℕ) :
    Finset (BaryFreudenthalDatumFacet d N) := by
  classical
  exact ((Finset.univ : Finset (BaryFreudenthalDatum d N)).product
    (Finset.univ : Finset (Fin (d + 1)))).image fun p =>
      { datum := p.1, omitted := p.2 }

theorem mem_all {d N : ℕ} (F : BaryFreudenthalDatumFacet d N) :
    F ∈ all d N := by
  classical
  refine Finset.mem_image.mpr ⟨(F.datum, F.omitted), by simp, ?_⟩
  cases F
  rfl

noncomputable instance instFintype (d N : ℕ) :
    Fintype (BaryFreudenthalDatumFacet d N) :=
  ⟨all d N, mem_all⟩

end BaryFreudenthalDatumFacet

namespace DeletedChainMatching

theorem ext_of_pair_preserving {d : ℕ}
    {k l : Fin (d + 1)}
    {p q : Equiv.Perm (Fin (d + 1))}
    {φ ψ :
      {i : Fin (d + 1) // i ≠ k} →
        {j : Fin (d + 1) // j ≠ l}}
    (hφ :
      ∀ i j,
        i.1.val < j.1.val →
          ({p i.1, p j.1} : Finset (Fin (d + 1))) =
            ({q (φ i).1, q (φ j).1} : Finset (Fin (d + 1))))
    (hψ :
      ∀ i j,
        i.1.val < j.1.val →
          ({p i.1, p j.1} : Finset (Fin (d + 1))) =
            ({q (ψ i).1, q (ψ j).1} : Finset (Fin (d + 1))))
    (hφ_bij : Function.Bijective φ)
    (hψ_bij : Function.Bijective ψ)
    (hanchor : ∃ i, φ i = ψ i) :
    φ = ψ := by
  classical
  ext x
  rcases hanchor with ⟨a, ha⟩
  by_cases hxa : x = a
  · subst hxa
    exact congrArg (fun y => y.1.val) ha
  have hval_ne : x.1.val ≠ a.1.val := by
    intro hval
    apply hxa
    exact Subtype.ext (Fin.ext hval)
  have hφx_ne_anchor : q (φ x).1 ≠ q (φ a).1 := by
    intro hq
    have hφeq : φ x = φ a := Subtype.ext (q.injective hq)
    exact hxa (hφ_bij.1 hφeq)
  have hψx_ne_anchor : q (ψ x).1 ≠ q (φ a).1 := by
    intro hq
    have hq' : q (ψ x).1 = q (ψ a).1 := by
      simpa [← ha] using hq
    have hψeq : ψ x = ψ a := Subtype.ext (q.injective hq')
    exact hxa (hψ_bij.1 hψeq)
  rcases lt_trichotomy x.1.val a.1.val with hxlt | hxeq | hxgt
  · have hsets :
        ({q (φ x).1, q (φ a).1} : Finset (Fin (d + 1))) =
          ({q (ψ x).1, q (φ a).1} : Finset (Fin (d + 1))) := by
      have hraw := (hφ x a hxlt).symm.trans (hψ x a hxlt)
      simpa [← ha] using hraw
    have hmem : q (φ x).1 ∈
        ({q (ψ x).1, q (φ a).1} : Finset (Fin (d + 1))) := by
      have hleft : q (φ x).1 ∈
          ({q (φ x).1, q (φ a).1} : Finset (Fin (d + 1))) := by
        simp
      simpa [hsets] using hleft
    have hcases :
        q (φ x).1 = q (ψ x).1 ∨ q (φ x).1 = q (φ a).1 := by
      simpa using hmem
    rcases hcases with hmain | hbad
    · exact congrArg Fin.val (q.injective hmain)
    · exact False.elim (hφx_ne_anchor hbad)
  · exact False.elim (hval_ne hxeq)
  · have hsets :
        ({q (φ a).1, q (φ x).1} : Finset (Fin (d + 1))) =
          ({q (φ a).1, q (ψ x).1} : Finset (Fin (d + 1))) := by
      have hraw := (hφ a x hxgt).symm.trans (hψ a x hxgt)
      simpa [← ha] using hraw
    have hmem : q (φ x).1 ∈
        ({q (φ a).1, q (ψ x).1} : Finset (Fin (d + 1))) := by
      have hleft : q (φ x).1 ∈
          ({q (φ a).1, q (φ x).1} : Finset (Fin (d + 1))) := by
        simp
      simpa [hsets] using hleft
    have hcases :
        q (φ x).1 = q (φ a).1 ∨ q (φ x).1 = q (ψ x).1 := by
      simpa using hmem
    rcases hcases with hbad | hmain
    · exact False.elim (hφx_ne_anchor hbad)
    · exact congrArg Fin.val (q.injective hmain)

theorem ext_raw_of_pair_preserving {d : ℕ}
    {k : Fin (d + 1)}
    {p q : Equiv.Perm (Fin (d + 1))}
    {φ ψ : {i : Fin (d + 1) // i ≠ k} → Fin (d + 1)}
    (hφ :
      ∀ i j,
        i.1.val < j.1.val →
          ({p i.1, p j.1} : Finset (Fin (d + 1))) =
            ({q (φ i), q (φ j)} : Finset (Fin (d + 1))))
    (hψ :
      ∀ i j,
        i.1.val < j.1.val →
          ({p i.1, p j.1} : Finset (Fin (d + 1))) =
            ({q (ψ i), q (ψ j)} : Finset (Fin (d + 1))))
    (hφ_inj : Function.Injective φ)
    (hψ_inj : Function.Injective ψ)
    (hanchor : ∃ i, φ i = ψ i) :
    φ = ψ := by
  classical
  ext x
  rcases hanchor with ⟨a, ha⟩
  by_cases hxa : x = a
  · subst hxa
    exact congrArg Fin.val ha
  have hval_ne : x.1.val ≠ a.1.val := by
    intro hval
    apply hxa
    exact Subtype.ext (Fin.ext hval)
  have hφx_ne_anchor : q (φ x) ≠ q (φ a) := by
    intro hq
    exact hxa (hφ_inj (q.injective hq))
  have hψx_ne_anchor : q (ψ x) ≠ q (φ a) := by
    intro hq
    have hq' : q (ψ x) = q (ψ a) := by
      simpa [← ha] using hq
    exact hxa (hψ_inj (q.injective hq'))
  rcases lt_trichotomy x.1.val a.1.val with hxlt | hxeq | hxgt
  · have hsets :
        ({q (φ x), q (φ a)} : Finset (Fin (d + 1))) =
          ({q (ψ x), q (φ a)} : Finset (Fin (d + 1))) := by
      have hraw := (hφ x a hxlt).symm.trans (hψ x a hxlt)
      simpa [← ha] using hraw
    have hmem : q (φ x) ∈
        ({q (ψ x), q (φ a)} : Finset (Fin (d + 1))) := by
      have hleft : q (φ x) ∈
          ({q (φ x), q (φ a)} : Finset (Fin (d + 1))) := by
        simp
      simpa [hsets] using hleft
    have hcases :
        q (φ x) = q (ψ x) ∨ q (φ x) = q (φ a) := by
      simpa using hmem
    rcases hcases with hmain | hbad
    · exact congrArg Fin.val (q.injective hmain)
    · exact False.elim (hφx_ne_anchor hbad)
  · exact False.elim (hval_ne hxeq)
  · have hsets :
        ({q (φ a), q (φ x)} : Finset (Fin (d + 1))) =
          ({q (φ a), q (ψ x)} : Finset (Fin (d + 1))) := by
      have hraw := (hφ a x hxgt).symm.trans (hψ a x hxgt)
      simpa [← ha] using hraw
    have hmem : q (φ x) ∈
        ({q (φ a), q (ψ x)} : Finset (Fin (d + 1))) := by
      have hleft : q (φ x) ∈
          ({q (φ a), q (φ x)} : Finset (Fin (d + 1))) := by
        simp
      simpa [hsets] using hleft
    have hcases :
        q (φ x) = q (φ a) ∨ q (φ x) = q (ψ x) := by
      simpa using hmem
    rcases hcases with hbad | hmain
    · exact False.elim (hφx_ne_anchor hbad)
    · exact congrArg Fin.val (q.injective hmain)

end DeletedChainMatching

/-- Geometric barycentric facets, represented by their vertex-set key. -/
abbrev BaryFreudenthalGeomFacet (d N : ℕ) :=
  {K : Finset (SimplexGrid d N) //
    ∃ F : BaryFreudenthalDatumFacet d N, F.vertices = K}

namespace BaryFreudenthalDatumFacet

noncomputable def toGeomFacet {d N : ℕ}
    (F : BaryFreudenthalDatumFacet d N) :
    BaryFreudenthalGeomFacet d N :=
  ⟨F.vertices, ⟨F, rfl⟩⟩

theorem toGeomFacet_eq_iff {d N : ℕ}
    (F G : BaryFreudenthalDatumFacet d N) :
    F.toGeomFacet = G.toGeomFacet ↔ F.GeomEq G := by
  classical
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact h

end BaryFreudenthalDatumFacet

namespace BaryFreudenthalGeomFacet

noncomputable instance instDecidableEq (d N : ℕ) :
    DecidableEq (BaryFreudenthalGeomFacet d N) :=
  inferInstance

noncomputable instance instFintype (d N : ℕ) :
    Fintype (BaryFreudenthalGeomFacet d N) :=
  inferInstance

end BaryFreudenthalGeomFacet

noncomputable def allBaryFreudenthalDatumFacets (d N : ℕ) :
    Finset (BaryFreudenthalDatumFacet d N) :=
  Finset.univ

noncomputable def allBaryFreudenthalGeomFacets (d N : ℕ) :
    Finset (BaryFreudenthalGeomFacet d N) :=
  (allBaryFreudenthalDatumFacets d N).image
    BaryFreudenthalDatumFacet.toGeomFacet

theorem mem_allBaryFreudenthalGeomFacets_iff {d N : ℕ}
    (K : BaryFreudenthalGeomFacet d N) :
    K ∈ allBaryFreudenthalGeomFacets d N
      ↔
    ∃ F : BaryFreudenthalDatumFacet d N, F.toGeomFacet = K := by
  classical
  simp [allBaryFreudenthalGeomFacets, allBaryFreudenthalDatumFacets]

namespace BaryFreudenthalDatum

noncomputable def geomFacets {d N : ℕ}
    (D : BaryFreudenthalDatum d N) :
    Finset (BaryFreudenthalGeomFacet d N) :=
  Finset.univ.image fun k : Fin (d + 1) =>
    (BaryFreudenthalDatumFacet.mk D k).toGeomFacet

theorem mem_geomFacets_iff {d N : ℕ}
    (D : BaryFreudenthalDatum d N)
    (K : BaryFreudenthalGeomFacet d N) :
    K ∈ D.geomFacets ↔
      ∃ k : Fin (d + 1),
        (BaryFreudenthalDatumFacet.mk D k).toGeomFacet = K := by
  classical
  simp [geomFacets]

theorem toGeomFacet_injective {d N : ℕ}
    (D : BaryFreudenthalDatum d N) :
    Function.Injective fun k : Fin (d + 1) =>
      (BaryFreudenthalDatumFacet.mk D k).toGeomFacet := by
  classical
  intro k l h
  have hverts :
      (BaryFreudenthalFacet.mk D.toSimplex k).vertices =
        (BaryFreudenthalFacet.mk D.toSimplex l).vertices := by
    have hval := congrArg Subtype.val h
    simpa [BaryFreudenthalDatumFacet.toGeomFacet,
      BaryFreudenthalDatumFacet.vertices,
      BaryFreudenthalDatumFacet.toChainFacet,
      BaryFreudenthalDatumFacet.simplex] using hval
  exact (BaryFreudenthalSimplex.deletionFacet_vertices_eq_iff
    D.toSimplex k l).mp hverts

theorem geomFacets_card {d N : ℕ}
    (D : BaryFreudenthalDatum d N) :
    D.geomFacets.card = Fintype.card (Fin (d + 1)) := by
  classical
  rw [geomFacets]
  simpa using
    Finset.card_image_of_injective
      (Finset.univ : Finset (Fin (d + 1)))
      (BaryFreudenthalDatum.toGeomFacet_injective D)

theorem geomFacet_vertices_subset {d N : ℕ}
    {D : BaryFreudenthalDatum d N}
    {K : BaryFreudenthalGeomFacet d N}
    (hK : K ∈ D.geomFacets) :
    (K : Finset (SimplexGrid d N)) ⊆ D.toSimplex.vertices := by
  classical
  rcases (BaryFreudenthalDatum.mem_geomFacets_iff D K).mp hK with ⟨k, hk⟩
  intro x hx
  have hval := congrArg Subtype.val hk
  change (BaryFreudenthalDatumFacet.mk D k).vertices =
    (K : Finset (SimplexGrid d N)) at hval
  have hxFacet : x ∈ (BaryFreudenthalDatumFacet.mk D k).vertices := by
    simpa [hval] using hx
  exact (BaryFreudenthalDatumFacet.mk D k).vertices_subset_simplex_vertices hxFacet

end BaryFreudenthalDatum

namespace BaryFreudenthalGeomFacet

noncomputable def incidentData {d N : ℕ}
    (K : BaryFreudenthalGeomFacet d N) :
    Finset (BaryFreudenthalDatum d N) :=
  (BaryFreudenthalDatum.all d N).filter fun D =>
    ∃ k : Fin (d + 1),
      (BaryFreudenthalDatumFacet.mk D k).toGeomFacet = K

theorem mem_incidentData_iff {d N : ℕ}
    (K : BaryFreudenthalGeomFacet d N)
    (D : BaryFreudenthalDatum d N) :
    D ∈ K.incidentData ↔
      ∃ k : Fin (d + 1),
        (BaryFreudenthalDatumFacet.mk D k).toGeomFacet = K := by
  classical
  simp [incidentData, BaryFreudenthalDatum.mem_all]

theorem incident_iff_geomFacet {d N : ℕ}
    (K : BaryFreudenthalGeomFacet d N)
    (D : BaryFreudenthalDatum d N) :
    D ∈ K.incidentData ↔ K ∈ D.geomFacets := by
  classical
  rw [mem_incidentData_iff, BaryFreudenthalDatum.mem_geomFacets_iff]

theorem incidentData_nonempty {d N : ℕ}
    (K : BaryFreudenthalGeomFacet d N) :
    K.incidentData.Nonempty := by
  classical
  rcases K.2 with ⟨F, hF⟩
  refine ⟨F.datum, ?_⟩
  rw [mem_incidentData_iff]
  refine ⟨F.omitted, ?_⟩
  apply Subtype.ext
  simpa [BaryFreudenthalDatumFacet.toGeomFacet] using hF

theorem one_le_incidentData_card {d N : ℕ}
    (K : BaryFreudenthalGeomFacet d N) :
    1 ≤ K.incidentData.card := by
  have hpos : 0 < K.incidentData.card := by
    rw [Finset.card_pos]
    exact incidentData_nonempty K
  omega

/--
For barycentric geometric facets, boundary is defined geometrically: a facet is
on the boundary exactly when it has a single incident generated datum.
-/
def boundary {d N : ℕ}
    (K : BaryFreudenthalGeomFacet d N) : Prop :=
  K.incidentData.card = 1

theorem boundary_incident_card {d N : ℕ}
    (K : BaryFreudenthalGeomFacet d N)
    (h : K.boundary) :
    K.incidentData.card = 1 :=
  h

end BaryFreudenthalGeomFacet

def BarycentricFreudenthalIncidenceHypothesis (d N : ℕ) : Prop :=
  ∀ K : BaryFreudenthalGeomFacet d N, K.incidentData.card ≤ 2

/-
This is the remaining geometric incidence theorem for the barycentric
Freudenthal complex. It should eventually be proved from alternate-incidence
orientation uniqueness. For now we keep it as an explicit hypothesis so the
Sperner pipeline can be completed conditionally.
-/

namespace BaryFreudenthalGeomFacet

theorem incident_card_eq_one_or_two_of_incidence {d N : ℕ}
    (hinc : BarycentricFreudenthalIncidenceHypothesis d N)
    (K : BaryFreudenthalGeomFacet d N) :
    K.incidentData.card = 1 ∨ K.incidentData.card = 2 := by
  have hge := K.one_le_incidentData_card
  have hle := hinc K
  omega

theorem interior_incident_card_of_incidence {d N : ℕ}
    (hinc : BarycentricFreudenthalIncidenceHypothesis d N)
    (K : BaryFreudenthalGeomFacet d N)
    (h : ¬ K.boundary) :
    K.incidentData.card = 2 := by
  rcases K.incident_card_eq_one_or_two_of_incidence hinc with h1 | h2
  · exact False.elim (h h1)
  · exact h2

end BaryFreudenthalGeomFacet

namespace BaryFreudenthalDatumFacet

end BaryFreudenthalDatumFacet

/-- Colourings for the barycentric simplex grid. -/
structure Coloring (d N : ℕ) where
  color : SimplexGrid d N → Label d

def IsFullyColored {d N : ℕ}
    (C : Coloring d N) (σ : BaryFreudenthalSimplex d N) : Prop :=
  EconLib.Sperner.FullyLabeled C.color σ.vertices

namespace BaryFreudenthalSimplex

/-- The label of the `k`th vertex of an explicit-chain barycentric simplex. -/
def labelAt {d N : ℕ} (C : Coloring d N)
    (σ : BaryFreudenthalSimplex d N)
    (k : Fin (d + 1)) : Label d :=
  C.color (σ.vertex k)

/--
Omitted vertex indices whose deletion facet contains every label except
`missing`.
-/
noncomputable def relevantOmittedIndices {d N : ℕ}
    (C : Coloring d N)
    (σ : BaryFreudenthalSimplex d N)
    (missing : Label d) : Finset (Fin (d + 1)) := by
  classical
  exact Finset.univ.filter fun k =>
    EconLib.Sperner.AlmostFullyLabeled
      C.color missing
      ((BaryFreudenthalFacet.mk σ k).vertices)

theorem mem_relevantOmittedIndices_iff {d N : ℕ}
    (C : Coloring d N)
    (σ : BaryFreudenthalSimplex d N)
    (missing : Label d)
    (k : Fin (d + 1)) :
    k ∈ σ.relevantOmittedIndices C missing
      ↔
    EconLib.Sperner.AlmostFullyLabeled
      C.color missing
      ((BaryFreudenthalFacet.mk σ k).vertices) := by
  classical
  simp [relevantOmittedIndices]

theorem isFullyColored_iff_labelAt_surjective {d N : ℕ}
    (C : Coloring d N) (σ : BaryFreudenthalSimplex d N) :
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
    (σ : BaryFreudenthalSimplex d N)
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
    rw [BaryFreudenthalSimplex.mem_relevantOmittedIndices_iff,
      LocalDeletionParity.mem_relevantOmissions_iff]
    constructor
    · intro h a ha
      have ha_mem := h a ha
      rcases (Sperner.mem_labelsOn_iff C.color
          ((BaryFreudenthalFacet.mk σ k).vertices) a).mp ha_mem with
        ⟨v, hv, hcolor⟩
      rcases (BaryFreudenthalFacet.mem_vertices_iff
          (BaryFreudenthalFacet.mk σ k) v).mp hv with
        ⟨i, hik, hiv⟩
      refine ⟨i, hik, ?_⟩
      dsimp [f]
      rw [hiv]
      exact hcolor
    · intro h a ha
      rcases h a ha with ⟨i, hik, hfi⟩
      apply (Sperner.mem_labelsOn_iff C.color
        ((BaryFreudenthalFacet.mk σ k).vertices) a).mpr
      refine ⟨σ.vertex i, ?_, hfi⟩
      exact (BaryFreudenthalFacet.mem_vertices_iff
        (BaryFreudenthalFacet.mk σ k) (σ.vertex i)).mpr
        ⟨i, hik, rfl⟩
  rw [hset]
  rw [LocalDeletionParity.odd_relevant_omissions_iff_surjective]
  exact (isFullyColored_iff_labelAt_surjective C σ).symm

theorem local_parity_facets {d N : ℕ}
    (C : Coloring d N)
    (σ : BaryFreudenthalSimplex d N)
    (missing : Label d) :
    Odd
      (((by
          classical
          exact Finset.univ.filter fun k : Fin (d + 1) =>
            EconLib.Sperner.AlmostFullyLabeled
              C.color missing
              ((BaryFreudenthalFacet.mk σ k).vertices)) :
          Finset (Fin (d + 1))).card)
      ↔
    IsFullyColored C σ := by
  classical
  simpa [BaryFreudenthalSimplex.relevantOmittedIndices]
    using σ.local_parity C missing

end BaryFreudenthalSimplex

namespace BaryFreudenthalDatum

noncomputable def relevantGeomFacets {d N : ℕ}
    (C : Coloring d N)
    (missing : Label d)
    (D : BaryFreudenthalDatum d N) :
    Finset (BaryFreudenthalGeomFacet d N) := by
  classical
  exact D.geomFacets.filter fun K =>
    EconLib.Sperner.AlmostFullyLabeled C.color missing
      (K : Finset (SimplexGrid d N))

theorem relevantGeomFacets_card_eq_relevantOmittedIndices {d N : ℕ}
    (C : Coloring d N)
    (missing : Label d)
    (D : BaryFreudenthalDatum d N) :
    (D.relevantGeomFacets C missing).card
      =
    ((D.toSimplex.relevantOmittedIndices C missing).card) := by
  classical
  let toGeom : Fin (d + 1) → BaryFreudenthalGeomFacet d N :=
    fun k => (BaryFreudenthalDatumFacet.mk D k).toGeomFacet
  have hset :
      D.relevantGeomFacets C missing
        =
      (D.toSimplex.relevantOmittedIndices C missing).image toGeom := by
    ext K
    constructor
    · intro hK
      simp [relevantGeomFacets] at hK
      rcases hK with ⟨hKgeom, hrel⟩
      rcases (BaryFreudenthalDatum.mem_geomFacets_iff D K).mp hKgeom with
        ⟨k, hk⟩
      refine Finset.mem_image.mpr ⟨k, ?_, hk⟩
      rw [BaryFreudenthalSimplex.mem_relevantOmittedIndices_iff]
      have hval := congrArg Subtype.val hk
      change (BaryFreudenthalDatumFacet.mk D k).vertices =
        (K : Finset (SimplexGrid d N)) at hval
      have hrel' :
          EconLib.Sperner.AlmostFullyLabeled C.color missing
            (BaryFreudenthalDatumFacet.mk D k).vertices := by
        rw [hval]
        exact hrel
      simpa [BaryFreudenthalDatumFacet.vertices,
        BaryFreudenthalDatumFacet.toChainFacet,
        BaryFreudenthalDatumFacet.simplex] using hrel'
    · intro hK
      rcases Finset.mem_image.mp hK with ⟨k, hkrel, hk⟩
      simp [relevantGeomFacets]
      constructor
      · exact (BaryFreudenthalDatum.mem_geomFacets_iff D K).mpr ⟨k, hk⟩
      · rw [BaryFreudenthalSimplex.mem_relevantOmittedIndices_iff] at hkrel
        have hval := congrArg Subtype.val hk
        change (BaryFreudenthalDatumFacet.mk D k).vertices =
          (K : Finset (SimplexGrid d N)) at hval
        change EconLib.Sperner.AlmostFullyLabeled C.color missing
          (K : Finset (SimplexGrid d N))
        have hkrel' :
            EconLib.Sperner.AlmostFullyLabeled C.color missing
              (BaryFreudenthalDatumFacet.mk D k).vertices := by
          simpa [BaryFreudenthalDatumFacet.vertices,
            BaryFreudenthalDatumFacet.toChainFacet,
            BaryFreudenthalDatumFacet.simplex] using hkrel
        rw [← hval]
        exact hkrel'
  rw [hset]
  simpa [toGeom] using
    Finset.card_image_of_injective
      (D.toSimplex.relevantOmittedIndices C missing)
      (BaryFreudenthalDatum.toGeomFacet_injective D)

theorem local_parity_for_geomFacets {d N : ℕ}
    (C : Coloring d N)
    (missing : Label d)
    (D : BaryFreudenthalDatum d N) :
    Odd (D.relevantGeomFacets C missing).card
      ↔
    IsFullyColored C D.toSimplex := by
  classical
  rw [BaryFreudenthalDatum.relevantGeomFacets_card_eq_relevantOmittedIndices]
  exact D.toSimplex.local_parity C missing

end BaryFreudenthalDatum

noncomputable def barycentricFreudenthalTriangulationCertificate {d N : ℕ}
    (hinc : BarycentricFreudenthalIncidenceHypothesis d N) :
    Sperner.SpernerTriangulationCertificate
      (SimplexGrid d N)
      (BaryFreudenthalDatum d N)
      (BaryFreudenthalGeomFacet d N) :=
  { fintypeCell := inferInstance
    fintypeFacet := inferInstance
    decCell := inferInstance
    decFacet := inferInstance
    verticesOfCell := fun D => D.toSimplex.vertices
    verticesOfFacet := fun K => K.1
    facetsOfCell := fun D => D.geomFacets
    incidentCells := fun K => K.incidentData
    incident_iff := by
      intro D K
      exact BaryFreudenthalGeomFacet.incident_iff_geomFacet K D
    facet_vertices_subset := by
      intro D K hK
      exact BaryFreudenthalDatum.geomFacet_vertices_subset hK
    boundaryFacet := fun K => K.boundary
    boundary_incident_card := by
      intro K hK
      exact BaryFreudenthalGeomFacet.boundary_incident_card K hK
    interior_incident_card := by
      intro K hK
      exact BaryFreudenthalGeomFacet.interior_incident_card_of_incidence
        hinc K hK }

theorem BaryFreudenthalDatum.local_parity_for_barycentric_certificate {d N : ℕ}
    (hinc : BarycentricFreudenthalIncidenceHypothesis d N)
    (C : Coloring d N)
    (missing : Label d)
    (D : BaryFreudenthalDatum d N) :
    Odd
      (((barycentricFreudenthalTriangulationCertificate hinc).relevantFacetsOfCell
        C.color missing D).card)
      ↔
    IsFullyColored C D.toSimplex := by
  classical
  simpa [barycentricFreudenthalTriangulationCertificate,
    Sperner.SpernerTriangulationCertificate.relevantFacetsOfCell,
    Sperner.SpernerTriangulationCertificate.relevantFacet,
    BaryFreudenthalDatum.relevantGeomFacets] using
    D.local_parity_for_geomFacets C missing

noncomputable def BarycentricBoundaryRelevantFacets {d N : ℕ}
    (C : Coloring d N)
    (missing : Label d) :
    Finset (BaryFreudenthalGeomFacet d N) := by
  classical
  exact (Finset.univ : Finset (BaryFreudenthalGeomFacet d N)).filter fun K =>
    K.boundary ∧
      EconLib.Sperner.AlmostFullyLabeled C.color missing
        (K : Finset (SimplexGrid d N))

theorem barycentric_freudenthal_sperner_of_boundary_odd_of_incidence {d N : ℕ}
    (hinc : BarycentricFreudenthalIncidenceHypothesis d N)
    (C : Coloring d N)
    (missing : Label d)
    (boundary_odd :
      Odd (BarycentricBoundaryRelevantFacets C missing).card) :
    ∃ D : BaryFreudenthalDatum d N, IsFullyColored C D.toSimplex := by
  classical
  let T := barycentricFreudenthalTriangulationCertificate hinc
  have hboundary :
      Odd (T.boundaryRelevantFacets C.color missing).card := by
    simpa [T, BarycentricBoundaryRelevantFacets,
      barycentricFreudenthalTriangulationCertificate,
      Sperner.SpernerTriangulationCertificate.boundaryRelevantFacets,
      Sperner.SpernerTriangulationCertificate.relevantFacet] using boundary_odd
  have h :
      ∃ D : BaryFreudenthalDatum d N,
        Sperner.FullyLabeled C.color (T.verticesOfCell D) :=
    T.abstract_sperner C.color missing hboundary
      (BaryFreudenthalDatum.local_parity_for_barycentric_certificate
        hinc C missing)
  simpa [T, barycentricFreudenthalTriangulationCertificate, IsFullyColored]
    using h


end BarycentricFreudenthal

end SpernerFreudenthal
end EconLib
