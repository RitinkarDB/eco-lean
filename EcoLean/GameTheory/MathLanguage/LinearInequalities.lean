import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Theorems of the alternative: Gordan's theorem

Finite-dimensional theorems of the alternative, developed from the geometric Hahn–Banach separation
theorem. These are the linear-programming-duality foundation for game theory (the minimax theorem and
Pearce's lemma are corollaries).

Given a finite family of vectors `g i : κ → ℝ` indexed by a finite `ι` (a payoff/gain matrix):

* `exists_separating_distribution` — if no convex combination of the `g i` is strictly positive in
  every coordinate, then there is a probability distribution `y` on `κ` with `∑ k, y k * g i k ≤ 0`
  for every `i`. This is the substantive (separating-hyperplane) half of Gordan's theorem.
* `gordan` — **Gordan's theorem**: at least one of the two alternatives holds.
* `gordan_not_both` — the two alternatives are mutually exclusive (so exactly one holds).

The convex set of mixed gain vectors misses the open positive orthant exactly when no mixture is
everywhere-positive; a separating functional has a nonnegative normal, which (normalized) is the
distribution `y`.
-/

namespace EcoLean.LinearInequalities

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The separating-distribution half of Gordan's theorem. If no convex combination of the vectors
`g i` is strictly positive in every coordinate, there is a probability distribution `y` over `κ` with
`∑ k, y k * g i k ≤ 0` for all `i`. -/
theorem exists_separating_distribution [Nonempty ι] [Nonempty κ] (g : ι → κ → ℝ)
    (hno : ¬ ∃ x : ι → ℝ, x ∈ stdSimplex ℝ ι ∧ ∀ k, 0 < ∑ i, x i * g i k) :
    ∃ y : κ → ℝ, y ∈ stdSimplex ℝ κ ∧ ∀ i, (∑ k, y k * g i k) ≤ 0 := by
  classical
  set S : Set (κ → ℝ) := (fun x : ι → ℝ => fun k => ∑ i, x i * g i k) '' stdSimplex ℝ ι with hS
  set P : Set (κ → ℝ) := {v | ∀ k, 0 < v k} with hP
  have hPopen : IsOpen P := by
    rw [hP, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun k => isOpen_Ioi.preimage (continuous_apply k)
  have hPconv : Convex ℝ P := by
    intro v hv v' hv' p q hp hq hpq k
    show 0 < (p • v + q • v') k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : 0 ≤ p * v k := mul_nonneg hp (hv k).le
    have h2 : 0 ≤ q * v' k := mul_nonneg hq (hv' k).le
    rcases eq_or_lt_of_le hp with hp0 | hp0
    · have hq1 : q = 1 := by linarith
      have : 0 < q * v' k := by rw [hq1, one_mul]; exact hv' k
      linarith
    · have : 0 < p * v k := mul_pos hp0 (hv k)
      linarith
  have hSconv : Convex ℝ S := by
    rw [hS]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ p q hp hq hpq
    refine ⟨fun i => p * x i + q * x' i, convex_stdSimplex ℝ _ hx hx' hp hq hpq, ?_⟩
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hdisj : Disjoint P S := by
    rw [Set.disjoint_left]
    rintro v hvP ⟨x, hx, rfl⟩
    exact hno ⟨x, hx, fun k => hvP k⟩
  obtain ⟨f, u, hfP, hfS⟩ := geometric_hahn_banach_open hPconv hPopen hSconv hdisj
  have h1P : (fun _ => (1 : ℝ)) ∈ P := fun _ => one_pos
  -- `f` is `≤ 0` on each positive basis direction (Archimedean cone argument).
  have hfsingle_nonpos : ∀ k, f (Pi.single k (1 : ℝ)) ≤ 0 := by
    intro k
    set e : κ → ℝ := Pi.single k 1 with he_def
    by_contra hpos
    push_neg at hpos
    obtain ⟨n, hn⟩ := exists_nat_gt ((u - f (fun _ => (1 : ℝ))) / f e)
    have hwP : ((n : ℝ) • e + (fun _ : κ => (1 : ℝ))) ∈ P := by
      intro l
      have hb : (0 : ℝ) ≤ e l := by rw [he_def, Pi.single_apply]; split_ifs <;> norm_num
      show 0 < ((n : ℝ) • e + (fun _ : κ => (1 : ℝ))) l
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : (0 : ℝ) ≤ (n : ℝ) * e l := mul_nonneg (Nat.cast_nonneg n) hb
      linarith
    have hfw : f ((n : ℝ) • e + (fun _ : κ => (1 : ℝ))) = (n : ℝ) * f e + f (fun _ => 1) := by
      rw [map_add, map_smul, smul_eq_mul]
    have hlt := hfP _ hwP
    rw [hfw] at hlt
    rw [div_lt_iff₀ hpos] at hn
    linarith
  -- Hence `f` is `≤ 0` on the all-ones vector.
  have hf1nonpos : f (fun _ : κ => (1 : ℝ)) ≤ 0 := by
    have he : (fun _ : κ => (1 : ℝ)) = ∑ k, Pi.single k 1 := (Finset.univ_sum_single _).symm
    rw [he, map_sum]
    exact Finset.sum_nonpos fun k _ => hfsingle_nonpos k
  -- The separation constant is nonnegative (the orthant accumulates at `0`).
  have hu_nonneg : 0 ≤ u := by
    by_contra hu
    push_neg at hu
    rcases eq_or_lt_of_le hf1nonpos with h1 | h1
    · have h2 := hfP (fun _ => 1) h1P
      rw [h1] at h2; linarith
    · set ε := u / f (fun _ => (1 : ℝ)) with hε
      have hεP : (ε • (fun _ : κ => (1 : ℝ))) ∈ P := by
        intro l
        show 0 < (ε • (fun _ : κ => (1 : ℝ))) l
        simp only [Pi.smul_apply, smul_eq_mul, mul_one]
        exact div_pos_of_neg_of_neg hu h1
      have hfε : f (ε • (fun _ : κ => (1 : ℝ))) = ε * f (fun _ => 1) := by
        rw [map_smul, smul_eq_mul]
      have hlt := hfP _ hεP
      rw [hfε, hε, div_mul_cancel₀ _ (ne_of_lt h1)] at hlt
      exact lt_irrefl u hlt
  -- The nonnegative normal `μ` and the functional representation `∑ μ k * w k = - f w`.
  set μ : κ → ℝ := fun k => - f (Pi.single k 1) with hμdef
  have hsingle_smul : ∀ (k : κ) (c : ℝ), Pi.single k c = c • (Pi.single k 1 : κ → ℝ) := by
    intro k c; funext l
    rw [Pi.smul_apply, Pi.single_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  have hfsingle' : ∀ (k : κ) (c : ℝ), f (Pi.single k c) = c * f (Pi.single k 1) := by
    intro k c; rw [hsingle_smul k c, map_smul, smul_eq_mul]
  have key : ∀ w : κ → ℝ, ∑ k, μ k * w k = - f w := by
    intro w
    have hexp : f w = ∑ k, w k * f (Pi.single k 1) := by
      have h1 : f w = f (∑ k, Pi.single k (w k)) := by rw [Finset.univ_sum_single]
      rw [h1, map_sum]
      exact Finset.sum_congr rfl fun k _ => hfsingle' k (w k)
    rw [hexp, eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun k _ => by simp only [hμdef]; ring
  have hμnn : ∀ k, 0 ≤ μ k := fun k => by
    show (0 : ℝ) ≤ -f (Pi.single k 1); exact neg_nonneg.mpr (hfsingle_nonpos k)
  -- The normal is nonzero (else `f = 0` contradicts the strict separation), so it has positive mass.
  have hsumpos : 0 < ∑ k, μ k := by
    rcases lt_or_eq_of_le (Finset.sum_nonneg fun k _ => hμnn k) with h | h
    · exact h
    · exfalso
      have hall : ∀ k, μ k = 0 := fun k =>
        (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hμnn k).mp h.symm k (Finset.mem_univ k)
      have hf0 : ∀ w : κ → ℝ, f w = 0 := by
        intro w
        have hk := key w
        simp only [hall, zero_mul, Finset.sum_const_zero] at hk
        linarith
      obtain ⟨x0, hx0⟩ : (stdSimplex ℝ ι).Nonempty :=
        ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary ι)⟩
      have hp := hfP _ h1P
      have hs := hfS _ (⟨x0, hx0, rfl⟩ : (fun k => ∑ i, x0 i * g i k) ∈ S)
      rw [hf0] at hp hs; linarith
  -- Each row `g i` is in `S`, so `f (g i) ≥ u ≥ 0`.
  have hgS : ∀ i, g i ∈ S := by
    intro i
    rw [hS]
    refine ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, ?_⟩
    funext k
    show ∑ j, (Pi.single i 1 : ι → ℝ) j * g j k = g i k
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul])
      (fun hh => absurd (Finset.mem_univ i) hh), Pi.single_eq_same, one_mul]
  -- Assemble the normalized distribution.
  refine ⟨fun k => μ k / (∑ l, μ l), ⟨fun k => div_nonneg (hμnn k) hsumpos.le, ?_⟩, fun i => ?_⟩
  · simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, mul_inv_cancel₀ (ne_of_gt hsumpos)]
  · have hμgi : ∑ k, μ k * g i k ≤ 0 := by
      rw [key (g i)]; linarith [le_trans hu_nonneg (hfS _ (hgS i))]
    have hre : ∑ k, μ k / (∑ l, μ l) * g i k = (∑ k, μ k * g i k) * (∑ l, μ l)⁻¹ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by rw [div_eq_mul_inv]; ring
    rw [hre]
    exact mul_nonpos_iff.2 (Or.inr ⟨hμgi, (inv_pos.mpr hsumpos).le⟩)

/-- **Gordan's theorem.** For any gain matrix `g`, at least one of the two alternatives holds: some
mixture of the rows is strictly positive everywhere, or some distribution over the columns makes every
row's expectation nonpositive. -/
theorem gordan [Nonempty ι] [Nonempty κ] (g : ι → κ → ℝ) :
    (∃ x : ι → ℝ, x ∈ stdSimplex ℝ ι ∧ ∀ k, 0 < ∑ i, x i * g i k) ∨
      (∃ y : κ → ℝ, y ∈ stdSimplex ℝ κ ∧ ∀ i, (∑ k, y k * g i k) ≤ 0) := by
  by_cases h : ∃ x : ι → ℝ, x ∈ stdSimplex ℝ ι ∧ ∀ k, 0 < ∑ i, x i * g i k
  · exact Or.inl h
  · exact Or.inr (exists_separating_distribution g h)

/-- The two Gordan alternatives are mutually exclusive: a mixture that is everywhere strictly positive
cannot coexist with a distribution that makes every row nonpositive. -/
theorem gordan_not_both (g : ι → κ → ℝ)
    (h1 : ∃ x : ι → ℝ, x ∈ stdSimplex ℝ ι ∧ ∀ k, 0 < ∑ i, x i * g i k)
    (h2 : ∃ y : κ → ℝ, y ∈ stdSimplex ℝ κ ∧ ∀ i, (∑ k, y k * g i k) ≤ 0) : False := by
  obtain ⟨x, ⟨hxnn, hxsum⟩, hxpos⟩ := h1
  obtain ⟨y, ⟨hynn, hysum⟩, hyle⟩ := h2
  have hswap : ∑ k, y k * (∑ i, x i * g i k) = ∑ i, x i * (∑ k, y k * g i k) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  -- The left side is positive (a distribution against everywhere-positive values)…
  have hpos : 0 < ∑ k, y k * (∑ i, x i * g i k) := by
    obtain ⟨k0, hk0⟩ : ∃ k0, 0 < y k0 := by
      by_contra hc
      push_neg at hc
      have : ∑ k, y k ≤ 0 := Finset.sum_nonpos fun k _ => hc k
      rw [hysum] at this; linarith
    refine Finset.sum_pos' (fun k _ => mul_nonneg (hynn k) (hxpos k).le) ?_
    exact ⟨k0, Finset.mem_univ k0, mul_pos hk0 (hxpos k0)⟩
  -- …but the right side is nonpositive.
  have hnonpos : ∑ i, x i * (∑ k, y k * g i k) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_iff.2 (Or.inl ⟨hxnn i, hyle i⟩)
  rw [hswap] at hpos
  linarith

/-! ### The minimax theorem -/

/-- **The minimax theorem (von Neumann).** Every finite two-person zero-sum game with payoff matrix
`A` (rows `ι`, columns `κ`) has a value `v` and optimal mixed strategies: a row mixture `x`
guaranteeing at least `v` against every column, and a column mixture `y` holding the row player to at
most `v` against every row. The maximin row strategy exists by compactness, and Gordan's theorem
supplies the matching column strategy. -/
theorem minimax [Nonempty ι] [Nonempty κ] (A : ι → κ → ℝ) :
    ∃ (v : ℝ) (x : ι → ℝ) (y : κ → ℝ), x ∈ stdSimplex ℝ ι ∧ y ∈ stdSimplex ℝ κ ∧
      (∀ k, v ≤ ∑ i, x i * A i k) ∧ (∀ i, (∑ k, y k * A i k) ≤ v) := by
  classical
  -- the row player's guarantee value: the minimum expected payoff over columns
  set Φ : (ι → ℝ) → ℝ :=
    fun x => Finset.univ.inf' Finset.univ_nonempty (fun k => ∑ i, x i * A i k) with hΦ
  have hΦcont : Continuous Φ :=
    Continuous.finset_inf'_apply Finset.univ_nonempty
      (fun k _ => continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const)
  obtain ⟨x, hxmem, hxmax⟩ := (isCompact_stdSimplex ℝ ι).exists_isMaxOn
    ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary ι)⟩ hΦcont.continuousOn
  set v := Φ x with hv
  have hxguar : ∀ k, v ≤ ∑ i, x i * A i k := by
    intro k
    simp only [hv, hΦ]
    exact Finset.inf'_le _ (Finset.mem_univ k)
  -- no row mixture strictly beats `v` (else it would beat the maximizer `x`)
  have hno : ¬ ∃ x' : ι → ℝ, x' ∈ stdSimplex ℝ ι ∧ ∀ k, 0 < ∑ i, x' i * (A i k - v) := by
    rintro ⟨x', hx', hpos⟩
    have hgt : v < Φ x' := by
      simp only [hΦ]
      rw [Finset.lt_inf'_iff]
      intro k _
      show v < ∑ i, x' i * A i k
      have hsum : ∑ i, x' i * (A i k - v) = (∑ i, x' i * A i k) - v := by
        rw [show (∑ i, x' i * (A i k - v)) = ∑ i, (x' i * A i k - x' i * v) from
            Finset.sum_congr rfl fun i _ => by ring, Finset.sum_sub_distrib, ← Finset.sum_mul,
          hx'.2, one_mul]
      have hp := hpos k; rw [hsum] at hp; linarith
    have h1 : Φ x' ≤ Φ x := hxmax hx'
    rw [hv] at hgt
    linarith
  obtain ⟨y, hymem, hyle⟩ := exists_separating_distribution (fun i k => A i k - v) hno
  refine ⟨v, x, y, hxmem, hymem, hxguar, fun i => ?_⟩
  have hyi : ∑ k, y k * (A i k - v) ≤ 0 := hyle i
  have hsum : ∑ k, y k * (A i k - v) = (∑ k, y k * A i k) - v := by
    rw [show (∑ k, y k * (A i k - v)) = ∑ k, (y k * A i k - y k * v) from
        Finset.sum_congr rfl fun k _ => by ring, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hymem.2, one_mul]
  rw [hsum] at hyi; linarith

end EcoLean.LinearInequalities
