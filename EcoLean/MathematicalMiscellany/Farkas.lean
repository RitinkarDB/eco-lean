import EcoLean.MathematicalMiscellany.LinearInequalities
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Farkas's lemma (via Minkowski–Weyl)

Farkas's lemma — a vector `b` is a nonnegative combination of finitely many vectors `a i` iff every
halfspace containing all the `a i` contains `b`. The substantive ingredient is the **Minkowski–Weyl**
fact that a finitely-generated cone is closed, which Mathlib does not provide; we build it here from
conic Carathéodory (reduce to a linearly independent subfamily) and the closedness of the cone of a
linearly independent family.

This file is being developed incrementally. The current milestone is the foundation:

* `coneOf` — the conic hull (nonnegative combinations) of a finite family.
* `isClosed_coneOf_of_linearIndependent` — the cone of a *linearly independent* family is closed
  (the linear combination map is an injective, hence closed, embedding of the orthant).
-/

namespace EconLib.LinearInequalities

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The **conic hull** of a finite family `a` of vectors in `κ → ℝ`: the set of nonnegative
combinations `∑ i, x i • a i` with `x ≥ 0`. -/
def coneOf (a : ι → (κ → ℝ)) : Set (κ → ℝ) :=
  {b | ∃ x : ι → ℝ, (∀ i, 0 ≤ x i) ∧ ∑ i, x i • a i = b}

/-- The cone of a **linearly independent** family is closed: the linear-combination map is injective,
hence a closed embedding (finite dimensions), and the cone is the image of the closed orthant. -/
theorem isClosed_coneOf_of_linearIndependent {a : ι → (κ → ℝ)} (ha : LinearIndependent ℝ a) :
    IsClosed (coneOf a) := by
  classical
  set L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ) := Fintype.linearCombination ℝ a with hL
  have hLinj : Function.Injective L :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp ha
  have hemb := L.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hLinj)
  have horth : IsClosed {x : ι → ℝ | ∀ i, 0 ≤ x i} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have hcone : coneOf a = L '' {x : ι → ℝ | ∀ i, 0 ≤ x i} := by
    ext b
    simp only [coneOf, Set.mem_image, Set.mem_setOf_eq, hL, Fintype.linearCombination_apply]
  rw [hcone]
  exact hemb.isClosedMap _ horth

/-- The conic hull is convex. -/
theorem convex_coneOf (a : ι → (κ → ℝ)) : Convex ℝ (coneOf a) := by
  rintro _ ⟨x, hxnn, rfl⟩ _ ⟨x', hx'nn, rfl⟩ p q hp hq _
  refine ⟨fun i => p * x i + q * x' i,
    fun i => add_nonneg (mul_nonneg hp (hxnn i)) (mul_nonneg hq (hx'nn i)), ?_⟩
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    rw [add_smul, smul_smul, smul_smul]

/-- The conic hull is closed under nonnegative scaling. -/
theorem smul_mem_coneOf {a : ι → (κ → ℝ)} {b : κ → ℝ} (hb : b ∈ coneOf a) {t : ℝ} (ht : 0 ≤ t) :
    t • b ∈ coneOf a := by
  obtain ⟨x, hxnn, rfl⟩ := hb
  refine ⟨fun i => t * x i, fun i => mul_nonneg ht (hxnn i), ?_⟩
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]

theorem self_mem_coneOf [DecidableEq ι] (a : ι → (κ → ℝ)) (i : ι) : a i ∈ coneOf a := by
  refine ⟨Pi.single i 1, fun j => by rw [Pi.single_apply]; split_ifs <;> norm_num, ?_⟩
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
    (fun hh => absurd (Finset.mem_univ i) hh), Pi.single_eq_same, one_smul]

/-- **Farkas's lemma** (modulo closedness of the cone). For a family `a` whose conic hull is closed,
`b` is a nonnegative combination of the `a i` iff every `y` with `⟨a i, y⟩ ≥ 0` for all `i` also has
`⟨b, y⟩ ≥ 0`. The hard direction is a hyperplane separating `b` from the closed convex cone. -/
theorem farkas_of_isClosed {a : ι → (κ → ℝ)} (hclosed : IsClosed (coneOf a)) (b : κ → ℝ) :
    b ∈ coneOf a ↔ ∀ y : κ → ℝ, (∀ i, 0 ≤ ∑ k, a i k * y k) → 0 ≤ ∑ k, b k * y k := by
  classical
  constructor
  · rintro ⟨x, hxnn, rfl⟩ y hy
    have hfub : ∑ k, (∑ i, x i • a i) k * y k = ∑ i, x i * (∑ k, a i k * y k) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [hfub]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hxnn i) (hy i)
  · intro hy
    by_contra hb
    obtain ⟨f, u, hf, hub⟩ := geometric_hahn_banach_closed_point (convex_coneOf a) hclosed hb
    -- `u > 0` from `0 ∈ coneOf a`, hence `f b > 0`.
    have h0 : (0 : κ → ℝ) ∈ coneOf a := ⟨0, fun _ => le_refl 0, by simp⟩
    have hu0 : 0 < u := by have := hf 0 h0; simpa using this
    -- `f (a i) ≤ 0` (cone Archimedean argument).
    have hfa : ∀ i, f (a i) ≤ 0 := by
      intro i
      by_contra hpos
      push_neg at hpos
      obtain ⟨n, hn⟩ := exists_nat_gt (u / f (a i))
      have hmem : (n : ℝ) • a i ∈ coneOf a := smul_mem_coneOf (self_mem_coneOf a i) (Nat.cast_nonneg n)
      have hlt := hf _ hmem
      rw [map_smul, smul_eq_mul] at hlt
      rw [div_lt_iff₀ hpos] at hn
      linarith
    -- functional representation `f w = ∑ k, f(δ k) * w k`.
    have hsingle_smul : ∀ (k : κ) (c : ℝ), Pi.single k c = c • (Pi.single k 1 : κ → ℝ) := by
      intro k c; funext l
      rw [Pi.smul_apply, Pi.single_apply, Pi.single_apply, smul_eq_mul]
      split_ifs <;> simp
    have hfsingle : ∀ (k : κ) (c : ℝ), f (Pi.single k c) = c * f (Pi.single k 1) := by
      intro k c; rw [hsingle_smul k c, map_smul, smul_eq_mul]
    have key : ∀ w : κ → ℝ, ∑ k, w k * f (Pi.single k 1) = f w := by
      intro w
      have h1 : f w = f (∑ k, Pi.single k (w k)) := by rw [Finset.univ_sum_single]
      rw [h1, map_sum]
      exact (Finset.sum_congr rfl fun k _ => hfsingle k (w k)).symm
    -- The separating direction `y k = - f (δ k)`.
    refine absurd (hy (fun k => - f (Pi.single k 1)) (fun i => ?_)) (not_le.mpr ?_)
    · -- `0 ≤ ⟨a i, y⟩ = - f (a i)`
      have : ∑ k, a i k * (-f (Pi.single k 1)) = - f (a i) := by
        rw [← key (a i)]; rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [this]; linarith [hfa i]
    · -- `⟨b, y⟩ = - f b < 0`
      have : ∑ k, b k * (-f (Pi.single k 1)) = - f b := by
        rw [← key b]; rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [this]; linarith [hub, hu0]

/-! ### Conic Carathéodory and closedness of the cone -/

open Finset in
/-- One step of conic Carathéodory: if the support of a nonnegative representation is linearly
dependent, the representation can be replaced by one with strictly smaller support. -/
theorem exists_smaller_support {a : ι → (κ → ℝ)} {x : ι → ℝ} (hxnn : ∀ i, 0 ≤ x i)
    (hdep : ¬ LinearIndependent ℝ (fun i : (univ.filter (fun i => x i ≠ 0) : Finset ι) => a i)) :
    ∃ x' : ι → ℝ, (∀ i, 0 ≤ x' i) ∧ ∑ i, x' i • a i = ∑ i, x i • a i ∧
      (univ.filter (fun i => x' i ≠ 0)).card < (univ.filter (fun i => x i ≠ 0)).card := by
  classical
  set t : Finset ι := univ.filter (fun i => x i ≠ 0) with ht
  have hmemt : ∀ i, i ∈ t ↔ x i ≠ 0 := fun i => by simp [ht]
  obtain ⟨g, hg0, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hdep
  -- extend the dependence to all of `ι`, supported on `t`
  set c : ι → ℝ := fun i => if h : i ∈ t then g ⟨i, h⟩ else 0 with hc
  have hcsupp : ∀ i ∉ t, c i = 0 := fun i hi => by simp only [hc, dif_neg hi]
  have hcsum : ∑ i, c i • a i = 0 := by
    rw [← Finset.sum_subset (subset_univ t) (fun i _ hit => by rw [hcsupp i hit, zero_smul]), ← hg0,
      ← Finset.sum_attach t (fun i => c i • a i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hc, dif_pos i.2]
  have hcne : c i0.1 ≠ 0 := by simp only [hc, dif_pos i0.2]; exact hi0
  -- arrange that `c` has a positive entry (negate if necessary)
  obtain ⟨d, hdsum, hdsupp, hdpos⟩ :
      ∃ d : ι → ℝ, (∑ i, d i • a i = 0) ∧ (∀ i ∉ t, d i = 0) ∧ ∃ j ∈ t, 0 < d j := by
    by_cases hpos : ∃ j ∈ t, 0 < c j
    · exact ⟨c, hcsum, hcsupp, hpos⟩
    · push_neg at hpos
      refine ⟨-c, by simp [Finset.sum_neg_distrib, hcsum], fun i hi => by simp [hcsupp i hi], ?_⟩
      have hi0t : i0.1 ∈ t := i0.2
      have : c i0.1 < 0 := lt_of_le_of_ne (hpos i0.1 hi0t) hcne
      exact ⟨i0.1, hi0t, by simpa using this⟩
  -- the ratio set is nonempty; pick the minimizing index
  obtain ⟨j0, hj0t, hj0pos⟩ := hdpos
  set rs : Finset ι := t.filter (fun i => 0 < d i) with hrs
  have hrsne : rs.Nonempty := ⟨j0, by simp [hrs, hj0t, hj0pos]⟩
  obtain ⟨istar, histar, hmin⟩ := rs.exists_min_image (fun i => x i / d i) hrsne
  rw [hrs, Finset.mem_filter] at histar
  set r : ℝ := x istar / d istar with hr
  have hdistar : 0 < d istar := histar.2
  have hrnn : 0 ≤ r := div_nonneg (hxnn istar) hdistar.le
  refine ⟨fun i => x i - r * d i, fun i => ?_, ?_, ?_⟩
  · -- nonnegativity
    show 0 ≤ x i - r * d i
    rcases lt_trichotomy (d i) 0 with hdi | hdi | hdi
    · have : r * d i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hrnn hdi.le
      linarith [hxnn i]
    · rw [hdi, mul_zero, sub_zero]; exact hxnn i
    · have hit_t : i ∈ t := by by_contra h; exact hdi.ne' (hdsupp i h)
      have hit : i ∈ rs := by rw [hrs, Finset.mem_filter]; exact ⟨hit_t, hdi⟩
      have hle : r ≤ x i / d i := hmin i hit
      have hxle : r * d i ≤ x i := (le_div_iff₀ hdi).mp hle
      linarith
  · -- sum unchanged
    have heq : ∑ i, (x i - r * d i) • a i = ∑ i, x i • a i - r • ∑ i, d i • a i := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [sub_smul, smul_smul]
    rw [heq, hdsum, smul_zero, sub_zero]
  · -- strictly smaller support: `x' = x - r·d` vanishes at `istar` and is supported within `t`
    have hsub : (univ.filter (fun i => x i - r * d i ≠ 0)) ⊆ t := by
      intro i hi
      rw [Finset.mem_filter] at hi
      by_contra hit
      have hxi0 : x i = 0 := by by_contra h; exact hit ((hmemt i).mpr h)
      have hdi0 : d i = 0 := hdsupp i hit
      exact hi.2 (by rw [hxi0, hdi0, mul_zero, sub_zero])
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset hsub]
    refine ⟨istar, histar.1, ?_⟩
    rw [Finset.mem_filter, not_and]
    intro _
    rw [not_not, hr, div_mul_cancel₀ _ (ne_of_gt hdistar), sub_self]

/-- **Conic Carathéodory.** Every element of the cone is a nonnegative combination of a *linearly
independent* subfamily of the generators. -/
theorem exists_linearIndependent_subset_coneOf {a : ι → (κ → ℝ)} {b : κ → ℝ} (hb : b ∈ coneOf a) :
    ∃ t : Finset ι, LinearIndependent ℝ (fun i : t => a i) ∧ b ∈ coneOf (fun i : t => a i) := by
  classical
  obtain ⟨x, hxnn, rfl⟩ := hb
  suffices H : ∀ (n : ℕ) (x : ι → ℝ), (∀ i, 0 ≤ x i) →
      (Finset.univ.filter (fun i => x i ≠ 0)).card ≤ n →
      ∃ t : Finset ι, LinearIndependent ℝ (fun i : t => a i) ∧
        (∑ i, x i • a i) ∈ coneOf (fun i : t => a i) by
    exact H _ x hxnn le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro x hxnn hcard
    set t : Finset ι := Finset.univ.filter (fun i => x i ≠ 0) with ht
    by_cases hindep : LinearIndependent ℝ (fun i : t => a i)
    · refine ⟨t, hindep, fun i => x i.1, fun i => hxnn i.1, ?_⟩
      show ∑ i : ↥t, x i.1 • a i.1 = ∑ i, x i • a i
      rw [Finset.sum_coe_sort t (fun j => x j • a j)]
      exact Finset.sum_subset (Finset.subset_univ t) fun i _ hit => by
        have hxi : x i = 0 := by
          by_contra h; exact hit (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
        rw [hxi, zero_smul]
    · obtain ⟨x', hx'nn, hx'sum, hx'card⟩ := exists_smaller_support hxnn hindep
      obtain ⟨s, hs, hsmem⟩ := IH _ (lt_of_lt_of_le hx'card hcard) x' hx'nn le_rfl
      exact ⟨s, hs, by rw [← hx'sum]; exact hsmem⟩

/-- **Minkowski–Weyl:** a finitely-generated cone is closed. -/
theorem isClosed_coneOf {a : ι → (κ → ℝ)} : IsClosed (coneOf a) := by
  classical
  have hunion : coneOf a =
      ⋃ (t : Finset ι) (_ : LinearIndependent ℝ (fun i : t => a i)), coneOf (fun i : t => a i) := by
    ext b
    simp only [Set.mem_iUnion]
    constructor
    · intro hb
      obtain ⟨t, ht, hbt⟩ := exists_linearIndependent_subset_coneOf hb
      exact ⟨t, ht, hbt⟩
    · rintro ⟨t, _, x', hx'nn, rfl⟩
      refine ⟨fun i => if h : i ∈ t then x' ⟨i, h⟩ else 0, fun i => by
        by_cases h : i ∈ t <;> simp [h, hx'nn], ?_⟩
      show ∑ i, (if h : i ∈ t then x' ⟨i, h⟩ else 0) • a i = ∑ i : ↥t, x' i • a i.1
      rw [← Finset.sum_subset (Finset.subset_univ t)
        (fun i _ hit => by rw [dif_neg hit, zero_smul])]
      rw [← Finset.sum_coe_sort t (fun j => (if h : j ∈ t then x' ⟨j, h⟩ else 0) • a j)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hval : (if h : (↑i : ι) ∈ t then x' ⟨↑i, h⟩ else 0) = x' i := dif_pos i.2
      rw [hval]
  rw [hunion]
  exact isClosed_iUnion_of_finite fun t =>
    isClosed_iUnion_of_finite fun ht => isClosed_coneOf_of_linearIndependent ht

/-- **Farkas's lemma.** `b` is a nonnegative combination of the `a i` iff every `y` that is
nonnegative against all `a i` is also nonnegative against `b`. -/
theorem farkas {a : ι → (κ → ℝ)} (b : κ → ℝ) :
    b ∈ coneOf a ↔ ∀ y : κ → ℝ, (∀ i, 0 ≤ ∑ k, a i k * y k) → 0 ≤ ∑ k, b k * y k :=
  farkas_of_isClosed isClosed_coneOf b

/-- **Gordan's theorem of the alternative for the simplex, derived from Farkas.** If no mixed strategy
`x ∈ Δ(ι)` makes every column `k` strictly positive, then some distribution `y ∈ Δ(κ)` makes every
row `i` nonpositive. This re-derives `exists_separating_distribution` (whose original proof is a direct
open separating hyperplane) from the Farkas/Minkowski–Weyl machinery by *homogenizing*: the question
becomes whether the vector `(0, 1)` lies in the cone generated by the columns `(g · k, 1)` (indexed by
`κ`) together with the slack unit vectors `(eᵢ, 0)` (indexed by `ι`), inside `Option ι → ℝ` (`≅ ℝ^ι × ℝ`,
with `none` the homogenizing coordinate). -/
theorem exists_separating_distribution_via_farkas [Nonempty ι] [Nonempty κ] (g : ι → κ → ℝ)
    (hno : ¬ ∃ x : ι → ℝ, x ∈ stdSimplex ℝ ι ∧ ∀ k, 0 < ∑ i, x i * g i k) :
    ∃ y : κ → ℝ, y ∈ stdSimplex ℝ κ ∧ ∀ i, (∑ k, y k * g i k) ≤ 0 := by
  classical
  set gens : κ ⊕ ι → (Option ι → ℝ) :=
    Sum.elim (fun k o => o.elim 1 (fun i => g i k))
             (fun i o => o.elim 0 (fun i' => if i' = i then 1 else 0)) with hgens
  set bb : Option ι → ℝ := fun o => o.elim 1 (fun _ => 0) with hbb
  -- coordinate pairings of a test vector `z` against `bb` and the generators
  have hsb : ∀ z : Option ι → ℝ, ∑ o, bb o * z o = z none := by
    intro z; rw [Fintype.sum_option]; simp [hbb]
  have hsl : ∀ (k : κ) (z : Option ι → ℝ),
      ∑ o, gens (Sum.inl k) o * z o = z none + ∑ i, g i k * z (some i) := by
    intro k z; rw [Fintype.sum_option]; simp [hgens]
  have hsr : ∀ (i : ι) (z : Option ι → ℝ),
      ∑ o, gens (Sum.inr i) o * z o = z (some i) := by
    intro i z; rw [Fintype.sum_option]
    simp only [hgens, Sum.elim_inr, Option.elim_none, Option.elim_some, zero_mul, zero_add]
    rw [Finset.sum_eq_single i]
    · simp
    · intro i' _ hne; rw [if_neg hne, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  -- `bb` lies in the cone, by Farkas
  have hmem : bb ∈ coneOf gens := by
    refine (farkas bb).mpr (fun z hz => ?_)
    rw [hsb]
    by_contra hzn
    push_neg at hzn
    have hwnn : ∀ i, 0 ≤ z (some i) := fun i => (hsr i z) ▸ hz (Sum.inr i)
    have hcol : ∀ k, 0 ≤ z none + ∑ i, g i k * z (some i) := fun k => (hsl k z) ▸ hz (Sum.inl k)
    obtain ⟨k₀⟩ := ‹Nonempty κ›
    set Sden : ℝ := ∑ i, z (some i) with hSden
    have hSpos : 0 < Sden := by
      rw [hSden]
      by_contra hS0
      push_neg at hS0
      have hzero : ∑ i, z (some i) = 0 := le_antisymm hS0 (Finset.sum_nonneg fun i _ => hwnn i)
      have hall : ∀ i, z (some i) = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hwnn i).mp hzero i (Finset.mem_univ i)
      have : ∑ i, g i k₀ * z (some i) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hall i, mul_zero]
      linarith [hcol k₀]
    refine hno ⟨fun i => z (some i) / Sden, ⟨fun i => div_nonneg (hwnn i) hSpos.le, ?_⟩, fun k => ?_⟩
    · simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← hSden, mul_inv_cancel₀ hSpos.ne']
    · have hrw : ∑ i, z (some i) / Sden * g i k = (∑ i, g i k * z (some i)) / Sden := by
        simp_rw [div_eq_mul_inv]
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hrw]
      exact div_pos (by linarith [hcol k]) hSpos
  -- read off the distribution `y` from the conic representation
  obtain ⟨c, hcnn, hceq⟩ := hmem
  have happ : ∀ o, ∑ j, c j * gens j o = bb o := by
    intro o
    have hco := congrFun hceq o
    rw [Finset.sum_apply] at hco
    rw [← hco]; exact Finset.sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul]
  refine ⟨fun k => c (Sum.inl k), ⟨fun k => hcnn (Sum.inl k), ?_⟩, fun i => ?_⟩
  · have h1 := happ none
    rw [Fintype.sum_sum_type] at h1
    simp only [hgens, hbb, Sum.elim_inl, Sum.elim_inr, Option.elim_none, mul_one, mul_zero,
      Finset.sum_const_zero, add_zero] at h1
    exact h1
  · have h2 := happ (some i)
    rw [Fintype.sum_sum_type] at h2
    simp only [hgens, hbb, Sum.elim_inl, Sum.elim_inr, Option.elim_some] at h2
    have hsnd : ∑ i', c (Sum.inr i') * (if i = i' then (1 : ℝ) else 0) = c (Sum.inr i) := by
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl, mul_one]
      · intro i' _ hne; rw [if_neg (fun h => hne h.symm), mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hsnd] at h2
    have : ∑ k, c (Sum.inl k) * g i k = -c (Sum.inr i) := by linarith
    rw [this]; linarith [hcnn (Sum.inr i)]

end EconLib.LinearInequalities
