import EcoLean.GameTheory.MathLanguage.Sperner.GridPackage

/-! Sorted `k`-subsets — the combinatorial encoding of the Freudenthal / Kuhn triangulation of the
barycentric simplex grid.  Prefix-count sortedness, the weight spectrum, the gap-fill / separation
theory of facet completions, and the coordinate-deletion machinery.  Pure combinatorics, no geometry. -/

namespace EcoLean
namespace SpernerFreudenthal
namespace BarycentricFreudenthal
open Finset
/-! ### Low-level objects for the correct (sorted-`k`-subset) cell model -/

/-- A `k`-subset of `Fin n`. -/
abbrev KSubset (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

/-- Characteristic coordinate of a subset. -/
def chi {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : ℕ :=
  if i ∈ S then 1 else 0

theorem chi_sum {n : ℕ} (S : Finset (Fin n)) :
    (∑ i, chi S i) = S.card := by
  classical
  unfold chi
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul,
    mul_one]

/-- Candidate vertex `base + χ(S)` for the corrected model. -/
def vertexFromSubset {d : ℕ}
    (base : Fin (d + 1) → ℕ) (S : Finset (Fin (d + 1))) :
    Fin (d + 1) → ℕ :=
  fun i => base i + chi S i

theorem vertexFromSubset_sum {d : ℕ}
    (base : Fin (d + 1) → ℕ) (S : Finset (Fin (d + 1))) :
    (∑ i, vertexFromSubset base S i) = (∑ i, base i) + S.card := by
  classical
  unfold vertexFromSubset
  rw [Finset.sum_add_distrib, chi_sum]

/-- If `S` is a `k`-subset and `(∑ base) + k = N`, the candidate vertex lands in
`SimplexGrid d N` (its coordinate sum is `N`). -/
theorem vertexFromSubset_sum_eq {d N k : ℕ}
    (base : Fin (d + 1) → ℕ) (S : Finset (Fin (d + 1)))
    (hcard : S.card = k) (hsum : (∑ i, base i) + k = N) :
    (∑ i, vertexFromSubset base S i) = N := by
  rw [vertexFromSubset_sum, hcard, hsum]

theorem vertexFromSubset_injective {d : ℕ} (base : Fin (d + 1) → ℕ) :
    Function.Injective (fun S : Finset (Fin (d + 1)) => vertexFromSubset base S) := by
  intro S T h
  ext i
  have hi := congrFun h i
  simp only [vertexFromSubset, chi, add_right_inj] at hi
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all

/-! ### Sorted collections of `k`-subsets (the correct cell model, in isolation)

This builds the cell model: vertices `base + χ(S)` for `S` in a maximal *sorted*
collection of `k`-subsets. Sortedness is by prefix counts (computable; no `Finset.sort`,
which is noncomputable). -/

/-- `#{x ∈ S : x ≤ t}` — the prefix count of `S` below threshold `t`. -/
def KSubset.prefixCount {n k : ℕ} (S : KSubset n k) (t : Fin n) : ℕ :=
  (S.1.filter (· ≤ t)).card

/-- `I` is sorted before `J`: at every threshold the prefix counts interleave,
`#(J ≤ t) ≤ #(I ≤ t) ≤ #(J ≤ t) + 1` (equivalently `i₁≤j₁≤i₂≤j₂≤…` on the sorted
element lists). -/
def KSubset.SortedBefore {n k : ℕ} (I J : KSubset n k) : Prop :=
  ∀ t : Fin n, J.prefixCount t ≤ I.prefixCount t ∧ I.prefixCount t ≤ J.prefixCount t + 1

/-- Two `k`-subsets form a sorted pair iff one is sorted before the other. -/
def KSubset.IsSortedPair {n k : ℕ} (I J : KSubset n k) : Prop :=
  I.SortedBefore J ∨ J.SortedBefore I

instance {n k : ℕ} (I J : KSubset n k) : Decidable (KSubset.SortedBefore I J) := by
  unfold KSubset.SortedBefore; infer_instance

instance {n k : ℕ} (I J : KSubset n k) : Decidable (KSubset.IsSortedPair I J) := by
  unfold KSubset.IsSortedPair; infer_instance

/-- A pairwise-sorted collection of `k`-subsets. -/
def KSubsetCollection.IsSorted {n k : ℕ} (C : Finset (KSubset n k)) : Prop :=
  ∀ I ∈ C, ∀ J ∈ C, I ≠ J → KSubset.IsSortedPair I J

/-- A top-dimensional cell datum: a sorted collection of the maximal size `n`. -/
def KSubsetCollection.IsMaximalSorted {n k : ℕ} (C : Finset (KSubset n k)) : Prop :=
  C.card = n ∧ KSubsetCollection.IsSorted C

instance {n k : ℕ} (C : Finset (KSubset n k)) :
    Decidable (KSubsetCollection.IsSorted C) := by
  unfold KSubsetCollection.IsSorted; infer_instance

instance {n k : ℕ} (C : Finset (KSubset n k)) :
    Decidable (KSubsetCollection.IsMaximalSorted C) := by
  unfold KSubsetCollection.IsMaximalSorted; infer_instance

/-! ### Frozen coordinates of a sorted wall (no-crossing infrastructure)

Coordinates whose membership is constant across a collection.  The key wall lemma:
after erasing one subset from a maximal sorted collection, at most one coordinate is
frozen — the combinatorial analogue of affine independence. -/

/-- Coordinates present in every subset of the collection. -/
def KSubsetCollection.commonPresent {n k : ℕ}
    (A : Finset (KSubset n k)) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∀ S ∈ A, i ∈ S.1

/-- Coordinates absent from every subset of the collection. -/
def KSubsetCollection.commonAbsent {n k : ℕ}
    (A : Finset (KSubset n k)) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∀ S ∈ A, i ∉ S.1

theorem KSubsetCollection.mem_commonPresent_iff {n k : ℕ}
    (A : Finset (KSubset n k)) (i : Fin n) :
    i ∈ KSubsetCollection.commonPresent A ↔ ∀ S ∈ A, i ∈ S.1 := by
  classical
  simp [KSubsetCollection.commonPresent]

theorem KSubsetCollection.mem_commonAbsent_iff {n k : ℕ}
    (A : Finset (KSubset n k)) (i : Fin n) :
    i ∈ KSubsetCollection.commonAbsent A ↔ ∀ S ∈ A, i ∉ S.1 := by
  classical
  simp [KSubsetCollection.commonAbsent]

theorem KSubsetCollection.commonPresent_disjoint_commonAbsent {n k : ℕ}
    {A : Finset (KSubset n k)} (hA : A.Nonempty) :
    Disjoint (KSubsetCollection.commonPresent A) (KSubsetCollection.commonAbsent A) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiP hiA
  obtain ⟨S, hS⟩ := hA
  exact (KSubsetCollection.mem_commonAbsent_iff A i).mp hiA S hS
    ((KSubsetCollection.mem_commonPresent_iff A i).mp hiP S hS)

/-- The frozen coordinates: present-in-all or absent-from-all. -/
def KSubsetCollection.frozenCoords {n k : ℕ}
    (A : Finset (KSubset n k)) : Finset (Fin n) :=
  KSubsetCollection.commonPresent A ∪ KSubsetCollection.commonAbsent A

theorem KSubsetCollection.frozenCoords_card {n k : ℕ}
    {A : Finset (KSubset n k)} (hA : A.Nonempty) :
    (KSubsetCollection.frozenCoords A).card =
      (KSubsetCollection.commonPresent A).card + (KSubsetCollection.commonAbsent A).card := by
  classical
  rw [KSubsetCollection.frozenCoords,
    Finset.card_union_of_disjoint (KSubsetCollection.commonPresent_disjoint_commonAbsent hA)]

theorem KSubsetCollection.isSorted_erase {n k : ℕ} {A : Finset (KSubset n k)}
    (hA : KSubsetCollection.IsSorted A) (S₀ : KSubset n k) :
    KSubsetCollection.IsSorted (A.erase S₀) := fun I hI J hJ hIJ =>
  hA I (Finset.mem_of_mem_erase hI) J (Finset.mem_of_mem_erase hJ) hIJ

/-! ### Sorted-collection cardinality (the broad ground bound, PROVED) -/

/-- `|F ∩ [0,j]| = |F ∩ [0,j)| + [j ∈ F]`. -/
theorem filter_le_card_eq {n : ℕ} (F : Finset (Fin n)) (j : Fin n) :
    (F.filter (· ≤ j)).card = (F.filter (· < j)).card + (if j ∈ F then 1 else 0) := by
  classical
  rw [show (F.filter (· ≤ j)) = (F.filter (· < j)) ∪ (F.filter (· = j)) by
    ext x; simp only [mem_union, mem_filter]; constructor
    · rintro ⟨hx, hxle⟩; rcases lt_or_eq_of_le hxle with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
      · exact ⟨hx, le_of_lt h⟩
      · exact ⟨hx, le_of_eq h⟩]
  rw [card_union_of_disjoint (by
    rw [disjoint_left]; intro x hx hx'
    simp only [mem_filter] at hx hx'
    exact absurd hx'.2 (ne_of_lt hx.2))]
  congr 1
  by_cases hj : j ∈ F
  · rw [if_pos hj, show F.filter (· = j) = {j} by
      ext x; simp only [mem_filter, mem_singleton]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨h ▸ hj, h⟩⟩]
    simp
  · rw [if_neg hj, show F.filter (· = j) = ∅ by
      ext x; simp only [mem_filter, notMem_empty, iff_false, not_and]
      rintro hx rfl; exact hj hx]
    simp

/-- The prefix-count profile determines the subset (least-differing-element argument). -/
theorem KSubset.prefixCount_injective {n k : ℕ} {S T : KSubset n k}
    (h : ∀ t, KSubset.prefixCount S t = KSubset.prefixCount T t) : S = T := by
  classical
  apply Subtype.ext
  by_contra hST
  set D := (S.1 \ T.1) ∪ (T.1 \ S.1) with hD
  have hne : D.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    rw [hD, Finset.union_eq_empty] at hemp
    exact hST (Finset.Subset.antisymm
      (Finset.sdiff_eq_empty_iff_subset.mp hemp.1)
      (Finset.sdiff_eq_empty_iff_subset.mp hemp.2))
  set j := D.min' hne with hj
  have hjmem : j ∈ D := Finset.min'_mem _ hne
  have hbelow : ∀ i, i < j → (i ∈ S.1 ↔ i ∈ T.1) := by
    intro i hi
    by_contra hdiff
    have hiD : i ∈ D := by
      rw [hD, mem_union, mem_sdiff, mem_sdiff]
      by_cases hiS : i ∈ S.1
      · exact Or.inl ⟨hiS, fun hiT => hdiff ⟨fun _ => hiT, fun _ => hiS⟩⟩
      · exact Or.inr ⟨(by tauto : i ∈ T.1), hiS⟩
    exact absurd (Finset.min'_le _ i hiD) (not_le.mpr hi)
  have hfilt : S.1.filter (· < j) = T.1.filter (· < j) := by
    ext x; simp only [mem_filter]
    exact ⟨fun ⟨hx, hxj⟩ => ⟨(hbelow x hxj).mp hx, hxj⟩,
           fun ⟨hx, hxj⟩ => ⟨(hbelow x hxj).mpr hx, hxj⟩⟩
  have hpc := h j
  rw [KSubset.prefixCount, KSubset.prefixCount,
    filter_le_card_eq, filter_le_card_eq, hfilt] at hpc
  rw [hD, mem_union, mem_sdiff, mem_sdiff] at hjmem
  rcases hjmem with ⟨hjS, hjT⟩ | ⟨hjT, hjS⟩
  · rw [if_pos hjS, if_neg hjT] at hpc; omega
  · rw [if_neg hjS, if_pos hjT] at hpc; omega

/-! ### Reusable profile-rank API for sorted collections

The "above-min profile" `aboveMinProfile A S = {t : pcₛ t > minpcₐ t}` is the rank
structure underlying the cardinality bounds: for sorted `A` the profiles lie in a
width-one band, are nested, determine their subset, hence have distinct cardinalities.
Factored out here so the fixed-slice gap-fill theorem can reuse it. -/

/-- The pointwise minimum prefix count over a nonempty collection. -/
noncomputable def KSubsetCollection.minPrefixCount {n k : ℕ}
    (A : Finset (KSubset n k)) (hA : A.Nonempty) (t : Fin n) : ℕ :=
  (A.image fun S => KSubset.prefixCount S t).min' (hA.image _)

theorem KSubsetCollection.minPrefixCount_le {n k : ℕ}
    {A : Finset (KSubset n k)} (hA : A.Nonempty) {S : KSubset n k} (hS : S ∈ A) (t : Fin n) :
    KSubsetCollection.minPrefixCount A hA t ≤ KSubset.prefixCount S t :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem _ hS)

/-- The coordinates where `S`'s prefix count exceeds the collection minimum. -/
noncomputable def KSubsetCollection.aboveMinProfile {n k : ℕ}
    (A : Finset (KSubset n k)) (hA : A.Nonempty) (S : KSubset n k) : Finset (Fin n) :=
  Finset.univ.filter fun t => KSubsetCollection.minPrefixCount A hA t < KSubset.prefixCount S t

theorem KSubsetCollection.mem_aboveMinProfile_iff {n k : ℕ}
    (A : Finset (KSubset n k)) (hA : A.Nonempty) (S : KSubset n k) (t : Fin n) :
    t ∈ KSubsetCollection.aboveMinProfile A hA S ↔
      KSubsetCollection.minPrefixCount A hA t < KSubset.prefixCount S t := by
  simp [KSubsetCollection.aboveMinProfile]

/-- Width-one: in a sorted collection, each prefix count is the minimum or one above. -/
theorem KSubsetCollection.prefixCount_eq_min_or_min_add_one {n k : ℕ}
    {A : Finset (KSubset n k)} (hA_sorted : KSubsetCollection.IsSorted A)
    (hA_ne : A.Nonempty) {S : KSubset n k} (hS : S ∈ A) (t : Fin n) :
    KSubset.prefixCount S t = KSubsetCollection.minPrefixCount A hA_ne t ∨
    KSubset.prefixCount S t = KSubsetCollection.minPrefixCount A hA_ne t + 1 := by
  have hlb := KSubsetCollection.minPrefixCount_le hA_ne hS t
  obtain ⟨S', hS', hS'eq⟩ :=
    Finset.mem_image.mp (Finset.min'_mem _ (hA_ne.image (fun S => KSubset.prefixCount S t)))
  have hS'eq' : KSubset.prefixCount S' t = KSubsetCollection.minPrefixCount A hA_ne t := hS'eq
  have hub : KSubset.prefixCount S t ≤ KSubsetCollection.minPrefixCount A hA_ne t + 1 := by
    by_cases hSS' : S = S'
    · subst hSS'; omega
    · rcases hA_sorted S hS S' hS' hSS' with hb | hb
      · have := (hb t).2; omega
      · have := (hb t).1; omega
  omega

/-- The above-min profile determines the subset (within a sorted collection). -/
theorem KSubsetCollection.eq_of_aboveMinProfile_eq {n k : ℕ}
    {A : Finset (KSubset n k)} (hA_sorted : KSubsetCollection.IsSorted A)
    (hA_ne : A.Nonempty) {S T : KSubset n k} (hS : S ∈ A) (hT : T ∈ A)
    (hprof : KSubsetCollection.aboveMinProfile A hA_ne S =
      KSubsetCollection.aboveMinProfile A hA_ne T) : S = T := by
  apply KSubset.prefixCount_injective
  intro t
  have hSw := KSubsetCollection.prefixCount_eq_min_or_min_add_one hA_sorted hA_ne hS t
  have hTw := KSubsetCollection.prefixCount_eq_min_or_min_add_one hA_sorted hA_ne hT t
  have hiff : KSubsetCollection.minPrefixCount A hA_ne t < KSubset.prefixCount S t ↔
      KSubsetCollection.minPrefixCount A hA_ne t < KSubset.prefixCount T t := by
    rw [← KSubsetCollection.mem_aboveMinProfile_iff, ← KSubsetCollection.mem_aboveMinProfile_iff,
      hprof]
  omega

/-- Above-min profiles of a sorted collection are nested. -/
theorem KSubsetCollection.aboveMinProfile_subset_or_superset {n k : ℕ}
    {A : Finset (KSubset n k)} (hA_sorted : KSubsetCollection.IsSorted A)
    (hA_ne : A.Nonempty) {S T : KSubset n k} (hS : S ∈ A) (hT : T ∈ A) :
    KSubsetCollection.aboveMinProfile A hA_ne S ⊆ KSubsetCollection.aboveMinProfile A hA_ne T ∨
    KSubsetCollection.aboveMinProfile A hA_ne T ⊆ KSubsetCollection.aboveMinProfile A hA_ne S := by
  by_cases hST : S = T
  · subst hST; exact Or.inl (Finset.Subset.refl _)
  · rcases hA_sorted S hS T hT hST with hb | hb
    · refine Or.inr (fun t ht => ?_)
      rw [KSubsetCollection.mem_aboveMinProfile_iff] at ht ⊢
      exact lt_of_lt_of_le ht (hb t).1
    · refine Or.inl (fun t ht => ?_)
      rw [KSubsetCollection.mem_aboveMinProfile_iff] at ht ⊢
      exact lt_of_lt_of_le ht (hb t).1

/-- The rank map: distinct above-min profiles have distinct cardinalities. -/
theorem KSubsetCollection.aboveMinProfile_card_injective_on {n k : ℕ}
    {A : Finset (KSubset n k)} (hA_sorted : KSubsetCollection.IsSorted A) (hA_ne : A.Nonempty) :
    Set.InjOn (fun S : KSubset n k => (KSubsetCollection.aboveMinProfile A hA_ne S).card)
      (↑A : Set (KSubset n k)) := by
  intro S hS T hT hcard
  simp only at hcard
  rcases KSubsetCollection.aboveMinProfile_subset_or_superset hA_sorted hA_ne hS hT with hsub | hsub
  · exact KSubsetCollection.eq_of_aboveMinProfile_eq hA_sorted hA_ne hS hT
      (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm))
  · exact (KSubsetCollection.eq_of_aboveMinProfile_eq hA_sorted hA_ne hT hS
      (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard))).symm

/- a sorted collection of `k`-subsets of `Fin n` (`0 < n`) has `≤ n`
members.  Proof: the "above-min" profile sets `T_S = {t : pcₛ t > minpcₐ t}` are
nested (chain in a width-1 band), distinct (they determine `S`), and avoid the last
coordinate, so `S ↦ |T_S|` injects `A` into `{0,…,n-1}`. -/
open KSubsetCollection in
theorem KSubsetCollection.sorted_card_le_ground_card {n k : ℕ} (hn : 0 < n)
    {A : Finset (KSubset n k)} (hA : IsSorted A) : A.card ≤ n := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · simp
  set mpc : Fin n → ℕ := fun t => (A.image (fun S => KSubset.prefixCount S t)).min'
    (hAne.image _) with hmpc
  have hlb : ∀ S ∈ A, ∀ t, mpc t ≤ KSubset.prefixCount S t := fun S hS t =>
    Finset.min'_le _ _ (Finset.mem_image_of_mem _ hS)
  have hub : ∀ S ∈ A, ∀ t, KSubset.prefixCount S t ≤ mpc t + 1 := by
    intro S hS t
    obtain ⟨S', hS', hS'eq⟩ :=
      Finset.mem_image.mp (Finset.min'_mem _ (hAne.image (fun S => KSubset.prefixCount S t)))
    have hS'eq' : KSubset.prefixCount S' t = mpc t := hS'eq
    by_cases hSS' : S = S'
    · subst hSS'; omega
    · rcases hA S hS S' hS' hSS' with hb | hb
      · have := (hb t).2; omega
      · have := (hb t).1; omega
  set T : KSubset n k → Finset (Fin n) :=
    fun S => Finset.univ.filter (fun t => mpc t < KSubset.prefixCount S t) with hT
  set last : Fin n := ⟨n - 1, by omega⟩ with hlast
  have hle_last : ∀ x : Fin n, x ≤ last := by
    intro x
    show x.val ≤ last.val
    have h2 : last.val = n - 1 := rfl
    have := x.isLt
    omega
  have hpc_last : ∀ S : KSubset n k, KSubset.prefixCount S last = k := by
    intro S
    rw [KSubset.prefixCount, Finset.filter_true_of_mem (fun x _ => hle_last x), S.2]
  have hlast_notT : ∀ S ∈ A, last ∉ T S := by
    intro S hS
    rw [hT]; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    have h1 := hlb S hS last
    have h2 : mpc last = k := by
      obtain ⟨S'', _, hS''eq⟩ :=
        Finset.mem_image.mp (Finset.min'_mem _ (hAne.image (fun S => KSubset.prefixCount S last)))
      have hS''eq' : KSubset.prefixCount S'' last = mpc last := hS''eq
      rw [← hS''eq', hpc_last S'']
    rw [hpc_last, h2]
  have hpc_eq : ∀ S ∈ A, ∀ t,
      KSubset.prefixCount S t = mpc t + (if t ∈ T S then 1 else 0) := by
    intro S hS t
    rw [hT]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 := hlb S hS t; have h2 := hub S hS t
    by_cases hlt : mpc t < KSubset.prefixCount S t
    · rw [if_pos hlt]; omega
    · rw [if_neg hlt]; omega
  have hTinj : ∀ S ∈ A, ∀ S' ∈ A, T S = T S' → S = S' := by
    intro S hS S' hS' hTeq
    apply KSubset.prefixCount_injective
    intro t
    rw [hpc_eq S hS t, hpc_eq S' hS' t, hTeq]
  have hnested : ∀ S ∈ A, ∀ S' ∈ A, T S ⊆ T S' ∨ T S' ⊆ T S := by
    intro S hS S' hS'
    by_cases hSS' : S = S'
    · subst hSS'; exact Or.inl (Finset.Subset.refl _)
    · rcases hA S hS S' hS' hSS' with hb | hb
      · right; intro t ht
        rw [hT] at ht ⊢; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        exact lt_of_lt_of_le ht (hb t).1
      · left; intro t ht
        rw [hT] at ht ⊢; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        exact lt_of_lt_of_le ht (hb t).1
  have hcardinj : Set.InjOn (fun S => (T S).card) (A : Set (KSubset n k)) := by
    intro S hS S' hS' hcard
    simp only at hcard
    by_contra hne
    rcases hnested S hS S' hS' with hsub | hsub
    · exact hne (hTinj S hS S' hS' (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)))
    · exact hne (hTinj S hS S' hS' (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard)).symm)
  have hcard_lt : ∀ S ∈ A, (T S).card < n := by
    intro S hS
    have hsub : T S ⊆ Finset.univ.erase last := by
      intro t ht
      rw [Finset.mem_erase]
      exact ⟨fun heq => hlast_notT S hS (heq ▸ ht), Finset.mem_univ t⟩
    calc (T S).card ≤ (Finset.univ.erase last).card := Finset.card_le_card hsub
      _ = n - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
                          Fintype.card_fin]
      _ < n := by omega
  calc A.card = (A.image (fun S => (T S).card)).card :=
        (Finset.card_image_of_injOn hcardinj).symm
    _ ≤ (Finset.range n).card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_range.mpr (hcard_lt S hS)
    _ = n := Finset.card_range n

/-! ### Fixed-slice extension building blocks (toward the gap-fill)

The fixed-slice gap-fill bounds the number of ways to complete a wall `A = C.erase S₀`
(`A.card = n-1`) back to a maximal sorted collection.  The reusable pieces below:
`isSorted_insert` (extend a sorted set by a compatible subset), the structural
`sameFrameExtensions_not_isSortedPair` (distinct completions CROSS — else the union
would beat the ground bound), and the finite-set 2-filler lemma
`card_interm_le_card_sdiff`. -/

/-- `IsSortedPair` is symmetric. -/
theorem KSubset.IsSortedPair.symm {n k : ℕ} {I J : KSubset n k}
    (h : KSubset.IsSortedPair I J) : KSubset.IsSortedPair J I := Or.symm h

/-- Insert a subset that is sorted with every member of a sorted collection. -/
theorem KSubsetCollection.isSorted_insert {n k : ℕ} {A : Finset (KSubset n k)}
    (hA : KSubsetCollection.IsSorted A) {x : KSubset n k}
    (hx : ∀ S ∈ A, KSubset.IsSortedPair x S) :
    KSubsetCollection.IsSorted (insert x A) := by
  intro I hI J hJ hIJ
  rw [Finset.mem_insert] at hI hJ
  rcases hI with rfl | hI <;> rcases hJ with rfl | hJ
  · exact absurd rfl hIJ
  · exact hx J hJ
  · exact (hx I hI).symm
  · exact hA I hI J hJ hIJ

/-- The fixed-slice completions of a wall `A`: subsets `T ∉ A` making `insert T A`
maximal sorted. -/
noncomputable def KSubsetCollection.sameFrameExtensions {n k : ℕ}
    (A : Finset (KSubset n k)) : Finset (KSubset n k) :=
  Finset.univ.filter fun T => T ∉ A ∧ KSubsetCollection.IsMaximalSorted (insert T A)

theorem KSubsetCollection.mem_sameFrameExtensions_iff {n k : ℕ}
    (A : Finset (KSubset n k)) (T : KSubset n k) :
    T ∈ KSubsetCollection.sameFrameExtensions A ↔
      T ∉ A ∧ KSubsetCollection.IsMaximalSorted (insert T A) := by
  simp [KSubsetCollection.sameFrameExtensions]

/-- A completion is sorted with every wall member. -/
theorem KSubsetCollection.extension_sortedWith_wall {n k : ℕ}
    {A : Finset (KSubset n k)} {T : KSubset n k}
    (hT : T ∈ KSubsetCollection.sameFrameExtensions A) {S : KSubset n k} (hS : S ∈ A) :
    KSubset.IsSortedPair T S := by
  rw [mem_sameFrameExtensions_iff] at hT
  have hTne : T ≠ S := fun h => hT.1 (h ▸ hS)
  exact hT.2.2 T (Finset.mem_insert_self _ _) S (Finset.mem_insert_of_mem hS) hTne

/-- KEY structural fact: distinct fixed-slice completions are pairwise NON-sorted
(they cross) — otherwise their union with the wall would be a sorted collection of
card `n+1`, contradicting the ground bound. -/
theorem KSubsetCollection.sameFrameExtensions_not_isSortedPair {n k : ℕ}
    {A : Finset (KSubset n k)}
    {T U : KSubset n k} (hT : T ∈ KSubsetCollection.sameFrameExtensions A)
    (hU : U ∈ KSubsetCollection.sameFrameExtensions A) (hTU : T ≠ U) :
    ¬ KSubset.IsSortedPair T U := by
  intro hpair
  rw [mem_sameFrameExtensions_iff] at hT hU
  have hTcard : (insert T A).card = n := hT.2.1
  have hTne : (insert T A).Nonempty := ⟨T, Finset.mem_insert_self _ _⟩
  have hn : 0 < n := by rw [← hTcard]; exact Finset.card_pos.mpr hTne
  have hUwith : ∀ S ∈ insert T A, KSubset.IsSortedPair U S := by
    intro S hS
    rw [Finset.mem_insert] at hS
    rcases hS with rfl | hS
    · exact hpair.symm
    · exact KSubsetCollection.extension_sortedWith_wall
        (by rw [mem_sameFrameExtensions_iff]; exact hU) hS
  have hsorted : KSubsetCollection.IsSorted (insert U (insert T A)) :=
    KSubsetCollection.isSorted_insert hT.2.2 hUwith
  have hUnotin : U ∉ insert T A := by
    rw [Finset.mem_insert]; rintro (rfl | hUA)
    · exact hTU rfl
    · exact hU.1 hUA
  have hcard : (insert U (insert T A)).card = n + 1 := by
    rw [Finset.card_insert_of_notMem hUnotin, hTcard]
  have hbound := KSubsetCollection.sorted_card_le_ground_card hn hsorted
  omega

/-- The 2-filler lemma: between `L` and `U`, the sets of card `|L|+1` inject into the
singletons of `U \ L`, hence number at most `|U \ L|` (which is `2` when `|U| = |L|+2`). -/
theorem Finset.card_interm_le_card_sdiff {α : Type*} [DecidableEq α] (L U : Finset α) :
    (U.powerset.filter fun X => L ⊆ X ∧ X.card = L.card + 1).card ≤ (U \ L).card := by
  classical
  rw [show (U \ L).card = ((U \ L).powersetCard 1).card by
    rw [Finset.card_powersetCard]; simp]
  apply Finset.card_le_card_of_injOn (fun X => X \ L)
  · intro X hX
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hX
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨Finset.sdiff_subset_sdiff hX.1 (le_refl L), ?_⟩
    have hu : X \ L ∪ L = X := Finset.sdiff_union_of_subset hX.2.1
    have hd : Disjoint (X \ L) L := Finset.sdiff_disjoint
    have hsum : (X \ L).card + L.card = X.card := by
      rw [← Finset.card_union_of_disjoint hd, hu]
    omega
  · intro X hX Y hY heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hX hY
    dsimp only at heq
    have hX' := Finset.sdiff_union_of_subset hX.2.1
    rw [heq, Finset.sdiff_union_of_subset hY.2.1] at hX'
    exact hX'.symm

/-! ### Ambient-independent prefix weight (the correct gap-fill invariant)

`aboveMinProfile` is ambient-dependent, so it cannot compare completions across the
competing collections `insert T A`.  The prefix WEIGHT `w(S) = ∑ₜ pcₛ(t)` is
ambient-independent: it is strictly monotone along `SortedBefore`, hence injective on
any sorted collection, and `w(S) = (∑ minpc) + rank(S)` — so a MAXIMAL sorted collection
has a CONSECUTIVE weight spectrum `Ico b (b+n)`.  This is the invariant that survives
across ambients. -/

/-- The prefix weight `∑ₜ #{x ∈ S : x ≤ t}` (ambient-independent). -/
def KSubset.prefixWeight {n k : ℕ} (S : KSubset n k) : ℕ :=
  ∑ t : Fin n, KSubset.prefixCount S t

/-- Along `SortedBefore S T` (so `pc T ≤ pc S` pointwise), weight decreases. -/
theorem KSubset.SortedBefore.prefixWeight_le {n k : ℕ} {S T : KSubset n k}
    (h : KSubset.SortedBefore S T) : KSubset.prefixWeight T ≤ KSubset.prefixWeight S := by
  apply Finset.sum_le_sum
  intro t _
  exact (h t).1

theorem KSubset.SortedBefore.prefixWeight_lt {n k : ℕ} {S T : KSubset n k}
    (h : KSubset.SortedBefore S T) (hne : S ≠ T) :
    KSubset.prefixWeight T < KSubset.prefixWeight S := by
  apply Finset.sum_lt_sum (fun t _ => (h t).1)
  by_contra hcon
  push_neg at hcon
  apply hne
  apply KSubset.prefixCount_injective
  intro t
  have h1 := (h t).1
  have h2 := hcon t (Finset.mem_univ t)
  omega

/-- Weight is injective on a sorted collection (its members form a weight chain). -/
theorem KSubsetCollection.prefixWeight_injective_on {n k : ℕ}
    {A : Finset (KSubset n k)} (hA : KSubsetCollection.IsSorted A) :
    Set.InjOn (fun S : KSubset n k => KSubset.prefixWeight S) (↑A : Set (KSubset n k)) := by
  intro S hS T hT heq
  simp only [Finset.mem_coe] at hS hT
  by_contra hST
  rcases hA S hS T hT hST with hb | hb
  · exact absurd heq (Nat.ne_of_lt (hb.prefixWeight_lt hST)).symm
  · exact absurd heq (Nat.ne_of_lt (hb.prefixWeight_lt (Ne.symm hST)))

/-- Weight splits as `(∑ minpc) + rank`, where rank is the above-min profile cardinality. -/
theorem KSubsetCollection.prefixWeight_eq_base_add_aboveMinProfile_card {n k : ℕ}
    {C : Finset (KSubset n k)} (hC_sorted : KSubsetCollection.IsSorted C)
    (hC_ne : C.Nonempty) {S : KSubset n k} (hS : S ∈ C) :
    KSubset.prefixWeight S =
      (∑ t : Fin n, KSubsetCollection.minPrefixCount C hC_ne t)
        + (KSubsetCollection.aboveMinProfile C hC_ne S).card := by
  classical
  have hpt : ∀ t : Fin n, KSubset.prefixCount S t =
      KSubsetCollection.minPrefixCount C hC_ne t +
        (if t ∈ KSubsetCollection.aboveMinProfile C hC_ne S then 1 else 0) := by
    intro t
    rcases KSubsetCollection.prefixCount_eq_min_or_min_add_one hC_sorted hC_ne hS t with h | h
    · have hni : t ∉ KSubsetCollection.aboveMinProfile C hC_ne S := by
        rw [KSubsetCollection.mem_aboveMinProfile_iff]; omega
      rw [if_neg hni]; omega
    · have hi : t ∈ KSubsetCollection.aboveMinProfile C hC_ne S := by
        rw [KSubsetCollection.mem_aboveMinProfile_iff]; omega
      rw [if_pos hi]; omega
  rw [KSubset.prefixWeight, Finset.sum_congr rfl (fun t _ => hpt t), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]

/-- The above-min rank avoids the last coordinate, so it is `< n`. -/
theorem KSubsetCollection.aboveMinProfile_card_lt {n k : ℕ} (hn : 0 < n)
    {C : Finset (KSubset n k)} (hC_ne : C.Nonempty) (S : KSubset n k) :
    (KSubsetCollection.aboveMinProfile C hC_ne S).card < n := by
  classical
  set tl : Fin n := ⟨n - 1, by omega⟩ with htl
  have hlast : ∀ S' : KSubset n k, KSubset.prefixCount S' tl = k := by
    intro S'
    have hf : S'.1.filter (· ≤ tl) = S'.1 := Finset.filter_true_of_mem (fun j _ => by
      have hj : j.val < n := j.isLt
      have htlv : tl.val = n - 1 := by rw [htl]
      rw [Fin.le_def]; omega)
    rw [KSubset.prefixCount, hf]; exact S'.2
  have hmin : KSubsetCollection.minPrefixCount C hC_ne tl = k := by
    obtain ⟨S', hS', hS'eq⟩ := Finset.mem_image.mp
      (Finset.min'_mem _ (hC_ne.image (fun S => KSubset.prefixCount S tl)))
    have heq : KSubset.prefixCount S' tl = KSubsetCollection.minPrefixCount C hC_ne tl := hS'eq
    rw [← heq]; exact hlast S'
  have htlni : tl ∉ KSubsetCollection.aboveMinProfile C hC_ne S := by
    rw [KSubsetCollection.mem_aboveMinProfile_iff, hmin, hlast S]; omega
  calc (KSubsetCollection.aboveMinProfile C hC_ne S).card
      ≤ (Finset.univ.erase tl).card :=
        Finset.card_le_card (fun x hx => Finset.mem_erase.mpr
          ⟨fun h => htlni (h ▸ hx), Finset.mem_univ x⟩)
    _ = n - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ tl), Finset.card_univ,
        Fintype.card_fin]
    _ < n := by omega

/-- THE SPECTRUM THEOREM: a maximal sorted collection has weights `Ico b (b+n)` —
`n` consecutive integers. -/
theorem KSubsetCollection.exists_base_weight_image_eq_Ico_of_isMaximalSorted {n k : ℕ}
    {C : Finset (KSubset n k)} (hC : KSubsetCollection.IsMaximalSorted C) :
    ∃ b : ℕ, C.image KSubset.prefixWeight = Finset.Ico b (b + n) := by
  classical
  obtain ⟨hcard, hsorted⟩ := hC
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    exact ⟨0, by rw [Finset.card_eq_zero.mp hcard]; simp⟩
  have hne : C.Nonempty := Finset.card_pos.mp (by omega)
  set base := ∑ t : Fin n, KSubsetCollection.minPrefixCount C hne t with hbase
  refine ⟨base, ?_⟩
  have h3 : C.image (fun S => (KSubsetCollection.aboveMinProfile C hne S).card)
      = Finset.range n := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (KSubsetCollection.aboveMinProfile_card_lt hn hne S)
    · rw [Finset.card_range,
        Finset.card_image_of_injOn (KSubsetCollection.aboveMinProfile_card_injective_on hsorted hne),
        hcard]
  have key : C.image KSubset.prefixWeight = (Finset.range n).image (fun c => base + c) := by
    rw [← h3, Finset.image_image]
    apply Finset.image_congr
    intro S hS
    exact KSubsetCollection.prefixWeight_eq_base_add_aboveMinProfile_card hsorted hne
      (Finset.mem_coe.mp hS)
  rw [key]
  ext m
  rw [Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [Finset.mem_range] at hc
    omega
  · intro hm
    exact ⟨m - base, Finset.mem_range.mpr (by omega), by omega⟩

/-- The erased wall inherits the consecutive spectrum minus one weight. -/
theorem KSubsetCollection.prefixWeight_image_erase_eq_delete {n k : ℕ}
    {C : Finset (KSubset n k)} (hC_sorted : KSubsetCollection.IsSorted C)
    {S₀ : KSubset n k} (hS₀ : S₀ ∈ C) :
    (C.erase S₀).image KSubset.prefixWeight =
      (C.image KSubset.prefixWeight).erase (KSubset.prefixWeight S₀) := by
  classical
  ext m
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨S, ⟨hSne, hSC⟩, rfl⟩
    refine ⟨?_, S, hSC, rfl⟩
    intro hpweq
    exact hSne (KSubsetCollection.prefixWeight_injective_on hC_sorted
      (Finset.mem_coe.mpr hSC) (Finset.mem_coe.mpr hS₀) hpweq)
  · rintro ⟨hne, S, hSC, rfl⟩
    exact ⟨S, ⟨fun hSeq => hne (by rw [hSeq]), hSC⟩, rfl⟩

/-! ### Fixed-slice INTERIOR case (deleting a non-endpoint weight ⟹ ≤ 2 completions)

The weight `w(S₀)` of the erased vertex sits inside `(b, b+n-1)`.  Then the wall spans the
FULL interval `[b, b+n-1]` minus the interior hole `w(S₀)`, so every completion has weight
exactly `w(S₀)` (only the hole keeps the spectrum consecutive — proved by
`interval_insert_erase_interior`), is sandwiched between the wall's two weight-neighbours
`Slo` (weight `w₀−1`) and `Shi` (weight `w₀+1`), hence is HIGH & in-band relative to the
wall.  The completion ↦ `aboveMinProfile` map is then injective into the sets bracketed
between `aboveMinProfile Slo ⊆ · ⊆ aboveMinProfile Shi` (cardinalities differ by 2), so
`Finset.card_interm_le_card_sdiff` gives `≤ 2`.  (The ENDPOINT case is genuinely different —
`EndpointDeletionAudit` shows it gives 2 via TWO exterior weights, not ≤ 1.) -/

/-- Weight `= base + above-min rank`, for ANY subset that is high & in-band relative to `A`
(not necessarily a member) — this is what completions satisfy. -/
theorem KSubsetCollection.prefixWeight_eq_base_add_aboveMinProfile_card_of_band {n k : ℕ}
    {A : Finset (KSubset n k)} (hA_ne : A.Nonempty) {T : KSubset n k}
    (hband : ∀ t, KSubsetCollection.minPrefixCount A hA_ne t ≤ KSubset.prefixCount T t ∧
      KSubset.prefixCount T t ≤ KSubsetCollection.minPrefixCount A hA_ne t + 1) :
    KSubset.prefixWeight T =
      (∑ t : Fin n, KSubsetCollection.minPrefixCount A hA_ne t)
        + (KSubsetCollection.aboveMinProfile A hA_ne T).card := by
  classical
  have hpt : ∀ t : Fin n, KSubset.prefixCount T t =
      KSubsetCollection.minPrefixCount A hA_ne t +
        (if t ∈ KSubsetCollection.aboveMinProfile A hA_ne T then 1 else 0) := by
    intro t
    have hb := hband t
    by_cases hi : t ∈ KSubsetCollection.aboveMinProfile A hA_ne T
    · rw [if_pos hi]
      rw [KSubsetCollection.mem_aboveMinProfile_iff] at hi
      omega
    · rw [if_neg hi]
      rw [KSubsetCollection.mem_aboveMinProfile_iff] at hi
      omega
  rw [KSubset.prefixWeight, Finset.sum_congr rfl (fun t _ => hpt t), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]

/-- Inserting `x` into an interval-minus-interior-point to get an interval forces `x` to be
that point. -/
theorem interval_insert_erase_interior {n b w x c : ℕ} (hn : 0 < n)
    (hbw : b < w) (hwb : w < b + n - 1)
    (heq : insert x ((Finset.Ico b (b + n)).erase w) = Finset.Ico c (c + n)) :
    x = w := by
  have hwmem : w ∈ Finset.Ico b (b + n) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hbmem : b ∈ (Finset.Ico b (b + n)).erase w :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩
  have hbnmem : b + n - 1 ∈ (Finset.Ico b (b + n)).erase w :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩
  have hb_in : b ∈ Finset.Ico c (c + n) := heq ▸ Finset.mem_insert_of_mem hbmem
  have hbn_in : b + n - 1 ∈ Finset.Ico c (c + n) := heq ▸ Finset.mem_insert_of_mem hbnmem
  rw [Finset.mem_Ico] at hb_in hbn_in
  have hc : c = b := by omega
  rw [hc] at heq
  have hcardS : ((Finset.Ico b (b + n)).erase w).card = n - 1 := by
    rw [Finset.card_erase_of_mem hwmem, Nat.card_Ico]; omega
  have hxnotin : x ∉ (Finset.Ico b (b + n)).erase w := by
    intro hx
    have : insert x ((Finset.Ico b (b + n)).erase w) = (Finset.Ico b (b + n)).erase w :=
      Finset.insert_eq_self.mpr hx
    rw [this] at heq
    have h1 := heq ▸ hcardS
    rw [Nat.card_Ico] at h1; omega
  have hx_in : x ∈ Finset.Ico b (b + n) := by
    have : x ∈ Finset.Ico b (b + n) := by rw [← heq]; exact Finset.mem_insert_self _ _
    exact this
  by_contra hxw
  exact hxnotin (Finset.mem_erase.mpr ⟨hxw, hx_in⟩)

/-- THE INTERIOR CASE: deleting an interior-weight vertex gives `≤ 2` completions. -/
theorem KSubsetCollection.sameFrame_extensions_card_le_two_of_erased_interior {n k : ℕ}
    {C : Finset (KSubset n k)} (hC : KSubsetCollection.IsMaximalSorted C)
    {S₀ : KSubset n k} (hS₀ : S₀ ∈ C) {b : ℕ}
    (himg : C.image KSubset.prefixWeight = Finset.Ico b (b + n))
    (hint : b < KSubset.prefixWeight S₀ ∧ KSubset.prefixWeight S₀ < b + n - 1) :
    (KSubsetCollection.sameFrameExtensions (C.erase S₀)).card ≤ 2 := by
  classical
  obtain ⟨hcardC, hCsorted⟩ := hC
  set A := C.erase S₀ with hA
  set w₀ := KSubset.prefixWeight S₀ with hw₀
  have hn3 : 3 ≤ n := by omega
  have hAsorted : KSubsetCollection.IsSorted A :=
    fun I hI J hJ hIJ => hCsorted I (Finset.mem_of_mem_erase hI) J (Finset.mem_of_mem_erase hJ) hIJ
  have hAne : A.Nonempty := by
    rw [hA, ← Finset.card_pos, Finset.card_erase_of_mem hS₀, hcardC]; omega
  have himgA : A.image KSubset.prefixWeight = (Finset.Ico b (b + n)).erase w₀ := by
    rw [hA, KSubsetCollection.prefixWeight_image_erase_eq_delete hCsorted hS₀, himg]
  have hlomem : w₀ - 1 ∈ A.image KSubset.prefixWeight := by
    rw [himgA]; exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩
  have himem : w₀ + 1 ∈ A.image KSubset.prefixWeight := by
    rw [himgA]; exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩
  obtain ⟨Slo, hSloA, hSlow⟩ := Finset.mem_image.mp hlomem
  obtain ⟨Shi, hShiA, hShiw⟩ := Finset.mem_image.mp himem
  set L := KSubsetCollection.aboveMinProfile A hAne Slo with hL
  set U := KSubsetCollection.aboveMinProfile A hAne Shi with hU
  set base := ∑ t : Fin n, KSubsetCollection.minPrefixCount A hAne t with hbase
  have hLcard : L.card = w₀ - 1 - base := by
    have h := KSubsetCollection.prefixWeight_eq_base_add_aboveMinProfile_card hAsorted hAne hSloA
    rw [hSlow, ← hbase, ← hL] at h; omega
  have hUcard : U.card = w₀ + 1 - base := by
    have h := KSubsetCollection.prefixWeight_eq_base_add_aboveMinProfile_card hAsorted hAne hShiA
    rw [hShiw, ← hbase, ← hU] at h; omega
  have hbase_le : base ≤ w₀ - 1 := by
    have h := KSubsetCollection.prefixWeight_eq_base_add_aboveMinProfile_card hAsorted hAne hSloA
    rw [hSlow, ← hbase] at h; omega
  have hSlohi_pair : KSubset.IsSortedPair Shi Slo := hAsorted Shi hShiA Slo hSloA (by
    intro h; rw [h] at hShiw; omega)
  have hpc_lohi : ∀ t, KSubset.prefixCount Slo t ≤ KSubset.prefixCount Shi t := by
    rcases hSlohi_pair with hb | hb
    · exact fun t => (hb t).1
    · exact fun t => absurd (hb.prefixWeight_lt (by rintro rfl; omega))
        (by rw [hShiw, hSlow]; omega)
  have hLU : L ⊆ U := by
    intro t ht
    rw [hL, KSubsetCollection.mem_aboveMinProfile_iff] at ht
    rw [hU, KSubsetCollection.mem_aboveMinProfile_iff]
    exact lt_of_lt_of_le ht (hpc_lohi t)
  have hclaim : ∀ T ∈ KSubsetCollection.sameFrameExtensions A,
      (∀ t, KSubset.prefixCount Slo t ≤ KSubset.prefixCount T t) ∧
      (∀ t, KSubset.prefixCount T t ≤ KSubset.prefixCount Shi t) ∧
      (∀ t, KSubsetCollection.minPrefixCount A hAne t ≤ KSubset.prefixCount T t ∧
        KSubset.prefixCount T t ≤ KSubsetCollection.minPrefixCount A hAne t + 1) ∧
      KSubset.prefixWeight T = w₀ := by
    intro T hT
    have hTmem := hT
    rw [KSubsetCollection.mem_sameFrameExtensions_iff] at hT
    obtain ⟨c, hc⟩ := KSubsetCollection.exists_base_weight_image_eq_Ico_of_isMaximalSorted hT.2
    rw [Finset.image_insert, himgA] at hc
    have hwT : KSubset.prefixWeight T = w₀ :=
      interval_insert_erase_interior (by omega) hint.1 hint.2 hc
    have hpairlo := KSubsetCollection.extension_sortedWith_wall hTmem hSloA
    have hpairhi := KSubsetCollection.extension_sortedWith_wall hTmem hShiA
    have hTlo : ∀ t, KSubset.prefixCount Slo t ≤ KSubset.prefixCount T t := by
      rcases hpairlo with hb | hb
      · exact fun t => (hb t).1
      · exact fun t => absurd (hb.prefixWeight_lt (by rintro rfl; omega))
          (by rw [hwT, hSlow]; omega)
    have hThi : ∀ t, KSubset.prefixCount T t ≤ KSubset.prefixCount Shi t := by
      rcases hpairhi with hb | hb
      · exact fun t => absurd (hb.prefixWeight_lt (by rintro rfl; omega))
          (by rw [hwT, hShiw]; omega)
      · exact fun t => (hb t).1
    refine ⟨hTlo, hThi, fun t => ⟨le_trans (KSubsetCollection.minPrefixCount_le hAne hSloA t) (hTlo t), ?_⟩, hwT⟩
    have hShib := KSubsetCollection.prefixCount_eq_min_or_min_add_one hAsorted hAne hShiA t
    have := hThi t
    omega
  have hmaps : ∀ T ∈ KSubsetCollection.sameFrameExtensions A,
      KSubsetCollection.aboveMinProfile A hAne T ∈
        U.powerset.filter (fun X => L ⊆ X ∧ X.card = L.card + 1) := by
    intro T hT
    obtain ⟨hTlo, hThi, hband, hwT⟩ := hclaim T hT
    have hTwt := KSubsetCollection.prefixWeight_eq_base_add_aboveMinProfile_card_of_band hAne hband
    rw [hwT] at hTwt
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      rw [KSubsetCollection.mem_aboveMinProfile_iff] at ht
      rw [hU, KSubsetCollection.mem_aboveMinProfile_iff]
      exact lt_of_lt_of_le ht (hThi t)
    · intro t ht
      rw [hL, KSubsetCollection.mem_aboveMinProfile_iff] at ht
      rw [KSubsetCollection.mem_aboveMinProfile_iff]
      exact lt_of_lt_of_le ht (hTlo t)
    · rw [hLcard]; omega
  have hinj : Set.InjOn (fun T => KSubsetCollection.aboveMinProfile A hAne T)
      (↑(KSubsetCollection.sameFrameExtensions A) : Set (KSubset n k)) := by
    intro T hT T' hT' heqp
    rw [Finset.mem_coe] at hT hT'
    obtain ⟨_, _, hbandT, _⟩ := hclaim T hT
    obtain ⟨_, _, hbandT', _⟩ := hclaim T' hT'
    have heqp' : KSubsetCollection.aboveMinProfile A hAne T =
        KSubsetCollection.aboveMinProfile A hAne T' := heqp
    apply KSubset.prefixCount_injective
    intro t
    have hiff : (KSubsetCollection.minPrefixCount A hAne t < KSubset.prefixCount T t) ↔
        (KSubsetCollection.minPrefixCount A hAne t < KSubset.prefixCount T' t) := by
      rw [← KSubsetCollection.mem_aboveMinProfile_iff, ← KSubsetCollection.mem_aboveMinProfile_iff,
        heqp']
    have h1 := hbandT t
    have h2 := hbandT' t
    omega
  calc (KSubsetCollection.sameFrameExtensions A).card
      ≤ (U.powerset.filter (fun X => L ⊆ X ∧ X.card = L.card + 1)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ (U \ L).card := Finset.card_interm_le_card_sdiff L U
    _ ≤ 2 := by
        have hu : U \ L ∪ L = U := Finset.sdiff_union_of_subset hLU
        have hd : Disjoint (U \ L) L := Finset.sdiff_disjoint
        have : (U \ L).card + L.card = U.card := by rw [← Finset.card_union_of_disjoint hd, hu]
        rw [hUcard, hLcard] at this; omega

/-- The prefix count at `j₀` equals the prefix count at its predecessor `jp`, plus the
indicator of `j₀ ∈ S`.  `jp` is any `Fin n` with `jp.val + 1 = j₀.val`.  (Relocated here so the
interior-existence lemmas below can use it.) -/
theorem KSubset.prefixCount_pred {n k : ℕ} (S : KSubset n k) {j₀ jp : Fin n}
    (hjp : jp.val + 1 = j₀.val) :
    S.prefixCount j₀ = S.prefixCount jp + (if j₀ ∈ S.1 then 1 else 0) := by
  classical
  rw [KSubset.prefixCount, KSubset.prefixCount]
  by_cases hj : j₀ ∈ S.1
  · rw [if_pos hj]
    have hset : S.1.filter (· ≤ j₀) = insert j₀ (S.1.filter (· ≤ jp)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Fin.le_def]
      constructor
      · rintro ⟨hxS, hxle⟩
        by_cases hxj : x = j₀
        · exact Or.inl hxj
        · have : x.val ≠ j₀.val := fun h => hxj (Fin.ext h)
          exact Or.inr ⟨hxS, by omega⟩
      · rintro (rfl | ⟨hxS, hxle⟩)
        · exact ⟨hj, le_refl _⟩
        · exact ⟨hxS, by omega⟩
    rw [hset, Finset.card_insert_of_notMem]
    simp only [Finset.mem_filter, Fin.le_def, not_and]
    intro _; omega
  · rw [if_neg hj, Nat.add_zero]
    congr 1
    ext x
    simp only [Finset.mem_filter, Fin.le_def]
    constructor
    · rintro ⟨hxS, hxle⟩
      have hxne : x ≠ j₀ := fun h => hj (h ▸ hxS)
      have : x.val ≠ j₀.val := fun h => hxne (Fin.ext h)
      exact ⟨hxS, by omega⟩
    · rintro ⟨hxS, hxle⟩; exact ⟨hxS, by omega⟩

-- top-coordinate facts (the coordinate above all others has prefix count `k`); relocated here
-- so the interior-existence lemmas below can use them.
theorem prefixCount_top_eq {n k : ℕ} (S : KSubset n k) {t : Fin n} (ht : ∀ j : Fin n, j ≤ t) :
    KSubset.prefixCount S t = k := by
  have hf : S.1.filter (· ≤ t) = S.1 := Finset.filter_true_of_mem (fun j _ => ht j)
  rw [KSubset.prefixCount, hf]; exact S.2

theorem minPrefixCount_top_eq {n k : ℕ} {A : Finset (KSubset n k)} (hA_ne : A.Nonempty)
    {t : Fin n} (ht : ∀ j : Fin n, j ≤ t) : KSubsetCollection.minPrefixCount A hA_ne t = k := by
  obtain ⟨S, _, hSeq⟩ := Finset.mem_image.mp
    (Finset.min'_mem _ (hA_ne.image (fun S => KSubset.prefixCount S t)))
  have heq : KSubset.prefixCount S t = KSubsetCollection.minPrefixCount A hA_ne t := hSeq
  rw [← heq, prefixCount_top_eq S ht]

/-! ### Interior EXISTENCE: constructing the second extension (the descent swap)

The `≤ 2` interior proof bounds extensions by the two bracket profiles `L ∪ {γ}`, `γ ∈ U \ L`.
For the `≥ 2` direction we must CONSTRUCT the extension realising a profile.  The candidate for
`L ∪ {γ}` (`pc = pc_{Slo} + 1_γ` pointwise, since `pc_{Slo} = minPrefixCount + 1_L`) is the
`k`-subset `(Slo.1 \ {γ+1}) ∪ {γ}` — a "descent swap" moving the element at `γ+1` down to `γ` —
valid exactly when `γ` is a descent of `Slo` (`γ ∉ Slo.1`, `γ+1 ∈ Slo.1`). -/

/-- The prefix count of the descent swap `(S.1 \ {γs}) ∪ {γ}` (with `γs = γ+1`, `γ ∉ S`,
`γs ∈ S`): it is `S`'s prefix count, plus one exactly at the threshold `γ`. -/
theorem KSubset.prefixCount_swapDescent {n k : ℕ} (S : KSubset n k) {γ γs : Fin n}
    (hγs : γ.val + 1 = γs.val) (hγ : γ ∉ S.1) (hγs_in : γs ∈ S.1) (t : Fin n) :
    (((S.1 \ {γs}) ∪ {γ}).filter (· ≤ t)).card
      = S.prefixCount t + (if t = γ then 1 else 0) := by
  classical
  have hdisj : Disjoint ((S.1 \ {γs}).filter (· ≤ t)) (({γ} : Finset (Fin n)).filter (· ≤ t)) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_singleton_right]
    exact fun h => hγ (Finset.mem_sdiff.mp h).1
  rw [Finset.filter_union, Finset.card_union_of_disjoint hdisj]
  have hγcard : (({γ} : Finset (Fin n)).filter (· ≤ t)).card = if γ ≤ t then 1 else 0 := by
    rw [Finset.filter_singleton]; split <;> simp
  have hγscard : (({γs} : Finset (Fin n)).filter (· ≤ t)).card = if γs ≤ t then 1 else 0 := by
    rw [Finset.filter_singleton]; split <;> simp
  have hSsplit : ((S.1 \ {γs}).filter (· ≤ t)).card
      + (({γs} : Finset (Fin n)).filter (· ≤ t)).card = S.prefixCount t := by
    rw [KSubset.prefixCount, ← Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter Finset.sdiff_disjoint), ← Finset.filter_union,
      Finset.sdiff_union_of_subset (Finset.singleton_subset_iff.mpr hγs_in)]
  rw [hγcard]
  rw [hγscard] at hSsplit
  have hkey : (if γ ≤ t then (1 : ℕ) else 0)
      = (if γs ≤ t then 1 else 0) + (if t = γ then 1 else 0) := by
    simp only [Fin.le_def, Fin.ext_iff]
    split_ifs <;> omega
  omega

/-! ### Interior existence — the descent swap

The interior same-frame extension is the descent swap `(Slo.1 \ {γ+1}) ∪ {γ}`
(`prefixCount_swapDescent`), with above-min profile `insert γ L` for a gap coordinate `γ ∈ U \ L`.
Compatibility with the whole wall is by profile nesting (`L ⊆ insert γ L ⊆ U`) plus the spectrum gap;
both gap coordinates are descents of `Slo` when non-adjacent, and an adjacent gap freezes the middle
coordinate. -/

/-- THE PSEUDOMANIFOLD FACT (interior, adjacent gap): if the two gap coordinates `γ, γ+1 = U \ L`
of a punctured-interval interior wall are ADJACENT, the middle coordinate `γ+1` is FROZEN.
Every wall profile is `⊆ L` (`⟹ γ, γ+1 ∉` it) or `⊇ U` (`⟹ γ, γ+1 ∈` it) since the spectrum
skips rank `|L|+1`; either way `pc_S(γ+1) − pc_S(γ)` is the constant `minPrefixCount(γ+1) −
minPrefixCount(γ)`, so `[γ+1 ∈ S]` does not depend on `S`. -/
theorem KSubsetCollection.exists_frozenCoord_of_adjacent_interior_gap {n k : ℕ}
    {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W) (hWne : W.Nonempty)
    {Slo Shi : KSubset n k} (hSloA : Slo ∈ W) (hShiA : Shi ∈ W)
    (hUcard : (KSubsetCollection.aboveMinProfile W hWne Shi).card
        = (KSubsetCollection.aboveMinProfile W hWne Slo).card + 2)
    (hgap : ∀ S ∈ W, (KSubsetCollection.aboveMinProfile W hWne S).card
        ≠ (KSubsetCollection.aboveMinProfile W hWne Slo).card + 1)
    {γ γs : Fin n} (hγs : γ.val + 1 = γs.val)
    (hγU : γ ∈ KSubsetCollection.aboveMinProfile W hWne Shi)
    (hγL : γ ∉ KSubsetCollection.aboveMinProfile W hWne Slo)
    (hγsU : γs ∈ KSubsetCollection.aboveMinProfile W hWne Shi)
    (hγsL : γs ∉ KSubsetCollection.aboveMinProfile W hWne Slo) :
    γs ∈ KSubsetCollection.frozenCoords W := by
  classical
  -- every wall profile is ⊆ profile Slo or ⊇ profile Shi
  have hstruct : ∀ S ∈ W,
      KSubsetCollection.aboveMinProfile W hWne S ⊆ KSubsetCollection.aboveMinProfile W hWne Slo
      ∨ KSubsetCollection.aboveMinProfile W hWne Shi ⊆ KSubsetCollection.aboveMinProfile W hWne S := by
    intro S hSA
    have hgapS := hgap S hSA
    rcases lt_or_ge (KSubsetCollection.aboveMinProfile W hWne S).card
        ((KSubsetCollection.aboveMinProfile W hWne Slo).card + 1) with hlt | hge0
    · refine Or.inl ?_
      have hle : (KSubsetCollection.aboveMinProfile W hWne S).card
          ≤ (KSubsetCollection.aboveMinProfile W hWne Slo).card := by omega
      rcases KSubsetCollection.aboveMinProfile_subset_or_superset hWsorted hWne hSA hSloA with h | h
      · exact h
      · exact (Finset.eq_of_subset_of_card_le h hle).ge
    · refine Or.inr ?_
      have hge : (KSubsetCollection.aboveMinProfile W hWne Shi).card
          ≤ (KSubsetCollection.aboveMinProfile W hWne S).card := by omega
      rcases KSubsetCollection.aboveMinProfile_subset_or_superset hWsorted hWne hSA hShiA with h | h
      · exact (Finset.eq_of_subset_of_card_le h hge).ge
      · exact h
  -- [γs ∈ S] = minPrefixCount(γs) − minPrefixCount(γ), constant across S
  have hδ : ∀ S ∈ W, (if γs ∈ S.1 then (1 : ℕ) else 0)
      = KSubsetCollection.minPrefixCount W hWne γs - KSubsetCollection.minPrefixCount W hWne γ := by
    intro S hSA
    have hpred := KSubset.prefixCount_pred S hγs
    have hγle := KSubsetCollection.minPrefixCount_le hWne hSA γ
    have hγsle := KSubsetCollection.minPrefixCount_le hWne hSA γs
    rcases hstruct S hSA with h | h
    · have hγS : γ ∉ KSubsetCollection.aboveMinProfile W hWne S := fun hc => hγL (h hc)
      have hγsS : γs ∉ KSubsetCollection.aboveMinProfile W hWne S := fun hc => hγsL (h hc)
      rw [KSubsetCollection.mem_aboveMinProfile_iff] at hγS hγsS
      push_neg at hγS hγsS
      omega
    · have hγS : γ ∈ KSubsetCollection.aboveMinProfile W hWne S := h hγU
      have hγsS : γs ∈ KSubsetCollection.aboveMinProfile W hWne S := h hγsU
      rw [KSubsetCollection.mem_aboveMinProfile_iff] at hγS hγsS
      have hγwo := KSubsetCollection.prefixCount_eq_min_or_min_add_one hWsorted hWne hSA γ
      have hγswo := KSubsetCollection.prefixCount_eq_min_or_min_add_one hWsorted hWne hSA γs
      omega
  rw [KSubsetCollection.frozenCoords, Finset.mem_union]
  by_cases hSlo : γs ∈ Slo.1
  · refine Or.inl ?_
    rw [KSubsetCollection.mem_commonPresent_iff]
    intro S hSA
    by_contra hSγs
    have e1 := hδ S hSA; have e2 := hδ Slo hSloA
    rw [if_neg hSγs] at e1; rw [if_pos hSlo] at e2
    omega
  · refine Or.inr ?_
    rw [KSubsetCollection.mem_commonAbsent_iff]
    intro S hSA hSγs
    have e1 := hδ S hSA; have e2 := hδ Slo hSloA
    rw [if_pos hSγs] at e1; rw [if_neg hSlo] at e2
    omega

/-- **Contrapositive.** A FROZEN-FREE punctured-interval interior wall has NO adjacent
gap pair: if the gap coordinates `γ, γ+1 = U \ L` were adjacent, the middle coordinate would be
frozen — contradicting `frozenCoords W = ∅`.  (This is the precise combinatorial fact that
unblocks the interior existence: the two gap coordinates are non-adjacent, hence — by the
descent analysis — both are descents of `Slo`, so `prefixCount_swapDescent` realises both
extensions.) -/
theorem KSubsetCollection.no_adjacent_gap_of_no_frozen_interior {n k : ℕ}
    {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W) (hWne : W.Nonempty)
    {Slo Shi : KSubset n k} (hSloA : Slo ∈ W) (hShiA : Shi ∈ W)
    (hUcard : (KSubsetCollection.aboveMinProfile W hWne Shi).card
        = (KSubsetCollection.aboveMinProfile W hWne Slo).card + 2)
    (hgap : ∀ S ∈ W, (KSubsetCollection.aboveMinProfile W hWne S).card
        ≠ (KSubsetCollection.aboveMinProfile W hWne Slo).card + 1)
    (hfrozen : (KSubsetCollection.frozenCoords W).card = 0)
    {γ γs : Fin n} (hγs : γ.val + 1 = γs.val)
    (hγU : γ ∈ KSubsetCollection.aboveMinProfile W hWne Shi)
    (hγL : γ ∉ KSubsetCollection.aboveMinProfile W hWne Slo)
    (hγsU : γs ∈ KSubsetCollection.aboveMinProfile W hWne Shi)
    (hγsL : γs ∉ KSubsetCollection.aboveMinProfile W hWne Slo) : False := by
  have hmem := KSubsetCollection.exists_frozenCoord_of_adjacent_interior_gap hWsorted hWne hSloA
    hShiA hUcard hgap hγs hγU hγL hγsU hγsL
  have : 0 < (KSubsetCollection.frozenCoords W).card := Finset.card_pos.mpr ⟨γs, hmem⟩
  omega

/-- Every wall profile is `⊆ aboveMinProfile Slo` or `⊇ aboveMinProfile Shi` (the rank
dichotomy from the spectrum gap at rank `|L|+1`).  Extracted for reuse by the descent-swap
construction. -/
theorem KSubsetCollection.wall_profile_subset_or_superset {n k : ℕ}
    {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W) (hWne : W.Nonempty)
    {Slo Shi : KSubset n k} (hSloA : Slo ∈ W) (hShiA : Shi ∈ W)
    (hUcard : (KSubsetCollection.aboveMinProfile W hWne Shi).card
        = (KSubsetCollection.aboveMinProfile W hWne Slo).card + 2)
    (hgap : ∀ S ∈ W, (KSubsetCollection.aboveMinProfile W hWne S).card
        ≠ (KSubsetCollection.aboveMinProfile W hWne Slo).card + 1)
    {S : KSubset n k} (hSA : S ∈ W) :
    KSubsetCollection.aboveMinProfile W hWne S ⊆ KSubsetCollection.aboveMinProfile W hWne Slo
    ∨ KSubsetCollection.aboveMinProfile W hWne Shi ⊆ KSubsetCollection.aboveMinProfile W hWne S := by
  have hgapS := hgap S hSA
  rcases lt_or_ge (KSubsetCollection.aboveMinProfile W hWne S).card
      ((KSubsetCollection.aboveMinProfile W hWne Slo).card + 1) with hlt | hge0
  · refine Or.inl ?_
    have hle : (KSubsetCollection.aboveMinProfile W hWne S).card
        ≤ (KSubsetCollection.aboveMinProfile W hWne Slo).card := by omega
    rcases KSubsetCollection.aboveMinProfile_subset_or_superset hWsorted hWne hSA hSloA with h | h
    · exact h
    · exact (Finset.eq_of_subset_of_card_le h hle).ge
  · refine Or.inr ?_
    have hge : (KSubsetCollection.aboveMinProfile W hWne Shi).card
        ≤ (KSubsetCollection.aboveMinProfile W hWne S).card := by omega
    rcases KSubsetCollection.aboveMinProfile_subset_or_superset hWsorted hWne hSA hShiA with h | h
    · exact (Finset.eq_of_subset_of_card_le h hge).ge
    · exact h

/-- The descent swap `(Slo.1 \ {γ+1}) ∪ {γ}` for a gap coordinate `γ`
that is a descent of `Slo` is an actual same-frame extension of `W`.  Compatibility with the
whole wall uses profile nesting (`wall_profile_subset_or_superset`) + the gap, NOT just band
membership. -/
theorem KSubsetCollection.descentSwap_isExtension {n k : ℕ}
    {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W) (hWne : W.Nonempty)
    (hWcard : W.card = n - 1) {Slo Shi : KSubset n k} (hSloA : Slo ∈ W) (hShiA : Shi ∈ W)
    (hLU : KSubsetCollection.aboveMinProfile W hWne Slo
        ⊆ KSubsetCollection.aboveMinProfile W hWne Shi)
    (hUcard : (KSubsetCollection.aboveMinProfile W hWne Shi).card
        = (KSubsetCollection.aboveMinProfile W hWne Slo).card + 2)
    (hgap : ∀ S ∈ W, (KSubsetCollection.aboveMinProfile W hWne S).card
        ≠ (KSubsetCollection.aboveMinProfile W hWne Slo).card + 1)
    {γ γs : Fin n} (hγs : γ.val + 1 = γs.val) (hγ : γ ∉ Slo.1) (hγs_in : γs ∈ Slo.1)
    (hγL : γ ∉ KSubsetCollection.aboveMinProfile W hWne Slo)
    (hγU : γ ∈ KSubsetCollection.aboveMinProfile W hWne Shi) :
    ∃ T : KSubset n k, T ∈ KSubsetCollection.sameFrameExtensions W ∧
      ∀ t, KSubset.prefixCount T t = KSubset.prefixCount Slo t + (if t = γ then 1 else 0) := by
  classical
  have hk1 : 1 ≤ k := by rw [← Slo.2]; exact Finset.card_pos.mpr ⟨γs, hγs_in⟩
  have hd : Disjoint (Slo.1 \ {γs}) ({γ} : Finset (Fin n)) := by
    rw [Finset.disjoint_singleton_right]; exact fun h => hγ (Finset.mem_sdiff.mp h).1
  have hcard : ((Slo.1 \ {γs}) ∪ {γ}).card = k := by
    rw [Finset.card_union_of_disjoint hd, Finset.card_singleton, ← Finset.erase_eq,
      Finset.card_erase_of_mem hγs_in, Slo.2]
    omega
  set T : KSubset n k := ⟨(Slo.1 \ {γs}) ∪ {γ}, hcard⟩ with hT
  have hpcT : ∀ t, KSubset.prefixCount T t
      = KSubset.prefixCount Slo t + (if t = γ then 1 else 0) :=
    fun t => KSubset.prefixCount_swapDescent Slo hγs hγ hγs_in t
  have hSloγ : KSubset.prefixCount Slo γ = KSubsetCollection.minPrefixCount W hWne γ := by
    have h1 := KSubsetCollection.minPrefixCount_le hWne hSloA γ
    by_contra hne
    exact hγL ((KSubsetCollection.mem_aboveMinProfile_iff W hWne Slo γ).mpr (by omega))
  have hprofT : KSubsetCollection.aboveMinProfile W hWne T
      = insert γ (KSubsetCollection.aboveMinProfile W hWne Slo) := by
    ext t
    simp only [KSubsetCollection.mem_aboveMinProfile_iff, Finset.mem_insert]
    rw [hpcT t]
    by_cases ht : t = γ
    · subst ht; rw [if_pos rfl, hSloγ]
      constructor
      · intro _; left; rfl
      · intro _; omega
    · rw [if_neg ht]
      constructor
      · intro h; right; omega
      · rintro (h | h)
        · exact absurd h ht
        · omega
  have hband : ∀ t, KSubsetCollection.minPrefixCount W hWne t ≤ KSubset.prefixCount T t
      ∧ KSubset.prefixCount T t ≤ KSubsetCollection.minPrefixCount W hWne t + 1 := by
    intro t
    have hlo := KSubsetCollection.minPrefixCount_le hWne hSloA t
    have hwo := KSubsetCollection.prefixCount_eq_min_or_min_add_one hWsorted hWne hSloA t
    rw [hpcT t]
    by_cases ht : t = γ
    · subst ht; rw [if_pos rfl, hSloγ]; omega
    · rw [if_neg ht]; omega
  have hcompat : ∀ S ∈ W, KSubset.IsSortedPair T S := by
    intro S hSA
    have hnest := KSubsetCollection.wall_profile_subset_or_superset hWsorted hWne hSloA hShiA
      hUcard hgap hSA
    have hTnest : KSubsetCollection.aboveMinProfile W hWne S
          ⊆ KSubsetCollection.aboveMinProfile W hWne T
        ∨ KSubsetCollection.aboveMinProfile W hWne T
          ⊆ KSubsetCollection.aboveMinProfile W hWne S := by
      rw [hprofT]
      rcases hnest with h | h
      · exact Or.inl (h.trans (Finset.subset_insert γ _))
      · exact Or.inr (by rw [Finset.insert_subset_iff]; exact ⟨h hγU, hLU.trans h⟩)
    rcases hTnest with h | h
    · refine Or.inl (fun t => ?_)
      have hbt := hband t
      have hbs := KSubsetCollection.prefixCount_eq_min_or_min_add_one hWsorted hWne hSA t
      have hSle := KSubsetCollection.minPrefixCount_le hWne hSA t
      by_cases hSt : t ∈ KSubsetCollection.aboveMinProfile W hWne S
      · have htT : t ∈ KSubsetCollection.aboveMinProfile W hWne T := h hSt
        rw [KSubsetCollection.mem_aboveMinProfile_iff] at hSt htT; omega
      · rw [KSubsetCollection.mem_aboveMinProfile_iff] at hSt; push_neg at hSt; omega
    · refine Or.inr (fun t => ?_)
      have hbt := hband t
      have hbs := KSubsetCollection.prefixCount_eq_min_or_min_add_one hWsorted hWne hSA t
      have hSle := KSubsetCollection.minPrefixCount_le hWne hSA t
      by_cases hTt : t ∈ KSubsetCollection.aboveMinProfile W hWne T
      · have htS : t ∈ KSubsetCollection.aboveMinProfile W hWne S := h hTt
        rw [KSubsetCollection.mem_aboveMinProfile_iff] at hTt htS; omega
      · rw [KSubsetCollection.mem_aboveMinProfile_iff] at hTt; push_neg at hTt; omega
  have hTnotin : T ∉ W := by
    intro hTW
    have hgapT := hgap T hTW
    rw [hprofT, Finset.card_insert_of_notMem hγL] at hgapT
    exact hgapT rfl
  refine ⟨T, ?_, hpcT⟩
  rw [KSubsetCollection.mem_sameFrameExtensions_iff]
  refine ⟨hTnotin, ?_, KSubsetCollection.isSorted_insert hWsorted (fun S hS => hcompat S hS)⟩
  rw [Finset.card_insert_of_notMem hTnotin, hWcard]
  have hWpos : 0 < W.card := Finset.card_pos.mpr hWne
  rw [hWcard] at hWpos
  omega

/-- The bottom coordinate (`γ.val = 0`), the prefix count is just the membership indicator. -/
theorem KSubset.prefixCount_eq_indicator_of_val_zero {n k : ℕ} (S : KSubset n k) {γ : Fin n}
    (hγ0 : γ.val = 0) : S.prefixCount γ = if γ ∈ S.1 then 1 else 0 := by
  classical
  rw [KSubset.prefixCount]
  have hpredeq : S.1.filter (· ≤ γ) = S.1.filter (· = γ) := by
    apply Finset.filter_congr
    intro x _
    rw [Fin.le_def, Fin.ext_iff]
    have := x.isLt; omega
  rw [hpredeq, Finset.filter_eq']
  split <;> simp

/-- **Descent bridge.** A gap coordinate `γ ∈ U \ L` whose successor `γ+1` and (if
present) predecessor `γ-1` are NOT themselves gap coordinates is a DESCENT of `Slo`
(`γ ∉ Slo.1`, `γ+1 ∈ Slo.1`).  In the assembly the two non-adjacency conditions come from
`no_adjacent_gap_of_no_frozen_interior`.  Uses `pc_Shi = pc_Slo + 1_{U\L}` + `Shi`-validity. -/
theorem KSubsetCollection.gap_coord_descent_of_interior {n k : ℕ}
    {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W) (hWne : W.Nonempty)
    {Slo Shi : KSubset n k} (hSloA : Slo ∈ W) (hShiA : Shi ∈ W)
    (hLU : KSubsetCollection.aboveMinProfile W hWne Slo
        ⊆ KSubsetCollection.aboveMinProfile W hWne Shi)
    {γ γs : Fin n} (hγs : γ.val + 1 = γs.val)
    (hγU : γ ∈ KSubsetCollection.aboveMinProfile W hWne Shi)
    (hγL : γ ∉ KSubsetCollection.aboveMinProfile W hWne Slo)
    (hγs_notUL : γs ∉ KSubsetCollection.aboveMinProfile W hWne Shi
        \ KSubsetCollection.aboveMinProfile W hWne Slo)
    (hpred_notUL : ∀ γp : Fin n, γp.val + 1 = γ.val →
        γp ∉ KSubsetCollection.aboveMinProfile W hWne Shi
          \ KSubsetCollection.aboveMinProfile W hWne Slo) :
    γ ∉ Slo.1 ∧ γs ∈ Slo.1 := by
  classical
  have hpc : ∀ (S : KSubset n k), S ∈ W → ∀ t,
      KSubset.prefixCount S t = KSubsetCollection.minPrefixCount W hWne t
        + (if t ∈ KSubsetCollection.aboveMinProfile W hWne S then 1 else 0) := by
    intro S hSA t
    have hwo := KSubsetCollection.prefixCount_eq_min_or_min_add_one hWsorted hWne hSA t
    by_cases h : t ∈ KSubsetCollection.aboveMinProfile W hWne S
    · rw [if_pos h]; rw [KSubsetCollection.mem_aboveMinProfile_iff] at h; omega
    · rw [if_neg h]; rw [KSubsetCollection.mem_aboveMinProfile_iff] at h; push_neg at h
      have := KSubsetCollection.minPrefixCount_le hWne hSA t; omega
  have keyγ : KSubset.prefixCount Shi γ = KSubset.prefixCount Slo γ + 1 := by
    rw [hpc Shi hShiA γ, hpc Slo hSloA γ, if_pos hγU, if_neg hγL]
  have hsame : ∀ δ : Fin n,
      δ ∉ KSubsetCollection.aboveMinProfile W hWne Shi
        \ KSubsetCollection.aboveMinProfile W hWne Slo →
      KSubset.prefixCount Shi δ = KSubset.prefixCount Slo δ := by
    intro δ hδ
    rw [hpc Shi hShiA δ, hpc Slo hSloA δ, Finset.mem_sdiff] at *
    push_neg at hδ
    by_cases h : δ ∈ KSubsetCollection.aboveMinProfile W hWne Shi
    · rw [if_pos h, if_pos (hδ h)]
    · rw [if_neg h, if_neg (fun hc => h (hLU hc))]
  refine ⟨?_, ?_⟩
  · by_contra hγSlo
    by_cases hγ0 : γ.val = 0
    · rw [KSubset.prefixCount_eq_indicator_of_val_zero Shi hγ0,
        KSubset.prefixCount_eq_indicator_of_val_zero Slo hγ0, if_pos hγSlo] at keyγ
      split at keyγ <;> omega
    · obtain ⟨γp, hγp⟩ : ∃ γp : Fin n, γp.val + 1 = γ.val :=
        ⟨⟨γ.val - 1, by have := γ.isLt; omega⟩, by show (γ.val - 1) + 1 = γ.val; omega⟩
      have hpredγ_Shi := KSubset.prefixCount_pred Shi hγp
      have hpredγ_Slo := KSubset.prefixCount_pred Slo hγp
      have keyγp := hsame γp (hpred_notUL γp hγp)
      rw [if_pos hγSlo] at hpredγ_Slo
      split at hpredγ_Shi <;> omega
  · by_contra hγsSlo
    have hpredγs_Slo := KSubset.prefixCount_pred Slo hγs
    have hpredγs_Shi := KSubset.prefixCount_pred Shi hγs
    have keyγs := hsame γs hγs_notUL
    rw [if_neg hγsSlo] at hpredγs_Slo
    split at hpredγs_Shi <;> omega

/-- **THE INTERIOR LOWER BOUND:** a punctured-interval interior wall with NO frozen coordinate
has at least two same-frame extensions.  Assembles the crux (`no_adjacent_gap…`: the two gap
coordinates are non-adjacent), the descent bridge (`gap_coord_descent…`: both are descents of
`Slo`), and the construction (`descentSwap_isExtension`: each descent yields an extension), with
distinctness from the differing profiles. -/
theorem KSubsetCollection.sameFrameExtensions_two_of_no_frozen_interior {n k : ℕ}
    {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W) (hWne : W.Nonempty)
    (hWcard : W.card = n - 1) {Slo Shi : KSubset n k} (hSloA : Slo ∈ W) (hShiA : Shi ∈ W)
    (hLU : KSubsetCollection.aboveMinProfile W hWne Slo
        ⊆ KSubsetCollection.aboveMinProfile W hWne Shi)
    (hUcard : (KSubsetCollection.aboveMinProfile W hWne Shi).card
        = (KSubsetCollection.aboveMinProfile W hWne Slo).card + 2)
    (hgap : ∀ S ∈ W, (KSubsetCollection.aboveMinProfile W hWne S).card
        ≠ (KSubsetCollection.aboveMinProfile W hWne Slo).card + 1)
    (hfrozen : (KSubsetCollection.frozenCoords W).card = 0) :
    2 ≤ (KSubsetCollection.sameFrameExtensions W).card := by
  classical
  set U := KSubsetCollection.aboveMinProfile W hWne Shi with hUdef
  set L := KSubsetCollection.aboveMinProfile W hWne Slo with hLdef
  -- |U \ L| = 2
  have hUL2 : (U \ L).card = 2 := by
    have hdisj : Disjoint L (U \ L) :=
      Finset.disjoint_left.mpr (fun a haL haUL => (Finset.mem_sdiff.mp haUL).2 haL)
    have hc := Finset.card_union_of_disjoint hdisj
    rw [Finset.union_sdiff_of_subset hLU] at hc; omega
  obtain ⟨γ₁, γ₂, hne12, hUL_eq⟩ := Finset.card_eq_two.mp hUL2
  have hγ₁ : γ₁ ∈ U \ L := by rw [hUL_eq]; exact Finset.mem_insert_self _ _
  have hγ₂ : γ₂ ∈ U \ L := by rw [hUL_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  -- top coordinate of `U` has a valid successor
  have hUlt : ∀ a ∈ U, a.val + 1 < n := by
    intro a ha
    rw [hUdef, KSubsetCollection.mem_aboveMinProfile_iff] at ha
    by_contra hge
    have hatop : ∀ j : Fin n, j ≤ a := fun j => by
      rw [Fin.le_def]; have := j.isLt; have := a.isLt; omega
    rw [prefixCount_top_eq Shi hatop, minPrefixCount_top_eq hWne hatop] at ha
    omega
  -- non-adjacency of the gap coordinates
  have hnoadj : ∀ a b : Fin n, a ∈ U \ L → b ∈ U \ L → a.val + 1 ≠ b.val := by
    intro a b ha hb hadj
    rw [Finset.mem_sdiff] at ha hb
    exact KSubsetCollection.no_adjacent_gap_of_no_frozen_interior hWsorted hWne hSloA hShiA hUcard
      hgap hfrozen hadj ha.1 ha.2 hb.1 hb.2
  -- build an extension from each gap coordinate
  have hbuild : ∀ γ γ' : Fin n, γ ∈ U \ L → γ' ∈ U \ L → U \ L = {γ, γ'} →
      ∃ T : KSubset n k, T ∈ KSubsetCollection.sameFrameExtensions W ∧
        ∀ t, KSubset.prefixCount T t = KSubset.prefixCount Slo t + (if t = γ then 1 else 0) := by
    intro γ γ' hγ hγ' hpair
    have hγU : γ ∈ U := (Finset.mem_sdiff.mp hγ).1
    have hγL : γ ∉ L := (Finset.mem_sdiff.mp hγ).2
    set γs : Fin n := ⟨γ.val + 1, hUlt γ hγU⟩ with hγsdef
    have hγs_eq : γ.val + 1 = γs.val := rfl
    have hγs_notUL : γs ∉ U \ L := by
      intro hmem
      rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · have := congrArg Fin.val h; omega
      · exact hnoadj γ γ' hγ hγ' (by rw [hγs_eq, h])
    have hpred_notUL : ∀ γp : Fin n, γp.val + 1 = γ.val → γp ∉ U \ L := by
      intro γp hγp hmem
      rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · rw [h] at hγp; omega
      · exact hnoadj γ' γ hγ' hγ (by rw [h] at hγp; exact hγp)
    have hdesc := KSubsetCollection.gap_coord_descent_of_interior hWsorted hWne hSloA hShiA hLU
      hγs_eq hγU hγL hγs_notUL hpred_notUL
    exact KSubsetCollection.descentSwap_isExtension hWsorted hWne hWcard hSloA hShiA hLU hUcard
      hgap hγs_eq hdesc.1 hdesc.2 hγL hγU
  obtain ⟨T₁, hT₁mem, hT₁pc⟩ := hbuild γ₁ γ₂ hγ₁ hγ₂ hUL_eq
  obtain ⟨T₂, hT₂mem, hT₂pc⟩ := hbuild γ₂ γ₁ hγ₂ hγ₁ (hUL_eq.trans (Finset.pair_comm γ₁ γ₂))
  have hT12 : T₁ ≠ T₂ := by
    intro h
    have h1 := hT₁pc γ₁
    have h2 := hT₂pc γ₁
    rw [if_pos rfl] at h1
    rw [if_neg hne12] at h2
    rw [h] at h1
    omega
  have hsub : ({T₁, T₂} : Finset (KSubset n k)) ⊆ KSubsetCollection.sameFrameExtensions W := by
    intro X hX
    rw [Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl
    · exact hT₁mem
    · exact hT₂mem
  calc 2 = ({T₁, T₂} : Finset (KSubset n k)).card := (Finset.card_pair hT12).symm
    _ ≤ (KSubsetCollection.sameFrameExtensions W).card := Finset.card_le_card hsub

/-- **`c = 1` UP-SIDE, case (a) — interior missing rank, NON-adjacent gap.**  A codim-1 sorted wall
with an interior rank gap (`Slo, Shi` of profile cards `r, r+2`, no member of card `r+1`) whose two
gap coordinates are NON-adjacent has a same-frame extension.  NO frozen-free hypothesis: this reuses
the frozen-free-INDEPENDENT `gap_coord_descent_of_interior` + `descentSwap_isExtension`, with
non-adjacency supplied as the explicit hypothesis `hnoadj` (which the frozen-free interior lemma
instead derived from `frozenCoords = ∅`).  For the geometric `c = 1` case the wall is common-absent
one-frozen and this is the non-adjacent-gap branch of the missing-rank dispatch. -/
theorem KSubsetCollection.sameFrameExtensions_nonempty_of_interior_nonadjacent_gap {n k : ℕ}
    {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W) (hWne : W.Nonempty)
    (hWcard : W.card = n - 1) {Slo Shi : KSubset n k} (hSloA : Slo ∈ W) (hShiA : Shi ∈ W)
    (hLU : KSubsetCollection.aboveMinProfile W hWne Slo
        ⊆ KSubsetCollection.aboveMinProfile W hWne Shi)
    (hUcard : (KSubsetCollection.aboveMinProfile W hWne Shi).card
        = (KSubsetCollection.aboveMinProfile W hWne Slo).card + 2)
    (hgap : ∀ S ∈ W, (KSubsetCollection.aboveMinProfile W hWne S).card
        ≠ (KSubsetCollection.aboveMinProfile W hWne Slo).card + 1)
    (hnoadj : ∀ a b : Fin n,
        a ∈ KSubsetCollection.aboveMinProfile W hWne Shi
          \ KSubsetCollection.aboveMinProfile W hWne Slo →
        b ∈ KSubsetCollection.aboveMinProfile W hWne Shi
          \ KSubsetCollection.aboveMinProfile W hWne Slo → a.val + 1 ≠ b.val) :
    (KSubsetCollection.sameFrameExtensions W).Nonempty := by
  classical
  set U := KSubsetCollection.aboveMinProfile W hWne Shi with hUdef
  set L := KSubsetCollection.aboveMinProfile W hWne Slo with hLdef
  have hUL2 : (U \ L).card = 2 := by
    have hdisj : Disjoint L (U \ L) :=
      Finset.disjoint_left.mpr (fun a haL haUL => (Finset.mem_sdiff.mp haUL).2 haL)
    have hc := Finset.card_union_of_disjoint hdisj
    rw [Finset.union_sdiff_of_subset hLU] at hc; omega
  obtain ⟨γ₁, γ₂, hne12, hUL_eq⟩ := Finset.card_eq_two.mp hUL2
  have hγ₁ : γ₁ ∈ U \ L := by rw [hUL_eq]; exact Finset.mem_insert_self _ _
  have hγ₂ : γ₂ ∈ U \ L := by
    rw [hUL_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hUlt : ∀ a ∈ U, a.val + 1 < n := by
    intro a ha
    rw [hUdef, KSubsetCollection.mem_aboveMinProfile_iff] at ha
    by_contra hge
    have hatop : ∀ j : Fin n, j ≤ a := fun j => by
      rw [Fin.le_def]; have := j.isLt; have := a.isLt; omega
    rw [prefixCount_top_eq Shi hatop, minPrefixCount_top_eq hWne hatop] at ha
    omega
  have hγU : γ₁ ∈ U := (Finset.mem_sdiff.mp hγ₁).1
  have hγL : γ₁ ∉ L := (Finset.mem_sdiff.mp hγ₁).2
  set γs : Fin n := ⟨γ₁.val + 1, hUlt γ₁ hγU⟩ with hγsdef
  have hγs_eq : γ₁.val + 1 = γs.val := rfl
  have hγs_notUL : γs ∉ U \ L := by
    intro hmem
    rw [hUL_eq, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · have := congrArg Fin.val h; omega
    · exact hnoadj γ₁ γ₂ hγ₁ hγ₂ (by rw [hγs_eq, h])
  have hpred_notUL : ∀ γp : Fin n, γp.val + 1 = γ₁.val → γp ∉ U \ L := by
    intro γp hγp hmem
    rw [hUL_eq, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · rw [h] at hγp; omega
    · exact hnoadj γ₂ γ₁ hγ₂ hγ₁ (by rw [h] at hγp; exact hγp)
  have hdesc := KSubsetCollection.gap_coord_descent_of_interior hWsorted hWne hSloA hShiA hLU
    hγs_eq hγU hγL hγs_notUL hpred_notUL
  obtain ⟨T, hTmem, _⟩ := KSubsetCollection.descentSwap_isExtension hWsorted hWne hWcard hSloA hShiA
    hLU hUcard hgap hγs_eq hdesc.1 hdesc.2 hγL hγU
  exact ⟨T, hTmem⟩

/-- **Adjacent case — identify the frozen coordinate.**  In the interior adjacent-gap
configuration the UPPER gap coordinate `γs` (`= γ + 1`) is frozen
(`exists_frozenCoord_of_adjacent_interior_gap`).  If additionally the wall has EXACTLY ONE frozen
coordinate and a common-absent coordinate `c`, then `γs = c` (both lie in the singleton
`frozenCoords W`). -/
theorem KSubsetCollection.adjacent_gap_middle_eq_commonAbsent_frozen {n k : ℕ}
    {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W) (hWne : W.Nonempty)
    {Slo Shi : KSubset n k} (hSloA : Slo ∈ W) (hShiA : Shi ∈ W)
    (hUcard : (KSubsetCollection.aboveMinProfile W hWne Shi).card
        = (KSubsetCollection.aboveMinProfile W hWne Slo).card + 2)
    (hgap : ∀ S ∈ W, (KSubsetCollection.aboveMinProfile W hWne S).card
        ≠ (KSubsetCollection.aboveMinProfile W hWne Slo).card + 1)
    {γ γs c : Fin n} (hγs : γ.val + 1 = γs.val)
    (hγU : γ ∈ KSubsetCollection.aboveMinProfile W hWne Shi)
    (hγL : γ ∉ KSubsetCollection.aboveMinProfile W hWne Slo)
    (hγsU : γs ∈ KSubsetCollection.aboveMinProfile W hWne Shi)
    (hγsL : γs ∉ KSubsetCollection.aboveMinProfile W hWne Slo)
    (hcabs : c ∈ KSubsetCollection.commonAbsent W)
    (hone : (KSubsetCollection.frozenCoords W).card = 1) :
    γs = c := by
  classical
  have hγsfroz : γs ∈ KSubsetCollection.frozenCoords W :=
    KSubsetCollection.exists_frozenCoord_of_adjacent_interior_gap hWsorted hWne hSloA hShiA hUcard
      hgap hγs hγU hγL hγsU hγsL
  have hcfroz : c ∈ KSubsetCollection.frozenCoords W := by
    rw [KSubsetCollection.frozenCoords, Finset.mem_union]; exact Or.inr hcabs
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hone
  rw [hx, Finset.mem_singleton] at hγsfroz hcfroz
  rw [hγsfroz, hcfroz]

/-- **Adjacent case — the forced descent.**  The descent for the adjacent gap is at the
UPPER gap coordinate `γs` (the common-absent frozen one): the swap removes its successor
`γss = γs + 1`.  The two descent conditions are `γs ∉ Slo.1` (because `γs` is common-absent) and
`γss ∈ Slo.1`.  The latter is FORCED by the prefix-count step relation between `Slo` and `Shi`:
since `γs ∈ U \ L` contributes `pc_Shi(γs) = pc_Slo(γs) + 1` while `γss ∉ U \ L` is flat
(`pc_Shi(γss) = pc_Slo(γss)`), we get `[γss ∈ Slo.1] = [γss ∈ Shi.1] + 1`, hence `= 1`. -/
theorem KSubsetCollection.adjacent_gap_descent_at_frozen_middle {n k : ℕ}
    {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W) (hWne : W.Nonempty)
    {Slo Shi : KSubset n k} (hSloA : Slo ∈ W) (hShiA : Shi ∈ W)
    (hLU : KSubsetCollection.aboveMinProfile W hWne Slo
        ⊆ KSubsetCollection.aboveMinProfile W hWne Shi)
    {γs γss : Fin n} (hγss : γs.val + 1 = γss.val)
    (hγsU : γs ∈ KSubsetCollection.aboveMinProfile W hWne Shi)
    (hγsL : γs ∉ KSubsetCollection.aboveMinProfile W hWne Slo)
    (hγss_notUL : γss ∉ KSubsetCollection.aboveMinProfile W hWne Shi
        \ KSubsetCollection.aboveMinProfile W hWne Slo)
    (hγs_cabs : γs ∈ KSubsetCollection.commonAbsent W) :
    γs ∉ Slo.1 ∧ γss ∈ Slo.1 := by
  classical
  refine ⟨(KSubsetCollection.mem_commonAbsent_iff W γs).mp hγs_cabs Slo hSloA, ?_⟩
  have hpc : ∀ (S : KSubset n k), S ∈ W → ∀ t,
      KSubset.prefixCount S t = KSubsetCollection.minPrefixCount W hWne t
        + (if t ∈ KSubsetCollection.aboveMinProfile W hWne S then 1 else 0) := by
    intro S hSA t
    have hwo := KSubsetCollection.prefixCount_eq_min_or_min_add_one hWsorted hWne hSA t
    by_cases h : t ∈ KSubsetCollection.aboveMinProfile W hWne S
    · rw [if_pos h]; rw [KSubsetCollection.mem_aboveMinProfile_iff] at h; omega
    · rw [if_neg h]; rw [KSubsetCollection.mem_aboveMinProfile_iff] at h; push_neg at h
      have := KSubsetCollection.minPrefixCount_le hWne hSA t; omega
  have keyγs : KSubset.prefixCount Shi γs = KSubset.prefixCount Slo γs + 1 := by
    rw [hpc Shi hShiA γs, hpc Slo hSloA γs, if_pos hγsU, if_neg hγsL]
  have hsameγss : KSubset.prefixCount Shi γss = KSubset.prefixCount Slo γss := by
    rw [hpc Shi hShiA γss, hpc Slo hSloA γss]
    rw [Finset.mem_sdiff] at hγss_notUL
    push_neg at hγss_notUL
    by_cases h : γss ∈ KSubsetCollection.aboveMinProfile W hWne Shi
    · rw [if_pos h, if_pos (hγss_notUL h)]
    · rw [if_neg h, if_neg (fun hc => h (hLU hc))]
  have hpredSlo := KSubset.prefixCount_pred Slo hγss
  have hpredShi := KSubset.prefixCount_pred Shi hγss
  by_contra hγssSlo
  rw [if_neg hγssSlo] at hpredSlo
  split at hpredShi <;> omega

/-- **`c = 1` UP-SIDE, case (b) — interior missing rank, ADJACENT gap.**  The last up-side
sub-case.  The gap `U \ L = {γ, γs}` is adjacent (`γs = γ + 1`); by
`exists_frozenCoord_of_adjacent_interior_gap` the upper coordinate `γs` is the unique
common-absent frozen coordinate `c` (`adjacent_gap_middle_eq_commonAbsent_frozen`).  The same-frame
extension is the descent swap at `γs` (removing `γs + 1`), valid because `γs ∉ Slo.1` (common-absent)
and `γs + 1 ∈ Slo.1` (the forced step relation, `adjacent_gap_descent_at_frozen_middle`).  This
completes the four-case missing-rank dispatch for the `c = 1` up-side existence. -/
theorem KSubsetCollection.sameFrameExtensions_nonempty_of_commonAbsent_oneFrozen_interior_adjacent
    {n k : ℕ} {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W)
    (hWne : W.Nonempty) (hWcard : W.card = n - 1) {Slo Shi : KSubset n k}
    (hSloA : Slo ∈ W) (hShiA : Shi ∈ W)
    (hLU : KSubsetCollection.aboveMinProfile W hWne Slo
        ⊆ KSubsetCollection.aboveMinProfile W hWne Shi)
    (hUcard : (KSubsetCollection.aboveMinProfile W hWne Shi).card
        = (KSubsetCollection.aboveMinProfile W hWne Slo).card + 2)
    (hgap : ∀ S ∈ W, (KSubsetCollection.aboveMinProfile W hWne S).card
        ≠ (KSubsetCollection.aboveMinProfile W hWne Slo).card + 1)
    {γ γs : Fin n} (hγs : γ.val + 1 = γs.val)
    (hγU : γ ∈ KSubsetCollection.aboveMinProfile W hWne Shi)
    (hγL : γ ∉ KSubsetCollection.aboveMinProfile W hWne Slo)
    (hγsU : γs ∈ KSubsetCollection.aboveMinProfile W hWne Shi)
    (hγsL : γs ∉ KSubsetCollection.aboveMinProfile W hWne Slo)
    {c : Fin n} (hcabs : c ∈ KSubsetCollection.commonAbsent W)
    (hone : (KSubsetCollection.frozenCoords W).card = 1) :
    (KSubsetCollection.sameFrameExtensions W).Nonempty := by
  classical
  -- the upper gap coordinate is the unique common-absent frozen coordinate
  have hγsc : γs = c :=
    KSubsetCollection.adjacent_gap_middle_eq_commonAbsent_frozen hWsorted hWne hSloA hShiA hUcard
      hgap hγs hγU hγL hγsU hγsL hcabs hone
  have hγs_cabs : γs ∈ KSubsetCollection.commonAbsent W := by rw [hγsc]; exact hcabs
  -- the successor of `γs` is a valid coordinate (a profile member is never the top)
  have hγss_lt : γs.val + 1 < n := by
    by_contra hge
    have hatop : ∀ j : Fin n, j ≤ γs := fun j => by
      rw [Fin.le_def]; have := j.isLt; have := γs.isLt; omega
    have hlt := (KSubsetCollection.mem_aboveMinProfile_iff W hWne Shi γs).mp hγsU
    rw [prefixCount_top_eq Shi hatop, minPrefixCount_top_eq hWne hatop] at hlt
    omega
  set γss : Fin n := ⟨γs.val + 1, hγss_lt⟩ with hγssdef
  have hγss_eq : γs.val + 1 = γss.val := rfl
  -- `U \ L = {γ, γs}`, so its non-member `γss` (`= γs + 1`) lies outside the gap
  have hUL2 : (KSubsetCollection.aboveMinProfile W hWne Shi
      \ KSubsetCollection.aboveMinProfile W hWne Slo).card = 2 := by
    have hdisj : Disjoint (KSubsetCollection.aboveMinProfile W hWne Slo)
        (KSubsetCollection.aboveMinProfile W hWne Shi
          \ KSubsetCollection.aboveMinProfile W hWne Slo) :=
      Finset.disjoint_left.mpr (fun a haL haUL => (Finset.mem_sdiff.mp haUL).2 haL)
    have hcU := Finset.card_union_of_disjoint hdisj
    rw [Finset.union_sdiff_of_subset hLU] at hcU; omega
  have hγγs : γ ≠ γs := fun h => by rw [h] at hγs; omega
  have hpairsub : ({γ, γs} : Finset (Fin n))
      ⊆ KSubsetCollection.aboveMinProfile W hWne Shi
        \ KSubsetCollection.aboveMinProfile W hWne Slo := by
    intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_sdiff.mpr ⟨hγU, hγL⟩
    · exact Finset.mem_sdiff.mpr ⟨hγsU, hγsL⟩
  have hUL_eq : KSubsetCollection.aboveMinProfile W hWne Shi
      \ KSubsetCollection.aboveMinProfile W hWne Slo = {γ, γs} :=
    (Finset.eq_of_subset_of_card_le hpairsub
      (le_of_eq (by rw [hUL2, Finset.card_pair hγγs]))).symm
  have hγss_notUL : γss ∉ KSubsetCollection.aboveMinProfile W hWne Shi
      \ KSubsetCollection.aboveMinProfile W hWne Slo := by
    rw [hUL_eq, Finset.mem_insert, Finset.mem_singleton]
    push_neg
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := congrArg Fin.val h; omega
    · have := congrArg Fin.val h; omega
  have hdesc := KSubsetCollection.adjacent_gap_descent_at_frozen_middle hWsorted hWne hSloA hShiA
    hLU hγss_eq hγsU hγsL hγss_notUL hγs_cabs
  obtain ⟨T, hTmem, _⟩ := KSubsetCollection.descentSwap_isExtension hWsorted hWne hWcard hSloA hShiA
    hLU hUcard hgap hγss_eq hdesc.1 hdesc.2 hγsL hγsU
  exact ⟨T, hTmem⟩

/-! ### Endpoint case — the refill and exterior extensions

For the endpoint case (`W = C.erase S₀` with `S₀` a weight-endpoint of the maximal `C`, so `W.image`
is consecutive), the two same-frame extensions are the refill (`S₀` re-inserted) and an exterior one
at a weight beyond the band — a rank-`(n-1)` (above) or rank-`0` (below/dip) profile element.
`frozenCoords W = ∅` makes its prefix-count profile valid via the boundary facts
`minPrefixCount(0) = 0` and `minPrefixCount(last-1) = k-1`. -/

/-- The REFILL extension: re-inserting the erased endpoint vertex `S₀` is a same-frame extension
of `C.erase S₀` (it rebuilds the maximal `C`).  Trivial; the substantive endpoint extension is
the exterior. -/
theorem KSubsetCollection.endpoint_refill_mem_sameFrameExtensions {n k : ℕ}
    {C : Finset (KSubset n k)} (hC : KSubsetCollection.IsMaximalSorted C) {S₀ : KSubset n k}
    (hS₀ : S₀ ∈ C) : S₀ ∈ KSubsetCollection.sameFrameExtensions (C.erase S₀) := by
  rw [KSubsetCollection.mem_sameFrameExtensions_iff]
  refine ⟨Finset.notMem_erase S₀ C, ?_⟩
  rwa [Finset.insert_erase hS₀]

/-- CRUX INGREDIENT (frozen-free, bottom): if no coordinate is common-present, the wall minimum
prefix count at the bottom coordinate is `0`. -/
theorem KSubsetCollection.minPrefixCount_bot_eq_zero {n k : ℕ} {W : Finset (KSubset n k)}
    (hWne : W.Nonempty) {z : Fin n} (hz : z.val = 0)
    (hcp : KSubsetCollection.commonPresent W = ∅) :
    KSubsetCollection.minPrefixCount W hWne z = 0 := by
  classical
  have hne : ¬ (∀ S ∈ W, z ∈ S.1) := by
    intro h
    have hmem : z ∈ KSubsetCollection.commonPresent W :=
      (KSubsetCollection.mem_commonPresent_iff W z).mpr h
    rw [hcp] at hmem; exact absurd hmem (Finset.notMem_empty z)
  push_neg at hne
  obtain ⟨S, hSW, hSz⟩ := hne
  have hpc : KSubset.prefixCount S z = 0 := by
    rw [KSubset.prefixCount_eq_indicator_of_val_zero S hz, if_neg hSz]
  have := KSubsetCollection.minPrefixCount_le hWne hSW z
  omega

/-- CRUX INGREDIENT (frozen-free, top−1): if no coordinate is common-absent, the wall minimum
prefix count just below the top coordinate is `k − 1`. -/
theorem KSubsetCollection.minPrefixCount_predTop_eq {n k : ℕ} {W : Finset (KSubset n k)}
    (hWne : W.Nonempty) {top ptop : Fin n} (htop : ∀ j : Fin n, j ≤ top)
    (hpt : ptop.val + 1 = top.val) (htna : top ∉ KSubsetCollection.commonAbsent W) :
    KSubsetCollection.minPrefixCount W hWne ptop = k - 1 := by
  classical
  have hpcform : ∀ S ∈ W, KSubset.prefixCount S ptop = k - (if top ∈ S.1 then 1 else 0) := by
    intro S hSW
    have h1 := KSubset.prefixCount_pred S hpt
    rw [prefixCount_top_eq S htop] at h1
    omega
  have hne : ¬ (∀ S ∈ W, top ∉ S.1) :=
    fun h => htna ((KSubsetCollection.mem_commonAbsent_iff W top).mpr h)
  push_neg at hne
  obtain ⟨S, hSW, hStop⟩ := hne
  have hle : KSubsetCollection.minPrefixCount W hWne ptop ≤ k - 1 := by
    have hsle := KSubsetCollection.minPrefixCount_le hWne hSW ptop
    rw [hpcform S hSW, if_pos hStop] at hsle; omega
  have hge : k - 1 ≤ KSubsetCollection.minPrefixCount W hWne ptop := by
    apply Finset.le_min'
    intro x hx
    obtain ⟨S, hSW, rfl⟩ := Finset.mem_image.mp hx
    rw [hpcform S hSW]; split <;> omega
  omega

/-- The wall minimum prefix count is monotone with `0/1` steps: across a single coordinate step
the minimum increases by `0` or `1`.  (A general fact about pointwise minima of prefix counts —
no sortedness needed; the achieving subset supplies each bound.) -/
theorem KSubsetCollection.minPrefixCount_step {n k : ℕ} {W : Finset (KSubset n k)}
    (hWne : W.Nonempty) {jp j : Fin n} (h : jp.val + 1 = j.val) :
    KSubsetCollection.minPrefixCount W hWne jp ≤ KSubsetCollection.minPrefixCount W hWne j ∧
      KSubsetCollection.minPrefixCount W hWne j
        ≤ KSubsetCollection.minPrefixCount W hWne jp + 1 := by
  classical
  refine ⟨?_, ?_⟩
  · obtain ⟨Sj, hSjW, hSjeq⟩ := Finset.mem_image.mp
      (Finset.min'_mem _ (hWne.image (fun S => KSubset.prefixCount S j)))
    have hmin_j : KSubset.prefixCount Sj j = KSubsetCollection.minPrefixCount W hWne j := hSjeq
    have hpcle : KSubset.prefixCount Sj jp ≤ KSubset.prefixCount Sj j := by
      rw [KSubset.prefixCount_pred Sj h]; omega
    calc KSubsetCollection.minPrefixCount W hWne jp
        ≤ KSubset.prefixCount Sj jp := KSubsetCollection.minPrefixCount_le hWne hSjW jp
      _ ≤ KSubset.prefixCount Sj j := hpcle
      _ = KSubsetCollection.minPrefixCount W hWne j := hmin_j
  · obtain ⟨Sjp, hSjpW, hSjpeq⟩ := Finset.mem_image.mp
      (Finset.min'_mem _ (hWne.image (fun S => KSubset.prefixCount S jp)))
    have hmin_jp : KSubset.prefixCount Sjp jp = KSubsetCollection.minPrefixCount W hWne jp := hSjpeq
    have hstep : KSubset.prefixCount Sjp j ≤ KSubset.prefixCount Sjp jp + 1 := by
      rw [KSubset.prefixCount_pred Sjp h]; split <;> omega
    calc KSubsetCollection.minPrefixCount W hWne j
        ≤ KSubset.prefixCount Sjp j := KSubsetCollection.minPrefixCount_le hWne hSjpW j
      _ ≤ KSubset.prefixCount Sjp jp + 1 := hstep
      _ = KSubsetCollection.minPrefixCount W hWne jp + 1 := by rw [hmin_jp]

/-! ### Prefix-count realization: turning a `0/1`-step path into a `k`-subset

A function `p : Fin n → ℕ` with `0/1` steps (each `p j` equals its predecessor value, or one more)
is the prefix-count of the subset of coordinates where `p` jumps.  This is the existence half
needed to realise the endpoint-exterior profile as an actual `k`-subset. -/

/-- `p` evaluated at the predecessor coordinate of `j` (or `0` at the bottom coordinate). -/
def KSubset.predValue {n : ℕ} (p : Fin n → ℕ) (j : Fin n) : ℕ :=
  if j.val = 0 then 0 else p ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le j.val 1) j.isLt⟩

/-- The coordinates where the path `p` jumps by one — the subset realising `p`. -/
def KSubset.ofPrefixJumps {n : ℕ} (p : Fin n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j => p j = KSubset.predValue p j + 1

theorem KSubset.mem_ofPrefixJumps {n : ℕ} (p : Fin n → ℕ) (j : Fin n) :
    j ∈ KSubset.ofPrefixJumps p ↔ p j = KSubset.predValue p j + 1 := by
  simp [KSubset.ofPrefixJumps]

/-- REALIZATION: under the `0/1`-step hypothesis, the prefix count of `ofPrefixJumps p` below any
threshold `t` is exactly `p t`. -/
theorem KSubset.card_filter_le_ofPrefixJumps {n : ℕ} (p : Fin n → ℕ)
    (hstep : ∀ j : Fin n, p j = KSubset.predValue p j ∨ p j = KSubset.predValue p j + 1)
    (t : Fin n) :
    ((KSubset.ofPrefixJumps p).filter (· ≤ t)).card = p t := by
  classical
  suffices H : ∀ m : ℕ, ∀ t : Fin n, t.val = m →
      ((KSubset.ofPrefixJumps p).filter (· ≤ t)).card = p t by
    exact H t.val t rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro t ht
    by_cases hm0 : t.val = 0
    · have hbot : (KSubset.ofPrefixJumps p).filter (· ≤ t)
          = (KSubset.ofPrefixJumps p).filter (· = t) := by
        apply Finset.filter_congr
        intro x _
        rw [Fin.le_def, Fin.ext_iff]
        omega
      rw [hbot, Finset.filter_eq']
      have hpv0 : KSubset.predValue p t = 0 := by rw [KSubset.predValue, if_pos hm0]
      have hmem : (t ∈ KSubset.ofPrefixJumps p) ↔ p t = 1 := by
        rw [KSubset.mem_ofPrefixJumps, hpv0]
      rcases hstep t with h | h
      · rw [hpv0] at h
        rw [if_neg (by rw [hmem]; omega), Finset.card_empty]; omega
      · rw [hpv0] at h
        rw [if_pos (by rw [hmem]; omega), Finset.card_singleton]; omega
    · have htp_lt : t.val - 1 < n := lt_of_le_of_lt (Nat.sub_le t.val 1) t.isLt
      set tp : Fin n := ⟨t.val - 1, htp_lt⟩ with htp_def
      have htpval : tp.val = t.val - 1 := by rw [htp_def]
      have hsplit : ((KSubset.ofPrefixJumps p).filter (· ≤ t)).card
          = ((KSubset.ofPrefixJumps p).filter (· ≤ tp)).card
            + (if t ∈ KSubset.ofPrefixJumps p then 1 else 0) := by
        rw [filter_le_card_eq (KSubset.ofPrefixJumps p) t]
        have hflt : (KSubset.ofPrefixJumps p).filter (· < t)
            = (KSubset.ofPrefixJumps p).filter (· ≤ tp) := by
          apply Finset.filter_congr
          intro x _
          rw [Fin.lt_def, Fin.le_def]
          omega
        rw [hflt]
      have hpv : KSubset.predValue p t = p tp := by
        rw [KSubset.predValue, if_neg hm0]
      have hmem : (t ∈ KSubset.ofPrefixJumps p) ↔ (p t = p tp + 1) := by
        rw [KSubset.mem_ofPrefixJumps, hpv]
      have hIHtp : ((KSubset.ofPrefixJumps p).filter (· ≤ tp)).card = p tp :=
        IH tp.val (by omega) tp rfl
      have hstept : p t = p tp ∨ p t = p tp + 1 := by
        rcases hstep t with hh | hh
        · left; rw [← hpv]; exact hh
        · right; rw [← hpv]; exact hh
      rw [hsplit, hIHtp]
      by_cases hc : p t = p tp + 1
      · rw [if_pos (hmem.mpr hc)]; omega
      · rw [if_neg (fun hh => hc (hmem.mp hh))]
        rcases hstept with hh | hh
        · omega
        · exact absurd hh hc

/-- The cardinality of the realising subset is the path's value at the top coordinate. -/
theorem KSubset.card_ofPrefixJumps {n : ℕ} (p : Fin n → ℕ)
    (hstep : ∀ j : Fin n, p j = KSubset.predValue p j ∨ p j = KSubset.predValue p j + 1)
    {top : Fin n} (htop : ∀ j : Fin n, j ≤ top) :
    (KSubset.ofPrefixJumps p).card = p top := by
  have heq := KSubset.card_filter_le_ofPrefixJumps p hstep top
  rwa [Finset.filter_true_of_mem (fun x (_ : x ∈ KSubset.ofPrefixJumps p) => htop x)] at heq

/-! ### Endpoint EXTERIOR: the rank-`(n-1)` extension above a frozen-free wall

For a frozen-free wall `W` (`|W| = n-1`) whose members all have rank `≤ n-2` (the "missing top
rank" / above-endpoint configuration), the prefix-count path `pc(j) = k` at the top coordinate,
`minPrefixCount W j + 1` elsewhere, is a valid `k`-subset (via the realization lemma).  Its
above-min profile is `univ \ {top}` (rank `n-1`).  It is a genuine same-frame extension of
`W`: in the band, profile-`⊇` every wall member (so sorted-compatible), and `∉ W` because
its rank `n-1` is not achieved in `W`.  Pairing it with any other extension gives `≥ 2`. -/

/-- The endpoint EXTERIOR subset.  Generalized: needs only `top ∉ commonAbsent W` (not full
`commonAbsent = ∅`) — the essential fact for the pred-top boundary value.  So it applies to the
`c = 1` common-absent one-frozen wall as long as the frozen coordinate is not the top. -/
theorem KSubsetCollection.exists_endpointExteriorSubset {n k : ℕ} {W : Finset (KSubset n k)}
    (hWne : W.Nonempty) {top : Fin n} (htop : ∀ j : Fin n, j ≤ top) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hcp : KSubsetCollection.commonPresent W = ∅) (htna : top ∉ KSubsetCollection.commonAbsent W) :
    ∃ E : KSubset n k, ∀ t : Fin n,
      KSubset.prefixCount E t
        = (if t = top then k else KSubsetCollection.minPrefixCount W hWne t + 1) := by
  classical
  set p : Fin n → ℕ :=
    fun j => if j = top then k else KSubsetCollection.minPrefixCount W hWne j + 1 with hp
  have htoppos : 1 ≤ top.val := by
    have h1 := htop (⟨1, by omega⟩ : Fin n)
    rw [Fin.le_def] at h1
    simpa using h1
  have hstep : ∀ j : Fin n, p j = KSubset.predValue p j ∨ p j = KSubset.predValue p j + 1 := by
    intro j
    by_cases hj0 : j.val = 0
    · have hjnetop : j ≠ top := fun h => by rw [h] at hj0; omega
      have hpvj : KSubset.predValue p j = 0 := by rw [KSubset.predValue, if_pos hj0]
      have hpj : p j = KSubsetCollection.minPrefixCount W hWne j + 1 := by
        simp only [hp, if_neg hjnetop]
      have hminj : KSubsetCollection.minPrefixCount W hWne j = 0 :=
        KSubsetCollection.minPrefixCount_bot_eq_zero hWne hj0 hcp
      right; rw [hpvj, hpj, hminj]
    · have hjp_lt : j.val - 1 < n := lt_of_le_of_lt (Nat.sub_le j.val 1) j.isLt
      set jp : Fin n := ⟨j.val - 1, hjp_lt⟩ with hjp_def
      have hjpval : jp.val = j.val - 1 := by rw [hjp_def]
      have hjp_succ : jp.val + 1 = j.val := by omega
      have hpvj : KSubset.predValue p j = p jp := by rw [KSubset.predValue, if_neg hj0]
      have hjt : j.val ≤ top.val := by have := htop j; rwa [Fin.le_def] at this
      have hjp_lt_top : jp.val < top.val := by omega
      have hjpnetop : jp ≠ top := fun h => by rw [h] at hjp_lt_top; omega
      have hpjp : p jp = KSubsetCollection.minPrefixCount W hWne jp + 1 := by
        simp only [hp, if_neg hjpnetop]
      by_cases hjtop : j = top
      · have hpj : p j = k := by simp only [hp, if_pos hjtop]
        have hjp_predtop : jp.val + 1 = top.val := by rw [← hjtop]; exact hjp_succ
        have hminjp : KSubsetCollection.minPrefixCount W hWne jp = k - 1 :=
          KSubsetCollection.minPrefixCount_predTop_eq hWne htop hjp_predtop htna
        rw [hpvj, hpjp, hpj, hminjp]; omega
      · have hpj : p j = KSubsetCollection.minPrefixCount W hWne j + 1 := by
          simp only [hp, if_neg hjtop]
        have hms := KSubsetCollection.minPrefixCount_step hWne hjp_succ
        rw [hpvj, hpjp, hpj]; omega
  have hptop_k : p top = k := by simp only [hp, if_pos rfl]
  have hcard : (KSubset.ofPrefixJumps p).card = k := by
    rw [KSubset.card_ofPrefixJumps p hstep htop, hptop_k]
  refine ⟨⟨KSubset.ofPrefixJumps p, hcard⟩, fun t => ?_⟩
  have hpc : KSubset.prefixCount ⟨KSubset.ofPrefixJumps p, hcard⟩ t = p t :=
    KSubset.card_filter_le_ofPrefixJumps p hstep t
  rw [hpc, hp]

/-- The endpoint exterior's above-min profile is `univ \ {top}` (rank `n-1`). -/
theorem KSubsetCollection.aboveMinProfile_endpointExterior {n k : ℕ} {W : Finset (KSubset n k)}
    (hWne : W.Nonempty) {top : Fin n} (htop : ∀ j : Fin n, j ≤ top) {E : KSubset n k}
    (hE : ∀ t : Fin n, KSubset.prefixCount E t
        = (if t = top then k else KSubsetCollection.minPrefixCount W hWne t + 1)) :
    KSubsetCollection.aboveMinProfile W hWne E = Finset.univ.erase top := by
  classical
  ext t
  rw [KSubsetCollection.mem_aboveMinProfile_iff, Finset.mem_erase, hE t]
  by_cases ht : t = top
  · subst ht
    rw [if_pos rfl, minPrefixCount_top_eq hWne htop]
    simp
  · rw [if_neg ht]
    constructor
    · intro _; exact ⟨ht, Finset.mem_univ t⟩
    · intro _; omega

/-- The endpoint exterior is a genuine same-frame extension (KEY deliverable). -/
theorem KSubsetCollection.endpoint_exterior_mem_sameFrameExtensions {n k : ℕ}
    {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W) (hWne : W.Nonempty)
    (hWcard : W.card = n - 1) (hfrozen : KSubsetCollection.frozenCoords W = ∅)
    (hmax : ∀ S ∈ W, (KSubsetCollection.aboveMinProfile W hWne S).card ≤ n - 2) :
    ∃ E : KSubset n k, E ∈ KSubsetCollection.sameFrameExtensions W ∧
      (KSubsetCollection.aboveMinProfile W hWne E).card = n - 1 := by
  classical
  have hn : 2 ≤ n := by
    have h1 : 1 ≤ W.card := Finset.card_pos.mpr hWne
    rw [hWcard] at h1; omega
  set top : Fin n := ⟨n - 1, by omega⟩ with htop_def
  have htopval : top.val = n - 1 := by rw [htop_def]
  have htop : ∀ j : Fin n, j ≤ top := by
    intro j; rw [Fin.le_def, htopval]; have := j.isLt; omega
  have hcp : KSubsetCollection.commonPresent W = ∅ := by
    rw [KSubsetCollection.frozenCoords] at hfrozen
    exact (Finset.union_eq_empty.mp hfrozen).1
  have hca : KSubsetCollection.commonAbsent W = ∅ := by
    rw [KSubsetCollection.frozenCoords] at hfrozen
    exact (Finset.union_eq_empty.mp hfrozen).2
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exfalso
      have hmem : top ∈ KSubsetCollection.commonAbsent W := by
        rw [KSubsetCollection.mem_commonAbsent_iff]
        intro T hTW
        have hT0 : T.1 = ∅ := Finset.card_eq_zero.mp (T.2.trans hk0)
        rw [hT0]; exact Finset.notMem_empty top
      rw [hca] at hmem; exact Finset.notMem_empty top hmem
    · exact hk0
  obtain ⟨E, hE⟩ := KSubsetCollection.exists_endpointExteriorSubset hWne htop hn hk hcp
    (by rw [hca]; exact Finset.notMem_empty top)
  have hprof : KSubsetCollection.aboveMinProfile W hWne E = Finset.univ.erase top :=
    KSubsetCollection.aboveMinProfile_endpointExterior hWne htop hE
  have hprofcard : (KSubsetCollection.aboveMinProfile W hWne E).card = n - 1 := by
    rw [hprof, Finset.card_erase_of_mem (Finset.mem_univ top), Finset.card_univ, Fintype.card_fin]
  have hEW : E ∉ W := by
    intro hin
    have hle := hmax E hin
    rw [hprofcard] at hle; omega
  have hband : ∀ t, KSubsetCollection.minPrefixCount W hWne t ≤ KSubset.prefixCount E t ∧
      KSubset.prefixCount E t ≤ KSubsetCollection.minPrefixCount W hWne t + 1 := by
    intro t
    rw [hE t]
    by_cases ht : t = top
    · subst ht; rw [if_pos rfl, minPrefixCount_top_eq hWne htop]; omega
    · rw [if_neg ht]; omega
  have hcompat : ∀ S ∈ W, KSubset.IsSortedPair E S := by
    intro S hSW
    have hSsub : KSubsetCollection.aboveMinProfile W hWne S ⊆ Finset.univ.erase top := by
      intro t ht
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ t⟩
      rintro rfl
      rw [KSubsetCollection.mem_aboveMinProfile_iff, prefixCount_top_eq S htop,
        minPrefixCount_top_eq hWne htop] at ht
      omega
    refine Or.inl (fun t => ?_)
    have hbt := hband t
    have hbs := KSubsetCollection.prefixCount_eq_min_or_min_add_one hWsorted hWne hSW t
    have hSle := KSubsetCollection.minPrefixCount_le hWne hSW t
    by_cases hSt : t ∈ KSubsetCollection.aboveMinProfile W hWne S
    · have htnetop : t ≠ top := (Finset.mem_erase.mp (hSsub hSt)).1
      rw [KSubsetCollection.mem_aboveMinProfile_iff] at hSt
      rw [hE t, if_neg htnetop]
      omega
    · rw [KSubsetCollection.mem_aboveMinProfile_iff] at hSt; push_neg at hSt
      omega
  refine ⟨E, ?_, hprofcard⟩
  rw [KSubsetCollection.mem_sameFrameExtensions_iff]
  refine ⟨hEW, ?_, KSubsetCollection.isSorted_insert hWsorted hcompat⟩
  rw [Finset.card_insert_of_notMem hEW, hWcard]; omega

/-- **`c = 1` UP-SIDE, case (c) — top missing rank.**  A codim-1 sorted wall whose ranks miss the
TOP value (`hmax : ∀ S, card ≤ n-2`) has a same-frame extension: the rank-`(n-1)` above-exterior.
NO frozen-free hypothesis — only `commonPresent = ∅` (for the bottom boundary value) and
`top ∉ commonAbsent` (for the pred-top boundary value), both of which the `c = 1` common-absent
one-frozen wall satisfies when the frozen coordinate is not the top.  `∉ W` is by RANK (`n-1` is the
missing rank); compatibility is the band + profile-`⊇` argument, frozen-free-independent.  (This is
the frozen-free-relaxed twin of `endpoint_exterior_mem_sameFrameExtensions`.) -/
theorem KSubsetCollection.sameFrameExtensions_nonempty_of_commonAbsent_oneFrozen_topEndpoint
    {n k : ℕ} {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W)
    (hWne : W.Nonempty) (hWcard : W.card = n - 1) {top : Fin n} (htop : ∀ j : Fin n, j ≤ top)
    (hcp : KSubsetCollection.commonPresent W = ∅)
    (htna : top ∉ KSubsetCollection.commonAbsent W)
    (hmax : ∀ S ∈ W, (KSubsetCollection.aboveMinProfile W hWne S).card ≤ n - 2) :
    (KSubsetCollection.sameFrameExtensions W).Nonempty := by
  classical
  have hn : 2 ≤ n := by
    have h1 : 1 ≤ W.card := Finset.card_pos.mpr hWne
    rw [hWcard] at h1; omega
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exfalso
      apply htna
      rw [KSubsetCollection.mem_commonAbsent_iff]
      intro T hTW
      have hT0 : T.1 = ∅ := Finset.card_eq_zero.mp (T.2.trans hk0)
      rw [hT0]; exact Finset.notMem_empty top
    · exact hk0
  obtain ⟨E, hE⟩ := KSubsetCollection.exists_endpointExteriorSubset hWne htop hn hk hcp htna
  have hprof : KSubsetCollection.aboveMinProfile W hWne E = Finset.univ.erase top :=
    KSubsetCollection.aboveMinProfile_endpointExterior hWne htop hE
  have hprofcard : (KSubsetCollection.aboveMinProfile W hWne E).card = n - 1 := by
    rw [hprof, Finset.card_erase_of_mem (Finset.mem_univ top), Finset.card_univ, Fintype.card_fin]
  have hEW : E ∉ W := by
    intro hin; have hle := hmax E hin; rw [hprofcard] at hle; omega
  have hband : ∀ t, KSubsetCollection.minPrefixCount W hWne t ≤ KSubset.prefixCount E t ∧
      KSubset.prefixCount E t ≤ KSubsetCollection.minPrefixCount W hWne t + 1 := by
    intro t; rw [hE t]
    by_cases ht : t = top
    · subst ht; rw [if_pos rfl, minPrefixCount_top_eq hWne htop]; omega
    · rw [if_neg ht]; omega
  have hcompat : ∀ S ∈ W, KSubset.IsSortedPair E S := by
    intro S hSW
    have hSsub : KSubsetCollection.aboveMinProfile W hWne S ⊆ Finset.univ.erase top := by
      intro t ht; rw [Finset.mem_erase]; refine ⟨?_, Finset.mem_univ t⟩
      rintro rfl
      rw [KSubsetCollection.mem_aboveMinProfile_iff, prefixCount_top_eq S htop,
        minPrefixCount_top_eq hWne htop] at ht
      omega
    refine Or.inl (fun t => ?_)
    have hbt := hband t
    have hbs := KSubsetCollection.prefixCount_eq_min_or_min_add_one hWsorted hWne hSW t
    have hSle := KSubsetCollection.minPrefixCount_le hWne hSW t
    by_cases hSt : t ∈ KSubsetCollection.aboveMinProfile W hWne S
    · have htnetop : t ≠ top := (Finset.mem_erase.mp (hSsub hSt)).1
      rw [KSubsetCollection.mem_aboveMinProfile_iff] at hSt
      rw [hE t, if_neg htnetop]; omega
    · rw [KSubsetCollection.mem_aboveMinProfile_iff] at hSt; push_neg at hSt; omega
  refine ⟨E, ?_⟩
  rw [KSubsetCollection.mem_sameFrameExtensions_iff]
  refine ⟨hEW, ?_, KSubsetCollection.isSorted_insert hWsorted hcompat⟩
  rw [Finset.card_insert_of_notMem hEW, hWcard]; omega

/- **`c = 1` up-side existence** (`sameFrameExtensions_nonempty_of_commonAbsent_oneFrozen`).  A
codim-1 sorted wall with one common-absent frozen coordinate has a same-frame extension, by a
missing-rank dispatch (rank `0` always present ⟹ missing rank `m ∈ {1,…,n-1}`): the endpoint case
`m = n-1` (above- or below-exterior) and the interior case `1 ≤ m ≤ n-2` (descent swap at the
non-adjacent or adjacent gap). -/

/-- The above-endpoint lower bound: a frozen-free wall in the missing-top-rank
configuration that already admits ONE extension of rank `≠ n-1` has `≥ 2` same-frame extensions
(the given one plus the exterior).  This is the above-endpoint half of the endpoint case; the
below-endpoint half (`rank = n-1` given, exterior on the opposite side) is its mirror and is the
remaining piece of the full `NoFrozenWallHasTwoExtensions` endpoint dispatch. -/
theorem KSubsetCollection.sameFrameExtensions_two_of_no_frozen_endpoint {n k : ℕ}
    {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W) (hWne : W.Nonempty)
    (hWcard : W.card = n - 1) (hfrozen : KSubsetCollection.frozenCoords W = ∅)
    (hmax : ∀ S ∈ W, (KSubsetCollection.aboveMinProfile W hWne S).card ≤ n - 2)
    (hV : ∃ V ∈ KSubsetCollection.sameFrameExtensions W,
      (KSubsetCollection.aboveMinProfile W hWne V).card ≠ n - 1) :
    2 ≤ (KSubsetCollection.sameFrameExtensions W).card := by
  classical
  obtain ⟨E, hEmem, hErank⟩ :=
    KSubsetCollection.endpoint_exterior_mem_sameFrameExtensions hWsorted hWne hWcard hfrozen hmax
  obtain ⟨V, hVmem, hVrank⟩ := hV
  have hEV : E ≠ V := by
    intro h; apply hVrank; rw [← h]; exact hErank
  have hsub : ({E, V} : Finset (KSubset n k)) ⊆ KSubsetCollection.sameFrameExtensions W := by
    intro X hX
    rw [Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl
    · exact hEmem
    · exact hVmem
  calc 2 = ({E, V} : Finset (KSubset n k)).card := (Finset.card_pair hEV).symm
    _ ≤ (KSubsetCollection.sameFrameExtensions W).card := Finset.card_le_card hsub

/-! ### Endpoint BELOW-exterior (the dip extension) — `maxPrefixCount` machinery

ROUTE DECISION: the below-exterior is built DIRECTLY (not by complement-dualising the above
exterior).  The complement `KSubset.compl : KSubset n k → KSubset n (n-k)` changes the rank index,
so pulling an above-exterior of `Wᶜ` back to `sameFrameExtensions W` needs `compl ∘ compl = id`
under the propositional cast `n - (n - k) = k` (the "double-compl type pain"; `mem_sameFrameExtensions_compl`
is forward-only), AND applying the above-exterior theorem to `Wᶜ` still requires `hmax` for `Wᶜ`
(`≥ 2` constant coords) — the same structural fact the direct `∉ W` step needs.  So complement adds
the cast pain without removing the real obligation.  The below-exterior path is the dual
`pc(j) = if j = top then k else maxPrefixCount W j − 1` (the dip sits at the unique non-top constant
coordinate).  This needs a `maxPrefixCount` mirror of `minPrefixCount`. -/

/-- Prefix count is monotone in the threshold. -/
theorem KSubset.prefixCount_mono {n k : ℕ} (S : KSubset n k) {s t : Fin n} (h : s ≤ t) :
    S.prefixCount s ≤ S.prefixCount t := by
  show (S.1.filter (· ≤ s)).card ≤ (S.1.filter (· ≤ t)).card
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, le_trans hx.2 h⟩

/-- The pointwise maximum prefix count over a nonempty collection (dual to `minPrefixCount`). -/
noncomputable def KSubsetCollection.maxPrefixCount {n k : ℕ}
    (A : Finset (KSubset n k)) (hA : A.Nonempty) (t : Fin n) : ℕ :=
  (A.image fun S => KSubset.prefixCount S t).max' (hA.image _)

theorem KSubsetCollection.le_maxPrefixCount {n k : ℕ}
    {A : Finset (KSubset n k)} (hA : A.Nonempty) {S : KSubset n k} (hS : S ∈ A) (t : Fin n) :
    KSubset.prefixCount S t ≤ KSubsetCollection.maxPrefixCount A hA t := by
  unfold KSubsetCollection.maxPrefixCount
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem (fun S => KSubset.prefixCount S t) hS)

/-- Width-one upper bound: the wall maximum prefix count is at most the minimum plus one. -/
theorem KSubsetCollection.maxPrefixCount_le_minPrefixCount_succ {n k : ℕ}
    {A : Finset (KSubset n k)} (hA_sorted : KSubsetCollection.IsSorted A) (hA : A.Nonempty)
    (t : Fin n) :
    KSubsetCollection.maxPrefixCount A hA t ≤ KSubsetCollection.minPrefixCount A hA t + 1 := by
  apply Finset.max'_le
  intro x hx
  obtain ⟨S, hSW, rfl⟩ := Finset.mem_image.mp hx
  rcases KSubsetCollection.prefixCount_eq_min_or_min_add_one hA_sorted hA hSW t with h | h <;> omega

/-- The wall maximum prefix count is monotone with `0/1` steps (dual to `minPrefixCount_step`). -/
theorem KSubsetCollection.maxPrefixCount_step {n k : ℕ} {W : Finset (KSubset n k)}
    (hWne : W.Nonempty) {jp j : Fin n} (h : jp.val + 1 = j.val) :
    KSubsetCollection.maxPrefixCount W hWne jp ≤ KSubsetCollection.maxPrefixCount W hWne j ∧
      KSubsetCollection.maxPrefixCount W hWne j
        ≤ KSubsetCollection.maxPrefixCount W hWne jp + 1 := by
  classical
  have hle : jp ≤ j := by rw [Fin.le_def]; omega
  refine ⟨?_, ?_⟩
  · obtain ⟨Sjp, hSjpW, hSjpeq⟩ := Finset.mem_image.mp
      (Finset.max'_mem _ (hWne.image (fun S => KSubset.prefixCount S jp)))
    have hmax_jp : KSubset.prefixCount Sjp jp = KSubsetCollection.maxPrefixCount W hWne jp := hSjpeq
    calc KSubsetCollection.maxPrefixCount W hWne jp
        = KSubset.prefixCount Sjp jp := hmax_jp.symm
      _ ≤ KSubset.prefixCount Sjp j := KSubset.prefixCount_mono Sjp hle
      _ ≤ KSubsetCollection.maxPrefixCount W hWne j := KSubsetCollection.le_maxPrefixCount hWne hSjpW j
  · obtain ⟨Sj, hSjW, hSjeq⟩ := Finset.mem_image.mp
      (Finset.max'_mem _ (hWne.image (fun S => KSubset.prefixCount S j)))
    have hmax_j : KSubset.prefixCount Sj j = KSubsetCollection.maxPrefixCount W hWne j := hSjeq
    have hstep : KSubset.prefixCount Sj j ≤ KSubset.prefixCount Sj jp + 1 := by
      rw [KSubset.prefixCount_pred Sj h]; split <;> omega
    calc KSubsetCollection.maxPrefixCount W hWne j
        = KSubset.prefixCount Sj j := hmax_j.symm
      _ ≤ KSubset.prefixCount Sj jp + 1 := hstep
      _ ≤ KSubsetCollection.maxPrefixCount W hWne jp + 1 := by
          have := KSubsetCollection.le_maxPrefixCount hWne hSjW jp; omega

theorem KSubsetCollection.maxPrefixCount_top_eq {n k : ℕ} {A : Finset (KSubset n k)}
    (hA : A.Nonempty) {t : Fin n} (ht : ∀ j : Fin n, j ≤ t) :
    KSubsetCollection.maxPrefixCount A hA t = k := by
  obtain ⟨S, _, hSeq⟩ := Finset.mem_image.mp
    (Finset.max'_mem _ (hA.image (fun S => KSubset.prefixCount S t)))
  have heq : KSubset.prefixCount S t = KSubsetCollection.maxPrefixCount A hA t := hSeq
  rw [← heq, prefixCount_top_eq S ht]

/-- Bottom not common-absent: if the bottom coordinate is not common-absent (some member contains
it), the wall maximum prefix count there is `1`.  (Generalizes the frozen-free `commonAbsent = ∅`
version, which is the special case for case `c′`, where `top` may be common-absent.) -/
theorem KSubsetCollection.maxPrefixCount_bot_eq_one {n k : ℕ} {W : Finset (KSubset n k)}
    (hWne : W.Nonempty) {z : Fin n} (hz : z.val = 0)
    (hbna : z ∉ KSubsetCollection.commonAbsent W) :
    KSubsetCollection.maxPrefixCount W hWne z = 1 := by
  classical
  have hne : ¬ (∀ S ∈ W, z ∉ S.1) :=
    fun h => hbna ((KSubsetCollection.mem_commonAbsent_iff W z).mpr h)
  push_neg at hne
  obtain ⟨S, hSW, hSz⟩ := hne
  have hge : 1 ≤ KSubsetCollection.maxPrefixCount W hWne z := by
    have hpc : KSubset.prefixCount S z = 1 := by
      rw [KSubset.prefixCount_eq_indicator_of_val_zero S hz, if_pos hSz]
    have := KSubsetCollection.le_maxPrefixCount hWne hSW z; omega
  have hle : KSubsetCollection.maxPrefixCount W hWne z ≤ 1 := by
    apply Finset.max'_le
    intro x hx
    obtain ⟨T, hTW, rfl⟩ := Finset.mem_image.mp hx
    rw [KSubset.prefixCount_eq_indicator_of_val_zero T hz]; split <;> omega
  omega

/-- Frozen-free (top−1): if no coordinate is common-present, the wall maximum prefix count just
below the top coordinate is `k`. -/
theorem KSubsetCollection.maxPrefixCount_predTop_eq {n k : ℕ} {W : Finset (KSubset n k)}
    (hWne : W.Nonempty) {top ptop : Fin n} (htop : ∀ j : Fin n, j ≤ top)
    (hpt : ptop.val + 1 = top.val) (hcp : KSubsetCollection.commonPresent W = ∅) :
    KSubsetCollection.maxPrefixCount W hWne ptop = k := by
  classical
  have hpcform : ∀ S ∈ W, KSubset.prefixCount S ptop = k - (if top ∈ S.1 then 1 else 0) := by
    intro S hSW
    have h1 := KSubset.prefixCount_pred S hpt
    rw [prefixCount_top_eq S htop] at h1
    omega
  have hne : ¬ (∀ S ∈ W, top ∈ S.1) := by
    intro h
    have hmem : top ∈ KSubsetCollection.commonPresent W :=
      (KSubsetCollection.mem_commonPresent_iff W top).mpr h
    rw [hcp] at hmem; exact absurd hmem (Finset.notMem_empty top)
  push_neg at hne
  obtain ⟨S, hSW, hStop⟩ := hne
  have hge : k ≤ KSubsetCollection.maxPrefixCount W hWne ptop := by
    have hsge := KSubsetCollection.le_maxPrefixCount hWne hSW ptop
    rw [hpcform S hSW, if_neg hStop] at hsge; omega
  have hle : KSubsetCollection.maxPrefixCount W hWne ptop ≤ k := by
    apply Finset.max'_le
    intro x hx
    obtain ⟨T, hTW, rfl⟩ := Finset.mem_image.mp hx
    rw [hpcform T hTW]; split <;> omega
  omega

/-- Bottom not common-absent: the wall maximum prefix count is positive everywhere (some member
contains the bottom coordinate, which propagates upward). -/
theorem KSubsetCollection.maxPrefixCount_pos {n k : ℕ} {W : Finset (KSubset n k)}
    (hWne : W.Nonempty) {z : Fin n} (hz : z.val = 0)
    (hbna : z ∉ KSubsetCollection.commonAbsent W) (t : Fin n) :
    1 ≤ KSubsetCollection.maxPrefixCount W hWne t := by
  classical
  have hzt : z ≤ t := by rw [Fin.le_def, hz]; omega
  have hne : ¬ (∀ S ∈ W, z ∉ S.1) :=
    fun h => hbna ((KSubsetCollection.mem_commonAbsent_iff W z).mpr h)
  push_neg at hne
  obtain ⟨S, hSW, hSz⟩ := hne
  have hpcz : KSubset.prefixCount S z = 1 := by
    rw [KSubset.prefixCount_eq_indicator_of_val_zero S hz, if_pos hSz]
  have h1 : 1 ≤ KSubset.prefixCount S t := by rw [← hpcz]; exact KSubset.prefixCount_mono S hzt
  exact le_trans h1 (KSubsetCollection.le_maxPrefixCount hWne hSW t)

/-- EVERY sorted nonempty wall has a RANK-`0` member (`aboveMinProfile = ∅`): the pointwise minimum
prefix count is achieved by a single member.  Proof: the profiles are a chain (nesting), so the
smallest-card one `P₀` is contained in all; if some `c ∈ P₀` then `c` is above-min for EVERY member,
so the wall minimum at `c` would exceed itself — contradiction, hence `P₀ = ∅`.  **COROLLARY: the
"missing-bottom" endpoint case is VACUOUS** — a sorted `(n-1)`-wall's ranks always include `0`, so
the missing rank is in `{1,…,n-1}` (never `0`).  (Machine-checked for `n=4,k=2`: every sorted wall
has a pointwise-min member; e.g. `{02,12,13}` is missing-TOP, with rank-`0` member `{1,3}`.) -/
theorem KSubsetCollection.exists_rank_zero_member {n k : ℕ} {W : Finset (KSubset n k)}
    (hWsorted : KSubsetCollection.IsSorted W) (hWne : W.Nonempty) :
    ∃ S ∈ W, KSubsetCollection.aboveMinProfile W hWne S = ∅ := by
  classical
  obtain ⟨S0, hS0W, hS0min⟩ := Finset.exists_min_image W
    (fun S => (KSubsetCollection.aboveMinProfile W hWne S).card) hWne
  refine ⟨S0, hS0W, ?_⟩
  rw [Finset.eq_empty_iff_forall_notMem]
  intro c hc
  obtain ⟨S', hS'W, hS'eq⟩ := Finset.mem_image.mp
    (Finset.min'_mem _ (hWne.image (fun S => KSubset.prefixCount S c)))
  have hmin_eq : KSubset.prefixCount S' c = KSubsetCollection.minPrefixCount W hWne c := hS'eq
  have hsub : KSubsetCollection.aboveMinProfile W hWne S0
      ⊆ KSubsetCollection.aboveMinProfile W hWne S' := by
    rcases KSubsetCollection.aboveMinProfile_subset_or_superset hWsorted hWne hS0W hS'W with h | h
    · exact h
    · exact (Finset.eq_of_subset_of_card_le h (hS0min S' hS'W)).ge
  have hcS' := hsub hc
  rw [KSubsetCollection.mem_aboveMinProfile_iff, hmin_eq] at hcS'
  exact absurd hcS' (lt_irrefl _)

/-- Lemma C (the `∉ W` ingredient): a missing-top-rank frozen-free wall has a NON-TOP constant
coordinate (where `maxPrefixCount = minPrefixCount`).  The above-min profiles form a chain with
distinct cards `≤ n-2`, so their union is contained in the largest profile (card `≤ n-2`); since the
`n-1` non-top coordinates cannot all be covered, some non-top coordinate lies in no profile. -/
theorem KSubsetCollection.exists_nontop_constantCoord {n k : ℕ} {W : Finset (KSubset n k)}
    (hWsorted : KSubsetCollection.IsSorted W) (hWne : W.Nonempty) {top : Fin n}
    (htop : ∀ j : Fin n, j ≤ top) (hn : 2 ≤ n)
    (hmax : ∀ S ∈ W, (KSubsetCollection.aboveMinProfile W hWne S).card ≤ n - 2) :
    ∃ c : Fin n, c ≠ top ∧
      KSubsetCollection.maxPrefixCount W hWne c = KSubsetCollection.minPrefixCount W hWne c := by
  classical
  obtain ⟨Sstar, hSstarW, hSstarmax⟩ := Finset.exists_max_image W
    (fun S => (KSubsetCollection.aboveMinProfile W hWne S).card) hWne
  set P := KSubsetCollection.aboveMinProfile W hWne Sstar with hP
  have hPtop : top ∉ P := by
    rw [hP, KSubsetCollection.mem_aboveMinProfile_iff, prefixCount_top_eq Sstar htop,
      minPrefixCount_top_eq hWne htop]; omega
  have hPcard : P.card ≤ n - 2 := by rw [hP]; exact hmax Sstar hSstarW
  have hEcard : (Finset.univ.erase top).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ top), Finset.card_univ, Fintype.card_fin]
  have hlt : P.card < (Finset.univ.erase top).card := by rw [hEcard]; omega
  obtain ⟨c, hcE, hcP⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨c, (Finset.mem_erase.mp hcE).1, ?_⟩
  have hcnotprof : ∀ S ∈ W, c ∉ KSubsetCollection.aboveMinProfile W hWne S := by
    intro S hSW hcS
    have hsub : KSubsetCollection.aboveMinProfile W hWne S ⊆ P := by
      rcases KSubsetCollection.aboveMinProfile_subset_or_superset hWsorted hWne hSW hSstarW
        with h | h
      · exact h
      · exact (Finset.eq_of_subset_of_card_le h (hSstarmax S hSW)).ge
    exact hcP (hsub hcS)
  apply le_antisymm
  · apply Finset.max'_le
    intro x hx
    obtain ⟨S, hSW, rfl⟩ := Finset.mem_image.mp hx
    have hcc := hcnotprof S hSW
    rw [KSubsetCollection.mem_aboveMinProfile_iff] at hcc; push_neg at hcc
    exact hcc
  · obtain ⟨S, hSW⟩ := id hWne
    exact le_trans (KSubsetCollection.minPrefixCount_le hWne hSW c)
      (KSubsetCollection.le_maxPrefixCount hWne hSW c)

/-- Below-EXTERIOR subset (dual to `exists_endpointExteriorSubset`): the prefix-count path
`pc(j) = k` at the top, `maxPrefixCount W j − 1` elsewhere.  Realised via `ofPrefixJumps`; the
`0/1`-step hypothesis is supplied by `maxPrefixCount_step` (interior), `maxPrefixCount_bot_eq_one`
(bottom), `maxPrefixCount_predTop_eq` (just below top), with `maxPrefixCount_pos` keeping the `−1`
honest. -/
theorem KSubsetCollection.exists_belowExteriorSubset {n k : ℕ} {W : Finset (KSubset n k)}
    (hWne : W.Nonempty) {top : Fin n} (htop : ∀ j : Fin n, j ≤ top) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hcp : KSubsetCollection.commonPresent W = ∅)
    (hbna : ∀ b : Fin n, b.val = 0 → b ∉ KSubsetCollection.commonAbsent W) :
    ∃ E : KSubset n k, ∀ t : Fin n,
      KSubset.prefixCount E t
        = (if t = top then k else KSubsetCollection.maxPrefixCount W hWne t - 1) := by
  classical
  set p : Fin n → ℕ :=
    fun j => if j = top then k else KSubsetCollection.maxPrefixCount W hWne j - 1 with hp
  have hbot0 : (⟨0, by omega⟩ : Fin n).val = 0 := rfl
  have htoppos : 1 ≤ top.val := by
    have h1 := htop (⟨1, by omega⟩ : Fin n)
    rw [Fin.le_def] at h1; simpa using h1
  have hstep : ∀ j : Fin n, p j = KSubset.predValue p j ∨ p j = KSubset.predValue p j + 1 := by
    intro j
    by_cases hj0 : j.val = 0
    · have hjnetop : j ≠ top := fun h => by rw [h] at hj0; omega
      have hpvj : KSubset.predValue p j = 0 := by rw [KSubset.predValue, if_pos hj0]
      have hpj : p j = KSubsetCollection.maxPrefixCount W hWne j - 1 := by
        simp only [hp, if_neg hjnetop]
      have hmaxj : KSubsetCollection.maxPrefixCount W hWne j = 1 :=
        KSubsetCollection.maxPrefixCount_bot_eq_one hWne hj0 (hbna j hj0)
      left; rw [hpvj, hpj, hmaxj]
    · have hjp_lt : j.val - 1 < n := lt_of_le_of_lt (Nat.sub_le j.val 1) j.isLt
      set jp : Fin n := ⟨j.val - 1, hjp_lt⟩ with hjp_def
      have hjpval : jp.val = j.val - 1 := by rw [hjp_def]
      have hjp_succ : jp.val + 1 = j.val := by omega
      have hpvj : KSubset.predValue p j = p jp := by rw [KSubset.predValue, if_neg hj0]
      have hjt : j.val ≤ top.val := by have := htop j; rwa [Fin.le_def] at this
      have hjp_lt_top : jp.val < top.val := by omega
      have hjpnetop : jp ≠ top := fun h => by rw [h] at hjp_lt_top; omega
      have hpjp : p jp = KSubsetCollection.maxPrefixCount W hWne jp - 1 := by
        simp only [hp, if_neg hjpnetop]
      by_cases hjtop : j = top
      · have hpj : p j = k := by simp only [hp, if_pos hjtop]
        have hjp_predtop : jp.val + 1 = top.val := by rw [← hjtop]; exact hjp_succ
        have hmaxjp : KSubsetCollection.maxPrefixCount W hWne jp = k :=
          KSubsetCollection.maxPrefixCount_predTop_eq hWne htop hjp_predtop hcp
        rw [hpvj, hpjp, hpj, hmaxjp]; omega
      · have hpj : p j = KSubsetCollection.maxPrefixCount W hWne j - 1 := by
          simp only [hp, if_neg hjtop]
        have hms := KSubsetCollection.maxPrefixCount_step hWne hjp_succ
        have hposj := KSubsetCollection.maxPrefixCount_pos hWne hbot0 (hbna _ hbot0) j
        have hposjp := KSubsetCollection.maxPrefixCount_pos hWne hbot0 (hbna _ hbot0) jp
        rw [hpvj, hpjp, hpj]; omega
  have hptop_k : p top = k := by simp only [hp, if_pos rfl]
  have hcard : (KSubset.ofPrefixJumps p).card = k := by
    rw [KSubset.card_ofPrefixJumps p hstep htop, hptop_k]
  refine ⟨⟨KSubset.ofPrefixJumps p, hcard⟩, fun t => ?_⟩
  have hpc : KSubset.prefixCount ⟨KSubset.ofPrefixJumps p, hcard⟩ t = p t :=
    KSubset.card_filter_le_ofPrefixJumps p hstep t
  rw [hpc, hp]

/-- The below-exterior has EMPTY above-min profile (rank `0`): its prefix count never exceeds the
wall minimum (`maxPrefixCount − 1 ≤ minPrefixCount` by width-one, and `= minPrefixCount` at top). -/
theorem KSubsetCollection.aboveMinProfile_belowExterior {n k : ℕ} {W : Finset (KSubset n k)}
    (hWsorted : KSubsetCollection.IsSorted W) (hWne : W.Nonempty) {top : Fin n}
    (htop : ∀ j : Fin n, j ≤ top) {E : KSubset n k}
    (hE : ∀ t : Fin n, KSubset.prefixCount E t
        = (if t = top then k else KSubsetCollection.maxPrefixCount W hWne t - 1)) :
    KSubsetCollection.aboveMinProfile W hWne E = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro t ht
  rw [KSubsetCollection.mem_aboveMinProfile_iff, hE t] at ht
  by_cases h : t = top
  · subst h; rw [if_pos rfl, minPrefixCount_top_eq hWne htop] at ht; omega
  · rw [if_neg h] at ht
    have hw := KSubsetCollection.maxPrefixCount_le_minPrefixCount_succ hWsorted hWne t
    omega

/-- The BELOW endpoint exterior is a genuine same-frame extension (the dip extension,
rank `0`).  Generalized boundary hypotheses (`commonPresent = ∅` and `bottom ∉ commonAbsent`)
instead of frozen-free, so this covers case `c′` (`top` common-absent, the unique frozen coordinate
is the top) where the ABOVE-exterior is invalid and the dip is the relevant extension. -/
theorem KSubsetCollection.endpoint_below_exterior_mem_sameFrameExtensions {n k : ℕ}
    {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W) (hWne : W.Nonempty)
    (hWcard : W.card = n - 1) (hcp : KSubsetCollection.commonPresent W = ∅)
    (hbna : ∀ b : Fin n, b.val = 0 → b ∉ KSubsetCollection.commonAbsent W)
    (hmax : ∀ S ∈ W, (KSubsetCollection.aboveMinProfile W hWne S).card ≤ n - 2) :
    ∃ E : KSubset n k, E ∈ KSubsetCollection.sameFrameExtensions W ∧
      KSubsetCollection.aboveMinProfile W hWne E = ∅ := by
  classical
  have hn : 2 ≤ n := by
    have h1 : 1 ≤ W.card := Finset.card_pos.mpr hWne
    rw [hWcard] at h1; omega
  set top : Fin n := ⟨n - 1, by omega⟩ with htop_def
  have htopval : top.val = n - 1 := by rw [htop_def]
  have htop : ∀ j : Fin n, j ≤ top := by
    intro j; rw [Fin.le_def, htopval]; have := j.isLt; omega
  have hbot0 : (⟨0, by omega⟩ : Fin n).val = 0 := rfl
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · refine absurd ?_ (hbna (⟨0, by omega⟩ : Fin n) hbot0)
      rw [KSubsetCollection.mem_commonAbsent_iff]
      intro T hTW
      have hT0 : T.1 = ∅ := Finset.card_eq_zero.mp (T.2.trans hk0)
      rw [hT0]; exact Finset.notMem_empty _
    · exact hk0
  obtain ⟨E, hE⟩ := KSubsetCollection.exists_belowExteriorSubset hWne htop hn hk hcp hbna
  have hprof : KSubsetCollection.aboveMinProfile W hWne E = ∅ :=
    KSubsetCollection.aboveMinProfile_belowExterior hWsorted hWne htop hE
  -- E ∉ W via the non-top constant coordinate
  obtain ⟨c, hcnetop, hcconst⟩ :=
    KSubsetCollection.exists_nontop_constantCoord hWsorted hWne htop hn hmax
  have hposc : 1 ≤ KSubsetCollection.maxPrefixCount W hWne c :=
    KSubsetCollection.maxPrefixCount_pos hWne hbot0 (hbna _ hbot0) c
  have hEc : KSubset.prefixCount E c = KSubsetCollection.minPrefixCount W hWne c - 1 := by
    rw [hE c, if_neg hcnetop, hcconst]
  have hEW : E ∉ W := by
    intro hin
    have hge : KSubsetCollection.minPrefixCount W hWne c ≤ KSubset.prefixCount E c :=
      KSubsetCollection.minPrefixCount_le hWne hin c
    rw [hEc] at hge
    have hpos : 1 ≤ KSubsetCollection.minPrefixCount W hWne c := by rw [← hcconst]; exact hposc
    omega
  have hcompat : ∀ S ∈ W, KSubset.IsSortedPair E S := by
    intro S hSW
    refine Or.inr (fun t => ?_)
    rw [hE t]
    by_cases ht : t = top
    · subst ht; rw [if_pos rfl, prefixCount_top_eq S htop]; omega
    · rw [if_neg ht]
      have hge := KSubsetCollection.le_maxPrefixCount hWne hSW t
      have hpost := KSubsetCollection.maxPrefixCount_pos hWne hbot0 (hbna _ hbot0) t
      have hwidth := KSubsetCollection.maxPrefixCount_le_minPrefixCount_succ hWsorted hWne t
      have hminle := KSubsetCollection.minPrefixCount_le hWne hSW t
      omega
  refine ⟨E, ?_, hprof⟩
  rw [KSubsetCollection.mem_sameFrameExtensions_iff]
  refine ⟨hEW, ?_, KSubsetCollection.isSorted_insert hWsorted hcompat⟩
  rw [Finset.card_insert_of_notMem hEW, hWcard]; omega

/-- THE UNCONDITIONAL above-endpoint lower bound: a frozen-free wall in the missing-top-rank
configuration has `≥ 2` same-frame extensions — the above-exterior (rank `n-1`) AND the
below/dip-exterior (rank `0`).  No exclusion hypothesis. -/
theorem KSubsetCollection.sameFrameExtensions_two_of_no_frozen_endpoint_full {n k : ℕ}
    {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W) (hWne : W.Nonempty)
    (hWcard : W.card = n - 1) (hfrozen : KSubsetCollection.frozenCoords W = ∅)
    (hmax : ∀ S ∈ W, (KSubsetCollection.aboveMinProfile W hWne S).card ≤ n - 2) :
    2 ≤ (KSubsetCollection.sameFrameExtensions W).card := by
  classical
  have hcp : KSubsetCollection.commonPresent W = ∅ := by
    rw [KSubsetCollection.frozenCoords] at hfrozen
    exact (Finset.union_eq_empty.mp hfrozen).1
  have hca : KSubsetCollection.commonAbsent W = ∅ := by
    rw [KSubsetCollection.frozenCoords] at hfrozen
    exact (Finset.union_eq_empty.mp hfrozen).2
  obtain ⟨T, hTmem, hTprof⟩ :=
    KSubsetCollection.endpoint_below_exterior_mem_sameFrameExtensions hWsorted hWne hWcard hcp
      (fun b _ => by rw [hca]; exact Finset.notMem_empty b) hmax
  have hn : 2 ≤ n := by
    have h1 : 1 ≤ W.card := Finset.card_pos.mpr hWne
    rw [hWcard] at h1; omega
  refine KSubsetCollection.sameFrameExtensions_two_of_no_frozen_endpoint hWsorted hWne hWcard
    hfrozen hmax ⟨T, hTmem, ?_⟩
  rw [hTprof, Finset.card_empty]; omega

/-- **Case (c′)** — top missing rank with the unique common-absent coordinate being `top` itself
(`top ∈ commonAbsent`).  The ABOVE-exterior is invalid here (it needs `top ∉ commonAbsent`); the
relevant same-frame extension is the BELOW/dip-exterior.  Hypotheses: `commonPresent = ∅` and the
bottom coordinate is not common-absent (which holds because the unique frozen coordinate is `top`,
not the bottom — supplied by the dispatcher `…_topEndpoint_full`). -/
theorem KSubsetCollection.sameFrameExtensions_nonempty_of_commonAbsent_oneFrozen_topEndpoint_topFrozen
    {n k : ℕ} {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W)
    (hWne : W.Nonempty) (hWcard : W.card = n - 1)
    (hcp : KSubsetCollection.commonPresent W = ∅)
    (hbna : ∀ b : Fin n, b.val = 0 → b ∉ KSubsetCollection.commonAbsent W)
    (hmax : ∀ S ∈ W, (KSubsetCollection.aboveMinProfile W hWne S).card ≤ n - 2) :
    (KSubsetCollection.sameFrameExtensions W).Nonempty := by
  obtain ⟨E, hEmem, _⟩ :=
    KSubsetCollection.endpoint_below_exterior_mem_sameFrameExtensions
      hWsorted hWne hWcard hcp hbna hmax
  exact ⟨E, hEmem⟩

/-- **Endpoint dispatch (`c = 1`, missing-top-rank)** — combines case (c) (`top ∉ commonAbsent`,
the above-exterior) and case (c′) (`top ∈ commonAbsent`, the below/dip-exterior).  The unique
common-absent coordinate is `c` (`commonAbsent W = {c}`, since `commonPresent = ∅`); the dispatch is
on whether `c` is the top coordinate.  If `c = top`, the bottom (≠ `c`) is not common-absent, so the
dip-exterior applies; if `c ≠ top`, then `top` is not common-absent, so the above-exterior applies. -/
theorem KSubsetCollection.sameFrameExtensions_nonempty_of_commonAbsent_oneFrozen_topEndpoint_full
    {n k : ℕ} {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W)
    (hWne : W.Nonempty) (hWcard : W.card = n - 1) {top : Fin n} (htop : ∀ j : Fin n, j ≤ top)
    (hcp : KSubsetCollection.commonPresent W = ∅)
    {c : Fin n} (hcca : KSubsetCollection.commonAbsent W = {c})
    (hmax : ∀ S ∈ W, (KSubsetCollection.aboveMinProfile W hWne S).card ≤ n - 2) :
    (KSubsetCollection.sameFrameExtensions W).Nonempty := by
  classical
  have hn : 2 ≤ n := by
    have h1 : 1 ≤ W.card := Finset.card_pos.mpr hWne
    rw [hWcard] at h1; omega
  have htopval : top.val = n - 1 := by
    have h1 : n - 1 ≤ top.val := Fin.le_def.mp (htop ⟨n - 1, by omega⟩)
    have h2 := top.isLt
    omega
  by_cases hcTop : c.val + 1 = n
  · -- `c` is the top coordinate ⟹ `top` common-absent ⟹ below/dip-exterior (case c′).
    refine KSubsetCollection.sameFrameExtensions_nonempty_of_commonAbsent_oneFrozen_topEndpoint_topFrozen
      hWsorted hWne hWcard hcp ?_ hmax
    intro b hb hmem
    rw [hcca, Finset.mem_singleton] at hmem
    have hbc : b.val = c.val := congrArg Fin.val hmem
    omega
  · -- `c ≠ top` ⟹ `top ∉ commonAbsent` ⟹ above-exterior (case c).
    refine KSubsetCollection.sameFrameExtensions_nonempty_of_commonAbsent_oneFrozen_topEndpoint
      hWsorted hWne hWcard htop hcp ?_ hmax
    intro hmem
    rw [hcca, Finset.mem_singleton] at hmem
    have htc : top.val = c.val := congrArg Fin.val hmem
    omega

/-- **`c = 1` UP-SIDE EXISTENCE (capstone).**  A codimension-one sorted wall with EXACTLY ONE
frozen coordinate, which is common-absent (`hcabs`, `hone`), has a same-frame extension.  This is
the combinatorial heart of the geometric `c = 1` UP-side existence (for the wall `slift F`,
`commonPresent = ∅` always, so its unique frozen coordinate is common-absent).  PURE missing-rank
DISPATCH (mirrors `noFrozenWallHasTwoExtensions`): rank `0` is always present
(`exists_rank_zero_member`), so the missing rank `m ∈ {1,…,n-1}`.  `m = n-1` ⟹ the endpoint
dispatch (`…_topEndpoint_full`, using `commonPresent = ∅` and `commonAbsent = {c}` derived from
`hone`+`hcabs`); `1 ≤ m ≤ n-2` ⟹ interior, where the two gap coordinates are NON-adjacent
(`…_interior_nonadjacent_gap`) or ADJACENT (`…_interior_adjacent`). -/
theorem KSubsetCollection.sameFrameExtensions_nonempty_of_commonAbsent_oneFrozen {n k : ℕ}
    {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W) (hWne : W.Nonempty)
    (hWcard : W.card = n - 1) {c : Fin n} (hcabs : c ∈ KSubsetCollection.commonAbsent W)
    (hone : (KSubsetCollection.frozenCoords W).card = 1) :
    (KSubsetCollection.sameFrameExtensions W).Nonempty := by
  classical
  have hn : 2 ≤ n := by
    have h1 : 1 ≤ W.card := Finset.card_pos.mpr hWne
    rw [hWcard] at h1; omega
  have hn1 : 0 < n := by omega
  -- `commonPresent = ∅` and `commonAbsent = {c}` from `1`-frozen + `c` common-absent
  have hdisj := KSubsetCollection.commonPresent_disjoint_commonAbsent hWne
  have hsplit : (KSubsetCollection.commonPresent W).card
      + (KSubsetCollection.commonAbsent W).card = 1 := by
    rw [← Finset.card_union_of_disjoint hdisj, ← KSubsetCollection.frozenCoords]; exact hone
  have hcabs_pos : 1 ≤ (KSubsetCollection.commonAbsent W).card := Finset.card_pos.mpr ⟨c, hcabs⟩
  have hcp_empty : KSubsetCollection.commonPresent W = ∅ := by
    rw [← Finset.card_eq_zero]; omega
  have hca_eq : KSubsetCollection.commonAbsent W = {c} := by
    have hcard1 : (KSubsetCollection.commonAbsent W).card = 1 := by omega
    rw [Finset.card_eq_one] at hcard1
    obtain ⟨x, hx⟩ := hcard1
    have hcx : c = x := by
      have hc := hcabs; rw [hx, Finset.mem_singleton] at hc; exact hc
    rw [hx, hcx]
  by_cases hmax : ∀ S ∈ W, (KSubsetCollection.aboveMinProfile W hWne S).card ≤ n - 2
  · -- endpoint: the missing rank is `n - 1`
    have htop : ∀ j : Fin n, j ≤ (⟨n - 1, by omega⟩ : Fin n) := fun j => by
      rw [Fin.le_def]; show j.val ≤ n - 1; have := j.isLt; omega
    exact KSubsetCollection.sameFrameExtensions_nonempty_of_commonAbsent_oneFrozen_topEndpoint_full
      hWsorted hWne hWcard htop hcp_empty hca_eq hmax
  · -- interior: extract `Slo, Shi` (ranks `m∓1`) from the missing rank `m`
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
    -- the gap `U \ L` has two coordinates; dispatch on their adjacency
    have hUL2 : (KSubsetCollection.aboveMinProfile W hWne Shi
        \ KSubsetCollection.aboveMinProfile W hWne Slo).card = 2 := by
      have hdisjUL : Disjoint (KSubsetCollection.aboveMinProfile W hWne Slo)
          (KSubsetCollection.aboveMinProfile W hWne Shi
            \ KSubsetCollection.aboveMinProfile W hWne Slo) :=
        Finset.disjoint_left.mpr (fun a haL haUL => (Finset.mem_sdiff.mp haUL).2 haL)
      have hcU := Finset.card_union_of_disjoint hdisjUL
      rw [Finset.union_sdiff_of_subset hLU] at hcU; omega
    obtain ⟨γ₁, γ₂, hne12, hUL_eq⟩ := Finset.card_eq_two.mp hUL2
    have hγ₁UL : γ₁ ∈ KSubsetCollection.aboveMinProfile W hWne Shi
        \ KSubsetCollection.aboveMinProfile W hWne Slo := by
      rw [hUL_eq]; exact Finset.mem_insert_self _ _
    have hγ₂UL : γ₂ ∈ KSubsetCollection.aboveMinProfile W hWne Shi
        \ KSubsetCollection.aboveMinProfile W hWne Slo := by
      rw [hUL_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hγ₁U : γ₁ ∈ KSubsetCollection.aboveMinProfile W hWne Shi := (Finset.mem_sdiff.mp hγ₁UL).1
    have hγ₁L : γ₁ ∉ KSubsetCollection.aboveMinProfile W hWne Slo := (Finset.mem_sdiff.mp hγ₁UL).2
    have hγ₂U : γ₂ ∈ KSubsetCollection.aboveMinProfile W hWne Shi := (Finset.mem_sdiff.mp hγ₂UL).1
    have hγ₂L : γ₂ ∉ KSubsetCollection.aboveMinProfile W hWne Slo := (Finset.mem_sdiff.mp hγ₂UL).2
    by_cases hadj12 : γ₁.val + 1 = γ₂.val
    · exact KSubsetCollection.sameFrameExtensions_nonempty_of_commonAbsent_oneFrozen_interior_adjacent
        hWsorted hWne hWcard hSloW hShiW hLU hUcard hgap hadj12 hγ₁U hγ₁L hγ₂U hγ₂L hcabs hone
    · by_cases hadj21 : γ₂.val + 1 = γ₁.val
      · exact KSubsetCollection.sameFrameExtensions_nonempty_of_commonAbsent_oneFrozen_interior_adjacent
          hWsorted hWne hWcard hSloW hShiW hLU hUcard hgap hadj21 hγ₂U hγ₂L hγ₁U hγ₁L hcabs hone
      · have hnoadj : ∀ a b : Fin n,
            a ∈ KSubsetCollection.aboveMinProfile W hWne Shi
              \ KSubsetCollection.aboveMinProfile W hWne Slo →
            b ∈ KSubsetCollection.aboveMinProfile W hWne Shi
              \ KSubsetCollection.aboveMinProfile W hWne Slo → a.val + 1 ≠ b.val := by
          intro a b ha hb
          rw [hUL_eq, Finset.mem_insert, Finset.mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · omega
          · exact hadj12
          · exact hadj21
          · omega
        exact KSubsetCollection.sameFrameExtensions_nonempty_of_interior_nonadjacent_gap
          hWsorted hWne hWcard hSloW hShiW hLU hUcard hgap hnoadj

/-! ### Fixed-slice ENDPOINT case (deleting a left/right endpoint weight)

The endpoint deletion gives `≤ 2` (NOT `≤ 1` — see `EndpointDeletionAudit`): the completion
weights are exactly the two EXTERIOR endpoints (`{b, b+n}` for a left endpoint, machine-checked
fibre-`≤1` in `FibreAudit` for small `n,k`).  This reduces the endpoint case to a single
"extreme-weight fibre uniqueness" residual; the weight classification and the reduction are
proved below. -/

/-- Inserting `x` into a consecutive block of `m` to get a block of `m+1` forces `x` to be one
of the two exterior endpoints. -/
theorem interval_insert_consecutive_endpoint {p m x c : ℕ} (hm : 1 ≤ m)
    (heq : insert x (Finset.Ico p (p + m)) = Finset.Ico c (c + (m + 1))) :
    x = p - 1 ∨ x = p + m := by
  have hpmem : p ∈ Finset.Ico p (p + m) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hp1mem : p + m - 1 ∈ Finset.Ico p (p + m) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hp_in : p ∈ Finset.Ico c (c + (m + 1)) := heq ▸ Finset.mem_insert_of_mem hpmem
  have hp1_in : p + m - 1 ∈ Finset.Ico c (c + (m + 1)) := heq ▸ Finset.mem_insert_of_mem hp1mem
  rw [Finset.mem_Ico] at hp_in hp1_in
  have hxin : x ∈ Finset.Ico c (c + (m + 1)) := by
    rw [← heq]; exact Finset.mem_insert_self _ _
  have hxnotin : x ∉ Finset.Ico p (p + m) := by
    intro hx
    have hself : insert x (Finset.Ico p (p + m)) = Finset.Ico p (p + m) :=
      Finset.insert_eq_self.mpr hx
    rw [hself] at heq
    have := congrArg Finset.card heq
    rw [Nat.card_Ico, Nat.card_Ico] at this; omega
  rw [Finset.mem_Ico] at hxin
  rw [Finset.mem_Ico] at hxnotin
  push_neg at hxnotin
  omega

/-- Left-endpoint deletion: completion weights are `b` or `b+n`. -/
theorem KSubsetCollection.sameFrame_extension_weight_left_endpoint {n k : ℕ} (hn : 2 ≤ n)
    {C : Finset (KSubset n k)} (hC : KSubsetCollection.IsMaximalSorted C)
    {S₀ T : KSubset n k} (hS₀ : S₀ ∈ C) {b : ℕ}
    (himg : C.image KSubset.prefixWeight = Finset.Ico b (b + n))
    (hleft : KSubset.prefixWeight S₀ = b)
    (hT : T ∈ KSubsetCollection.sameFrameExtensions (C.erase S₀)) :
    KSubset.prefixWeight T = b ∨ KSubset.prefixWeight T = b + n := by
  classical
  obtain ⟨hcardC, hCsorted⟩ := hC
  have himgA : (C.erase S₀).image KSubset.prefixWeight = Finset.Ico (b + 1) (b + n) := by
    rw [KSubsetCollection.prefixWeight_image_erase_eq_delete hCsorted hS₀, himg, hleft]
    ext y; rw [Finset.mem_erase, Finset.mem_Ico, Finset.mem_Ico]; omega
  rw [mem_sameFrameExtensions_iff] at hT
  obtain ⟨c, hc⟩ := KSubsetCollection.exists_base_weight_image_eq_Ico_of_isMaximalSorted hT.2
  rw [Finset.image_insert, himgA] at hc
  have hc' : insert (KSubset.prefixWeight T) (Finset.Ico (b + 1) ((b + 1) + (n - 1)))
      = Finset.Ico c (c + ((n - 1) + 1)) := by
    rw [show (b + 1) + (n - 1) = b + n by omega, show (n - 1) + 1 = n by omega]; exact hc
  rcases interval_insert_consecutive_endpoint (by omega) hc' with h | h
  · left; omega
  · right; omega

/-- Right-endpoint deletion: completion weights are `b-1` or `b+n-1`. -/
theorem KSubsetCollection.sameFrame_extension_weight_right_endpoint {n k : ℕ} (hn : 2 ≤ n)
    {C : Finset (KSubset n k)} (hC : KSubsetCollection.IsMaximalSorted C)
    {S₀ T : KSubset n k} (hS₀ : S₀ ∈ C) {b : ℕ}
    (himg : C.image KSubset.prefixWeight = Finset.Ico b (b + n))
    (hright : KSubset.prefixWeight S₀ = b + n - 1)
    (hT : T ∈ KSubsetCollection.sameFrameExtensions (C.erase S₀)) :
    KSubset.prefixWeight T = b - 1 ∨ KSubset.prefixWeight T = b + n - 1 := by
  classical
  obtain ⟨hcardC, hCsorted⟩ := hC
  have himgA : (C.erase S₀).image KSubset.prefixWeight = Finset.Ico b (b + n - 1) := by
    rw [KSubsetCollection.prefixWeight_image_erase_eq_delete hCsorted hS₀, himg, hright]
    ext y; rw [Finset.mem_erase, Finset.mem_Ico, Finset.mem_Ico]; omega
  rw [mem_sameFrameExtensions_iff] at hT
  obtain ⟨c, hc⟩ := KSubsetCollection.exists_base_weight_image_eq_Ico_of_isMaximalSorted hT.2
  rw [Finset.image_insert, himgA] at hc
  have hc' : insert (KSubset.prefixWeight T) (Finset.Ico b (b + (n - 1)))
      = Finset.Ico c (c + ((n - 1) + 1)) := by
    rw [show b + (n - 1) = b + n - 1 by omega, show (n - 1) + 1 = n by omega]; exact hc
  rcases interval_insert_consecutive_endpoint (by omega) hc' with h | h
  · left; omega
  · right; omega

/-- Reduction: a left-endpoint deletion has `≤ 2` completions provided each of its two
exterior-weight fibres has `≤ 1`. -/
theorem KSubsetCollection.sameFrame_extensions_card_le_two_of_erased_left_endpoint_of_fibre
    {n k : ℕ} (hn : 2 ≤ n) {C : Finset (KSubset n k)} (hC : KSubsetCollection.IsMaximalSorted C)
    {S₀ : KSubset n k} (hS₀ : S₀ ∈ C) {b : ℕ}
    (himg : C.image KSubset.prefixWeight = Finset.Ico b (b + n))
    (hleft : KSubset.prefixWeight S₀ = b)
    (hfib_b : ((KSubsetCollection.sameFrameExtensions (C.erase S₀)).filter
      (fun T => KSubset.prefixWeight T = b)).card ≤ 1)
    (hfib_bn : ((KSubsetCollection.sameFrameExtensions (C.erase S₀)).filter
      (fun T => KSubset.prefixWeight T = b + n)).card ≤ 1) :
    (KSubsetCollection.sameFrameExtensions (C.erase S₀)).card ≤ 2 := by
  classical
  set E := KSubsetCollection.sameFrameExtensions (C.erase S₀) with hE
  have hsub : E ⊆ E.filter (fun T => KSubset.prefixWeight T = b) ∪
      E.filter (fun T => KSubset.prefixWeight T = b + n) := by
    intro T hT
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases KSubsetCollection.sameFrame_extension_weight_left_endpoint hn hC hS₀ himg hleft hT with h | h
    · exact Or.inl ⟨hT, h⟩
    · exact Or.inr ⟨hT, h⟩
  calc E.card ≤ (E.filter (fun T => KSubset.prefixWeight T = b) ∪
        E.filter (fun T => KSubset.prefixWeight T = b + n)).card := Finset.card_le_card hsub
    _ ≤ (E.filter (fun T => KSubset.prefixWeight T = b)).card +
        (E.filter (fun T => KSubset.prefixWeight T = b + n)).card := Finset.card_union_le _ _
    _ ≤ 2 := by omega

/-- Reduction: a right-endpoint deletion has `≤ 2` completions provided each of its two
exterior-weight fibres has `≤ 1`. -/
theorem KSubsetCollection.sameFrame_extensions_card_le_two_of_erased_right_endpoint_of_fibre
    {n k : ℕ} (hn : 2 ≤ n) {C : Finset (KSubset n k)} (hC : KSubsetCollection.IsMaximalSorted C)
    {S₀ : KSubset n k} (hS₀ : S₀ ∈ C) {b : ℕ}
    (himg : C.image KSubset.prefixWeight = Finset.Ico b (b + n))
    (hright : KSubset.prefixWeight S₀ = b + n - 1)
    (hfib1 : ((KSubsetCollection.sameFrameExtensions (C.erase S₀)).filter
      (fun T => KSubset.prefixWeight T = b - 1)).card ≤ 1)
    (hfib2 : ((KSubsetCollection.sameFrameExtensions (C.erase S₀)).filter
      (fun T => KSubset.prefixWeight T = b + n - 1)).card ≤ 1) :
    (KSubsetCollection.sameFrameExtensions (C.erase S₀)).card ≤ 2 := by
  classical
  set E := KSubsetCollection.sameFrameExtensions (C.erase S₀) with hE
  have hsub : E ⊆ E.filter (fun T => KSubset.prefixWeight T = b - 1) ∪
      E.filter (fun T => KSubset.prefixWeight T = b + n - 1) := by
    intro T hT
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases KSubsetCollection.sameFrame_extension_weight_right_endpoint hn hC hS₀ himg hright hT with h | h
    · exact Or.inl ⟨hT, h⟩
    · exact Or.inr ⟨hT, h⟩
  calc E.card ≤ (E.filter (fun T => KSubset.prefixWeight T = b - 1) ∪
        E.filter (fun T => KSubset.prefixWeight T = b + n - 1)).card := Finset.card_le_card hsub
    _ ≤ (E.filter (fun T => KSubset.prefixWeight T = b - 1)).card +
        (E.filter (fun T => KSubset.prefixWeight T = b + n - 1)).card := Finset.card_union_le _ _
    _ ≤ 2 := by omega

/-- Weight trichotomy: the erased vertex is a left endpoint, a right endpoint, or interior. -/
theorem KSubsetCollection.prefixWeight_trichotomy_of_mem {n k : ℕ}
    {C : Finset (KSubset n k)} {S₀ : KSubset n k} (hS₀ : S₀ ∈ C) {b : ℕ}
    (himg : C.image KSubset.prefixWeight = Finset.Ico b (b + n)) :
    KSubset.prefixWeight S₀ = b ∨ KSubset.prefixWeight S₀ = b + n - 1 ∨
      (b < KSubset.prefixWeight S₀ ∧ KSubset.prefixWeight S₀ < b + n - 1) := by
  have hmem : KSubset.prefixWeight S₀ ∈ Finset.Ico b (b + n) := by
    rw [← himg]; exact Finset.mem_image_of_mem _ hS₀
  rw [Finset.mem_Ico] at hmem
  omega


/-! ### Fixed-slice ENDPOINT fibre uniqueness (the extreme-weight residual) -/

-- helper: two functions agreeing off a ≤1-element set with equal sums are equal.
theorem eq_of_agree_off_le_one {n : ℕ} {f g : Fin n → ℕ} {D : Finset (Fin n)}
    (hD : D.card ≤ 1) (hagree : ∀ t ∉ D, f t = g t)
    (hsum : ∑ t : Fin n, f t = ∑ t : Fin n, g t) : ∀ t, f t = g t := by
  classical
  -- ∑ over Dᶜ agree; so ∑ over D agree; with |D| ≤ 1, conclude
  have hsplitf : ∑ t : Fin n, f t = ∑ t ∈ D, f t + ∑ t ∈ Dᶜ, f t := by
    rw [← Finset.sum_add_sum_compl D f]
  have hsplitg : ∑ t : Fin n, g t = ∑ t ∈ D, g t + ∑ t ∈ Dᶜ, g t := by
    rw [← Finset.sum_add_sum_compl D g]
  have hcompl : ∑ t ∈ Dᶜ, f t = ∑ t ∈ Dᶜ, g t := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_compl] at ht
    exact hagree t ht
  have hDsum : ∑ t ∈ D, f t = ∑ t ∈ D, g t := by
    rw [hsplitf, hcompl] at hsum; omega
  intro t
  by_cases htD : t ∈ D
  · -- D = {t} since |D| ≤ 1 and t ∈ D
    have hDeq : D = {t} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨htD, fun y hy => ?_⟩
      by_contra hyt
      have : 2 ≤ D.card := by
        have : ({t, y} : Finset (Fin n)) ⊆ D := by
          intro z hz; rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        calc 2 = ({t, y} : Finset (Fin n)).card := by rw [Finset.card_pair (Ne.symm hyt)]
          _ ≤ D.card := Finset.card_le_card this
      omega
    rw [hDeq, Finset.sum_singleton, Finset.sum_singleton] at hDsum
    exact hDsum
  · exact hagree t htD

-- the "split" coords of a wall: where some member exceeds the min profile.
-- KEY: a sorted (n-1)-collection has ≤ 2 flat (non-split) coords.
theorem flat_card_le_two {n k : ℕ} (hn : 2 ≤ n) {A : Finset (KSubset n k)}
    (hA_sorted : KSubsetCollection.IsSorted A) (hA_ne : A.Nonempty) (hAcard : A.card = n - 1) :
    (Finset.univ.filter (fun t => ∀ S ∈ A,
      KSubset.prefixCount S t = KSubsetCollection.minPrefixCount A hA_ne t)).card ≤ 2 := by
  classical
  -- the above-min profile cards: n-1 distinct values in [0,n), so the max is ≥ n-2
  set M := A.image (fun S => (KSubsetCollection.aboveMinProfile A hA_ne S).card) with hM
  have hMcard : M.card = n - 1 := by
    rw [hM, Finset.card_image_of_injOn
      (KSubsetCollection.aboveMinProfile_card_injective_on hA_sorted hA_ne), hAcard]
  have hMne : M.Nonempty := by rw [hM]; exact hA_ne.image _
  have hMsub : M ⊆ Finset.range n := by
    intro x hx
    rw [hM, Finset.mem_image] at hx
    obtain ⟨S, _, rfl⟩ := hx
    exact Finset.mem_range.mpr (KSubsetCollection.aboveMinProfile_card_lt (by omega) hA_ne S)
  have hmax : n - 2 ≤ M.max' hMne := by
    by_contra h
    push_neg at h
    have : M ⊆ Finset.range (n - 2) := by
      intro x hx
      have := Finset.le_max' M x hx
      exact Finset.mem_range.mpr (by omega)
    have := Finset.card_le_card this
    rw [hMcard, Finset.card_range] at this; omega
  -- pick S* achieving the max card
  obtain ⟨Sstar, hSstar, hSstareq⟩ := Finset.mem_image.mp (Finset.max'_mem M hMne)
  -- the flat set is disjoint from aboveMinProfile Sstar (which has card ≥ n-2)
  have hdisj : (Finset.univ.filter (fun t => ∀ S ∈ A,
      KSubset.prefixCount S t = KSubsetCollection.minPrefixCount A hA_ne t)) ⊆
      (KSubsetCollection.aboveMinProfile A hA_ne Sstar)ᶜ := by
    intro t ht
    rw [Finset.mem_filter] at ht
    rw [Finset.mem_compl, KSubsetCollection.mem_aboveMinProfile_iff]
    have := ht.2 Sstar hSstar
    omega
  calc (Finset.univ.filter _).card
      ≤ (KSubsetCollection.aboveMinProfile A hA_ne Sstar)ᶜ.card := Finset.card_le_card hdisj
    _ = n - (KSubsetCollection.aboveMinProfile A hA_ne Sstar).card := by
        rw [Finset.card_compl, Fintype.card_fin]
    _ ≤ 2 := by
        have : (KSubsetCollection.aboveMinProfile A hA_ne Sstar).card = M.max' hMne := hSstareq
        rw [this]; omega

-- (the top-coordinate facts `prefixCount_top_eq` / `minPrefixCount_top_eq` are in the
-- interior-existence section above.)

-- DIP fibre uniqueness (covers left-refill weight b and right-exterior weight b-1).
theorem KSubsetCollection.dip_completions_eq {n k : ℕ} (hn : 2 ≤ n)
    {A : Finset (KSubset n k)} (hA_sorted : KSubsetCollection.IsSorted A) (hA_ne : A.Nonempty)
    (hAcard : A.card = n - 1) {T U : KSubset n k}
    (hT : T ∈ KSubsetCollection.sameFrameExtensions A)
    (hU : U ∈ KSubsetCollection.sameFrameExtensions A)
    (hTdip : ∀ t, KSubset.prefixCount T t ≤ KSubsetCollection.minPrefixCount A hA_ne t)
    (hUdip : ∀ t, KSubset.prefixCount U t ≤ KSubsetCollection.minPrefixCount A hA_ne t)
    (hwt : KSubset.prefixWeight T = KSubset.prefixWeight U) : T = U := by
  classical
  -- direction: a dip completion is sorted-AFTER each wall member
  have hdir : ∀ (V : KSubset n k), V ∈ KSubsetCollection.sameFrameExtensions A →
      (∀ t, KSubset.prefixCount V t ≤ KSubsetCollection.minPrefixCount A hA_ne t) →
      ∀ S ∈ A, KSubset.SortedBefore S V := by
    intro V hV hVdip S hS
    have hVnotin := ((KSubsetCollection.mem_sameFrameExtensions_iff A V).mp hV).1
    rcases KSubsetCollection.extension_sortedWith_wall hV hS with hb | hb
    · exfalso
      apply hVnotin
      have : V = S := KSubset.prefixCount_injective (fun t => le_antisymm
        (le_trans (hVdip t) (KSubsetCollection.minPrefixCount_le hA_ne hS t)) (hb t).1)
      rw [this]; exact hS
    · exact hb
  apply KSubset.prefixCount_injective
  set last : Fin n := ⟨n - 1, by omega⟩ with hlast_def
  have htop : ∀ j : Fin n, j ≤ last := by
    intro j; rw [hlast_def]; simp only [Fin.le_def]; have := j.isLt; omega
  set flatSet := Finset.univ.filter (fun t => ∀ S ∈ A,
    KSubset.prefixCount S t = KSubsetCollection.minPrefixCount A hA_ne t) with hflat
  have hlast_flat : last ∈ flatSet := by
    rw [hflat, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun S hS => ?_⟩
    rw [prefixCount_top_eq S htop, minPrefixCount_top_eq hA_ne htop]
  have hDcard : (flatSet.erase last).card ≤ 1 := by
    have h2 := flat_card_le_two hn hA_sorted hA_ne hAcard
    rw [← hflat] at h2
    rw [Finset.card_erase_of_mem hlast_flat]
    omega
  have hagree : ∀ t ∉ flatSet.erase last,
      KSubset.prefixCount T t = KSubset.prefixCount U t := by
    intro t ht
    by_cases htf : t ∈ flatSet
    · -- t ∈ flatSet but ∉ erase last ⟹ t = last
      have htlast : t = last := by
        by_contra hne
        exact ht (Finset.mem_erase.mpr ⟨hne, htf⟩)
      rw [htlast, prefixCount_top_eq T htop, prefixCount_top_eq U htop]
    · -- t split: both forced to minPrefixCount (dip)
      rw [hflat, Finset.mem_filter] at htf
      push_neg at htf
      obtain ⟨S, hS, hSne⟩ := htf (Finset.mem_univ t)
      have hSge := KSubsetCollection.minPrefixCount_le hA_ne hS t
      have hSgt : KSubsetCollection.minPrefixCount A hA_ne t + 1 ≤ KSubset.prefixCount S t := by omega
      have hTval : KSubset.prefixCount T t = KSubsetCollection.minPrefixCount A hA_ne t := by
        have := (hdir T hT hTdip S hS t).2
        have := hTdip t
        omega
      have hUval : KSubset.prefixCount U t = KSubsetCollection.minPrefixCount A hA_ne t := by
        have := (hdir U hU hUdip S hS t).2
        have := hUdip t
        omega
      rw [hTval, hUval]
  exact eq_of_agree_off_le_one hDcard hagree hwt

-- RISE fibre uniqueness (covers left-exterior weight b+n and right-refill weight b+n-1).
theorem KSubsetCollection.rise_completions_eq {n k : ℕ} (hn : 2 ≤ n)
    {A : Finset (KSubset n k)} (hA_sorted : KSubsetCollection.IsSorted A) (hA_ne : A.Nonempty)
    (hAcard : A.card = n - 1) {T U : KSubset n k}
    (hTabove : ∀ S ∈ A, ∀ t, KSubset.prefixCount S t ≤ KSubset.prefixCount T t)
    (hUabove : ∀ S ∈ A, ∀ t, KSubset.prefixCount S t ≤ KSubset.prefixCount U t)
    (hTband : ∀ t, KSubset.prefixCount T t ≤ KSubsetCollection.minPrefixCount A hA_ne t + 1)
    (hUband : ∀ t, KSubset.prefixCount U t ≤ KSubsetCollection.minPrefixCount A hA_ne t + 1)
    (hwt : KSubset.prefixWeight T = KSubset.prefixWeight U) : T = U := by
  classical
  apply KSubset.prefixCount_injective
  set last : Fin n := ⟨n - 1, by omega⟩ with hlast_def
  have htop : ∀ j : Fin n, j ≤ last := by
    intro j; rw [hlast_def]; simp only [Fin.le_def]; have := j.isLt; omega
  set flatSet := Finset.univ.filter (fun t => ∀ S ∈ A,
    KSubset.prefixCount S t = KSubsetCollection.minPrefixCount A hA_ne t) with hflat
  have hlast_flat : last ∈ flatSet := by
    rw [hflat, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun S hS => ?_⟩
    rw [prefixCount_top_eq S htop, minPrefixCount_top_eq hA_ne htop]
  have hDcard : (flatSet.erase last).card ≤ 1 := by
    have h2 := flat_card_le_two hn hA_sorted hA_ne hAcard
    rw [← hflat] at h2
    rw [Finset.card_erase_of_mem hlast_flat]
    omega
  have hagree : ∀ t ∉ flatSet.erase last,
      KSubset.prefixCount T t = KSubset.prefixCount U t := by
    intro t ht
    by_cases htf : t ∈ flatSet
    · have htlast : t = last := by
        by_contra hne
        exact ht (Finset.mem_erase.mpr ⟨hne, htf⟩)
      rw [htlast, prefixCount_top_eq T htop, prefixCount_top_eq U htop]
    · rw [hflat, Finset.mem_filter] at htf
      push_neg at htf
      obtain ⟨S, hS, hSne⟩ := htf (Finset.mem_univ t)
      have hSge := KSubsetCollection.minPrefixCount_le hA_ne hS t
      have hSgt : KSubsetCollection.minPrefixCount A hA_ne t + 1 ≤ KSubset.prefixCount S t := by omega
      have hTval : KSubset.prefixCount T t = KSubsetCollection.minPrefixCount A hA_ne t + 1 := by
        have := hTabove S hS t; have := hTband t; omega
      have hUval : KSubset.prefixCount U t = KSubsetCollection.minPrefixCount A hA_ne t + 1 := by
        have := hUabove S hS t; have := hUband t; omega
      rw [hTval, hUval]
  exact eq_of_agree_off_le_one hDcard hagree hwt

-- direction helpers (a wall member and a completion are sorted in the weight order)
theorem KSubsetCollection.sortedBefore_wall_of_weight_gt {n k : ℕ} {A : Finset (KSubset n k)}
    {V S : KSubset n k} (hV : V ∈ KSubsetCollection.sameFrameExtensions A) (hS : S ∈ A)
    (hgt : KSubset.prefixWeight V < KSubset.prefixWeight S) : KSubset.SortedBefore S V := by
  have hVnotin := ((KSubsetCollection.mem_sameFrameExtensions_iff A V).mp hV).1
  rcases KSubsetCollection.extension_sortedWith_wall hV hS with hb | hb
  · exfalso
    have hne : V ≠ S := fun h => hVnotin (h ▸ hS)
    have := hb.prefixWeight_lt hne
    omega
  · exact hb

theorem KSubsetCollection.sortedBefore_wall_of_weight_lt {n k : ℕ} {A : Finset (KSubset n k)}
    {V S : KSubset n k} (hV : V ∈ KSubsetCollection.sameFrameExtensions A) (hS : S ∈ A)
    (hlt : KSubset.prefixWeight S < KSubset.prefixWeight V) : KSubset.SortedBefore V S := by
  have hVnotin := ((KSubsetCollection.mem_sameFrameExtensions_iff A V).mp hV).1
  rcases KSubsetCollection.extension_sortedWith_wall hV hS with hb | hb
  · exact hb
  · exfalso
    have hne : S ≠ V := fun h => hVnotin (h ▸ hS)
    have := hb.prefixWeight_lt hne
    omega

theorem KSubsetCollection.sameFrameExtensions_left_refill_fibre_card_le_one {n k : ℕ} (hn : 2 ≤ n)
    {C : Finset (KSubset n k)} (hC : KSubsetCollection.IsMaximalSorted C)
    {S₀ : KSubset n k} (hS₀ : S₀ ∈ C) {b : ℕ}
    (himg : C.image KSubset.prefixWeight = Finset.Ico b (b + n))
    (hleft : KSubset.prefixWeight S₀ = b) :
    ((KSubsetCollection.sameFrameExtensions (C.erase S₀)).filter
      (fun T => KSubset.prefixWeight T = b)).card ≤ 1 := by
  classical
  obtain ⟨hcardC, hCsorted⟩ := hC
  set A := C.erase S₀ with hA
  have hAsorted : KSubsetCollection.IsSorted A :=
    fun I hI J hJ hIJ => hCsorted I (Finset.mem_of_mem_erase hI) J (Finset.mem_of_mem_erase hJ) hIJ
  have hAcard : A.card = n - 1 := by rw [hA, Finset.card_erase_of_mem hS₀, hcardC]
  have hAne : A.Nonempty := by rw [← Finset.card_pos, hAcard]; omega
  have himgA : A.image KSubset.prefixWeight = Finset.Ico (b + 1) (b + n) := by
    rw [hA, KSubsetCollection.prefixWeight_image_erase_eq_delete hCsorted hS₀, himg, hleft]
    ext y; rw [Finset.mem_erase, Finset.mem_Ico, Finset.mem_Ico]; omega
  have hSwt : ∀ S ∈ A, b + 1 ≤ KSubset.prefixWeight S := by
    intro S hS
    have hm : KSubset.prefixWeight S ∈ A.image KSubset.prefixWeight := Finset.mem_image_of_mem _ hS
    rw [himgA, Finset.mem_Ico] at hm; omega
  have hdip : ∀ V ∈ KSubsetCollection.sameFrameExtensions A, KSubset.prefixWeight V = b →
      ∀ t, KSubset.prefixCount V t ≤ KSubsetCollection.minPrefixCount A hAne t := by
    intro V hV hVw t
    apply Finset.le_min'
    intro x hx
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
    have hgt : KSubset.prefixWeight V < KSubset.prefixWeight S := by
      rw [hVw]; have := hSwt S hS; omega
    exact (KSubsetCollection.sortedBefore_wall_of_weight_gt hV hS hgt t).1
  rw [Finset.card_le_one]
  intro T hT U hU
  rw [Finset.mem_filter] at hT hU
  exact KSubsetCollection.dip_completions_eq hn hAsorted hAne hAcard hT.1 hU.1
    (hdip T hT.1 hT.2) (hdip U hU.1 hU.2) (by rw [hT.2, hU.2])

theorem KSubsetCollection.sameFrameExtensions_left_exterior_fibre_card_le_one {n k : ℕ} (hn : 2 ≤ n)
    {C : Finset (KSubset n k)} (hC : KSubsetCollection.IsMaximalSorted C)
    {S₀ : KSubset n k} (hS₀ : S₀ ∈ C) {b : ℕ}
    (himg : C.image KSubset.prefixWeight = Finset.Ico b (b + n))
    (hleft : KSubset.prefixWeight S₀ = b) :
    ((KSubsetCollection.sameFrameExtensions (C.erase S₀)).filter
      (fun T => KSubset.prefixWeight T = b + n)).card ≤ 1 := by
  classical
  obtain ⟨hcardC, hCsorted⟩ := hC
  set A := C.erase S₀ with hA
  have hAsorted : KSubsetCollection.IsSorted A :=
    fun I hI J hJ hIJ => hCsorted I (Finset.mem_of_mem_erase hI) J (Finset.mem_of_mem_erase hJ) hIJ
  have hAcard : A.card = n - 1 := by rw [hA, Finset.card_erase_of_mem hS₀, hcardC]
  have hAne : A.Nonempty := by rw [← Finset.card_pos, hAcard]; omega
  have himgA : A.image KSubset.prefixWeight = Finset.Ico (b + 1) (b + n) := by
    rw [hA, KSubsetCollection.prefixWeight_image_erase_eq_delete hCsorted hS₀, himg, hleft]
    ext y; rw [Finset.mem_erase, Finset.mem_Ico, Finset.mem_Ico]; omega
  have hSwt : ∀ S ∈ A, KSubset.prefixWeight S ≤ b + n - 1 := by
    intro S hS
    have hm : KSubset.prefixWeight S ∈ A.image KSubset.prefixWeight := Finset.mem_image_of_mem _ hS
    rw [himgA, Finset.mem_Ico] at hm; omega
  have habove : ∀ V ∈ KSubsetCollection.sameFrameExtensions A, KSubset.prefixWeight V = b + n →
      ∀ S ∈ A, ∀ t, KSubset.prefixCount S t ≤ KSubset.prefixCount V t := by
    intro V hV hVw S hS t
    have hlt : KSubset.prefixWeight S < KSubset.prefixWeight V := by
      rw [hVw]; have := hSwt S hS; omega
    exact (KSubsetCollection.sortedBefore_wall_of_weight_lt hV hS hlt t).1
  have hband : ∀ V ∈ KSubsetCollection.sameFrameExtensions A, KSubset.prefixWeight V = b + n →
      ∀ t, KSubset.prefixCount V t ≤ KSubsetCollection.minPrefixCount A hAne t + 1 := by
    intro V hV hVw t
    have hkey : KSubset.prefixCount V t - 1 ≤ KSubsetCollection.minPrefixCount A hAne t := by
      apply Finset.le_min'
      intro x hx
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
      have hlt : KSubset.prefixWeight S < KSubset.prefixWeight V := by
        rw [hVw]; have := hSwt S hS; omega
      have := (KSubsetCollection.sortedBefore_wall_of_weight_lt hV hS hlt t).2
      omega
    omega
  rw [Finset.card_le_one]
  intro T hT U hU
  rw [Finset.mem_filter] at hT hU
  exact KSubsetCollection.rise_completions_eq hn hAsorted hAne hAcard
    (habove T hT.1 hT.2) (habove U hU.1 hU.2) (hband T hT.1 hT.2) (hband U hU.1 hU.2)
    (by rw [hT.2, hU.2])

theorem KSubsetCollection.weight_ne_wall {n k : ℕ} {A : Finset (KSubset n k)}
    {V S : KSubset n k} (hV : V ∈ KSubsetCollection.sameFrameExtensions A) (hS : S ∈ A) :
    KSubset.prefixWeight V ≠ KSubset.prefixWeight S := by
  have hVnotin := ((KSubsetCollection.mem_sameFrameExtensions_iff A V).mp hV).1
  have hne : V ≠ S := fun h => hVnotin (h ▸ hS)
  rcases KSubsetCollection.extension_sortedWith_wall hV hS with hb | hb
  · have := hb.prefixWeight_lt hne; omega
  · have := hb.prefixWeight_lt (Ne.symm hne); omega

theorem KSubsetCollection.sameFrameExtensions_right_refill_fibre_card_le_one {n k : ℕ} (hn : 2 ≤ n)
    {C : Finset (KSubset n k)} (hC : KSubsetCollection.IsMaximalSorted C)
    {S₀ : KSubset n k} (hS₀ : S₀ ∈ C) {b : ℕ}
    (himg : C.image KSubset.prefixWeight = Finset.Ico b (b + n))
    (hright : KSubset.prefixWeight S₀ = b + n - 1) :
    ((KSubsetCollection.sameFrameExtensions (C.erase S₀)).filter
      (fun T => KSubset.prefixWeight T = b + n - 1)).card ≤ 1 := by
  classical
  obtain ⟨hcardC, hCsorted⟩ := hC
  set A := C.erase S₀ with hA
  have hAsorted : KSubsetCollection.IsSorted A :=
    fun I hI J hJ hIJ => hCsorted I (Finset.mem_of_mem_erase hI) J (Finset.mem_of_mem_erase hJ) hIJ
  have hAcard : A.card = n - 1 := by rw [hA, Finset.card_erase_of_mem hS₀, hcardC]
  have hAne : A.Nonempty := by rw [← Finset.card_pos, hAcard]; omega
  have himgA : A.image KSubset.prefixWeight = Finset.Ico b (b + n - 1) := by
    rw [hA, KSubsetCollection.prefixWeight_image_erase_eq_delete hCsorted hS₀, himg, hright]
    ext y; rw [Finset.mem_erase, Finset.mem_Ico, Finset.mem_Ico]; omega
  have hSwt : ∀ S ∈ A, KSubset.prefixWeight S ≤ b + n - 2 := by
    intro S hS
    have hm : KSubset.prefixWeight S ∈ A.image KSubset.prefixWeight := Finset.mem_image_of_mem _ hS
    rw [himgA, Finset.mem_Ico] at hm; omega
  have habove : ∀ V ∈ KSubsetCollection.sameFrameExtensions A, KSubset.prefixWeight V = b + n - 1 →
      ∀ S ∈ A, ∀ t, KSubset.prefixCount S t ≤ KSubset.prefixCount V t := by
    intro V hV hVw S hS t
    have hlt : KSubset.prefixWeight S < KSubset.prefixWeight V := by
      rw [hVw]; have := hSwt S hS; omega
    exact (KSubsetCollection.sortedBefore_wall_of_weight_lt hV hS hlt t).1
  have hband : ∀ V ∈ KSubsetCollection.sameFrameExtensions A, KSubset.prefixWeight V = b + n - 1 →
      ∀ t, KSubset.prefixCount V t ≤ KSubsetCollection.minPrefixCount A hAne t + 1 := by
    intro V hV hVw t
    have hkey : KSubset.prefixCount V t - 1 ≤ KSubsetCollection.minPrefixCount A hAne t := by
      apply Finset.le_min'
      intro x hx
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
      have hlt : KSubset.prefixWeight S < KSubset.prefixWeight V := by
        rw [hVw]; have := hSwt S hS; omega
      have := (KSubsetCollection.sortedBefore_wall_of_weight_lt hV hS hlt t).2
      omega
    omega
  rw [Finset.card_le_one]
  intro T hT U hU
  rw [Finset.mem_filter] at hT hU
  exact KSubsetCollection.rise_completions_eq hn hAsorted hAne hAcard
    (habove T hT.1 hT.2) (habove U hU.1 hU.2) (hband T hT.1 hT.2) (hband U hU.1 hU.2)
    (by rw [hT.2, hU.2])

theorem KSubsetCollection.sameFrameExtensions_right_exterior_fibre_card_le_one {n k : ℕ} (hn : 2 ≤ n)
    {C : Finset (KSubset n k)} (hC : KSubsetCollection.IsMaximalSorted C)
    {S₀ : KSubset n k} (hS₀ : S₀ ∈ C) {b : ℕ}
    (himg : C.image KSubset.prefixWeight = Finset.Ico b (b + n))
    (hright : KSubset.prefixWeight S₀ = b + n - 1) :
    ((KSubsetCollection.sameFrameExtensions (C.erase S₀)).filter
      (fun T => KSubset.prefixWeight T = b - 1)).card ≤ 1 := by
  classical
  obtain ⟨hcardC, hCsorted⟩ := hC
  set A := C.erase S₀ with hA
  have hAsorted : KSubsetCollection.IsSorted A :=
    fun I hI J hJ hIJ => hCsorted I (Finset.mem_of_mem_erase hI) J (Finset.mem_of_mem_erase hJ) hIJ
  have hAcard : A.card = n - 1 := by rw [hA, Finset.card_erase_of_mem hS₀, hcardC]
  have hAne : A.Nonempty := by rw [← Finset.card_pos, hAcard]; omega
  have himgA : A.image KSubset.prefixWeight = Finset.Ico b (b + n - 1) := by
    rw [hA, KSubsetCollection.prefixWeight_image_erase_eq_delete hCsorted hS₀, himg, hright]
    ext y; rw [Finset.mem_erase, Finset.mem_Ico, Finset.mem_Ico]; omega
  have hSwt : ∀ S ∈ A, b ≤ KSubset.prefixWeight S := by
    intro S hS
    have hm : KSubset.prefixWeight S ∈ A.image KSubset.prefixWeight := Finset.mem_image_of_mem _ hS
    rw [himgA, Finset.mem_Ico] at hm; omega
  have hdip : ∀ V ∈ KSubsetCollection.sameFrameExtensions A, KSubset.prefixWeight V = b - 1 →
      ∀ t, KSubset.prefixCount V t ≤ KSubsetCollection.minPrefixCount A hAne t := by
    intro V hV hVw t
    apply Finset.le_min'
    intro x hx
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
    have hgt : KSubset.prefixWeight V < KSubset.prefixWeight S := by
      have h1 := hSwt S hS
      have h2 := KSubsetCollection.weight_ne_wall hV hS
      rw [hVw] at h2 ⊢; omega
    exact (KSubsetCollection.sortedBefore_wall_of_weight_gt hV hS hgt t).1
  rw [Finset.card_le_one]
  intro T hT U hU
  rw [Finset.mem_filter] at hT hU
  exact KSubsetCollection.dip_completions_eq hn hAsorted hAne hAcard hT.1 hU.1
    (hdip T hT.1 hT.2) (hdip U hU.1 hU.2) (by rw [hT.2, hU.2])

/-! ### Fixed-slice bound: unconditional endpoints, then the full theorem -/

/-- Left-endpoint deletion: `≤ 2` completions (unconditional). -/
theorem KSubsetCollection.sameFrame_extensions_card_le_two_of_erased_left_endpoint {n k : ℕ}
    (hn : 2 ≤ n) {C : Finset (KSubset n k)} (hC : KSubsetCollection.IsMaximalSorted C)
    {S₀ : KSubset n k} (hS₀ : S₀ ∈ C) {b : ℕ}
    (himg : C.image KSubset.prefixWeight = Finset.Ico b (b + n))
    (hleft : KSubset.prefixWeight S₀ = b) :
    (KSubsetCollection.sameFrameExtensions (C.erase S₀)).card ≤ 2 :=
  KSubsetCollection.sameFrame_extensions_card_le_two_of_erased_left_endpoint_of_fibre hn hC hS₀
    himg hleft (KSubsetCollection.sameFrameExtensions_left_refill_fibre_card_le_one hn hC hS₀ himg hleft)
    (KSubsetCollection.sameFrameExtensions_left_exterior_fibre_card_le_one hn hC hS₀ himg hleft)

/-- Right-endpoint deletion: `≤ 2` completions (unconditional). -/
theorem KSubsetCollection.sameFrame_extensions_card_le_two_of_erased_right_endpoint {n k : ℕ}
    (hn : 2 ≤ n) {C : Finset (KSubset n k)} (hC : KSubsetCollection.IsMaximalSorted C)
    {S₀ : KSubset n k} (hS₀ : S₀ ∈ C) {b : ℕ}
    (himg : C.image KSubset.prefixWeight = Finset.Ico b (b + n))
    (hright : KSubset.prefixWeight S₀ = b + n - 1) :
    (KSubsetCollection.sameFrameExtensions (C.erase S₀)).card ≤ 2 :=
  KSubsetCollection.sameFrame_extensions_card_le_two_of_erased_right_endpoint_of_fibre hn hC hS₀
    himg hright
    (KSubsetCollection.sameFrameExtensions_right_exterior_fibre_card_le_one hn hC hS₀ himg hright)
    (KSubsetCollection.sameFrameExtensions_right_refill_fibre_card_le_one hn hC hS₀ himg hright)

/-- THE FIXED-SLICE THEOREM: erasing any vertex of a maximal sorted collection leaves at most
two same-frame completions.  Trichotomy on the erased weight (left / right / interior);
`n ≤ 1` is degenerate (the whole `KSubset` type has `≤ 2^n ≤ 2` elements). -/
theorem KSubsetCollection.sameFrame_extensions_card_le_two_of_erase_maximalSorted {n k : ℕ}
    {C : Finset (KSubset n k)} (hC : KSubsetCollection.IsMaximalSorted C)
    {S₀ : KSubset n k} (hS₀ : S₀ ∈ C) :
    (KSubsetCollection.sameFrameExtensions (C.erase S₀)).card ≤ 2 := by
  classical
  by_cases hn : 2 ≤ n
  · obtain ⟨b, himg⟩ := KSubsetCollection.exists_base_weight_image_eq_Ico_of_isMaximalSorted hC
    rcases KSubsetCollection.prefixWeight_trichotomy_of_mem hS₀ himg with hl | hr | hint
    · exact KSubsetCollection.sameFrame_extensions_card_le_two_of_erased_left_endpoint hn hC hS₀ himg hl
    · exact KSubsetCollection.sameFrame_extensions_card_le_two_of_erased_right_endpoint hn hC hS₀ himg hr
    · exact KSubsetCollection.sameFrame_extensions_card_le_two_of_erased_interior hC hS₀ himg hint
  · -- n ≤ 1: the whole type has ≤ 2^n ≤ 2 elements
    have hcard : Fintype.card (KSubset n k) ≤ 2 := by
      have hle : Fintype.card (KSubset n k) ≤ Fintype.card (Finset (Fin n)) :=
        Fintype.card_subtype_le _
      rw [Fintype.card_finset, Fintype.card_fin] at hle
      have : (2 : ℕ) ^ n ≤ 2 := by interval_cases n <;> norm_num
      omega
    calc (KSubsetCollection.sameFrameExtensions (C.erase S₀)).card
        ≤ (Finset.univ : Finset (KSubset n k)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card (KSubset n k) := Finset.card_univ
      _ ≤ 2 := hcard

/-! ### Separation theorem (the pure gap-fill residual): reusable e-function lemmas +
INTERIOR omitting-extension uniqueness.  Two same-frame extensions both omitting a
wall-common coordinate `j₀` are EQUAL — proved here for the INTERIOR weight case (the bulk).
The ENDPOINT (dip/rise) case is the documented residual (see the comment after the lemmas). -/

/-! ### predecessor-safe prefix-count jump (`KSubset.prefixCount_pred` is above, relocated
to the interior-existence section so it is in scope there). -/

/-- When every wall subset contains `j₀`, the wall minimum prefix count jumps by one at `j₀`. -/
theorem KSubsetCollection.minPrefixCount_jump_of_commonPresent {n k : ℕ}
    {W : Finset (KSubset n k)} (hWne : W.Nonempty) {j₀ jp : Fin n}
    (hjp : jp.val + 1 = j₀.val) (hW : ∀ S ∈ W, j₀ ∈ S.1) :
    KSubsetCollection.minPrefixCount W hWne j₀
      = KSubsetCollection.minPrefixCount W hWne jp + 1 := by
  classical
  have key : ∀ S ∈ W, KSubset.prefixCount S j₀ = KSubset.prefixCount S jp + 1 := by
    intro S hS
    rw [S.prefixCount_pred hjp, if_pos (hW S hS)]
  apply le_antisymm
  · obtain ⟨S, hS, hSeq⟩ :=
      Finset.mem_image.mp (Finset.min'_mem _ (hWne.image (fun S => KSubset.prefixCount S jp)))
    have hSeq' : KSubset.prefixCount S jp = KSubsetCollection.minPrefixCount W hWne jp := hSeq
    calc KSubsetCollection.minPrefixCount W hWne j₀ ≤ KSubset.prefixCount S j₀ :=
          KSubsetCollection.minPrefixCount_le hWne hS j₀
      _ = KSubset.prefixCount S jp + 1 := key S hS
      _ = KSubsetCollection.minPrefixCount W hWne jp + 1 := by rw [hSeq']
  · obtain ⟨S, hS, hSeq⟩ :=
      Finset.mem_image.mp (Finset.min'_mem _ (hWne.image (fun S => KSubset.prefixCount S j₀)))
    have hSeq' : KSubset.prefixCount S j₀ = KSubsetCollection.minPrefixCount W hWne j₀ := hSeq
    have hle : KSubsetCollection.minPrefixCount W hWne jp ≤ KSubset.prefixCount S jp :=
      KSubsetCollection.minPrefixCount_le hWne hS jp
    have hk := key S hS
    rw [← hSeq']; omega

/-! ### e-function (profile deviation) -/

/-- Deviation of an extension's prefix count from the wall minimum. -/
noncomputable def KSubsetCollection.eProfile {n k : ℕ}
    (W : Finset (KSubset n k)) (hWne : W.Nonempty) (T : KSubset n k) (t : Fin n) : ℤ :=
  (KSubset.prefixCount T t : ℤ) - (KSubsetCollection.minPrefixCount W hWne t : ℤ)

/-- An extension omitting `j₀` drops its e-profile by one at `j₀`. -/
theorem KSubsetCollection.eProfile_omit_commonPresent_drop {n k : ℕ}
    {W : Finset (KSubset n k)} (hWne : W.Nonempty) {j₀ jp : Fin n} (hjp : jp.val + 1 = j₀.val)
    {T : KSubset n k} (hW : ∀ S ∈ W, j₀ ∈ S.1) (hTj : j₀ ∉ T.1) :
    KSubsetCollection.eProfile W hWne T j₀ - KSubsetCollection.eProfile W hWne T jp = -1 := by
  have hT := T.prefixCount_pred hjp
  rw [if_neg hTj, Nat.add_zero] at hT
  have hmin := KSubsetCollection.minPrefixCount_jump_of_commonPresent hWne hjp hW
  rw [KSubsetCollection.eProfile, KSubsetCollection.eProfile, hT, hmin]
  push_cast
  ring

/-! ### interior omitting-extension uniqueness -/

/-- INTERIOR case of the separation: when `W`'s weight image is a punctured interval
`(Ico b (b+n)).erase w₀` with `w₀` interior, two same-frame extensions both omitting a
wall-common coordinate `j₀` are EQUAL. -/
theorem KSubsetCollection.sameFrameExtensions_eq_of_both_omit_commonPresent_interior {n k : ℕ}
    {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W) (hWne : W.Nonempty)
    {b w₀ : ℕ} (himgW : W.image KSubset.prefixWeight = (Finset.Ico b (b + n)).erase w₀)
    (hint : b < w₀ ∧ w₀ < b + n - 1) {j₀ : Fin n} (hW : ∀ S ∈ W, j₀ ∈ S.1)
    {T U : KSubset n k} (hT : T ∈ KSubsetCollection.sameFrameExtensions W)
    (hU : U ∈ KSubsetCollection.sameFrameExtensions W)
    (hTj : j₀ ∉ T.1) (hUj : j₀ ∉ U.1) :
    T = U := by
  classical
  have hn3 : 3 ≤ n := by omega
  -- neighbours of the hole
  have hlomem : w₀ - 1 ∈ W.image KSubset.prefixWeight := by
    rw [himgW]; exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩
  have himem : w₀ + 1 ∈ W.image KSubset.prefixWeight := by
    rw [himgW]; exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩
  obtain ⟨Slo, hSloW, hSlow⟩ := Finset.mem_image.mp hlomem
  obtain ⟨Shi, hShiW, hShiw⟩ := Finset.mem_image.mp himem
  set L := KSubsetCollection.aboveMinProfile W hWne Slo with hL
  set Uu := KSubsetCollection.aboveMinProfile W hWne Shi with hUu
  set base := ∑ t : Fin n, KSubsetCollection.minPrefixCount W hWne t with hbase
  have hLcard : L.card = w₀ - 1 - base := by
    have h := KSubsetCollection.prefixWeight_eq_base_add_aboveMinProfile_card hWsorted hWne hSloW
    rw [hSlow, ← hbase, ← hL] at h; omega
  have hUcard : Uu.card = w₀ + 1 - base := by
    have h := KSubsetCollection.prefixWeight_eq_base_add_aboveMinProfile_card hWsorted hWne hShiW
    rw [hShiw, ← hbase, ← hUu] at h; omega
  have hbase_le : base ≤ w₀ - 1 := by
    have h := KSubsetCollection.prefixWeight_eq_base_add_aboveMinProfile_card hWsorted hWne hSloW
    rw [hSlow, ← hbase] at h; omega
  have hSlohi_pair : KSubset.IsSortedPair Shi Slo := hWsorted Shi hShiW Slo hSloW (by
    intro h; rw [h] at hShiw; omega)
  have hpc_lohi : ∀ t, KSubset.prefixCount Slo t ≤ KSubset.prefixCount Shi t := by
    rcases hSlohi_pair with hb | hb
    · exact fun t => (hb t).1
    · exact fun t => absurd (hb.prefixWeight_lt (by rintro rfl; omega))
        (by rw [hShiw, hSlow]; omega)
  have hLU : L ⊆ Uu := by
    intro t ht
    rw [hL, KSubsetCollection.mem_aboveMinProfile_iff] at ht
    rw [hUu, KSubsetCollection.mem_aboveMinProfile_iff]
    exact lt_of_lt_of_le ht (hpc_lohi t)
  -- bracketing + band for any extension
  have hclaim : ∀ V ∈ KSubsetCollection.sameFrameExtensions W,
      (∀ t, KSubset.prefixCount Slo t ≤ KSubset.prefixCount V t) ∧
      (∀ t, KSubset.prefixCount V t ≤ KSubset.prefixCount Shi t) ∧
      (∀ t, KSubsetCollection.minPrefixCount W hWne t ≤ KSubset.prefixCount V t ∧
        KSubset.prefixCount V t ≤ KSubsetCollection.minPrefixCount W hWne t + 1) := by
    intro V hV
    have hVmem := hV
    rw [KSubsetCollection.mem_sameFrameExtensions_iff] at hV
    obtain ⟨c, hc⟩ := KSubsetCollection.exists_base_weight_image_eq_Ico_of_isMaximalSorted hV.2
    rw [Finset.image_insert, himgW] at hc
    have hwV : KSubset.prefixWeight V = w₀ :=
      interval_insert_erase_interior (by omega) hint.1 hint.2 hc
    have hpairlo := KSubsetCollection.extension_sortedWith_wall hVmem hSloW
    have hpairhi := KSubsetCollection.extension_sortedWith_wall hVmem hShiW
    have hVlo : ∀ t, KSubset.prefixCount Slo t ≤ KSubset.prefixCount V t := by
      rcases hpairlo with hb | hb
      · exact fun t => (hb t).1
      · exact fun t => absurd (hb.prefixWeight_lt (by rintro rfl; omega))
          (by rw [hwV, hSlow]; omega)
    have hVhi : ∀ t, KSubset.prefixCount V t ≤ KSubset.prefixCount Shi t := by
      rcases hpairhi with hb | hb
      · exact fun t => absurd (hb.prefixWeight_lt (by rintro rfl; omega))
          (by rw [hwV, hShiw]; omega)
      · exact fun t => (hb t).1
    refine ⟨hVlo, hVhi, fun t => ⟨le_trans (KSubsetCollection.minPrefixCount_le hWne hSloW t) (hVlo t), ?_⟩⟩
    have hShib := KSubsetCollection.prefixCount_eq_min_or_min_add_one hWsorted hWne hShiW t
    have := hVhi t
    omega
  have hmaps : ∀ V ∈ KSubsetCollection.sameFrameExtensions W,
      KSubsetCollection.aboveMinProfile W hWne V ∈
        Uu.powerset.filter (fun X => L ⊆ X ∧ X.card = L.card + 1) := by
    intro V hV
    obtain ⟨hVlo, hVhi, hband⟩ := hclaim V hV
    have hVwt := KSubsetCollection.prefixWeight_eq_base_add_aboveMinProfile_card_of_band hWne hband
    have hwV : KSubset.prefixWeight V = w₀ := by
      rw [KSubsetCollection.mem_sameFrameExtensions_iff] at hV
      obtain ⟨c, hc⟩ := KSubsetCollection.exists_base_weight_image_eq_Ico_of_isMaximalSorted hV.2
      rw [Finset.image_insert, himgW] at hc
      exact interval_insert_erase_interior (by omega) hint.1 hint.2 hc
    rw [hwV] at hVwt
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      rw [KSubsetCollection.mem_aboveMinProfile_iff] at ht
      rw [hUu, KSubsetCollection.mem_aboveMinProfile_iff]
      exact lt_of_lt_of_le ht (hVhi t)
    · intro t ht
      rw [hL, KSubsetCollection.mem_aboveMinProfile_iff] at ht
      rw [KSubsetCollection.mem_aboveMinProfile_iff]
      exact lt_of_lt_of_le ht (hVlo t)
    · rw [hLcard]; omega
  -- 0 < j₀.val for an omitting extension (else band contradicts at j₀=0)
  have hmin1 : 1 ≤ KSubsetCollection.minPrefixCount W hWne j₀ := by
    obtain ⟨S, hSW, hSeq⟩ :=
      Finset.mem_image.mp (Finset.min'_mem _ (hWne.image (fun S => KSubset.prefixCount S j₀)))
    have heq : KSubsetCollection.minPrefixCount W hWne j₀ = KSubset.prefixCount S j₀ := hSeq.symm
    rw [heq, KSubset.prefixCount]
    exact Finset.card_pos.mpr ⟨j₀, Finset.mem_filter.mpr ⟨hW S hSW, le_refl _⟩⟩
  have hpos : 0 < j₀.val := by
    by_contra h
    have hj0 : j₀.val = 0 := by omega
    obtain ⟨_, _, hband⟩ := hclaim T hT
    have hb := (hband j₀).1
    have hpcT : KSubset.prefixCount T j₀ = 0 := by
      rw [KSubset.prefixCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hxV
      rw [Fin.le_def]
      intro hle
      exact hTj ((Fin.ext (by omega) : x = j₀) ▸ hxV)
    omega
  obtain ⟨jp, hjpval⟩ : ∃ jp : Fin n, jp.val + 1 = j₀.val :=
    ⟨⟨j₀.val - 1, by have := j₀.isLt; omega⟩, by show (j₀.val - 1) + 1 = j₀.val; omega⟩
  -- [j₀ ∈ L] ↔ [jp ∈ L] (via Slo ∈ W ∋ j₀ jump)
  have hSlojump : KSubset.prefixCount Slo j₀ = KSubset.prefixCount Slo jp + 1 := by
    rw [Slo.prefixCount_pred hjpval, if_pos (hW Slo hSloW)]
  have hminjump := KSubsetCollection.minPrefixCount_jump_of_commonPresent hWne hjpval hW
  have hLjump : j₀ ∈ L ↔ jp ∈ L := by
    rw [hL, KSubsetCollection.mem_aboveMinProfile_iff, KSubsetCollection.mem_aboveMinProfile_iff]
    rw [hSlojump, hminjump]; omega
  -- for an omitting extension, its profile is `insert jp L`
  have hprof : ∀ V ∈ KSubsetCollection.sameFrameExtensions W, j₀ ∉ V.1 →
      KSubsetCollection.aboveMinProfile W hWne V = insert jp L := by
    intro V hV hVj
    have hmem := hmaps V hV
    rw [Finset.mem_filter, Finset.mem_powerset] at hmem
    obtain ⟨hsubU, hLsub, hcard⟩ := hmem
    obtain ⟨_, _, hband⟩ := hclaim V hV
    have hdrop := KSubsetCollection.eProfile_omit_commonPresent_drop hWne hjpval hW hVj
    have bj := hband j₀; have bp := hband jp
    have hj0notin : j₀ ∉ KSubsetCollection.aboveMinProfile W hWne V := by
      rw [KSubsetCollection.mem_aboveMinProfile_iff]
      simp only [KSubsetCollection.eProfile] at hdrop; push_cast at hdrop; omega
    have hjpin : jp ∈ KSubsetCollection.aboveMinProfile W hWne V := by
      rw [KSubsetCollection.mem_aboveMinProfile_iff]
      simp only [KSubsetCollection.eProfile] at hdrop; push_cast at hdrop; omega
    have hj0notL : j₀ ∉ L := fun h => hj0notin (hLsub h)
    have hjpnotL : jp ∉ L := fun h => hj0notL (hLjump.mpr h)
    have hsub2 : insert jp L ⊆ KSubsetCollection.aboveMinProfile W hWne V := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hjpin
      · exact hLsub hx
    have hcard2 : (insert jp L).card = (KSubsetCollection.aboveMinProfile W hWne V).card := by
      rw [Finset.card_insert_of_notMem hjpnotL, hcard]
    exact (Finset.eq_of_subset_of_card_le hsub2 (le_of_eq hcard2.symm)).symm
  have hpT := hprof T hT hTj
  have hpU := hprof U hU hUj
  apply KSubset.prefixCount_injective
  intro t
  obtain ⟨_, _, hbandT⟩ := hclaim T hT
  obtain ⟨_, _, hbandU⟩ := hclaim U hU
  have hbT := hbandT t
  have hbU := hbandU t
  have hpe : (KSubsetCollection.minPrefixCount W hWne t < KSubset.prefixCount T t) ↔
      (KSubsetCollection.minPrefixCount W hWne t < KSubset.prefixCount U t) := by
    rw [← KSubsetCollection.mem_aboveMinProfile_iff, ← KSubsetCollection.mem_aboveMinProfile_iff,
      hpT, hpU]
  omega

/-! ### Endpoint case — the mixed dip/rise contradiction

When `W.image prefixWeight` is consecutive (`W = C.erase S₀`, `S₀` a weight-endpoint of the maximal
`C`), an omitting extension is weight-extreme: a dip (weight `b`) or a rise (weight `b+n`).  Two dips
or two rises are handled by `dip_completions_eq` / `rise_completions_eq`; the theorem below rules out
a dip and a rise both omitting `j₀`.  Writing `pcⱼ := minPrefixCount W`, the dip pins `pc_T = pcⱼ`
off `j₀` (`base = b+1`) and the rise pins `pc_U = pcⱼ+1` off `j₀`, so `pc_U = pc_T+1` everywhere; at
the top coordinate both equal `k`, giving `k = k+1`. -/

/-- MIXED ENDPOINT case: when `W` has consecutive weight image `Ico (b+1) (b+n)`, a DIP
extension (weight `b`) and a RISE extension (weight `b+n`) cannot BOTH omit a wall-common
coordinate `j₀`. -/
theorem KSubsetCollection.not_both_omit_commonPresent_dip_rise {n k : ℕ} (hn : 2 ≤ n)
    {W : Finset (KSubset n k)} (hWsorted : KSubsetCollection.IsSorted W) (hWne : W.Nonempty)
    {b : ℕ} (himgW : W.image KSubset.prefixWeight = Finset.Ico (b + 1) (b + n))
    {j₀ : Fin n} (hW : ∀ S ∈ W, j₀ ∈ S.1)
    {T U : KSubset n k} (hT : T ∈ KSubsetCollection.sameFrameExtensions W)
    (hU : U ∈ KSubsetCollection.sameFrameExtensions W)
    (hwT : KSubset.prefixWeight T = b) (hwU : KSubset.prefixWeight U = b + n)
    (hTj : j₀ ∉ T.1) (hUj : j₀ ∉ U.1) : False := by
  classical
  set base := ∑ t : Fin n, KSubsetCollection.minPrefixCount W hWne t with hbase
  have hwge : ∀ w ∈ W, b + 1 ≤ KSubset.prefixWeight w ∧ KSubset.prefixWeight w ≤ b + n - 1 := by
    intro w hw
    have hmem : KSubset.prefixWeight w ∈ Finset.Ico (b + 1) (b + n) := by
      rw [← himgW]; exact Finset.mem_image_of_mem _ hw
    rw [Finset.mem_Ico] at hmem; omega
  obtain ⟨top, htop⟩ : ∃ top : Fin n, ∀ j : Fin n, j ≤ top :=
    ⟨⟨n - 1, by omega⟩, fun j => by rw [Fin.le_def]; show j.val ≤ n - 1; have := j.isLt; omega⟩
  have hmin_wit : ∀ t, ∃ w ∈ W, KSubsetCollection.minPrefixCount W hWne t = KSubset.prefixCount w t := by
    intro t
    obtain ⟨w, hw, hweq⟩ :=
      Finset.mem_image.mp (Finset.min'_mem _ (hWne.image (fun S => KSubset.prefixCount S t)))
    exact ⟨w, hw, hweq.symm⟩
  -- DIP bounds
  have hTle : ∀ t, KSubset.prefixCount T t ≤ KSubsetCollection.minPrefixCount W hWne t := by
    intro t
    apply Finset.le_min'
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    exact ((KSubsetCollection.sortedBefore_wall_of_weight_gt hT hw
      (by rw [hwT]; exact (hwge w hw).1)) t).1
  have hTge : ∀ t, KSubsetCollection.minPrefixCount W hWne t ≤ KSubset.prefixCount T t + 1 := by
    intro t
    obtain ⟨w, hw, hweq⟩ := hmin_wit t
    rw [hweq]
    exact ((KSubsetCollection.sortedBefore_wall_of_weight_gt hT hw
      (by rw [hwT]; exact (hwge w hw).1)) t).2
  -- RISE bounds
  have hUge : ∀ t, KSubsetCollection.minPrefixCount W hWne t ≤ KSubset.prefixCount U t := by
    intro t
    obtain ⟨w, hw, hweq⟩ := hmin_wit t
    rw [hweq]
    exact ((KSubsetCollection.sortedBefore_wall_of_weight_lt hU hw
      (by rw [hwU]; have := (hwge w hw).2; omega)) t).1
  have hUle : ∀ t, KSubset.prefixCount U t ≤ KSubsetCollection.minPrefixCount W hWne t + 1 := by
    intro t
    obtain ⟨w, hw, hweq⟩ := hmin_wit t
    rw [hweq]
    exact ((KSubsetCollection.sortedBefore_wall_of_weight_lt hU hw
      (by rw [hwU]; have := (hwge w hw).2; omega)) t).2
  -- base ≤ b+1
  have hbase_le : base ≤ b + 1 := by
    have hb1mem : b + 1 ∈ W.image KSubset.prefixWeight := by
      rw [himgW]; exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    obtain ⟨S₀, hS₀W, hS₀w⟩ := Finset.mem_image.mp hb1mem
    have h := KSubsetCollection.prefixWeight_eq_base_add_aboveMinProfile_card hWsorted hWne hS₀W
    rw [hS₀w, ← hbase] at h; omega
  -- j₀ = 0 ⟹ rise contradiction
  by_cases hj0 : j₀.val = 0
  · have hpcU0 : KSubset.prefixCount U j₀ = 0 := by
      rw [KSubset.prefixCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hxU
      rw [Fin.le_def]; intro hle
      exact hUj ((Fin.ext (by omega) : x = j₀) ▸ hxU)
    have hmin0 : 1 ≤ KSubsetCollection.minPrefixCount W hWne j₀ := by
      obtain ⟨w, hw, hweq⟩ := hmin_wit j₀
      rw [hweq, KSubset.prefixCount]
      exact Finset.card_pos.mpr ⟨j₀, Finset.mem_filter.mpr ⟨hW w hw, le_refl _⟩⟩
    have := hUge j₀; omega
  -- j₀ > 0
  obtain ⟨jp, hjpval⟩ : ∃ jp : Fin n, jp.val + 1 = j₀.val :=
    ⟨⟨j₀.val - 1, by have := j₀.isLt; omega⟩, by show (j₀.val - 1) + 1 = j₀.val; omega⟩
  have hdropT := KSubsetCollection.eProfile_omit_commonPresent_drop hWne hjpval hW hTj
  have hdropU := KSubsetCollection.eProfile_omit_commonPresent_drop hWne hjpval hW hUj
  -- dip omit shape at j₀
  have heT : KSubset.prefixCount T j₀ + 1 = KSubsetCollection.minPrefixCount W hWne j₀ := by
    have a1 := hTle j₀; have a2 := hTge j₀; have a3 := hTle jp; have a4 := hTge jp
    simp only [KSubsetCollection.eProfile] at hdropT; omega
  -- rise omit shape at j₀
  have heU : KSubset.prefixCount U j₀ = KSubsetCollection.minPrefixCount W hWne j₀ := by
    have a1 := hUge j₀; have a2 := hUle j₀; have a3 := hUge jp; have a4 := hUle jp
    simp only [KSubsetCollection.eProfile] at hdropU; omega
  -- DIP sum: base = b + ∑(min - pc_T)
  have hsumT : base = b + ∑ t : Fin n,
      (KSubsetCollection.minPrefixCount W hWne t - KSubset.prefixCount T t) := by
    rw [hbase]
    have hcong : ∑ t : Fin n, KSubsetCollection.minPrefixCount W hWne t
        = ∑ t : Fin n, (KSubset.prefixCount T t +
          (KSubsetCollection.minPrefixCount W hWne t - KSubset.prefixCount T t)) := by
      apply Finset.sum_congr rfl; intro t _; have := hTle t; omega
    have hpcsum : (∑ t : Fin n, KSubset.prefixCount T t) = b := by rw [← hwT, KSubset.prefixWeight]
    rw [hcong, Finset.sum_add_distrib, hpcsum]
  have hsumT1 : (∑ t : Fin n,
      (KSubsetCollection.minPrefixCount W hWne t - KSubset.prefixCount T t)) = 1 := by
    have hj : (KSubsetCollection.minPrefixCount W hWne j₀ - KSubset.prefixCount T j₀) = 1 := by
      have := heT; omega
    have hge : 1 ≤ ∑ t : Fin n,
        (KSubsetCollection.minPrefixCount W hWne t - KSubset.prefixCount T t) := by
      calc 1 = (KSubsetCollection.minPrefixCount W hWne j₀ - KSubset.prefixCount T j₀) := hj.symm
        _ ≤ _ := Finset.single_le_sum
          (f := fun t => KSubsetCollection.minPrefixCount W hWne t - KSubset.prefixCount T t)
          (fun i _ => Nat.zero_le _) (Finset.mem_univ j₀)
    omega
  have hbase_eq : base = b + 1 := by rw [hsumT, hsumT1]
  have hdToff : ∀ t, t ≠ j₀ →
      KSubsetCollection.minPrefixCount W hWne t = KSubset.prefixCount T t := by
    have hzero : ∑ t ∈ Finset.univ.erase j₀,
        (KSubsetCollection.minPrefixCount W hWne t - KSubset.prefixCount T t) = 0 := by
      have hsplit : (KSubsetCollection.minPrefixCount W hWne j₀ - KSubset.prefixCount T j₀)
          + ∑ t ∈ Finset.univ.erase j₀,
            (KSubsetCollection.minPrefixCount W hWne t - KSubset.prefixCount T t)
          = ∑ t : Fin n, (KSubsetCollection.minPrefixCount W hWne t - KSubset.prefixCount T t) :=
        Finset.add_sum_erase Finset.univ
          (fun t => KSubsetCollection.minPrefixCount W hWne t - KSubset.prefixCount T t)
          (Finset.mem_univ j₀)
      rw [hsumT1] at hsplit
      have hj : (KSubsetCollection.minPrefixCount W hWne j₀ - KSubset.prefixCount T j₀) = 1 := by
        have := heT; omega
      omega
    intro t ht
    have := (Finset.sum_eq_zero_iff.mp hzero) t (Finset.mem_erase.mpr ⟨ht, Finset.mem_univ t⟩)
    have := hTle t; omega
  -- RISE sum: b + n = base + ∑(pc_U - min)
  have hsumU : b + n = base + ∑ t : Fin n,
      (KSubset.prefixCount U t - KSubsetCollection.minPrefixCount W hWne t) := by
    rw [← hwU, KSubset.prefixWeight, hbase]
    have hcong : ∑ t : Fin n, KSubset.prefixCount U t
        = ∑ t : Fin n, (KSubsetCollection.minPrefixCount W hWne t +
          (KSubset.prefixCount U t - KSubsetCollection.minPrefixCount W hWne t)) := by
      apply Finset.sum_congr rfl; intro t _; have := hUge t; omega
    rw [hcong, Finset.sum_add_distrib]
  have hsumU1 : (∑ t : Fin n,
      (KSubset.prefixCount U t - KSubsetCollection.minPrefixCount W hWne t)) = n - 1 := by
    have := hsumU; have := hbase_eq; omega
  have heUoff : ∀ t, t ≠ j₀ →
      KSubset.prefixCount U t = KSubsetCollection.minPrefixCount W hWne t + 1 := by
    have hdecomp : (∑ _t : Fin n, (1 : ℕ))
        = (∑ t : Fin n, (KSubset.prefixCount U t - KSubsetCollection.minPrefixCount W hWne t))
          + ∑ t : Fin n,
            (1 - (KSubset.prefixCount U t - KSubsetCollection.minPrefixCount W hWne t)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro t _; have := hUle t; omega
    have hone : (∑ _t : Fin n, (1 : ℕ)) = n := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    have hsumfU : (∑ t : Fin n,
        (1 - (KSubset.prefixCount U t - KSubsetCollection.minPrefixCount W hWne t))) = 1 := by
      rw [hone, hsumU1] at hdecomp; omega
    have hzero : ∑ t ∈ Finset.univ.erase j₀,
        (1 - (KSubset.prefixCount U t - KSubsetCollection.minPrefixCount W hWne t)) = 0 := by
      have hsplit : (1 - (KSubset.prefixCount U j₀ - KSubsetCollection.minPrefixCount W hWne j₀))
          + ∑ t ∈ Finset.univ.erase j₀,
            (1 - (KSubset.prefixCount U t - KSubsetCollection.minPrefixCount W hWne t))
          = ∑ t : Fin n, (1 - (KSubset.prefixCount U t - KSubsetCollection.minPrefixCount W hWne t)) :=
        Finset.add_sum_erase Finset.univ
          (fun t => 1 - (KSubset.prefixCount U t - KSubsetCollection.minPrefixCount W hWne t))
          (Finset.mem_univ j₀)
      rw [hsumfU] at hsplit
      have hj : (1 - (KSubset.prefixCount U j₀ - KSubsetCollection.minPrefixCount W hWne j₀)) = 1 := by
        have := heU; omega
      omega
    intro t ht
    have := (Finset.sum_eq_zero_iff.mp hzero) t (Finset.mem_erase.mpr ⟨ht, Finset.mem_univ t⟩)
    have := hUge t; have := hUle t; omega
  -- pc_U = pc_T + 1 everywhere ⟹ contradiction at top
  have hkey : ∀ t, KSubset.prefixCount U t = KSubset.prefixCount T t + 1 := by
    intro t
    by_cases ht : t = j₀
    · subst ht; have := heU; have := heT; omega
    · have := heUoff t ht; have := hdToff t ht; omega
  have hUtop := prefixCount_top_eq U htop
  have hTtop := prefixCount_top_eq T htop
  have := hkey top; omega

/-! ### The full SEPARATION theorem (interior + endpoint dispatch)

Two same-frame extensions of a wall `W` (every member `∋ j₀`) that BOTH omit `j₀` are equal.
Dispatch on the weight of `T` inside its own completion `insert T W` (spectrum `Ico b (b+n)`):
• INTERIOR (`b < w_T < b+n-1`) — `W.image` is the punctured interval; the interior lemma applies.
• LEFT endpoint (`w_T = b`) — `W.image = Ico (b+1) (b+n)`; `U` is a dip (weight `b`) ⟹ same
  fibre as `T` (`…left_refill_fibre…`), or a rise (weight `b+n`) ⟹ the mixed contradiction.
• RIGHT endpoint (`w_T = b+n-1`) — `W.image = Ico b (b+n-1)`; `U` is a rise ⟹ same fibre
  (`…right_refill_fibre…`), or a dip (weight `b-1`) ⟹ the mixed contradiction (with `b ≥ 1`,
  forced since `b-1 ∉ W.image`). -/

/-- SEPARATION THEOREM (unconditional, `2 ≤ n`): two same-frame extensions of a wall `W`
whose every member contains `j₀`, both omitting `j₀`, are EQUAL. -/
theorem KSubsetCollection.sameFrameExtensions_eq_of_both_omit_commonPresent {n k : ℕ}
    (hn : 2 ≤ n) {W : Finset (KSubset n k)} {j₀ : Fin n} (hW : ∀ S ∈ W, j₀ ∈ S.1)
    {T U : KSubset n k} (hT : T ∈ KSubsetCollection.sameFrameExtensions W)
    (hU : U ∈ KSubsetCollection.sameFrameExtensions W)
    (hTj : j₀ ∉ T.1) (hUj : j₀ ∉ U.1) : T = U := by
  classical
  -- structural facts about the wall `W` from `T`'s membership
  have hTpair := (KSubsetCollection.mem_sameFrameExtensions_iff W T).mp hT
  have hTnotin : T ∉ W := hTpair.1
  have hC : KSubsetCollection.IsMaximalSorted (insert T W) := hTpair.2
  have hWsorted : KSubsetCollection.IsSorted W := fun I hI J hJ hIJ =>
    hC.2 I (Finset.mem_insert_of_mem hI) J (Finset.mem_insert_of_mem hJ) hIJ
  have hWcard : W.card = n - 1 := by
    have h := hC.1; rw [Finset.card_insert_of_notMem hTnotin] at h; omega
  have hWne : W.Nonempty := by rw [← Finset.card_pos, hWcard]; omega
  have hST : T ∈ insert T W := Finset.mem_insert_self T W
  have hCeraseT : (insert T W).erase T = W := Finset.erase_insert hTnotin
  obtain ⟨b, himgC⟩ := KSubsetCollection.exists_base_weight_image_eq_Ico_of_isMaximalSorted hC
  have himgW : W.image KSubset.prefixWeight
      = (Finset.Ico b (b + n)).erase (KSubset.prefixWeight T) := by
    rw [← hCeraseT, KSubsetCollection.prefixWeight_image_erase_eq_delete hC.2 hST, himgC]
  have hUC : U ∈ KSubsetCollection.sameFrameExtensions ((insert T W).erase T) := by
    rw [hCeraseT]; exact hU
  rcases KSubsetCollection.prefixWeight_trichotomy_of_mem hST himgC with hl | hr | hint
  · -- LEFT endpoint: w_T = b
    rcases KSubsetCollection.sameFrame_extension_weight_left_endpoint hn hC hST himgC hl hUC
      with hwU | hwU
    · -- U is a dip (weight b): same fibre as T
      have hfib := KSubsetCollection.sameFrameExtensions_left_refill_fibre_card_le_one hn hC hST
        himgC hl
      rw [hCeraseT] at hfib
      exact Finset.card_le_one.mp hfib T (Finset.mem_filter.mpr ⟨hT, hl⟩) U
        (Finset.mem_filter.mpr ⟨hU, hwU⟩)
    · -- U is a rise (weight b+n): T dip, U rise — mixed contradiction
      have himgW' : W.image KSubset.prefixWeight = Finset.Ico (b + 1) (b + n) := by
        rw [himgW, hl]; ext y; rw [Finset.mem_erase, Finset.mem_Ico, Finset.mem_Ico]; omega
      exact (KSubsetCollection.not_both_omit_commonPresent_dip_rise hn hWsorted hWne himgW' hW
        hT hU hl hwU hTj hUj).elim
  · -- RIGHT endpoint: w_T = b+n-1
    have himgWr : W.image KSubset.prefixWeight = Finset.Ico b (b + n - 1) := by
      rw [himgW, hr]; ext y; rw [Finset.mem_erase, Finset.mem_Ico, Finset.mem_Ico]; omega
    rcases KSubsetCollection.sameFrame_extension_weight_right_endpoint hn hC hST himgC hr hUC
      with hwU | hwU
    · -- U is a dip (weight b-1): T rise, U dip — mixed contradiction (needs b ≥ 1)
      have hwUnotin : KSubset.prefixWeight U ∉ W.image KSubset.prefixWeight := by
        rw [Finset.mem_image]; rintro ⟨S, hS, hSeq⟩
        exact KSubsetCollection.weight_ne_wall hU hS hSeq.symm
      have hb1 : 1 ≤ b := by
        by_contra hb0
        apply hwUnotin
        rw [hwU, himgWr, Finset.mem_Ico]; omega
      have himgW'' : W.image KSubset.prefixWeight
          = Finset.Ico ((b - 1) + 1) ((b - 1) + n) := by
        rw [himgWr]; congr 1 <;> omega
      have hwT' : KSubset.prefixWeight T = (b - 1) + n := by omega
      exact (KSubsetCollection.not_both_omit_commonPresent_dip_rise hn hWsorted hWne himgW'' hW
        hU hT hwU hwT' hUj hTj).elim
    · -- U is a rise (weight b+n-1): same fibre as T
      have hfib := KSubsetCollection.sameFrameExtensions_right_refill_fibre_card_le_one hn hC hST
        himgC hr
      rw [hCeraseT] at hfib
      exact Finset.card_le_one.mp hfib T (Finset.mem_filter.mpr ⟨hT, hr⟩) U
        (Finset.mem_filter.mpr ⟨hU, hwU⟩)
  · -- INTERIOR: b < w_T < b+n-1
    exact KSubsetCollection.sameFrameExtensions_eq_of_both_omit_commonPresent_interior hWsorted
      hWne himgW hint hW hT hU hTj hUj

/-! ### The gap-fill extensions (the LOWER-completion combinatorics)

`sameFrameExtensions` (above, `≤ 2`) is the SAME-min-frame side of the flip.  The LOWER
side, after reducing to the lowered coordinate frame, injects into the `j₀`-EXCLUDING
same-frame extensions of a wall `W` whose every member contains the (unique constant)
coordinate `j₀`.  The defining computable form (direct filter, so `decide` reduces — the
`sameFrameExtensions` def is `noncomputable`) and its bridge to `sameFrameExtensions`: -/

/-- The `j₀`-excluding same-frame extensions of a wall `W` (computable form). -/
def KSubsetCollection.lowerGapFillExtensions {n k : ℕ}
    (W : Finset (KSubset n k)) (j₀ : Fin n) : Finset (KSubset n k) :=
  Finset.univ.filter fun T =>
    T ∉ W ∧ j₀ ∉ T.1 ∧ KSubsetCollection.IsMaximalSorted (insert T W)

theorem KSubsetCollection.mem_lowerGapFillExtensions_iff {n k : ℕ}
    (W : Finset (KSubset n k)) (j₀ : Fin n) (T : KSubset n k) :
    T ∈ KSubsetCollection.lowerGapFillExtensions W j₀ ↔
      T ∈ KSubsetCollection.sameFrameExtensions W ∧ j₀ ∉ T.1 := by
  rw [lowerGapFillExtensions, Finset.mem_filter, mem_sameFrameExtensions_iff]
  simp only [Finset.mem_univ, true_and]
  tauto

/-- THE GAP-FILL RESIDUAL (unconditional): a wall `W` whose every member contains `j₀` has
at most ONE same-frame extension that omits `j₀`.  Immediate from the separation theorem for
`2 ≤ n`; for `n ≤ 1` every `j₀`-omitting `k`-subset is empty (so there is at most one). -/
theorem KSubsetCollection.lowerGapFill_extensions_card_le_one {n k : ℕ}
    {W : Finset (KSubset n k)} {j₀ : Fin n} (hW : ∀ S ∈ W, j₀ ∈ S.1) :
    (KSubsetCollection.lowerGapFillExtensions W j₀).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro T hT U hU
  rw [KSubsetCollection.mem_lowerGapFillExtensions_iff] at hT hU
  by_cases hn : 2 ≤ n
  · exact KSubsetCollection.sameFrameExtensions_eq_of_both_omit_commonPresent hn hW
      hT.1 hU.1 hT.2 hU.2
  · -- n ≤ 1: a `j₀`-omitting subset of `Fin n` is empty, so `T = U`
    apply Subtype.ext
    have hempty : ∀ V : KSubset n k, j₀ ∉ V.1 → V.1 = ∅ := by
      intro V hV
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have hxj : x = j₀ := by
        apply Fin.ext; have := x.isLt; have := j₀.isLt; omega
      exact hV (hxj ▸ hx)
    rw [hempty T hT.2, hempty U hU.2]

/-!
**The lower-frame uniqueness lemma** `KSubsetCollection.lowerGapFill_extensions_card_le_one`: a wall
`W` all of whose members contain `j₀` has at most one same-frame extension that omits `j₀`.  The
unconditional `≤ 2` bound is `lowerGapFillExtensions_card_le_two`; this strengthens it to `≤ 1`.

Geometrically the two same-frame extensions are the two cells sharing the facet `W`, on opposite
sides of the `j₀`-wall, so exactly one omits `j₀`.  The proof is the separation theorem
`sameFrameExtensions_eq_of_both_omit_commonPresent` (two same-frame extensions both omitting a
wall-common coordinate are equal), in the prefix-count / `prefixWeight` framework; small cases are
`decide`-checked below for `n = 3`. -/

/-- UNCONDITIONAL `≤ 2`: the `j₀`-excluding extensions are a subset of the `≤ 2` same-frame
extensions of `W` (when `W` is extendable, it is `(insert T W).erase T` for any extension `T`).
The OPEN target sharpens this to `≤ 1`. -/
theorem KSubsetCollection.lowerGapFillExtensions_card_le_two {n k : ℕ}
    {W : Finset (KSubset n k)} {j₀ : Fin n} :
    (KSubsetCollection.lowerGapFillExtensions W j₀).card ≤ 2 := by
  classical
  rcases (KSubsetCollection.lowerGapFillExtensions W j₀).eq_empty_or_nonempty with h | ⟨T, hT⟩
  · rw [h, Finset.card_empty]; omega
  · have hTpair := (KSubsetCollection.mem_lowerGapFillExtensions_iff W j₀ T).mp hT
    have hTmax := ((KSubsetCollection.mem_sameFrameExtensions_iff W T).mp hTpair.1).2
    have hTnotin := ((KSubsetCollection.mem_sameFrameExtensions_iff W T).mp hTpair.1).1
    have hsub : KSubsetCollection.lowerGapFillExtensions W j₀ ⊆
        KSubsetCollection.sameFrameExtensions W :=
      fun S hS => ((KSubsetCollection.mem_lowerGapFillExtensions_iff W j₀ S).mp hS).1
    calc (KSubsetCollection.lowerGapFillExtensions W j₀).card
        ≤ (KSubsetCollection.sameFrameExtensions W).card := Finset.card_le_card hsub
      _ ≤ 2 := by
          rw [show W = (insert T W).erase T from (Finset.erase_insert hTnotin).symm]
          exact KSubsetCollection.sameFrame_extensions_card_le_two_of_erase_maximalSorted
            hTmax (Finset.mem_insert_self _ _)

/-- Gap-fill for `d = 2`, `k = 1` (axiom-free `decide`). -/
theorem KSubsetCollection.lowerGapFill_d2k1 :
    ∀ W : Finset (KSubset 3 1), ∀ j₀ : Fin 3, (∀ S ∈ W, j₀ ∈ S.1) →
      (KSubsetCollection.lowerGapFillExtensions W j₀).card ≤ 1 := by decide

/-- Gap-fill for `d = 2`, `k = 2` (axiom-free `decide`). -/
theorem KSubsetCollection.lowerGapFill_d2k2 :
    ∀ W : Finset (KSubset 3 2), ∀ j₀ : Fin 3, (∀ S ∈ W, j₀ ∈ S.1) →
      (KSubsetCollection.lowerGapFillExtensions W j₀).card ≤ 1 := by decide

/-! ### Frame-reduction bridge (toward the geometric lift)

A geometric cell's datum `base` can sit BELOW the coordinate-min frame at "common-present"
coordinates (those in every subset).  This reduction removes the common-present coordinates
from every subset (equivalently shifts `base` up to `coordMin`), preserving maximal-sortedness
— since every prefix count shifts by the SAME amount, the sorted-before relation is unchanged.
This is the combinatorial half of the lift from `sameFrameExtensions` to the geometric
`sameMinFrameCompletions`. -/
namespace KSubsetReduction

/-- Prefix count of the common coords below `t`. -/
def pcCommon {n : ℕ} (cp : Finset (Fin n)) (t : Fin n) : ℕ := (cp.filter (· ≤ t)).card

theorem prefixCount_sdiff {n k : ℕ} (cp : Finset (Fin n)) (S : KSubset n k)
    (hcp : cp ⊆ S.1) (t : Fin n) :
    ((S.1 \ cp).filter (· ≤ t)).card = KSubset.prefixCount S t - pcCommon cp t := by
  classical
  have hsub : cp.filter (· ≤ t) ⊆ S.1.filter (· ≤ t) :=
    Finset.filter_subset_filter _ hcp
  have hfd : (S.1 \ cp).filter (· ≤ t) = S.1.filter (· ≤ t) \ cp.filter (· ≤ t) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  rw [hfd, KSubset.prefixCount, pcCommon]
  have hd : Disjoint (S.1.filter (· ≤ t) \ cp.filter (· ≤ t)) (cp.filter (· ≤ t)) :=
    Finset.sdiff_disjoint
  have hu : (S.1.filter (· ≤ t) \ cp.filter (· ≤ t)) ∪ cp.filter (· ≤ t) = S.1.filter (· ≤ t) :=
    Finset.sdiff_union_of_subset hsub
  have : (S.1.filter (· ≤ t) \ cp.filter (· ≤ t)).card + (cp.filter (· ≤ t)).card
      = (S.1.filter (· ≤ t)).card := by rw [← Finset.card_union_of_disjoint hd, hu]
  omega

theorem prefixCount_le_of_subset {n k : ℕ} (cp : Finset (Fin n)) (S : KSubset n k)
    (hcp : cp ⊆ S.1) (t : Fin n) : pcCommon cp t ≤ KSubset.prefixCount S t := by
  rw [pcCommon, KSubset.prefixCount]
  exact Finset.card_le_card (Finset.filter_subset_filter _ hcp)

/-- The typed reduced subset `S \ cp`. -/
def removeCommon {n k : ℕ} (cp : Finset (Fin n)) (S : KSubset n k) (hcp : cp ⊆ S.1) :
    KSubset n (k - cp.card) :=
  ⟨S.1 \ cp, by
    have hu : (S.1 \ cp) ∪ cp = S.1 := Finset.sdiff_union_of_subset hcp
    have hcard : (S.1 \ cp).card + cp.card = S.1.card := by
      rw [← Finset.card_union_of_disjoint Finset.sdiff_disjoint, hu]
    rw [S.2] at hcard; omega⟩

theorem prefixCount_removeCommon {n k : ℕ} (cp : Finset (Fin n)) (S : KSubset n k)
    (hcp : cp ⊆ S.1) (t : Fin n) :
    KSubset.prefixCount (removeCommon cp S hcp) t = KSubset.prefixCount S t - pcCommon cp t := by
  rw [KSubset.prefixCount]; exact prefixCount_sdiff cp S hcp t

theorem sortedBefore_removeCommon {n k : ℕ} (cp : Finset (Fin n)) {S S' : KSubset n k}
    (hcp : cp ⊆ S.1) (hcp' : cp ⊆ S'.1) (h : KSubset.SortedBefore S S') :
    KSubset.SortedBefore (removeCommon cp S hcp) (removeCommon cp S' hcp') := by
  intro t
  rw [prefixCount_removeCommon, prefixCount_removeCommon]
  have h1 := (h t).1
  have h2 := (h t).2
  have hc1 := prefixCount_le_of_subset cp S hcp t
  have hc2 := prefixCount_le_of_subset cp S' hcp' t
  omega

theorem removeCommon_injective {n k : ℕ} (cp : Finset (Fin n)) {S S' : KSubset n k}
    (hcp : cp ⊆ S.1) (hcp' : cp ⊆ S'.1) (h : removeCommon cp S hcp = removeCommon cp S' hcp') :
    S = S' := by
  apply Subtype.ext
  have hd : S.1 \ cp = S'.1 \ cp := congrArg Subtype.val h
  calc S.1 = (S.1 \ cp) ∪ cp := (Finset.sdiff_union_of_subset hcp).symm
    _ = (S'.1 \ cp) ∪ cp := by rw [hd]
    _ = S'.1 := Finset.sdiff_union_of_subset hcp'

/-- The reduced collection (remove the common-present coords from every subset). -/
noncomputable def collRemoveCommon {n k : ℕ} (A : Finset (KSubset n k)) :
    Finset (KSubset n (k - (KSubsetCollection.commonPresent A).card)) :=
  A.attach.image fun S => removeCommon (KSubsetCollection.commonPresent A) S.1
    (fun i hi => (KSubsetCollection.mem_commonPresent_iff A i).mp hi S.1 S.2)

theorem collRemoveCommon_isSorted {n k : ℕ} {A : Finset (KSubset n k)}
    (hA : KSubsetCollection.IsSorted A) :
    KSubsetCollection.IsSorted (collRemoveCommon A) := by
  classical
  have hcpS : ∀ S ∈ A, KSubsetCollection.commonPresent A ⊆ S.1 := fun S hS i hi =>
    (KSubsetCollection.mem_commonPresent_iff A i).mp hi S hS
  intro I hI J hJ hIJ
  rw [collRemoveCommon, Finset.mem_image] at hI hJ
  obtain ⟨S, _, hSeq⟩ := hI
  obtain ⟨S', _, hS'eq⟩ := hJ
  have hSne : S ≠ S' := by
    intro h; apply hIJ; rw [← hSeq, ← hS'eq, h]
  have hSS' : S.1 ≠ S'.1 := fun h => hSne (Subtype.ext h)
  rw [← hSeq, ← hS'eq]
  rcases hA S.1 S.2 S'.1 S'.2 hSS' with hb | hb
  · exact Or.inl (sortedBefore_removeCommon _ (hcpS S.1 S.2) (hcpS S'.1 S'.2) hb)
  · exact Or.inr (sortedBefore_removeCommon _ (hcpS S'.1 S'.2) (hcpS S.1 S.2) hb)

theorem collRemoveCommon_card {n k : ℕ} (A : Finset (KSubset n k)) :
    (collRemoveCommon A).card = A.card := by
  classical
  have hcpS : ∀ S ∈ A, KSubsetCollection.commonPresent A ⊆ S.1 := fun S hS i hi =>
    (KSubsetCollection.mem_commonPresent_iff A i).mp hi S hS
  rw [collRemoveCommon, Finset.card_image_of_injOn, Finset.card_attach]
  intro S _ S' _ h
  exact Subtype.ext (removeCommon_injective _ (hcpS S.1 S.2) (hcpS S'.1 S'.2) h)

theorem collRemoveCommon_isMaximalSorted {n k : ℕ} {A : Finset (KSubset n k)}
    (hA : KSubsetCollection.IsMaximalSorted A) :
    KSubsetCollection.IsMaximalSorted (collRemoveCommon A) :=
  ⟨by rw [collRemoveCommon_card, hA.1], collRemoveCommon_isSorted hA.2⟩

end KSubsetReduction

/-! ### One-coordinate deletion machinery (toward the active-ground engine)

Delete a frozen coordinate `p` by re-indexing the ground set `Fin (n+1) → Fin n` via
`Fin.succAbove`.  The KEY (proved) facts are the prefix-count relationships: deleting
an ABSENT coordinate shifts every prefix profile by `succAbove` (`pc_delSet_absent`);
deleting a PRESENT one does the same up to a single common correction
(`pc_delSet_present`).  Both make sorted-before inequalities transfer (the correction
cancels).  These are the engine's remaining residual's core tools. -/

/-- The deleted subset's coordinate set: preimage of `S` under `Fin.succAbove p`. -/
def delSet {n k : ℕ} (p : Fin (n + 1)) (S : KSubset (n + 1) k) : Finset (Fin n) :=
  Finset.univ.filter (fun j => p.succAbove j ∈ S.1)

theorem mem_delSet {n k : ℕ} (p : Fin (n + 1)) (S : KSubset (n + 1) k) (j : Fin n) :
    j ∈ delSet p S ↔ p.succAbove j ∈ S.1 := by simp [delSet]

/-- Deleting an absent coordinate shifts every prefix count by `succAbove`. -/
theorem pc_delSet_absent {n k : ℕ} (p : Fin (n + 1)) (S : KSubset (n + 1) k)
    (hp : p ∉ S.1) (t : Fin n) :
    ((delSet p S).filter (· ≤ t)).card = (S.1.filter (· ≤ p.succAbove t)).card := by
  apply Finset.card_bij (fun j _ => p.succAbove j)
  · intro j hj
    simp only [delSet, mem_filter, mem_univ, true_and] at hj ⊢
    exact ⟨hj.1, Fin.succAbove_le_succAbove_iff.mpr hj.2⟩
  · intro a _ b _ hab
    exact Fin.succAbove_right_injective hab
  · intro x hx
    simp only [mem_filter] at hx
    have hxne : x ≠ p := fun h => hp (h ▸ hx.1)
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hxne
    refine ⟨j, ?_, hj⟩
    simp only [delSet, mem_filter, mem_univ, true_and]
    refine ⟨hj ▸ hx.1, ?_⟩
    rw [← Fin.succAbove_le_succAbove_iff (p := p), hj]; exact hx.2

theorem delSet_card_absent {n k : ℕ} (p : Fin (n + 1)) (S : KSubset (n + 1) k)
    (hp : p ∉ S.1) : (delSet p S).card = k := by
  have hb : (delSet p S).card = S.1.card := by
    apply Finset.card_bij (fun j _ => p.succAbove j)
    · intro j hj; rw [mem_delSet] at hj; exact hj
    · intro a _ b _ hab; exact Fin.succAbove_right_injective hab
    · intro x hx
      have hxne : x ≠ p := fun h => hp (h ▸ hx)
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hxne
      exact ⟨j, by rw [mem_delSet, hj]; exact hx, hj⟩
  rw [hb]; exact S.2

/-- Deleting a present coordinate shifts prefix counts by `succAbove`, minus a single
common correction `[p ≤ succAbove t]` (independent of `S`). -/
theorem pc_delSet_present {n k : ℕ} (p : Fin (n + 1)) (S : KSubset (n + 1) k)
    (hp : p ∈ S.1) (t : Fin n) :
    ((delSet p S).filter (· ≤ t)).card + (if p ≤ p.succAbove t then 1 else 0)
      = (S.1.filter (· ≤ p.succAbove t)).card := by
  have hbij : ((delSet p S).filter (· ≤ t)).card
      = ((S.1.filter (· ≤ p.succAbove t)).erase p).card := by
    apply Finset.card_bij (fun j _ => p.succAbove j)
    · intro j hj
      simp only [delSet, mem_filter, mem_univ, true_and] at hj
      rw [mem_erase]
      exact ⟨Fin.succAbove_ne p j, mem_filter.mpr ⟨hj.1, Fin.succAbove_le_succAbove_iff.mpr hj.2⟩⟩
    · intro a _ b _ hab; exact Fin.succAbove_right_injective hab
    · intro x hx
      rw [mem_erase, mem_filter] at hx
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hx.1
      refine ⟨j, ?_, hj⟩
      simp only [delSet, mem_filter, mem_univ, true_and]
      refine ⟨hj ▸ hx.2.1, ?_⟩
      rw [← Fin.succAbove_le_succAbove_iff (p := p), hj]; exact hx.2.2
  rw [hbij]
  by_cases h : p ≤ p.succAbove t
  · rw [if_pos h, Finset.card_erase_of_mem (mem_filter.mpr ⟨hp, h⟩)]
    have : 0 < (S.1.filter (· ≤ p.succAbove t)).card :=
      Finset.card_pos.mpr ⟨p, mem_filter.mpr ⟨hp, h⟩⟩
    omega
  · rw [if_neg h]
    have hpnm : p ∉ S.1.filter (· ≤ p.succAbove t) := fun hmem => h (mem_filter.mp hmem).2
    rw [Finset.erase_eq_of_notMem hpnm]; omega

theorem delSet_card_present {n k : ℕ} (p : Fin (n + 1)) (S : KSubset (n + 1) k)
    (hp : p ∈ S.1) : (delSet p S).card = k - 1 := by
  have hb : (delSet p S).card = (S.1.erase p).card := by
    apply Finset.card_bij (fun j _ => p.succAbove j)
    · intro j hj; rw [mem_delSet] at hj
      rw [mem_erase]; exact ⟨Fin.succAbove_ne p j, hj⟩
    · intro a _ b _ hab; exact Fin.succAbove_right_injective hab
    · intro x hx
      rw [mem_erase] at hx
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hx.1
      exact ⟨j, by rw [mem_delSet, hj]; exact hx.2, hj⟩
  rw [hb, Finset.card_erase_of_mem hp, S.2]

/-! ### Deletion as `KSubset` maps; sortedness preserved (toward the engine) -/

/-- Wrap `delSet` into a `KSubset` map (absent coordinate). -/
noncomputable def KSubset.deleteAbsentCoord {n k : ℕ} (p : Fin (n + 1))
    (S : KSubset (n + 1) k) (hp : p ∉ S.1) : KSubset n k :=
  ⟨delSet p S, delSet_card_absent p S hp⟩

/-- Wrap `delSet` into a `KSubset` map (present coordinate; size drops to `k-1`). -/
noncomputable def KSubset.deletePresentCoord {n k : ℕ} (p : Fin (n + 1))
    (S : KSubset (n + 1) k) (hp : p ∈ S.1) : KSubset n (k - 1) :=
  ⟨delSet p S, delSet_card_present p S hp⟩

theorem KSubset.prefixCount_deleteAbsentCoord {n k : ℕ} (p : Fin (n + 1))
    (S : KSubset (n + 1) k) (hp : p ∉ S.1) (t : Fin n) :
    KSubset.prefixCount (KSubset.deleteAbsentCoord p S hp) t
      = KSubset.prefixCount S (p.succAbove t) :=
  pc_delSet_absent p S hp t

theorem KSubset.prefixCount_deletePresentCoord {n k : ℕ} (p : Fin (n + 1))
    (S : KSubset (n + 1) k) (hp : p ∈ S.1) (t : Fin n) :
    KSubset.prefixCount (KSubset.deletePresentCoord p S hp) t
      = KSubset.prefixCount S (p.succAbove t) - (if p ≤ p.succAbove t then 1 else 0) := by
  have h := pc_delSet_present p S hp t
  show ((delSet p S).filter (· ≤ t)).card
    = (S.1.filter (· ≤ p.succAbove t)).card - (if p ≤ p.succAbove t then 1 else 0)
  omega

/-- Sorted-before transfers under deleting an absent coordinate (specialise to
`succAbove t`). -/
theorem KSubset.SortedBefore.deleteAbsentCoord {n k : ℕ} {p : Fin (n + 1)}
    {S T : KSubset (n + 1) k} (hpS : p ∉ S.1) (hpT : p ∉ T.1)
    (h : KSubset.SortedBefore S T) :
    KSubset.SortedBefore (KSubset.deleteAbsentCoord p S hpS)
      (KSubset.deleteAbsentCoord p T hpT) := by
  intro t
  rw [KSubset.prefixCount_deleteAbsentCoord, KSubset.prefixCount_deleteAbsentCoord]
  exact h (p.succAbove t)

/-- Sorted-before transfers under deleting a present coordinate (the common
correction cancels). -/
theorem KSubset.SortedBefore.deletePresentCoord {n k : ℕ} {p : Fin (n + 1)}
    {S T : KSubset (n + 1) k} (hpS : p ∈ S.1) (hpT : p ∈ T.1)
    (h : KSubset.SortedBefore S T) :
    KSubset.SortedBefore (KSubset.deletePresentCoord p S hpS)
      (KSubset.deletePresentCoord p T hpT) := by
  intro t
  rw [KSubset.prefixCount_deletePresentCoord, KSubset.prefixCount_deletePresentCoord]
  have h2 := h (p.succAbove t)
  split_ifs <;> omega

/-- The image of a collection under deleting an absent coordinate. -/
noncomputable def KSubsetCollection.deleteAbsentCoord {n k : ℕ}
    (A : Finset (KSubset (n + 1) k)) (p : Fin (n + 1))
    (hpA : p ∈ KSubsetCollection.commonAbsent A) : Finset (KSubset n k) :=
  A.attach.image fun S =>
    KSubset.deleteAbsentCoord p S.1 ((KSubsetCollection.mem_commonAbsent_iff A p).mp hpA S.1 S.2)

/-- The image of a collection under deleting a present coordinate. -/
noncomputable def KSubsetCollection.deletePresentCoord {n k : ℕ}
    (A : Finset (KSubset (n + 1) k)) (p : Fin (n + 1))
    (hpA : p ∈ KSubsetCollection.commonPresent A) : Finset (KSubset n (k - 1)) :=
  A.attach.image fun S =>
    KSubset.deletePresentCoord p S.1 ((KSubsetCollection.mem_commonPresent_iff A p).mp hpA S.1 S.2)

/-- Sortedness is preserved under deleting an absent coordinate. -/
theorem KSubsetCollection.isSorted_deleteAbsentCoord {n k : ℕ}
    {A : Finset (KSubset (n + 1) k)} {p : Fin (n + 1)}
    (hA : KSubsetCollection.IsSorted A) (hpA : p ∈ KSubsetCollection.commonAbsent A) :
    KSubsetCollection.IsSorted (KSubsetCollection.deleteAbsentCoord A p hpA) := by
  classical
  intro I hI J hJ hIJ
  rw [KSubsetCollection.deleteAbsentCoord, Finset.mem_image] at hI hJ
  obtain ⟨S, _, rfl⟩ := hI
  obtain ⟨T, _, rfl⟩ := hJ
  have hST : S.1 ≠ T.1 := by
    intro h; apply hIJ; apply Subtype.ext
    show delSet p S.1 = delSet p T.1
    rw [h]
  have hpS := (KSubsetCollection.mem_commonAbsent_iff A p).mp hpA S.1 S.2
  have hpT := (KSubsetCollection.mem_commonAbsent_iff A p).mp hpA T.1 T.2
  rcases hA S.1 S.2 T.1 T.2 hST with hb | hb
  · exact Or.inl (KSubset.SortedBefore.deleteAbsentCoord hpS hpT hb)
  · exact Or.inr (KSubset.SortedBefore.deleteAbsentCoord hpT hpS hb)

/-- Sortedness is preserved under deleting a present coordinate. -/
theorem KSubsetCollection.isSorted_deletePresentCoord {n k : ℕ}
    {A : Finset (KSubset (n + 1) k)} {p : Fin (n + 1)}
    (hA : KSubsetCollection.IsSorted A) (hpA : p ∈ KSubsetCollection.commonPresent A) :
    KSubsetCollection.IsSorted (KSubsetCollection.deletePresentCoord A p hpA) := by
  classical
  intro I hI J hJ hIJ
  rw [KSubsetCollection.deletePresentCoord, Finset.mem_image] at hI hJ
  obtain ⟨S, _, rfl⟩ := hI
  obtain ⟨T, _, rfl⟩ := hJ
  have hST : S.1 ≠ T.1 := by
    intro h; apply hIJ; apply Subtype.ext
    show delSet p S.1 = delSet p T.1
    rw [h]
  have hpS := (KSubsetCollection.mem_commonPresent_iff A p).mp hpA S.1 S.2
  have hpT := (KSubsetCollection.mem_commonPresent_iff A p).mp hpA T.1 T.2
  rcases hA S.1 S.2 T.1 T.2 hST with hb | hb
  · exact Or.inl (KSubset.SortedBefore.deletePresentCoord hpS hpT hb)
  · exact Or.inr (KSubset.SortedBefore.deletePresentCoord hpT hpS hb)

/-- Image cardinality preserved (absent). -/
theorem KSubsetCollection.card_deleteAbsentCoord {n k : ℕ}
    (A : Finset (KSubset (n + 1) k)) (p : Fin (n + 1))
    (hpA : p ∈ KSubsetCollection.commonAbsent A) :
    (KSubsetCollection.deleteAbsentCoord A p hpA).card = A.card := by
  classical
  have hinj : Set.InjOn
      (fun S : {x // x ∈ A} =>
        KSubset.deleteAbsentCoord p S.1 ((KSubsetCollection.mem_commonAbsent_iff A p).mp hpA S.1 S.2))
      ↑(A.attach) := by
    intro S _ T _ heq
    have hdel : delSet p S.1 = delSet p T.1 := congrArg Subtype.val heq
    apply Subtype.ext; apply Subtype.ext
    ext x
    by_cases hx : x = p
    · rw [hx]
      exact ⟨fun h => absurd h ((KSubsetCollection.mem_commonAbsent_iff A p).mp hpA S.1 S.2),
             fun h => absurd h ((KSubsetCollection.mem_commonAbsent_iff A p).mp hpA T.1 T.2)⟩
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hx
      rw [← hj, ← mem_delSet p S.1 j, ← mem_delSet p T.1 j, hdel]
  rw [KSubsetCollection.deleteAbsentCoord, Finset.card_image_of_injOn hinj, Finset.card_attach]

/-- Image cardinality preserved (present). -/
theorem KSubsetCollection.card_deletePresentCoord {n k : ℕ}
    (A : Finset (KSubset (n + 1) k)) (p : Fin (n + 1))
    (hpA : p ∈ KSubsetCollection.commonPresent A) :
    (KSubsetCollection.deletePresentCoord A p hpA).card = A.card := by
  classical
  have hinj : Set.InjOn
      (fun S : {x // x ∈ A} =>
        KSubset.deletePresentCoord p S.1 ((KSubsetCollection.mem_commonPresent_iff A p).mp hpA S.1 S.2))
      ↑(A.attach) := by
    intro S _ T _ heq
    have hdel : delSet p S.1 = delSet p T.1 := congrArg Subtype.val heq
    apply Subtype.ext; apply Subtype.ext
    ext x
    by_cases hx : x = p
    · rw [hx]
      exact ⟨fun _ => (KSubsetCollection.mem_commonPresent_iff A p).mp hpA T.1 T.2,
             fun _ => (KSubsetCollection.mem_commonPresent_iff A p).mp hpA S.1 S.2⟩
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hx
      rw [← hj, ← mem_delSet p S.1 j, ← mem_delSet p T.1 j, hdel]
  rw [KSubsetCollection.deletePresentCoord, Finset.card_image_of_injOn hinj, Finset.card_attach]

/-- STRUCTURAL FOUNDATION for the `c = 1` up-side: a CODIM-ONE sorted wall (`card = n`) with a
common-absent coordinate `p` DELETES (at `p`) to a MAXIMAL sorted collection in `Fin n` (`card = n
= ground`).  So such a wall is "maximal-minus-a-coordinate"; its same-frame extension is the unique
re-insertion of `p` into that maximal collection (the remaining construction). -/
theorem KSubsetCollection.isMaximalSorted_deleteAbsentCoord_of_card_eq {n k : ℕ}
    {A : Finset (KSubset (n + 1) k)} (hA : KSubsetCollection.IsSorted A) (hcard : A.card = n)
    {p : Fin (n + 1)} (hp : p ∈ KSubsetCollection.commonAbsent A) :
    KSubsetCollection.IsMaximalSorted (KSubsetCollection.deleteAbsentCoord A p hp) :=
  ⟨(KSubsetCollection.card_deleteAbsentCoord A p hp).trans hcard,
    KSubsetCollection.isSorted_deleteAbsentCoord hA hp⟩

/-- EXACT frozen-count drop (absent): `frozen(image) + 1 = frozen(A)`.  This is the
direction the engine's induction needs (it gives `frozen A ≤ frozen image + 1`).
Proof: `succAbove p` is a bijection `frozenCoords(image) ≃ frozenCoords A \ {p}`
(forward+backward membership transfer + `succAbove ≠ p`). -/
theorem KSubsetCollection.frozenCoords_deleteAbsentCoord_succ {n k : ℕ}
    {A : Finset (KSubset (n + 1) k)} {p : Fin (n + 1)}
    (hpA : p ∈ KSubsetCollection.commonAbsent A) :
    (KSubsetCollection.frozenCoords (KSubsetCollection.deleteAbsentCoord A p hpA)).card + 1
      = (KSubsetCollection.frozenCoords A).card := by
  classical
  have hmem : ∀ (S : KSubset (n + 1) k) (hS : S ∈ A),
      KSubset.deleteAbsentCoord p S ((KSubsetCollection.mem_commonAbsent_iff A p).mp hpA S hS)
        ∈ KSubsetCollection.deleteAbsentCoord A p hpA :=
    fun S hS => Finset.mem_image.mpr ⟨⟨S, hS⟩, Finset.mem_attach _ _, rfl⟩
  have hmap : ∀ j ∈ KSubsetCollection.frozenCoords (KSubsetCollection.deleteAbsentCoord A p hpA),
      p.succAbove j ∈ KSubsetCollection.frozenCoords A := by
    intro j hj
    rw [KSubsetCollection.frozenCoords, Finset.mem_union] at hj
    rw [KSubsetCollection.frozenCoords, Finset.mem_union]
    rcases hj with hjP | hjA
    · refine Or.inl ?_; rw [KSubsetCollection.mem_commonPresent_iff] at hjP ⊢
      intro S hS; have h1 := hjP _ (hmem S hS)
      rwa [show (KSubset.deleteAbsentCoord p S _).1 = delSet p S from rfl, mem_delSet] at h1
    · refine Or.inr ?_; rw [KSubsetCollection.mem_commonAbsent_iff] at hjA ⊢
      intro S hS; have h1 := hjA _ (hmem S hS)
      rwa [show (KSubset.deleteAbsentCoord p S _).1 = delSet p S from rfl, mem_delSet] at h1
  have hmap' : ∀ j, p.succAbove j ∈ KSubsetCollection.frozenCoords A →
      j ∈ KSubsetCollection.frozenCoords (KSubsetCollection.deleteAbsentCoord A p hpA) := by
    intro j hj
    rw [KSubsetCollection.frozenCoords, Finset.mem_union] at hj
    rw [KSubsetCollection.frozenCoords, Finset.mem_union]
    rcases hj with hjP | hjA
    · refine Or.inl ?_; rw [KSubsetCollection.mem_commonPresent_iff] at hjP ⊢
      intro I hI
      rw [KSubsetCollection.deleteAbsentCoord, Finset.mem_image] at hI
      obtain ⟨S, _, rfl⟩ := hI
      rw [show (KSubset.deleteAbsentCoord p S.1 _).1 = delSet p S.1 from rfl, mem_delSet]
      exact hjP S.1 S.2
    · refine Or.inr ?_; rw [KSubsetCollection.mem_commonAbsent_iff] at hjA ⊢
      intro I hI
      rw [KSubsetCollection.deleteAbsentCoord, Finset.mem_image] at hI
      obtain ⟨S, _, rfl⟩ := hI
      rw [show (KSubset.deleteAbsentCoord p S.1 _).1 = delSet p S.1 from rfl, mem_delSet]
      exact hjA S.1 S.2
  have hp_frozen : p ∈ KSubsetCollection.frozenCoords A := Finset.mem_union.mpr (Or.inr hpA)
  have hset : (KSubsetCollection.frozenCoords
      (KSubsetCollection.deleteAbsentCoord A p hpA)).image (p.succAbove)
      = (KSubsetCollection.frozenCoords A).erase p := by
    ext q
    rw [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨Fin.succAbove_ne p j, hmap j hj⟩
    · rintro ⟨hqp, hqA⟩
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hqp
      exact ⟨j, hmap' j hqA, rfl⟩
  have hcard : (KSubsetCollection.frozenCoords (KSubsetCollection.deleteAbsentCoord A p hpA)).card
      = ((KSubsetCollection.frozenCoords A).erase p).card := by
    rw [← hset, Finset.card_image_of_injective _ Fin.succAbove_right_injective]
  rw [hcard, Finset.card_erase_of_mem hp_frozen]
  have : 0 < (KSubsetCollection.frozenCoords A).card := Finset.card_pos.mpr ⟨p, hp_frozen⟩
  omega

/-- EXACT frozen-count drop (present): `frozen(image) + 1 = frozen(A)`. -/
theorem KSubsetCollection.frozenCoords_deletePresentCoord_succ {n k : ℕ}
    {A : Finset (KSubset (n + 1) k)} {p : Fin (n + 1)}
    (hpA : p ∈ KSubsetCollection.commonPresent A) :
    (KSubsetCollection.frozenCoords (KSubsetCollection.deletePresentCoord A p hpA)).card + 1
      = (KSubsetCollection.frozenCoords A).card := by
  classical
  have hmem : ∀ (S : KSubset (n + 1) k) (hS : S ∈ A),
      KSubset.deletePresentCoord p S ((KSubsetCollection.mem_commonPresent_iff A p).mp hpA S hS)
        ∈ KSubsetCollection.deletePresentCoord A p hpA :=
    fun S hS => Finset.mem_image.mpr ⟨⟨S, hS⟩, Finset.mem_attach _ _, rfl⟩
  have hmap : ∀ j ∈ KSubsetCollection.frozenCoords (KSubsetCollection.deletePresentCoord A p hpA),
      p.succAbove j ∈ KSubsetCollection.frozenCoords A := by
    intro j hj
    rw [KSubsetCollection.frozenCoords, Finset.mem_union] at hj
    rw [KSubsetCollection.frozenCoords, Finset.mem_union]
    rcases hj with hjP | hjA
    · refine Or.inl ?_; rw [KSubsetCollection.mem_commonPresent_iff] at hjP ⊢
      intro S hS; have h1 := hjP _ (hmem S hS)
      rwa [show (KSubset.deletePresentCoord p S _).1 = delSet p S from rfl, mem_delSet] at h1
    · refine Or.inr ?_; rw [KSubsetCollection.mem_commonAbsent_iff] at hjA ⊢
      intro S hS; have h1 := hjA _ (hmem S hS)
      rwa [show (KSubset.deletePresentCoord p S _).1 = delSet p S from rfl, mem_delSet] at h1
  have hmap' : ∀ j, p.succAbove j ∈ KSubsetCollection.frozenCoords A →
      j ∈ KSubsetCollection.frozenCoords (KSubsetCollection.deletePresentCoord A p hpA) := by
    intro j hj
    rw [KSubsetCollection.frozenCoords, Finset.mem_union] at hj
    rw [KSubsetCollection.frozenCoords, Finset.mem_union]
    rcases hj with hjP | hjA
    · refine Or.inl ?_; rw [KSubsetCollection.mem_commonPresent_iff] at hjP ⊢
      intro I hI
      rw [KSubsetCollection.deletePresentCoord, Finset.mem_image] at hI
      obtain ⟨S, _, rfl⟩ := hI
      rw [show (KSubset.deletePresentCoord p S.1 _).1 = delSet p S.1 from rfl, mem_delSet]
      exact hjP S.1 S.2
    · refine Or.inr ?_; rw [KSubsetCollection.mem_commonAbsent_iff] at hjA ⊢
      intro I hI
      rw [KSubsetCollection.deletePresentCoord, Finset.mem_image] at hI
      obtain ⟨S, _, rfl⟩ := hI
      rw [show (KSubset.deletePresentCoord p S.1 _).1 = delSet p S.1 from rfl, mem_delSet]
      exact hjA S.1 S.2
  have hp_frozen : p ∈ KSubsetCollection.frozenCoords A := Finset.mem_union.mpr (Or.inl hpA)
  have hset : (KSubsetCollection.frozenCoords
      (KSubsetCollection.deletePresentCoord A p hpA)).image (p.succAbove)
      = (KSubsetCollection.frozenCoords A).erase p := by
    ext q
    rw [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨Fin.succAbove_ne p j, hmap j hj⟩
    · rintro ⟨hqp, hqA⟩
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hqp
      exact ⟨j, hmap' j hqA, rfl⟩
  have hcard : (KSubsetCollection.frozenCoords (KSubsetCollection.deletePresentCoord A p hpA)).card
      = ((KSubsetCollection.frozenCoords A).erase p).card := by
    rw [← hset, Finset.card_image_of_injective _ Fin.succAbove_right_injective]
  rw [hcard, Finset.card_erase_of_mem hp_frozen]
  have : 0 < (KSubsetCollection.frozenCoords A).card := Finset.card_pos.mpr ⟨p, hp_frozen⟩
  omega

/-- THE active-ground engine (PROVED): a sorted collection of `k`-subsets of `Fin n`
with `2 ≤ |A|` satisfies `|A| + |frozenCoords A| ≤ n`.  Proof: strong induction on `n`
(`Fin (n+1) → Fin n` by deleting a frozen coordinate); base = `sorted_card_le_ground_card`;
step = `card_delete…` (`= |A|`) + `frozenCoords_delete…_succ` (`frozen(image)+1 = frozen A`)
+ `omega`.  The `2 ≤ |A|` is essential (false for singletons) and excludes the `n = 0`
base (no two-element collection there). -/
theorem KSubsetCollection.sorted_card_add_frozenCoords_card_le_ground_of_two_le_card
    {n k : ℕ} {A : Finset (KSubset n k)}
    (hA : KSubsetCollection.IsSorted A) (hcard : 2 ≤ A.card) :
    A.card + (KSubsetCollection.frozenCoords A).card ≤ n := by
  induction n generalizing k with
  | zero =>
    exfalso
    have hle : A.card ≤ 1 := Finset.card_le_one.mpr (fun a _ b _ =>
      Subtype.ext ((Finset.eq_empty_of_isEmpty a.1).trans (Finset.eq_empty_of_isEmpty b.1).symm))
    omega
  | succ n ih =>
    classical
    by_cases hfrozen : (KSubsetCollection.frozenCoords A).Nonempty
    · obtain ⟨p, hp⟩ := hfrozen
      rw [KSubsetCollection.frozenCoords, Finset.mem_union] at hp
      rcases hp with hp_present | hp_absent
      · have hcard' : 2 ≤ (KSubsetCollection.deletePresentCoord A p hp_present).card := by
          rw [KSubsetCollection.card_deletePresentCoord]; exact hcard
        have ih' := ih (KSubsetCollection.isSorted_deletePresentCoord hA hp_present) hcard'
        have he1 := KSubsetCollection.card_deletePresentCoord A p hp_present
        have he2 := KSubsetCollection.frozenCoords_deletePresentCoord_succ hp_present
        omega
      · have hcard' : 2 ≤ (KSubsetCollection.deleteAbsentCoord A p hp_absent).card := by
          rw [KSubsetCollection.card_deleteAbsentCoord]; exact hcard
        have ih' := ih (KSubsetCollection.isSorted_deleteAbsentCoord hA hp_absent) hcard'
        have he1 := KSubsetCollection.card_deleteAbsentCoord A p hp_absent
        have he2 := KSubsetCollection.frozenCoords_deleteAbsentCoord_succ hp_absent
        omega
    · have hfc : (KSubsetCollection.frozenCoords A).card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hfrozen)
      have hg := KSubsetCollection.sorted_card_le_ground_card (Nat.succ_pos n) hA
      omega

/-- The dimension-qualified erased-maximal wall lemma (needs `3 ≤ n`; see the `n = 2`
guardrail): erasing one subset from a maximal sorted collection freezes ≤ 1 coordinate.
Now UNCONDITIONAL (the engine is proved). -/
theorem KSubsetCollection.card_commonPresent_add_commonAbsent_le_one_of_erase_maximalSorted
    {n k : ℕ} (hn : 3 ≤ n) (_hk_pos : 0 < k) (_hk_lt : k < n)
    {C : Finset (KSubset n k)} (hC : KSubsetCollection.IsMaximalSorted C)
    {S₀ : KSubset n k} (hS₀ : S₀ ∈ C) :
    (KSubsetCollection.commonPresent (C.erase S₀)).card +
      (KSubsetCollection.commonAbsent (C.erase S₀)).card ≤ 1 := by
  classical
  have hCcard : C.card = n := hC.1
  have hAcard : (C.erase S₀).card = n - 1 := by
    rw [Finset.card_erase_of_mem hS₀, hCcard]
  have h2 : 2 ≤ (C.erase S₀).card := by rw [hAcard]; omega
  have hAne : (C.erase S₀).Nonempty := by rw [← Finset.card_pos]; omega
  have heng := KSubsetCollection.sorted_card_add_frozenCoords_card_le_ground_of_two_le_card
    (KSubsetCollection.isSorted_erase hC.2 S₀) h2
  have hfc := KSubsetCollection.frozenCoords_card hAne
  rw [hfc, hAcard] at heng
  omega

/-
The frozen-coordinate wall bound, built bottom-up: `sorted_card_le_ground_card`
(`0 < n → IsSorted A → |A| ≤ n`), one-coordinate deletion via `Fin.succAbove` with the exact frozen
drop `frozenCoords_…_succ`, then the engine `sorted_card_add_frozenCoords_card_le_ground_of_two_le_card`
(`2 ≤ |A| → |A| + frozenCoords ≤ n`, by induction on `n`), giving the wall lemma
`card_commonPresent_add_commonAbsent_le_one_of_erase_maximalSorted` (`3 ≤ n`) and the cell-level
`erasedSubsets_frozen_card_le_one` (`2 ≤ d`).  Two guardrails: the arbitrary-`A` engine is false
(`frozen_engine_false_for_singleton`), and the wall lemma needs `3 ≤ n` (`frozen_wall_bound_false_for_n2`). -/

end BarycentricFreudenthal
end SpernerFreudenthal
end EcoLean
