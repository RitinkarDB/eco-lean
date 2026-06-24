import Mathlib.Topology.Sequences
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Berge's maximum theorem on a real interval (toward nice-game point rationalizability)

A real-analysis brick for Battigalli–Catonini–De Vito Lemma 7 / Theorem 30: in a nice game the
best-response function (the unique maximiser of a continuous, strictly concave payoff section over a
compact action interval) depends continuously on the conjecture. This is the single-valued case of
Berge's maximum theorem, which Mathlib's nice-game *existence* development (the multi-valued Kakutani
argmax correspondence) does not provide.
-/

namespace EcoLean.GameTheory

open Filter Topology Set

/-- **Berge's maximum theorem, single-valued, on a real interval.** If `u : C × ℝ → ℝ` is jointly
continuous and each section `u c` is strictly concave on `[lo, hi]`, then the (unique) maximiser
`r c` of `u c` over `[lo, hi]` is a continuous function of `c`. -/
theorem bestResponse_continuous {C : Type*} [TopologicalSpace C] [SequentialSpace C]
    {lo hi : ℝ} {u : C → ℝ → ℝ} (hcont : Continuous (Function.uncurry u))
    (hstrict : ∀ c, StrictConcaveOn ℝ (Set.Icc lo hi) (u c))
    {r : C → ℝ} (hrmem : ∀ c, r c ∈ Set.Icc lo hi)
    (hr : ∀ c, IsMaxOn (u c) (Set.Icc lo hi) (r c)) :
    Continuous r := by
  rw [continuous_iff_seqContinuous]
  intro cs c hcs
  refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
  obtain ⟨a, haI, φ, hφmono, hφtend⟩ :=
    isCompact_Icc.tendsto_subseq (x := fun k => r (cs (ns k))) (fun k => hrmem (cs (ns k)))
  refine ⟨φ, ?_⟩
  have hcsc : Tendsto (fun k => cs (ns (φ k))) atTop (𝓝 c) :=
    hcs.comp (hns.comp hφmono.tendsto_atTop)
  have hmaxa : IsMaxOn (u c) (Set.Icc lo hi) a := by
    intro b hb
    have hRHS : Tendsto (fun k => u (cs (ns (φ k))) (r (cs (ns (φ k))))) atTop (𝓝 (u c a)) :=
      (hcont.tendsto (c, a)).comp (hcsc.prodMk_nhds hφtend)
    have hLHS : Tendsto (fun k => u (cs (ns (φ k))) b) atTop (𝓝 (u c b)) :=
      ((hcont.comp (continuous_id.prodMk continuous_const)).tendsto c).comp hcsc
    exact le_of_tendsto_of_tendsto' hLHS hRHS (fun k => hr (cs (ns (φ k))) hb)
  have ha_eq : a = r c := (hstrict c).eq_of_isMaxOn hmaxa (hr c) haI (hrmem c)
  rw [← ha_eq]
  exact hφtend

/-- A strictly concave function on a convex set is **strictly increasing below its maximiser**:
if `x < y ≤ m` and `m` maximises `f`, then `f x < f y`. (The dominating-endpoint half of Lemma 7.) -/
theorem StrictConcaveOn.lt_of_lt_le_isMaxOn {s : Set ℝ} {f : ℝ → ℝ}
    (hf : StrictConcaveOn ℝ s f) {m x y : ℝ} (hm : IsMaxOn f s m) (hms : m ∈ s) (hxs : x ∈ s)
    (hxy : x < y) (hym : y ≤ m) : f x < f y := by
  have hxm : x < m := lt_of_lt_of_le hxy hym
  have hys : y ∈ s := hf.1.ordConnected.out hxs hms ⟨le_of_lt hxy, hym⟩
  have hmx : (0:ℝ) < m - x := by linarith
  have hmxne : m - x ≠ 0 := ne_of_gt hmx
  rcases eq_or_lt_of_le hym with rfl | hyltm
  · -- `y = m`: a strict midpoint sits strictly above `f x`, and `m` is the maximiser.
    have hcomb := hf.2 hxs hys (ne_of_lt hxy)
      (show (0:ℝ) < 1/2 by norm_num) (show (0:ℝ) < 1/2 by norm_num)
      (show (1:ℝ)/2 + 1/2 = 1 by norm_num)
    have hmid : ((1:ℝ)/2) • x + ((1:ℝ)/2) • y ∈ s :=
      hf.1 hxs hys (by norm_num) (by norm_num) (by norm_num)
    have hmax := hm hmid
    simp only [smul_eq_mul, Set.mem_setOf_eq] at hcomb hmax
    nlinarith [hcomb, hmax]
  · -- `y` is a strict convex combination of `x` and `m`.
    set t : ℝ := (y - x) / (m - x) with ht
    have htpos : 0 < t := by rw [ht]; exact div_pos (by linarith) hmx
    have htlt : t < 1 := by rw [ht, div_lt_one hmx]; linarith
    have h1t : 0 < 1 - t := by linarith
    have hcomb := hf.2 hxs hms (ne_of_lt hxm) h1t htpos (by ring)
    have hcombo : (1 - t) • x + t • m = y := by
      simp only [ht, smul_eq_mul]; field_simp; ring
    rw [hcombo] at hcomb
    have hfm : f y ≤ f m := hm hys
    simp only [smul_eq_mul] at hcomb
    nlinarith [hcomb, hfm, htpos, h1t]

/-- A strictly concave function on a convex set is **strictly decreasing above its maximiser**:
if `m ≤ y < x` and `m` maximises `f`, then `f x < f y`. (The mirror of `lt_of_lt_le_isMaxOn`.) -/
theorem StrictConcaveOn.lt_of_le_lt_isMaxOn {s : Set ℝ} {f : ℝ → ℝ}
    (hf : StrictConcaveOn ℝ s f) {m x y : ℝ} (hm : IsMaxOn f s m) (hms : m ∈ s) (hxs : x ∈ s)
    (hmy : m ≤ y) (hyx : y < x) : f x < f y := by
  have hmx : m < x := lt_of_le_of_lt hmy hyx
  have hys : y ∈ s := hf.1.ordConnected.out hms hxs ⟨hmy, le_of_lt hyx⟩
  rcases eq_or_lt_of_le hmy with rfl | hmlt
  · -- `y = m` (substituted to `m`): a strict midpoint sits strictly above `f x`.
    have hcomb := hf.2 hms hxs (ne_of_lt hmx)
      (show (0:ℝ) < 1/2 by norm_num) (show (0:ℝ) < 1/2 by norm_num)
      (show (1:ℝ)/2 + 1/2 = 1 by norm_num)
    have hmid : ((1:ℝ)/2) • m + ((1:ℝ)/2) • x ∈ s :=
      hf.1 hms hxs (by norm_num) (by norm_num) (by norm_num)
    have hmax := hm hmid
    simp only [smul_eq_mul, Set.mem_setOf_eq] at hcomb hmax
    nlinarith [hcomb, hmax]
  · have hxm : (0:ℝ) < x - m := by linarith
    set t : ℝ := (x - y) / (x - m) with ht
    have htpos : 0 < t := by rw [ht]; exact div_pos (by linarith) hxm
    have htlt : t < 1 := by rw [ht, div_lt_one hxm]; linarith
    have h1t : 0 < 1 - t := by linarith
    have hcomb := hf.2 hms hxs (ne_of_lt hmx) htpos h1t (by ring)
    have hcombo : t • m + (1 - t) • x = y := by
      simp only [ht, smul_eq_mul]; field_simp; ring
    rw [hcombo] at hcomb
    have hfm : f y ≤ f m := hm hys
    simp only [smul_eq_mul] at hcomb
    nlinarith [hcomb, hfm, htpos, h1t]

/-- **Lemma 7 (the point-rationalizability/pure-dominance equivalence).** In a nice game — a jointly
continuous payoff, strictly concave in the own action on a compact action interval, over a compact
connected conjecture space `C` — an action is a best reply to some deterministic conjecture iff it is
not strictly dominated by another pure action. (Battigalli–Catonini–De Vito, Lemma 7 / Theorem 30.) -/
theorem bestReply_eq_not_pureDominated
    {C : Type*} [TopologicalSpace C] [SequentialSpace C] [CompactSpace C] [PreconnectedSpace C]
    [Nonempty C] {lo hi : ℝ} (hlohi : lo ≤ hi) {u : C → ℝ → ℝ}
    (hcont : Continuous (Function.uncurry u))
    (hstrict : ∀ c, StrictConcaveOn ℝ (Set.Icc lo hi) (u c)) :
    {a | a ∈ Set.Icc lo hi ∧ ∃ c, IsMaxOn (u c) (Set.Icc lo hi) a}
      = {a | a ∈ Set.Icc lo hi ∧ ¬ ∃ b ∈ Set.Icc lo hi, ∀ c, u c a < u c b} := by
  classical
  have hsecCont : ∀ c, Continuous (fun x => u c x) := fun c =>
    hcont.comp (continuous_const.prodMk continuous_id)
  have hexr : ∀ c, ∃ a, a ∈ Set.Icc lo hi ∧ IsMaxOn (u c) (Set.Icc lo hi) a := fun c =>
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hlohi) (hsecCont c).continuousOn
  set r : C → ℝ := fun c => (hexr c).choose with hrdef
  have hrmem : ∀ c, r c ∈ Set.Icc lo hi := fun c => (hexr c).choose_spec.1
  have hr : ∀ c, IsMaxOn (u c) (Set.Icc lo hi) (r c) := fun c => (hexr c).choose_spec.2
  have hrcont : Continuous r := bestResponse_continuous hcont hstrict hrmem hr
  ext a
  simp only [Set.mem_setOf_eq]
  refine ⟨fun ⟨haI, c, hmax⟩ => ⟨haI, fun ⟨b, hbI, hdom⟩ =>
    absurd (hmax hbI) (not_le.mpr (hdom c))⟩, fun ⟨haI, hnotdom⟩ => ⟨haI, ?_⟩⟩
  by_contra hno
  push_neg at hno
  apply hnotdom
  have hrange_compact : IsCompact (Set.range r) := isCompact_range hrcont
  have hrange_conn : IsPreconnected (Set.range r) := by
    rw [← Set.image_univ]; exact isPreconnected_univ.image r hrcont.continuousOn
  have hrange_ne : (Set.range r).Nonempty := Set.range_nonempty r
  set rmin := sInf (Set.range r) with hrmindef
  set rmax := sSup (Set.range r) with hrmaxdef
  have hrmin_mem : rmin ∈ Set.range r := hrange_compact.sInf_mem hrange_ne
  have hrmax_mem : rmax ∈ Set.range r := hrange_compact.sSup_mem hrange_ne
  have hrange_sub : Set.range r ⊆ Set.Icc lo hi := by rintro _ ⟨c, rfl⟩; exact hrmem c
  have hrmin_le : ∀ c, rmin ≤ r c := fun c => csInf_le hrange_compact.bddBelow ⟨c, rfl⟩
  have hrle_max : ∀ c, r c ≤ rmax := fun c => le_csSup hrange_compact.bddAbove ⟨c, rfl⟩
  have ha_notrange : a ∉ Set.range r := by
    rintro ⟨c, hc⟩; exact hno c (hc ▸ hr c)
  have hcase : a < rmin ∨ rmax < a := by
    by_contra hc
    push_neg at hc
    exact ha_notrange (hrange_conn.ordConnected.out hrmin_mem hrmax_mem ⟨hc.1, hc.2⟩)
  rcases hcase with hlt | hgt
  · exact ⟨rmin, hrange_sub hrmin_mem, fun c =>
      StrictConcaveOn.lt_of_lt_le_isMaxOn (hstrict c) (hr c) (hrmem c) haI hlt (hrmin_le c)⟩
  · exact ⟨rmax, hrange_sub hrmax_mem, fun c =>
      StrictConcaveOn.lt_of_le_lt_isMaxOn (hstrict c) (hr c) (hrmem c) haI (hrle_max c) hgt⟩

end EcoLean.GameTheory
