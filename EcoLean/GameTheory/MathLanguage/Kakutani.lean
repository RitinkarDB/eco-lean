import EcoLean.GameTheory.MathLanguage.SpernerBrouwer
import EcoLean.GameTheory.MathLanguage.SetsFunctionsCorrespondences
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Kakutani's fixed-point theorem and its extension to compact convex bodies

Building on the Brouwer fixed-point theorem `brouwer_simplex_sorted` and the abstract
correspondence/Kakutani scaffolding in `SetsFunctionsCorrespondences.lean`, this file proves, in
order:

* the Brouwer fixed-point property of the standard simplex viewed as a set
  (`brouwerFixedPointProperty_stdSimplex`);
* Kakutani's fixed-point theorem on the standard simplex, via Cellina's continuous approximate
  selection (`kakutaniFixedPointProperty_stdSimplex`);
* transfer of the Kakutani property along a continuous retraction, hence to any compact convex
  subset of a set that already has it (`KakutaniFixedPointProperty.of_retraction`,
  `kakutaniFixedPointProperty_of_subset_stdSimplex`);
* the Kakutani fixed-point property of an arbitrary nonempty compact convex body in a
  finite-dimensional real normed space (`kakutaniFixedPointProperty_of_isCompact_convex_finrank`),
  via the nearest-point metric projection and an affine-section transfer across the dimension gap;
* as a special case, the property of a product of standard simplices
  (`kakutaniFixedPointProperty_pi_stdSimplex`).
-/

namespace EcoLean
namespace GameTheory
namespace Correspondence

open scoped BigOperators

/-- **The Brouwer fixed-point property of the standard simplex (as a set).**
`brouwer_simplex_sorted` (a fixed point for every continuous self-map of
the *subtype* `StdSimplex d`) yields the carrier-set `BrouwerFixedPointProperty` for the
*set* `stdSimplex ℝ (Fin (d+1))`, for `2 ≤ d`.  The two are defeq subtypes, so the only
work is bridging `MapsTo`/`ContinuousOn` on the set to `Continuous` on the subtype. -/
theorem brouwerFixedPointProperty_stdSimplex {d : ℕ} (hd : 2 ≤ d) :
    BrouwerFixedPointProperty (stdSimplex ℝ (Fin (d + 1))) := by
  classical
  intro f hfMap hfCont
  -- `StdSimplex d` is defeq to `↥(stdSimplex ℝ (Fin (d+1)))`, so this typechecks as a
  -- continuous self-map of the eco-lean simplex subtype.
  let g : EcoLean.SpernerFreudenthal.Brouwer.StdSimplex d →
      EcoLean.SpernerFreudenthal.Brouwer.StdSimplex d :=
    fun x => ⟨f x.1, hfMap x.2⟩
  have hgCont : Continuous g :=
    (hfCont.restrict).codRestrict (fun x => hfMap x.2)
  obtain ⟨z, hz⟩ := EcoLean.SpernerFreudenthal.Brouwer.brouwer_simplex_sorted hd g hgCont
  refine ⟨z.1, z.2, ?_⟩
  have hval : (g z).1 = z.1 := congrArg Subtype.val hz
  simpa [g] using hval

/-- **The upper-hemicontinuity ball property.**  With a closed graph on a
compact domain whose values lie back in the domain, the values `F z` (for `z ∈ K`) of points
`z` close to `x ∈ K` are contained in the `ε`-thickening of `F x`.  Proved by a closed-image
(projection) argument — no sequences. -/
theorem exists_ball_forall_subset_thickening_of_closedGraph
    {X : Type*} [PseudoMetricSpace X] [T2Space X]
    {K : Set X} {F : Correspondence X X}
    (hKcompact : IsCompact K) (hFclosed : ClosedGraphOn F K) (hFmaps : MapsToOn F K K)
    {x : X} (hx : x ∈ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ K, dist z x < δ → F z ⊆ Metric.thickening ε (F x) := by
  classical
  have hUopen : IsOpen (Metric.thickening ε (F x)) := Metric.isOpen_thickening
  -- The "bad" set: graph points whose image coordinate escapes the thickening.
  have hCclosed :
      IsClosed (graphOn F K ∩ {p : X × X | p.2 ∉ Metric.thickening ε (F x)}) :=
    IsClosed.inter hFclosed ((hUopen.preimage continuous_snd).isClosed_compl)
  have hCsub :
      graphOn F K ∩ {p : X × X | p.2 ∉ Metric.thickening ε (F x)} ⊆ K ×ˢ K := by
    rintro ⟨z, y⟩ ⟨hzy, -⟩
    rw [mem_graphOn_iff] at hzy
    exact ⟨hzy.1, hFmaps hzy.1 hzy.2⟩
  have hCcompact :
      IsCompact (graphOn F K ∩ {p : X × X | p.2 ∉ Metric.thickening ε (F x)}) :=
    (hKcompact.prod hKcompact).of_isClosed_subset hCclosed hCsub
  have hProjClosed :
      IsClosed (Prod.fst '' (graphOn F K ∩ {p : X × X | p.2 ∉ Metric.thickening ε (F x)})) :=
    (hCcompact.image continuous_fst).isClosed
  have hxNot :
      x ∉ Prod.fst '' (graphOn F K ∩ {p : X × X | p.2 ∉ Metric.thickening ε (F x)}) := by
    rintro ⟨⟨z, y⟩, ⟨hzy, hyU⟩, rfl⟩
    rw [mem_graphOn_iff] at hzy
    exact hyU (Metric.mem_thickening_iff.mpr ⟨y, hzy.2, by simpa using hε⟩)
  obtain ⟨δ, hδpos, hball⟩ := Metric.isOpen_iff.mp hProjClosed.isOpen_compl x hxNot
  refine ⟨δ, hδpos, fun z hzK hzx y hyFz => ?_⟩
  by_contra hyU
  exact hball (by rwa [Metric.mem_ball])
    ⟨(z, y), ⟨mem_graphOn_iff.mpr ⟨hzK, hyFz⟩, hyU⟩, rfl⟩

/-- **An explicit tent partition of unity** subordinate to a finite ball cover of `K`.
For a finite index `ι`, centers `c i`, radii `ρ i > 0`, with `K` covered by the balls
`ball (c i) (ρ i)`, the normalized tents `h i p = max 0 (ρ i − dist p (c i)) / (∑ⱼ …)` are
nonnegative, continuous on `K`, sum to one on `K`, and vanish off the `i`-th ball. -/
theorem exists_tent_partition
    {X : Type*} [PseudoMetricSpace X] {ι : Type*} [Fintype ι]
    (c : ι → X) (ρ : ι → ℝ) {K : Set X}
    (hcover : ∀ p ∈ K, ∃ i, dist p (c i) < ρ i) :
    ∃ h : ι → X → ℝ,
      (∀ i, ContinuousOn (h i) K) ∧
      (∀ i p, 0 ≤ h i p) ∧
      (∀ p ∈ K, ∑ i, h i p = 1) ∧
      (∀ i p, h i p ≠ 0 → dist p (c i) < ρ i) := by
  classical
  set w : ι → X → ℝ := fun i p => max 0 (ρ i - dist p (c i)) with hw
  set W : X → ℝ := fun p => ∑ i, w i p with hW
  have hwnonneg : ∀ i p, 0 ≤ w i p := fun i p => le_max_left _ _
  have hWnonneg : ∀ p, 0 ≤ W p := fun p => Finset.sum_nonneg fun i _ => hwnonneg i p
  have hwcont : ∀ i, Continuous (w i) := fun i =>
    continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))
  have hWcont : Continuous W := continuous_finset_sum _ fun i _ => hwcont i
  have hwactive : ∀ i p, w i p ≠ 0 → dist p (c i) < ρ i := by
    intro i p hwp
    by_contra hge
    push_neg at hge
    exact hwp (by rw [hw]; exact max_eq_left (by linarith))
  have hWpos : ∀ p ∈ K, 0 < W p := by
    intro p hp
    obtain ⟨i, hi⟩ := hcover p hp
    have hwi : 0 < w i p := by rw [hw]; exact lt_max_iff.mpr (Or.inr (by linarith))
    exact lt_of_lt_of_le hwi
      (Finset.single_le_sum (fun j _ => hwnonneg j p) (Finset.mem_univ i))
  refine ⟨fun i p => w i p / W p, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hwcont i).continuousOn.div hWcont.continuousOn fun p hp => (hWpos p hp).ne'
  · intro i p; exact div_nonneg (hwnonneg i p) (hWnonneg p)
  · intro p hp
    show (∑ i, w i p / W p) = 1
    rw [← Finset.sum_div]
    exact div_self (hWpos p hp).ne'
  · intro i p hdiv
    refine hwactive i p fun hwzero => hdiv ?_
    show w i p / W p = 0
    rw [hwzero, zero_div]

open scoped BigOperators in
/-- **Cellina's continuous approximate selection.**  A correspondence satisfying the
Kakutani hypotheses on a compact convex carrier `K` of a normed space has, for every `ε > 0`,
a continuous `ε`-approximate selection (`ApproximateKakutaniSelection`).  Construction: cover `K`
by uhc balls, take the explicit tent partition of unity, and form the convex combination
`∑ᵢ hᵢ(p) • yᵢ` of selected values `yᵢ ∈ F(cᵢ)`. -/
theorem KakutaniPremises.nonempty_approximateKakutaniSelection
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [T2Space X]
    {K : Set X} {F : Correspondence X X} (hF : KakutaniPremises K F)
    {ε : ℝ} (hε : 0 < ε) :
    Nonempty (ApproximateKakutaniSelection K F ε) := by
  classical
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  -- For every `x ∈ K` choose a radius `δ x ≤ ε` with the uhc(ε/2) ball property.
  have hδexists : ∀ x ∈ K, ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧
      ∀ z ∈ K, dist z x < δ → F z ⊆ Metric.thickening (ε / 2) (F x) := by
    intro x hx
    obtain ⟨δ, hδpos, hδball⟩ :=
      exists_ball_forall_subset_thickening_of_closedGraph
        hF.compact_domain hF.closed_graph hF.mapsTo_domain hx hε2
    refine ⟨min δ ε, lt_min hδpos hε, min_le_right _ _, fun z hz hlt => ?_⟩
    exact hδball z hz (lt_of_lt_of_le hlt (min_le_left _ _))
  let δ : X → ℝ := fun x => if hx : x ∈ K then Classical.choose (hδexists x hx) else ε
  have hδspec : ∀ x (hx : x ∈ K), 0 < δ x ∧ δ x ≤ ε ∧
      ∀ z ∈ K, dist z x < δ x → F z ⊆ Metric.thickening (ε / 2) (F x) := by
    intro x hx
    have : δ x = Classical.choose (hδexists x hx) := dif_pos hx
    rw [this]; exact Classical.choose_spec (hδexists x hx)
  -- Finite subcover of `K` by the balls `ball x (δ x / 2)`.
  have hcoverK : K ⊆ ⋃ x ∈ K, Metric.ball x (δ x / 2) := by
    intro p hp
    exact Set.mem_biUnion hp (Metric.mem_ball_self (by have := (hδspec p hp).1; linarith))
  obtain ⟨K', hK'sub, hK'fin, hK'cover⟩ :=
    hF.compact_domain.elim_finite_subcover_image
      (fun x _ => Metric.isOpen_ball) hcoverK
  haveI : Fintype (↥K') := hK'fin.fintype
  let c : (↥K') → X := Subtype.val
  let ρ : (↥K') → ℝ := fun i => δ (c i) / 2
  have hcK : ∀ i : ↥K', c i ∈ K := fun i => hK'sub i.2
  have hcover : ∀ p ∈ K, ∃ i : ↥K', dist p (c i) < ρ i := by
    intro p hp
    obtain ⟨x, hx, hpx⟩ := Set.mem_iUnion₂.mp (hK'cover hp)
    exact ⟨⟨x, hx⟩, by simpa [c, ρ] using hpx⟩
  obtain ⟨h, hhcont, hhnonneg, hhsum, hhsupp⟩ := exists_tent_partition c ρ hcover
  -- Selections `y i ∈ F (c i)`.
  have hynonempty : ∀ i : ↥K', (F (c i)).Nonempty := fun i => hF.nonempty_values (hcK i)
  let y : (↥K') → X := fun i => Classical.choose (hynonempty i)
  have hymem : ∀ i, y i ∈ F (c i) := fun i => Classical.choose_spec (hynonempty i)
  -- The candidate selection map.
  let g : X → X := fun p => ∑ i, h i p • y i
  refine ⟨⟨g, ?_, ?_, ?_⟩⟩
  · -- maps `K` into `K`
    intro p hp
    refine hF.convex_domain.sum_mem (fun i _ => hhnonneg i p) (hhsum p hp) ?_
    exact fun i _ => hF.mapsTo_domain (hcK i) (hymem i)
  · -- continuous on `K`
    refine continuousOn_finset_sum _ (fun i _ => ?_)
    exact (hhcont i).smul continuousOn_const
  · -- approximate graph property
    intro p hp
    -- pick an active index `i₀` maximizing `δ (c i₀)`
    have hJne : (Finset.univ.filter (fun i : ↥K' => h i p ≠ 0)).Nonempty := by
      obtain ⟨i, _, hi⟩ :=
        Finset.exists_ne_zero_of_sum_ne_zero (s := (Finset.univ : Finset ↥K'))
          (by rw [hhsum p hp]; exact one_ne_zero)
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    obtain ⟨i₀, hi₀mem, hi₀max⟩ :=
      Finset.exists_max_image _ (fun i : ↥K' => δ (c i)) hJne
    rw [Finset.mem_filter] at hi₀mem
    have hpi₀ : dist p (c i₀) < δ (c i₀) / 2 := by
      have := hhsupp i₀ p hi₀mem.2; simpa [ρ] using this
    -- for each active `i`: `y i` is within `ε/2` of `F (c i₀)`
    have hactive : ∀ i : ↥K', h i p ≠ 0 →
        ∃ q ∈ F (c i₀), dist (y i) q < ε / 2 := by
      intro i hi
      have hdist_pci : dist p (c i) < δ (c i) / 2 := by
        have := hhsupp i p hi; simpa [ρ] using this
      have hδi_le : δ (c i) ≤ δ (c i₀) :=
        hi₀max i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
      have hcici₀ : dist (c i) (c i₀) < δ (c i₀) := by
        calc dist (c i) (c i₀) ≤ dist (c i) p + dist p (c i₀) := dist_triangle _ _ _
          _ < δ (c i) / 2 + δ (c i₀) / 2 := by
                rw [dist_comm (c i) p]; exact add_lt_add hdist_pci hpi₀
          _ ≤ δ (c i₀) := by linarith
      have hsub := (hδspec (c i₀) (hcK i₀)).2.2 (c i) (hcK i) hcici₀
      have : y i ∈ Metric.thickening (ε / 2) (F (c i₀)) := hsub (hymem i)
      exact Metric.mem_thickening_iff.mp this
    -- build the witness `cc i ∈ F (c i₀)`, near `y i` on active indices
    obtain ⟨qdef, hqdef⟩ := hynonempty i₀
    let cc : (↥K') → X := fun i =>
      if hi : h i p ≠ 0 then Classical.choose (hactive i hi) else qdef
    have hccmem : ∀ i, cc i ∈ F (c i₀) := by
      intro i
      by_cases hi : h i p ≠ 0
      · simp only [cc, dif_pos hi]; exact (Classical.choose_spec (hactive i hi)).1
      · simp only [cc, dif_neg hi]; exact hqdef
    have hccdist : ∀ i, h i p ≠ 0 → dist (y i) (cc i) ≤ ε / 2 := by
      intro i hi
      simp only [cc, dif_pos hi]
      exact le_of_lt (Classical.choose_spec (hactive i hi)).2
    refine ⟨c i₀, hcK i₀, ∑ i, h i p • cc i, ?_, ?_, ?_⟩
    · exact (hF.convex_values (hcK i₀)).sum_mem (fun i _ => hhnonneg i p) (hhsum p hp)
        (fun i _ => hccmem i)
    · exact le_of_lt (lt_of_lt_of_le hpi₀ (by have := (hδspec (c i₀) (hcK i₀)).2.1; linarith))
    · -- `dist (g p) (∑ h i p • cc i) ≤ ε/2 ≤ ε`
      have hbound : dist (g p) (∑ i, h i p • cc i) ≤ ε / 2 := by
        rw [dist_eq_norm]
        have hsub : g p - (∑ i, h i p • cc i) = ∑ i, h i p • (y i - cc i) := by
          simp only [g, smul_sub, Finset.sum_sub_distrib]
        rw [hsub]
        calc ‖∑ i, h i p • (y i - cc i)‖
            ≤ ∑ i, ‖h i p • (y i - cc i)‖ := norm_sum_le _ _
          _ = ∑ i, h i p * dist (y i) (cc i) := by
                refine Finset.sum_congr rfl (fun i _ => ?_)
                rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hhnonneg i p), dist_eq_norm]
          _ ≤ ∑ i, h i p * (ε / 2) := by
                refine Finset.sum_le_sum (fun i _ => ?_)
                by_cases hi : h i p ≠ 0
                · exact mul_le_mul_of_nonneg_left (hccdist i hi) (hhnonneg i p)
                · push_neg at hi; rw [hi]; simp
          _ = ε / 2 := by rw [← Finset.sum_mul, hhsum p hp, one_mul]
      exact le_trans hbound (by linarith)

/-- The continuous `ε`-approximate selection of a Kakutani correspondence (the data extracted
from `nonempty_approximateKakutaniSelection`). -/
noncomputable def KakutaniPremises.approximateKakutaniSelection
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [T2Space X]
    {K : Set X} {F : Correspondence X X} (hF : KakutaniPremises K F)
    {ε : ℝ} (hε : 0 < ε) :
    ApproximateKakutaniSelection K F ε :=
  (hF.nonempty_approximateKakutaniSelection hε).some

set_option maxHeartbeats 800000 in
/-- **Kakutani's fixed-point theorem on the standard simplex.**
Every correspondence on `stdSimplex ℝ (Fin (d+1))` (`2 ≤ d`) satisfying the Kakutani hypotheses
(nonempty/compact/convex values, closed graph, into the compact convex domain) has a fixed point.
Assembled from the simplex Brouwer property and the Cellina approximate selection. -/
theorem kakutaniFixedPointProperty_stdSimplex {d : ℕ} (hd : 2 ≤ d) :
    KakutaniFixedPointProperty (stdSimplex ℝ (Fin (d + 1))) := by
  -- supply `T2Space` explicitly: the generic search for `T2Space ℝ` is pathologically slow here
  haveI : T2Space (Fin (d + 1) → ℝ) :=
    @Pi.t2Space (Fin (d + 1)) (fun _ => ℝ) inferInstance fun _ => OrderClosedTopology.to_t2Space
  exact KakutaniFixedPointProperty.of_brouwer_approximateSelections
    (brouwerFixedPointProperty_stdSimplex hd)
    fun _F hF _n => hF.approximateKakutaniSelection (by positivity)

/-! ## Retraction transfer of the fixed-point property

A *continuous retraction* of `X` onto `K ⊆ S` (a global continuous `r : X → X` with `r x ∈ K`
for all `x` and `r = id` on `K`) transfers the Brouwer / Kakutani fixed-point property from `S`
to `K`.  This is the abstract backbone for realising a compact convex body as a retract of a
simplex.  Pure topology — no inner product or metric is needed here. -/

/-- **Brouwer transfer along a continuous retraction.**  If `S` has the Brouwer fixed-point
property and `r : X → X` is a continuous retraction onto `K ⊆ S`, then `K` has it too. -/
theorem BrouwerFixedPointProperty.of_retraction
    {X : Type*} [TopologicalSpace X] {S K : Set X}
    (hS : BrouwerFixedPointProperty S) (hKS : K ⊆ S)
    {r : X → X} (hrCont : Continuous r) (hrK : ∀ x, r x ∈ K)
    (hrid : ∀ x ∈ K, r x = x) :
    BrouwerFixedPointProperty K := by
  intro g hgMap hgCont
  -- The extended self-map `g ∘ r` of `S`.
  have hMapS : Set.MapsTo (fun x => g (r x)) S S :=
    fun x _ => hKS (hgMap (hrK x))
  have hContS : ContinuousOn (fun x => g (r x)) S :=
    hgCont.comp hrCont.continuousOn (fun x _ => hrK x)
  obtain ⟨s, _, hsFix⟩ := hS _ hMapS hContS
  -- `s = g (r s) ∈ K`, hence `r s = s` and `g s = s`.
  have hsK : s ∈ K := by rw [← hsFix]; exact hgMap (hrK s)
  refine ⟨s, hsK, ?_⟩
  rwa [hrid s hsK] at hsFix

/-- **Kakutani transfer along a continuous retraction.**  If `S` (compact, convex, closed) has the
Kakutani fixed-point property and `r : X → X` is a continuous retraction onto `K ⊆ S`, then `K` has
the Kakutani fixed-point property.  The pulled-back correspondence `G x := F (r x)` inherits all the
Kakutani premises on `S`; its closed graph is the intersection of two closed sets via continuity of
`r`. -/
theorem KakutaniFixedPointProperty.of_retraction
    {X : Type*} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X] {S K : Set X}
    (hS : KakutaniFixedPointProperty S)
    (hScompact : IsCompact S) (hSconvex : Convex ℝ S) (hSclosed : IsClosed S)
    (hKS : K ⊆ S)
    {r : X → X} (hrCont : Continuous r) (hrK : ∀ x, r x ∈ K)
    (hrid : ∀ x ∈ K, r x = x) :
    KakutaniFixedPointProperty K := by
  intro F hF
  set G : Correspondence X X := fun x => F (r x) with hGdef
  -- The pulled-back correspondence satisfies the Kakutani premises on `S`.
  have hGprem : KakutaniPremises S G := by
    refine
      { compact_domain := hScompact
        convex_domain := hSconvex
        nonempty_domain := hF.nonempty_domain.mono hKS
        mapsTo_domain := fun x _ => (hF.mapsTo_domain (hrK x)).trans hKS
        nonempty_values := fun x _ => hF.nonempty_values (hrK x)
        compact_values := fun x _ => hF.compact_values (hrK x)
        convex_values := fun x _ => hF.convex_values (hrK x)
        closed_graph := ?_ }
    -- `graphOn G S = (fst ⁻¹' S) ∩ (Ψ ⁻¹' graphOn F K)` with `Ψ p = (r p.1, p.2)` continuous.
    have hΨ : Continuous (fun p : X × X => (r p.1, p.2)) :=
      (hrCont.comp continuous_fst).prodMk continuous_snd
    have hEq : graphOn G S =
        (Prod.fst ⁻¹' S) ∩ ((fun p : X × X => (r p.1, p.2)) ⁻¹' graphOn F K) := by
      ext p
      simp only [graphOn, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, hrK p.1, h2⟩
      · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
    show IsClosed (graphOn G S)
    rw [hEq]
    exact (hSclosed.preimage continuous_fst).inter (hF.closed_graph.preimage hΨ)
  -- Pull the fixed point of `G` on `S` back to `K`.
  obtain ⟨s, _, hsG⟩ := hS G hGprem
  have hsG' : s ∈ F (r s) := hsG
  have hsK : s ∈ K := (hF.mapsTo_domain (hrK s)) hsG'
  refine ⟨s, hsK, ?_⟩
  rwa [hrid s hsK] at hsG'

/-! ## The metric-projection retraction onto a compact convex set

In a real inner product space, a nonempty compact convex `K` admits a continuous (1-Lipschitz)
retraction onto `K`: the nearest-point (metric) projection.  Existence of the nearest point is the
Hilbert projection theorem (`exists_norm_eq_iInf_of_complete_convex`, using `IsCompact ⇒ IsComplete`);
the projection fixes `K` and is nonexpansive by the variational inequality
`norm_eq_iInf_iff_real_inner_le_zero`. -/

open scoped RealInnerProductSpace in
/-- A nonempty compact convex set in a real inner product space is a retract of the whole space via a
continuous (1-Lipschitz) map — the nearest-point projection.  Returns the retraction `r` with
`Continuous r`, `r x ∈ K` for all `x`, and `r = id` on `K`. -/
theorem exists_continuous_retraction_of_isCompact_convex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} (hne : K.Nonempty) (hcomp : IsCompact K) (hconv : Convex ℝ K) :
    ∃ r : E → E, Continuous r ∧ (∀ x, r x ∈ K) ∧ (∀ x ∈ K, r x = x) := by
  classical
  have hcomplete : IsComplete K := hcomp.isComplete
  -- the nearest-point projection
  let proj : E → E := fun u =>
    Classical.choose (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconv u)
  have hmem : ∀ u, proj u ∈ K := fun u =>
    (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconv u)).1
  have hspec : ∀ u, ‖u - proj u‖ = ⨅ w : K, ‖u - w‖ := fun u =>
    (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconv u)).2
  -- the variational inequality characterising the projection
  have hvar : ∀ u, ∀ w ∈ K, ⟪u - proj u, w - proj u⟫ ≤ 0 := fun u =>
    (norm_eq_iInf_iff_real_inner_le_zero hconv (hmem u)).mp (hspec u)
  -- nonexpansiveness from two variational inequalities
  have hlip : LipschitzWith 1 proj := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro u₁ u₂
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    have hvar1 : ⟪u₁ - proj u₁, proj u₂ - proj u₁⟫ ≤ 0 := hvar u₁ (proj u₂) (hmem u₂)
    have hvar2 : ⟪u₂ - proj u₂, proj u₁ - proj u₂⟫ ≤ 0 := hvar u₂ (proj u₁) (hmem u₁)
    have hident :
        ⟪u₁ - proj u₁, proj u₂ - proj u₁⟫ + ⟪u₂ - proj u₂, proj u₁ - proj u₂⟫
          = ⟪proj u₁ - proj u₂, proj u₁ - proj u₂⟫ - ⟪u₁ - u₂, proj u₁ - proj u₂⟫ := by
      simp only [inner_sub_left, inner_sub_right]; ring
    have hkey : ⟪proj u₁ - proj u₂, proj u₁ - proj u₂⟫ ≤ ⟪u₁ - u₂, proj u₁ - proj u₂⟫ := by
      linarith
    rw [real_inner_self_eq_norm_mul_norm] at hkey
    have hcs : ⟪u₁ - u₂, proj u₁ - proj u₂⟫ ≤ ‖u₁ - u₂‖ * ‖proj u₁ - proj u₂‖ :=
      real_inner_le_norm _ _
    have hfin : ‖proj u₁ - proj u₂‖ * ‖proj u₁ - proj u₂‖
        ≤ ‖u₁ - u₂‖ * ‖proj u₁ - proj u₂‖ := le_trans hkey hcs
    rcases eq_or_lt_of_le (norm_nonneg (proj u₁ - proj u₂)) with h | h
    · rw [← h]; exact norm_nonneg _
    · exact le_of_mul_le_mul_right hfin h
  refine ⟨proj, hlip.continuous, hmem, ?_⟩
  -- the projection fixes `K`: the variational inequality at `w = x` forces `‖x - proj x‖ = 0`
  intro x hx
  have h0 : ⟪x - proj x, x - proj x⟫ ≤ 0 := hvar x x hx
  rw [real_inner_self_eq_norm_mul_norm] at h0
  have hz : ‖x - proj x‖ = 0 :=
    mul_self_eq_zero.mp (le_antisymm h0 (mul_self_nonneg _))
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

/-- **Subset inheritance of the Kakutani fixed-point property.**  In a real inner
product space, any nonempty compact convex set `K` contained in a compact convex closed set `S` that
has the Kakutani fixed-point property inherits it: retract `S` onto `K` by the metric projection and
transfer the property along the retraction.  This isolates all the geometry of "containing simplex"
into the choice of `S`. -/
theorem KakutaniFixedPointProperty.of_subset_of_isCompact_convex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S K : Set E}
    (hS : KakutaniFixedPointProperty S)
    (hScomp : IsCompact S) (hSconv : Convex ℝ S) (hSclosed : IsClosed S)
    (hKS : K ⊆ S)
    (hne : K.Nonempty) (hcomp : IsCompact K) (hconv : Convex ℝ K) :
    KakutaniFixedPointProperty K := by
  obtain ⟨r, hrc, hrK, hrid⟩ := exists_continuous_retraction_of_isCompact_convex hne hcomp hconv
  exact hS.of_retraction hScomp hSconv hSclosed hKS hrc hrK hrid

/-- **Retraction via a continuous linear equivalence to an inner product space.**
A topological `ℝ`-vector space `X` need not carry an inner product, but if it is `ℝ`-linearly
homeomorphic (`X ≃L[ℝ] E`) to an inner product space `E`, then a nonempty compact convex `K ⊆ X`
still admits a continuous retraction: transport `K` to `E`, project there, and pull the projected
point back through the equivalence.  This lets the metric projection be used in the Pi (sup-norm)
coordinate space of a simplex grid, which has no native inner product. -/
theorem exists_continuous_retraction_of_cle
    {X E : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (T : X ≃L[ℝ] E)
    {K : Set X} (hne : K.Nonempty) (hcomp : IsCompact K) (hconv : Convex ℝ K) :
    ∃ r : X → X, Continuous r ∧ (∀ x, r x ∈ K) ∧ (∀ x ∈ K, r x = x) := by
  obtain ⟨projE, hprojCont, hprojMem, hprojFix⟩ :=
    exists_continuous_retraction_of_isCompact_convex (K := T '' K)
      (hne.image _) (hcomp.image T.continuous)
      (hconv.linear_image (T : X →L[ℝ] E).toLinearMap)
  refine ⟨fun x => T.symm (projE (T x)),
    T.symm.continuous.comp (hprojCont.comp T.continuous), ?_, ?_⟩
  · intro x
    show T.symm (projE (T x)) ∈ K
    obtain ⟨k, hk, hkE⟩ := hprojMem (T x)
    rw [← hkE, T.symm_apply_apply]; exact hk
  · intro x hx
    show T.symm (projE (T x)) = x
    rw [hprojFix (T x) ⟨x, hx, rfl⟩, T.symm_apply_apply]

/-- **Subset inheritance through a linear homeomorphism.**  As `of_subset_of_isCompact_convex`,
but `X` only needs a continuous linear equivalence `T : X ≃L[ℝ] E` to an inner product space (not a
native inner product).  Any nonempty compact convex `K` contained in a compact convex closed `S`
with the Kakutani fixed-point property inherits it. -/
theorem KakutaniFixedPointProperty.of_subset_cle
    {X E : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (T : X ≃L[ℝ] E)
    {S K : Set X}
    (hS : KakutaniFixedPointProperty S)
    (hScomp : IsCompact S) (hSconv : Convex ℝ S) (hSclosed : IsClosed S)
    (hKS : K ⊆ S) (hne : K.Nonempty) (hcomp : IsCompact K) (hconv : Convex ℝ K) :
    KakutaniFixedPointProperty K := by
  obtain ⟨r, hrc, hrK, hrid⟩ := exists_continuous_retraction_of_cle T hne hcomp hconv
  exact hS.of_retraction hScomp hSconv hSclosed hKS hrc hrK hrid

/-- **The Kakutani fixed-point property of a compact convex subset of the standard simplex.**
The simplex itself has the property (`kakutaniFixedPointProperty_stdSimplex`, `2 ≤ n`), it is
compact, convex and closed, and `Fin (n+1) → ℝ` is linearly homeomorphic to
`EuclideanSpace ℝ (Fin (n+1))`; so any nonempty compact convex `K ⊆ stdSimplex` inherits the
property by the metric-projection retraction. -/
theorem kakutaniFixedPointProperty_of_subset_stdSimplex
    {n : ℕ} (hn : 2 ≤ n)
    {K : Set (Fin (n + 1) → ℝ)} (hKS : K ⊆ stdSimplex ℝ (Fin (n + 1)))
    (hne : K.Nonempty) (hcomp : IsCompact K) (hconv : Convex ℝ K) :
    KakutaniFixedPointProperty K :=
  (kakutaniFixedPointProperty_stdSimplex hn).of_subset_cle
    (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
    (isCompact_stdSimplex ℝ (Fin (n + 1))) (convex_stdSimplex ℝ (Fin (n + 1)))
    (isClosed_stdSimplex ℝ (Fin (n + 1))) hKS hne hcomp hconv

/-! ## Affine-section transfer across a dimension gap

`image_continuousAffineEquiv` transfers the Kakutani property along an *ambient* affine equivalence,
which forces the two spaces to have the same dimension.  To realise a general compact convex body in
`ℝⁿ` as a retract of a simplex we must cross a dimension gap (`ℝⁿ⁺¹ → ℝⁿ`).  The tool is a pair of
affine maps `φ : E → F`, `ψ : F → E` that form a section *on the relevant sets* (`φ ∘ ψ = id` on `K`),
not a global equivalence. -/

/-- **Affine-section transfer of the Kakutani fixed-point property.**  If `S` (compact, convex,
closed) has the property and continuous affine maps `φ : E → F`, `ψ : F → E` satisfy `φ '' S ⊆ K`,
`ψ '' K ⊆ S`, and `φ (ψ x) = x` on `K`, then `K` has the property.  Pull a Kakutani correspondence
`F` on `K` back to `G y = ψ '' F (φ y)` on `S`: the values are convex/compact (affine/continuous
images) and the graph is closed because it is a continuous image of the compact set
`{(y, z) : y ∈ S, z ∈ F (φ y)} ⊆ S ×ˢ K`.  (`T2Space` is taken as an explicit binder: re-deriving it
from `NormedSpace ℝ` in-proof triggers a pathologically slow instance search.) -/
theorem KakutaniFixedPointProperty.of_affine_section
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [T2Space E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [T2Space F]
    {S : Set E} {K : Set F}
    (hS : KakutaniFixedPointProperty S)
    (hScompact : IsCompact S) (hSconvex : Convex ℝ S) (hSclosed : IsClosed S)
    (φ : E →ᵃ[ℝ] F) (hφc : Continuous φ) (hφS : Set.MapsTo φ S K)
    (ψ : F →ᵃ[ℝ] E) (hψc : Continuous ψ) (hψK : Set.MapsTo ψ K S)
    (hφψ : ∀ x ∈ K, φ (ψ x) = x) :
    KakutaniFixedPointProperty K := by
  intro Fc hF
  set G : Correspondence E E := fun y => ψ '' Fc (φ y) with hGdef
  have hGprem : KakutaniPremises S G := by
    refine
      { compact_domain := hScompact
        convex_domain := hSconvex
        nonempty_domain := ?_
        mapsTo_domain := ?_
        nonempty_values := ?_
        compact_values := ?_
        convex_values := ?_
        closed_graph := ?_ }
    · obtain ⟨x, hx⟩ := hF.nonempty_domain; exact ⟨ψ x, hψK hx⟩
    · intro y hy z hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact hψK (hF.mapsTo_domain (hφS hy) hw)
    · intro y hy; exact (hF.nonempty_values (hφS hy)).image ψ
    · intro y hy; exact (hF.compact_values (hφS hy)).image hψc
    · intro y hy; exact (hF.convex_values (hφS hy)).affine_image ψ
    · have hcont : Continuous (fun p : E × F => (φ p.1, p.2)) :=
        (hφc.comp continuous_fst).prodMk continuous_snd
      have hΓclosed : IsClosed {p : E × F | p.1 ∈ S ∧ p.2 ∈ Fc (φ p.1)} := by
        have heq : {p : E × F | p.1 ∈ S ∧ p.2 ∈ Fc (φ p.1)}
            = (Prod.fst ⁻¹' S) ∩ ((fun p : E × F => (φ p.1, p.2)) ⁻¹' graphOn Fc K) := by
          ext p
          simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, mem_graphOn_iff]
          exact ⟨fun ⟨h1, h2⟩ => ⟨h1, hφS h1, h2⟩, fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩⟩
        rw [heq]
        exact (hSclosed.preimage continuous_fst).inter (hF.closed_graph.preimage hcont)
      have hΓsub : {p : E × F | p.1 ∈ S ∧ p.2 ∈ Fc (φ p.1)} ⊆ S ×ˢ K := by
        rintro ⟨y, z⟩ ⟨hy, hz⟩; exact ⟨hy, hF.mapsTo_domain (hφS hy) hz⟩
      have hΓcompact : IsCompact {p : E × F | p.1 ∈ S ∧ p.2 ∈ Fc (φ p.1)} :=
        (hScompact.prod hF.compact_domain).of_isClosed_subset hΓclosed hΓsub
      have hgeq : graphOn G S
          = (fun p : E × F => (p.1, ψ p.2)) '' {p : E × F | p.1 ∈ S ∧ p.2 ∈ Fc (φ p.1)} := by
        ext p
        obtain ⟨y, w⟩ := p
        simp only [graphOn, hGdef, Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq]
        constructor
        · rintro ⟨hy, z, hz, rfl⟩; exact ⟨(y, z), ⟨hy, hz⟩, rfl, rfl⟩
        · rintro ⟨⟨y', z⟩, ⟨hy', hz⟩, rfl, rfl⟩; exact ⟨hy', z, hz, rfl⟩
      show IsClosed (graphOn G S)
      rw [hgeq]
      exact (hΓcompact.image (continuous_fst.prodMk (hψc.comp continuous_snd))).isClosed
  obtain ⟨y, hyS, hyG⟩ := hS G hGprem
  obtain ⟨z, hz, hzeq⟩ := hyG
  have hzK : z ∈ K := hF.mapsTo_domain (hφS hyS) hz
  have hφy : φ y = z := by rw [← hzeq]; exact hφψ z hzK
  refine ⟨φ y, hφS hyS, ?_⟩
  rw [hφy] at hz ⊢
  exact hz

/-! ## The corner simplex

The "corner" simplex `Δ⁺ = {x ≥ 0, ∑ x ≤ T} ⊆ Fin n → ℝ` is a *full-dimensional* `n`-simplex; the
standard `n`-simplex `stdSimplex ℝ (Fin (n+1))` is its `(n)`-dimensional copy in `Fin (n+1) → ℝ`.  The
affine maps `cornerDrop` (drop the last coordinate, scale by `T`) and `cornerLift` (append the slack
`1 − (∑x)/T`, scale by `1/T`) form a section pair, so `of_affine_section` transfers the FPP. -/

section CornerSimplex

/-- The corner simplex `{x ≥ 0, ∑ x ≤ T}` in `Fin n → ℝ`. -/
def cornerSimplex (n : ℕ) (T : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ T}

/-- Drop the last coordinate and scale by `T` (a linear map). -/
noncomputable def cornerDrop (n : ℕ) (T : ℝ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun y i := T * y i.castSucc
  map_add' y z := by funext i; simp [Pi.add_apply, mul_add]
  map_smul' c y := by funext i; simp [Pi.smul_apply]; ring

/-- The linear part of the lift: append the slack `−(∑x)/T`, scale by `1/T`. -/
noncomputable def cornerLiftLinear (n : ℕ) (T : ℝ) : (Fin n → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun x := Fin.snoc (fun j => x j / T) (-(∑ j, x j) / T)
  map_add' x y := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, Pi.add_apply]
      rw [show ∑ j, (x j + y j) = (∑ j, x j) + ∑ j, y j from Finset.sum_add_distrib]; ring
    · simp only [Fin.snoc_castSucc, Pi.add_apply]; ring
  map_smul' c x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [show ∑ j, c * x j = c * ∑ j, x j from by rw [Finset.mul_sum]]; ring
    · simp only [Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Append the slack coordinate `1 − (∑x)/T`, scale by `1/T` (an affine map). -/
noncomputable def cornerLift (n : ℕ) (T : ℝ) : (Fin n → ℝ) →ᵃ[ℝ] (Fin (n + 1) → ℝ) where
  toFun x := Fin.snoc (fun j => x j / T) (1 - (∑ j, x j) / T)
  linear := cornerLiftLinear n T
  map_vadd' p v := by
    funext i
    simp only [vadd_eq_add, Pi.add_apply, cornerLiftLinear, LinearMap.coe_mk, AddHom.coe_mk]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      rw [show ∑ j, (v j + p j) = (∑ j, v j) + ∑ j, p j from Finset.sum_add_distrib]; ring
    · simp only [Fin.snoc_castSucc]; ring

@[simp] lemma cornerDrop_apply (n : ℕ) (T : ℝ) (y : Fin (n + 1) → ℝ) (i : Fin n) :
    (cornerDrop n T).toAffineMap y i = T * y i.castSucc := rfl

@[simp] lemma cornerLift_last (n : ℕ) (T : ℝ) (x : Fin n → ℝ) :
    cornerLift n T x (Fin.last n) = 1 - (∑ j, x j) / T := by
  simp only [cornerLift, AffineMap.coe_mk, Fin.snoc_last]

@[simp] lemma cornerLift_castSucc (n : ℕ) (T : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    cornerLift n T x i.castSucc = x i / T := by
  simp only [cornerLift, AffineMap.coe_mk, Fin.snoc_castSucc]

/-- **The corner simplex has the Kakutani fixed-point property** (`2 ≤ n`, `0 < T`).
Transferred from `stdSimplex ℝ (Fin (n+1))` along the section pair `cornerDrop` / `cornerLift`. -/
theorem kakutaniFixedPointProperty_cornerSimplex {n : ℕ} (hn : 2 ≤ n) {T : ℝ} (hT : 0 < T) :
    KakutaniFixedPointProperty (cornerSimplex n T) := by
  haveI : T2Space (Fin (n + 1) → ℝ) :=
    @Pi.t2Space (Fin (n + 1)) (fun _ => ℝ) inferInstance fun _ => OrderClosedTopology.to_t2Space
  haveI : T2Space (Fin n → ℝ) :=
    @Pi.t2Space (Fin n) (fun _ => ℝ) inferInstance fun _ => OrderClosedTopology.to_t2Space
  refine (kakutaniFixedPointProperty_stdSimplex hn).of_affine_section
    (isCompact_stdSimplex ℝ (Fin (n + 1))) (convex_stdSimplex ℝ (Fin (n + 1)))
    (isClosed_stdSimplex ℝ (Fin (n + 1)))
    (cornerDrop n T).toAffineMap (AffineMap.continuous_of_finiteDimensional _) ?_
    (cornerLift n T) (AffineMap.continuous_of_finiteDimensional _) ?_ ?_
  · -- `cornerDrop` maps the standard simplex into the corner simplex
    intro y hy
    refine ⟨fun i => ?_, ?_⟩
    · rw [cornerDrop_apply]; exact mul_nonneg hT.le (hy.1 _)
    · have hsum : ∑ i : Fin n, y i.castSucc = 1 - y (Fin.last n) := by
        have h := Fin.sum_univ_castSucc (fun i => y i)
        rw [hy.2] at h; linarith
      simp only [cornerDrop_apply]
      rw [← Finset.mul_sum, hsum]
      nlinarith [hy.1 (Fin.last n)]
  · -- `cornerLift` maps the corner simplex into the standard simplex
    intro x hx
    refine ⟨fun i => ?_, ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [cornerLift_last, sub_nonneg, div_le_one hT]; exact hx.2
      · rw [cornerLift_castSucc]; exact div_nonneg (hx.1 j) hT.le
    · rw [Fin.sum_univ_castSucc]
      simp only [cornerLift_castSucc, cornerLift_last]
      rw [← Finset.sum_div]; ring
  · -- `cornerDrop ∘ cornerLift = id` on the corner simplex
    intro x _
    funext i
    rw [cornerDrop_apply, cornerLift_castSucc]
    field_simp

lemma cornerSimplex_convex (n : ℕ) (T : ℝ) : Convex ℝ (cornerSimplex n T) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc ∑ i, (a * x i + b * y i)
        = a * ∑ i, x i + b * ∑ i, y i := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ a * T + b * T :=
          add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = T := by rw [← add_mul, hab, one_mul]

lemma cornerSimplex_isClosed (n : ℕ) (T : ℝ) : IsClosed (cornerSimplex n T) := by
  have hEq : cornerSimplex n T
      = (⋂ i, {x : Fin n → ℝ | 0 ≤ x i}) ∩ {x | ∑ i, x i ≤ T} := by
    ext x; simp only [cornerSimplex, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hEq]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const)

lemma cornerSimplex_isCompact (n : ℕ) (T : ℝ) : IsCompact (cornerSimplex n T) :=
  (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => T)).of_isClosed_subset
    (cornerSimplex_isClosed n T) fun x hx => Set.mem_Icc.mpr
      ⟨fun i => hx.1 i, fun i => le_trans
        (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)) hx.2⟩

/-- **Every nonempty compact convex body in `Fin n → ℝ` has the Kakutani fixed-point property**
(`2 ≤ n`).  The body is bounded, so a translate sits inside a corner simplex `Δ⁺`; subset-inheritance
gives the property for the translate, and the translation is an affine equivalence, so it transfers
back.  A product of simplices is one such body, so this is the geometric input to the general Nash
existence theorem. -/
theorem kakutaniFixedPointProperty_of_isCompact_convex {n : ℕ} (hn : 2 ≤ n)
    {K : Set (Fin n → ℝ)} (hKne : K.Nonempty) (hKcomp : IsCompact K) (hKconv : Convex ℝ K) :
    KakutaniFixedPointProperty K := by
  -- a norm bound on `K`
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hKcomp.isBounded
  have hR₀pos : 0 ≤ R₀ := le_trans dist_nonneg
    (by have := hR₀ hKne.choose_spec; rwa [Metric.mem_closedBall] at this)
  set R : ℝ := R₀ + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  set T : ℝ := 2 * R * n with hTdef
  have hTpos : 0 < T := by rw [hTdef]; positivity
  set v : Fin n → ℝ := fun _ => R with hvdef
  -- coordinatewise bound on `K`
  have hbound : ∀ x ∈ K, ∀ i, |x i| ≤ R₀ := fun x hx i => by
    have hx' : ‖x‖ ≤ R₀ := by have := hR₀ hx; rwa [Metric.mem_closedBall, dist_zero_right] at this
    calc |x i| = ‖x i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x‖ := norm_le_pi_norm x i
      _ ≤ R₀ := hx'
  -- the translation equivalence
  set e : (Fin n → ℝ) ≃ᴬ[ℝ] (Fin n → ℝ) := ContinuousAffineEquiv.constVAdd ℝ (Fin n → ℝ) v with hedef
  have hecoe : ∀ x, e x = v + x := fun x => by rw [hedef]; rfl
  -- the translate of `K` lands in the corner simplex
  have hKS : e '' K ⊆ cornerSimplex n T := by
    rintro y ⟨x, hx, rfl⟩
    have hb := fun i => abs_le.mp (hbound x hx i)
    rw [hecoe]
    have hsum_eq : (∑ _i : Fin n, (2 * R)) = T := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hTdef]; ring
    refine ⟨fun i => ?_, ?_⟩
    · have := (hb i).1; simp only [Pi.add_apply, hvdef]; linarith
    · refine le_trans (Finset.sum_le_sum fun i _ => ?_) (le_of_eq hsum_eq)
      have := (hb i).2; simp only [Pi.add_apply, hvdef]; linarith
  -- transfer the FPP to the translate (corner simplex superset), then back along `e`
  have hFPPtrans : KakutaniFixedPointProperty (e '' K) :=
    (kakutaniFixedPointProperty_cornerSimplex hn hTpos).of_subset_cle
      (EuclideanSpace.equiv (Fin n) ℝ).symm
      (cornerSimplex_isCompact n T) (cornerSimplex_convex n T) (cornerSimplex_isClosed n T)
      hKS (hKne.image _) (hKcomp.image e.continuous)
      (hKconv.affine_image e.toAffineEquiv.toAffineMap)
  exact (kakutaniFixedPointProperty_image_continuousAffineEquiv_iff e K).mp hFPPtrans

/-- **Kakutani fixed-point property for a compact convex body in a finite-dimensional space.**
Every nonempty compact convex body `K` in a finite-dimensional real normed space `E` with
`2 ≤ finrank E` has the Kakutani fixed-point property: pick a basis to get `E ≃L (Fin (finrank E) → ℝ)`,
push `K` over, apply the coordinate-space result, and pull the property back along the equivalence. -/
theorem kakutaniFixedPointProperty_of_isCompact_convex_finrank
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [T2Space E]
    (hdim : 2 ≤ Module.finrank ℝ E)
    {K : Set E} (hKne : K.Nonempty) (hKcomp : IsCompact K) (hKconv : Convex ℝ K) :
    KakutaniFixedPointProperty K := by
  haveI : T2Space (Fin (Module.finrank ℝ E) → ℝ) :=
    @Pi.t2Space _ _ inferInstance fun _ => OrderClosedTopology.to_t2Space
  let T : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    { (Module.finBasis ℝ E).equivFun with
      continuous_toFun := ((Module.finBasis ℝ E).equivFun.toLinearMap).continuous_of_finiteDimensional
      continuous_invFun :=
        ((Module.finBasis ℝ E).equivFun.symm.toLinearMap).continuous_of_finiteDimensional }
  have hbody : KakutaniFixedPointProperty (T '' K) :=
    kakutaniFixedPointProperty_of_isCompact_convex hdim (hKne.image _)
      (hKcomp.image T.continuous)
      (hKconv.is_linear_image (⟨T.map_add, T.map_smul⟩ : IsLinearMap ℝ ⇑T))
  exact (kakutaniFixedPointProperty_image_continuousAffineEquiv_iff
    T.toContinuousAffineEquiv K).mp hbody

end CornerSimplex

/-! ## The Kakutani property for a product of simplices

Nash's strategy space is a *product* of simplices `K = ∏ᵢ Δ^{aᵢ-1}`, which is not a single simplex.
We flatten it into one big simplex: the coordinate space `∀ i, Fin (aᵢ) → ℝ` is linearly homeomorphic
(via a manual reindexing `(Σ i, Fin aᵢ) ≃ Fin (∑ aᵢ)`, with a `1/|players|` rescale folded in) to
`Fin (M+1) → ℝ`, carrying the product of simplices *into the unit standard simplex*.  The
compact-convex-body result then applies, and `image_continuousAffineEquiv` transfers the property
back to the product. -/

section ProductSimplex

variable {ι : Type*} [Fintype ι] {a : ι → ℕ} {m : ℕ}

/-- Flatten `∀ i, Fin (aᵢ) → ℝ` into `Fin (m+1) → ℝ` (reindexing the disjoint union of coordinates
along `eσ : (Σ i, Fin aᵢ) ≃ Fin (m+1)`) and rescale by `c⁻¹`.  A linear equivalence; with `c = the
total block sum`, it maps the product of simplices into the unit simplex. -/
noncomputable def flattenScaleEquiv (eσ : (Σ i, Fin (a i)) ≃ Fin (m + 1)) (c : ℝ) (hc : c ≠ 0) :
    (∀ i, Fin (a i) → ℝ) ≃ₗ[ℝ] (Fin (m + 1) → ℝ) where
  toFun x := fun j => c⁻¹ * x (eσ.symm j).1 (eσ.symm j).2
  invFun y := fun i k => c * y (eσ ⟨i, k⟩)
  map_add' x y := by funext j; simp only [Pi.add_apply, mul_add]
  map_smul' r x := by
    funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
  left_inv x := by
    funext i k
    simp only [mul_inv_cancel_left₀ hc]
    rw [Equiv.symm_apply_apply]
  right_inv y := by
    funext j
    simp only [inv_mul_cancel_left₀ hc]
    rw [show (⟨(eσ.symm j).1, (eσ.symm j).2⟩ : Σ i, Fin (a i)) = eσ.symm j from rfl,
      Equiv.apply_symm_apply]

set_option maxHeartbeats 1000000 in
/-- **The Kakutani fixed-point property for a product of standard simplices.**
For players `ι` (finite, nonempty) with action counts `a i > 0` whose total `∑ a i = m + 1` with
`2 ≤ m`, the product strategy space `∏ᵢ stdSimplex ℝ (Fin aᵢ)` has the Kakutani fixed-point property.
The flatten+scale equivalence carries it into the unit simplex `stdSimplex ℝ (Fin (m+1))`, where the
compact-convex-body result applies; `image_continuousAffineEquiv` transfers the property back. -/
theorem kakutaniFixedPointProperty_pi_stdSimplex
    [Nonempty ι] (hm : 2 ≤ m) (hcard : ∑ i, a i = m + 1) (ha : ∀ i, 0 < a i) :
    KakutaniFixedPointProperty
      (Set.univ.pi (fun i => stdSimplex ℝ (Fin (a i))) : Set (∀ i, Fin (a i) → ℝ)) := by
  classical
  -- supply the (otherwise pathologically slow) `T2Space` instances explicitly
  haveI : ∀ i : ι, T2Space (Fin (a i) → ℝ) := fun i =>
    @Pi.t2Space (Fin (a i)) (fun _ => ℝ) inferInstance fun _ => OrderClosedTopology.to_t2Space
  haveI : T2Space ((i : ι) → Fin (a i) → ℝ) :=
    @Pi.t2Space ι (fun i => Fin (a i) → ℝ) inferInstance fun _ => inferInstance
  haveI : T2Space (Fin (m + 1) → ℝ) :=
    @Pi.t2Space (Fin (m + 1)) (fun _ => ℝ) inferInstance fun _ => OrderClosedTopology.to_t2Space
  -- the cardinality reindexing `(Σ i, Fin aᵢ) ≃ Fin (m+1)`
  have hcardσ : Fintype.card ((i : ι) × Fin (a i)) = m + 1 := by
    rw [Fintype.card_sigma]; simpa using hcard
  let eσ : ((i : ι) × Fin (a i)) ≃ Fin (m + 1) := Fintype.equivFinOfCardEq hcardσ
  -- the rescaling factor: the number of simplex blocks
  set c : ℝ := (Fintype.card ι : ℝ) with hcdef
  have hc : c ≠ 0 := by rw [hcdef]; exact_mod_cast Fintype.card_pos.ne'
  -- flatten+scale as a continuous linear equivalence (finite dimensions ⇒ continuous)
  let Ecle : (∀ i, Fin (a i) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ) :=
    { flattenScaleEquiv eσ c hc with
      continuous_toFun :=
        (flattenScaleEquiv eσ c hc).toLinearMap.continuous_of_finiteDimensional
      continuous_invFun :=
        (flattenScaleEquiv eσ c hc).symm.toLinearMap.continuous_of_finiteDimensional }
  let Ecae : (∀ i, Fin (a i) → ℝ) ≃ᴬ[ℝ] (Fin (m + 1) → ℝ) := Ecle.toContinuousAffineEquiv
  set K : Set (∀ i, Fin (a i) → ℝ) := Set.univ.pi (fun i => stdSimplex ℝ (Fin (a i))) with hKdef
  -- value of the flattening on a point (definitional)
  have hval : ∀ (x : ∀ i, Fin (a i) → ℝ) (j : Fin (m + 1)),
      Ecle x j = c⁻¹ * x (eσ.symm j).1 (eσ.symm j).2 := fun x j => rfl
  -- the product is nonempty / compact / convex
  have hKne : K.Nonempty := by
    rw [hKdef, Set.univ_pi_nonempty_iff]
    exact fun i => ⟨_, single_mem_stdSimplex ℝ ⟨0, ha i⟩⟩
  have hKcomp : IsCompact K := by
    rw [hKdef]; exact isCompact_univ_pi fun i => isCompact_stdSimplex ℝ (Fin (a i))
  have hKconv : Convex ℝ K := by
    rw [hKdef]; exact convex_pi fun i _ => convex_stdSimplex ℝ (Fin (a i))
  -- the flattened product lands in the unit simplex
  have hsub : Ecle '' K ⊆ stdSimplex ℝ (Fin (m + 1)) := by
    rintro y ⟨x, hx, rfl⟩
    rw [hKdef, Set.mem_univ_pi] at hx
    refine ⟨fun j => ?_, ?_⟩
    · rw [hval]
      exact mul_nonneg (inv_nonneg.mpr (by positivity)) ((hx (eσ.symm j).1).1 (eσ.symm j).2)
    · have hreindex : (∑ j, x (eσ.symm j).1 (eσ.symm j).2)
          = ∑ p : (i : ι) × Fin (a i), x p.1 p.2 :=
        Equiv.sum_comp eσ.symm (fun p => x p.1 p.2)
      have hsigma : (∑ p : (i : ι) × Fin (a i), x p.1 p.2) = ∑ i, ∑ k, x i k := by
        rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
      have hblocks : (∑ i, ∑ k, x i k) = c := by
        rw [hcdef, show (∑ i, ∑ k, x i k) = ∑ _i : ι, (1 : ℝ) from
            Finset.sum_congr rfl fun i _ => (hx i).2,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      calc (∑ j, Ecle x j)
          = ∑ j, c⁻¹ * x (eσ.symm j).1 (eσ.symm j).2 := by simp only [hval]
        _ = c⁻¹ * ∑ j, x (eσ.symm j).1 (eσ.symm j).2 := by rw [Finset.mul_sum]
        _ = c⁻¹ * ∑ i, ∑ k, x i k := by rw [hreindex, hsigma]
        _ = c⁻¹ * c := by rw [hblocks]
        _ = 1 := inv_mul_cancel₀ hc
  -- the flattened product inherits the Kakutani property (subset of the standard simplex)
  have hImg : KakutaniFixedPointProperty (Ecle '' K) :=
    kakutaniFixedPointProperty_of_subset_stdSimplex hm hsub
      (hKne.image _) (hKcomp.image Ecle.continuous)
      (hKconv.is_linear_image (⟨Ecle.map_add, Ecle.map_smul⟩ : IsLinearMap ℝ ⇑Ecle))
  -- transport back along the flattening
  exact (kakutaniFixedPointProperty_image_continuousAffineEquiv_iff Ecae K).mp hImg

end ProductSimplex

end Correspondence
end GameTheory
end EcoLean
