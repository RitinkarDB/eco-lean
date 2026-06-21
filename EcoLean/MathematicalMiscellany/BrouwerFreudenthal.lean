import EcoLean.MathematicalMiscellany.SpernerFreudenthal

/-!
# Brouwer-facing analytic setup

This file starts the analytic bridge from the finite grid Sperner interface in
`SpernerFreudenthal.lean` toward Brouwer.  It deliberately stops before any
compactness, continuity, Kakutani, or Brouwer fixed-point proof.
-/

namespace EconLib
namespace SpernerFreudenthal
namespace Brouwer

open scoped BigOperators

/-- The standard `d`-simplex in real barycentric coordinates. -/
abbrev StdSimplex (d : ℕ) :=
  {x : Fin (d + 1) → ℝ // (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

namespace StdSimplex

/-- The `i`th barycentric coordinate. -/
def coord {d : ℕ} (x : StdSimplex d) (i : Fin (d + 1)) : ℝ :=
  x.1 i

theorem coord_nonneg {d : ℕ} (x : StdSimplex d) (i : Fin (d + 1)) :
    0 ≤ x.coord i :=
  x.2.1 i

theorem sum_coord_eq_one {d : ℕ} (x : StdSimplex d) :
    (∑ i, x.coord i) = 1 :=
  x.2.2

theorem coord_le_one {d : ℕ} (x : StdSimplex d) (i : Fin (d + 1)) :
    x.coord i ≤ 1 := by
  classical
  rw [← x.sum_coord_eq_one]
  exact Finset.single_le_sum (fun j _hj => x.coord_nonneg j) (Finset.mem_univ i)

/-- The standard simplex predicate cuts out a closed subset of coordinate space. -/
theorem isClosed_set (d : ℕ) :
    IsClosed
      {x : Fin (d + 1) → ℝ |
        (∀ i : Fin (d + 1), 0 ≤ x i) ∧
          (∑ i, x i) = 1} := by
  change IsClosed (stdSimplex ℝ (Fin (d + 1)))
  exact isClosed_stdSimplex ℝ (Fin (d + 1))

/-- The standard simplex lies in the coordinate cube `[0,1]^(d+1)`. -/
theorem subset_pi_Icc (d : ℕ) :
    {x : Fin (d + 1) → ℝ |
      (∀ i : Fin (d + 1), 0 ≤ x i) ∧
        (∑ i, x i) = 1}
      ⊆
    Set.pi Set.univ (fun _ : Fin (d + 1) => Set.Icc (0 : ℝ) 1) := by
  classical
  intro x hx i _hi
  constructor
  · exact hx.1 i
  · rw [← hx.2]
    exact Finset.single_le_sum (fun j _hj => hx.1 j) (Finset.mem_univ i)

/-- The standard simplex is compact as a subset of finite coordinate space. -/
theorem isCompact_set (d : ℕ) :
    IsCompact
      {x : Fin (d + 1) → ℝ |
        (∀ i : Fin (d + 1), 0 ≤ x i) ∧
          (∑ i, x i) = 1} := by
  change IsCompact (stdSimplex ℝ (Fin (d + 1)))
  exact isCompact_stdSimplex ℝ (Fin (d + 1))

instance instCompactSpace (d : ℕ) :
    CompactSpace (StdSimplex d) := by
  change CompactSpace (stdSimplex ℝ (Fin (d + 1)))
  infer_instance

/-- Coordinatewise sup-distance bound for points of the standard simplex. -/
def BarySupDistLe {d : ℕ} (x y : StdSimplex d) (ε : ℝ) : Prop :=
  ∀ i : Fin (d + 1), |x.coord i - y.coord i| ≤ ε

/-- A finite coordinatewise modulus for a self-map of the standard simplex. -/
def MapCoordCloseOn {d : ℕ}
    (f : StdSimplex d → StdSimplex d) (δ η : ℝ) : Prop :=
  ∀ x y : StdSimplex d,
    BarySupDistLe x y δ →
      ∀ i : Fin (d + 1), |(f x).coord i - (f y).coord i| ≤ η

/-- Custom pointwise coordinate continuity, stated in barycentric sup norm. -/
def CoordinateContinuous {d : ℕ}
    (f : StdSimplex d → StdSimplex d) : Prop :=
  ∀ x : StdSimplex d, ∀ i : Fin (d + 1), ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y : StdSimplex d,
        BarySupDistLe y x δ →
          |(f y).coord i - (f x).coord i| ≤ ε

/-- Custom uniform coordinate continuity, stated in barycentric sup norm. -/
def UniformCoordinateContinuous {d : ℕ}
    (f : StdSimplex d → StdSimplex d) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x y : StdSimplex d,
        BarySupDistLe x y δ →
          ∀ i : Fin (d + 1), |(f x).coord i - (f y).coord i| ≤ ε

/-- A custom uniform coordinate modulus, stated in barycentric sup norm. -/
def UniformCoordinateModulus {d : ℕ}
    (f : StdSimplex d → StdSimplex d) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ MapCoordCloseOn f δ ε

theorem MapCoordCloseOn.mono {d : ℕ}
    {f : StdSimplex d → StdSimplex d}
    {δ₁ δ₂ η : ℝ}
    (hδ : δ₁ ≤ δ₂)
    (h : MapCoordCloseOn f δ₂ η) :
    MapCoordCloseOn f δ₁ η := by
  intro x y hxy i
  exact h x y (fun j => le_trans (hxy j) hδ) i

theorem dist_le_of_barySupDistLe {d : ℕ}
    {x y : StdSimplex d} {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hxy : BarySupDistLe x y δ) :
    dist x y ≤ δ := by
  change dist x.1 y.1 ≤ δ
  rw [dist_pi_le_iff hδ]
  intro i
  simpa [coord, Real.dist_eq, abs_sub_comm] using hxy i

theorem coord_abs_sub_le_of_dist_lt {d : ℕ}
    {x y : StdSimplex d} {ε : ℝ}
    (i : Fin (d + 1))
    (h : dist x y < ε) :
    |x.coord i - y.coord i| ≤ ε := by
  have hcoord : dist (x.1 i) (y.1 i) ≤ dist x.1 y.1 :=
    dist_le_pi_dist x.1 y.1 i
  change |x.1 i - y.1 i| ≤ ε
  rw [← Real.dist_eq]
  calc
    dist (x.1 i) (y.1 i) ≤ dist x.1 y.1 := hcoord
    _ = dist x y := rfl
    _ ≤ ε := le_of_lt h

theorem uniformCoordinateModulus_of_uniformCoordinateContinuous {d : ℕ}
    {f : StdSimplex d → StdSimplex d}
    (h : UniformCoordinateContinuous f) :
    UniformCoordinateModulus f := by
  classical
  intro ε hε
  rcases h ε hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro x y hxy i
  exact hδ x y hxy i

theorem coordinateContinuous_of_continuous {d : ℕ}
    {f : StdSimplex d → StdSimplex d}
    (hf : Continuous f) :
    CoordinateContinuous f := by
  classical
  intro x i ε hε
  have hcoord_cont :
      Continuous (fun z : StdSimplex d => (f z).coord i) := by
    simpa [coord] using
      (continuous_apply i).comp (continuous_subtype_val.comp hf)
  rcases (Metric.continuousAt_iff.mp hcoord_cont.continuousAt) ε hε with
    ⟨δ, hδpos, hδ⟩
  refine ⟨δ / 2, by positivity, ?_⟩
  intro y hyx
  have hdist_le : dist y x ≤ δ / 2 :=
    dist_le_of_barySupDistLe (by positivity) hyx
  have hdist_lt : dist y x < δ := by linarith
  have hmetric := hδ hdist_lt
  simpa [coord, Real.dist_eq] using le_of_lt hmetric

theorem uniformCoordinateContinuous_of_uniformContinuous {d : ℕ}
    {f : StdSimplex d → StdSimplex d}
    (hf : UniformContinuous f) :
    UniformCoordinateContinuous f := by
  classical
  intro ε hε
  have hhalf_pos : 0 < ε / 2 := by linarith
  rcases (Metric.uniformContinuous_iff.mp hf) (ε / 2) hhalf_pos with
    ⟨δ, hδpos, hδ⟩
  refine ⟨δ / 2, by positivity, ?_⟩
  intro x y hxy i
  have hdist_le : dist x y ≤ δ / 2 :=
    dist_le_of_barySupDistLe (by positivity) hxy
  have hdist_lt : dist x y < δ := by linarith
  have hfxfy : dist (f x) (f y) < ε / 2 := hδ hdist_lt
  exact (coord_abs_sub_le_of_dist_lt i hfxfy).trans (by linarith)

theorem uniformCoordinateContinuous_of_continuous_compact {d : ℕ}
    [CompactSpace (StdSimplex d)]
    {f : StdSimplex d → StdSimplex d}
    (hf : Continuous f) :
    UniformCoordinateContinuous f :=
  uniformCoordinateContinuous_of_uniformContinuous
    (CompactSpace.uniformContinuous_of_continuous hf)

/-- `x` is an `ε`-approximate fixed point in barycentric sup norm. -/
def ApproxFixedPoint {d : ℕ}
    (f : StdSimplex d → StdSimplex d)
    (x : StdSimplex d) (ε : ℝ) : Prop :=
  BarySupDistLe (f x) x ε

/-- The map has approximate fixed points at every positive tolerance. -/
def HasArbitrarilyGoodApproxFixedPoints {d : ℕ}
    (f : StdSimplex d → StdSimplex d) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ x : StdSimplex d, ApproxFixedPoint f x ε

/--
A soft finite-coordinate modulus that can be supplied later by uniform
continuity on the compact standard simplex.
-/
def HasVanishingCoordinateModulus {d : ℕ}
    (f : StdSimplex d → StdSimplex d) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ η : ℝ,
      0 < δ ∧ 0 ≤ η ∧
      ((Fintype.card (Fin (d + 1)) : ℝ) * (δ + η)) < ε ∧
      MapCoordCloseOn f δ η

/-- Sequential compactness, stated directly in barycentric sup norm. -/
def SequentialCompactness (d : ℕ) : Prop :=
  ∀ x : ℕ → StdSimplex d,
    ∃ xstar : StdSimplex d,
      ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
        ∀ ε : ℝ, 0 < ε →
          ∃ N₀ : ℕ,
            ∀ n ≥ N₀,
              BarySupDistLe (x (φ n)) xstar ε

/-- Named placeholder for the remaining custom compactness theorem. -/
def SequentialCompactnessHypothesis (d : ℕ) : Prop :=
  SequentialCompactness d

theorem sequentialCompactness_of_compactSpace {d : ℕ}
    [CompactSpace (StdSimplex d)] :
    SequentialCompactness d := by
  classical
  intro x
  rcases CompactSpace.tendsto_subseq x with ⟨xstar, φ, hφmono, hlim⟩
  refine ⟨xstar, φ, hφmono, ?_⟩
  intro ε hε
  have hcoord_eventually :
      ∀ i : Fin (d + 1),
        ∀ᶠ n in Filter.atTop,
          |(x (φ n)).coord i - xstar.coord i| ≤ ε := by
    intro i
    have hcont :
        Continuous (fun z : StdSimplex d => z.coord i) := by
      simpa [coord] using (continuous_apply i).comp continuous_subtype_val
    have hcoord_tendsto :
        Filter.Tendsto (fun n => (x (φ n)).coord i)
          Filter.atTop (nhds (xstar.coord i)) := by
      simpa [Function.comp_def] using (hcont.tendsto xstar).comp hlim
    have hdist_eventually :
        ∀ᶠ n in Filter.atTop,
          dist ((x (φ n)).coord i) (xstar.coord i) < ε :=
      (Metric.tendsto_nhds.mp hcoord_tendsto) ε hε
    exact hdist_eventually.mono (by
      intro n hn
      simpa [Real.dist_eq] using le_of_lt hn)
  have hall_eventually :
      ∀ᶠ n in Filter.atTop,
        ∀ i : Fin (d + 1),
          |(x (φ n)).coord i - xstar.coord i| ≤ ε :=
    (Filter.eventually_all).2 hcoord_eventually
  rcases Filter.eventually_atTop.mp hall_eventually with ⟨N₀, hN₀⟩
  refine ⟨N₀, ?_⟩
  intro n hn i
  exact hN₀ n hn i

/-- Sequential continuity, stated directly in barycentric sup norm. -/
def SequentialContinuous {d : ℕ}
    (f : StdSimplex d → StdSimplex d) : Prop :=
  ∀ (xseq : ℕ → StdSimplex d) (xstar : StdSimplex d),
    (∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ,
        ∀ n ≥ N₀,
          BarySupDistLe (xseq n) xstar ε) →
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ,
        ∀ n ≥ N₀,
          BarySupDistLe (f (xseq n)) (f xstar) ε

theorem sequentialContinuous_of_uniformCoordinateModulus {d : ℕ}
    {f : StdSimplex d → StdSimplex d}
    (hmod : UniformCoordinateModulus f) :
    SequentialContinuous f := by
  classical
  intro xseq xstar hxconv ε hε
  rcases hmod ε hε with ⟨δ, hδpos, hclose⟩
  rcases hxconv δ hδpos with ⟨N₀, hN₀⟩
  refine ⟨N₀, ?_⟩
  intro n hn
  exact hclose (xseq n) xstar (hN₀ n hn)

theorem hasVanishingCoordinateModulus_of_uniformCoordinateModulus {d : ℕ}
    {f : StdSimplex d → StdSimplex d}
    (hmod : UniformCoordinateModulus f) :
    HasVanishingCoordinateModulus f := by
  classical
  intro ε hε
  let n : ℝ := (Fintype.card (Fin (d + 1)) : ℝ)
  have hnpos : 0 < n := by
    have hnpos_nat : 0 < Fintype.card (Fin (d + 1)) :=
      Fintype.card_pos_iff.mpr ⟨⟨0, Nat.succ_pos d⟩⟩
    dsimp [n]
    exact_mod_cast hnpos_nat
  let ηTarget : ℝ := ε / (4 * n)
  have hηpos : 0 < ηTarget := by
    dsimp [ηTarget]
    positivity
  rcases hmod ηTarget hηpos with ⟨δ₀, hδ₀pos, hclose₀⟩
  let δ : ℝ := min δ₀ ηTarget
  let η : ℝ := ηTarget
  refine ⟨δ, η, ?_, ?_, ?_, ?_⟩
  · exact lt_min hδ₀pos hηpos
  · exact le_of_lt hηpos
  · have hδle : δ ≤ ηTarget := min_le_right δ₀ ηTarget
    have hsum : δ + η ≤ ηTarget + ηTarget := by
      dsimp [η]
      linarith
    have hmain_eq : n * (ηTarget + ηTarget) = ε / 2 := by
      dsimp [ηTarget]
      field_simp [ne_of_gt hnpos]
      ring
    have hmain : n * (ηTarget + ηTarget) < ε := by
      linarith
    have hnnonneg : 0 ≤ n := le_of_lt hnpos
    have hmul := mul_le_mul_of_nonneg_left hsum hnnonneg
    exact lt_of_le_of_lt hmul hmain
  · have hδle₀ : δ ≤ δ₀ := min_le_left δ₀ ηTarget
    exact MapCoordCloseOn.mono hδle₀ hclose₀

theorem real_eq_of_forall_abs_sub_le {a b : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → |a - b| ≤ ε) :
    a = b := by
  by_contra hne
  have hpos : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hhalf_pos : 0 < |a - b| / 2 := by positivity
  have hle := h (|a - b| / 2) hhalf_pos
  linarith

theorem lower_bound_from_upper_bound {d : ℕ}
    {x y : StdSimplex d}
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hupper : ∀ i : Fin (d + 1), y.coord i ≤ x.coord i + ε) :
    ∀ i : Fin (d + 1),
      x.coord i ≤ y.coord i +
        (Fintype.card (Fin (d + 1)) : ℝ) * ε := by
  classical
  intro i
  let s : Finset (Fin (d + 1)) := Finset.univ
  let g : Fin (d + 1) → ℝ := fun j => y.coord j - x.coord j
  have hsumdiff : (∑ j : Fin (d + 1), g j) = 0 := by
    simp [g, Finset.sum_sub_distrib,
      StdSimplex.sum_coord_eq_one y,
      StdSimplex.sum_coord_eq_one x]
  have hsumdiff_s : s.sum g = 0 := by
    simpa [s] using hsumdiff
  have hsplit :
      (s.erase i).sum g + g i = s.sum g := by
    exact Finset.sum_erase_add (s := s) (a := i) (f := g) (by simp [s])
  have herase_eq :
      (s.erase i).sum g = x.coord i - y.coord i := by
    linarith
  have hterm :
      ∀ j ∈ s.erase i, g j ≤ ε := by
    intro j _hj
    dsimp [g]
    linarith [hupper j]
  have hsum_le :
      (s.erase i).sum g ≤ (s.erase i).sum (fun _j => ε) :=
    Finset.sum_le_sum hterm
  have hconst :
      (s.erase i).sum (fun _j => ε)
        =
      ((s.erase i).card : ℝ) * ε := by
    simp
  have hcard_nat :
      (s.erase i).card ≤ Fintype.card (Fin (d + 1)) := by
    exact Finset.card_le_univ (s.erase i)
  have hcard :
      ((s.erase i).card : ℝ)
        ≤
      (Fintype.card (Fin (d + 1)) : ℝ) := by
    exact_mod_cast hcard_nat
  have hsum_le_total :
      (s.erase i).sum g
        ≤
      (Fintype.card (Fin (d + 1)) : ℝ) * ε := by
    calc
      (s.erase i).sum g ≤ (s.erase i).sum (fun _j => ε) := hsum_le
      _ = ((s.erase i).card : ℝ) * ε := hconst
      _ ≤ (Fintype.card (Fin (d + 1)) : ℝ) * ε :=
        mul_le_mul_of_nonneg_right hcard hε
  linarith

theorem approxFixedPoint_of_forall_upper {d : ℕ}
    {f : StdSimplex d → StdSimplex d}
    {x : StdSimplex d}
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hupper : ∀ i : Fin (d + 1), (f x).coord i ≤ x.coord i + ε) :
    ApproxFixedPoint
      f x
      ((Fintype.card (Fin (d + 1)) : ℝ) * ε) := by
  classical
  intro i
  have hlower :=
    lower_bound_from_upper_bound (x := x) (y := f x) hε hupper i
  have hcard_ge_one :
      (1 : ℝ) ≤ (Fintype.card (Fin (d + 1)) : ℝ) := by
    rw [Fintype.card_fin]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
  have hε_le :
      ε ≤ (Fintype.card (Fin (d + 1)) : ℝ) * ε := by
    calc
      ε = (1 : ℝ) * ε := by ring
      _ ≤ (Fintype.card (Fin (d + 1)) : ℝ) * ε :=
        mul_le_mul_of_nonneg_right hcard_ge_one hε
  apply abs_le.mpr
  constructor
  · linarith
  · have hupper_i := hupper i
    linarith

end StdSimplex

/-- A realised barycentric grid point lies in the real standard simplex. -/
theorem realiseSimplexGrid_mem_stdSimplex {d N : ℕ} [NeZero N]
    (x : BarycentricFreudenthal.SimplexGrid d N) :
    (∀ i, 0 ≤ BarycentricFreudenthal.realiseSimplexGrid x i) ∧
      (∑ i, BarycentricFreudenthal.realiseSimplexGrid x i) = 1 := by
  exact ⟨BarycentricFreudenthal.realiseSimplexGrid_nonneg x,
    BarycentricFreudenthal.realiseSimplexGrid_sum_eq_one x⟩

/-- Realise a barycentric grid point as a point of the standard simplex. -/
noncomputable def stdSimplexOfSimplexGrid {d N : ℕ} [NeZero N]
    (x : BarycentricFreudenthal.SimplexGrid d N) : StdSimplex d :=
  ⟨BarycentricFreudenthal.realiseSimplexGrid x,
    realiseSimplexGrid_mem_stdSimplex x⟩

end Brouwer

namespace BarycentricFreudenthal
namespace GridSmallSimplex

theorem stdSimplex_closeness_of_mesh {d N : ℕ} [NeZero N]
    {C : GridSmallSimplex d N}
    {ε : ℝ}
    (hmesh : C.MeshLe ε)
    {x y : SimplexGrid d N}
    (hx : x ∈ C.vertices)
    (hy : y ∈ C.vertices) :
    Brouwer.StdSimplex.BarySupDistLe
      (Brouwer.stdSimplexOfSimplexGrid x)
      (Brouwer.stdSimplexOfSimplexGrid y)
      ε := by
  intro i
  simpa [Brouwer.StdSimplex.BarySupDistLe, Brouwer.StdSimplex.coord,
    Brouwer.stdSimplexOfSimplexGrid] using hmesh x hx y hy i

end GridSmallSimplex

namespace GeometricGridCell

theorem stdSimplex_closeness_of_mesh {d N : ℕ} [NeZero N]
    {C : GeometricGridCell d N}
    {ε : ℝ}
    (hmesh : C.MeshLe ε)
    {x y : SimplexGrid d N}
    (hx : x ∈ C.vertices)
    (hy : y ∈ C.vertices) :
    Brouwer.StdSimplex.BarySupDistLe
      (Brouwer.stdSimplexOfSimplexGrid x)
      (Brouwer.stdSimplexOfSimplexGrid y)
      ε := by
  intro i
  simpa [Brouwer.StdSimplex.BarySupDistLe, Brouwer.StdSimplex.coord,
    Brouwer.stdSimplexOfSimplexGrid] using hmesh x hx y hy i

end GeometricGridCell
end BarycentricFreudenthal

namespace Brouwer

/-- A label witnesses a coordinate where `f` moves `x` downward. -/
def IsBrouwerDecreaseLabel {d : ℕ}
    (f : StdSimplex d → StdSimplex d)
    (x : StdSimplex d)
    (i : Fin (d + 1)) : Prop :=
  (f x).coord i < x.coord i

/-- The same decrease-label predicate, specialised to realised grid points. -/
def IsBrouwerGridLabel {d N : ℕ} [NeZero N]
    (f : StdSimplex d → StdSimplex d)
    (x : BarycentricFreudenthal.SimplexGrid d N)
    (i : Fin (d + 1)) : Prop :=
  IsBrouwerDecreaseLabel f (stdSimplexOfSimplexGrid x) i

/--
If a self-map of the standard simplex does not fix `x`, then some barycentric
coordinate strictly decreases.
-/
theorem exists_decrease_label_of_ne {d : ℕ}
    (f : StdSimplex d → StdSimplex d)
    (x : StdSimplex d)
    (hne : f x ≠ x) :
    ∃ i : Fin (d + 1), IsBrouwerDecreaseLabel f x i := by
  classical
  by_contra hnone
  push_neg at hnone
  have hle : ∀ i : Fin (d + 1), x.coord i ≤ (f x).coord i := by
    intro i
    exact not_lt.mp (by
      simpa [IsBrouwerDecreaseLabel] using hnone i)
  have hdiff_nonneg :
      ∀ i ∈ (Finset.univ : Finset (Fin (d + 1))),
        0 ≤ (f x).coord i - x.coord i := by
    intro i _hi
    linarith [hle i]
  have hsumdiff :
      (∑ i : Fin (d + 1), ((f x).coord i - x.coord i)) = 0 := by
    rw [Finset.sum_sub_distrib,
      StdSimplex.sum_coord_eq_one (f x),
      StdSimplex.sum_coord_eq_one x]
    ring
  have hdiff_zero :
      ∀ i ∈ (Finset.univ : Finset (Fin (d + 1))),
        (f x).coord i - x.coord i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hdiff_nonneg).mp hsumdiff
  apply hne
  apply Subtype.ext
  funext i
  have hi := hdiff_zero i (by simp)
  have hcoord : (f x).coord i = x.coord i := by
    linarith [hi]
  simpa [StdSimplex.coord] using hcoord

theorem exists_grid_decrease_label_of_ne {d N : ℕ} [NeZero N]
    (f : StdSimplex d → StdSimplex d)
    (x : BarycentricFreudenthal.SimplexGrid d N)
    (hne : f (stdSimplexOfSimplexGrid x) ≠ stdSimplexOfSimplexGrid x) :
    ∃ i : Fin (d + 1), IsBrouwerGridLabel f x i := by
  rcases exists_decrease_label_of_ne f (stdSimplexOfSimplexGrid x) hne with
    ⟨i, hi⟩
  exact ⟨i, by simpa [IsBrouwerGridLabel] using hi⟩

/-- A self-map with no fixed points on the standard simplex. -/
def FixedPointFree {d : ℕ} (f : StdSimplex d → StdSimplex d) : Prop :=
  ∀ x : StdSimplex d, f x ≠ x

/-- The Brouwer contradiction labelling: choose a coordinate that decreases. -/
noncomputable def brouwerGridLabel {d N : ℕ} [NeZero N]
    (f : StdSimplex d → StdSimplex d)
    (hff : FixedPointFree f) :
    BarycentricFreudenthal.SimplexGrid d N → Fin (d + 1) :=
  fun x =>
    Classical.choose
      (exists_grid_decrease_label_of_ne f x
        (hff (stdSimplexOfSimplexGrid x)))

theorem brouwerGridLabel_spec {d N : ℕ} [NeZero N]
    (f : StdSimplex d → StdSimplex d)
    (hff : FixedPointFree f)
    (x : BarycentricFreudenthal.SimplexGrid d N) :
    IsBrouwerDecreaseLabel
      f
      (stdSimplexOfSimplexGrid x)
      (brouwerGridLabel f hff x) := by
  classical
  have hchoose :=
    Classical.choose_spec
      (exists_grid_decrease_label_of_ne f x
        (hff (stdSimplexOfSimplexGrid x)))
  simpa [brouwerGridLabel, IsBrouwerGridLabel] using hchoose

theorem positive_grid_coord_of_positive_realise {d N : ℕ} [NeZero N]
    (x : BarycentricFreudenthal.SimplexGrid d N)
    (i : Fin (d + 1))
    (hpos : 0 < BarycentricFreudenthal.realiseSimplexGrid x i) :
    0 < x.1 i := by
  by_contra hnot
  have hzero : x.1 i = 0 := Nat.eq_zero_of_not_pos hnot
  have hreal_zero : BarycentricFreudenthal.realiseSimplexGrid x i = 0 := by
    simp [BarycentricFreudenthal.realiseSimplexGrid, hzero]
  linarith

theorem brouwerGridLabel_isSperner {d N : ℕ} [NeZero N]
    (f : StdSimplex d → StdSimplex d)
    (hff : FixedPointFree f) :
    BarycentricFreudenthal.GridIsSperner
      (d := d) (N := N) (brouwerGridLabel (d := d) (N := N) f hff) := by
  classical
  intro x
  let i : Fin (d + 1) := brouwerGridLabel f hff x
  have hdec :
      IsBrouwerDecreaseLabel f (stdSimplexOfSimplexGrid x) i :=
    brouwerGridLabel_spec f hff x
  have hf_nonneg : 0 ≤ (f (stdSimplexOfSimplexGrid x)).coord i :=
    StdSimplex.coord_nonneg (f (stdSimplexOfSimplexGrid x)) i
  have hreal_pos :
      0 < BarycentricFreudenthal.realiseSimplexGrid x i := by
    simpa [IsBrouwerDecreaseLabel, StdSimplex.coord,
      stdSimplexOfSimplexGrid] using lt_of_le_of_lt hf_nonneg hdec
  have hcoord_pos : 0 < x.1 i :=
    positive_grid_coord_of_positive_realise x i hreal_pos
  simpa [BarycentricFreudenthal.SimplexGrid.support, i]
    using hcoord_pos

theorem brouwer_fully_labelled_small_simplex {d N : ℕ} [NeZero N]
    (P : BarycentricFreudenthal.GridSpernerForBrouwerPackage d N)
    (f : StdSimplex d → StdSimplex d)
    (hff : FixedPointFree f)
    (missing : Fin (d + 1)) :
    ∃ C : BarycentricFreudenthal.GridSmallSimplex d N,
      BarycentricFreudenthal.FullyLabelledGridSmallSimplex
        (brouwerGridLabel f hff) C ∧
      C.MeshLe ((1 : ℝ) / (N : ℝ)) := by
  classical
  exact BarycentricFreudenthal.grid_sperner_for_brouwer_package_with_mesh
    P
    (brouwerGridLabel f hff)
    (brouwerGridLabel_isSperner f hff)
    missing

theorem exists_vertex_with_brouwer_label {d N : ℕ} [NeZero N]
    {f : StdSimplex d → StdSimplex d}
    {hff : FixedPointFree f}
    {C : BarycentricFreudenthal.GridSmallSimplex d N}
    (hC :
      BarycentricFreudenthal.FullyLabelledGridSmallSimplex
        (brouwerGridLabel f hff) C)
    (i : Fin (d + 1)) :
    ∃ x ∈ C.vertices, brouwerGridLabel f hff x = i := by
  classical
  have hi :
      i ∈ Sperner.labelsOn (brouwerGridLabel f hff) C.vertices := by
    exact hC (Finset.mem_univ i)
  exact (Sperner.mem_labelsOn_iff
    (brouwerGridLabel f hff) C.vertices i).mp hi

theorem exists_vertex_with_decrease_at {d N : ℕ} [NeZero N]
    {f : StdSimplex d → StdSimplex d}
    {hff : FixedPointFree f}
    {C : BarycentricFreudenthal.GridSmallSimplex d N}
    (hC :
      BarycentricFreudenthal.FullyLabelledGridSmallSimplex
        (brouwerGridLabel f hff) C)
    (i : Fin (d + 1)) :
    ∃ x ∈ C.vertices,
      IsBrouwerDecreaseLabel f (stdSimplexOfSimplexGrid x) i := by
  classical
  rcases exists_vertex_with_brouwer_label
      (f := f) (hff := hff) (C := C) hC i with
    ⟨x, hxC, hxlabel⟩
  refine ⟨x, hxC, ?_⟩
  simpa [hxlabel] using brouwerGridLabel_spec f hff x

theorem approximate_fixed_point_from_labelled_small_simplex
    {d N : ℕ} [NeZero N]
    {f : StdSimplex d → StdSimplex d}
    {hff : FixedPointFree f}
    {C : BarycentricFreudenthal.GridSmallSimplex d N}
    {δ η : ℝ}
    (hmesh : C.MeshLe δ)
    (hcont : StdSimplex.MapCoordCloseOn f δ η)
    (hC :
      BarycentricFreudenthal.FullyLabelledGridSmallSimplex
        (brouwerGridLabel f hff) C)
    (x₀ : BarycentricFreudenthal.SimplexGrid d N)
    (hx₀ : x₀ ∈ C.vertices) :
    ∀ i : Fin (d + 1),
      (f (stdSimplexOfSimplexGrid x₀)).coord i
        ≤
      (stdSimplexOfSimplexGrid x₀).coord i + δ + η := by
  classical
  intro i
  rcases exists_vertex_with_decrease_at
      (f := f) (hff := hff) (C := C) hC i with
    ⟨xi, hxiC, hdec⟩
  have hclose_x :
      StdSimplex.BarySupDistLe
        (stdSimplexOfSimplexGrid xi)
        (stdSimplexOfSimplexGrid x₀)
        δ :=
    BarycentricFreudenthal.GridSmallSimplex.stdSimplex_closeness_of_mesh
      hmesh hxiC hx₀
  have hclose_f :=
    hcont
      (stdSimplexOfSimplexGrid xi)
      (stdSimplexOfSimplexGrid x₀)
      hclose_x
      i
  have hdec' :
      (f (stdSimplexOfSimplexGrid xi)).coord i
        <
      (stdSimplexOfSimplexGrid xi).coord i :=
    hdec
  have hf_bounds := abs_le.mp hclose_f
  have hx_bounds := abs_le.mp (hclose_x i)
  linarith [hdec', hf_bounds.1, hx_bounds.2]

theorem exists_approximate_fixed_point_from_grid_sperner
    {d N : ℕ} [NeZero N]
    (P : BarycentricFreudenthal.GridSpernerForBrouwerPackage d N)
    (f : StdSimplex d → StdSimplex d)
    (hff : FixedPointFree f)
    (missing : Fin (d + 1))
    {η : ℝ}
    (hcont :
      StdSimplex.MapCoordCloseOn f ((1 : ℝ) / (N : ℝ)) η) :
    ∃ x₀ : BarycentricFreudenthal.SimplexGrid d N,
      ∀ i : Fin (d + 1),
        (f (stdSimplexOfSimplexGrid x₀)).coord i
          ≤
        (stdSimplexOfSimplexGrid x₀).coord i
          + ((1 : ℝ) / (N : ℝ)) + η := by
  classical
  rcases brouwer_fully_labelled_small_simplex
      P f hff missing with
    ⟨C, hC, hmesh⟩
  let zero : Fin (d + 1) := ⟨0, Nat.succ_pos d⟩
  rcases exists_vertex_with_brouwer_label
      (f := f) (hff := hff) (C := C) hC zero with
    ⟨x₀, hx₀C, _hlabel⟩
  refine ⟨x₀, ?_⟩
  exact approximate_fixed_point_from_labelled_small_simplex
    (f := f) (hff := hff) (C := C)
    (δ := ((1 : ℝ) / (N : ℝ))) (η := η)
    hmesh hcont hC x₀ hx₀C

theorem exists_supnorm_approx_fixed_point_from_grid_sperner
    {d N : ℕ} [NeZero N]
    (P : BarycentricFreudenthal.GridSpernerForBrouwerPackage d N)
    (f : StdSimplex d → StdSimplex d)
    (hff : FixedPointFree f)
    (missing : Fin (d + 1))
    {η : ℝ}
    (hη : 0 ≤ η)
    (hcont :
      StdSimplex.MapCoordCloseOn f ((1 : ℝ) / (N : ℝ)) η) :
    ∃ x₀ : BarycentricFreudenthal.SimplexGrid d N,
      StdSimplex.ApproxFixedPoint
        f
        (stdSimplexOfSimplexGrid x₀)
        ((Fintype.card (Fin (d + 1)) : ℝ) *
          (((1 : ℝ) / (N : ℝ)) + η)) := by
  classical
  rcases exists_approximate_fixed_point_from_grid_sperner
      (P := P) (f := f) (hff := hff) (missing := missing)
      (η := η) hcont with
    ⟨x₀, hupper⟩
  refine ⟨x₀, ?_⟩
  apply StdSimplex.approxFixedPoint_of_forall_upper
  · have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    exact add_nonneg (div_nonneg zero_le_one hNpos.le) hη
  · intro i
    linarith [hupper i]

theorem exists_vertex_with_brouwer_label_geometric {d N : ℕ} [NeZero N]
    {f : StdSimplex d → StdSimplex d}
    {hff : FixedPointFree f}
    {C : BarycentricFreudenthal.GeometricGridCell d N}
    (hC :
      BarycentricFreudenthal.FullyLabelledGeometricGridCell
        (brouwerGridLabel f hff) C)
    (i : Fin (d + 1)) :
    ∃ x ∈ C.vertices, brouwerGridLabel f hff x = i := by
  classical
  exact hC i

theorem exists_vertex_with_decrease_at_geometric {d N : ℕ} [NeZero N]
    {f : StdSimplex d → StdSimplex d}
    {hff : FixedPointFree f}
    {C : BarycentricFreudenthal.GeometricGridCell d N}
    (hC :
      BarycentricFreudenthal.FullyLabelledGeometricGridCell
        (brouwerGridLabel f hff) C)
    (i : Fin (d + 1)) :
    ∃ x ∈ C.vertices,
      IsBrouwerDecreaseLabel f (stdSimplexOfSimplexGrid x) i := by
  classical
  rcases exists_vertex_with_brouwer_label_geometric
      (f := f) (hff := hff) (C := C) hC i with
    ⟨x, hxC, hxlabel⟩
  refine ⟨x, hxC, ?_⟩
  simpa [hxlabel] using brouwerGridLabel_spec f hff x

theorem brouwer_fully_labelled_geometric_small_simplex
    {d N : ℕ} [NeZero N]
    (P : BarycentricFreudenthal.GeometricGridSpernerForBrouwerPackage d N)
    (f : StdSimplex d → StdSimplex d)
    (hff : FixedPointFree f)
    (missing : Fin (d + 1)) :
    ∃ C : BarycentricFreudenthal.GeometricGridCell d N,
      BarycentricFreudenthal.FullyLabelledGeometricGridCell
        (brouwerGridLabel f hff) C ∧
        C.MeshLe ((1 : ℝ) / (N : ℝ)) := by
  classical
  exact BarycentricFreudenthal.geometric_grid_sperner_for_brouwer_package_with_mesh
    P
    (brouwerGridLabel f hff)
    (brouwerGridLabel_isSperner f hff)
    missing

theorem approximate_fixed_point_from_labelled_geometric_small_simplex
    {d N : ℕ} [NeZero N]
    {f : StdSimplex d → StdSimplex d}
    {hff : FixedPointFree f}
    {C : BarycentricFreudenthal.GeometricGridCell d N}
    {δ η : ℝ}
    (hmesh : C.MeshLe δ)
    (hcont : StdSimplex.MapCoordCloseOn f δ η)
    (hC :
      BarycentricFreudenthal.FullyLabelledGeometricGridCell
        (brouwerGridLabel f hff) C)
    (x₀ : BarycentricFreudenthal.SimplexGrid d N)
    (hx₀ : x₀ ∈ C.vertices) :
    ∀ i : Fin (d + 1),
      (f (stdSimplexOfSimplexGrid x₀)).coord i
        ≤
      (stdSimplexOfSimplexGrid x₀).coord i + δ + η := by
  classical
  intro i
  rcases exists_vertex_with_decrease_at_geometric
      (f := f) (hff := hff) (C := C) hC i with
    ⟨xi, hxiC, hdec⟩
  have hclose_x :
      StdSimplex.BarySupDistLe
        (stdSimplexOfSimplexGrid xi)
        (stdSimplexOfSimplexGrid x₀)
        δ :=
    BarycentricFreudenthal.GeometricGridCell.stdSimplex_closeness_of_mesh
      hmesh hxiC hx₀
  have hclose_f :=
    hcont
      (stdSimplexOfSimplexGrid xi)
      (stdSimplexOfSimplexGrid x₀)
      hclose_x
      i
  have hdec' :
      (f (stdSimplexOfSimplexGrid xi)).coord i
        <
      (stdSimplexOfSimplexGrid xi).coord i :=
    hdec
  have hf_bounds := abs_le.mp hclose_f
  have hx_bounds := abs_le.mp (hclose_x i)
  linarith [hdec', hf_bounds.1, hx_bounds.2]

theorem exists_approximate_fixed_point_from_geometric_grid_sperner
    {d N : ℕ} [NeZero N]
    (P : BarycentricFreudenthal.GeometricGridSpernerForBrouwerPackage d N)
    (f : StdSimplex d → StdSimplex d)
    (hff : FixedPointFree f)
    (missing : Fin (d + 1))
    {η : ℝ}
    (hcont :
      StdSimplex.MapCoordCloseOn f ((1 : ℝ) / (N : ℝ)) η) :
    ∃ x₀ : BarycentricFreudenthal.SimplexGrid d N,
      ∀ i : Fin (d + 1),
        (f (stdSimplexOfSimplexGrid x₀)).coord i
          ≤
        (stdSimplexOfSimplexGrid x₀).coord i
          + ((1 : ℝ) / (N : ℝ)) + η := by
  classical
  rcases brouwer_fully_labelled_geometric_small_simplex
      P f hff missing with
    ⟨C, hC, hmesh⟩
  let zero : Fin (d + 1) := ⟨0, Nat.succ_pos d⟩
  rcases exists_vertex_with_brouwer_label_geometric
      (f := f) (hff := hff) (C := C) hC zero with
    ⟨x₀, hx₀C, _hlabel⟩
  refine ⟨x₀, ?_⟩
  exact approximate_fixed_point_from_labelled_geometric_small_simplex
    (f := f) (hff := hff) (C := C)
    (δ := ((1 : ℝ) / (N : ℝ))) (η := η)
    hmesh hcont hC x₀ hx₀C

theorem exists_supnorm_approx_fixed_point_from_geometric_grid_sperner
    {d N : ℕ} [NeZero N]
    (P : BarycentricFreudenthal.GeometricGridSpernerForBrouwerPackage d N)
    (f : StdSimplex d → StdSimplex d)
    (hff : FixedPointFree f)
    (missing : Fin (d + 1))
    {η : ℝ}
    (hη : 0 ≤ η)
    (hcont :
      StdSimplex.MapCoordCloseOn f ((1 : ℝ) / (N : ℝ)) η) :
    ∃ x₀ : BarycentricFreudenthal.SimplexGrid d N,
      StdSimplex.ApproxFixedPoint
        f
        (stdSimplexOfSimplexGrid x₀)
        ((Fintype.card (Fin (d + 1)) : ℝ) *
          (((1 : ℝ) / (N : ℝ)) + η)) := by
  classical
  rcases exists_approximate_fixed_point_from_geometric_grid_sperner
      (P := P) (f := f) (hff := hff) (missing := missing)
      (η := η) hcont with
    ⟨x₀, hupper⟩
  refine ⟨x₀, ?_⟩
  apply StdSimplex.approxFixedPoint_of_forall_upper
  · have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    exact add_nonneg (div_nonneg zero_le_one hNpos.le) hη
  · intro i
    linarith [hupper i]

/--
Availability of concrete grid-Sperner packages at arbitrarily fine mesh.

This isolates the remaining finite triangulation construction needed by the
later Brouwer proof.
-/
structure GridSpernerPackagesArbitrarilyFine (d : ℕ) : Prop where
  exists_package_le :
    ∀ δ εmesh : ℝ, 0 < δ → 0 < εmesh →
      ∃ N : ℕ, ∃ _hN : NeZero N,
        ∃ _P : BarycentricFreudenthal.GridSpernerForBrouwerPackage d N,
          ((1 : ℝ) / (N : ℝ)) ≤ δ ∧
          ((Fintype.card (Fin (d + 1)) : ℝ) *
            ((1 : ℝ) / (N : ℝ))) < εmesh

/--
Availability of canonical geometric grid-Sperner packages at arbitrarily fine
mesh.  This mirrors `GridSpernerPackagesArbitrarilyFine`, but uses the
theorem-facing `GeometricGridCell` package.
-/
structure GeometricGridSpernerPackagesArbitrarilyFine (d : ℕ) : Prop where
  exists_package_le :
    ∀ δ εmesh : ℝ, 0 < δ → 0 < εmesh →
      ∃ N : ℕ, ∃ _hN : NeZero N,
        ∃ _P : BarycentricFreudenthal.GeometricGridSpernerForBrouwerPackage d N,
          ((1 : ℝ) / (N : ℝ)) ≤ δ ∧
          ((Fintype.card (Fin (d + 1)) : ℝ) *
            ((1 : ℝ) / (N : ℝ))) < εmesh

theorem hasApproxFixedPoints_of_grid_sperner {d : ℕ}
    (packages : GridSpernerPackagesArbitrarilyFine d)
    (f : StdSimplex d → StdSimplex d)
    (hff : FixedPointFree f)
    (hmod : StdSimplex.HasVanishingCoordinateModulus f) :
    StdSimplex.HasArbitrarilyGoodApproxFixedPoints f := by
  classical
  intro ε hε
  rcases hmod ε hε with ⟨δ, η, hδpos, hηnonneg, herr, hcontδ⟩
  have honepos : (0 : ℝ) < 1 := by norm_num
  rcases packages.exists_package_le δ 1 hδpos honepos with
    ⟨N, hN, P, hmesh_le, _hmesh_small⟩
  letI : NeZero N := hN
  have hcontN :
      StdSimplex.MapCoordCloseOn f ((1 : ℝ) / (N : ℝ)) η :=
    StdSimplex.MapCoordCloseOn.mono hmesh_le hcontδ
  let missing : Fin (d + 1) := ⟨0, Nat.succ_pos d⟩
  rcases exists_supnorm_approx_fixed_point_from_grid_sperner
      (P := P) (f := f) (hff := hff) (missing := missing)
      (η := η) hηnonneg hcontN with
    ⟨x₀, happrox⟩
  refine ⟨stdSimplexOfSimplexGrid x₀, ?_⟩
  have hcard_nonneg :
      0 ≤ (Fintype.card (Fin (d + 1)) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin (d + 1)))
  have hsum_le :
      ((1 : ℝ) / (N : ℝ)) + η ≤ δ + η := by
    linarith
  have herrN :
      ((Fintype.card (Fin (d + 1)) : ℝ) *
          (((1 : ℝ) / (N : ℝ)) + η)) < ε := by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hsum_le hcard_nonneg)
      herr
  intro i
  exact (happrox i).trans herrN.le

theorem hasApproxFixedPoints_of_geometric_grid_sperner {d : ℕ}
    (packages : GeometricGridSpernerPackagesArbitrarilyFine d)
    (f : StdSimplex d → StdSimplex d)
    (hff : FixedPointFree f)
    (hmod : StdSimplex.HasVanishingCoordinateModulus f) :
    StdSimplex.HasArbitrarilyGoodApproxFixedPoints f := by
  classical
  intro ε hε
  rcases hmod ε hε with ⟨δ, η, hδpos, hηnonneg, herr, hcontδ⟩
  have honepos : (0 : ℝ) < 1 := by norm_num
  rcases packages.exists_package_le δ 1 hδpos honepos with
    ⟨N, hN, P, hmesh_le, _hmesh_small⟩
  letI : NeZero N := hN
  have hcontN :
      StdSimplex.MapCoordCloseOn f ((1 : ℝ) / (N : ℝ)) η :=
    StdSimplex.MapCoordCloseOn.mono hmesh_le hcontδ
  let missing : Fin (d + 1) := ⟨0, Nat.succ_pos d⟩
  rcases exists_supnorm_approx_fixed_point_from_geometric_grid_sperner
      (P := P) (f := f) (hff := hff) (missing := missing)
      (η := η) hηnonneg hcontN with
    ⟨x₀, happrox⟩
  refine ⟨stdSimplexOfSimplexGrid x₀, ?_⟩
  have hcard_nonneg :
      0 ≤ (Fintype.card (Fin (d + 1)) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin (d + 1)))
  have hsum_le :
      ((1 : ℝ) / (N : ℝ)) + η ≤ δ + η := by
    linarith
  have herrN :
      ((Fintype.card (Fin (d + 1)) : ℝ) *
          (((1 : ℝ) / (N : ℝ)) + η)) < ε := by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hsum_le hcard_nonneg)
      herr
  intro i
  exact (happrox i).trans herrN.le

theorem fixedPoint_of_convergent_approxFixedPoints {d : ℕ}
    (f : StdSimplex d → StdSimplex d)
    (hseqcont : StdSimplex.SequentialContinuous f)
    (xseq : ℕ → StdSimplex d)
    (errors : ℕ → ℝ)
    (_herr_nonneg : ∀ n, 0 ≤ errors n)
    (herr_tendsto_zero :
      ∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, ∀ n ≥ N₀, errors n ≤ ε)
    (happrox :
      ∀ n, StdSimplex.ApproxFixedPoint f (xseq n) (errors n))
    (xstar : StdSimplex d)
    (hconv :
      ∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ,
          ∀ n ≥ N₀,
            StdSimplex.BarySupDistLe (xseq n) xstar ε) :
    f xstar = xstar := by
  classical
  apply Subtype.ext
  funext i
  apply StdSimplex.real_eq_of_forall_abs_sub_le
  intro ε hε
  have hthird_pos : 0 < ε / 3 := by linarith
  rcases hseqcont xseq xstar hconv (ε / 3) hthird_pos with
    ⟨Nf, hNf⟩
  rcases hconv (ε / 3) hthird_pos with ⟨Nx, hNx⟩
  rcases herr_tendsto_zero (ε / 3) hthird_pos with ⟨Ne, hNe⟩
  let n₀ : ℕ := max Nf (max Nx Ne)
  have hn_f : n₀ ≥ Nf := Nat.le_max_left Nf (max Nx Ne)
  have hn_x : n₀ ≥ Nx :=
    le_trans (Nat.le_max_left Nx Ne) (Nat.le_max_right Nf (max Nx Ne))
  have hn_e : n₀ ≥ Ne :=
    le_trans (Nat.le_max_right Nx Ne) (Nat.le_max_right Nf (max Nx Ne))
  have hf_raw := hNf n₀ hn_f i
  have hf_close :
      |(f xstar).coord i - (f (xseq n₀)).coord i| ≤ ε / 3 := by
    simpa [abs_sub_comm] using hf_raw
  have hx_close : |(xseq n₀).coord i - xstar.coord i| ≤ ε / 3 :=
    hNx n₀ hn_x i
  have herr_small : errors n₀ ≤ ε / 3 :=
    hNe n₀ hn_e
  have happ_close :
      |(f (xseq n₀)).coord i - (xseq n₀).coord i| ≤ ε / 3 :=
    le_trans (happrox n₀ i) herr_small
  have hf_bounds := abs_le.mp hf_close
  have ha_bounds := abs_le.mp happ_close
  have hx_bounds := abs_le.mp hx_close
  have hdecomp :
      (f xstar).coord i - xstar.coord i =
        ((f xstar).coord i - (f (xseq n₀)).coord i)
        + ((f (xseq n₀)).coord i - (xseq n₀).coord i)
        + ((xseq n₀).coord i - xstar.coord i) := by
    ring
  apply abs_le.mpr
  constructor
  · change -ε ≤ (f xstar).coord i - xstar.coord i
    rw [hdecomp]
    calc
      -ε = -(ε / 3) + -(ε / 3) + -(ε / 3) := by ring
      _ ≤ ((f xstar).coord i - (f (xseq n₀)).coord i)
          + ((f (xseq n₀)).coord i - (xseq n₀).coord i)
          + ((xseq n₀).coord i - xstar.coord i) := by
            linarith [hf_bounds.1, ha_bounds.1, hx_bounds.1]
  · change (f xstar).coord i - xstar.coord i ≤ ε
    rw [hdecomp]
    calc
      ((f xstar).coord i - (f (xseq n₀)).coord i)
          + ((f (xseq n₀)).coord i - (xseq n₀).coord i)
          + ((xseq n₀).coord i - xstar.coord i)
          ≤ ε / 3 + ε / 3 + ε / 3 := by
            linarith [hf_bounds.2, ha_bounds.2, hx_bounds.2]
      _ = ε := by ring

theorem fixedPoint_of_arbitrarilyGoodApproxFixedPoints {d : ℕ}
    (hcompact : StdSimplex.SequentialCompactness d)
    (f : StdSimplex d → StdSimplex d)
    (hseqcont : StdSimplex.SequentialContinuous f)
    (happrox : StdSimplex.HasArbitrarilyGoodApproxFixedPoints f) :
    ∃ x : StdSimplex d, f x = x := by
  classical
  let err : ℕ → ℝ := fun n => (1 : ℝ) / ((n : ℝ) + 1)
  have herr_pos : ∀ n, 0 < err n := by
    intro n
    dsimp [err]
    positivity
  let xseq : ℕ → StdSimplex d := fun n =>
    Classical.choose (happrox (err n) (herr_pos n))
  have hxseq_approx :
      ∀ n, StdSimplex.ApproxFixedPoint f (xseq n) (err n) := by
    intro n
    exact Classical.choose_spec (happrox (err n) (herr_pos n))
  rcases hcompact xseq with ⟨xstar, φ, hφmono, hconv⟩
  have hφ_ge : ∀ n, n ≤ φ n := by
    intro n
    have h := hφmono.add_le_nat n 0
    have hleft : n ≤ n + φ 0 := Nat.le_add_right n (φ 0)
    exact le_trans hleft (by simpa using h)
  have herr_nonneg_sub : ∀ n, 0 ≤ err (φ n) := by
    intro n
    exact (herr_pos (φ n)).le
  have herr_tendsto_zero_sub :
      ∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, ∀ n ≥ N₀, err (φ n) ≤ ε := by
    intro ε hε
    rcases exists_nat_one_div_lt hε with ⟨N₀, hN₀⟩
    refine ⟨N₀, ?_⟩
    intro n hn
    have hNle : N₀ ≤ φ n := le_trans hn (hφ_ge n)
    have hmono :
        err (φ n) ≤ err N₀ := by
      dsimp [err]
      simpa using (Nat.one_div_le_one_div (α := ℝ) hNle)
    exact hmono.trans hN₀.le
  have happrox_sub :
      ∀ n, StdSimplex.ApproxFixedPoint f (xseq (φ n)) (err (φ n)) := by
    intro n
    exact hxseq_approx (φ n)
  refine ⟨xstar, ?_⟩
  exact fixedPoint_of_convergent_approxFixedPoints
    f hseqcont
    (fun n => xseq (φ n))
    (fun n => err (φ n))
    herr_nonneg_sub
    herr_tendsto_zero_sub
    happrox_sub
    xstar
    hconv

theorem brouwer_conditional_from_grid_sperner {d : ℕ}
    (packages : GridSpernerPackagesArbitrarilyFine d)
    (hcompact : StdSimplex.SequentialCompactness d)
    (f : StdSimplex d → StdSimplex d)
    (hseqcont : StdSimplex.SequentialContinuous f)
    (hmod : StdSimplex.HasVanishingCoordinateModulus f) :
    ∃ x : StdSimplex d, f x = x := by
  classical
  by_cases hfixed : ∃ x : StdSimplex d, f x = x
  · exact hfixed
  · have hff : FixedPointFree f := by
      intro x hx
      exact hfixed ⟨x, hx⟩
    have happrox :
        StdSimplex.HasArbitrarilyGoodApproxFixedPoints f :=
      hasApproxFixedPoints_of_grid_sperner packages f hff hmod
    exact fixedPoint_of_arbitrarilyGoodApproxFixedPoints
      hcompact f hseqcont happrox

theorem brouwer_conditional_from_geometric_grid_sperner {d : ℕ}
    (packages : GeometricGridSpernerPackagesArbitrarilyFine d)
    (hcompact : StdSimplex.SequentialCompactness d)
    (f : StdSimplex d → StdSimplex d)
    (hseqcont : StdSimplex.SequentialContinuous f)
    (hmod : StdSimplex.HasVanishingCoordinateModulus f) :
    ∃ x : StdSimplex d, f x = x := by
  classical
  by_cases hfixed : ∃ x : StdSimplex d, f x = x
  · exact hfixed
  · have hff : FixedPointFree f := by
      intro x hx
      exact hfixed ⟨x, hx⟩
    have happrox :
        StdSimplex.HasArbitrarilyGoodApproxFixedPoints f :=
      hasApproxFixedPoints_of_geometric_grid_sperner packages f hff hmod
    exact fixedPoint_of_arbitrarilyGoodApproxFixedPoints
      hcompact f hseqcont happrox

theorem brouwer_fixed_point_conditional {d : ℕ}
    (packages : GridSpernerPackagesArbitrarilyFine d)
    (hcompact : StdSimplex.SequentialCompactness d)
    (f : StdSimplex d → StdSimplex d)
    (hseqcont : StdSimplex.SequentialContinuous f)
    (hmod : StdSimplex.HasVanishingCoordinateModulus f) :
    ∃ x : StdSimplex d, f x = x :=
  brouwer_conditional_from_grid_sperner
    packages hcompact f hseqcont hmod

theorem brouwer_fixed_point_conditional_of_uniformCoordinateModulus {d : ℕ}
    (packages : GridSpernerPackagesArbitrarilyFine d)
    (hcompact : StdSimplex.SequentialCompactness d)
    (f : StdSimplex d → StdSimplex d)
    (hmod : StdSimplex.UniformCoordinateModulus f) :
    ∃ x : StdSimplex d, f x = x :=
  brouwer_fixed_point_conditional
    packages
    hcompact
    f
    (StdSimplex.sequentialContinuous_of_uniformCoordinateModulus hmod)
    (StdSimplex.hasVanishingCoordinateModulus_of_uniformCoordinateModulus hmod)

structure BrouwerSpernerHypotheses (d : ℕ) : Prop where
  gridPackages : GridSpernerPackagesArbitrarilyFine d
  sequentialCompactness : StdSimplex.SequentialCompactness d

theorem brouwer_fixed_point_from_sperner_hypotheses {d : ℕ}
    (H : BrouwerSpernerHypotheses d)
    (f : StdSimplex d → StdSimplex d)
    (hmod : StdSimplex.UniformCoordinateModulus f) :
    ∃ x : StdSimplex d, f x = x :=
  brouwer_fixed_point_conditional_of_uniformCoordinateModulus
    H.gridPackages
    H.sequentialCompactness
    f
    hmod

theorem brouwer_simplex_from_sperner {d : ℕ}
    (H : BrouwerSpernerHypotheses d)
    (f : StdSimplex d → StdSimplex d)
    (hmod : StdSimplex.UniformCoordinateModulus f) :
    ∃ x : StdSimplex d, f x = x :=
  brouwer_fixed_point_from_sperner_hypotheses H f hmod

theorem brouwer_simplex_from_sperner_of_uniformCoordinateContinuous {d : ℕ}
    (H : BrouwerSpernerHypotheses d)
    (f : StdSimplex d → StdSimplex d)
    (hf : StdSimplex.UniformCoordinateContinuous f) :
    ∃ x : StdSimplex d, f x = x :=
  brouwer_simplex_from_sperner
    H f
    (StdSimplex.uniformCoordinateModulus_of_uniformCoordinateContinuous hf)

theorem brouwer_simplex_from_sperner_of_uniformCoordinateContinuous_compact
    {d : ℕ}
    [CompactSpace (StdSimplex d)]
    (packages : GridSpernerPackagesArbitrarilyFine d)
    (f : StdSimplex d → StdSimplex d)
    (hf : StdSimplex.UniformCoordinateContinuous f) :
    ∃ x : StdSimplex d, f x = x :=
  brouwer_simplex_from_sperner_of_uniformCoordinateContinuous
    ⟨packages, StdSimplex.sequentialCompactness_of_compactSpace⟩
    f hf

theorem brouwer_simplex_from_sperner_of_continuous_compact
    {d : ℕ}
    [CompactSpace (StdSimplex d)]
    (packages : GridSpernerPackagesArbitrarilyFine d)
    (f : StdSimplex d → StdSimplex d)
    (hf : Continuous f) :
    ∃ x : StdSimplex d, f x = x :=
  brouwer_simplex_from_sperner_of_uniformCoordinateContinuous_compact
    packages f
    (StdSimplex.uniformCoordinateContinuous_of_continuous_compact hf)

theorem brouwer_simplex_from_sperner_of_continuous
    {d : ℕ}
    (packages : GridSpernerPackagesArbitrarilyFine d)
    (f : StdSimplex d → StdSimplex d)
    (hf : Continuous f) :
    ∃ x : StdSimplex d, f x = x :=
  brouwer_simplex_from_sperner_of_continuous_compact
    packages f hf

theorem brouwer_simplex_from_geometric_sperner_of_continuous {d : ℕ}
    [CompactSpace (StdSimplex d)]
    (packages : GeometricGridSpernerPackagesArbitrarilyFine d)
    (f : StdSimplex d → StdSimplex d)
    (hf : Continuous f) :
    ∃ x : StdSimplex d, f x = x := by
  exact brouwer_conditional_from_geometric_grid_sperner
    packages
    StdSimplex.sequentialCompactness_of_compactSpace
    f
    (StdSimplex.sequentialContinuous_of_uniformCoordinateModulus
      (StdSimplex.uniformCoordinateModulus_of_uniformCoordinateContinuous
        (StdSimplex.uniformCoordinateContinuous_of_continuous_compact hf)))
    (StdSimplex.hasVanishingCoordinateModulus_of_uniformCoordinateModulus
      (StdSimplex.uniformCoordinateModulus_of_uniformCoordinateContinuous
        (StdSimplex.uniformCoordinateContinuous_of_continuous_compact hf)))

/-
Status of the Brouwer route:

`brouwer_simplex_from_sperner_of_continuous` proves Brouwer for the standard
simplex from the older compatibility package hypothesis, while
`brouwer_simplex_from_geometric_sperner_of_continuous` is the parallel
canonical endpoint over theorem-facing geometric cells.

1. `GridSpernerPackagesArbitrarilyFine d`
2. `GeometricGridSpernerPackagesArbitrarilyFine d`

The second is the intended canonical remaining hypothesis: it contains exactly
the geometric-cell triangulation facts needed by the finite Sperner argument.

This file now discharges the analytic side by:

* proving `CompactSpace (StdSimplex d)` from mathlib's compact standard
  simplex;
* deriving the custom uniform coordinate-continuity assumption from ordinary
  `Continuous f` on the compact simplex.

The non-analytic side — the finite Sperner engine feeding this chain — is supplied
unconditionally by the sorted-subset Freudenthal route in `SpernerBrouwer.lean`, which
bypasses the geometric grid packages.
-/

end Brouwer
end SpernerFreudenthal
end EconLib
