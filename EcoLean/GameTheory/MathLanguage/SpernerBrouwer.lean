import EcoLean.GameTheory.MathLanguage.BrouwerFreudenthal
import EcoLean.GameTheory.MathLanguage.Sperner.KuhnGrid

/-!
# Sperner → Brouwer bridge through the Kuhn cells

This file routes the approximate-fixed-point step of the analytic Brouwer chain
(`BrouwerFreudenthal.lean`) through the Kuhn cells, whose Sperner
output `kuhn_exists_fullyLabeled` is unconditional (`2 ≤ d`); the resulting approximate
fixed point therefore needs no grid-Sperner package hypothesis.  The standard analytic steps that
follow — arbitrarily-good approximate fixed points as `N → ∞`, then the compactness limit — give
`brouwer_simplex_sorted`: every continuous self-map of `Δ^d` (`2 ≤ d`) has a fixed point.
-/

namespace EcoLean
namespace SpernerFreudenthal
namespace Brouwer

open BarycentricFreudenthal

/-- **Sorted-cell barycentric closeness.**  Any two vertices of a Kuhn cell realise within
`StdSimplex.BarySupDistLe (1/N)`, lifting `realise_barySupDistLe` to the `StdSimplex` sup-distance. -/
theorem sorted_stdSimplex_closeness {d N : ℕ} [NeZero N]
    (C : KuhnGeometricGridCell d N)
    {x y : SimplexGrid d N} (hx : x ∈ C.vertices) (hy : y ∈ C.vertices) :
    StdSimplex.BarySupDistLe (stdSimplexOfSimplexGrid x) (stdSimplexOfSimplexGrid y)
      ((1 : ℝ) / (N : ℝ)) := by
  intro i
  simpa [StdSimplex.BarySupDistLe, StdSimplex.coord, stdSimplexOfSimplexGrid]
    using C.realise_barySupDistLe hx hy i

/-- A fully-labelled sorted cell (for the Brouwer decrease-label) has a vertex with every label. -/
theorem exists_vertex_with_label_sorted {d N : ℕ} [NeZero N]
    {f : StdSimplex d → StdSimplex d} {hff : FixedPointFree f}
    {C : KuhnGeometricGridCell d N}
    (hC : Sperner.FullyLabeled (brouwerGridLabel f hff) C.vertices)
    (i : Fin (d + 1)) :
    ∃ x ∈ C.vertices, brouwerGridLabel f hff x = i := by
  classical
  have hi : i ∈ Sperner.labelsOn (brouwerGridLabel f hff) C.vertices := hC (Finset.mem_univ i)
  exact (Sperner.mem_labelsOn_iff (brouwerGridLabel f hff) C.vertices i).mp hi

/-- At the label-`i` vertex of a fully-labelled sorted cell, `f` strictly decreases coordinate `i`. -/
theorem exists_vertex_with_decrease_at_sorted {d N : ℕ} [NeZero N]
    {f : StdSimplex d → StdSimplex d} {hff : FixedPointFree f}
    {C : KuhnGeometricGridCell d N}
    (hC : Sperner.FullyLabeled (brouwerGridLabel f hff) C.vertices)
    (i : Fin (d + 1)) :
    ∃ x ∈ C.vertices, IsBrouwerDecreaseLabel f (stdSimplexOfSimplexGrid x) i := by
  classical
  obtain ⟨x, hxC, hxlabel⟩ := exists_vertex_with_label_sorted (hff := hff) (C := C) hC i
  refine ⟨x, hxC, ?_⟩
  simpa [hxlabel] using brouwerGridLabel_spec f hff x

/-- **The per-coordinate upper bound.**  At any base vertex `x₀` of a fully-labelled sorted cell,
with realisation mesh `1/N` and coordinate modulus `η`, `f` increases each coordinate by at most
`1/N + η`. -/
theorem approx_fixed_point_from_labelled_sorted_cell {d N : ℕ} [NeZero N]
    {f : StdSimplex d → StdSimplex d} {hff : FixedPointFree f}
    {C : KuhnGeometricGridCell d N} {η : ℝ}
    (hcont : StdSimplex.MapCoordCloseOn f ((1 : ℝ) / (N : ℝ)) η)
    (hC : Sperner.FullyLabeled (brouwerGridLabel f hff) C.vertices)
    (x₀ : SimplexGrid d N) (hx₀ : x₀ ∈ C.vertices) :
    ∀ i : Fin (d + 1),
      (f (stdSimplexOfSimplexGrid x₀)).coord i ≤
        (stdSimplexOfSimplexGrid x₀).coord i + ((1 : ℝ) / (N : ℝ)) + η := by
  classical
  intro i
  obtain ⟨xi, hxiC, hdec⟩ := exists_vertex_with_decrease_at_sorted (hff := hff) (C := C) hC i
  have hclose_x : StdSimplex.BarySupDistLe (stdSimplexOfSimplexGrid xi) (stdSimplexOfSimplexGrid x₀)
      ((1 : ℝ) / (N : ℝ)) := sorted_stdSimplex_closeness C hxiC hx₀
  have hclose_f := hcont (stdSimplexOfSimplexGrid xi) (stdSimplexOfSimplexGrid x₀) hclose_x i
  have hdec' : (f (stdSimplexOfSimplexGrid xi)).coord i < (stdSimplexOfSimplexGrid xi).coord i := hdec
  have hf_bounds := abs_le.mp hclose_f
  have hx_bounds := abs_le.mp (hclose_x i)
  linarith [hdec', hf_bounds.1, hx_bounds.2]

/-- **The sorted approximate fixed point.**  For a fixed-point-free self-map of the simplex with
coordinate modulus `η` at scale `1/N` (`2 ≤ d`, `[NeZero N]`), some grid point realises an approximate
fixed point with tolerance `(d+1)·(1/N + η)`.  The fully-labelled cell is supplied by
`kuhn_exists_fullyLabeled`, so there is no grid-Sperner package hypothesis (contrast
`exists_supnorm_approx_fixed_point_from_grid_sperner`). -/
theorem exists_supnorm_approx_fixed_point_sorted {d N : ℕ} [NeZero N] (hd : 2 ≤ d)
    (f : StdSimplex d → StdSimplex d) (hff : FixedPointFree f) (missing : Fin (d + 1))
    {η : ℝ} (hη : 0 ≤ η)
    (hcont : StdSimplex.MapCoordCloseOn f ((1 : ℝ) / (N : ℝ)) η) :
    ∃ x₀ : SimplexGrid d N,
      StdSimplex.ApproxFixedPoint f (stdSimplexOfSimplexGrid x₀)
        ((Fintype.card (Fin (d + 1)) : ℝ) * (((1 : ℝ) / (N : ℝ)) + η)) := by
  classical
  obtain ⟨C, hC⟩ := kuhn_exists_fullyLabeled (N := N) hd (brouwerGridLabel (N := N) f hff)
    (brouwerGridLabel_isSperner (N := N) f hff) missing
  obtain ⟨x₀, hx₀, _⟩ :=
    exists_vertex_with_label_sorted (hff := hff) (C := C) hC ⟨0, Nat.succ_pos d⟩
  refine ⟨x₀, ?_⟩
  apply StdSimplex.approxFixedPoint_of_forall_upper
  · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    exact add_nonneg (div_nonneg zero_le_one hNpos.le) hη
  · intro i
    linarith [approx_fixed_point_from_labelled_sorted_cell (hff := hff) hcont hC x₀ hx₀ i]

/-- **Arbitrarily good approximate fixed points.**  A fixed-point-free self-map with vanishing
coordinate modulus has approximate fixed points at every tolerance.  The mesh scale `1/N` is chosen
by `exists_nat_one_div_lt` and the cell by `exists_supnorm_approx_fixed_point_sorted` (no grid
package). -/
theorem hasApproxFixedPoints_sorted {d : ℕ} (hd : 2 ≤ d)
    (f : StdSimplex d → StdSimplex d) (hff : FixedPointFree f)
    (hmod : StdSimplex.HasVanishingCoordinateModulus f) :
    StdSimplex.HasArbitrarilyGoodApproxFixedPoints f := by
  classical
  intro ε hε
  rcases hmod ε hε with ⟨δ, η, hδpos, hηnonneg, herr, hcontδ⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδpos
  haveI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
  have hmesh_le : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ δ := by push_cast; exact hn.le
  have hcontN : StdSimplex.MapCoordCloseOn f ((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) η :=
    StdSimplex.MapCoordCloseOn.mono hmesh_le hcontδ
  let missing : Fin (d + 1) := ⟨0, Nat.succ_pos d⟩
  rcases exists_supnorm_approx_fixed_point_sorted (N := n + 1) hd f hff missing hηnonneg hcontN with
    ⟨x₀, happrox⟩
  refine ⟨stdSimplexOfSimplexGrid x₀, ?_⟩
  have hcard_nonneg : 0 ≤ (Fintype.card (Fin (d + 1)) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin (d + 1)))
  have hsum_le : ((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) + η ≤ δ + η := by linarith
  have herrN :
      ((Fintype.card (Fin (d + 1)) : ℝ) * (((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) + η)) < ε :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsum_le hcard_nonneg) herr
  intro i
  exact (happrox i).trans herrN.le

/-- **The conditional fixed point.**  Given sequential compactness, sequential continuity, and a
vanishing coordinate modulus, `f` has a fixed point (via the sorted approximate-fixed-point route). -/
theorem brouwer_conditional_sorted {d : ℕ} (hd : 2 ≤ d)
    (hcompact : StdSimplex.SequentialCompactness d)
    (f : StdSimplex d → StdSimplex d)
    (hseqcont : StdSimplex.SequentialContinuous f)
    (hmod : StdSimplex.HasVanishingCoordinateModulus f) :
    ∃ x : StdSimplex d, f x = x := by
  classical
  by_cases hfixed : ∃ x : StdSimplex d, f x = x
  · exact hfixed
  · have hff : FixedPointFree f := fun x hx => hfixed ⟨x, hx⟩
    exact fixedPoint_of_arbitrarilyGoodApproxFixedPoints hcompact f hseqcont
      (hasApproxFixedPoints_sorted hd f hff hmod)

/-- **Brouwer's fixed-point theorem for the standard simplex.**  Every continuous self-map of the
standard `d`-simplex (`2 ≤ d`) has a fixed point.  Sequential
compactness is discharged by `sequentialCompactness_of_compactSpace` + `instCompactSpace`; sequential
continuity and the vanishing modulus come from `Continuous f` on the compact simplex; the combinatorial
fixed-point engine is the unconditional sorted Sperner theorem. -/
theorem brouwer_simplex_sorted {d : ℕ} (hd : 2 ≤ d)
    (f : StdSimplex d → StdSimplex d) (hf : Continuous f) :
    ∃ x : StdSimplex d, f x = x := by
  have hucc : StdSimplex.UniformCoordinateContinuous f :=
    StdSimplex.uniformCoordinateContinuous_of_continuous_compact hf
  have hucm : StdSimplex.UniformCoordinateModulus f :=
    StdSimplex.uniformCoordinateModulus_of_uniformCoordinateContinuous hucc
  exact brouwer_conditional_sorted hd
    StdSimplex.sequentialCompactness_of_compactSpace
    f
    (StdSimplex.sequentialContinuous_of_uniformCoordinateModulus hucm)
    (StdSimplex.hasVanishingCoordinateModulus_of_uniformCoordinateModulus hucm)

/-! ### Stable public API aliases -/

/-- **Sorted approximate fixed point** (stable public name for
`exists_supnorm_approx_fixed_point_sorted`). -/
alias kuhn_approx_fixed_point := exists_supnorm_approx_fixed_point_sorted

/-- **Brouwer's fixed-point theorem for the standard simplex** (stable public name for
`brouwer_simplex_sorted`): every continuous self-map of `Δ^d` (`2 ≤ d`) has a fixed point. -/
alias brouwer_simplex := brouwer_simplex_sorted

/-! ### Canonical `Freudenthal` public names -/

/-- Approximate fixed point via the Freudenthal triangulation. -/
alias freudenthal_approx_fixed_point := exists_supnorm_approx_fixed_point_sorted
/-- **Brouwer's fixed-point theorem for the simplex, via the Freudenthal triangulation.** -/
alias brouwer_simplex_via_freudenthal := brouwer_simplex_sorted

end Brouwer
end SpernerFreudenthal
end EcoLean
