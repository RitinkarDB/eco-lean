import EcoLean.GameTheory.MathLanguage.Sperner.Kuhn.BoundaryOdd

/-!
# Freudenthal / Kuhn triangulation of the barycentric simplex grid — public barrel

This file is the **public barrel** for the Freudenthal / Kuhn triangulation of the simplex grid and
its finite Sperner theorem.  The cells are encoded by maximal sorted `k`-subset collections; the
results are exported under the canonical `kuhn_*` names and the equivalent `freudenthal_*`
aliases (the same theorems under the Freudenthal name).  Importing this file (re)exports the entire
chain, which lives in the split modules under `Sperner/Kuhn/` (dependency order):

* `Kuhn/KSubsetCombinatorics.lean` — pure `KSubset` / sorted-collection combinatorics + deletion.
* `Kuhn/Cells.lean`                — sorted geometric cells/facets, the completions API, and the
                                        local-flip door property (`incidentCells_card_eq_one_or_two`).
* `Kuhn/Incidence.lean`            — the incidence classification: a facet is shared by one cell ⟺
                                        boundary, two ⟺ interior.
* `Kuhn/Mesh.lean`                 — the realisation-mesh bound `realise_barySupDistLe`.
* `Kuhn/Certificate.lean`          — the `Sperner.SpernerTriangulationCertificate` + `local_parity`.
* `Kuhn/BoundaryOdd.lean`          — `boundary_odd` (deletion bijection, dimension induction,
                                        1-dim base case `OneDimSperner`).
* `Kuhn/Audit.lean`                — build-time `#check`/`#print axioms` guardrail (leaf).
* `Kuhn/LocalAudit.lean`           — local-only `decide` sanity witnesses (NOT imported here).

This file itself holds only the unconditional finite Sperner theorems (the `kuhn_*` names) and their
`freudenthal_*` aliases.  The Brouwer bridge — including `Brouwer.brouwer_simplex` — lives in
`SpernerBrouwer.lean`.
-/

namespace EcoLean
namespace SpernerFreudenthal
namespace BarycentricFreudenthal

open Finset

/-! ### The finite Sperner theorem (base case discharged)

`OneDimSperner.oneDimensional_base` discharges the `hbase` hypothesis everywhere, making the
dimension induction, `boundary_odd`, and the Sperner output unconditional. -/

open scoped Classical in
/-- **The Sperner parity.**  For every Sperner colouring of the dimension-`d`
(`1 ≤ d`) Freudenthal grid, the number of fully-labelled top cells is odd. -/
theorem kuhn_fullyLabeled_count_odd {d : ℕ} (hd : 1 ≤ d) :
    ∀ (N : ℕ) (L : SimplexGrid d N → Fin (d + 1)), GridIsSperner L →
      Odd ((Finset.univ : Finset (KuhnGeometricGridCell d N)).filter
        (fun C : KuhnGeometricGridCell d N => Sperner.FullyLabeled L C.vertices)).card :=
  kuhn_fullyLabeled_count_odd_of_base OneDimSperner.oneDimensional_base hd

/-- **`boundary_odd`.**  The boundary double count for the Freudenthal certificate. -/
theorem kuhn_boundary_odd {d N : ℕ} (hd : 2 ≤ d)
    (L : SimplexGrid d N → Fin (d + 1)) (hSperner : GridIsSperner L) (missing : Fin (d + 1)) :
    Odd ((kuhnTriangulationCertificate hd).boundaryRelevantFacets L missing).card :=
  kuhn_boundary_odd_of_base OneDimSperner.oneDimensional_base hd L hSperner missing

/-- **The finite Sperner theorem for the Freudenthal triangulation.**  For every Sperner
colouring (`2 ≤ d`), a fully-labelled (rainbow) top cell exists.  This is the combinatorial
fixed-point engine feeding Brouwer/Kakutani. -/
theorem kuhn_exists_fullyLabeled {d N : ℕ} (hd : 2 ≤ d)
    (color : SimplexGrid d N → Fin (d + 1)) (hSperner : GridIsSperner color)
    (missing : Fin (d + 1)) :
    ∃ C : KuhnGeometricGridCell d N, Sperner.FullyLabeled color C.vertices :=
  kuhn_exists_fullyLabeled_of_base OneDimSperner.oneDimensional_base hd color hSperner missing

/-- The Freudenthal triangulation as a full labelled `Sperner.SpernerCertificate`
(every field discharged: `triangulation`, `local_parity`, and `boundary_odd`). -/
noncomputable def kuhnSpernerCertificate {d N : ℕ} (hd : 2 ≤ d)
    (color : SimplexGrid d N → Fin (d + 1)) (hSperner : GridIsSperner color) (missing : Fin (d + 1)) :
    Sperner.SpernerCertificate (Fin (d + 1)) (SimplexGrid d N)
      (KuhnGeometricGridCell d N) (KuhnGeometricGridFacet d N) :=
  kuhnSpernerCertificate_of_boundaryOdd hd color missing
    (kuhn_boundary_odd hd color hSperner missing)

/-! ### Public API — `Freudenthal` aliases

The sorted-`k`-subset cells implement the standard **Freudenthal / Kuhn triangulation** of the
barycentric simplex grid.  The `kuhn_*` theorems above are the canonical names; the
`freudenthal_*` aliases below give the same results under the Freudenthal name. -/

/-- **The finite Sperner theorem** (`kuhn_sperner`): every Sperner colouring of `N • Δ^d` (`2 ≤ d`)
has a fully-labelled top cell. -/
alias kuhn_sperner := kuhn_exists_fullyLabeled

/-- The Freudenthal triangulation as an abstract `Sperner.SpernerTriangulationCertificate`. -/
alias freudenthalTriangulationCertificate := kuhnTriangulationCertificate
/-- The Freudenthal triangulation as a full labelled `Sperner.SpernerCertificate`. -/
alias freudenthalSpernerCertificate := kuhnSpernerCertificate
/-- Boundary oddness for the Freudenthal Sperner certificate. -/
alias freudenthal_boundary_odd := kuhn_boundary_odd
/-- **The finite Sperner theorem for the Freudenthal triangulation**: a fully-labelled cell exists. -/
alias freudenthal_sperner := kuhn_exists_fullyLabeled
/-- The finite Sperner theorem (fully-labelled cell), explicit form. -/
alias freudenthal_exists_fullyLabeled := kuhn_exists_fullyLabeled
/-- An interior facet of the Freudenthal triangulation is shared by exactly two cells. -/
alias freudenthal_interior_facet_two_cells := kuhn_interior_facet_two_cells

/-! The local incidence classification, the Sperner certificate, `local_parity`, and `boundary_odd`
are all unconditional; their construction lives in the split modules `Sperner/Kuhn/{KSubsetCombinatorics,
Cells, Incidence, Mesh, Certificate, BoundaryOdd}.lean` (see each module docstring).  Small-case `decide`
sanity audits live in the local-only `Kuhn/LocalAudit.lean`. -/
/-! ## Status — Sperner → Brouwer, complete and unconditional

End-to-end, with no hypotheses beyond `2 ≤ d` / `Continuous f`:
`kuhnSpernerCertificate` → `kuhn_exists_fullyLabeled` (alias `kuhn_sperner`)
→ `Brouwer.exists_supnorm_approx_fixed_point_sorted` (alias `kuhn_approx_fixed_point`)
→ `Brouwer.brouwer_simplex_sorted` (alias `brouwer_simplex`).  `N = 0` is vacuous
(`not_gridIsSperner_zero_mesh`).  Future, non-blocking: generalise to `1 ≤ d` / `d = 0`; Kakutani;
a `ContinuousMap`-bundled restatement. -/

end BarycentricFreudenthal
end SpernerFreudenthal
end EcoLean
