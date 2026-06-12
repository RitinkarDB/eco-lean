import EcoLean.GameTheory.MathLanguage.Sperner.Kuhn.Incidence

/-! Mesh bound for realised sorted-Freudenthal cells: the two vertices of a cell realise within
barycentric sup-distance `1/N` — the analytic brick of the Sperner → Brouwer bridge. -/

namespace EcoLean
namespace SpernerFreudenthal
namespace BarycentricFreudenthal
open Finset
namespace KuhnGeometricGridCell
/-- **THE BROUWER-BRIDGE MESH BOUND.**  The barycentric realisations of any two vertices of a sorted
Freudenthal cell are within sup-distance `1/N` — the first analytic brick of the Sperner→Brouwer bridge
(mirrors `GridSmallSimplex.mesh_le_of_pairwise_coord_diff_le` for the live sorted cells).  Scales the
unit coordinate mesh (`mesh`, integer coordinates differ by ≤ 1) by `1/N`. -/
theorem realise_barySupDistLe {d N : ℕ} [NeZero N]
    (C : KuhnGeometricGridCell d N)
    {x y : SimplexGrid d N} (hx : x ∈ C.vertices) (hy : y ∈ C.vertices) :
    BarySupDistLe (realiseSimplexGrid x) (realiseSimplexGrid y) ((1 : ℝ) / (N : ℝ)) := by
  intro i
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have hNnat : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast hNnat
  have hi : Int.natAbs ((x.1 i : ℤ) - (y.1 i : ℤ)) ≤ 1 := C.mesh x hx y hy i
  have hiZ : |((x.1 i : ℤ) - (y.1 i : ℤ))| ≤ (1 : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hi
  have hreal : |(x.1 i : ℝ) - (y.1 i : ℝ)| ≤ (1 : ℝ) := by
    have hcast : (((x.1 i : ℤ) - (y.1 i : ℤ) : ℤ) : ℝ) = (x.1 i : ℝ) - (y.1 i : ℝ) := by norm_num
    have := (by exact_mod_cast hiZ :
      |(((x.1 i : ℤ) - (y.1 i : ℤ) : ℤ) : ℝ)| ≤ (1 : ℝ))
    simpa [hcast] using this
  calc
    |realiseSimplexGrid x i - realiseSimplexGrid y i|
        = |(x.1 i : ℝ) - (y.1 i : ℝ)| / (N : ℝ) := by
          simp only [realiseSimplexGrid]
          rw [← sub_div, abs_div, abs_of_pos hNpos]
    _ ≤ (1 : ℝ) / (N : ℝ) := div_le_div_of_nonneg_right hreal hNpos.le
end KuhnGeometricGridCell
end BarycentricFreudenthal
end SpernerFreudenthal
end EcoLean
