import EcoLean.Microeconomics.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Pure exchange economies

This file starts the pure-exchange side of the First Welfare Theorem
translation.  It defines aggregate allocations, feasible allocations, and
Walrasian equilibrium for a pure exchange economy.

The main theorem in this first layer is an abstract price-support result:
if prices support an allocation in the usual separating-hyperplane sense, then
the allocation is Pareto efficient.  Later files can discharge the support
assumptions from utility maximization plus local non-satiation.
-/

open scoped BigOperators

universe u v

namespace EcoLean
namespace Microeconomics

variable {Agent : Type u} {Bundle : Type v}

section Aggregates

variable [Fintype Agent] [AddCommMonoid Bundle]

/-- Aggregate an allocation by summing bundles across agents. -/
noncomputable def aggregate (X : Allocation Agent Bundle) : Bundle :=
  ∑ i : Agent, X i

@[simp] theorem aggregate_apply (X : Allocation Agent Bundle) :
    aggregate X = ∑ i : Agent, X i :=
  rfl

end Aggregates

section Exchange

variable [Fintype Agent] [AddCommMonoid Bundle] [LE Bundle]

/--
Feasibility in a pure exchange economy: every individual bundle is in the
consumption set and aggregate consumption does not exceed aggregate endowment.
-/
def ExchangeFeasible
    (consumptionSet : Set Bundle)
    (endowment : Allocation Agent Bundle)
    (X : Allocation Agent Bundle) : Prop :=
  aggregate X ≤ aggregate endowment ∧ ∀ i : Agent, X i ∈ consumptionSet

/-- The feasible-allocation set associated with a pure exchange economy. -/
def ExchangeFeasibleSet
    (consumptionSet : Set Bundle)
    (endowment : Allocation Agent Bundle) :
    Set (Allocation Agent Bundle) :=
  {X | ExchangeFeasible consumptionSet endowment X}

@[simp] theorem mem_exchangeFeasibleSet_iff
    {consumptionSet : Set Bundle}
    {endowment X : Allocation Agent Bundle} :
    X ∈ ExchangeFeasibleSet consumptionSet endowment ↔
      ExchangeFeasible consumptionSet endowment X :=
  Iff.rfl

theorem aggregate_le_endowment_of_exchangeFeasible
    {consumptionSet : Set Bundle}
    {endowment X : Allocation Agent Bundle}
    (hX : ExchangeFeasible consumptionSet endowment X) :
    aggregate X ≤ aggregate endowment :=
  hX.1

theorem mem_consumptionSet_of_exchangeFeasible
    {consumptionSet : Set Bundle}
    {endowment X : Allocation Agent Bundle}
    (hX : ExchangeFeasible consumptionSet endowment X) (i : Agent) :
    X i ∈ consumptionSet :=
  hX.2 i

end Exchange

section Equilibrium

variable [Fintype Agent] [AddCommMonoid Bundle] [LE Bundle]

/--
Walrasian equilibrium in a pure exchange economy.

`value` is the value functional induced by prices.  In the finite-dimensional
commodity-space specialization this will usually be `fun x => inner price x`.
-/
def ExchangeEquilibrium
    (consumptionSet : Set Bundle)
    (value : Bundle → ℝ)
    (endowment : Allocation Agent Bundle)
    (U : Agent → Bundle → ℝ)
    (X : Allocation Agent Bundle) : Prop :=
  ExchangeFeasible consumptionSet endowment X ∧
    ∀ i : Agent,
      X i ∈ Maximizers (U i)
        (BudgetSet value consumptionSet (value (endowment i)))

theorem feasible_of_exchangeEquilibrium
    {consumptionSet : Set Bundle}
    {value : Bundle → ℝ}
    {endowment : Allocation Agent Bundle}
    {U : Agent → Bundle → ℝ}
    {X : Allocation Agent Bundle}
    (hEq : ExchangeEquilibrium consumptionSet value endowment U X) :
    ExchangeFeasible consumptionSet endowment X :=
  hEq.1

theorem optimal_of_exchangeEquilibrium
    {consumptionSet : Set Bundle}
    {value : Bundle → ℝ}
    {endowment : Allocation Agent Bundle}
    {U : Agent → Bundle → ℝ}
    {X : Allocation Agent Bundle}
    (hEq : ExchangeEquilibrium consumptionSet value endowment U X)
    (i : Agent) :
    X i ∈ Maximizers (U i)
      (BudgetSet value consumptionSet (value (endowment i))) :=
  hEq.2 i

end Equilibrium

section PriceSupport

variable [Fintype Agent] [AddCommMonoid Bundle] [LE Bundle]

/--
Abstract price-support form of the First Welfare Theorem for pure exchange.

The assumptions say:

* `value` is monotone with respect to the aggregate resource order;
* `value` distributes over finite aggregate allocations;
* each equilibrium bundle exhausts the value of the corresponding endowment;
* every bundle weakly/strictly improving on `X i` is weakly/strictly more
  expensive.

The usual FWT proof supplies the last two bullets from utility maximization and
local non-satiation.
-/
theorem paretoEfficient_of_priceSupport_exchange
    (consumptionSet : Set Bundle)
    (value : Bundle → ℝ)
    (endowment : Allocation Agent Bundle)
    (U : Agent → Bundle → ℝ)
    (X : Allocation Agent Bundle)
    (hX : ExchangeFeasible consumptionSet endowment X)
    (hValue_mono :
      ∀ ⦃x y : Bundle⦄, x ≤ y → value x ≤ value y)
    (hValue_sum :
      ∀ A : Allocation Agent Bundle,
        value (aggregate A) = ∑ i : Agent, value (A i))
    (hBudget_exhausts :
      ∀ i : Agent, value (X i) = value (endowment i))
    (hWeak_support :
      ∀ (i : Agent) (y : Bundle),
        y ∈ consumptionSet →
          U i y ≥ U i (X i) → value y ≥ value (X i))
    (hStrict_support :
      ∀ (i : Agent) (y : Bundle),
        y ∈ consumptionSet →
          U i y > U i (X i) → value y > value (X i)) :
    ParetoEfficient
      (ExchangeFeasibleSet consumptionSet endowment)
      (Set.univ : Set Agent) U X := by
  refine paretoEfficient_intro hX ?_
  intro hDom
  rcases hDom with ⟨Y, hY, hPareto⟩
  have hsum_strict :
      (∑ i : Agent, value (X i)) < ∑ i : Agent, value (Y i) := by
    refine Finset.sum_lt_sum ?hle ?hexists
    · intro i _hi
      exact hWeak_support i (Y i) (hY.2 i) (hPareto.1 i trivial)
    · rcases hPareto.2 with ⟨i, _hi, hstrict⟩
      exact ⟨i, Finset.mem_univ i,
        hStrict_support i (Y i) (hY.2 i) hstrict⟩
  have hvalueY_le :
      value (aggregate Y) ≤ value (aggregate endowment) :=
    hValue_mono hY.1
  rw [hValue_sum Y, hValue_sum endowment] at hvalueY_le
  have hsumX_eq :
      (∑ i : Agent, value (X i)) =
        ∑ i : Agent, value (endowment i) := by
    simp [hBudget_exhausts]
  linarith

/--
First Welfare Theorem for pure exchange, factored through a local-improvement
principle.

Compared with `paretoEfficient_of_priceSupport_exchange`, this theorem derives
the weak and strict price-support hypotheses from individual budget
maximization.  The local-improvement premise is the abstract form of the usual
local non-satiation argument: any weakly improving bundle that is strictly
cheaper than wealth can be perturbed to a strictly improving affordable bundle.
-/
theorem paretoEfficient_of_exchangeEquilibrium_of_local_improvement
    (consumptionSet : Set Bundle)
    (value : Bundle → ℝ)
    (endowment : Allocation Agent Bundle)
    (U : Agent → Bundle → ℝ)
    (X : Allocation Agent Bundle)
    (hEq : ExchangeEquilibrium consumptionSet value endowment U X)
    (hValue_mono :
      ∀ ⦃x y : Bundle⦄, x ≤ y → value x ≤ value y)
    (hValue_sum :
      ∀ A : Allocation Agent Bundle,
        value (aggregate A) = ∑ i : Agent, value (A i))
    (hBudget_exhausts :
      ∀ i : Agent, value (X i) = value (endowment i))
    (hLocal_improvement :
      ∀ (i : Agent) (y : Bundle),
        y ∈ consumptionSet →
          value y < value (endowment i) →
            U i y ≥ U i (X i) →
              ∃ z : Bundle,
                z ∈ consumptionSet ∧
                  value z ≤ value (endowment i) ∧
                    U i z > U i (X i)) :
    ParetoEfficient
      (ExchangeFeasibleSet consumptionSet endowment)
      (Set.univ : Set Agent) U X := by
  refine paretoEfficient_of_priceSupport_exchange
    consumptionSet value endowment U X hEq.1 hValue_mono hValue_sum
    hBudget_exhausts ?hWeak ?hStrict
  · intro i y hyS hyu
    exact weak_value_support_of_mem_maximizers_of_local_improvement
      (hEq.2 i) (hBudget_exhausts i) (hLocal_improvement i) hyS hyu
  · intro i y hyS hyu
    exact strict_value_support_of_mem_maximizers
      (hEq.2 i) (hBudget_exhausts i) hyS hyu

end PriceSupport

end Microeconomics
end EcoLean
