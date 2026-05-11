import EcoLean.Microeconomics.ExchangeEconomy

/-!
# Production economies and private ownership

This file adds the production/private-ownership side of the welfare theorem
translation.  It keeps the same design as the exchange file: the mathematical
objects are small and reusable, while the welfare theorem is factored through
price-support assumptions that later commodity-space files can discharge from
more concrete hypotheses.
-/

open scoped BigOperators

universe u v w

namespace EcoLean
namespace Microeconomics

variable {Agent : Type u} {Firm : Type v} {Bundle : Type w}

/-- A production allocation assigns a net-output bundle to each firm. -/
abbrev ProductionAllocation (Firm : Type v) (Bundle : Type w) : Type (max v w) :=
  Firm → Bundle

/-- Ownership shares: `ownership i f` is agent `i`'s share of firm `f`. -/
abbrev OwnershipShares (Agent : Type u) (Firm : Type v) : Type (max u v) :=
  Agent → Firm → ℝ

section Wealth

variable [Fintype Agent] [Fintype Firm]

/--
The private-ownership wealth of an agent: endowment value plus shares of firm
profits.  A firm's profit at allocation `Y` is represented by `value (Y f)`.
-/
noncomputable def privateOwnershipWealth
    (value : Bundle → ℝ)
    (endowment : Allocation Agent Bundle)
    (ownership : OwnershipShares Agent Firm)
    (Y : ProductionAllocation Firm Bundle)
    (i : Agent) : ℝ :=
  value (endowment i) + ∑ f : Firm, ownership i f * value (Y f)

/--
Ownership shares are normalized when every firm's shares sum to one.

Nonnegativity can be added separately when it is economically relevant; the
welfare accounting identity only needs normalization.
-/
def OwnershipSharesNormalized
    (ownership : OwnershipShares Agent Firm) : Prop :=
  ∀ f : Firm, ∑ i : Agent, ownership i f = 1

theorem sum_privateOwnershipWealth
    (value : Bundle → ℝ)
    (endowment : Allocation Agent Bundle)
    (ownership : OwnershipShares Agent Firm)
    (Y : ProductionAllocation Firm Bundle)
    (hNorm : OwnershipSharesNormalized ownership) :
    (∑ i : Agent,
      privateOwnershipWealth value endowment ownership Y i) =
        (∑ i : Agent, value (endowment i)) +
          ∑ f : Firm, value (Y f) := by
  unfold privateOwnershipWealth
  calc
    (∑ i : Agent,
      (value (endowment i) + ∑ f : Firm, ownership i f * value (Y f)))
        =
          (∑ i : Agent, value (endowment i)) +
            ∑ i : Agent, ∑ f : Firm, ownership i f * value (Y f) := by
          rw [Finset.sum_add_distrib]
    _ =
          (∑ i : Agent, value (endowment i)) +
            ∑ f : Firm, ∑ i : Agent, ownership i f * value (Y f) := by
          rw [Finset.sum_comm]
    _ =
          (∑ i : Agent, value (endowment i)) +
            ∑ f : Firm, value (Y f) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro f _hf
          rw [← Finset.sum_mul, hNorm f]
          simp

end Wealth

section Feasibility

variable [Fintype Agent] [Fintype Firm]
variable [AddCommMonoid Bundle] [LE Bundle]

/--
Feasibility for a production economy: consumers choose bundles in the
consumption set, firms choose net outputs in their production sets, and
aggregate consumption is resource-feasible relative to endowments plus output.
-/
def ProductionFeasible
    (consumptionSet : Set Bundle)
    (productionSet : Firm → Set Bundle)
    (endowment : Allocation Agent Bundle)
    (X : Allocation Agent Bundle)
    (Y : ProductionAllocation Firm Bundle) : Prop :=
  aggregate X ≤ aggregate endowment + aggregate Y ∧
    (∀ i : Agent, X i ∈ consumptionSet) ∧
      ∀ f : Firm, Y f ∈ productionSet f

/-- The feasible state set for a production economy. -/
def ProductionFeasibleSet
    (consumptionSet : Set Bundle)
    (productionSet : Firm → Set Bundle)
    (endowment : Allocation Agent Bundle) :
    Set (Allocation Agent Bundle × ProductionAllocation Firm Bundle) :=
  {Z | ProductionFeasible consumptionSet productionSet endowment Z.1 Z.2}

@[simp] theorem mem_productionFeasibleSet_iff
    {consumptionSet : Set Bundle}
    {productionSet : Firm → Set Bundle}
    {endowment X : Allocation Agent Bundle}
    {Y : ProductionAllocation Firm Bundle} :
    (X, Y) ∈ ProductionFeasibleSet consumptionSet productionSet endowment ↔
      ProductionFeasible consumptionSet productionSet endowment X Y :=
  Iff.rfl

theorem aggregate_le_endowment_add_production_of_productionFeasible
    {consumptionSet : Set Bundle}
    {productionSet : Firm → Set Bundle}
    {endowment X : Allocation Agent Bundle}
    {Y : ProductionAllocation Firm Bundle}
    (hXY : ProductionFeasible consumptionSet productionSet endowment X Y) :
    aggregate X ≤ aggregate endowment + aggregate Y :=
  hXY.1

theorem mem_consumptionSet_of_productionFeasible
    {consumptionSet : Set Bundle}
    {productionSet : Firm → Set Bundle}
    {endowment X : Allocation Agent Bundle}
    {Y : ProductionAllocation Firm Bundle}
    (hXY : ProductionFeasible consumptionSet productionSet endowment X Y)
    (i : Agent) :
    X i ∈ consumptionSet :=
  hXY.2.1 i

theorem mem_productionSet_of_productionFeasible
    {consumptionSet : Set Bundle}
    {productionSet : Firm → Set Bundle}
    {endowment X : Allocation Agent Bundle}
    {Y : ProductionAllocation Firm Bundle}
    (hXY : ProductionFeasible consumptionSet productionSet endowment X Y)
    (f : Firm) :
    Y f ∈ productionSet f :=
  hXY.2.2 f

end Feasibility

section Equilibrium

variable [Fintype Agent] [Fintype Firm]
variable [AddCommMonoid Bundle] [LE Bundle]

/--
Private-ownership equilibrium with production.

Consumers maximize utility on their wealth-induced budget sets.  Firms maximize
the value of net output over their production sets.
-/
def PrivateOwnershipEquilibrium
    (consumptionSet : Set Bundle)
    (productionSet : Firm → Set Bundle)
    (value : Bundle → ℝ)
    (endowment : Allocation Agent Bundle)
    (ownership : OwnershipShares Agent Firm)
    (U : Agent → Bundle → ℝ)
    (X : Allocation Agent Bundle)
    (Y : ProductionAllocation Firm Bundle) : Prop :=
  ProductionFeasible consumptionSet productionSet endowment X Y ∧
    (∀ i : Agent,
      X i ∈ Maximizers (U i)
        (BudgetSet value consumptionSet
          (privateOwnershipWealth value endowment ownership Y i))) ∧
      ∀ f : Firm, Y f ∈ Maximizers value (productionSet f)

theorem feasible_of_privateOwnershipEquilibrium
    {consumptionSet : Set Bundle}
    {productionSet : Firm → Set Bundle}
    {value : Bundle → ℝ}
    {endowment : Allocation Agent Bundle}
    {ownership : OwnershipShares Agent Firm}
    {U : Agent → Bundle → ℝ}
    {X : Allocation Agent Bundle}
    {Y : ProductionAllocation Firm Bundle}
    (hEq :
      PrivateOwnershipEquilibrium consumptionSet productionSet value
        endowment ownership U X Y) :
    ProductionFeasible consumptionSet productionSet endowment X Y :=
  hEq.1

theorem consumer_optimal_of_privateOwnershipEquilibrium
    {consumptionSet : Set Bundle}
    {productionSet : Firm → Set Bundle}
    {value : Bundle → ℝ}
    {endowment : Allocation Agent Bundle}
    {ownership : OwnershipShares Agent Firm}
    {U : Agent → Bundle → ℝ}
    {X : Allocation Agent Bundle}
    {Y : ProductionAllocation Firm Bundle}
    (hEq :
      PrivateOwnershipEquilibrium consumptionSet productionSet value
        endowment ownership U X Y)
    (i : Agent) :
    X i ∈ Maximizers (U i)
      (BudgetSet value consumptionSet
        (privateOwnershipWealth value endowment ownership Y i)) :=
  hEq.2.1 i

theorem firm_optimal_of_privateOwnershipEquilibrium
    {consumptionSet : Set Bundle}
    {productionSet : Firm → Set Bundle}
    {value : Bundle → ℝ}
    {endowment : Allocation Agent Bundle}
    {ownership : OwnershipShares Agent Firm}
    {U : Agent → Bundle → ℝ}
    {X : Allocation Agent Bundle}
    {Y : ProductionAllocation Firm Bundle}
    (hEq :
      PrivateOwnershipEquilibrium consumptionSet productionSet value
        endowment ownership U X Y)
    (f : Firm) :
    Y f ∈ Maximizers value (productionSet f) :=
  hEq.2.2 f

end Equilibrium

section Welfare

variable [Fintype Agent] [Fintype Firm]
variable [AddCommMonoid Bundle] [LE Bundle]

/-- Pareto efficiency for a production economy state. -/
def ProductionParetoEfficient
    (consumptionSet : Set Bundle)
    (productionSet : Firm → Set Bundle)
    (endowment : Allocation Agent Bundle)
    (agents : Set Agent)
    (U : Agent → Bundle → ℝ)
    (X : Allocation Agent Bundle)
    (Y : ProductionAllocation Firm Bundle) : Prop :=
  ProductionFeasible consumptionSet productionSet endowment X Y ∧
    ¬ ∃ X' : Allocation Agent Bundle,
      ∃ Y' : ProductionAllocation Firm Bundle,
        ProductionFeasible consumptionSet productionSet endowment X' Y' ∧
          ParetoDominates agents U X' X

theorem productionParetoEfficient_intro
    {consumptionSet : Set Bundle}
    {productionSet : Firm → Set Bundle}
    {endowment X : Allocation Agent Bundle}
    {Y : ProductionAllocation Firm Bundle}
    {agents : Set Agent}
    {U : Agent → Bundle → ℝ}
    (hXY : ProductionFeasible consumptionSet productionSet endowment X Y)
    (hNoDom :
      ¬ ∃ X' : Allocation Agent Bundle,
        ∃ Y' : ProductionAllocation Firm Bundle,
          ProductionFeasible consumptionSet productionSet endowment X' Y' ∧
            ParetoDominates agents U X' X) :
    ProductionParetoEfficient consumptionSet productionSet endowment agents U X Y :=
  ⟨hXY, hNoDom⟩

/--
Abstract price-support First Welfare Theorem for private-ownership production
economies.

The value-feasibility premise packages the commodity-space accounting step:
every feasible alternative has aggregate consumption value bounded by
endowment value plus the value of its production plan.  Firm optimality then
bounds alternative production profits by equilibrium profits.
-/
theorem productionParetoEfficient_of_priceSupport_privateOwnership
    (consumptionSet : Set Bundle)
    (productionSet : Firm → Set Bundle)
    (value : Bundle → ℝ)
    (endowment : Allocation Agent Bundle)
    (U : Agent → Bundle → ℝ)
    (X : Allocation Agent Bundle)
    (Y : ProductionAllocation Firm Bundle)
    (hXY : ProductionFeasible consumptionSet productionSet endowment X Y)
    (hFeasible_value :
      ∀ (A : Allocation Agent Bundle) (Z : ProductionAllocation Firm Bundle),
        ProductionFeasible consumptionSet productionSet endowment A Z →
          (∑ i : Agent, value (A i)) ≤
            value (aggregate endowment) + ∑ f : Firm, value (Z f))
    (hCurrent_value :
      (∑ i : Agent, value (X i)) =
        value (aggregate endowment) + ∑ f : Firm, value (Y f))
    (hFirm_support :
      ∀ (f : Firm) (z : Bundle),
        z ∈ productionSet f → value z ≤ value (Y f))
    (hWeak_support :
      ∀ (i : Agent) (y : Bundle),
        y ∈ consumptionSet →
          U i y ≥ U i (X i) → value y ≥ value (X i))
    (hStrict_support :
      ∀ (i : Agent) (y : Bundle),
        y ∈ consumptionSet →
          U i y > U i (X i) → value y > value (X i)) :
    ProductionParetoEfficient
      consumptionSet productionSet endowment Set.univ U X Y := by
  refine productionParetoEfficient_intro hXY ?_
  intro hDom
  rcases hDom with ⟨X', Y', hXY', hPareto⟩
  have hsum_strict :
      (∑ i : Agent, value (X i)) < ∑ i : Agent, value (X' i) := by
    refine Finset.sum_lt_sum ?hle ?hexists
    · intro i _hi
      exact hWeak_support i (X' i) (hXY'.2.1 i) (hPareto.1 i trivial)
    · rcases hPareto.2 with ⟨i, _hi, hstrict⟩
      exact ⟨i, Finset.mem_univ i,
        hStrict_support i (X' i) (hXY'.2.1 i) hstrict⟩
  have hfirm_sum_le :
      (∑ f : Firm, value (Y' f)) ≤ ∑ f : Firm, value (Y f) := by
    exact Finset.sum_le_sum fun f _hf =>
      hFirm_support f (Y' f) (hXY'.2.2 f)
  have halt_value :
      (∑ i : Agent, value (X' i)) ≤
        value (aggregate endowment) + ∑ f : Firm, value (Y f) := by
    have hprod_bound :
        value (aggregate endowment) + ∑ f : Firm, value (Y' f) ≤
          value (aggregate endowment) + ∑ f : Firm, value (Y f) := by
      nlinarith
    exact le_trans (hFeasible_value X' Y' hXY') hprod_bound
  linarith

/--
Private-ownership FWT derived from equilibrium, budget exhaustion, and local
improvement.
-/
theorem productionParetoEfficient_of_privateOwnershipEquilibrium_of_local_improvement
    (consumptionSet : Set Bundle)
    (productionSet : Firm → Set Bundle)
    (value : Bundle → ℝ)
    (endowment : Allocation Agent Bundle)
    (ownership : OwnershipShares Agent Firm)
    (U : Agent → Bundle → ℝ)
    (X : Allocation Agent Bundle)
    (Y : ProductionAllocation Firm Bundle)
    (hEq :
      PrivateOwnershipEquilibrium consumptionSet productionSet value
        endowment ownership U X Y)
    (hFeasible_value :
      ∀ (A : Allocation Agent Bundle) (Z : ProductionAllocation Firm Bundle),
        ProductionFeasible consumptionSet productionSet endowment A Z →
          (∑ i : Agent, value (A i)) ≤
            value (aggregate endowment) + ∑ f : Firm, value (Z f))
    (hBudget_exhausts :
      ∀ i : Agent,
        value (X i) =
          privateOwnershipWealth value endowment ownership Y i)
    (hCurrent_value :
      (∑ i : Agent, value (X i)) =
        value (aggregate endowment) + ∑ f : Firm, value (Y f))
    (hLocal_improvement :
      ∀ (i : Agent) (y : Bundle),
        y ∈ consumptionSet →
          value y <
            privateOwnershipWealth value endowment ownership Y i →
            U i y ≥ U i (X i) →
              ∃ z : Bundle,
                z ∈ consumptionSet ∧
                  value z ≤
                    privateOwnershipWealth value endowment ownership Y i ∧
                    U i z > U i (X i)) :
    ProductionParetoEfficient
      consumptionSet productionSet endowment Set.univ U X Y := by
  refine productionParetoEfficient_of_priceSupport_privateOwnership
    consumptionSet productionSet value endowment U X Y hEq.1
    hFeasible_value hCurrent_value ?hFirm ?hWeak ?hStrict
  · intro f z hz
    exact utility_ge_of_mem_maximizers (hEq.2.2 f) hz
  · intro i y hyS hyu
    exact weak_value_support_of_mem_maximizers_of_local_improvement
      (hEq.2.1 i) (hBudget_exhausts i) (hLocal_improvement i) hyS hyu
  · intro i y hyS hyu
    exact strict_value_support_of_mem_maximizers
      (hEq.2.1 i) (hBudget_exhausts i) hyS hyu

end Welfare

end Microeconomics
end EcoLean
