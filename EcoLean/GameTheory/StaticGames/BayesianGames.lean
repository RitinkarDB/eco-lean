import EcoLean.GameTheory.StaticGames.MixedStrategies

/-!
# Bayesian games (incomplete information)

Following Battigalli–Catonini–De Vito §8.5 (Harsanyi's type-space model). A **Bayesian game** enriches
a game with payoff uncertainty with a finite set of *states of the world* `Ω`; at each state every
player receives a *type* (signal) `τ i ω`, and holds a prior `p i ∈ Δ(Ω)`. Payoffs depend on the
state and the action profile. (We let the payoff depend on the state directly, absorbing the
interpretive parameter decomposition `θ = (θ₀, (θᵢ)ᵢ)` of §8.1 — only the dependence of `uᵢ` on the
state and actions matters for equilibrium.)

A (pure) **strategy** maps each type to an action, `σ i : T i → A i`. A profile `σ` is an **(interim)
Bayesian Nash equilibrium** (§8.4–8.5) when, for every player `i` and type `tᵢ`, `σ i tᵢ` maximises
`i`'s type-`tᵢ` expected payoff — no type can profitably deviate.

* `IsBayesianNashEquilibrium` — the equilibrium notion.
* `interimDevPayoff_self` — deviating a type to its own prescribed action changes nothing.
* `agentGame` / `isBayesianNashEquilibrium_iff_agentGame` — the **agent normal form**: a static game
  whose players are the type-pairs `(i, tᵢ)`; a Bayesian Nash equilibrium is exactly a Nash
  equilibrium of it. Hence finite Bayesian games inherit the static-game theory (Harsanyi's
  reduction).
-/

namespace EcoLean.GameTheory

open scoped BigOperators

/-- A **finite Bayesian game**: players each have a set of types `PlayerType i` and actions
`Action i`; a finite state space `State`; a signal `signal i : State → PlayerType i` revealing `i`'s
type at each state; a prior `prior i` over states; and a state-dependent payoff. -/
structure BayesianGame where
  /-- The players. -/
  Player : Type*
  /-- The states of the world `Ω`. -/
  State : Type*
  /-- Each player's type (signal) space. -/
  PlayerType : Player → Type*
  /-- Each player's action set. -/
  Action : Player → Type*
  /-- The signal: the type player `i` observes at a state. -/
  signal : ∀ i, State → PlayerType i
  /-- Player `i`'s prior belief over states. -/
  prior : Player → State → ℝ
  /-- The state-dependent payoff of player `i` at an action profile. -/
  payoff : Player → State → (∀ j, Action j) → ℝ

namespace BayesianGame

variable {G : BayesianGame} [Fintype G.State] [DecidableEq G.Player]
  [∀ i, DecidableEq (G.PlayerType i)]

/-- A **pure strategy profile**: each player maps their type to an action. -/
abbrev Strategy (G : BayesianGame) : Type _ := ∀ i, G.PlayerType i → G.Action i

/-- An **action profile**: an action for every player. -/
abbrev ActionProfile (G : BayesianGame) : Type _ := ∀ j, G.Action j

/-- The action profile realised at state `ω` when players follow `σ`. -/
def realizedProfile (σ : G.Strategy) (ω : G.State) : G.ActionProfile :=
  fun j => σ j (G.signal j ω)

/-- Player `i`'s **interim expected payoff** for type `tᵢ` under `σ`: the prior-weighted payoff over
the states consistent with observing `tᵢ` (unnormalised — the normalising constant `p i (τᵢ⁻¹ tᵢ)`
does not affect the best response). -/
def interimPayoff (σ : G.Strategy) (i : G.Player) (tᵢ : G.PlayerType i) : ℝ :=
  ∑ ω, (if G.signal i ω = tᵢ then G.prior i ω else 0) * G.payoff i ω (G.realizedProfile σ ω)

/-- The interim payoff to type `tᵢ` of deviating to action `aᵢ` (keeping all other behaviour fixed). -/
def interimDevPayoff (σ : G.Strategy) (i : G.Player) (tᵢ : G.PlayerType i) (aᵢ : G.Action i) : ℝ :=
  ∑ ω, (if G.signal i ω = tᵢ then G.prior i ω else 0) *
    G.payoff i ω (Function.update (G.realizedProfile σ ω) i aᵢ)

/-- `σ` is an **(interim) Bayesian Nash equilibrium**: for every player `i` and type `tᵢ`, no
deviation improves `i`'s type-`tᵢ` expected payoff. -/
def IsBayesianNashEquilibrium (σ : G.Strategy) : Prop :=
  ∀ (i : G.Player) (tᵢ : G.PlayerType i) (aᵢ : G.Action i),
    G.interimDevPayoff σ i tᵢ aᵢ ≤ G.interimPayoff σ i tᵢ

/-- Deviating a type to the action it already plays leaves the interim payoff unchanged. -/
@[simp] theorem interimDevPayoff_self (σ : G.Strategy) (i : G.Player) (tᵢ : G.PlayerType i) :
    G.interimDevPayoff σ i tᵢ (σ i tᵢ) = G.interimPayoff σ i tᵢ := by
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : G.signal i ω = tᵢ
  · have hr : G.realizedProfile σ ω i = σ i tᵢ := by simp only [realizedProfile, h]
    rw [← hr, Function.update_eq_self]
  · simp only [if_neg h, zero_mul]

/-! ### The agent normal form (Harsanyi's reduction)

A Bayesian Nash equilibrium of `G` is exactly a Nash equilibrium of the static game whose players are
the type-pairs `(i, tᵢ)` ("agents"), each choosing an action in `A i`, with payoff player `i`'s interim
payoff for type `tᵢ`. So finite Bayesian games inherit the static-game theory. -/

/-- The **agent normal form** of a Bayesian game: the static game over the type-pairs `(i, tᵢ)`. -/
noncomputable def agentGame (G : BayesianGame) [Fintype G.State] [DecidableEq G.Player]
    [∀ i, DecidableEq (G.PlayerType i)] : StaticGame where
  Player := Σ i : G.Player, G.PlayerType i
  Action := fun p => G.Action p.1
  payoff := fun p b => G.interimPayoff (fun j tⱼ => b ⟨j, tⱼ⟩) p.1 p.2

instance : DecidableEq (G.agentGame).Player :=
  inferInstanceAs (DecidableEq (Σ i : G.Player, G.PlayerType i))

/-- Flatten a Bayesian strategy into an action profile of the agent normal form. -/
def flatten (σ : G.Strategy) : (G.agentGame).ActionProfile := fun p => σ p.1 p.2

theorem agentGame_payoff_flatten (σ : G.Strategy) (i : G.Player) (tᵢ : G.PlayerType i) :
    (G.agentGame).payoff ⟨i, tᵢ⟩ (G.flatten σ) = G.interimPayoff σ i tᵢ := rfl

/-- The agent-normal-form deviation of agent `(i, tᵢ)` to `aᵢ` realises exactly the interim deviation
payoff: the recovered strategy plays `aᵢ` precisely at player `i`'s type-`tᵢ` states. -/
theorem agentGame_devPayoff_flatten (σ : G.Strategy) (i : G.Player) (tᵢ : G.PlayerType i)
    (aᵢ : G.Action i) :
    (G.agentGame).devPayoff (G.flatten σ) ⟨i, tᵢ⟩ aᵢ = G.interimDevPayoff σ i tᵢ aᵢ := by
  show G.interimPayoff (fun j tⱼ => (Function.update (G.flatten σ) ⟨i, tᵢ⟩ aᵢ) ⟨j, tⱼ⟩) i tᵢ
    = G.interimDevPayoff σ i tᵢ aᵢ
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : G.signal i ω = tᵢ
  · have hprof :
        G.realizedProfile (fun j tⱼ => (Function.update (G.flatten σ) ⟨i, tᵢ⟩ aᵢ) ⟨j, tⱼ⟩) ω
          = Function.update (G.realizedProfile σ ω) i aᵢ := by
      funext j
      by_cases hj : j = i
      · subst hj
        show (Function.update (G.flatten σ) ⟨j, tᵢ⟩ aᵢ) ⟨j, G.signal j ω⟩
          = Function.update (G.realizedProfile σ ω) j aᵢ j
        rw [h, Function.update_self, Function.update_self]
      · have hne : (⟨j, G.signal j ω⟩ : Σ k, G.PlayerType k) ≠ ⟨i, tᵢ⟩ :=
          fun heq => hj (congrArg Sigma.fst heq)
        show (Function.update (G.flatten σ) ⟨i, tᵢ⟩ aᵢ) ⟨j, G.signal j ω⟩
          = Function.update (G.realizedProfile σ ω) i aᵢ j
        rw [Function.update_of_ne hj]
        exact Function.update_of_ne hne aᵢ (G.flatten σ)
    rw [hprof]
  · simp only [if_neg h, zero_mul]

/-- **Harsanyi's reduction.** A pure strategy profile is a Bayesian Nash equilibrium iff its
flattening is a Nash equilibrium of the agent normal form. -/
theorem isBayesianNashEquilibrium_iff_agentGame (σ : G.Strategy) :
    G.IsBayesianNashEquilibrium σ ↔ (G.agentGame).IsNashEquilibrium (G.flatten σ) := by
  constructor
  · rintro h ⟨i, tᵢ⟩ aᵢ
    rw [G.agentGame_payoff_flatten, G.agentGame_devPayoff_flatten]
    exact h i tᵢ aᵢ
  · intro h i tᵢ aᵢ
    have hp := h ⟨i, tᵢ⟩ aᵢ
    rwa [G.agentGame_payoff_flatten, G.agentGame_devPayoff_flatten] at hp

/-! ### Existence of a mixed Bayesian Nash equilibrium

A finite Bayesian game always has a **mixed (behavioral) Bayesian Nash equilibrium**: a mixed Nash
equilibrium of its agent normal form, in which each agent `(i, tᵢ)` independently randomises over
actions. This is immediate from Harsanyi's reduction (`isBayesianNashEquilibrium_iff_agentGame`) — the
agent normal form is a finite static game — together with the mixed-Nash existence theorem
(`StaticGame.exists_mixedNashEquilibrium`, Kakutani on the product of simplices). -/

section Existence

variable [Fintype G.Player] [∀ i, Fintype (G.PlayerType i)] [∀ i, Fintype (G.Action i)]

instance : Fintype (G.agentGame).Player :=
  inferInstanceAs (Fintype (Σ i : G.Player, G.PlayerType i))

instance (p : (G.agentGame).Player) : Fintype ((G.agentGame).Action p) :=
  inferInstanceAs (Fintype (G.Action p.1))

instance [∀ i, Nonempty (G.Action i)] (p : (G.agentGame).Player) :
    Nonempty ((G.agentGame).Action p) :=
  inferInstanceAs (Nonempty (G.Action p.1))

/-- **Existence of a mixed Bayesian Nash equilibrium** (Harsanyi). A finite Bayesian game whose agent
normal form has at least a two-dimensional space of mixed profiles admits a mixed Nash equilibrium of
that agent normal form — i.e. a behavioral Bayesian Nash equilibrium in which each type independently
randomises over actions. -/
theorem exists_mixedAgentNashEquilibrium [∀ i, Nonempty (G.Action i)]
    (hdim : 2 ≤ Module.finrank ℝ (G.agentGame).MixedProfile) :
    ∃ α, (G.agentGame).IsMixedNashEquilibrium α :=
  (G.agentGame).exists_mixedNashEquilibrium hdim

end Existence

end BayesianGame

end EcoLean.GameTheory
