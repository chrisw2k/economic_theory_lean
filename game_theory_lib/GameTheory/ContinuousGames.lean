/-
# Continuous Strategic Games

This file defines strategic games with continuous action spaces, as required for
proving Nash equilibrium existence via Kakutani's fixed point theorem.

This corresponds to Proposition 20.3 in Osborne & Rubinstein (1994), Chapter 2.

## Main Definitions

- `ContinuousStrategicGame`: A strategic game where each player's action set is a
  compact convex subset of a finite-dimensional vector space
- `has_continuous_payoffs`: Payoff functions are continuous
- `has_quasiconcave_payoffs`: Payoff functions are quasi-concave in own action

## Main Results

- `proposition_20_3`: Nash equilibrium existence for continuous games with
  continuous quasi-concave payoffs

## References

- Osborne, M. J., & Rubinstein, A. (1994). A Course in Game Theory. MIT Press.
  Chapter 2: Nash Equilibrium, Section 2.4, Proposition 20.3
-/

import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import GameTheory.Basic
import GameTheory.ActionProfiles
import FixedPointTheorems.Kakutani

/-! ## Continuous Strategic Games -/

/--
A continuous strategic game where each player's action set is a compact convex
subset of a finite-dimensional normed space.

This is the setting for Proposition 20.3 (Nash equilibrium existence via Kakutani).
-/
structure ContinuousStrategicGame (N : Type*) [Fintype N] [DecidableEq N] where
  /-- For each player, the ambient vector space containing their actions -/
  (V : N → Type*)
  /-- Each V i has the structure of a normed additive commutative group -/
  [normed : ∀ i, NormedAddCommGroup (V i)]
  /-- Each V i has the structure of a normed space over ℝ -/
  [space : ∀ i, NormedSpace ℝ (V i)]
  /-- Each V i is finite-dimensional -/
  [findim : ∀ i, FiniteDimensional ℝ (V i)]

  /-- The set of actions available to each player (subset of V i) -/
  (A : (i : N) → Set (V i))

  /-- Each player's action set is compact -/
  (compact_A : ∀ i, IsCompact (A i))
  /-- Each player's action set is convex -/
  (convex_A : ∀ i, Convex ℝ (A i))
  /-- Each player's action set is nonempty -/
  (nonempty_A : ∀ i, (A i).Nonempty)

  /-- Payoff function for each player -/
  (payoff : (i : N) → ((j : N) → V j) → ℝ)

namespace ContinuousStrategicGame

variable {N : Type*} [Fintype N] [DecidableEq N] (G : ContinuousStrategicGame N)

/-- Instance for normed group structure -/
instance instNormedAddCommGroup (i : N) : NormedAddCommGroup (G.V i) := G.normed i

/-- Instance for normed space structure -/
instance instNormedSpace (i : N) : NormedSpace ℝ (G.V i) := G.space i

/-- Instance for finite-dimensionality -/
instance instFiniteDimensional (i : N) : FiniteDimensional ℝ (G.V i) := G.findim i

/--
An action profile is a choice of action for each player.
-/
abbrev ActionProfile := (i : N) → G.V i

/--
The set of all valid action profiles (Cartesian product of individual action sets).
-/
def ActionProfileSet : Set (G.ActionProfile) :=
  {a : G.ActionProfile | ∀ i, a i ∈ G.A i}

/--
The action profile set is the product of compact sets, hence compact by Tychonov.
-/
theorem actionProfileSet_isCompact : IsCompact G.ActionProfileSet := by
  unfold ActionProfileSet
  have : IsCompact (Set.univ : Set ((i : N) → G.V i)) := by
    haveI : ∀ i, CompactSpace (G.A i) := fun i =>
      isCompact_iff_compactSpace.mp (G.compact_A i)
    sorry -- Need to show product is compact using Tychonov
  sorry

/--
The action profile set is convex (product of convex sets).
-/
theorem actionProfileSet_convex : Convex ℝ G.ActionProfileSet := by
  unfold ActionProfileSet
  intro a ha b hb t s ht_nonneg hs_nonneg hts
  simp only [Set.mem_setOf_eq] at ha hb ⊢
  intro i
  -- Need to show: (t • a + s • b) i ∈ G.A i
  -- This equals: t • (a i) + s • (b i)
  show t • a i + s • b i ∈ G.A i
  exact G.convex_A i (ha i) (hb i) ht_nonneg hs_nonneg hts

/--
The action profile set is nonempty (product of nonempty sets).
-/
theorem actionProfileSet_nonempty : G.ActionProfileSet.Nonempty := by
  simp [ActionProfileSet]
  have : ∀ i, ∃ a_i, a_i ∈ G.A i := fun i => G.nonempty_A i
  choose a ha using this
  exact ⟨a, ha⟩

/-! ## Continuity Condition -/

/--
A continuous strategic game has continuous payoffs if each player's payoff function
is continuous in the action profile.

This is one of the conditions of Proposition 20.3.
-/
def has_continuous_payoffs : Prop :=
  ∀ i : N, Continuous (fun a : G.ActionProfile => G.payoff i a)

/-! ## Quasi-Concavity Condition -/

/--
A continuous strategic game has quasi-concave payoffs if, for each player i and
each fixed action profile of the other players, player i's payoff function is
quasi-concave in their own action.

This is one of the conditions of Proposition 20.3.

Quasi-concavity means that the upper contour sets {a_i : u_i(a_i, a_{-i}) ≥ r} are convex.
-/
def has_quasiconcave_payoffs : Prop :=
  ∀ (i : N) (a_minus_i : (j : N) → G.V j),
    (∀ j, j ≠ i → a_minus_i j ∈ G.A j) →
    QuasiconcaveOn ℝ (G.A i) (fun a_i => G.payoff i (Function.update a_minus_i i a_i))

/-! ## Nash Equilibrium -/

/--
A Nash equilibrium is an action profile where no player can improve by unilaterally
changing their action.
-/
def is_nash_equilibrium (a : G.ActionProfile) : Prop :=
  (∀ i, a i ∈ G.A i) ∧
  ∀ (i : N) (a_i : G.V i), a_i ∈ G.A i →
    G.payoff i a ≥ G.payoff i (Function.update a i a_i)

/-! ## Best Response Correspondence -/

/--
The best response set for player i given an action profile a.
This is the set of actions for player i that maximize their payoff given a.
-/
def best_response_set (i : N) (a : G.ActionProfile) : Set (G.V i) :=
  {a_i ∈ G.A i | ∀ a'_i ∈ G.A i, G.payoff i (Function.update a i a_i) ≥
                                    G.payoff i (Function.update a i a'_i)}

/--
The best response set is nonempty when payoffs are continuous.
This follows from the extreme value theorem: a continuous function on a compact set
attains its maximum.
-/
theorem best_response_set_nonempty
    (i : N) (a : G.ActionProfile) (hcont : has_continuous_payoffs G) :
    (G.best_response_set i a).Nonempty := by
  unfold best_response_set

  -- Define the payoff function restricted to player i's action
  let f : G.V i → ℝ := fun a_i => G.payoff i (Function.update a i a_i)

  -- Show f is continuous on G.A i
  have h_cont : ContinuousOn f (G.A i) := by
    unfold has_continuous_payoffs at hcont
    -- f is the composition of (a_i ↦ update a i a_i) and (payoff i)
    -- The update map is continuous, and payoff i is continuous
    have h_update_cont : Continuous (fun a_i : G.V i => Function.update a i a_i) := by
      -- The map a_i ↦ (a, a_i) is continuous
      have h1 : Continuous (fun a_i : G.V i => (a, a_i)) :=
        Continuous.prodMk continuous_const continuous_id
      -- The map (f, x) ↦ update f i x is continuous
      have h2 : Continuous (fun (p : G.ActionProfile × G.V i) => Function.update p.1 i p.2) :=
        continuous_update i
      -- Composition gives continuity of a_i ↦ update a i a_i
      convert h2.comp h1 using 1
    have h_payoff_cont : Continuous (G.payoff i) := hcont i
    -- Composition of continuous functions is continuous
    exact (h_payoff_cont.comp h_update_cont).continuousOn

  -- Apply extreme value theorem
  have ⟨a_max, ha_max_mem, ha_max⟩ := IsCompact.exists_isMaxOn (G.compact_A i) (G.nonempty_A i) h_cont

  -- a_max is in the best response set
  use a_max
  refine ⟨ha_max_mem, ?_⟩
  intro a'_i ha'_i
  -- IsMaxOn f (G.A i) a_max means ∀ y ∈ G.A i, f y ≤ f a_max
  exact ha_max ha'_i

/--
The best response set is convex when payoffs are quasi-concave.
-/
theorem best_response_set_convex
    (i : N) (a : G.ActionProfile) (hquasi : has_quasiconcave_payoffs G) :
    Convex ℝ (G.best_response_set i a) := by
  unfold best_response_set
  intro x hx y hy a_coef b_coef ha_nonneg hb_nonneg hab
  simp only [Set.mem_sep_iff] at hx hy ⊢
  constructor
  · -- Show a_coef • x + b_coef • y ∈ G.A i (follows from convexity of G.A i)
    exact G.convex_A i hx.1 hy.1 ha_nonneg hb_nonneg hab
  · -- Show a_coef • x + b_coef • y is still a best response
    intro a'_i ha'_i
    -- Define f(a_i) = payoff i (update a i a_i)
    let f := fun a_i => G.payoff i (Function.update a i a_i)

    -- Both x and y are best responses, so f(x) ≥ f(a'_i) and f(y) ≥ f(a'_i)
    have hx_best : f x ≥ f a'_i := hx.2 a'_i ha'_i
    have hy_best : f y ≥ f a'_i := hy.2 a'_i ha'_i

    -- We need to show: f(a_coef • x + b_coef • y) ≥ f(a'_i)
    -- By quasi-concavity, the upper level set {z : f(z) ≥ f(a'_i)} is convex
    -- Since x, y are in this set, so is a_coef•x + b_coef•y

    -- Get quasi-concavity for this specific level
    have h_quasi : QuasiconcaveOn ℝ (G.A i) f := by
      -- Apply hquasi with a_minus_i = a
      have h := hquasi i a
      -- Need to show: ∀ j, j ≠ i → a j ∈ G.A j
      have ha_valid : ∀ j, j ≠ i → a j ∈ G.A j := by
        sorry -- This requires a to be a valid action profile
      exact h ha_valid

    -- Apply definition of QuasiconcaveOn
    unfold QuasiconcaveOn at h_quasi
    have h_upper_convex : Convex ℝ ({a_i ∈ G.A i | f a'_i ≤ f a_i}) := h_quasi (f a'_i)

    -- x and y are in the upper level set
    have hx_in : x ∈ {a_i ∈ G.A i | f a'_i ≤ f a_i} := by
      simp [Set.mem_setOf_eq]
      exact ⟨hx.1, hx_best⟩
    have hy_in : y ∈ {a_i ∈ G.A i | f a'_i ≤ f a_i} := by
      simp [Set.mem_setOf_eq]
      exact ⟨hy.1, hy_best⟩

    -- By convexity, a_coef•x + b_coef•y is also in the upper level set
    have h_combo_in : a_coef • x + b_coef • y ∈ {a_i ∈ G.A i | f a'_i ≤ f a_i} :=
      h_upper_convex hx_in hy_in ha_nonneg hb_nonneg hab
    simp only [Set.mem_sep_iff] at h_combo_in
    exact h_combo_in.2

/--
The product best response correspondence.
BR(a) = {b | ∀ i, b_i ∈ B_i(a_{-i})}
     = ×_{i∈N} B_i(a_{-i})
-/
def BR : G.ActionProfile → Set G.ActionProfile :=
  fun a => {b | ∀ i, b i ∈ G.best_response_set i a}

/--
The product best response correspondence maps action profiles to subsets of the
action profile set.
-/
theorem BR_subset_actionProfileSet (a : G.ActionProfile) :
    G.BR a ⊆ G.ActionProfileSet := by
  intro b hb
  simp [ActionProfileSet, BR, best_response_set] at hb ⊢
  intro i
  exact (hb i).1

/--
The product best response is nonempty when each individual best response is nonempty.
-/
theorem BR_nonempty (a : G.ActionProfile) (hcont : has_continuous_payoffs G) :
    (G.BR a).Nonempty := by
  unfold BR
  -- Each best_response_set i a is nonempty
  have h_each_nonempty : ∀ i, (G.best_response_set i a).Nonempty :=
    fun i => G.best_response_set_nonempty i a hcont
  -- Use axiom of choice to get one element from each set
  choose b hb using h_each_nonempty
  -- b is an action profile with b i ∈ best_response_set i a for all i
  use b
  simp only [Set.mem_setOf_eq]
  exact hb

/--
The product best response is convex (product of convex sets is convex).
-/
theorem BR_convex (a : G.ActionProfile) (hquasi : has_quasiconcave_payoffs G) :
    Convex ℝ (G.BR a) := by
  unfold BR
  intro b hb c hc t s ht_nonneg hs_nonneg hts
  simp only [Set.mem_setOf_eq] at hb hc ⊢
  intro i
  -- Need to show: (t • b + s • c) i ∈ best_response_set i a
  -- This equals: t • (b i) + s • (c i)
  show t • b i + s • c i ∈ G.best_response_set i a
  have h_convex : Convex ℝ (G.best_response_set i a) := G.best_response_set_convex i a hquasi
  exact h_convex (hb i) (hc i) ht_nonneg hs_nonneg hts

/--
The product best response correspondence has a closed graph.
This is the key property needed for Kakutani's theorem.
-/
def BR_has_closed_graph (hcont : has_continuous_payoffs G) : Prop :=
  IsClosed {p : G.ActionProfile × G.ActionProfile | p.2 ∈ G.BR p.1}

theorem BR_closed_graph (hcont : has_continuous_payoffs G) :
    BR_has_closed_graph G hcont := by
  sorry

end ContinuousStrategicGame
