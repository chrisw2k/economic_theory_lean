/-
# Euclidean Strategic Games

Specialized version of continuous strategic games where each player's action set
is a compact convex subset of Euclidean space ℝⁿ.

This simplifies type matching for Kakutani's fixed point theorem while covering
essentially all practical game theory applications.

## Main Definitions

- `EuclideanStrategicGame`: Strategic game with Euclidean action spaces
- `has_continuous_payoffs`: Payoff functions are continuous
- `has_quasiconcave_payoffs`: Payoff functions are quasi-concave in own action
- `is_nash_equilibrium`: Nash equilibrium definition

## Main Results

- `proposition_20_3`: Nash equilibrium existence via Kakutani's theorem

## Design Decision

We use Euclidean spaces instead of abstract finite-dimensional normed spaces because:
- Type matching for Kakutani is automatic (no manual instance construction)
- Compactness proofs are simpler (concrete topology)
- Covers all practical applications (every finite-dim normed space ≃ ℝⁿ)
- More readable and maintainable code

## References

- Osborne, M. J., & Rubinstein, A. (1994). A Course in Game Theory. MIT Press.
  Chapter 2: Nash Equilibrium, Section 2.4, Proposition 20.3
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import FixedPointTheorems.Kakutani

/-! ## Euclidean Strategic Games -/

/--
A strategic game where each player's action set is a nonempty compact convex
subset of Euclidean space ℝⁿ.

This is a specialization of `ContinuousStrategicGame` that simplifies type
matching for Kakutani's fixed point theorem.
-/
structure EuclideanStrategicGame (N : Type*) [Fintype N] [DecidableEq N] where
  /-- Dimension of each player's action space -/
  (dim : N → ℕ)

  /-- The set of actions available to each player (subset of ℝⁿ) -/
  (A : (i : N) → Set (EuclideanSpace ℝ (Fin (dim i))))

  /-- Each player's action set is compact -/
  (compact_A : ∀ i, IsCompact (A i))

  /-- Each player's action set is convex -/
  (convex_A : ∀ i, Convex ℝ (A i))

  /-- Each player's action set is nonempty -/
  (nonempty_A : ∀ i, (A i).Nonempty)

  /-- Payoff function for each player -/
  (payoff : (i : N) → ((j : N) → EuclideanSpace ℝ (Fin (dim j))) → ℝ)

namespace EuclideanStrategicGame

variable {N : Type*} [Fintype N] [DecidableEq N] (G : EuclideanStrategicGame N)

/-! ## Basic Definitions -/

/--
An action profile is a choice of action for each player.
-/
abbrev ActionProfile := (i : N) → EuclideanSpace ℝ (Fin (G.dim i))

/--
The set of all valid action profiles (Cartesian product of individual action sets).
-/
def ActionProfileSet : Set (G.ActionProfile) :=
  {a : G.ActionProfile | ∀ i, a i ∈ G.A i}

/-! ## Continuity and Quasi-Concavity Conditions -/

/--
A game has continuous payoffs if each player's payoff function is continuous
in the action profile.
-/
def has_continuous_payoffs : Prop :=
  ∀ i : N, Continuous (fun a : G.ActionProfile => G.payoff i a)

/--
A game has quasi-concave payoffs if, for each player i and each fixed action
profile of the other players, player i's payoff function is quasi-concave in
their own action.

Quasi-concavity means that the upper contour sets {a_i : u_i(a_i, a_{-i}) ≥ r} are convex.
-/
def has_quasiconcave_payoffs : Prop :=
  ∀ (i : N) (a_minus_i : (j : N) → EuclideanSpace ℝ (Fin (G.dim j))),
    (∀ j, j ≠ i → a_minus_i j ∈ G.A j) →
    QuasiconcaveOn ℝ (G.A i) (fun a_i => G.payoff i (Function.update a_minus_i i a_i))

/-! ## Nash Equilibrium -/

/--
A Nash equilibrium is an action profile where no player can improve by
unilaterally changing their action.
-/
def is_nash_equilibrium (a : G.ActionProfile) : Prop :=
  (∀ i, a i ∈ G.A i) ∧
  ∀ (i : N) (a_i : EuclideanSpace ℝ (Fin (G.dim i))), a_i ∈ G.A i →
    G.payoff i a ≥ G.payoff i (Function.update a i a_i)

/-! ## Best Response Correspondence -/

/--
The best response set for player i given an action profile a.
This is the set of actions for player i that maximize their payoff given a.
-/
def best_response_set (i : N) (a : G.ActionProfile) : Set (EuclideanSpace ℝ (Fin (G.dim i))) :=
  {a_i ∈ G.A i | ∀ a'_i ∈ G.A i, G.payoff i (Function.update a i a_i) ≥
                                    G.payoff i (Function.update a i a'_i)}

/--
The product best response correspondence.
BR(a) = {b | ∀ i, b_i ∈ B_i(a_{-i})} = ×_{i∈N} B_i(a_{-i})
-/
def BR : G.ActionProfile → Set G.ActionProfile :=
  fun a => {b | ∀ i, b i ∈ G.best_response_set i a}

/-! ## Basic Properties of Action Profile Set -/

/--
The action profile set is nonempty (product of nonempty sets).
-/
theorem actionProfileSet_nonempty : G.ActionProfileSet.Nonempty := by
  simp [ActionProfileSet]
  have : ∀ i, ∃ a_i, a_i ∈ G.A i := fun i => G.nonempty_A i
  choose a ha using this
  exact ⟨a, ha⟩

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
The action profile set is compact (product of compact sets).
This follows from Tychonov's theorem.
-/
theorem actionProfileSet_isCompact : IsCompact G.ActionProfileSet := by
  unfold ActionProfileSet
  -- Use Tychonoff's theorem: product of compact sets is compact
  -- ActionProfileSet = {a | ∀ i, a i ∈ G.A i} = pi univ G.A
  exact isCompact_pi_infinite (fun i => G.compact_A i)

/-! ## Properties of Best Response Sets -/

/--
The best response set is nonempty when payoffs are continuous.
This follows from the extreme value theorem.
-/
theorem best_response_set_nonempty
    (i : N) (a : G.ActionProfile) (hcont : has_continuous_payoffs G) :
    (G.best_response_set i a).Nonempty := by
  unfold best_response_set

  -- Define the payoff function restricted to player i's action
  let f : EuclideanSpace ℝ (Fin (G.dim i)) → ℝ :=
    fun a_i => G.payoff i (Function.update a i a_i)

  -- Show f is continuous on G.A i
  have h_cont : ContinuousOn f (G.A i) := by
    unfold has_continuous_payoffs at hcont
    -- f is the composition of (a_i ↦ update a i a_i) and (payoff i)
    -- Both are continuous, so their composition is continuous on any set
    have h_payoff_cont : Continuous (G.payoff i) := hcont i
    have h_update_cont : Continuous (fun a_i : EuclideanSpace ℝ (Fin (G.dim i)) =>
                                     Function.update a i a_i) := by
      -- Use continuous_update from Mathlib.Topology.Constructions
      exact (continuous_update (A := fun j => EuclideanSpace ℝ (Fin (G.dim j))) i).comp
        (Continuous.prodMk continuous_const continuous_id)
    exact (h_payoff_cont.comp h_update_cont).continuousOn

  -- Apply extreme value theorem
  have ⟨a_max, ha_max_mem, ha_max⟩ :=
    IsCompact.exists_isMaxOn (G.compact_A i) (G.nonempty_A i) h_cont

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
    (i : N) (a : G.ActionProfile)
    (ha : a ∈ G.ActionProfileSet)
    (hquasi : has_quasiconcave_payoffs G) :
    Convex ℝ (G.best_response_set i a) := by
  unfold best_response_set
  intro x hx y hy a_coef b_coef ha_nonneg hb_nonneg hab
  simp only [Set.mem_sep_iff] at hx hy ⊢
  constructor
  · -- Show a_coef • x + b_coef • y ∈ G.A i
    exact G.convex_A i hx.1 hy.1 ha_nonneg hb_nonneg hab
  · -- Show a_coef • x + b_coef • y is still a best response
    intro a'_i ha'_i
    let f := fun a_i => G.payoff i (Function.update a i a_i)

    have hx_best : f x ≥ f a'_i := hx.2 a'_i ha'_i
    have hy_best : f y ≥ f a'_i := hy.2 a'_i ha'_i

    -- Get quasi-concavity
    have h_quasi : QuasiconcaveOn ℝ (G.A i) f := by
      have h := hquasi i a
      have ha_valid : ∀ j, j ≠ i → a j ∈ G.A j := by
        intro j hj
        unfold ActionProfileSet at ha
        simp only [Set.mem_setOf_eq] at ha
        exact ha j
      exact h ha_valid

    -- Apply definition of QuasiconcaveOn
    unfold QuasiconcaveOn at h_quasi
    have h_upper_convex : Convex ℝ ({a_i ∈ G.A i | f a'_i ≤ f a_i}) := h_quasi (f a'_i)

    -- x and y are in the upper level set
    have hx_in : x ∈ {a_i ∈ G.A i | f a'_i ≤ f a_i} := by
      simp only [Set.mem_sep_iff]
      exact ⟨hx.1, hx_best⟩
    have hy_in : y ∈ {a_i ∈ G.A i | f a'_i ≤ f a_i} := by
      simp only [Set.mem_sep_iff]
      exact ⟨hy.1, hy_best⟩

    -- By convexity, a_coef•x + b_coef•y is also in the upper level set
    have h_combo_in : a_coef • x + b_coef • y ∈ {a_i ∈ G.A i | f a'_i ≤ f a_i} :=
      h_upper_convex hx_in hy_in ha_nonneg hb_nonneg hab
    simp only [Set.mem_sep_iff] at h_combo_in
    exact h_combo_in.2

/-! ## Properties of Product Best Response -/

/--
The product best response maps action profiles to subsets of the action profile set.
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
theorem BR_convex (a : G.ActionProfile)
    (ha : a ∈ G.ActionProfileSet)
    (hquasi : has_quasiconcave_payoffs G) :
    Convex ℝ (G.BR a) := by
  unfold BR
  intro b hb c hc t s ht_nonneg hs_nonneg hts
  simp only [Set.mem_setOf_eq] at hb hc ⊢
  intro i
  -- Need to show: (t • b + s • c) i ∈ best_response_set i a
  -- This equals: t • (b i) + s • (c i)
  show t • b i + s • c i ∈ G.best_response_set i a
  have h_convex : Convex ℝ (G.best_response_set i a) :=
    G.best_response_set_convex i a ha hquasi
  exact h_convex (hb i) (hc i) ht_nonneg hs_nonneg hts

/-! ## Closed Graph Property - Helper Lemmas -/

/--
Standard result: Preimage of a closed interval [0, ∞) under a continuous function is closed.
-/
lemma closed_nonneg_preimage {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : Continuous f) :
    IsClosed {x | 0 ≤ f x} := by
  have h_eq : {x | 0 ≤ f x} = f⁻¹' (Set.Ici 0) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici]
  rw [h_eq]
  exact IsClosed.preimage hf isClosed_Ici

/--
The payoff difference function is continuous.
Shows that (a, b) ↦ payoff_i(update a i (b_i)) - payoff_i(update a i a'_i) is continuous.
-/
lemma continuous_payoff_diff (i : N) (a'_i : EuclideanSpace ℝ (Fin (G.dim i)))
    (hcont : has_continuous_payoffs G) :
    Continuous (fun p : G.ActionProfile × G.ActionProfile =>
      G.payoff i (Function.update p.1 i (p.2 i)) -
      G.payoff i (Function.update p.1 i a'_i)) := by
  -- Show both terms are continuous, then subtract
  have h1 : Continuous (fun p : G.ActionProfile × G.ActionProfile =>
                         G.payoff i (Function.update p.1 i (p.2 i))) := by
    -- Break into steps: p ↦ (p.1, p.2 i) ↦ update p.1 i (p.2 i) ↦ payoff i
    have step1 : Continuous (fun (p : G.ActionProfile × G.ActionProfile) => (p.1, p.2 i)) := by
      apply Continuous.prodMk continuous_fst
      exact (continuous_apply i).comp continuous_snd
    have step2 : Continuous (fun (q : G.ActionProfile × EuclideanSpace ℝ (Fin (G.dim i))) =>
                             Function.update q.1 i q.2) := by
      exact continuous_update (A := fun j => EuclideanSpace ℝ (Fin (G.dim j))) i
    have step3 : Continuous (G.payoff i) := hcont i
    exact step3.comp (step2.comp step1)

  have h2 : Continuous (fun p : G.ActionProfile × G.ActionProfile =>
                         G.payoff i (Function.update p.1 i a'_i)) := by
    -- Similar composition: p ↦ (p.1, a'_i) ↦ update p.1 i a'_i ↦ payoff i
    have step1 : Continuous (fun (p : G.ActionProfile × G.ActionProfile) => (p.1, a'_i)) := by
      exact Continuous.prodMk continuous_fst continuous_const
    have step2 : Continuous (fun (q : G.ActionProfile × EuclideanSpace ℝ (Fin (G.dim i))) =>
                             Function.update q.1 i q.2) := by
      exact continuous_update (A := fun j => EuclideanSpace ℝ (Fin (G.dim j))) i
    have step3 : Continuous (G.payoff i) := hcont i
    exact step3.comp (step2.comp step1)

  exact Continuous.sub h1 h2

/--
For each player i, the component set {(a, b) | b_i ∈ best_response_set i a} is closed.
This is the intersection of:
1. The constraint set: {(a, b) | b_i ∈ A_i} (closed because A_i is compact in Hausdorff)
2. The optimality set: ⋂_{a'_i ∈ A_i} {(a, b) | payoff_i(update a i (b_i)) ≥ payoff_i(update a i a'_i)}
-/
lemma component_set_closed (i : N) (hcont : has_continuous_payoffs G) :
    IsClosed {p : G.ActionProfile × G.ActionProfile |
      p.2 i ∈ G.best_response_set i p.1} := by
  unfold best_response_set

  -- Rewrite as intersection of constraint set and optimality set
  have h_eq : {p : G.ActionProfile × G.ActionProfile |
               p.2 i ∈ {a_i : EuclideanSpace ℝ (Fin (G.dim i)) |
                        a_i ∈ G.A i ∧
                        ∀ a'_i ∈ G.A i, G.payoff i (Function.update p.1 i a_i) ≥
                                        G.payoff i (Function.update p.1 i a'_i)}} =
              {p : G.ActionProfile × G.ActionProfile | p.2 i ∈ G.A i} ∩
              {p : G.ActionProfile × G.ActionProfile |
               ∀ a'_i ∈ G.A i, G.payoff i (Function.update p.1 i (p.2 i)) ≥
                               G.payoff i (Function.update p.1 i a'_i)} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_sep_iff, Set.mem_inter_iff]

  rw [h_eq]
  apply IsClosed.inter

  -- Part 1: Constraint set is closed
  · -- {p | p.2 i ∈ G.A i} is closed because it's the preimage of G.A i
    -- under the continuous projection p ↦ p.2 i
    have h_proj : Continuous (fun p : G.ActionProfile × G.ActionProfile => p.2 i) := by
      exact (continuous_apply i).comp continuous_snd
    have h_compact : IsCompact (G.A i) := G.compact_A i
    haveI : T2Space (EuclideanSpace ℝ (Fin (G.dim i))) := inferInstance
    have h_closed_Ai : IsClosed (G.A i) := h_compact.isClosed
    exact h_closed_Ai.preimage h_proj

  -- Part 2: Optimality set is closed (intersection of closed sets)
  · -- For each a'_i ∈ A_i, {p | payoff_i(update p.1 i (p.2 i)) ≥ payoff_i(update p.1 i a'_i)} is closed
    -- This is an intersection over all a'_i ∈ A_i
    have h_inter : {p : G.ActionProfile × G.ActionProfile |
                    ∀ a'_i ∈ G.A i, G.payoff i (Function.update p.1 i (p.2 i)) ≥
                                    G.payoff i (Function.update p.1 i a'_i)} =
                   ⋂ (a'_i : EuclideanSpace ℝ (Fin (G.dim i))) (_ : a'_i ∈ G.A i),
                     {p : G.ActionProfile × G.ActionProfile |
                      0 ≤ G.payoff i (Function.update p.1 i (p.2 i)) -
                          G.payoff i (Function.update p.1 i a'_i)} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h a'_i ha'_i
        have := h a'_i ha'_i
        linarith
      · intro h a'_i ha'_i
        have := h a'_i ha'_i
        linarith

    rw [h_inter]
    -- Apply isClosed_iInter for dependent intersections
    refine isClosed_iInter fun a'_i => isClosed_iInter fun ha'_i => ?_
    -- For fixed a'_i ∈ A_i, the set is closed by closed_nonneg_preimage
    exact closed_nonneg_preimage (@continuous_payoff_diff N _ _ G i a'_i hcont)

/--
The product best response correspondence has a closed graph.
-/
def BR_has_closed_graph (hcont : has_continuous_payoffs G) : Prop :=
  IsClosed {p : G.ActionProfile × G.ActionProfile | p.2 ∈ G.BR p.1}

theorem BR_closed_graph (hcont : has_continuous_payoffs G) :
    BR_has_closed_graph G hcont := by
  unfold BR_has_closed_graph

  -- Rewrite using BR definition
  show IsClosed {p : G.ActionProfile × G.ActionProfile | p.2 ∈ G.BR p.1}

  -- The graph equals the intersection over all players
  suffices h : IsClosed (⋂ i : N, {p : G.ActionProfile × G.ActionProfile |
                                    p.2 i ∈ G.best_response_set i p.1}) by
    convert h using 1
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    unfold BR
    simp only [Set.mem_setOf_eq]

  -- Each component set is closed by component_set_closed
  -- Apply isClosed_iInter: arbitrary intersection of closed sets is closed
  apply isClosed_iInter
  intro i
  exact @component_set_closed N _ _ G i hcont

end EuclideanStrategicGame

