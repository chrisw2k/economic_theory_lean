/-
# Nash Equilibrium Existence for Euclidean Games

This file contains the proof of Nash equilibrium existence for Euclidean strategic
games using Kakutani's fixed point theorem.

## Main Result

- `proposition_20_3`: Every Euclidean strategic game with continuous quasi-concave
  payoffs has a Nash equilibrium.

This is Proposition 20.3 from Osborne & Rubinstein (1994), proven for the special
case where action sets are compact convex subsets of Euclidean space.

## Design Decision

This file proves the theorem for Euclidean games (where each player's action set is
a subset of ℝⁿ) rather than abstract finite-dimensional normed spaces. This
simplification:
- Avoids complex type matching for Kakutani's theorem
- Makes instances automatic (no manual typeclass construction)
- Covers all practical applications
- Results in cleaner, more maintainable code

## References

- Osborne, M. J., & Rubinstein, A. (1994). A Course in Game Theory. MIT Press.
  Chapter 2: Nash Equilibrium, Section 2.4, Proposition 20.3
- Kakutani, S. (1941). A generalization of Brouwer's fixed point theorem.
  Duke Mathematical Journal, 8(3), 457-459.
-/

import GameTheory.EuclideanGames
import FixedPointTheorems.Kakutani

namespace EuclideanStrategicGame

variable {N : Type*} [Fintype N] [DecidableEq N] (G : EuclideanStrategicGame N)

/-! ## Main Theorem: Nash Equilibrium Existence -/

/--
**Proposition 20.3 (Nash Equilibrium Existence via Kakutani)**

Let G = ⟨N, (Aᵢ), (uᵢ)⟩ be an Euclidean strategic game where:
- For each player i, the action set Aᵢ is a nonempty compact convex subset of ℝⁿⁱ
- Each payoff function uᵢ is continuous
- Each payoff function uᵢ is quasi-concave in player i's own action

Then G has a Nash equilibrium.

**Proof outline:**
1. The product action space A = ×ᵢ∈N Aᵢ is nonempty, compact, and convex
2. The best response correspondence BR: A → 2^A satisfies:
   - BR(a) ⊆ A for all a (subset property)
   - BR(a) is nonempty (by compactness and continuity)
   - BR(a) is convex (by quasi-concavity)
   - BR has a closed graph (by continuity of payoffs)
3. The product space has automatic NormedAddCommGroup, NormedSpace, and
   FiniteDimensional instances from Mathlib
4. By Kakutani's fixed point theorem, ∃ a* with a* ∈ BR(a*)
5. This means a*ᵢ ∈ Bᵢ(a*₋ᵢ) for all i, which is precisely a Nash equilibrium
-/
theorem proposition_20_3
    (hcont : G.has_continuous_payoffs)
    (hquasi : G.has_quasiconcave_payoffs) :
    ∃ a : G.ActionProfile, G.is_nash_equilibrium a := by

  -- Step 1: Verify type instances (automatic for Euclidean spaces!)
  -- ActionProfile unfolds to: (i : N) → EuclideanSpace ℝ (Fin (G.dim i))
  letI : NormedAddCommGroup G.ActionProfile := Pi.normedAddCommGroup
  letI : NormedSpace ℝ G.ActionProfile := Pi.normedSpace
  letI : FiniteDimensional ℝ G.ActionProfile := by
    -- Product of finite-dimensional spaces where index set is finite
    -- G.ActionProfile = (i : N) → EuclideanSpace ℝ (Fin (G.dim i))
    -- Each EuclideanSpace ℝ (Fin n) is finite-dimensional
    -- N is Fintype, hence Finite
    -- The instance FiniteDimensional.pi' applies automatically
    infer_instance

  -- Step 2: Set up Kakutani parameters
  let s := G.ActionProfileSet
  have hcvx : Convex ℝ s := G.actionProfileSet_convex
  have hcmpct : IsCompact s := G.actionProfileSet_isCompact
  have hne : s.Nonempty := G.actionProfileSet_nonempty

  -- Step 3: BR correspondence satisfies Kakutani hypotheses
  -- Note: Kakutani expects f : ↥s → Set V, but BR : ActionProfile → Set ActionProfile
  -- So we define a restricted version
  let BR_restricted : ↥s → Set G.ActionProfile := fun x => G.BR x.1

  have h1 : ∀ x : ↥s, BR_restricted x ⊆ s ∧ Convex ℝ (BR_restricted x) ∧ (BR_restricted x).Nonempty := by
    intro ⟨a, ha⟩
    simp only [BR_restricted]
    refine ⟨G.BR_subset_actionProfileSet a,
            G.BR_convex a ha hquasi,
            G.BR_nonempty a hcont⟩

  have hcg : closedGraph BR_restricted := by
    -- Closed graph of BR_restricted follows from closed graph of BR
    unfold closedGraph BR_restricted
    -- Graph of BR_restricted = {(x, y) : ↥s × ActionProfile | y ∈ BR x.1}
    -- This is a subset of the graph of BR (via the embedding x.1)

    have h_BR_closed : IsClosed {p : G.ActionProfile × G.ActionProfile | p.2 ∈ G.BR p.1} :=
      G.BR_closed_graph hcont

    -- The graph of BR_restricted is the preimage of the graph of BR
    -- under the continuous map (x, y) ↦ (x.1, y)
    have h_cont : Continuous (fun (p : ↥s × G.ActionProfile) => (p.1.1, p.2)) := by
      exact Continuous.prod_mk (continuous_subtype_val.comp continuous_fst) continuous_snd

    -- Apply: preimage of closed set is closed
    show IsClosed {p : ↥s × G.ActionProfile | p.2 ∈ G.BR p.1.1}
    exact h_BR_closed.preimage h_cont

  -- Step 4: Apply Kakutani's fixed point theorem!
  -- Type V is automatically inferred as G.ActionProfile (Euclidean product)
  have ⟨a_star, ha_star⟩ :=
    kakutani_fixed_point s hcvx hcmpct hne BR_restricted hcg h1

  -- Step 5: Extract Nash equilibrium from fixed point
  -- ha_star : a_star.1 ∈ BR_restricted a_star
  -- which means: a_star.1 ∈ BR a_star.1
  use a_star.1

  -- Prove it's a Nash equilibrium
  unfold is_nash_equilibrium
  simp only [BR_restricted] at ha_star
  unfold BR at ha_star
  simp only [Set.mem_setOf_eq] at ha_star

  constructor
  · -- Show a_star.1 ∈ ActionProfileSet
    exact a_star.2
  · -- Show no profitable deviations
    intro i a'_i ha'_i
    -- ha_star says: ∀ i, a_star.1 i ∈ best_response_set i a_star.1
    have := ha_star i
    unfold best_response_set at this
    simp only [Set.mem_sep_iff] at this
    -- this.2 gives us: payoff i (update a_star.1 i (a_star.1 i)) ≥ payoff i (update a_star.1 i a'_i)
    -- We need: payoff i a_star.1 ≥ payoff i (update a_star.1 i a'_i)
    -- Simplify using update a i (a i) = a
    simp only [Function.update_eq_self] at this
    exact this.2 a'_i ha'_i

/--
Corollary: For an Euclidean strategic game with continuous quasi-concave payoffs,
the set of Nash equilibria is nonempty.
-/
theorem nash_equilibrium_exists
    (hcont : G.has_continuous_payoffs)
    (hquasi : G.has_quasiconcave_payoffs) :
    (G.ActionProfileSet ∩ {a | G.is_nash_equilibrium a}).Nonempty := by
  obtain ⟨a, ha⟩ := proposition_20_3 G hcont hquasi
  use a
  exact ⟨ha.1, ha⟩

end EuclideanStrategicGame
