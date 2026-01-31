/-
# Nash Equilibrium Existence

This file contains the proof of Nash equilibrium existence for continuous strategic games
using Kakutani's fixed point theorem.

## Main Result

- `proposition_20_3`: Every continuous strategic game with compact convex action sets
  and continuous quasi-concave payoffs has a Nash equilibrium.

This is Proposition 20.3 from Osborne & Rubinstein (1994), Chapter 2, Section 2.4.

## References

- Osborne, M. J., & Rubinstein, A. (1994). A Course in Game Theory. MIT Press.
  Chapter 2: Nash Equilibrium, Section 2.4, Proposition 20.3
- Kakutani, S. (1941). A generalization of Brouwer's fixed point theorem.
  Duke Mathematical Journal, 8(3), 457-459.
-/

import GameTheory.ContinuousGames
import FixedPointTheorems.Kakutani

namespace ContinuousStrategicGame

variable {N : Type*} [Fintype N] [DecidableEq N] (G : ContinuousStrategicGame N)

/-! ## Main Theorem: Nash Equilibrium Existence -/

/--
**Proposition 20.3 (Nash Equilibrium Existence via Kakutani)**

Let G = ⟨N, (Aᵢ), (uᵢ)⟩ be a strategic game where:
- For each player i, the action set Aᵢ is a nonempty compact convex subset of a
  finite-dimensional vector space
- Each payoff function uᵢ is continuous
- Each payoff function uᵢ is quasi-concave in player i's own action

Then G has a Nash equilibrium.

**Proof outline:**
1. The product action space A = ×ᵢ∈N Aᵢ is nonempty, compact (Tychonov), and convex
2. The best response correspondence BR: A → 2^A satisfies:
   - BR(a) ⊆ A for all a
   - BR(a) is nonempty (by compactness and continuity)
   - BR(a) is convex (by quasi-concavity)
   - BR has a closed graph (by continuity of payoffs)
3. By Kakutani's fixed point theorem, ∃ a* with a* ∈ BR(a*)
4. This means a*ᵢ ∈ Bᵢ(a*₋ᵢ) for all i, which is precisely a Nash equilibrium
-/
theorem proposition_20_3
    (hcont : G.has_continuous_payoffs)
    (hquasi : G.has_quasiconcave_payoffs) :
    ∃ a : G.ActionProfile, G.is_nash_equilibrium a := by

  -- Note: This proof requires applying Kakutani's fixed point theorem to
  -- the product space of action sets. However, Kakutani's theorem in our
  -- library requires a single finite-dimensional normed space, while we have
  -- a dependent product (i : N) → G.V i where each G.V i is finite-dimensional.

  -- The full proof would require either:
  -- (A) Showing the product of finitely many finite-dimensional spaces is
  --     finite-dimensional with appropriate normed space structure, OR
  -- (B) A version of Kakutani for product spaces

  -- For now, we outline the proof strategy assuming these technical details:

  -- Step 1: Action profile space properties
  have hA_convex : Convex ℝ G.ActionProfileSet := G.actionProfileSet_convex
  have hA_compact : IsCompact G.ActionProfileSet := G.actionProfileSet_isCompact
  have hA_nonempty : G.ActionProfileSet.Nonempty := G.actionProfileSet_nonempty

  -- Step 2: Best response properties
  have hBR_subset : ∀ a, G.BR a ⊆ G.ActionProfileSet :=
    fun a => G.BR_subset_actionProfileSet a
  have hBR_nonempty : ∀ a, (G.BR a).Nonempty :=
    fun a => G.BR_nonempty a hcont
  have hBR_convex : ∀ a, Convex ℝ (G.BR a) :=
    fun a => G.BR_convex a hquasi
  have hBR_closed : BR_has_closed_graph G hcont := G.BR_closed_graph hcont

  -- Step 3: Would apply Kakutani here (requires type matching work)
  -- Challenge: kakutani_fixed_point expects f : ↥s → Set V
  -- But G.BR : G.ActionProfile → Set G.ActionProfile
  -- Need to restrict BR to ActionProfileSet subtype

  sorry -- Apply Kakutani and extract Nash equilibrium from fixed point

/--
Corollary: For a finite strategic game represented with continuous payoff functions
on compact convex action sets, Nash equilibrium exists.
-/
theorem nash_equilibrium_exists
    (hcont : G.has_continuous_payoffs)
    (hquasi : G.has_quasiconcave_payoffs) :
    (G.ActionProfileSet ∩ {a | G.is_nash_equilibrium a}).Nonempty := by
  obtain ⟨a, ha⟩ := proposition_20_3 G hcont hquasi
  use a
  exact ⟨ha.1, ha⟩

end ContinuousStrategicGame
