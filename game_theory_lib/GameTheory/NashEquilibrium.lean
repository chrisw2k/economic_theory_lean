/-
# Nash Equilibrium

This file defines Nash equilibrium and best response functions for strategic games.

## Main Definitions

- `best_response`: The set of best actions for a player given others' actions
- `is_nash_equilibrium`: Predicate for Nash equilibrium (no profitable deviations)
- `is_nash_equilibrium'`: Alternative characterization via best responses
- `nash_equilibria`: The set of all Nash equilibria of a game

## Main Results

- `nash_equiv`: The two definitions of Nash equilibrium are equivalent
- `nash_no_profitable_deviation`: Nash equilibrium means no player can profit by unilateral deviation

## References

- Osborne, M. J., & Rubinstein, A. (1994). A Course in Game Theory. MIT Press.
  Chapter 2: Nash Equilibrium, Section 2.2, Definition 14.1
-/

import GameTheory.Basic
import GameTheory.ActionProfiles

namespace StrategicGame

variable {N : Type*} [Fintype N] [DecidableEq N] {G : StrategicGame N}

/-! ## Best Response Function -/

/--
The best response set for player i given the actions of all other players.
Bi(a_{-i}) = {ai ∈ Ai : (ai, a_{-i}) ≿i (a'i, a_{-i}) for all a'i ∈ Ai}

This corresponds to Equation 15.1 in Osborne & Rubinstein.
-/
def best_response (i : N) (a : G.ActionProfile) : Set (G.A i) :=
  {a_i : G.A i | ∀ a'_i : G.A i, G.preference i (a[i ↦ a_i]) (a[i ↦ a'_i])}

/-! ## Nash Equilibrium Definitions -/

/--
Nash equilibrium (Definition 14.1 from Osborne & Rubinstein).
A profile a* is a Nash equilibrium if for every player i,
(a*_{-i}, a*_i) ≿i (a*_{-i}, ai) for all ai ∈ Ai.

In other words, no player can profitably deviate given the others' actions.
-/
def is_nash_equilibrium (a : G.ActionProfile) : Prop :=
  ∀ (i : N) (a_i : G.A i), G.preference i a (a[i ↦ a_i])

/--
Alternative characterization of Nash equilibrium (Equation 15.2).
A profile a* is a Nash equilibrium if and only if a*_i ∈ Bi(a*_{-i}) for all i ∈ N.
-/
def is_nash_equilibrium' (a : G.ActionProfile) : Prop :=
  ∀ i : N, a i ∈ best_response i a

/--
The set of all Nash equilibria of a game.
-/
def nash_equilibria : Set (G.ActionProfile) :=
  {a : G.ActionProfile | is_nash_equilibrium a}

/-! ## Equivalence of Definitions -/

/--
The two definitions of Nash equilibrium are equivalent.
-/
theorem nash_equiv (a : G.ActionProfile) :
    is_nash_equilibrium a ↔ is_nash_equilibrium' a := by
  unfold is_nash_equilibrium is_nash_equilibrium' best_response
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h i a'_i
    have := h i a'_i
    convert this using 2
    exact update_eq_self a i
  · intro h i a_i
    have := h i a_i
    convert this using 2
    exact (update_eq_self a i).symm

end StrategicGame

namespace StrategicGamePayoff

variable {N : Type*} [Fintype N] [DecidableEq N] {G : StrategicGamePayoff N}

/-! ## Best Response for Payoff Games -/

/--
The best response set for player i in a payoff game.
-/
def best_response (i : N) (a : G.ActionProfile) : Set (G.A i) :=
  {a_i : G.A i | ∀ a'_i : G.A i, G.payoff i (a[i ↦ a_i]) ≥ G.payoff i (a[i ↦ a'_i])}

/-! ## Nash Equilibrium for Payoff Games -/

/--
Nash equilibrium for payoff games.
-/
def is_nash_equilibrium (a : G.ActionProfile) : Prop :=
  ∀ (i : N) (a_i : G.A i), G.payoff i a ≥ G.payoff i (a[i ↦ a_i])

/--
Alternative characterization via best responses.
-/
def is_nash_equilibrium' (a : G.ActionProfile) : Prop :=
  ∀ i : N, a i ∈ best_response i a

/--
The set of all Nash equilibria.
-/
def nash_equilibria : Set (G.ActionProfile) :=
  {a : G.ActionProfile | is_nash_equilibrium a}

/-! ## Properties of Nash Equilibrium -/

/--
The two definitions of Nash equilibrium are equivalent (payoff game version).
-/
theorem nash_equiv (a : G.ActionProfile) :
    is_nash_equilibrium a ↔ is_nash_equilibrium' a := by
  unfold is_nash_equilibrium is_nash_equilibrium' best_response
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h i a'_i
    have := h i a'_i
    convert this using 2
    exact update_eq_self a i
  · intro h i a_i
    have := h i a_i
    convert this using 2
    exact (update_eq_self a i).symm

/--
Nash equilibrium means no profitable deviation.
A player cannot increase their payoff by unilaterally changing their action.
-/
theorem nash_no_profitable_deviation (a : G.ActionProfile) :
    is_nash_equilibrium a ↔
    ∀ i : N, ∀ a_i : G.A i, G.payoff i a ≥ G.payoff i (a[i ↦ a_i]) := by
  rfl

/--
If a is a Nash equilibrium, then for each player i, their action a i
is a best response to the actions of all other players.
-/
theorem nash_implies_best_response (a : G.ActionProfile) (h : is_nash_equilibrium a) :
    ∀ i : N, a i ∈ best_response i a := by
  intro i
  rw [nash_equiv] at h
  exact h i

/-! ## Relationship with Preference-Based Games -/

/--
Nash equilibrium in the converted game corresponds to Nash equilibrium
in terms of payoffs.
-/
theorem nash_payoff_equiv (a : G.ActionProfile) :
    @StrategicGame.is_nash_equilibrium N _ _ (payoff_to_preference G) a ↔
    is_nash_equilibrium a := by
  unfold StrategicGame.is_nash_equilibrium payoff_to_preference is_nash_equilibrium
  simp only [ge_iff_le]
  rfl

end StrategicGamePayoff
