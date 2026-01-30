/-
# Basic Game Theory Definitions

This file contains the core definitions of strategic games as defined in
Osborne and Rubinstein's "A Course in Game Theory", Chapter 2, Section 2.1.

## Main Definitions

- `StrategicGame`: A strategic game with preference relations (Definition 11.1)
- `ActionProfile`: Type alias for action profiles
- `StrategicGamePayoff`: A strategic game with payoff functions
- `payoff_to_preference`: Conversion from payoff games to preference games
- `StrategicGame.is_finite`: Predicate for finite games

## References

- Osborne, M. J., & Rubinstein, A. (1994). A Course in Game Theory. MIT Press.
  Chapter 2: Nash Equilibrium, Section 2.1: Strategic Games, Definition 11.1
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Real.Basic

/-! ## Strategic Games with Preference Relations -/

/--
A strategic game consists of a finite set of players, actions available to each player,
and preference relations over action profiles.

This corresponds to Definition 11.1 in Osborne & Rubinstein.
-/
structure StrategicGame (N : Type*) [Fintype N] [DecidableEq N] where
  /-- Actions available to each player -/
  (A : N → Type*)
  /-- Each player has at least one action available -/
  (nonempty_A : ∀ i, Nonempty (A i))
  /-- Preference relation for each player over action profiles.
      `preference i a b` means player i weakly prefers a to b (a ≿ᵢ b) -/
  (preference : (i : N) → ((i : N) → A i) → ((i : N) → A i) → Prop)

namespace StrategicGame

variable {N : Type*} [Fintype N] [DecidableEq N] (G : StrategicGame N)

/--
An action profile is a choice of action for each player.
This corresponds to the notation a = (aⱼ)ⱼ∈N in Osborne & Rubinstein.
-/
abbrev ActionProfile := (i : N) → G.A i

/--
A strategic game is finite if each player has finitely many actions available.
-/
def is_finite : Prop := ∀ i : N, Nonempty (Fintype (G.A i))

/--
The set of actions available to player i.
-/
def actions (i : N) : Type* := G.A i

/--
Each player has at least one available action (nonemptiness).
-/
theorem actions_nonempty (i : N) : Nonempty (G.A i) :=
  G.nonempty_A i

end StrategicGame

/-! ## Strategic Games with Payoff Functions -/

/--
A strategic game with payoff (utility) functions.
When preferences can be represented by real-valued payoff functions,
we denote the game as ⟨N, (Aᵢ), (uᵢ)⟩.

This corresponds to the payoff function representation mentioned in
Osborne & Rubinstein, page 13.
-/
structure StrategicGamePayoff (N : Type*) [Fintype N] [DecidableEq N] where
  /-- Actions available to each player -/
  (A : N → Type*)
  /-- Each player has at least one action available -/
  (nonempty_A : ∀ i, Nonempty (A i))
  /-- Payoff (utility) function for each player.
      `payoff i a` gives the payoff to player i at action profile a -/
  (payoff : (i : N) → ((i : N) → A i) → ℝ)

namespace StrategicGamePayoff

variable {N : Type*} [Fintype N] [DecidableEq N] (G : StrategicGamePayoff N)

/--
An action profile for a payoff game.
-/
abbrev ActionProfile := (i : N) → G.A i

/--
A payoff game is finite if each player has finitely many actions available.
-/
def is_finite : Prop := ∀ i : N, Nonempty (Fintype (G.A i))

/--
The set of actions available to player i.
-/
def actions (i : N) : Type* := G.A i

/--
Each player has at least one available action (nonemptiness).
-/
theorem actions_nonempty (i : N) : Nonempty (G.A i) :=
  G.nonempty_A i

end StrategicGamePayoff

/-! ## Conversion Between Representations -/

/--
Convert a strategic game with payoff functions to one with preference relations.
Player i prefers action profile a to b if and only if their payoff at a is
at least as high as their payoff at b.
-/
def payoff_to_preference {N : Type*} [Fintype N] [DecidableEq N]
    (G : StrategicGamePayoff N) : StrategicGame N where
  A := G.A
  nonempty_A := G.nonempty_A
  preference := fun i a b => G.payoff i a ≥ G.payoff i b

namespace payoff_to_preference

variable {N : Type*} [Fintype N] [DecidableEq N] (G : StrategicGamePayoff N)

/--
Preference in the converted game corresponds to payoff comparison.
-/
theorem preference_iff (i : N) (a b : G.ActionProfile) :
    (payoff_to_preference G).preference i a b ↔ G.payoff i a ≥ G.payoff i b := by
  rfl

end payoff_to_preference
