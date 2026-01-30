/-
# Action Profile Operations

This file defines operations on action profiles, particularly the notation for
updating a single player's action while keeping others fixed (a_{-i}, a_i notation).

## Main Definitions

- `update_action_at`: Update the action of a single player
- Notation `a[i ↦ ai]`: Convenient syntax for action profile updates
- Key lemmas about update operations

## References

- Osborne, M. J., & Rubinstein, A. (1994). A Course in Game Theory. MIT Press.
  Chapter 2: Nash Equilibrium. The notation (a_{-i}, a_i) appears throughout.
-/

import GameTheory.Basic
import Mathlib.Logic.Function.Basic

namespace StrategicGame

variable {N : Type*} [Fintype N] [DecidableEq N] {G : StrategicGame N}

/-! ## Action Profile Updates -/

/--
Update the action of player `i` in action profile `a` to `a_i`.
This corresponds to the notation (a_{-i}, a_i) in Osborne & Rubinstein,
where a_{-i} represents the actions of all players except i.
-/
def update_action_at (a : G.ActionProfile) (i : N) (a_i : G.A i) :
    G.ActionProfile :=
  Function.update a i a_i

/-- Notation for updating action profiles: `a[i ↦ ai]` means update action of player i to ai -/
notation:max a "[" i " ↦ " ai "]" => update_action_at a i ai

/-! ## Basic Properties of Action Profile Updates -/

/--
Retrieving the updated value: if we update player i's action to a_i,
then the resulting profile assigns a_i to player i.
-/
theorem update_get_same (a : G.ActionProfile) (i : N) (x : G.A i) :
    a[i ↦ x] i = x := by
  unfold update_action_at Function.update
  simp

/--
Retrieving other players' actions: if we update player i's action,
the actions of other players j ≠ i remain unchanged.
-/
theorem update_get_other (a : G.ActionProfile) (i j : N) (h : j ≠ i) (x : G.A i) :
    a[i ↦ x] j = a j := by
  unfold update_action_at Function.update
  simp [h]

/--
Updating twice at the same position: the second update overwrites the first.
-/
theorem update_update_same (a : G.ActionProfile) (i : N) (x y : G.A i) :
    a[i ↦ x][i ↦ y] = a[i ↦ y] := by
  unfold update_action_at Function.update
  funext j
  simp
  split
  · rfl
  · rfl

/--
Updating at different positions commutes.
-/
theorem update_update_comm (a : G.ActionProfile) (i j : N) (h : i ≠ j)
    (x : G.A i) (y : G.A j) :
    a[i ↦ x][j ↦ y] = a[j ↦ y][i ↦ x] := by
  unfold update_action_at
  exact Function.update_comm h x y a

/--
If an action profile already has value x at position i, updating it to x doesn't change it.
-/
theorem update_eq_self (a : G.ActionProfile) (i : N) :
    a[i ↦ a i] = a := by
  unfold update_action_at Function.update
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

/-! ## Semantic Properties -/

/--
Two action profiles are equal if and only if they assign the same action to every player.
-/
theorem actionProfile_ext {a b : G.ActionProfile} :
    a = b ↔ ∀ i : N, a i = b i := by
  constructor
  · intro h i
    rw [h]
  · intro h
    funext i
    exact h i

/--
An action profile is uniquely determined by one player's action and the remaining profile.
More precisely, if we take an action profile b, update it at position i to get a_i,
and the result equals a, then a i = a_i and a j = b j for all j ≠ i.
-/
theorem update_characterizes (a b : G.ActionProfile) (i : N) (a_i : G.A i)
    (h : b[i ↦ a_i] = a) :
    a i = a_i ∧ ∀ j : N, j ≠ i → a j = b j := by
  constructor
  · rw [←h]
    exact update_get_same b i a_i
  · intro j hj
    rw [←h]
    exact update_get_other b i j hj a_i

end StrategicGame

namespace StrategicGamePayoff

variable {N : Type*} [Fintype N] [DecidableEq N] {G : StrategicGamePayoff N}

/-! ## Action Profile Updates for Payoff Games -/

/--
Update the action of player `i` in action profile `a` to `a_i` (payoff game version).
-/
def update_action_at (a : G.ActionProfile) (i : N) (a_i : G.A i) :
    G.ActionProfile :=
  Function.update a i a_i

/-- Notation for updating action profiles in payoff games -/
notation:max a "[" i " ↦ " ai "]" => update_action_at a i ai

/-! ## Basic Properties (Payoff Game Version) -/

theorem update_get_same (a : G.ActionProfile) (i : N) (x : G.A i) :
    a[i ↦ x] i = x := by
  unfold update_action_at Function.update
  simp

theorem update_get_other (a : G.ActionProfile) (i j : N) (h : j ≠ i) (x : G.A i) :
    a[i ↦ x] j = a j := by
  unfold update_action_at Function.update
  simp [h]

theorem update_update_same (a : G.ActionProfile) (i : N) (x y : G.A i) :
    a[i ↦ x][i ↦ y] = a[i ↦ y] := by
  unfold update_action_at Function.update
  funext j
  simp
  split
  · rfl
  · rfl

theorem update_update_comm (a : G.ActionProfile) (i j : N) (h : i ≠ j)
    (x : G.A i) (y : G.A j) :
    a[i ↦ x][j ↦ y] = a[j ↦ y][i ↦ x] := by
  unfold update_action_at
  exact Function.update_comm h x y a

theorem update_eq_self (a : G.ActionProfile) (i : N) :
    a[i ↦ a i] = a := by
  unfold update_action_at Function.update
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

theorem actionProfile_ext {a b : G.ActionProfile} :
    a = b ↔ ∀ i : N, a i = b i := by
  constructor
  · intro h i
    rw [h]
  · intro h
    funext i
    exact h i

end StrategicGamePayoff
