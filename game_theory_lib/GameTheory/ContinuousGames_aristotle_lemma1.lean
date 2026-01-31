/-
Isolated lemma for Aristotle: best_response_set_nonempty
-/

import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Topology.Compactness.Compact
import GameTheory.Basic
import GameTheory.ActionProfiles

structure ContinuousStrategicGame (N : Type*) [Fintype N] [DecidableEq N] where
  (V : N → Type*)
  [normed : ∀ i, NormedAddCommGroup (V i)]
  [space : ∀ i, NormedSpace ℝ (V i)]
  [findim : ∀ i, FiniteDimensional ℝ (V i)]
  (A : (i : N) → Set (V i))
  (compact_A : ∀ i, IsCompact (A i))
  (convex_A : ∀ i, Convex ℝ (A i))
  (nonempty_A : ∀ i, (A i).Nonempty)
  (payoff : (i : N) → ((j : N) → V j) → ℝ)

namespace ContinuousStrategicGame

variable {N : Type*} [Fintype N] [DecidableEq N] (G : ContinuousStrategicGame N)

instance instNormedAddCommGroup (i : N) : NormedAddCommGroup (G.V i) := G.normed i
instance instNormedSpace (i : N) : NormedSpace ℝ (G.V i) := G.space i
instance instFiniteDimensional (i : N) : FiniteDimensional ℝ (G.V i) := G.findim i

abbrev ActionProfile := (i : N) → G.V i

def has_continuous_payoffs : Prop :=
  ∀ i : N, Continuous (fun a : G.ActionProfile => G.payoff i a)

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
  sorry

end ContinuousStrategicGame
