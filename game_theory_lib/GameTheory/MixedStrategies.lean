/-
# Mixed Strategies for Strategic Games

This file formalizes mixed strategies (probability distributions over actions) for
finite strategic games, following Osborne & Rubinstein Chapter 3.

## Main Definitions

- `Simplex n`: The probability simplex in ℝⁿ
- `ProbSimplex A`: Probability distributions over a finite type A
- `expectedPayoff`: Expected utility of mixed strategy profiles
- `isMixedNashEquilibrium`: Nash equilibrium in mixed strategies

## Main Results

- Probability simplex is nonempty, compact, and convex
- Expected payoff is continuous and quasi-concave
- Connection to Euclidean strategic games (enables use of Proposition 20.3)

## References

- Osborne, M. J., & Rubinstein, A. (1994). A Course in Game Theory. MIT Press.
  Chapter 3: Mixed, Correlated, and Evolutionary Equilibrium
  Section 3.1: Mixed Strategy Nash Equilibrium
-/

import GameTheory.Basic
import GameTheory.NashEquilibrium
import GameTheory.EuclideanGames
import GameTheory.EuclideanNashExistence
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Bornology.Constructions
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Fintype.Card

/-! ## Probability Simplex -/

/--
The probability simplex in ℝⁿ: the set of probability distributions over n outcomes.

This is the set {p ∈ ℝⁿ | pᵢ ≥ 0 for all i, and Σᵢ pᵢ = 1}.
Geometrically, it's a convex polytope in ℝⁿ.
-/
def Simplex (n : ℕ) : Set (Fin n → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ Finset.sum Finset.univ p = 1}

namespace Simplex

variable {n : ℕ}

/--
The uniform distribution is in the simplex.
-/
theorem nonempty (hn : 0 < n) : (Simplex n).Nonempty := by
  use fun _ => (1 : ℝ) / n
  constructor
  · intro i
    apply div_nonneg
    · norm_num
    · exact Nat.cast_nonneg n
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul]
    have h_pos : (n : ℝ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    field_simp [h_pos]

/--
All coordinates of a point in the simplex are in [0,1].
-/
theorem mem_Icc (hp : p ∈ Simplex n) (i : Fin n) : p i ∈ Set.Icc 0 1 := by
  constructor
  · -- Lower bound: p i ≥ 0
    exact hp.1 i
  · -- Upper bound: p i ≤ 1
    -- Since p i ≤ Σⱼ p j = 1 (all other terms are ≥ 0)
    have h_sum : Finset.sum Finset.univ p = 1 := hp.2
    have h_nonneg : ∀ j, 0 ≤ p j := hp.1
    rw [← h_sum]
    exact Finset.single_le_sum (fun j _ => h_nonneg j) (Finset.mem_univ i)

/--
The simplex is bounded (contained in the unit cube).
-/
theorem bounded : Bornology.IsBounded (Simplex n) := by
  -- Simplex ⊆ [0,1]ⁿ which is bounded
  have h_subset : Simplex n ⊆ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1) := by
    intro p hp
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
    exact fun i => mem_Icc hp i
  apply Bornology.IsBounded.subset _ h_subset
  -- The unit cube [0,1]ⁿ is bounded (product of bounded intervals)
  apply Bornology.IsBounded.pi
  intro i
  exact isCompact_Icc.isBounded

/--
The simplex is closed as an intersection of closed sets.
-/
theorem isClosed : IsClosed (Simplex n) := by
  -- Simplex = (⋂ i, {p | 0 ≤ p i}) ∩ {p | ∑ i, p i = 1}
  have h_eq : Simplex n = (⋂ i : Fin n, {p | 0 ≤ p i}) ∩ {p | Finset.sum Finset.univ p = 1} := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Simplex]
  rw [h_eq]
  apply IsClosed.inter
  · -- Each {p | 0 ≤ p i} is closed (half-space)
    apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const (continuous_apply i)
  · -- {p | ∑ p i = 1} is closed (hyperplane)
    apply isClosed_eq
    · exact continuous_finset_sum Finset.univ (fun i _ => continuous_apply i)
    · exact continuous_const

/--
The simplex is compact (closed and bounded in finite-dimensional space).
-/
theorem isCompact [Finite (Fin n)] : IsCompact (Simplex n) := by
  -- Simplex is a closed subset of the compact unit cube
  have h_subset : Simplex n ⊆ Set.pi Set.univ (fun _ => Set.Icc 0 1) := by
    intro p hp
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
    exact fun i => mem_Icc hp i
  have h_compact_cube : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) := by
    apply isCompact_univ_pi
    intro i
    exact isCompact_Icc
  exact IsCompact.of_isClosed_subset h_compact_cube isClosed h_subset

/--
The simplex is convex.
-/
theorem convex : Convex ℝ (Simplex n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    apply add_nonneg
    · apply mul_nonneg ha (hx.1 i)
    · apply mul_nonneg hb (hy.1 i)
  · simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, smul_eq_mul]
    calc ∑ i, a * x i + ∑ i, b * y i
        = a * ∑ i, x i + b * ∑ i, y i := by rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = a * 1 + b * 1 := by rw [hx.2, hy.2]
      _ = a + b := by ring
      _ = 1 := hab

end Simplex

/-! ## Probability Distributions over Finite Types -/

/--
The set of probability distributions over a finite type A.

This is isomorphic to the simplex in ℝⁿ where n = |A|.
-/
def ProbSimplex (A : Type*) [Fintype A] [DecidableEq A] : Set (A → ℝ) :=
  {p | (∀ a, 0 ≤ p a) ∧ Finset.sum Finset.univ p = 1}

namespace ProbSimplex

variable {A : Type*} [Fintype A] [DecidableEq A]

/--
The uniform distribution over A.
-/
noncomputable def uniform (hne : Nonempty A) : A → ℝ :=
  fun _ => 1 / Fintype.card A

theorem uniform_mem (hne : Nonempty A) : uniform hne ∈ ProbSimplex A := by
  constructor
  · intro a
    unfold uniform
    apply div_nonneg
    · norm_num
    · exact Nat.cast_nonneg _
  · unfold uniform
    simp only [Finset.sum_const, Finset.card_univ]
    rw [nsmul_eq_mul]
    have h_pos : (Fintype.card A : ℝ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      exact Fintype.card_ne_zero
    field_simp [h_pos]

theorem nonempty (hne : Nonempty A) : (ProbSimplex A).Nonempty :=
  ⟨uniform hne, uniform_mem hne⟩

end ProbSimplex

/-! ## Expected Payoff for Mixed Strategies -/

namespace StrategicGamePayoff

variable {N : Type*} [Fintype N] [DecidableEq N] (G : StrategicGamePayoff N)
variable [∀ i, Fintype (G.A i)] [∀ i, DecidableEq (G.A i)]

/--
The expected payoff for player i when all players use mixed strategies.

This is the formula: Uᵢ(α) = Σₐ∈A (Πⱼ∈N αⱼ(aⱼ)) · uᵢ(a)

where α is a profile of mixed strategies (probability distributions).
-/
def expectedPayoff (i : N) (α : (j : N) → (G.A j → ℝ)) : ℝ :=
  Finset.sum (Finset.univ : Finset G.ActionProfile) fun a =>
    (Finset.prod (Finset.univ : Finset N) fun j => α j (a j)) * G.payoff i a

/--
A mixed strategy profile is a mixed strategy Nash equilibrium if no player
can improve their expected payoff by unilaterally changing their mixed strategy.
-/
def isMixedNashEquilibrium (α : (i : N) → (G.A i → ℝ)) : Prop :=
  (∀ i, α i ∈ ProbSimplex (G.A i)) ∧
  ∀ (i : N) (α'ᵢ : G.A i → ℝ), α'ᵢ ∈ ProbSimplex (G.A i) →
    expectedPayoff G i α ≥ expectedPayoff G i (Function.update α i α'ᵢ)

/-! ## Properties of Expected Payoff -/

/--
Helper lemma: Product decomposition when one player's strategy is updated.

When player i's strategy is σ and others use α, the probability of action profile a is:
(∏ⱼ≠ᵢ αⱼ(aⱼ)) · σ(aᵢ)
-/
lemma prod_update_eq (i : N) (α : (j : N) → (G.A j → ℝ))
    (σ : G.A i → ℝ) (a : G.ActionProfile) :
    Finset.prod Finset.univ (fun j => Function.update α i σ j (a j)) =
    (Finset.prod (Finset.univ.erase i) fun j => α j (a j)) * σ (a i) := by
  -- Split the product: ∏ⱼ∈N (update α i σ j (a j)) = (term for i) · (product over N \ {i})
  rw [← Finset.mul_prod_erase Finset.univ (fun j => Function.update α i σ j (a j)) (Finset.mem_univ i)]
  -- Now LHS = (update α i σ i (a i)) · ∏ⱼ∈N\{i} (update α i σ j (a j))
  -- Simplify the term for i
  simp only [Function.update_self]
  -- Now LHS = σ(a i) · ∏ⱼ∈N\{i} (update α i σ j (a j))
  -- Simplify the product over N \ {i} - update doesn't affect j ≠ i
  have h_prod : ∏ j ∈ Finset.univ.erase i, Function.update α i σ j (a j) =
                ∏ j ∈ Finset.univ.erase i, α j (a j) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Finset.mem_erase] at hj
    rw [Function.update_of_ne hj.1]
  rw [h_prod]
  -- Now LHS = σ(a i) · ∏ⱼ∈N\{i} α j (a j)
  -- Rearrange to match RHS
  ring

/--
**Linearity in own strategy**: The expected payoff is linear in player i's strategy
when other players' strategies are fixed.

This is the key property for proving quasi-concavity.
-/
theorem expectedPayoff_linear_in_own_strategy
    (i : N) (α : (j : N) → (G.A j → ℝ))
    (β γ : G.A i → ℝ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    expectedPayoff G i (Function.update α i (t • β + (1 - t) • γ)) =
    t * expectedPayoff G i (Function.update α i β) +
    (1 - t) * expectedPayoff G i (Function.update α i γ) := by
  unfold expectedPayoff
  simp_rw [prod_update_eq G i]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_add, add_mul]
  rw [Finset.sum_add_distrib]
  congr 1 <;> {
    simp_rw [mul_comm (∏ j ∈ Finset.univ.erase i, α j _), mul_assoc, ← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  }

/--
**Multilinearity**: Expected payoff is linear in each player's strategy separately.

This is a more general version of linearity that works for any player j's strategy,
not just player i's own strategy.
-/
theorem expectedPayoff_multilinear (i : N) (α : (j : N) → (G.A j → ℝ))
    (j : N) (β γ : G.A j → ℝ) (t : ℝ) :
    expectedPayoff G i (Function.update α j (t • β + (1 - t) • γ)) =
    t * expectedPayoff G i (Function.update α j β) +
    (1 - t) * expectedPayoff G i (Function.update α j γ) := by
  unfold expectedPayoff
  simp_rw [prod_update_eq G j]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_add, add_mul]
  rw [Finset.sum_add_distrib]
  congr 1 <;> {
    simp_rw [mul_comm (∏ k ∈ Finset.univ.erase j, α k _), mul_assoc, ← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  }

end StrategicGamePayoff

/-! ## Embedding into Euclidean Space -/

namespace StrategicGamePayoff

variable {N : Type*} [Fintype N] [DecidableEq N] (G : StrategicGamePayoff N)
variable [∀ i, Fintype (G.A i)] [∀ i, DecidableEq (G.A i)]

/--
Canonical bijection between a finite type and Fin n.
-/
noncomputable def finEquiv (i : N) : G.A i ≃ Fin (Fintype.card (G.A i)) :=
  Fintype.equivFin (G.A i)

/--
Embedding of probability simplex into Euclidean space.
This allows us to view mixed strategies as points in ℝⁿ.
-/
noncomputable def simplexToEuclidean (i : N) (p : G.A i → ℝ) :
    EuclideanSpace ℝ (Fin (Fintype.card (G.A i))) :=
  fun k => p ((finEquiv G i).symm k)

/--
The mixed strategy space for player i as a subset of Euclidean space.
-/
def mixedStrategySpace (i : N) : Set (EuclideanSpace ℝ (Fin (Fintype.card (G.A i)))) :=
  simplexToEuclidean G i '' ProbSimplex (G.A i)

/--
Decode a point in Euclidean space back to a probability distribution.
-/
noncomputable def euclideanToSimplex (i : N) (x : EuclideanSpace ℝ (Fin (Fintype.card (G.A i)))) :
    G.A i → ℝ :=
  fun a => x ((finEquiv G i) a)

/-! ## Encoding/Decoding Lemmas -/

/--
**Round-trip property**: Decoding an encoded probability distribution gives back the original.
This is the key infrastructure lemma for showing the Nash equilibrium transfers correctly.
-/
lemma euclidean_simplex_inverse (i : N) (p : G.A i → ℝ) :
    euclideanToSimplex G i (simplexToEuclidean G i p) = p := by
  ext a
  unfold euclideanToSimplex simplexToEuclidean
  simp only [Equiv.symm_apply_apply]

/--
**Continuity of encoding**: The embedding from probability distributions to Euclidean space is continuous.
-/
lemma simplexToEuclidean_continuous (i : N) :
    Continuous (simplexToEuclidean G i : (G.A i → ℝ) → EuclideanSpace ℝ (Fin (Fintype.card (G.A i)))) := by
  -- simplexToEuclidean G i p = fun k => p ((finEquiv G i).symm k)
  -- This is continuous because it's a Pi type of continuous functions
  apply continuous_pi
  intro k
  -- Each coordinate k ↦ p ((finEquiv G i).symm k) is a projection, hence continuous
  exact continuous_apply ((finEquiv G i).symm k)

/--
`euclideanToSimplex` preserves scalar multiplication (it's a linear map).
-/
lemma euclideanToSimplex_smul (i : N) (c : ℝ) (x : EuclideanSpace ℝ (Fin (Fintype.card (G.A i)))) :
    euclideanToSimplex G i (c • x) = c • euclideanToSimplex G i x := by
  ext a
  unfold euclideanToSimplex
  simp [Pi.smul_apply]

/--
`euclideanToSimplex` preserves addition (it's a linear map).
-/
lemma euclideanToSimplex_add (i : N) (x y : EuclideanSpace ℝ (Fin (Fintype.card (G.A i)))) :
    euclideanToSimplex G i (x + y) = euclideanToSimplex G i x + euclideanToSimplex G i y := by
  ext a
  unfold euclideanToSimplex
  simp [Pi.add_apply]

/-! ## Mixed Extension as Euclidean Game -/

/--
The mixed extension of a finite strategic game as an Euclidean strategic game.

This transforms a finite game into a game on probability simplices, which are
compact convex subsets of Euclidean space. By Proposition 20.3, this game has
a Nash equilibrium, which corresponds to a mixed strategy Nash equilibrium of
the original game.
-/
noncomputable def mixedExtension : EuclideanStrategicGame N where
  dim := fun i => Fintype.card (G.A i)
  A := fun i => mixedStrategySpace G i
  compact_A := by
    intro i
    -- The mixed strategy space is the image of a compact simplex under a continuous map
    unfold mixedStrategySpace
    -- Step 1: Show ProbSimplex (G.A i) is compact
    -- ProbSimplex is a closed subset of the compact unit cube [0,1]^(G.A i)
    have h_prob_compact : IsCompact (ProbSimplex (G.A i)) := by
      -- Define the unit cube
      let unit_cube := Set.pi Set.univ (fun _ : G.A i => Set.Icc (0 : ℝ) 1)
      -- Show ProbSimplex ⊆ unit_cube
      have h_subset : ProbSimplex (G.A i) ⊆ unit_cube := by
        intro p hp
        show p ∈ Set.pi Set.univ (fun _ : G.A i => Set.Icc (0 : ℝ) 1)
        intro a _
        constructor
        · exact hp.1 a
        · have h_sum := hp.2
          rw [← h_sum]
          exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ a)
      -- Show unit_cube is compact
      have h_cube_compact : IsCompact unit_cube := by
        apply isCompact_univ_pi
        intro _
        exact isCompact_Icc
      -- Show ProbSimplex is closed
      have h_closed : IsClosed (ProbSimplex (G.A i)) := by
        unfold ProbSimplex
        rw [Set.setOf_and]
        apply IsClosed.inter
        · -- {p | ∀ a, 0 ≤ p a} is closed
          have : {p : G.A i → ℝ | ∀ a, 0 ≤ p a} = ⋂ a : G.A i, {p | 0 ≤ p a} := by
            ext p
            simp only [Set.mem_setOf_eq, Set.mem_iInter]
          rw [this]
          apply isClosed_iInter
          intro a
          exact isClosed_le continuous_const (continuous_apply a)
        · -- {p | ∑ a, p a = 1} is closed
          apply isClosed_eq
          · exact continuous_finset_sum Finset.univ (fun a _ => continuous_apply a)
          · exact continuous_const
      -- Apply IsCompact.of_isClosed_subset
      exact IsCompact.of_isClosed_subset h_cube_compact h_closed h_subset
    -- Step 2: Apply IsCompact.image with the continuous embedding
    exact IsCompact.image h_prob_compact (simplexToEuclidean_continuous G i)
  convex_A := by
    intro i
    -- The embedding preserves convex combinations
    intro x hx y hy a b ha hb hab
    -- x and y are images of probability distributions
    obtain ⟨px, hpx, rfl⟩ := hx
    obtain ⟨py, hpy, rfl⟩ := hy
    -- Show that the convex combination is also in the image
    use fun k => a * px k + b * py k
    constructor
    · -- Show this is a probability distribution
      constructor
      · intro k
        apply add_nonneg
        · exact mul_nonneg ha (hpx.1 k)
        · exact mul_nonneg hb (hpy.1 k)
      · simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hpx.2, hpy.2]
        ring_nf
        exact hab
    · -- Show it equals the convex combination of the images
      ext k
      unfold simplexToEuclidean
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rfl
  nonempty_A := by
    intro i
    -- The uniform distribution is in the probability simplex
    have h := ProbSimplex.nonempty (G.nonempty_A i)
    obtain ⟨p, hp⟩ := h
    use simplexToEuclidean G i p
    exact Set.mem_image_of_mem _ hp
  payoff := fun i α => expectedPayoff G i (fun j => euclideanToSimplex G j (α j))

/-! ## Proposition 33.1: Mixed Strategy Nash Equilibrium Existence -/

/--
**Proposition 33.1 (Nash 1950): Every finite strategic game has a mixed strategy
Nash equilibrium.**

This is the fundamental existence theorem for game theory. It shows that when players
are allowed to randomize over their actions (use mixed strategies), an equilibrium
always exists.

**Proof strategy**:
1. Construct the mixed extension as an Euclidean strategic game
2. Show it satisfies the hypotheses of Proposition 20.3 (Kakutani):
   - Action sets are compact, convex, nonempty subsets of Euclidean space
   - Payoffs are continuous and quasi-concave
3. Apply Proposition 20.3 to get a Nash equilibrium
4. This equilibrium in the mixed extension is a mixed Nash equilibrium of the original game

**References**:
- Osborne & Rubinstein (1994), Proposition 33.1, page 33
- Nash (1950), "Equilibrium Points in N-Person Games", PNAS
-/
theorem proposition_33_1 :
    ∃ (α : (i : N) → (G.A i → ℝ)), isMixedNashEquilibrium G α := by
  -- Step 1: Construct the mixed extension
  let G_mixed := mixedExtension G

  -- Step 2: Prove the mixed extension has continuous payoffs
  have hcont : G_mixed.has_continuous_payoffs := by
    intro i
    -- Expected payoff = ∑ₐ (∏ⱼ αⱼ(aⱼ)) · uᵢ(a) is continuous in α
    -- G_mixed.payoff i α = expectedPayoff G i (fun j => euclideanToSimplex G j (α j))
    -- We need to show: Continuous (fun α => G_mixed.payoff i α)
    -- Since G_mixed is mixedExtension G, this expands to:
    -- Continuous (fun α => expectedPayoff G i (fun j => euclideanToSimplex G j (α j)))
    --
    -- expectedPayoff G i σ = ∑ₐ∈ActionProfile (∏ⱼ∈N σ j (a j)) * G.payoff i a
    -- So we need: Continuous (fun α => ∑ₐ (∏ⱼ (euclideanToSimplex G j (α j)) (a j)) * G.payoff i a)
    --
    -- Proof: Finite sums and products of continuous functions are continuous
    apply continuous_finset_sum
    intro a _
    apply Continuous.mul
    · apply continuous_finset_prod
      intro j _
      -- Need: Continuous (fun α => euclideanToSimplex G j (α j) (a j))
      -- By definition: euclideanToSimplex G j x = fun a => x ((finEquiv G j) a)
      -- So: euclideanToSimplex G j (α j) (a j) = α j ((finEquiv G j) (a j))
      -- This is continuous as evaluation at a fixed index
      unfold euclideanToSimplex
      -- Now need: Continuous (fun α => α j ((finEquiv G j) (a j)))
      exact Continuous.comp (continuous_apply ((finEquiv G j) (a j))) (continuous_apply j)
    · exact continuous_const

  -- Step 3: Prove the mixed extension has quasi-concave payoffs
  have hquasi : G_mixed.has_quasiconcave_payoffs := by
    -- Need to show: QuasiconcaveOn ℝ (G_mixed.A i) (fun a_i => G_mixed.payoff i (Function.update a_minus_i i a_i))
    -- Quasi-concave means: ∀ r, Convex ℝ {x ∈ s | r ≤ f x}
    -- For linear functions, this holds because weighted averages preserve the inequality
    intro i a_minus_i ha_minus_i
    intro r
    -- Show: Convex ℝ {a_i ∈ G_mixed.A i | r ≤ G_mixed.payoff i (Function.update a_minus_i i a_i)}
    intro x hx y hy a b ha_nn hb_nn hab
    constructor
    · -- Show: a • x + b • y ∈ G_mixed.A i
      apply G_mixed.convex_A i hx.1 hy.1
      exact ha_nn
      exact hb_nn
      exact hab
    · -- Show: r ≤ G_mixed.payoff i (Function.update a_minus_i i (a • x + b • y))
      -- The goal has a lambda, need to beta-reduce
      show r ≤ G_mixed.payoff i (Function.update a_minus_i i (a • x + b • y))
      -- By linearity: payoff i (update ... (a•x + b•y)) = a * payoff i (update ... x) + b * payoff i (update ... y)
      have h_linear : G_mixed.payoff i (Function.update a_minus_i i (a • x + b • y)) =
                      a * G_mixed.payoff i (Function.update a_minus_i i x) +
                      b * G_mixed.payoff i (Function.update a_minus_i i y) := by
        -- G_mixed.payoff i α = expectedPayoff G i (fun j => euclideanToSimplex G j (α j))
        -- Apply expectedPayoff_linear_in_own_strategy
        -- First establish b = 1 - a so we can match the linearity lemma
        have h_b_eq : b = 1 - a := by linarith
        -- Rewrite using b = 1 - a
        rw [h_b_eq]
        -- Now show: payoff (a•x + (1-a)•y) = a * payoff x + (1-a) * payoff y
        -- This follows from expectedPayoff_linear_in_own_strategy
        have h_lhs : G_mixed.payoff i (Function.update a_minus_i i (a • x + (1 - a) • y)) =
                     expectedPayoff G i (Function.update (fun j => euclideanToSimplex G j (a_minus_i j)) i
                       (a • euclideanToSimplex G i x + (1 - a) • euclideanToSimplex G i y)) := by
          show expectedPayoff G i (fun j => euclideanToSimplex G j (Function.update a_minus_i i (a • x + (1 - a) • y) j)) =
               expectedPayoff G i (Function.update (fun j => euclideanToSimplex G j (a_minus_i j)) i
                 (a • euclideanToSimplex G i x + (1 - a) • euclideanToSimplex G i y))
          congr 1
          funext j
          unfold Function.update
          split
          · next h =>
            -- j = i case
            simp only [dif_pos h]
            cases h
            rw [euclideanToSimplex_add, euclideanToSimplex_smul, euclideanToSimplex_smul]
          · next h =>
            -- j ≠ i case
            simp only [dif_neg h]
        have h_rhs_x : G_mixed.payoff i (Function.update a_minus_i i x) =
                       expectedPayoff G i (Function.update (fun j => euclideanToSimplex G j (a_minus_i j)) i
                         (euclideanToSimplex G i x)) := by
          show expectedPayoff G i (fun j => euclideanToSimplex G j (Function.update a_minus_i i x j)) =
               expectedPayoff G i (Function.update (fun j => euclideanToSimplex G j (a_minus_i j)) i
                 (euclideanToSimplex G i x))
          congr 1
          funext j
          unfold Function.update
          split
          · next h => simp only [dif_pos h]; cases h; rfl
          · next h => simp only [dif_neg h]
        have h_rhs_y : G_mixed.payoff i (Function.update a_minus_i i y) =
                       expectedPayoff G i (Function.update (fun j => euclideanToSimplex G j (a_minus_i j)) i
                         (euclideanToSimplex G i y)) := by
          show expectedPayoff G i (fun j => euclideanToSimplex G j (Function.update a_minus_i i y j)) =
               expectedPayoff G i (Function.update (fun j => euclideanToSimplex G j (a_minus_i j)) i
                 (euclideanToSimplex G i y))
          congr 1
          funext j
          unfold Function.update
          split
          · next h => simp only [dif_pos h]; cases h; rfl
          · next h => simp only [dif_neg h]
        rw [h_lhs, h_rhs_x, h_rhs_y]
        exact expectedPayoff_linear_in_own_strategy G i
          (fun j => euclideanToSimplex G j (a_minus_i j))
          (euclideanToSimplex G i x)
          (euclideanToSimplex G i y)
          a
          ⟨ha_nn, by linarith⟩
      rw [h_linear]
      -- Since r ≤ f(x) and r ≤ f(y), and a + b = 1, we have: r = a*r + b*r ≤ a*f(x) + b*f(y)
      have hx_ineq : r ≤ G_mixed.payoff i (Function.update a_minus_i i x) := hx.2
      have hy_ineq : r ≤ G_mixed.payoff i (Function.update a_minus_i i y) := hy.2
      calc r = (a + b) * r := by rw [hab, one_mul]
           _ = a * r + b * r := by ring
           _ ≤ a * G_mixed.payoff i (Function.update a_minus_i i x) +
               b * G_mixed.payoff i (Function.update a_minus_i i y) := by
                 apply add_le_add
                 · exact mul_le_mul_of_nonneg_left hx_ineq ha_nn
                 · exact mul_le_mul_of_nonneg_left hy_ineq hb_nn

  -- Step 4: Apply Proposition 20.3 to get a Nash equilibrium in the mixed extension
  obtain ⟨a_eq, ha_eq⟩ := EuclideanStrategicGame.proposition_20_3 G_mixed hcont hquasi

  -- Step 5: Convert back to a mixed strategy Nash equilibrium
  use fun i => euclideanToSimplex G i (a_eq i)
  constructor
  · -- Show each strategy is a probability distribution
    intro i
    -- a_eq i ∈ G_mixed.A i = mixedStrategySpace G i = simplexToEuclidean G i '' ProbSimplex (G.A i)
    -- So a_eq i = simplexToEuclidean G i p for some p ∈ ProbSimplex (G.A i)
    have h_in_image : a_eq i ∈ mixedStrategySpace G i := ha_eq.1 i
    unfold mixedStrategySpace at h_in_image
    obtain ⟨p, hp, heq⟩ := h_in_image
    -- euclideanToSimplex G i (a_eq i) = euclideanToSimplex G i (simplexToEuclidean G i p) = p
    simp only []
    rw [← heq, euclidean_simplex_inverse]
    exact hp
  · -- Show the Nash equilibrium condition
    intro i α'ᵢ hα'ᵢ
    -- Nash condition in Euclidean game: ∀x ∈ A i, payoff i a_eq ≥ payoff i (update a_eq i x)
    -- Encode the alternative strategy
    let x := simplexToEuclidean G i α'ᵢ
    -- Show x is in the action set
    have hx : x ∈ mixedStrategySpace G i := by
      unfold mixedStrategySpace
      exact Set.mem_image_of_mem (simplexToEuclidean G i) hα'ᵢ
    -- Apply Euclidean Nash condition
    have h_nash := ha_eq.2 i x hx
    -- Unfold the payoff definition: G_mixed.payoff i α = expectedPayoff G i (fun j => euclideanToSimplex G j (α j))
    unfold mixedExtension at h_nash
    -- The equilibrium conditions correspond under encoding/decoding
    -- Show that the payoff functions match up after encoding/decoding
    have h_eq : (fun j => euclideanToSimplex G j (Function.update a_eq i x j)) =
                Function.update (fun j => euclideanToSimplex G j (a_eq j)) i α'ᵢ := by
      funext j a
      by_cases h : j = i
      · -- Case: j = i, use the round-trip identity x = simplexToEuclidean G i α'ᵢ
        cases h
        unfold Function.update
        simp only [dif_pos]
        -- Show: euclideanToSimplex G i x a = α'ᵢ a
        -- Since x = simplexToEuclidean G i α'ᵢ, we have:
        -- euclideanToSimplex G i x = euclideanToSimplex G i (simplexToEuclidean G i α'ᵢ) = α'ᵢ
        have := euclidean_simplex_inverse G i α'ᵢ
        rw [this]
      · -- Case: j ≠ i, update doesn't affect j
        unfold Function.update
        simp only [dif_neg h]
    -- Rewrite the RHS using h_eq
    calc expectedPayoff G i (fun j => euclideanToSimplex G j (a_eq j))
        ≥ expectedPayoff G i (fun j => euclideanToSimplex G j (Function.update a_eq i x j)) := h_nash
      _ = expectedPayoff G i (Function.update (fun j => euclideanToSimplex G j (a_eq j)) i α'ᵢ) := by rw [h_eq]

end StrategicGamePayoff

