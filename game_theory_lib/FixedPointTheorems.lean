import FixedPointTheorems.CubicalSpernerPrep
import FixedPointTheorems.CubicalSperner
import FixedPointTheorems.ApplyCubicalSperner
import FixedPointTheorems.ConvexHomeos
import FixedPointTheorems.Brouwer
import FixedPointTheorems.Kakutani

/-!
# Fixed Point Theorems

This module provides formalizations of classical fixed point theorems:
- Brouwer's fixed point theorem
- Kakutani's fixed point theorem

Ported from: https://github.com/harfe/fixed-point-theorems-lean4
Original proofs based on: Kuhn, H. W. (1960). "Some Combinatorial Lemmas in Topology."

## Main Results

* `brouwer_fixed_point` - Every continuous function from a convex compact subset to itself has a fixed point
* `kakutani_fixed_point` - Every set-valued correspondence with closed graph and convex compact values has a fixed point

-/
