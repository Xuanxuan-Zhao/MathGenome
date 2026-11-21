import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.EmbeddingsAndCharacteristicMaps
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.DenselyOrdered

/-!
Independent statements for paper.tex, d10:02:cautions (first paragraph)
and d10:02:open-closed-examples. Bool represents the same two-point set in
both topologies. In Mathlib's reverse order, ⊥ is discrete and ⊤ indiscrete.
Real products and the interval subtype have their usual product/subspace
topologies. Accumulation uses the canonical derivedSet, whose punctured
neighborhood meaning is proved in the upstream ClosureCalculus interface.
-/

open Set
universe u v

namespace Specs.D10Topology.Ch02.MapCounterexamples

def discrete_indiscrete_identity : Prop :=
  @Continuous Bool Bool ⊥ ⊤ id ∧ Function.Bijective (id : Bool → Bool) ∧
    ¬ @Continuous Bool Bool ⊤ ⊥ id

def indiscrete_discrete_identity : Prop :=
  @IsOpenMap Bool Bool ⊤ ⊥ id ∧ @IsClosedMap Bool Bool ⊤ ⊥ id ∧
    ¬ @Continuous Bool Bool ⊤ ⊥ id

/-- In particular, no separation assumptions are imposed on either space. -/
def constant_accumulation_failure : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (x : X) (c : Y), x ∈ derivedSet A →
      Continuous (fun _ : X => c) ∧ (fun _ : X => c) '' A = {c} ∧
      c ∉ derivedSet ((fun _ : X => c) '' A) ∧
      ¬ (fun _ : X => c) '' derivedSet A ⊆ derivedSet ((fun _ : X => c) '' A)

/-- A concrete witness ensures the general counterexample is nonvacuous. -/
def real_constant_counterexample : Prop :=
  (0 : ℝ) ∈ derivedSet (univ : Set ℝ) ∧
    Continuous (fun _ : ℝ => (0 : ℝ)) ∧
    (fun _ : ℝ => (0 : ℝ)) '' univ = {0} ∧
    (0 : ℝ) ∉ derivedSet ((fun _ : ℝ => (0 : ℝ)) '' univ) ∧
    ¬ (fun _ : ℝ => (0 : ℝ)) '' derivedSet univ ⊆
      derivedSet ((fun _ : ℝ => (0 : ℝ)) '' univ)

def hyperbola_closed : Prop :=
  IsClosed {z : ℝ × ℝ | z.1 * z.2 = 1}

def hyperbola_projection : Prop :=
  Prod.fst '' {z : ℝ × ℝ | z.1 * z.2 = 1} = (univ : Set ℝ) \ {0}

def hyperbola_projection_not_closed : Prop :=
  ¬ IsClosed (Prod.fst '' {z : ℝ × ℝ | z.1 * z.2 = 1})

def real_projection_open_not_closed : Prop :=
  IsOpenMap (Prod.fst : ℝ × ℝ → ℝ) ∧ ¬ IsClosedMap (Prod.fst : ℝ × ℝ → ℝ)

def unit_interval_inclusion_closed_not_open : Prop :=
  IsClosedMap (Subtype.val : Icc (0 : ℝ) 1 → ℝ) ∧
    ¬ IsOpenMap (Subtype.val : Icc (0 : ℝ) 1 → ℝ) ∧
    (Subtype.val : Icc (0 : ℝ) 1 → ℝ) '' univ = Icc (0 : ℝ) 1 ∧
    ¬ IsOpen (Icc (0 : ℝ) 1)

end Specs.D10Topology.Ch02.MapCounterexamples
