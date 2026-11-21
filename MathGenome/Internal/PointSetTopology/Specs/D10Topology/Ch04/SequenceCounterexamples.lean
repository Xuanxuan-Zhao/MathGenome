import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.ElementaryTopologies
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.NetTests

/-! Independent statements for paper.tex, d10:04:sequence-failure.
Sequences have index ℕ, with its usual nonempty directed order. Convergence
and clustering are exactly the upstream neighborhood definitions. The
cocountable topology is the shared canonical topology, and ℝ × ℝ has the
usual product topology. No countability assumption is needed for the first
sequence equivalence; the discontinuity assertion assumes uncountability. -/
open Set
open scoped Topology
universe u v
namespace Specs.D10Topology.Ch04.SequenceCounterexamples
open Specs.D10Topology.Ch04.NetsAndSubnets
open Specs.D10Topology.Ch01.ElementaryTopologies

/-- Even stages are (0,1); odd stages are (1,0). -/
def alternatingPair (n : ℕ) : ℝ × ℝ :=
  if n % 2 = 0 then (0, 1) else (1, 0)

def alternatingPairType := ℕ → ℝ × ℝ
def alternatingPairValue : alternatingPairType :=
  fun n => if n % 2 = 0 then (0, 1) else (1, 0)

def cocountable_sequence_converges_iff : Prop :=
  ∀ (X : Type u) (a : ℕ → X) (x : X),
    Converges (cocountableTopology X) a x ↔ ∃ N, ∀ n, N ≤ n → a n = x

def cocountable_id_preserves_sequences : Prop :=
  ∀ (X : Type u) (a : ℕ → X) (x : X),
    Converges (cocountableTopology X) a x →
      Converges (⊥ : TopologicalSpace X) (id ∘ a) (id x)

def cocountable_singleton_not_open : Prop :=
  ∀ (X : Type u) [Uncountable X] (x : X),
    ¬ IsOpen[cocountableTopology X] ({x} : Set X)

def cocountable_id_not_continuous : Prop :=
  ∀ (X : Type u) [Uncountable X],
    ¬ @Continuous X X (cocountableTopology X) ⊥ id

/-- Density and the contrast between sequences and genuine directed nets,
including every point outside A and the existence of such a point. -/
def cocountable_dense_not_sequential : Prop :=
  ∀ (X : Type u) (A : Set X), ¬ A.Countable → A ≠ univ →
    @Dense X (cocountableTopology X) A ∧
    (∃ x : X, x ∉ A) ∧
    ∀ x : X, x ∉ A →
      (∀ a : ℕ → X, (∀ n, a n ∈ A) → ¬ Converges (cocountableTopology X) a x) ∧
      (∃ (D : Type (max u v)) (p : Preorder D),
        Nonempty D ∧ @IsDirectedOrder D p.toLE ∧
        ∃ a : Net D X, (∀ d, a d ∈ A) ∧
          @Converges D X p (cocountableTopology X) a x)

def alternating_coordinate_clusters : Prop :=
  Clusters (inferInstance : TopologicalSpace ℝ) (fun n => (alternatingPair n).1) 0 ∧
  Clusters (inferInstance : TopologicalSpace ℝ) (fun n => (alternatingPair n).2) 0

/-- The explicit open square is a neighborhood of (0,0) missing every term. -/
def alternating_square_witness : Prop :=
  let U : Set (ℝ × ℝ) := (Ioo (-(1/2 : ℝ)) (1/2)) ×ˢ (Ioo (-(1/2 : ℝ)) (1/2))
  IsOpen U ∧ (0, 0) ∈ U ∧ ∀ n, alternatingPair n ∉ U

def alternating_not_cluster : Prop :=
  ¬ Clusters (inferInstance : TopologicalSpace (ℝ × ℝ)) alternatingPair (0, 0)

end Specs.D10Topology.Ch04.SequenceCounterexamples
