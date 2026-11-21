import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Products
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Independent statements for `paper.tex` d10:05:interval and d10:05:heine-borel.
The Euclidean representation is `EuclideanSpace ℝ (Fin n)`, equipped with
its L² norm. Its coordinate map is compared with the chapter 3 product
topology explicitly. Boundedness in the main statement means a uniform
bound on that Euclidean norm. All natural dimensions, arbitrary interval
endpoints, and empty subsets are allowed.
-/

open Set

namespace Specs.D10Topology.Ch05.RealAndEuclideanCompactness

open Specs.D10Topology.Ch05.Compactness

def real_interval_compact : Prop :=
  ∀ a b : ℝ, SubspaceCompact (Icc a b)

def euclidean_product_homeomorph : Prop :=
  ∀ n : ℕ,
    @IsHomeomorph (EuclideanSpace ℝ (Fin n)) (Fin n → ℝ)
      inferInstance (Ch03.Products.productTopologyValue (fun _ => inferInstance))
      (fun x i => x i)

def euclidean_norm_formula : Prop :=
  ∀ (n : ℕ) (x : EuclideanSpace ℝ (Fin n)),
    ‖x‖ = Real.sqrt (∑ i : Fin n, (x i) ^ 2)

def euclidean_bounded_iff_norm_bound : Prop :=
  ∀ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))),
    Bornology.IsBounded K ↔ ∃ R : ℝ, ∀ x ∈ K, ‖x‖ ≤ R

def heine_borel : Prop :=
  ∀ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))),
    SubspaceCompact K ↔ IsClosed K ∧ ∃ R : ℝ, ∀ x ∈ K, ‖x‖ ≤ R

end Specs.D10Topology.Ch05.RealAndEuclideanCompactness
