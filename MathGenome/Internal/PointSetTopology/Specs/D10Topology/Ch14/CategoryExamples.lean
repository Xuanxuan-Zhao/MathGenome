import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch14.CategoryInterface
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Irrational

/-! Independent statements for `d10:14:category-boundaries` and
`d10:14:countable-dense`. `ℚ`, all real subsets, and singletons have their
usual induced topologies. The binary sum has the disjoint-sum topology,
whose open-set characterization is also an explicit target. -/

open Set
namespace Specs.D10Topology.Ch14.CategoryExamples
open CategoryInterface

def rationals_dense_meager : Prop :=
  Dense (range (Rat.cast : ℚ → ℝ)) ∧
    meagerValue (range (Rat.cast : ℚ → ℝ)) ∧
    ¬ residualValue (range (Rat.cast : ℚ → ℝ))

def irrationals_residual : Prop := residualValue {x : ℝ | Irrational x}

def irrationals_baire : Prop := baireValue {x : ℝ // Irrational x}

def rational_singletons : Prop :=
  ∀ q : ℚ, IsClosed ({q} : Set ℚ) ∧ interior ({q} : Set ℚ) = ∅

def rationals_meager_self : Prop := meagerValue (univ : Set ℚ)

def rationals_empty_residual_not_dense : Prop :=
  residualValue (∅ : Set ℚ) ∧ ¬ Dense (∅ : Set ℚ)

def singleton_ambient_intrinsic : Prop :=
  ∀ x : ℝ, nowhereDenseValue ({x} : Set ℝ) ∧
    secondCategoryValue (univ : Set ({x} : Set ℝ))

def real_rat_sum_opens : Prop :=
  ∀ U : Set (ℝ ⊕ ℚ), IsOpen U ↔
    IsOpen (Sum.inl ⁻¹' U) ∧ IsOpen (Sum.inr ⁻¹' U)

def real_rat_sum_second_category_not_baire : Prop :=
  Nonempty (ℝ ⊕ ℚ) ∧ secondCategoryValue (univ : Set (ℝ ⊕ ℚ)) ∧
    ¬ baireValue (ℝ ⊕ ℚ)

def no_countable_dense_gdelta : Prop :=
  ∀ D : Set ℝ, D.Countable → Dense D → ¬ IsGδ D

end Specs.D10Topology.Ch14.CategoryExamples
