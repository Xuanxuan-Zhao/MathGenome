import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.JamesSpaceShrinking
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
The coefficient model and codimension assertion in `fa2:p1:james-space`,
paper.tex:4559–4578. The source specifies real scalars in this section.
Coordinates are zero based; `range N` means the first N coordinates.

The bidual below is the actual continuous real linear bidual, with its operator
norm. Its coefficient map is fixed by evaluation on the actual coordinate
functionals. Injectivity, exact image, and the norm identity give the asserted
isometric identification without choosing an auxiliary normed-space structure
on the set of bounded-coefficient sequences. The final linear equivalence fixes
the codimension of the canonical evaluation image, rather than an arbitrary copy
of J. All models of the prescribed cyclic norm are covered.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ExpandedFA.P1.JamesBidualSpec

/-- Type synonym that keeps the chosen normed model visible to instance inference. -/
def ModelSpace (m : JamesBanachBasisSpec.BanachBasisModel) : Type :=
  JamesBanachBasisSpec.Sequence

instance (m : JamesBanachBasisSpec.BanachBasisModel) : NormedAddCommGroup (ModelSpace m) := m.group
instance (m : JamesBanachBasisSpec.BanachBasisModel) : NormedSpace ℝ (ModelSpace m) := m.scalars

section Model
variable (m : JamesBanachBasisSpec.BanachBasisModel)

abbrev Dual := ModelSpace m →L[ℝ] ℝ
local instance : NormedAddCommGroup (Dual m) := inferInstance
local instance : NormedSpace ℝ (Dual m) := inferInstance
abbrev Bidual := Dual m →L[ℝ] ℝ
local instance : NormedAddCommGroup (Bidual m) := inferInstance
local instance : NormedSpace ℝ (Bidual m) := inferInstance

def initialSum (a : ℕ → ℝ) (N : ℕ) : ModelSpace m :=
  C15Basis.Spec.orderedPartialSum m.e a N

def Bounded (a : ℕ → ℝ) : Prop :=
  BddAbove (Set.range (fun N => ‖initialSum m a N‖))

def coefficientMap (b : SchauderBasis ℝ (ModelSpace m)) :
    Bidual m →ₗ[ℝ] (ℕ → ℝ) where
  toFun Φ i := Φ (b.coord i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def canonical : ModelSpace m →L[ℝ] Bidual m :=
  C04CanonicalMap.Spec.CanonicalEvaluationValue ℝ (ModelSpace m)


def CoefficientModel : Prop :=
  ∀ m : JamesBanachBasisSpec.BanachBasisModel,
    ∀ b : SchauderBasis ℝ (ModelSpace m),
      b.basis = m.e → (∀ i x, b.coord i x = x.val i) →
      Function.Injective (coefficientMap m b) ∧
      (∀ a : ℕ → ℝ, (∃ Φ : Bidual m, coefficientMap m b Φ = a) ↔ Bounded m a) ∧
      (∀ Φ : Bidual m,
        ‖Φ‖ = sSup (Set.range (fun N => ‖initialSum m (coefficientMap m b Φ) N‖)))

def BoundedDecomposition : Prop :=
  ∀ (m : JamesBanachBasisSpec.BanachBasisModel) (a : ℕ → ℝ),
    Bounded m a → ∃! L : ℝ,
      Tendsto a atTop (𝓝 L) ∧ JamesSpec.membershipValue (fun n => a n - L)

def ConstantSequence : Prop :=
  ∀ m : JamesBanachBasisSpec.BanachBasisModel,
    Bounded m (fun _ => 1) ∧
      (sSup (Set.range (fun N => ‖initialSum m (fun _ => 1) N‖))) = 1

def CanonicalImage : Prop :=
  ∀ m : JamesBanachBasisSpec.BanachBasisModel,
    ∀ b : SchauderBasis ℝ (ModelSpace m),
      b.basis = m.e → (∀ i x, b.coord i x = x.val i) →
      ∀ Φ : Bidual m,
        Φ ∈ (canonical m).range ↔
          Tendsto (coefficientMap m b Φ) atTop (𝓝 0)

def CodimensionOne : Prop :=
  ∀ m : JamesBanachBasisSpec.BanachBasisModel,
    Nonempty ((Bidual m ⧸ (canonical m).range) ≃ₗ[ℝ] ℝ)

end Model
end ExpandedFA.P1.JamesBidualSpec
