import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.ConicProgramModels
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! Independent scope for paper.tex, Proposition `prop:standard-self-dual-cones`,
orthant and Lorentz clauses (2474–2497). `WithLp 2` carries the product Euclidean
inner product, and the norm on U is its inner-product norm. No positive dimension
assumption is made. The Lorentz statements hold even without finite dimension. -/
noncomputable section
universe u
namespace VariationalNotes.Ch05.OrthantLorentzCones.Specs

def orthant {ι : Type u} [Fintype ι] : Set (EuclideanSpace ℝ ι) :=
  {x | ∀ i, 0 ≤ x i}

def orthantType : Type (u + 1) :=
  ∀ {ι : Type u} [Fintype ι], Set (EuclideanSpace ℝ ι)

def lorentzCone {U : Type u} [NormedAddCommGroup U] [InnerProductSpace ℝ U] :
    Set (WithLp 2 (ℝ × U)) := {z | ‖z.snd‖ ≤ z.fst}

def lorentzConeType : Type (u + 1) :=
  ∀ {U : Type u} [NormedAddCommGroup U] [InnerProductSpace ℝ U],
    Set (WithLp 2 (ℝ × U))

def orthant_properties : Prop :=
  ∀ {ι : Type u} [Fintype ι],
    IsClosed (orthant : Set (EuclideanSpace ℝ ι)) ∧
    Convex ℝ (orthant : Set (EuclideanSpace ℝ ι)) ∧
    VariationalNotes.ConvexGeometry.Specs.IsCone (orthant : Set (EuclideanSpace ℝ ι)) ∧
    ConicProgramModels.Specs.innerPositiveDual (orthant : Set (EuclideanSpace ℝ ι)) = orthant

def lorentz_properties : Prop :=
  ∀ {U : Type u} [NormedAddCommGroup U] [InnerProductSpace ℝ U],
    IsClosed (lorentzCone : Set (WithLp 2 (ℝ × U))) ∧
    Convex ℝ (lorentzCone : Set (WithLp 2 (ℝ × U))) ∧
    VariationalNotes.ConvexGeometry.Specs.IsCone (lorentzCone : Set (WithLp 2 (ℝ × U))) ∧
    ConicProgramModels.Specs.innerPositiveDual (lorentzCone : Set (WithLp 2 (ℝ × U))) =
      lorentzCone

def lorentz_axis : Prop :=
  ∀ {U : Type u} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (t : ℝ),
    WithLp.toLp 2 (t, (0 : U)) ∈ lorentzCone ↔ 0 ≤ t

def lorentz_zero_dimension : Prop :=
  ∀ {U : Type u} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [Subsingleton U]
    (z : WithLp 2 (ℝ × U)), z ∈ lorentzCone ↔ 0 ≤ z.fst

def product_pairing : Prop :=
  ∀ {U : Type u} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (z w : WithLp 2 (ℝ × U)),
    inner ℝ z w = z.fst * w.fst + inner ℝ z.snd w.snd

end VariationalNotes.Ch05.OrthantLorentzCones.Specs
