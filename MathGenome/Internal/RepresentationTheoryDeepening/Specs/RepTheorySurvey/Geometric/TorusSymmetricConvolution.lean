import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TorusFusion

noncomputable section

open CategoryTheory
open scoped MonoidalCategory BraidedCategory

namespace RepTheorySurvey.Geometric.TorusSymmetricConvolutionSpecs

open TorusPerverseSpecs TorusOrderedConvolutionSpecs TorusFusionSpecs

variable {r : ℕ} {D : OrderedGeometry r} {g : StageGeometry r} {c : ContinuousJets r}
variable {P : OrderedProduct D g c}

/-- The tensor functor and constraints from ordered geometric convolution. -/
@[instance_reducible]
def orderedMonoidalData (U : OrderedConstraints P) : MonoidalCategoryStruct (Heart r g c) where
  tensorObj V W := P.convolution.obj (V, W)
  whiskerLeft := fun V {_ _} f ↦ P.convolution.map (𝟙 V, f)
  whiskerRight := fun {_ _} f W ↦ P.convolution.map (f, 𝟙 W)
  tensorHom := fun {_ _ _ _} f h ↦ P.convolution.map (f, h)
  tensorUnit := U.unit
  associator V W X := U.associator.app (V, W, X)
  leftUnitor V := U.leftUnitor.app V
  rightUnitor V := U.rightUnitor.app V

/-- Coherence on the equivariant perverse heart with the ordered product and
the fusion commutor. The monoidal and symmetric classes impose the pentagon,
triangle, both hexagons and the involutivity of exchange. -/
structure SymmetricConvolution (U : OrderedConstraints P) (σ : SwapsConvolution P) where
  monoidal : MonoidalCategory (Heart r g c)
  ordered : monoidal.toMonoidalCategoryStruct = orderedMonoidalData U
  symmetric : @SymmetricCategory (Heart r g c) _ monoidal
  fusionBraiding :
    letI := monoidal
    letI := symmetric
    ∀ V W : Heart r g c,
      let e : ∀ X Y : Heart r g c, X ⊗ Y ≅ P.convolution.obj (X, Y) :=
        fun X Y ↦ eqToIso (congrArg (fun T : MonoidalCategoryStruct (Heart r g c) ↦
          @MonoidalCategoryStruct.tensorObj (Heart r g c) _ T X Y) ordered)
      β_ V W = e V W ≪≫ σ.app (V, W) ≪≫ (e W V).symm

/-- For every split torus, ordered convolution (with its natural direct-sum
stalk comparison, point unit and tensor rebracketing) is symmetric monoidal,
with braiding the specialization of the two-point exchange. -/
def TorusSymmetricConvolution : Prop :=
  ∀ r : ℕ, ∃ (D : OrderedGeometry r) (g : StageGeometry r) (c : ContinuousJets r)
    (P : OrderedProduct D g c) (U : OrderedConstraints P) (σ : SwapsConvolution P),
    Nonempty (SymmetricConvolution U σ) ∧
    FlipsConvolutionSummands P σ ∧ LocalGeometry D ∧
    ∀ (A B : Set (Labels r)), A.Finite → B.Finite →
      ∃ (N : ℕ) (G : SectionGeometry N A B) (H : SectionGeometry N B A)
        (S : SectionExchange G H) (E : CoefficientExchange D S),
        ClearsPoles N A B ∧ SpecializesToConvolution σ E

end RepTheorySurvey.Geometric.TorusSymmetricConvolutionSpecs
