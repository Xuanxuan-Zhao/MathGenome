import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.Projective
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainTensorTransport
import Mathlib.CategoryTheory.Monoidal.PushoutProduct

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomotopicalAlgebra MonoidalCategory
open scoped TensorProduct
open CochainComplex.HomComplex

universe u a

namespace DerivedFormalization.Specs.ComplexMonoidal

open Model.Complexes
open _root_.Specs.DerivedFormalization
open CochainTensorMonoidal (cochainMonoidalValue HasKoszulBraiding pureTensorValue)
open CochainTensorHomAdjunction (homFromValue)
open CochainRingTransport (complexFunctorValue)
open CochainTensorTransport (AdequateModel)
open Cochains (compValue)

/-- The pushout-product and unit axioms on the specified model and monoidal
structures. The two unit comparisons are required for every weak equivalence
from a cofibrant object to the unit. -/
structure TensorModelAxioms (C : Type*) [Category* C]
    [ModelCategory C] [MonoidalCategory C] : Prop where
  pushoutProduct_cofibration :
    ∀ {X Y U V : C} (f : X ⟶ Y) (g : U ⟶ V),
      cofibrations C f → cofibrations C g → cofibrations C (Arrow.mk f □ Arrow.mk g).hom
  pushoutProduct_trivial :
    ∀ {X Y U V : C} (f : X ⟶ Y) (g : U ⟶ V),
      cofibrations C f → cofibrations C g →
      (weakEquivalences C f ∨ weakEquivalences C g) →
      weakEquivalences C (Arrow.mk f □ Arrow.mk g).hom
  unit_cofibrant : IsCofibrant (𝟙_ C)
  unit_comparison :
    ∀ {Q : C} (q : Q ⟶ 𝟙_ C), IsCofibrant Q → weakEquivalences C q →
      ∀ (X : C), IsCofibrant X →
        weakEquivalences C ((q ▷ X) ≫ (λ_ X).hom) ∧
        weakEquivalences C ((X ◁ q) ≫ (ρ_ X).hom)

attribute [local instance] cochainMonoidalValue

/-- View the right-tensor adjunction as a closed structure via the symmetry. -/
@[instance_reducible]
noncomputable def nativeClosedValue {A : Type u} [CommRing A] [BraidedCategory (Cochains A)]
    (adj : ∀ Y : Cochains A, tensorRight Y ⊣ homFromValue Y) :
    MonoidalClosed (Cochains A) where
  closed Y :=
    { rightAdj := homFromValue Y
      adj := (adj Y).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight Y).symm }

/-- The projective model on the native diagonal category uses the direct-sum total
tensor, Koszul symmetry, and signed product internal Hom. -/
def nativeTensorModelType : Prop :=
  ∀ (A : Type u) [CommRing A] (M : ProjectiveModel A),
    letI := M.model
    ∃ s : SymmetricCategory (Cochains A),
      HasKoszulBraiding s ∧
      letI := s
      ∃ (adj : ∀ Y : Cochains A, tensorRight Y ⊣ homFromValue Y)
        (c : MonoidalClosed (Cochains A)),
        c = nativeClosedValue adj ∧
        (∀ (X Y Z : Cochains A) (f : X ⊗ Y ⟶ Z) (i j : ℤ) (x : X.X i) (y : Y.X j),
          (((adj Y).homEquiv X Z f).f i x).v j (i + j) (add_comm j i) y =
            f.f (i + j) (pureTensorValue X Y i j rfl x y)) ∧
        TensorModelAxioms (Cochains A)

/-- At an adequate bound the model structure has the original degreewise
surjections, quasi-isomorphisms, and their lifting-defined cofibrations. Its tensor,
unit and internal Hom are the ones identified by the signed adequate model. -/
def representedTensorModelType : Prop :=
  ∀ {R : Type u} {A : Type a} [CommRing R] [CommRing A]
    (e : R ≃+* A) (M : ProjectiveModel A),
    letI := M.model
    ∃ (S : AdequateModel e) (N : FunctorialModelCategory (compValue.{a} R)),
      letI := N
      letI := S.chainMonoidal
      let F := complexFunctorValue e
      let C := compValue.{a} R
      fibrations C =
        (fun _ _ f ↦ ∀ i : ℤ, Function.Surjective (f.f i)) ∧
      weakEquivalences C = quasiIso (ModuleCat.{a} R) (.up ℤ) ∧
      cofibrations C = (fibrations C ⊓ weakEquivalences C).llp ∧
      cofibrations C = (cofibrations (Cochains A)).inverseImage F ∧
      fibrations C = (fibrations (Cochains A)).inverseImage F ∧
      weakEquivalences C = (weakEquivalences (Cochains A)).inverseImage F ∧
      TensorModelAxioms C

end DerivedFormalization.Specs.ComplexMonoidal
