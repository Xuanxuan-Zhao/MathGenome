import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Affine.CartanRealization
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.CartanQuotient
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.LoopAlgebra

namespace Specs.LieNotes.Affine.ContragredientComparison

open _root_.RepTheorySurvey.Affine
open _root_.Specs.RepTheorySurvey.Affine.LoopAlgebra (K_value d_value homogeneous_value)
open _root_.Specs.RepTheorySurvey.Affine.TriangularRootSpaces (affineCartan_value)
open _root_.Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open _root_.LieAlgebrasAndRepresentations.HighestRoot (simpleRoots)
open _root_.Specs.LieNotes.Contragredient.CartanData
open _root_.Specs.LieNotes.Contragredient
open scoped Classical

universe u

/-- The contragredient quotient for the affine simple roots is the full normalized
untwisted affine algebra, with its specified Cartan, triples, center and derivation. -/
def AffineContragredientComparison : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H), B.IsNormalized H → Regular H φ →
    (∃ θ : Module.Dual ℂ H, IsHighestFiniteRoot H φ θ ∧
      Nonempty (FiniteRootTriple H θ × (∀ i : simpleRoots H φ, FiniteRootTriple H i.val))) ∧
    (∀ (θ : Module.Dual ℂ H), IsHighestFiniteRoot H φ θ →
      ∀ (T : FiniteRootTriple H θ) (S : ∀ i : simpleRoots H φ, FiniteRootTriple H i.val),
      ∃ indexFintype : Fintype (simpleRoots H φ),
        letI := indexFintype
        ∃ (A : Matrix (AffineSimpleIndex H φ) (AffineSimpleIndex H φ) ℤ)
          (R : Realization A (affineCartan_value B H)),
          (∀ i, (R.h i : AffineAlgebra B) = affineSimpleH B H θ i) ∧
          (∀ i, R.α i = affineSimpleRoot B H θ i) ∧
          IsGeneralizedCartanMatrix A ∧ IsSymmetrizable A ∧ R.IsMinimal ∧
          (A.map fun z : ℤ => (z : ℂ)).rank = Fintype.card (simpleRoots H φ) ∧
          ∃ E : CartanQuotient.Algebra R ≃ₗ⁅ℂ⁆ AffineAlgebra B,
            (∀ h, E (CartanQuotient.cartan R h) = (h : AffineAlgebra B)) ∧
            (∀ i, E (CartanQuotient.e R i) = affineSimpleE B T S i) ∧
            (∀ i, E (CartanQuotient.f R i) = affineSimpleF B T S i) ∧
            (LieAlgebra.center ℂ (AffineAlgebra B)).toSubmodule = ℂ ∙ K_value B ∧
            (LieAlgebra.center ℂ (CartanQuotient.Algebra R)).toSubmodule =
              ℂ ∙ E.symm (K_value B) ∧
            (∀ c k : ℂ, c • E.symm (K_value B) + k • E.symm (d_value B) = 0 →
              c = 0 ∧ k = 0) ∧
            E.symm (d_value B) ∉ LieAlgebra.center ℂ (CartanQuotient.Algebra R) ∧
            ∀ (m : ℤ) (x : G),
              ⁅E.symm (d_value B), E.symm (homogeneous_value B m x)⁆ =
                (m : ℂ) • E.symm (homogeneous_value B m x))

end Specs.LieNotes.Affine.ContragredientComparison
