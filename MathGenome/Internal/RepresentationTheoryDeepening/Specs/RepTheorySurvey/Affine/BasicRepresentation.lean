import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.Integrability

/-! The level-one basic highest weight and its degree eigenvectors. -/

noncomputable section

open UniversalEnvelopingAlgebra (ι)

universe u

namespace Specs.RepTheorySurvey.Affine.BasicRepresentation

open _root_.RepTheorySurvey.Affine
open _root_.RepTheorySurvey.CategoryO.BorelInduction (U)
open _root_.LieAlgebrasAndRepresentations.HighestRoot (simpleRoots)
open _root_.Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open LoopAlgebra (d_value homogeneous_value)
open TriangularRootSpaces (affineCartan_value coordinates)
open VermaWeightSpaces (Model Carrier Weight affineBorel_value IsWeightCharacter IsHighestVector)
open VermaModules (centralCartanElement affineSimple_value)
open Integrability (affineSimpleCoroot_value IsIntegrable_value)

/-- The functional extracting the central coordinate of the affine Cartan. -/
def basicWeight_value {G : Type u} [LieRing G] [LieAlgebra ℂ G]
    (B : InvariantForm G) (H : LieSubalgebra ℂ G) : Weight B H :=
  (LinearMap.snd ℂ (ℤ →₀ G) ℂ).comp
    ((LinearMap.fst ℂ ((ℤ →₀ G) × ℂ) ℂ).comp
      ((coordinates B).toLinearMap.comp (affineCartan_value B H).subtype))

def basicWeight_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G]
    (B : InvariantForm G) (H : LieSubalgebra ℂ G), Weight B H

/-- The values of the basic weight on the three summands of the affine Cartan. -/
def basicWeightCoordinates_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G]
    (B : InvariantForm G) (H : LieSubalgebra ℂ G),
    basicWeight_value B H (centralCartanElement B H) = 1 ∧
      (∀ x : affineCartan_value B H, (x : AffineAlgebra B) = d_value B →
        basicWeight_value B H x = 0) ∧
      (∀ h : H, ∀ x : affineCartan_value B H,
        (x : AffineAlgebra B) = homogeneous_value B 0 h → basicWeight_value B H x = 0)

/-- The extra coroot has value one and all finite simple coroots have value zero. -/
def basicWeightCoroots_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    (B : InvariantForm G) (H : LieSubalgebra ℂ G) (φ : Direction H)
    (θ : Module.Dual ℂ H) (i : AffineSimpleIndex H φ),
    basicWeight_value B H (affineSimpleCoroot_value B H θ i) =
      match i with
      | none => 1
      | some _ => 0

/-- The character at the basic weight exists, and its simple quotient is
integrable and infinite-dimensional. -/
def basicRepresentation_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H) (D : Model B H φ),
    B.IsNormalized H → Regular H φ →
    (∃! χ, IsWeightCharacter D (basicWeight_value B H) χ) ∧
      ∀ (χ : U (affineBorel_value D) →ₐ[ℂ] ℂ),
        IsWeightCharacter D (basicWeight_value B H) χ →
        (∀ (θ : Module.Dual ℂ H), IsHighestFiniteRoot H φ θ →
          ∀ (T : FiniteRootTriple H θ) (S : ∀ i : simpleRoots H φ, FiniteRootTriple H i.val),
            IsIntegrable_value D T S (affineSimple_value D χ)) ∧
        ¬ FiniteDimensional ℂ (affineSimple_value D χ)

/-- Every nonzero highest vector gives a linearly independent family of powers
of a degree-minus-one Cartan loop with nonzero square under the invariant form. -/
def basicRepresentationStrings_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H) (D : Model B H φ),
    B.IsNormalized H → Regular H φ →
    ∀ (χ : U (affineBorel_value D) →ₐ[ℂ] ℂ),
      IsWeightCharacter D (basicWeight_value B H) χ →
      ∀ v : affineSimple_value D χ, IsHighestVector D (basicWeight_value B H) v → v ≠ 0 →
        ∀ h : H, B.form (h : G) (h : G) ≠ 0 →
          let w := fun j : ℕ =>
            (ι ℂ (show Carrier D from homogeneous_value B (-1) h)) ^ j • v
          (∀ j, w j ≠ 0 ∧
            ι ℂ (show Carrier D from d_value B) • w j = (-(j : ℂ)) • w j) ∧
          Function.Injective (fun j : ℕ => -(j : ℂ)) ∧ LinearIndependent ℂ w

end Specs.RepTheorySurvey.Affine.BasicRepresentation
