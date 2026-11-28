import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.TorusWeights
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.RationalActionComparison
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.ExactInvariants

open AlgebraicGeometry CategoryTheory LinearAlgebraicGroups
open LinearAlgebraicGroups.RationalRepresentations (invariants invariantsMap)
open RepTheorySurvey.Invariants.RationalActionComparison
  (KPoints HasRegularOrbits pointEvaluation contract)
open scoped TensorProduct

universe u

namespace RepTheorySurvey.Invariants.TorusProjection.Specs

noncomputable section

open RepTheorySurvey.Invariants.Specs.TorusWeights (coordinates)

variable {k M V W : Type u} [Field k] [CommGroup M]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Extract the coefficient of the trivial character in the right tensor factor.
The identity of the multiplicatively written character group represents weight zero. -/
def zeroComponent (ρ : RightComodule k (coordinates k M) V) : V →ₗ[k] V :=
  (contract ((Finsupp.lapply (R := k) (1 : M)).comp
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)).comp ρ.coaction

def ZeroComponentType :=
  ∀ {k M V : Type u} [Field k] [CommGroup M] [AddCommGroup V] [Module k V],
    RightComodule k (coordinates k M) V → (V →ₗ[k] V)

/-- The zero-weight component corestricts to an equivariant retraction onto invariants. -/
def Projection : Prop :=
  ∀ {k M V : Type u} [Field k] [CommGroup M] [AddCommGroup V] [Module k V]
    (ρ : RightComodule k (coordinates k M) V),
    ∃ R : V →ₗ[k] invariants (coordinates k M) ρ,
      ((invariants (coordinates k M) ρ).subtype).comp R = zeroComponent ρ ∧
      R.comp (invariants (coordinates k M) ρ).subtype = LinearMap.id ∧
      Invariants.Specs.isComoduleMap ρ (Invariants.Specs.rationalTrivial (coordinates k M)) R

/-- Equivariant linear maps commute with taking the zero-weight component. -/
def Naturality : Prop :=
  ∀ {k M V W : Type u} [Field k] [CommGroup M]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : RightComodule k (coordinates k M) V) (σ : RightComodule k (coordinates k M) W)
    (f : V →ₗ[k] W), Invariants.Specs.isComoduleMap ρ σ f →
    f.comp (zeroComponent ρ) = (zeroComponent σ).comp f

/-- The restricted maps of a short exact sequence of rational torus modules
form a short exact sequence, with arbitrary-dimensional modules over any field. -/
def ExactInvariants : Prop :=
  ∀ {k M U V W : Type u} [Field k] [CommGroup M]
    [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (ρ : RightComodule k (coordinates k M) U) (σ : RightComodule k (coordinates k M) V)
    (τ : RightComodule k (coordinates k M) W) (f : U →ₗ[k] V) (g : V →ₗ[k] W)
    (hf : Invariants.Specs.isComoduleMap ρ σ f) (hg : Invariants.Specs.isComoduleMap σ τ g),
    Function.Injective f → Function.Exact f g → Function.Surjective g →
      Function.Injective (invariantsMap f hf) ∧
      Function.Exact (invariantsMap f hf) (invariantsMap g hg) ∧
      Function.Surjective (invariantsMap g hg)

/-- Corestricting the zero-weight component of an algebra coaction gives a Reynolds operator. -/
def Reynolds : Prop :=
  ∀ {k M A : Type u} [Field k] [CommGroup M] [Ring A] [Algebra k A]
    (ρ : Invariants.Specs.RationalAlgebraAction (coordinates k M) A),
    ∃ R : A →ₗ[k] Invariants.Specs.rationalFixedSubalgebra ρ,
      (Invariants.Specs.rationalFixedSubalgebra ρ).val.toLinearMap.comp R =
        zeroComponent (Invariants.Specs.rationalToRightComodule ρ) ∧
      Invariants.Specs.rationalIsReynolds ρ R

/-- In particular each homogeneous degree stable under an algebra coaction
is preserved by the zero-weight component. -/
def StableSubspaces : Prop :=
  ∀ {k M V : Type u} [Field k] [CommGroup M] [AddCommGroup V] [Module k V]
    (ρ : RightComodule k (coordinates k M) V) (S : Submodule k V), ρ.IsSubcomodule S →
      S ≤ S.comap (zeroComponent ρ)

/-- Over an algebraically closed field the actual split torus has the Laurent
coordinate Hopf algebra. Evaluating its coaction on base-field points identifies
rational representations and identifies the invariant subspaces. -/
def PointInvariants : Prop :=
  ∀ (k ι : Type u) [Field k] [IsAlgClosed k] [Fintype ι],
    let T := (LinearAlgebraicGroups.Specs.StandardGroups.multiplicativePowerGroup k ι).val
    let B := coordinates k (Multiplicative (ι → ℤ))
    ∃ (H : GlobalFunctions.Specs.GlobalHopf T) (a : T ⟶ H.spectrum)
      (s : (hopfSpec (CommRingCat.of k)).obj (Opposite.op B) ≅ T)
      (e : B ≅ H.hopf),
      a.hom.hom = GlobalFunctions.unit T.X ∧
      a ≫ (hopfSpec (CommRingCat.of k)).map e.hom.op = s.inv ∧
      ∀ (V : Type u) [AddCommGroup V] [Module k V],
        ∃ E : RightComodule k B V ≃ {r : Representation k (KPoints T) V // HasRegularOrbits r},
          ∀ ρ : RightComodule k B V,
            (∀ (g : KPoints T) (v : V), (E ρ).1 g v =
              contract (((pointEvaluation H g).comp e.hom.hom.toAlgHom).toLinearMap)
                (ρ.coaction v)) ∧
            (E ρ).1.invariants = invariants B ρ

end

end RepTheorySurvey.Invariants.TorusProjection.Specs
