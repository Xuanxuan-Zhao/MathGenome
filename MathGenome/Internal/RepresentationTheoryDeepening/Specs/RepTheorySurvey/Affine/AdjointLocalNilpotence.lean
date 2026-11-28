import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.AffineSimpleTriples
import Mathlib.Algebra.Lie.UniversalEnveloping

/-! The adjoint and cyclic-module local nilpotence used in LO12. -/

universe u v

namespace Specs.RepTheorySurvey.Affine.AdjointLocalNilpotence

open _root_.RepTheorySurvey.Affine
open _root_.LieAlgebrasAndRepresentations.HighestRoot (simpleRoots)
open _root_.Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open LoopAlgebra
open UniversalEnvelopingAlgebra (ι)

/-- Compatibility with the additive group, scalar action, and bracket of LO09. -/
def CompatibleLieStructure {G : Type u} [LieRing G] [LieAlgebra ℂ G]
    (B : InvariantForm G) (ring : LieRing (AffineAlgebra B))
    (algebra : @LieAlgebra ℂ (AffineAlgebra B) _ ring) : Prop :=
  ring.toAddCommGroup = (inferInstance : AddCommGroup (AffineAlgebra B)) ∧
    HEq algebra.toModule (inferInstance : Module ℂ (AffineAlgebra B)) ∧
    ∀ x y, ring.toBracket.bracket x y = affineBracket_value B x y

/-- Each affine simple generator acts locally nilpotently by the affine Lie bracket. -/
def affineSimpleAdjointLocallyNilpotent_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H), B.IsNormalized H → Regular H φ →
    ∀ (θ : Module.Dual ℂ H), IsHighestFiniteRoot H φ θ → ∀ (T : FiniteRootTriple H θ)
    (S : ∀ i : simpleRoots H φ, FiniteRootTriple H i.val) (i : AffineSimpleIndex H φ)
    (a : AffineAlgebra B), (a = affineSimpleE B T S i ∨ a = affineSimpleF B T S i) →
    ∀ x : AffineAlgebra B, ∃ n : ℕ, (affineBracket_value B a)^[n] x = 0

/-- The commutator with the image of each affine simple generator is a locally
nilpotent derivation on the enveloping algebra. -/
def affineSimpleEnvelopingAdjointLocallyNilpotent_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H), B.IsNormalized H → Regular H φ →
    ∀ (θ : Module.Dual ℂ H), IsHighestFiniteRoot H φ θ → ∀ (T : FiniteRootTriple H θ)
    (S : ∀ i : simpleRoots H φ, FiniteRootTriple H i.val) (i : AffineSimpleIndex H φ)
    (a : AffineAlgebra B), (a = affineSimpleE B T S i ∨ a = affineSimpleF B T S i) →
    ∀ [ring : LieRing (AffineAlgebra B)] [algebra : LieAlgebra ℂ (AffineAlgebra B)],
      CompatibleLieStructure B ring algebra →
      let A := UniversalEnvelopingAlgebra ℂ (AffineAlgebra B)
      let z : A := ι ℂ a
      let D : A →ₗ[ℂ] A := LinearMap.mulLeft ℂ z - LinearMap.mulRight ℂ z
      (∀ p q : A, D (p * q) = D p * q + p * D q) ∧
        ∀ p : A, ∃ n : ℕ, (D : A → A)^[n] p = 0

/-- A power killing the cyclic generator suffices for local nilpotence on
the cyclic submodule of any left module for the enveloping algebra. -/
def affineSimpleLocallyNilpotentOnCyclic_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H), B.IsNormalized H → Regular H φ →
    ∀ (θ : Module.Dual ℂ H), IsHighestFiniteRoot H φ θ → ∀ (T : FiniteRootTriple H θ)
    (S : ∀ i : simpleRoots H φ, FiniteRootTriple H i.val) (i : AffineSimpleIndex H φ)
    (a : AffineAlgebra B), (a = affineSimpleE B T S i ∨ a = affineSimpleF B T S i) →
    ∀ [ring : LieRing (AffineAlgebra B)] [algebra : LieAlgebra ℂ (AffineAlgebra B)],
      CompatibleLieStructure B ring algebra →
      let A := UniversalEnvelopingAlgebra ℂ (AffineAlgebra B)
      let z : A := ι ℂ a
      ∀ (M : Type v) [AddCommGroup M] [Module A M] (m : M),
        (∃ n : ℕ, z ^ n • m = 0) →
        ∀ w ∈ Submodule.span A ({m} : Set M), ∃ n : ℕ, z ^ n • w = 0

end Specs.RepTheorySurvey.Affine.AdjointLocalNilpotence
