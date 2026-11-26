import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.TorusCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import Mathlib.LinearAlgebra.PerfectPairing.Basic

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.CharacterPairing

open CharacterDescent (Character Cocharacter compositionPairing)
open DiagonalizableGroups (groupAlgebra groupAlgebraMap IntegerCharacters integerGenerator)
open AdjointRepresentation (GroupPoints dualMap constants scale)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open GeometricRadicals (IsReductive IsMaximalTorus IsSplitTorus baseChangedSubgroup)

noncomputable section

variable {k : Type u} [Field k]
local notation "Gm" => specGroup (groupAlgebra k IntegerCharacters)

/-- The power map on the multiplicative group, with its integer exponent. -/
def powerMorphism (n : ℤ) : Character Gm :=
  specGroupMap (groupAlgebraMap k
    ((zpowersHom IntegerCharacters (integerGenerator ^ n)).comp MulEquiv.ulift.toMonoidHom))

/-- The exponent of the composite of a character and a cocharacter. -/
def pairing (T : GroupScheme k) (χ : Character T) (cochar : Cocharacter T) : ℤ :=
  Function.invFun (powerMorphism (k := k)) (compositionPairing T χ cochar)

/-- Pull back the Laurent coordinate of the multiplicative group along a character
evaluated at a test point. -/
def characterValue {T : GroupScheme k} (χ : Character T)
    (R : TestAlgebra k) (t : GroupPoints T R) : R :=
  let x : Points (Gm).X R := t ≫ χ.hom.hom
  let f := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage x).unop
  f.hom (MonoidAlgebra.single integerGenerator 1 : MonoidAlgebra k IntegerCharacters)

/-- A tangent vector with weight χ. The test point may have coefficients
in any commutative k-algebra. -/
def adjointWeightVectors {G : GroupScheme k} (T : ClosedSubgroup G) (χ : Character T.group) :
    Set (Lie k G) :=
  {v | ∀ (R : TestAlgebra k) (t : GroupPoints T.group R),
    let p := mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) v.toMul.val
    let g := mapPoints (constants R) (t ≫ T.inclusion.hom.hom)
    g * p * g⁻¹ = mapPoints (scale R (characterValue χ R t)) p}

/-- The adjoint weight space, expressed inside the identity Lie algebra. -/
def adjointWeightSpace {G : GroupScheme k} (T : ClosedSubgroup G) (χ : Character T.group)
    (s : IdentityLieStructure G) :
    letI := s.lieRing
    letI := s.lieAlgebra
    Submodule k (Lie k G) :=
  letI := s.lieRing
  letI := s.lieAlgebra
  Submodule.span k (adjointWeightVectors T χ)

/-- The absolute roots are the nontrivial characters with a nonzero
adjoint weight vector. -/
def absoluteRoots {G : GroupScheme k} (T : ClosedSubgroup G) : Set (Character T.group) :=
  {χ | χ ≠ 1 ∧ ∃ v ∈ adjointWeightVectors T χ, v ≠ 0}

abbrev PairingType := ∀ {k : Type u} [Field k] (T : GroupScheme k),
  Character T → Cocharacter T → ℤ

abbrev AdjointWeightSpaceType := ∀ {k : Type u} [Field k] {G : GroupScheme k}
  (T : ClosedSubgroup G) (_χ : Character T.group) (s : IdentityLieStructure G),
  letI := s.lieRing
  letI := s.lieAlgebra
  Submodule k (Lie k G)

abbrev AbsoluteRootsType := ∀ {k : Type u} [Field k] {G : GroupScheme k}
  (T : ClosedSubgroup G), Set (Character T.group)

/-- Both lattices are finite free, and composition induces a perfect pairing. -/
def PerfectCharacterPairing : Prop :=
  ∀ {k : Type u} [Field k] (T : GroupScheme k), IsSplitTorus T →
    ∃ h : IsCommMonObj T.X,
    letI := h
    Module.Free ℤ (Additive (Character T)) ∧ Module.Finite ℤ (Additive (Character T)) ∧
    Module.Free ℤ (Additive (Cocharacter T)) ∧ Module.Finite ℤ (Additive (Cocharacter T)) ∧
    ∃ P : Additive (Character T) →ₗ[ℤ] Additive (Cocharacter T) →ₗ[ℤ] ℤ,
      P.IsPerfPair ∧ ∀ χ cochar, P (Additive.ofMul χ) (Additive.ofMul cochar) = pairing T χ cochar

/-- Composition has a unique exponent and evaluates to the corresponding power. -/
def CharacterPairingComposition : Prop :=
  ∀ {k : Type u} [Field k] (T : GroupScheme k) (χ : Character T) (cochar : Cocharacter T),
    (∀ n : ℤ, compositionPairing T χ cochar = powerMorphism n ↔ pairing T χ cochar = n) ∧
    ∀ (R : TestAlgebra k) (t : Rˣ),
      characterValue χ R (cocharacterPoint cochar R t) = (↑(t ^ pairing T χ cochar) : R)

/-- Scheme-valued evaluation distinguishes characters in every characteristic. -/
def CharacterValuesDetectCharacters : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k}, IsSplitTorus T →
    ∀ {χ ψ : Character T},
      (∀ (R : TestAlgebra k) (t : GroupPoints T R), characterValue χ R t = characterValue ψ R t) →
      χ = ψ

def AdjointWeightSpaceVectors : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val)
    (s : IdentityLieStructure G.val) (χ : Character T.group),
    letI := s.lieRing
    letI := s.lieAlgebra
    (adjointWeightSpace T χ s : Set (Lie k G.val)) = adjointWeightVectors T χ

def AbsoluteRootWeights : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} (T : ClosedSubgroup G.val)
    (s : IdentityLieStructure G.val) (χ : Character T.group),
    letI := s.lieRing
    letI := s.lieAlgebra
    χ ∈ absoluteRoots T ↔ χ ≠ 1 ∧ adjointWeightSpace T χ s ≠ ⊥

def FiniteAbsoluteRoots : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val),
    IsSplitTorus T.group → (absoluteRoots T).Finite

def ZeroWeightSpace : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group →
      (∃ h : IsClosedImmersion
          ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion).hom.hom.left,
        IsMaximalTorus (baseChangedSubgroup (AlgebraicClosure k) T h)) →
      ∀ s : IdentityLieStructure G.val,
        letI := s.lieRing
        letI := s.lieAlgebra
        Function.Injective (mapPointKernel T.inclusion) ∧
        (adjointWeightSpace T 1 s : Set (Lie k G.val)) = Set.range (mapPointKernel T.inclusion)

end

end LinearAlgebraicGroups.Specs.CharacterPairing
