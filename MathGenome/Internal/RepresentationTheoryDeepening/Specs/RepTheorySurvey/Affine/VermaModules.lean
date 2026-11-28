import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.VermaWeightSpaces
import Mathlib.RingTheory.SimpleModule.Basic

/-! The canonical simple quotient of an untwisted affine Verma module and its level. -/

noncomputable section

open scoped DirectSum
open UniversalEnvelopingAlgebra (ι)

universe u v

namespace Specs.RepTheorySurvey.Affine.VermaModules

open _root_.RepTheorySurvey.Affine (InvariantForm)
open _root_.RepTheorySurvey.CategoryO.BorelInduction (U)
open _root_.Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open VermaWeightSpaces
open LoopAlgebra (K_value)
open TriangularRootSpaces (affineCartan_value cartanDegrees components coordinates)

section Construction

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G]
  {B : InvariantForm G} {H : LieSubalgebra ℂ G} {φ : Direction H}

/-- The sum of all proper left enveloping submodules of the actual induced module. -/
def affineVermaRadical_value (D : Model B H φ) (χ : U (affineBorel_value D) →ₐ[ℂ] ℂ) :
    Submodule (U (Carrier D)) (affineVerma_value D χ) :=
  sSup {S | S ≠ ⊤}

/-- The simple quotient, with the quotient action of the affine enveloping algebra. -/
abbrev affineSimple_value (D : Model B H φ) (χ : U (affineBorel_value D) →ₐ[ℂ] ℂ) :=
  affineVerma_value D χ ⧸ affineVermaRadical_value D χ

/-- The canonical map from the affine Verma module to its simple quotient. -/
def affineSimpleProjection_value (D : Model B H φ) (χ : U (affineBorel_value D) →ₐ[ℂ] ℂ) :
    affineVerma_value D χ →ₗ[U (Carrier D)] affineSimple_value D χ :=
  (affineVermaRadical_value D χ).mkQ

/-- The image of the class of the tensor of the two units. -/
def affineSimpleTop_value (D : Model B H φ) (χ : U (affineBorel_value D) →ₐ[ℂ] ℂ) :
    affineSimple_value D χ :=
  affineSimpleProjection_value D χ (affineVermaTop_value D χ)

/-- Ordinary simultaneous affine Cartan eigenspaces in the simple quotient. -/
def affineSimpleWeightSpace_value (D : Model B H φ) (χ : U (affineBorel_value D) →ₐ[ℂ] ℂ)
    (μ : Weight B H) : Submodule ℂ (affineSimple_value D χ) :=
  ⨅ h : affineCartan_value B H, LinearMap.ker
    (Algebra.lsmul ℂ ℂ (affineSimple_value D χ) (ι ℂ (show Carrier D from h.1)) -
      μ h • LinearMap.id)

/-- The central generator in the domain of the affine weights. -/
def centralCartanElement (B : InvariantForm G) (H : LieSubalgebra ℂ G) :
    affineCartan_value B H :=
  ⟨K_value B, by
    change (∀ m, (coordinates B (K_value B)).1.1 m ∈ cartanDegrees H m) ∧
      (coordinates B (K_value B)).1.2 ∈ (⊤ : Submodule ℂ ℂ) ∧
      (coordinates B (K_value B)).2 ∈ (⊤ : Submodule ℂ ℂ)
    exact ⟨fun m => by simp [coordinates, K_value], Submodule.mem_top, Submodule.mem_top⟩⟩

/-- The quotient at an affine weight, using the character furnished upstream. -/
abbrev affineSimpleAt_value (D : Model B H φ) (Λ : Weight B H)
    (hχ : ∃! χ, IsWeightCharacter D Λ χ) :=
  affineSimple_value D (affineWeightCharacter_value D Λ hχ)

/-- The distinguished highest vector of the quotient at Λ. -/
abbrev affineSimpleTopAt_value (D : Model B H φ) (Λ : Weight B H)
    (hχ : ∃! χ, IsWeightCharacter D Λ χ) : affineSimpleAt_value D Λ hχ :=
  affineSimpleTop_value D (affineWeightCharacter_value D Λ hχ)

/-- The level is the value of the affine highest weight on the central generator. -/
def affineLevel_value (B : InvariantForm G) (H : LieSubalgebra ℂ G) (Λ : Weight B H) : ℂ :=
  Λ (centralCartanElement B H)

end Construction

def affineVermaRadical_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] {B : InvariantForm G}
    {H : LieSubalgebra ℂ G} {φ : Direction H} (D : Model B H φ)
    (χ : U (affineBorel_value D) →ₐ[ℂ] ℂ), Submodule (U (Carrier D)) (affineVerma_value D χ)

def affineSimple_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] {B : InvariantForm G}
    {H : LieSubalgebra ℂ G} {φ : Direction H} (D : Model B H φ),
    (U (affineBorel_value D) →ₐ[ℂ] ℂ) → Type u

def affineSimpleProjection_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] {B : InvariantForm G}
    {H : LieSubalgebra ℂ G} {φ : Direction H} (D : Model B H φ)
    (χ : U (affineBorel_value D) →ₐ[ℂ] ℂ),
    affineVerma_value D χ →ₗ[U (Carrier D)] affineSimple_value D χ

def affineSimpleTop_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] {B : InvariantForm G}
    {H : LieSubalgebra ℂ G} {φ : Direction H} (D : Model B H φ)
    (χ : U (affineBorel_value D) →ₐ[ℂ] ℂ), affineSimple_value D χ

def affineSimpleWeightSpace_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] {B : InvariantForm G}
    {H : LieSubalgebra ℂ G} {φ : Direction H} (D : Model B H φ)
    (χ : U (affineBorel_value D) →ₐ[ℂ] ℂ), Weight B H → Submodule ℂ (affineSimple_value D χ)

def affineSimpleAt_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] {B : InvariantForm G}
    {H : LieSubalgebra ℂ G} {φ : Direction H} (D : Model B H φ) (Λ : Weight B H),
    (∃! χ, IsWeightCharacter D Λ χ) → Type u

def affineSimpleTopAt_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] {B : InvariantForm G}
    {H : LieSubalgebra ℂ G} {φ : Direction H} (D : Model B H φ) (Λ : Weight B H)
    (hχ : ∃! χ, IsWeightCharacter D Λ χ), affineSimpleAt_value D Λ hχ

def affineLevel_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G),
    Weight B H → ℂ

/-- The character exists at every weight, and the induced module has the stated
universal property, finite-dimensional weight spaces, and one-dimensional top. -/
def affineVermaProperties_type : Prop :=
  affineVermaCharacter_type.{u} ∧ affineVermaUniversal_type.{u, v} ∧ affineVermaWeights_type.{u}

/-- The sum of all proper submodules misses the highest vector. -/
def affineVermaRadicalProper_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H) (D : Model B H φ), B.IsNormalized H →
    Regular H φ → ∀ (Λ : Weight B H) (χ : U (affineBorel_value D) →ₐ[ℂ] ℂ),
    IsWeightCharacter D Λ χ →
    affineVermaTop_value D χ ∉ affineVermaRadical_value D χ

/-- The quotient is simple and generated by its nonzero highest vector of weight Λ. -/
def affineSimpleHighestWeight_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H) (D : Model B H φ), B.IsNormalized H →
    Regular H φ → ∀ (Λ : Weight B H) (χ : U (affineBorel_value D) →ₐ[ℂ] ℂ),
    IsWeightCharacter D Λ χ →
    IsSimpleModule (U (Carrier D)) (affineSimple_value D χ) ∧
      affineSimpleTop_value D χ ≠ 0 ∧ IsHighestVector D Λ (affineSimpleTop_value D χ) ∧
      ∀ x : affineSimple_value D χ, ∃ a : U (Carrier D), a • affineSimpleTop_value D χ = x

open scoped Classical in
/-- The simple quotient inherits the ordinary affine Cartan weight decomposition. -/
def affineSimpleWeights_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H) (D : Model B H φ), B.IsNormalized H →
    Regular H φ → ∀ (Λ : Weight B H) (χ : U (affineBorel_value D) →ₐ[ℂ] ℂ),
    IsWeightCharacter D Λ χ →
    let W := affineSimpleWeightSpace_value D χ
    DirectSum.IsInternal W ∧ (∀ μ, FiniteDimensional ℂ (W μ)) ∧
      W Λ = ℂ ∙ affineSimpleTop_value D χ

/-- Any simple quotient of the induced module is isomorphic to the canonical quotient
by a map carrying its highest vector to the image of the Verma highest vector. -/
def affineSimpleUnique_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H) (D : Model B H φ), B.IsNormalized H →
    Regular H φ → ∀ (Λ : Weight B H) (χ : U (affineBorel_value D) →ₐ[ℂ] ℂ),
    IsWeightCharacter D Λ χ →
    ∀ (V : Type v) [AddCommGroup V] [Module (U (Carrier D)) V] [IsSimpleModule (U (Carrier D)) V]
      (f : affineVerma_value D χ →ₗ[U (Carrier D)] V), Function.Surjective f →
      ∃! e : affineSimple_value D χ ≃ₗ[U (Carrier D)] V,
        ∀ x, e (affineSimpleProjection_value D χ x) = f x

/-- The central generator acts on both modules by the level Λ(K). -/
def affineLevelAction_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H) (D : Model B H φ), B.IsNormalized H →
    Regular H φ → ∀ (Λ : Weight B H) (χ : U (affineBorel_value D) →ₐ[ℂ] ℂ),
    IsWeightCharacter D Λ χ →
    let k := ι ℂ (show Carrier D from K_value B)
    let level := affineLevel_value B H Λ
    (∀ x : affineVerma_value D χ, k • x = level • x) ∧
      ∀ x : affineSimple_value D χ, k • x = level • x

end Specs.RepTheorySurvey.Affine.VermaModules
