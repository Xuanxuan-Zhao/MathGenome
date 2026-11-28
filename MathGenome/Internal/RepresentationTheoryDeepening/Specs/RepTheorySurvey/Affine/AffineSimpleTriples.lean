import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.TriangularRootSpaces
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.HighestRoot

/-! The highest root and the simple triples of the untwisted affine loop algebra. -/

noncomputable section

universe u

namespace RepTheorySurvey.Affine

open LieAlgebrasAndRepresentations.HighestRoot
open _root_.Specs.LieAlgebrasAndRepresentations
open RootDecomposition (rootSet_value rootSpace_value)
open RootForm (coroot_value)
open VermaModules (Direction)
open _root_.Specs.RepTheorySurvey.Affine.LoopAlgebra
open _root_.Specs.RepTheorySurvey.Affine.TriangularRootSpaces

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G]

/-- The greatest finite root in the order given by the chosen simple roots. -/
def IsHighestFiniteRoot (H : LieSubalgebra ℂ G) (φ : Direction H)
    (θ : Module.Dual ℂ H) : Prop :=
  θ ∈ positiveRoots H φ ∧ ∀ β ∈ rootSet_value H, θ - β ∈ positiveRootMonoid H φ

/-- An opposite pair normalized by the finite coroot. -/
structure FiniteRootTriple [FiniteDimensional ℂ G] (H : LieSubalgebra ℂ G)
    (α : Module.Dual ℂ H) where
  e : G
  f : G
  e_mem : e ∈ rootSpace_value H α
  f_mem : f ∈ rootSpace_value H (-α)
  e_ne_zero : e ≠ 0
  f_ne_zero : f ≠ 0
  lie_e_f : ⁅e, f⁆ = (coroot_value H α : G)

/-- The extra index `none` and one index for each finite simple root. -/
abbrev AffineSimpleIndex (H : LieSubalgebra ℂ G) (φ : Direction H) :=
  Option (simpleRoots H φ)

def alphaZero (B : InvariantForm G) (H : LieSubalgebra ℂ G) (θ : Module.Dual ℂ H) :
    Module.Dual ℂ (affineCartan_value B H) :=
  delta_value B H - extendFiniteRoot_value B H θ

def eZero [FiniteDimensional ℂ G] (B : InvariantForm G) {H : LieSubalgebra ℂ G}
    {θ : Module.Dual ℂ H} (T : FiniteRootTriple H θ) : AffineAlgebra B :=
  homogeneous_value B 1 T.f

def fZero [FiniteDimensional ℂ G] (B : InvariantForm G) {H : LieSubalgebra ℂ G}
    {θ : Module.Dual ℂ H} (T : FiniteRootTriple H θ) : AffineAlgebra B :=
  homogeneous_value B (-1) T.e

def hZero [FiniteDimensional ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    (θ : Module.Dual ℂ H) : AffineAlgebra B :=
  K_value B - homogeneous_value B 0 (coroot_value H θ : G)

def affineSimpleRoot (B : InvariantForm G) (H : LieSubalgebra ℂ G) {φ : Direction H}
    (θ : Module.Dual ℂ H) : AffineSimpleIndex H φ → Module.Dual ℂ (affineCartan_value B H)
  | none => alphaZero B H θ
  | some i => extendFiniteRoot_value B H i.val

def affineSimpleE [FiniteDimensional ℂ G] (B : InvariantForm G) {H : LieSubalgebra ℂ G}
    {φ : Direction H} {θ : Module.Dual ℂ H} (T : FiniteRootTriple H θ)
    (S : ∀ i : simpleRoots H φ, FiniteRootTriple H i.val) :
    AffineSimpleIndex H φ → AffineAlgebra B
  | none => eZero B T
  | some i => homogeneous_value B 0 (S i).e

def affineSimpleF [FiniteDimensional ℂ G] (B : InvariantForm G) {H : LieSubalgebra ℂ G}
    {φ : Direction H} {θ : Module.Dual ℂ H} (T : FiniteRootTriple H θ)
    (S : ∀ i : simpleRoots H φ, FiniteRootTriple H i.val) :
    AffineSimpleIndex H φ → AffineAlgebra B
  | none => fZero B T
  | some i => homogeneous_value B 0 (S i).f

def affineSimpleH [FiniteDimensional ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    {φ : Direction H} (θ : Module.Dual ℂ H) : AffineSimpleIndex H φ → AffineAlgebra B
  | none => hZero B H θ
  | some i => homogeneous_value B 0 (coroot_value H i.val : G)

/-- The underlying submodule of the Lie span for the specified affine bracket. -/
def affineLieSpan (B : InvariantForm G) (s : Set (AffineAlgebra B)) :
    Submodule ℂ (AffineAlgebra B) :=
  sInf {P | s ⊆ (P : Set (AffineAlgebra B)) ∧ ClosedUnderBracket B P}

end RepTheorySurvey.Affine

namespace Specs.RepTheorySurvey.Affine.AffineSimpleTriples

open _root_.RepTheorySurvey.Affine
open _root_.LieAlgebrasAndRepresentations.HighestRoot (simpleRoots)
open _root_.Specs.LieAlgebrasAndRepresentations
open RootForm (coroot_value)
open VermaModules (Direction Regular)
open LoopAlgebra TriangularRootSpaces

def highestFiniteRoot_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ → ∃! θ, IsHighestFiniteRoot H φ θ

def highestFiniteRootIsLong_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ → ∀ (θ : Module.Dual ℂ H)
    (hθ : IsHighestFiniteRoot H φ θ), IsLongRoot (H := H) ⟨θ, hθ.1.1⟩

def finiteSimpleTripleChoices_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ → ∀ (θ : Module.Dual ℂ H),
    IsHighestFiniteRoot H φ θ →
    Nonempty (FiniteRootTriple H θ × (∀ i : simpleRoots H φ, FiniteRootTriple H i.val))

def highestRootNormalization_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H), B.IsNormalized H → Regular H φ →
    ∀ (θ : Module.Dual ℂ H), IsHighestFiniteRoot H φ θ → ∀ T : FiniteRootTriple H θ,
    B.form T.e T.f = 1 ∧ ∀ y : H, B.form (coroot_value H θ : G) (y : G) = θ y

def affineSimpleRootWeights_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H), B.IsNormalized H → Regular H φ →
    ∀ (θ : Module.Dual ℂ H), IsHighestFiniteRoot H φ θ → ∀ (T : FiniteRootTriple H θ)
    (S : ∀ i : simpleRoots H φ, FiniteRootTriple H i.val) (i : AffineSimpleIndex H φ),
    affineSimpleH B H θ i ∈ affineCartan_value B H ∧
    affineSimpleRoot B H θ i ≠ 0 ∧
    IsAdjointWeightVector B H (affineSimpleRoot B H θ i) (affineSimpleE B T S i) ∧
    IsAdjointWeightVector B H (-affineSimpleRoot B H θ i) (affineSimpleF B T S i)

def affineSimpleTripleRelations_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H), B.IsNormalized H → Regular H φ →
    ∀ (θ : Module.Dual ℂ H), IsHighestFiniteRoot H φ θ → ∀ (T : FiniteRootTriple H θ)
    (S : ∀ i : simpleRoots H φ, FiniteRootTriple H i.val),
    (∀ i : AffineSimpleIndex H φ,
      let h := affineSimpleH B H θ i
      let e := affineSimpleE B T S i
      let f := affineSimpleF B T S i
      h ≠ 0 ∧ affineBracket_value B e f = h ∧
        affineBracket_value B h e = (2 : ℂ) • e ∧
        affineBracket_value B h f = (-2 : ℂ) • f) ∧
    ∀ i j : AffineSimpleIndex H φ, i ≠ j →
      affineBracket_value B (affineSimpleE B T S i) (affineSimpleF B T S j) = 0

def affineSimpleGenerators_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H), B.IsNormalized H → Regular H φ →
    ∀ (θ : Module.Dual ℂ H), IsHighestFiniteRoot H φ θ → ∀ (T : FiniteRootTriple H θ)
    (S : ∀ i : simpleRoots H φ, FiniteRootTriple H i.val),
    affineLieSpan B (Set.range (affineSimpleE B T S)) = affinePositive_value B H φ ∧
    affineLieSpan B (Set.range (affineSimpleF B T S)) = affineNegative_value B H φ

end Specs.RepTheorySurvey.Affine.AffineSimpleTriples
