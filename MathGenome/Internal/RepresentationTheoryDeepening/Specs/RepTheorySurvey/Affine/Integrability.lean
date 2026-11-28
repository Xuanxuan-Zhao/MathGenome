import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.VermaModules

/-! Integrability of simple highest-weight modules of the untwisted affine algebra. -/

noncomputable section

open scoped TensorProduct
open UniversalEnvelopingAlgebra (ι)

universe u v

namespace Specs.RepTheorySurvey.Affine.Integrability

open _root_.RepTheorySurvey.Affine
open _root_.RepTheorySurvey.CategoryO.BorelInduction (U)
open _root_.LieAlgebrasAndRepresentations.HighestRoot (simpleRoots)
open _root_.Specs.LieAlgebrasAndRepresentations.RootForm (coroot_value)
open _root_.Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open LoopAlgebra (homogeneous_value)
open TriangularRootSpaces (affineCartan_value cartanDegrees coordinates)
open VermaWeightSpaces (Model Carrier Weight affineBorel_value IsWeightCharacter)
open VermaModules (centralCartanElement affineSimple_value affineLevel_value)

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G]
  {B : InvariantForm G} {H : LieSubalgebra ℂ G} {φ : Direction H}

/-- A constant finite Cartan vector belongs to the affine Cartan. -/
private def constantCartan (B : InvariantForm G) (H : LieSubalgebra ℂ G) (h : H) :
    affineCartan_value B H :=
  ⟨homogeneous_value B 0 h, by
    change (∀ m, (coordinates B (homogeneous_value B 0 h)).1.1 m ∈ cartanDegrees H m) ∧
      (coordinates B (homogeneous_value B 0 h)).1.2 ∈ (⊤ : Submodule ℂ ℂ) ∧
      (coordinates B (homogeneous_value B 0 h)).2 ∈ (⊤ : Submodule ℂ ℂ)
    refine ⟨fun m => ?_, Submodule.mem_top, Submodule.mem_top⟩
    have hm : (coordinates B (homogeneous_value B 0 h)).1.1 m = Finsupp.single 0 (h : G) m := by
      change (LieAlgebra.LoopAlgebra.toFinsupp ℂ ℤ G
        (AddMonoidAlgebra.single 0 1 ⊗ₜ[ℂ] (h : G))) m = _
      rw [LieAlgebra.LoopAlgebra.toFinsupp_single_tmul]
    rw [hm]
    by_cases he : m = 0
    · subst m
      simp [cartanDegrees]
    · simp [cartanDegrees, he]⟩

/-- The affine simple coroot, as an element in the domain of affine weights. -/
def affineSimpleCoroot_value [FiniteDimensional ℂ G] (B : InvariantForm G)
    (H : LieSubalgebra ℂ G) {φ : Direction H} (θ : Module.Dual ℂ H) :
    AffineSimpleIndex H φ → affineCartan_value B H
  | none => centralCartanElement B H - constantCartan B H (coroot_value H θ)
  | some i => constantCartan B H (coroot_value H i.val)

def affineSimpleCoroot_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    (B : InvariantForm G) (H : LieSubalgebra ℂ G) {φ : Direction H}
    (_θ : Module.Dual ℂ H), AffineSimpleIndex H φ → affineCartan_value B H

@[simp] theorem coe_affineSimpleCoroot [FiniteDimensional ℂ G] (θ : Module.Dual ℂ H)
    (i : AffineSimpleIndex H φ) :
    (affineSimpleCoroot_value B H θ i : AffineAlgebra B) = affineSimpleH B H θ i := by
  cases i <;> rfl

/-- On a weight module, integrability means local nilpotence of every affine simple
raising and lowering operator on every vector. -/
def IsIntegrable_value [FiniteDimensional ℂ G] (D : Model B H φ)
    {θ : Module.Dual ℂ H} (T : FiniteRootTriple H θ)
    (S : ∀ i : simpleRoots H φ, FiniteRootTriple H i.val)
    (V : Type v) [AddCommGroup V] [Module (U (Carrier D)) V] : Prop :=
  ∀ i : AffineSimpleIndex H φ,
    (∀ x : V, ∃ n : ℕ, (ι ℂ (show Carrier D from affineSimpleE B (θ := θ) T S i)) ^ n • x = 0) ∧
    (∀ x : V, ∃ n : ℕ, (ι ℂ (show Carrier D from affineSimpleF B T S i)) ^ n • x = 0)

set_option linter.checkUnivs false in
def IsIntegrable_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G]
    {B : InvariantForm G} {H : LieSubalgebra ℂ G} {φ : Direction H} [FiniteDimensional ℂ G]
    (D : Model B H φ) {θ : Module.Dual ℂ H} (_T : FiniteRootTriple H θ)
    (_S : ∀ i : simpleRoots H φ, FiniteRootTriple H i.val)
    (V : Type v) [AddCommGroup V] [Module (U (Carrier D)) V], Prop

/-- Integrability of the canonical simple highest-weight quotient is equivalent to
nonnegative integral values on the affine simple coroots. -/
def affineSimpleIntegrable_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H) (D : Model B H φ), B.IsNormalized H →
    Regular H φ → ∀ (θ : Module.Dual ℂ H), IsHighestFiniteRoot H φ θ →
    ∀ (T : FiniteRootTriple H θ) (S : ∀ i : simpleRoots H φ, FiniteRootTriple H i.val)
    (Λ : Weight B H) (χ : U (affineBorel_value D) →ₐ[ℂ] ℂ), IsWeightCharacter D Λ χ →
    (IsIntegrable_value D T S (affineSimple_value D χ) ↔
      ∀ i : AffineSimpleIndex H φ, ∃ n : ℕ, Λ (affineSimpleCoroot_value B H θ i) = (n : ℂ))

/-- The highest finite root's coroot has nonnegative integral simple-coroot
coordinates. -/
def highestFiniteCorootCoordinates_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (θ : Module.Dual ℂ H), IsHighestFiniteRoot H φ θ →
      ∃ a : simpleRoots H φ →₀ ℕ, coroot_value H θ = a.sum (fun i n => n • coroot_value H i.val)

/-- The level formula for the simple-coroot coordinates of the highest finite coroot. -/
def affineLevelFormula_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    (B : InvariantForm G) (H : LieSubalgebra ℂ G) (φ : Direction H)
    (θ : Module.Dual ℂ H) (a : simpleRoots H φ →₀ ℕ),
    coroot_value H θ = a.sum (fun i n => n • coroot_value H i.val) →
    ∀ Λ : Weight B H, affineLevel_value B H Λ =
      Λ (affineSimpleCoroot_value (φ := φ) B H θ none) +
        a.sum (fun i n => (n : ℂ) * Λ (affineSimpleCoroot_value B H θ (some i)))

/-- The level of an integrable simple affine highest-weight quotient is a
nonnegative integer. -/
def affineIntegrableLevel_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H) (D : Model B H φ), B.IsNormalized H →
    Regular H φ → ∀ (θ : Module.Dual ℂ H), IsHighestFiniteRoot H φ θ →
    ∀ (T : FiniteRootTriple H θ) (S : ∀ i : simpleRoots H φ, FiniteRootTriple H i.val)
    (Λ : Weight B H) (χ : U (affineBorel_value D) →ₐ[ℂ] ℂ), IsWeightCharacter D Λ χ →
    IsIntegrable_value D T S (affineSimple_value D χ) →
    ∃ n : ℕ, affineLevel_value B H Λ = (n : ℂ)

end Specs.RepTheorySurvey.Affine.Integrability
