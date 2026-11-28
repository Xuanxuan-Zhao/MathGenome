import Mathlib.Algebra.Lie.Loop
import Mathlib.Algebra.Lie.Extension
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootForm

/-! Coordinates and statements for the untwisted affine Lie algebra of LO09. -/

noncomputable section

open scoped TensorProduct LaurentPolynomial
open LieAlgebra LieModule

universe u

namespace RepTheorySurvey.Affine

/-- The invariant symmetric form whose scale determines the central term. -/
structure InvariantForm (G : Type u) [LieRing G] [LieAlgebra ℂ G] where
  form : LinearMap.BilinForm ℂ G
  invariant : form.lieInvariant G
  symmetric : form.IsSymm

abbrev Loop (G : Type u) [LieRing G] [LieAlgebra ℂ G] := loopAlgebra ℂ ℤ G

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G]

/-- The complex scalar line with the trivial loop action. -/
abbrev ScalarLine (G : Type u) [LieRing G] [LieAlgebra ℂ G] :=
  TrivialLieModule ℂ (Loop G) ℂ

instance : LieRing (ScalarLine G) where
  bracket _ _ := 0
  add_lie _ _ _ := (zero_add _).symm
  lie_add _ _ _ := (zero_add _).symm
  lie_self _ := rfl
  leibniz_lie _ _ _ := (zero_add _).symm

instance : LieAlgebra ℂ (ScalarLine G) where
  lie_smul _ _ _ := (smul_zero _).symm

instance : IsLieAbelian (ScalarLine G) := ⟨fun _ _ ↦ rfl⟩

/-- The sign changes the convention from `Res(f dg)` to `Res((df) g)`. -/
def loopCocycle (B : InvariantForm G) :
    Cohomology.twoCocycle ℂ (Loop G) (ScalarLine G) :=
  let c := LoopAlgebra.twoCocycleOfBilinear ℂ ℤ G B.form B.invariant B.symmetric
  ⟨(-1 : ℂ) • c.val, (Cohomology.twoCocycle ℂ (Loop G) (ScalarLine G)).smul_mem _ c.property⟩

abbrev LoopCentral (B : InvariantForm G) := LieAlgebra.ofTwoCocycle (loopCocycle B)

/-- The affine vector space, with the Lie structure to be established. -/
def AffineAlgebra (B : InvariantForm G) := LoopCentral B × ℂ

instance (B : InvariantForm G) : AddCommGroup (AffineAlgebra B) :=
  inferInstanceAs (AddCommGroup (LoopCentral B × ℂ))

instance (B : InvariantForm G) : Module ℂ (AffineAlgebra B) :=
  inferInstanceAs (Module ℂ (LoopCentral B × ℂ))

section Normalization

open LieAlgebrasAndRepresentations (rootSet rootForm)

/-- Long roots maximize squared length for the Killing-induced form, which is
real and positive on the real root span. -/
def IsLongRoot [FiniteDimensional ℂ G] {H : LieSubalgebra ℂ G}
    (α : rootSet H) : Prop :=
  ∀ β : rootSet H, (rootForm H β.val β.val).re ≤ (rootForm H α.val α.val).re

/-- The fixed form is nondegenerate and each long root has squared length two
for its induced dual form. The dual representative of a root is written `h`. -/
def InvariantForm.IsNormalized [FiniteDimensional ℂ G]
    (B : InvariantForm G) (H : LieSubalgebra ℂ G) : Prop :=
  B.form.Nondegenerate ∧
    ∀ α : rootSet H, IsLongRoot α →
      ∃ h : H, (∀ y : H, B.form (h : G) (y : G) = α.val y) ∧ α.val h = 2

end Normalization
end RepTheorySurvey.Affine

namespace Specs.RepTheorySurvey.Affine.LoopAlgebra

open _root_.RepTheorySurvey.Affine

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G]

def loopVector_value (m : ℤ) : G →ₗ[ℂ] Loop G :=
  TensorProduct.mk ℂ (AddMonoidAlgebra ℂ ℤ) G (AddMonoidAlgebra.single m 1)

def loopVector_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G], ℤ → G →ₗ[ℂ] Loop G

def loopVector_laurent_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (m : ℤ) (x : G),
    loopAlgebraEquivLaurent ℂ G (loopVector_value m x) = LaurentPolynomial.T m ⊗ₜ[ℂ] x

def loopVector_coefficients_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (m : ℤ) (x : G),
    LoopAlgebra.toFinsupp ℂ ℤ G (loopVector_value m x) = Finsupp.single m x

abbrev centralExtension_value (B : InvariantForm G) :
    Extension.{0, 0, u, u} ℂ (ScalarLine G) (Loop G) :=
  Extension.ofTwoCocycle (loopCocycle B)

def centralExtension_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G],
    InvariantForm G → Extension.{0, 0, u, u} ℂ (ScalarLine G) (Loop G)

def centralCoordinates_value (B : InvariantForm G) : LoopCentral B ≃ₗ[ℂ] Loop G × ℂ where
  __ := (ofProd (loopCocycle B)).symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def centralCoordinates_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G),
    LoopCentral B ≃ₗ[ℂ] Loop G × ℂ

def affineCoordinates_value (B : InvariantForm G) :
    AffineAlgebra B ≃ₗ[ℂ] (Loop G × ℂ) × ℂ :=
  (centralCoordinates_value B).prodCongr (LinearEquiv.refl ℂ ℂ)

def affineCoordinates_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G),
    AffineAlgebra B ≃ₗ[ℂ] (Loop G × ℂ) × ℂ

def centralLoopIncl_value (B : InvariantForm G) : Loop G →ₗ[ℂ] LoopCentral B :=
  (centralCoordinates_value B).symm.toLinearMap.comp (LinearMap.inl ℂ (Loop G) ℂ)

def centralLoopIncl_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G),
    Loop G →ₗ[ℂ] LoopCentral B

def centralLineIncl_value (B : InvariantForm G) (k : ℂ) : LoopCentral B :=
  (centralCoordinates_value B).symm (0, k)

def centralInclLinear_value (B : InvariantForm G) : LoopCentral B →ₗ[ℂ] AffineAlgebra B :=
  LinearMap.inl ℂ (LoopCentral B) ℂ

def centralInclLinear_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G),
    LoopCentral B →ₗ[ℂ] AffineAlgebra B

def K_value (B : InvariantForm G) : AffineAlgebra B :=
  (affineCoordinates_value B).symm ((0, 1), 0)

def K_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G), AffineAlgebra B

def d_value (B : InvariantForm G) : AffineAlgebra B :=
  (affineCoordinates_value B).symm ((0, 0), 1)

def d_type := K_type

def homogeneous_value (B : InvariantForm G) (m : ℤ) (x : G) : AffineAlgebra B :=
  (affineCoordinates_value B).symm ((loopVector_value m x, 0), 0)

def homogeneous_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G),
    ℤ → G → AffineAlgebra B

/-- The loop degree operator, expressed in the finitely supported coordinates. -/
def loopDegree_value (G : Type u) [LieRing G] [LieAlgebra ℂ G] : Loop G →ₗ[ℂ] Loop G :=
  let e := LieAlgebra.LoopAlgebra.toFinsupp ℂ ℤ G
  e.symm.toLinearMap.comp <| (Finsupp.lsum ℂ fun m : ℤ ↦
    (m : ℂ) • (Finsupp.lsingle m : G →ₗ[ℂ] ℤ →₀ G)).comp e.toLinearMap

def loopDegree_type :=
  ∀ (G : Type u) [LieRing G] [LieAlgebra ℂ G], Loop G →ₗ[ℂ] Loop G

def degreeCentral_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G),
    LoopCentral B →ₗ[ℂ] LoopCentral B

def degreeCentral_value (B : InvariantForm G) : LoopCentral B →ₗ[ℂ] LoopCentral B :=
  (centralLoopIncl_value B).comp <|
    (loopDegree_value G).comp (centralExtension_value B).proj.toLinearMap

/-- The bracket on the direct sum, independent of a LieRing instance on it. -/
def affineBracket_value (B : InvariantForm G) (x y : AffineAlgebra B) :
    AffineAlgebra B :=
  let p : LoopCentral B × ℂ := x
  let q : LoopCentral B × ℂ := y
  (⁅p.1, q.1⁆ + p.2 • degreeCentral_value B q.1 - q.2 • degreeCentral_value B p.1, 0)

def affineBracket_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G),
    AffineAlgebra B → AffineAlgebra B → AffineAlgebra B

def affineStructure_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G),
    ∃ lieRing : LieRing (AffineAlgebra B),
      ∃ lieAlgebra : @LieAlgebra ℂ (AffineAlgebra B) _ lieRing,
        lieRing.toAddCommGroup = (inferInstance : AddCommGroup (AffineAlgebra B)) ∧
          HEq lieAlgebra.toModule (inferInstance : Module ℂ (AffineAlgebra B)) ∧
          ∀ x y, lieRing.toBracket.bracket x y = affineBracket_value B x y

def loopIncl_value (B : InvariantForm G) : Loop G →ₗ[ℂ] AffineAlgebra B :=
  (centralInclLinear_value B).comp (centralLoopIncl_value B)

def loopIncl_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G),
    Loop G →ₗ[ℂ] AffineAlgebra B

def degreeIncl_value (B : InvariantForm G) : ScalarLine G →ₗ[ℂ] AffineAlgebra B :=
  (LinearMap.inr ℂ (LoopCentral B) ℂ).comp (TrivialLieModule.equiv ℂ (Loop G) ℂ).toLinearMap

def degreeIncl_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G),
    ScalarLine G →ₗ[ℂ] AffineAlgebra B

def constantIncl_value (B : InvariantForm G) : G →ₗ[ℂ] AffineAlgebra B :=
  (loopIncl_value B).comp (loopVector_value 0)

def constantIncl_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G),
    G →ₗ[ℂ] AffineAlgebra B

def centralIncl_range_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G) (x : AffineAlgebra B),
    (∃ y : LoopCentral B, centralInclLinear_value B y = x) ↔
      (affineCoordinates_value B x).2 = 0

def coordinateEmbeddings_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G),
    Function.Injective (centralLoopIncl_value B) ∧
    Function.Injective (centralInclLinear_value B) ∧
    Function.Injective (loopIncl_value B) ∧
    Function.Injective (degreeIncl_value B) ∧
    Function.Injective (constantIncl_value B) ∧
    (∀ f, affineCoordinates_value B (loopIncl_value B f) = ((f, 0), 0)) ∧
    (∀ k : ScalarLine G, affineCoordinates_value B
      (centralInclLinear_value B ((centralExtension_value B).incl k)) =
        ((0, (k : ℂ)), 0)) ∧
    (∀ k : ScalarLine G, affineCoordinates_value B (degreeIncl_value B k) = ((0, 0), (k : ℂ)))

def centralExtension_central_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G)
    (k : ScalarLine G) (x : LoopCentral B),
    let z : LoopCentral B := (centralExtension_value B).incl k
    ⁅z, x⁆ = 0

def centralBracket_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G)
    (m n : ℤ) (x y : G),
    ⁅centralLoopIncl_value B (loopVector_value m x),
      centralLoopIncl_value B (loopVector_value n y)⁆ =
      centralLoopIncl_value B (loopVector_value (m + n) ⁅x, y⁆) +
        (if m = -n then (m : ℂ) * B.form x y else 0) • (centralLineIncl_value B 1)

def homogeneousBracket_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G)
    (m n : ℤ) (x y : G),
    affineBracket_value B (homogeneous_value B m x) (homogeneous_value B n y) =
      homogeneous_value B (m + n) ⁅x, y⁆ +
        (if m = -n then (m : ℂ) * B.form x y else 0) • K_value B

def degreeBracket_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G) (m : ℤ) (x : G),
    affineBracket_value B (d_value B) (homogeneous_value B m x) =
      (m : ℂ) • homogeneous_value B m x

def centralGenerator_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G) (x : AffineAlgebra B),
    affineBracket_value B (K_value B) x = 0

def cartanNondegenerate_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra]
    (B : InvariantForm G), B.form.Nondegenerate → (B.form.restrict H.toSubmodule).Nondegenerate

def cartanNontrivial_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra], Nontrivial H

def cartanAbelian_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra], IsLieAbelian H

def normalizedRootLengths_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra]
    (B : InvariantForm G) (hH : (B.form.restrict H.toSubmodule).Nondegenerate),
    B.IsNormalized H ↔ B.form.Nondegenerate ∧
      ∀ α : LieAlgebrasAndRepresentations.rootSet H, IsLongRoot α →
        α.val (((B.form.restrict H.toSubmodule).toDual hH).symm α.val) = 2

end Specs.RepTheorySurvey.Affine.LoopAlgebra
