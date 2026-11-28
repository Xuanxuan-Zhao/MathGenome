import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Virasoro.WittAlgebra
import Mathlib.Algebra.Lie.Cochain

/-! The cocycle and the underlying product model in Theorem KM11. -/

noncomputable section

open LieModule.Cohomology

namespace LieNotes.Virasoro.VirasoroSpec

local notation "W" => WittSpec.Witt

/-- The scalar multiplying the chosen central vector on the pair of modes. -/
def centralCoefficient (m n : ℤ) : ℂ :=
  if m + n = 0 then ((m : ℂ)^3 - (m : ℂ)) / 12 else 0

/-- The Laurent monomial of index `m` is `t^(m+1)`. The Witt mode has
the negative of this Laurent coefficient. -/
def shiftedLaurentBasis : Module.Basis ℤ ℂ (LaurentPolynomial ℂ) :=
  (AddMonoidAlgebra.basis ℤ ℂ).reindex (Equiv.subRight 1)

abbrev CocycleFormType : Type _ :=
  ∀ {Z : Type*} [AddCommGroup Z] [Module ℂ Z], Z → W →ₗ[ℂ] W →ₗ[ℂ] Z

/-- Extend the specified coefficients bilinearly, using the signed Laurent
coefficients of the two derivations. -/
def cocycleForm : CocycleFormType :=
  fun {_Z} _ _ z =>
    (shiftedLaurentBasis.constr ℂ fun m =>
      shiftedLaurentBasis.constr ℂ fun n => centralCoefficient m n • z).compl₂
      (-WittSpec.evaluation) ∘ₗ (-WittSpec.evaluation)

def FormOnModes : Prop :=
  ∀ {Z : Type*} [AddCommGroup Z] [Module ℂ Z] (z : Z) (m n : ℤ),
    cocycleForm z (WittSpec.mode m) (WittSpec.mode n) = centralCoefficient m n • z

def FormAlternating : Prop :=
  ∀ {Z : Type*} [AddCommGroup Z] [Module ℂ Z] (z : Z) (x : W), cocycleForm z x x = 0

def FormCyclic : Prop :=
  ∀ {Z : Type*} [AddCommGroup Z] [Module ℂ Z] (z : Z) (x y u : W),
    cocycleForm z ⁅x, y⁆ u + cocycleForm z ⁅y, u⁆ x + cocycleForm z ⁅u, x⁆ y = 0

def BundledCocycleExists : Prop :=
  ∀ {Z : Type*} [AddCommGroup Z] [Module ℂ Z] [LieRingModule W Z] [LieModule ℂ W Z]
    [LieModule.IsTrivial W Z] (z : Z),
      ∃ c : twoCocycle ℂ W Z, c.val.val = cocycleForm z

def CoboundaryOnTrivialCoefficients : Prop :=
  ∀ {Z : Type*} [AddCommGroup Z] [Module ℂ Z] [LieRingModule W Z] [LieModule ℂ W Z]
    [LieModule.IsTrivial W Z] (φ : W →ₗ[ℂ] Z) (x y : W),
      d₁₂ ℂ W Z φ x y = -φ ⁅x, y⁆

/-- The underlying vector space of the canonical extension. -/
def Vir : Type := W × ℂ

abbrev VirType : Type 1 := Type

instance : AddCommGroup Vir := inferInstanceAs (AddCommGroup (W × ℂ))
instance : Module ℂ Vir := inferInstanceAs (Module ℂ (W × ℂ))

abbrev CoordinatesType : Type := Vir ≃ₗ[ℂ] W × ℂ

/-- The Witt and central coordinates of a vector of the extension. -/
def coordinates : CoordinatesType := LinearEquiv.refl ℂ (W × ℂ)

abbrev ModeType : Type := ℤ → Vir
def mode (m : ℤ) : Vir := coordinates.symm (WittSpec.mode m, 0)

abbrev CentralType : Type := Vir
def central : Vir := coordinates.symm (0, 1)

def bracket (x y : Vir) : Vir :=
  coordinates.symm
    (⁅(coordinates x).1, (coordinates y).1⁆,
      cocycleForm (1 : ℂ) (coordinates x).1 (coordinates y).1)

def ProjectionOnCoordinates : Vir →ₗ[ℂ] W :=
  LinearMap.fst ℂ W ℂ ∘ₗ coordinates.toLinearMap

def ModeBracket : Prop :=
  ∀ m n : ℤ, bracket (mode m) (mode n) =
    ((m : ℂ) - (n : ℂ)) • mode (m + n) + centralCoefficient m n • central

def CentralBracket : Prop := ∀ x : Vir, bracket central x = 0

def ProjectionSurjective : Prop := Function.Surjective ProjectionOnCoordinates

def ProjectionKernel : Prop :=
  ∀ x : Vir, ProjectionOnCoordinates x = 0 ↔ ∃ a : ℂ, x = a • central

def CentralNonzero : Prop := central ≠ 0

def CanonicalLieProjection : Prop :=
  ∃ r : LieRing Vir, ∃ a : @LieAlgebra ℂ Vir _ r,
    letI : LieRing Vir := r
    letI : LieAlgebra ℂ Vir := a
    ∃ p : Vir →ₗ⁅ℂ⁆ W, (∀ x, p x = (coordinates x).1) ∧
      (∀ x y : Vir, ⁅x, y⁆ = bracket x y)

end LieNotes.Virasoro.VirasoroSpec
