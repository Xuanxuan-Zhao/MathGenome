import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Cartan data over the complex numbers, with the coroot indexing the row. -/

namespace Specs.LieNotes.Contragredient.CartanData

-- The type specifications retain separate universes for the indices and the Cartan space.
set_option linter.checkUnivs false

universe u v

variable {I : Type u} {A : Matrix I I ℤ}
variable {H : Type v} [AddCommGroup H] [Module ℂ H]

def MatrixPredicate := {I : Type u} → [Finite I] → Matrix I I ℤ → Prop

/-- The diagonal, sign and zero-pattern conditions for a generalized Cartan matrix. -/
def IsGeneralizedCartanMatrix [Finite I] (A : Matrix I I ℤ) : Prop :=
  (∀ i, A i i = 2) ∧
  (∀ i j, i ≠ j → A i j ≤ 0) ∧
  (∀ i j, A i j = 0 ↔ A j i = 0)

/-- Symmetrizability is defined using a strictly positive real diagonal. -/
def IsSymmetrizable [Finite I] (A : Matrix I I ℤ) : Prop :=
  ∃ d : I → ℝ, (∀ i, 0 < d i) ∧ (∀ i j, d i * (A i j : ℝ) = d j * (A j i : ℝ))

def RealizationType :=
  {I : Type u} → [Finite I] → Matrix I I ℤ → (H : Type v) → [AddCommGroup H] → [Module ℂ H] →
    Type (max u v)

/-- Independent coroots and independent roots with the specified evaluation pairing. -/
structure Realization [Finite I] (A : Matrix I I ℤ) (H : Type v) [AddCommGroup H] [Module ℂ H] where
  h : I → H
  α : I → Module.Dual ℂ H
  h_independent : LinearIndependent ℂ h
  α_independent : LinearIndependent ℂ α
  pairing : ∀ i j, α j (h i) = (A i j : ℂ)

abbrev RealizationValue [Finite I] (A : Matrix I I ℤ) (H : Type v) [AddCommGroup H] [Module ℂ H] :=
  Realization A H

def MinimalityType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I] [Fintype I],
    Realization A H → Prop

/-- A minimal realization is finite-dimensional with dimension twice the size
of the index type minus the complex rank of the Cartan matrix. -/
def Realization.IsMinimal [Finite I] [Fintype I] (_R : Realization A H) : Prop :=
  FiniteDimensional ℂ H ∧
    Module.finrank ℂ H = 2 * Fintype.card I - (A.map fun a : ℤ => (a : ℂ)).rank

def QType := Type u → Type u

/-- The root lattice in simple-root coordinates. -/
abbrev Q (I : Type u) := I →₀ ℤ

def SimpleDegreeType := ∀ {I : Type u}, I → Q I

/-- The degree of the positive simple generator at index `i`. -/
noncomputable def simpleDegree (i : I) : Q I := Finsupp.single i 1

def DegreePredicate := ∀ {I : Type u}, Q I → Prop

/-- A positive degree is a nonzero lattice vector with nonnegative coordinates. -/
def PositiveDegree (q : Q I) : Prop :=
  q ≠ 0 ∧ ∀ i, 0 ≤ q i

/-- Negative degrees are the negatives of positive degrees. -/
def NegativeDegree (q : Q I) : Prop :=
  PositiveDegree (-q)

def RootWeightType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    Realization A H → (Q I →+ Module.Dual ℂ H)

/-- The weight of a lattice vector is the indicated integral linear combination of roots. -/
noncomputable def Realization.rootWeight [Finite I] (R : Realization A H) :
    Q I →+ Module.Dual ℂ H :=
  (Finsupp.linearCombination ℂ R.α).toAddMonoidHom.comp
    (Finsupp.mapRange.addMonoidHom (Int.castAddHom ℂ))

def CorootPairingType := ∀ {I : Type u}, Matrix I I ℤ → I → (Q I →ₗ[ℤ] ℤ)

/-- Integral evaluation at the `i`th coroot, using the `i`th row. -/
noncomputable def corootPairing (A : Matrix I I ℤ) (i : I) : Q I →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (A i)

def RootReflectionType := ∀ {I : Type u}, Matrix I I ℤ → I → (Q I →ₗ[ℤ] Q I)

/-- Simple reflection in integral root coordinates. -/
noncomputable def rootReflection (A : Matrix I I ℤ) (i : I) : Q I →ₗ[ℤ] Q I :=
  LinearMap.id - (Finsupp.lsingle i).comp (corootPairing A i)

def WeightReflectionType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    Realization A H → I → (Module.Dual ℂ H →ₗ[ℂ] Module.Dual ℂ H)

/-- Simple reflection on the full Cartan dual, including weights outside the root lattice. -/
def Realization.weightReflection [Finite I] (R : Realization A H) (i : I) :
    Module.Dual ℂ H →ₗ[ℂ] Module.Dual ℂ H :=
  LinearMap.id - (Module.Dual.eval ℂ H (R.h i)).smulRight (R.α i)

def RootWeightSingle : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    ∀ (R : Realization A H) (i : I) (m : ℤ),
      R.rootWeight (Finsupp.single i m) = (m : ℂ) • R.α i

def RootWeightSimple : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    ∀ (R : Realization A H) (i : I), R.rootWeight (simpleDegree i) = R.α i

def RootWeightInjective : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    ∀ (R : Realization A H), Function.Injective R.rootWeight

def CorootPairingSingle : Prop :=
  ∀ {I : Type u} (A : Matrix I I ℤ) (i j : I) (m : ℤ),
    corootPairing A i (Finsupp.single j m) = m * A i j

def RootWeightApplyCoroot : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    ∀ (R : Realization A H) (q : Q I) (i : I),
      R.rootWeight q (R.h i) = (corootPairing A i q : ℂ)

def RootReflectionApply : Prop :=
  ∀ {I : Type u} (A : Matrix I I ℤ) (i : I) (q : Q I),
    rootReflection A i q = q - Finsupp.single i (corootPairing A i q)

def WeightReflectionApply : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    ∀ (R : Realization A H) (i : I) (μ : Module.Dual ℂ H),
      R.weightReflection i μ = μ - μ (R.h i) • R.α i

def RootWeightRootReflection : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    ∀ (R : Realization A H) (i : I) (q : Q I),
      R.rootWeight (rootReflection A i q) = R.weightReflection i (R.rootWeight q)

def RootReflectionInvolutive : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} [Finite I],
    IsGeneralizedCartanMatrix A → ∀ i, Function.Involutive (rootReflection A i)

def WeightReflectionInvolutive : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    ∀ (R : Realization A H), IsGeneralizedCartanMatrix A →
      ∀ i, Function.Involutive (R.weightReflection i)

end Specs.LieNotes.Contragredient.CartanData
