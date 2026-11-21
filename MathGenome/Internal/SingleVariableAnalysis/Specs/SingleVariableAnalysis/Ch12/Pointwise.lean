import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SequenceLimit

/-!
Independent specification for `K03.12.pointwise`, paper.tex:1190–1197.
The arbitrary type `E` represents the domain itself; a subset of an ambient
space is represented by its subtype. No topology or nonemptiness is required.
As in the upstream sequence interface, Lean index `n` denotes term `n + 1`.
The quantifier for the tail index follows the point and the positive epsilon.
-/

namespace Specs.SingleVariableAnalysis.Ch12.Pointwise

open _root_.SingleVariableAnalysis
open scoped Topology

universe u

def realPointwiseConvergesType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℝ) → (E → ℝ) → Prop

def realPointwiseConvergesValue : realPointwiseConvergesType :=
  fun F f => ∀ x, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |F n x - f x| < ε

def complexPointwiseConvergesType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℂ) → (E → ℂ) → Prop

def complexPointwiseConvergesValue : complexPointwiseConvergesType :=
  fun F f => ∀ x, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ‖F n x - f x‖ < ε

def realPointwiseConvergesEpsilonIff : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℝ) (f : E → ℝ),
    realPointwiseConvergesValue F f ↔
      ∀ x, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |F n x - f x| < ε

def complexPointwiseConvergesEpsilonIff : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℂ) (f : E → ℂ),
    complexPointwiseConvergesValue F f ↔
      ∀ x, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ‖F n x - f x‖ < ε

/-- Compatibility with the already fixed scalar sequence interface. -/
def realPointwiseConvergesSequenceIff : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℝ) (f : E → ℝ),
    realPointwiseConvergesValue F f ↔
      ∀ x, Ch01.SequenceLimit.realSequenceConvergesValue (fun n => F n x) (f x)

def complexPointwiseConvergesSequenceIff : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℂ) (f : E → ℂ),
    complexPointwiseConvergesValue F f ↔
      ∀ x, Ch01.SequenceLimit.complexSequenceConvergesValue (fun n => F n x) (f x)

def realPointwiseLimitUnique : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℝ) (f g : E → ℝ),
    realPointwiseConvergesValue F f → realPointwiseConvergesValue F g → f = g

def complexPointwiseLimitUnique : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℂ) (f g : E → ℂ),
    complexPointwiseConvergesValue F f → complexPointwiseConvergesValue F g → f = g

/-- The empty function is defined for either canonical scalar target. -/
def emptyScalarFunctionType : Type (u + 1) :=
  (k : ScalarKind) → (E : Type u) → [IsEmpty E] → E → Ch01.Scalar.scalarValue k

def emptyScalarFunctionValue : emptyScalarFunctionType :=
  fun _ _ _ x => isEmptyElim x

def emptyScalarFunctionUnique : Prop :=
  ∀ (k : ScalarKind) (E : Type u) [IsEmpty E] (f : E → Ch01.Scalar.scalarValue k),
    f = emptyScalarFunctionValue k E

/-- Every function on an empty domain is a pointwise limit, vacuously. -/
def realPointwiseConvergesEmpty : Prop :=
  ∀ {E : Type u} [IsEmpty E] (F : ℕ → E → ℝ) (f : E → ℝ),
    realPointwiseConvergesValue F f

def complexPointwiseConvergesEmpty : Prop :=
  ∀ {E : Type u} [IsEmpty E] (F : ℕ → E → ℂ) (f : E → ℂ),
    complexPointwiseConvergesValue F f

end Specs.SingleVariableAnalysis.Ch12.Pointwise
