import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.MultiplicityModel

/-!
Uniqueness in paper.tex, `fa2:p2:spectral-multiplicity` (12245–12302 in the
adopted source). All measures are Borel measures on the *same* spectral
parameter ℂ. Unitary equivalence intertwines multiplication by z, rather than
allowing a change of spectral parameter. Zero measures are included.

The rectangular field is a canonical zero extension between coordinate fibers.
Its unitary condition holds on one common conull set. Measurability is tested
on constant vectors (the strong operator sense), not in operator norm.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ExpandedFA.VonNeumann.MultiplicityUniqueness.Spec
open MultiplicityModel.Spec

/-- Equality of the scalar measure class and multiplicity invariant. -/
def SameData (μ ν : Measure ℂ) (m : Multiplicity μ) (n : Multiplicity ν) : Prop :=
  μ ≪ ν ∧ ν ≪ μ ∧ m.toFun =ᵐ[μ] n.toFun

/-- Unitary equivalence of the actual bounded coordinate operators. -/
def CoordinateEquivalent (μ ν : Measure ℂ) (m : Multiplicity μ) (n : Multiplicity ν)
    (hμ : BoundedCoordinate μ) (hν : BoundedCoordinate ν) : Prop :=
  ∃ U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral ν n,
    ∀ f, U (coordinateOperatorValue μ m hμ f) = coordinateOperatorValue ν n hν (U f)

/-- Commutation with every bounded Borel scalar multiplication. Stated via
its a.e. graph to avoid choosing representatives of L∞ classes. -/
def IntertwinesScalars {μ : Measure ℂ} {m n : Multiplicity μ}
    (T : DirectIntegral μ m →L[ℂ] DirectIntegral μ n) : Prop :=
  ∀ (φ : ℂ → ℂ), Measurable φ → (∃ C : ℝ, ∀ z, ‖φ z‖ ≤ C) →
    ∀ f g : DirectIntegral μ m,
    (g.val =ᵐ[μ] fun z => φ z • f.val z) →
    (T g).val =ᵐ[μ] fun z => φ z • (T f).val z

/-- A unitary from the d-fiber onto the e-fiber, extended by zero. The norm
and surjectivity clauses refer to the fibers themselves, including d=0. -/
def IsFiberUnitary (d e : ℕ∞) (B : SequenceSpace →L[ℂ] SequenceSpace) : Prop :=
  (∀ x, B x ∈ fiber e) ∧
  (∀ x ∈ (fiber d)ᗮ, B x = 0) ∧
  (∀ x ∈ fiber d, ‖B x‖ = ‖x‖) ∧
  (∀ y ∈ fiber e, ∃ x ∈ fiber d, B x = y)

structure UnitaryField (μ : Measure ℂ) (m n : Multiplicity μ) where
  toFun : ℂ → SequenceSpace →L[ℂ] SequenceSpace
  measurable_orbit : ∀ x, AEStronglyMeasurable (fun z => toFun z x) μ
  unitary : ∀ᵐ z ∂μ, IsFiberUnitary (m z) (n z) (toFun z)

instance {μ : Measure ℂ} {m n : Multiplicity μ} :
    CoeFun (UnitaryField μ m n) (fun _ => ℂ → SequenceSpace →L[ℂ] SequenceSpace) :=
  ⟨UnitaryField.toFun⟩

/-- Equality of actual L² actions; the exceptional set may depend on the
section, whereas the field's fiber-unitarity exceptional set is common. -/
def Realizes {μ : Measure ℂ} {m n : Multiplicity μ}
    (U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n) (B : UnitaryField μ m n) : Prop :=
  ∀ f, (U f).val =ᵐ[μ] fun z => B z (f.val z)

/-- The full classification of bounded finite-measure coordinate models. -/
def Classification : Prop :=
  ∀ (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (m : Multiplicity μ) (n : Multiplicity ν)
    (hμ : BoundedCoordinate μ) (hν : BoundedCoordinate ν),
    CoordinateEquivalent μ ν m n hμ hν ↔ SameData μ ν m n

/-- The fiberwise statement required for a scalar-intertwining unitary. -/
def UnitaryDecomposition : Prop :=
  ∀ (μ : Measure ℂ) [IsFiniteMeasure μ] (m n : Multiplicity μ)
    (U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n),
    IntertwinesScalars U.toLinearIsometry.toContinuousLinearMap →
    ∃ B : UnitaryField μ m n, Realizes U B

/-- Equality of the invariants suffices, without normalization of the measure. -/
def Sufficiency : Prop :=
  ∀ (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (m : Multiplicity μ) (n : Multiplicity ν)
    (hμ : BoundedCoordinate μ) (hν : BoundedCoordinate ν),
    SameData μ ν m n → CoordinateEquivalent μ ν m n hμ hν

/-- The spectral-projection bridge: equivalence of coordinate operators
preserves the finite scalar measure class. -/
def MeasureClassInvariant : Prop :=
  ∀ (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (m : Multiplicity μ) (n : Multiplicity ν)
    (hμ : BoundedCoordinate μ) (hν : BoundedCoordinate ν),
    CoordinateEquivalent μ ν m n hμ hν → μ ≪ ν ∧ ν ≪ μ

/-- Fuglede and Borel calculus on the native L² models give scalar
intertwining, with no extra assumption on the coordinate unitary. -/
def CoordinateScalarIntertwining : Prop :=
  ∀ (μ : Measure ℂ) [IsFiniteMeasure μ] (m n : Multiplicity μ)
    (hμ hν : BoundedCoordinate μ)
    (U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n),
    (∀ f, U (coordinateOperatorValue μ m hμ f) =
      coordinateOperatorValue μ n hν (U f)) →
    IntertwinesScalars U.toLinearIsometry.toContinuousLinearMap

/-- Explicit assembly interface for the spectral bridges and fiber decomposition.
This conditional helper is not the unconditional classification target. -/
def ClassificationFromBridges : Prop :=
  MeasureClassInvariant → CoordinateScalarIntertwining → UnitaryDecomposition → Classification

/-- Ordinary unitary invariance of the finite-or-countable fiber dimension. -/
def FiberDimension : Prop :=
  ∀ (d e : ℕ∞) (B : SequenceSpace →L[ℂ] SequenceSpace), IsFiberUnitary d e B → d = e

end ExpandedFA.VonNeumann.MultiplicityUniqueness.Spec
