import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.Representations
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-! Specifications of endpointwise relations, their generated ideals, and admissibility. -/

open scoped BigOperators

universe u v w d

namespace RM03.QuiverRelationSpec

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]

/-- A relation has finitely many coefficients on paths with prescribed endpoints. -/
abbrev Coefficients (k : Type w) [Zero k] {Q : Type u} [Quiver.{v} Q] (i j : Q) :=
  Quiver.Path i j →₀ k

/-- A relation together with its endpoints, for forming sets of generators. -/
def Bundled (k : Type w) [Zero k] (Q : Type u) [Quiver.{v} Q] :=
  Σ i : Q, Σ j : Q, Coefficients k i j

noncomputable def inclusion (i j : Q) :
    Coefficients k i j →ₗ[k] PathAlgebraSpec.Carrier k Q :=
  Finsupp.linearCombination k (fun p : Quiver.Path i j => PathAlgebraSpec.ofPath k Q (Path.ofPath p))

noncomputable def evaluate (F : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q) (i j : Q) :
    Coefficients k i j →ₗ[k]
      (QuiverRepresentationSpec.vertex F i →ₗ[k] QuiverRepresentationSpec.vertex F j) :=
  Finsupp.linearCombination k (fun p : Quiver.Path i j => QuiverRepresentationSpec.mapPath F p)

def satisfies (F : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q) {i j : Q}
    (r : Coefficients k i j) : Prop :=
  evaluate F i j r = 0

/-- The two-sided ideal type can be specified using the additive group and bilinear product
alone. This structure is the reduct of the path algebra ring structure. -/
@[instance_reducible]
noncomputable def nonUnitalNonAssocRing (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] :
    NonUnitalNonAssocRing (PathAlgebraSpec.Carrier k Q) where
  __ := (inferInstance : AddCommGroup (PathAlgebraSpec.Carrier k Q))
  __ := (inferInstance : Mul (PathAlgebraSpec.Carrier k Q))
  zero_mul x := ((PathAlgebraSpec.mul k Q).flip x).map_zero
  mul_zero x := (PathAlgebraSpec.mul k Q x).map_zero
  left_distrib x y z := (PathAlgebraSpec.mul k Q x).map_add y z
  right_distrib x y z := ((PathAlgebraSpec.mul k Q).flip z).map_add x y

attribute [local instance] nonUnitalNonAssocRing

noncomputable def toElement (r : Bundled k Q) : PathAlgebraSpec.Carrier k Q :=
  inclusion r.1 r.2.1 r.2.2

noncomputable def generatedIdeal (S : Set (Bundled k Q)) :
    TwoSidedIdeal (PathAlgebraSpec.Carrier k Q) :=
  TwoSidedIdeal.span (toElement '' S)

noncomputable def arrowIdeal (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] :
    TwoSidedIdeal (PathAlgebraSpec.Carrier k Q) :=
  TwoSidedIdeal.span (Set.range fun a : Arrow Q => PathAlgebraSpec.arrow k Q a.2.2)

/-- The ideal obtained by iterating the two-sided span of products, with exponent zero
giving the whole algebra. -/
noncomputable def spanProductPowers {R : Type u} [NonUnitalNonAssocRing R]
    (I : TwoSidedIdeal R) : ℕ → TwoSidedIdeal R
  | 0 => ⊤
  | n + 1 => TwoSidedIdeal.span {z | ∃ x ∈ spanProductPowers I n, ∃ y ∈ I, x * y = z}

/-- Agreement with ordinary ideal powers when the full unital ring is available. -/
def OrdinaryPowers : Prop :=
  ∀ {R : Type u} [Ring R] (I : TwoSidedIdeal R) (n : ℕ),
    (spanProductPowers I n).asIdeal = I.asIdeal ^ n

noncomputable abbrev idealPower (I : TwoSidedIdeal (PathAlgebraSpec.Carrier k Q)) :=
  spanProductPowers I

def admissible (I : TwoSidedIdeal (PathAlgebraSpec.Carrier k Q)) : Prop :=
  ∃ m : ℤ, 2 ≤ m ∧ idealPower (arrowIdeal k Q) m.toNat ≤ I ∧ I ≤ idealPower (arrowIdeal k Q) 2

section Signatures

set_option linter.checkUnivs false

abbrev CoefficientsSignature :=
  ∀ (k : Type w) [Zero k] {Q : Type u} [Quiver.{v} Q], Q → Q → Type (max u v w)

abbrev BundledSignature :=
  ∀ (k : Type w) [Zero k] (Q : Type u) [Quiver.{v} Q], Type (max u v w)

abbrev InclusionSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] (i j : Q),
    Coefficients k i j →ₗ[k] PathAlgebraSpec.Carrier k Q

abbrev EvaluateSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
    (F : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q) (i j : Q),
    Coefficients k i j →ₗ[k]
      (QuiverRepresentationSpec.vertex F i →ₗ[k] QuiverRepresentationSpec.vertex F j)

abbrev SatisfiesSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
    (_F : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q) {i j : Q}, Coefficients k i j → Prop

abbrev ToElementSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q],
    Bundled k Q → PathAlgebraSpec.Carrier k Q

abbrev GeneratedIdealSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q],
    Set (Bundled k Q) → TwoSidedIdeal (PathAlgebraSpec.Carrier k Q)

noncomputable def generatedIdealValue : GeneratedIdealSignature :=
  fun {_ _} _ _ _ => generatedIdeal

abbrev ArrowIdealSignature :=
  ∀ (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Fintype Q],
    TwoSidedIdeal (PathAlgebraSpec.Carrier k Q)

noncomputable def arrowIdealValue : ArrowIdealSignature :=
  fun k Q _ _ _ => arrowIdeal k Q

abbrev IdealPowerSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q],
    TwoSidedIdeal (PathAlgebraSpec.Carrier k Q) → ℕ → TwoSidedIdeal (PathAlgebraSpec.Carrier k Q)

noncomputable def idealPowerValue : IdealPowerSignature :=
  fun {_ _} _ _ _ => idealPower

abbrev AdmissibleSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q],
    TwoSidedIdeal (PathAlgebraSpec.Carrier k Q) → Prop

def admissibleValue : AdmissibleSignature :=
  fun {_ _} _ _ _ => admissible

end Signatures

def InclusionInjective : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] (i j : Q),
    Function.Injective (inclusion (k := k) i j)

def InclusionRange : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] (i j : Q),
    LinearMap.range (inclusion (k := k) i j) = PathAlgebraSpec.corner k Q i j

def VertexDecomposition : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]
    (x : PathAlgebraSpec.Carrier k Q),
    (∑ i : Q, ∑ j : Q, PathAlgebraSpec.vertex k Q j * x * PathAlgebraSpec.vertex k Q i) = x

def LeastGeneratedIdeal : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]
    (S : Set (Bundled k Q)) (I : TwoSidedIdeal (PathAlgebraSpec.Carrier k Q)),
    generatedIdeal S ≤ I ↔ ∀ r ∈ S, toElement r ∈ I

def GeneratedByRelations : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]
    (I : TwoSidedIdeal (PathAlgebraSpec.Carrier k Q)),
    generatedIdeal {r : Bundled k Q | toElement r ∈ I} = I

end RM03.QuiverRelationSpec
