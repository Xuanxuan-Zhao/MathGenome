import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.ShortDirections
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.KrullDimension.Polynomial

/-! Trace-one zero-adjoint elements of the split Albert model, their standard
principal opens, and the split ordered-frame incidence. -/

namespace LinearAlgebraicGroups.Albert.IdempotentSpecification

open _root_.LinearAlgebraicGroups.Composition (Zorn)
open Composition.ZornSpecification (norm)
open Composition.AdjointSpecification (conjugate)
open HermitianSpecification (cyclicNext cyclicPrev)
open CubicSpecification (cubicAdjoint linearTrace cubicUnit)
open FrameSpecification (frameAxis)
open TrialitySpecification (Model modelOp mapModel)
open scoped BigOperators

universe u v w

section Points

variable {R : Type u} [CommRing R]

abbrev adjoint : Model R → Model R := cubicAdjoint (norm R) (fun _ => 1)

abbrev trace : Model R → R := linearTrace (norm R) (fun _ => 1)

/-- Equations of the first idempotent, evaluated in any scalar algebra. -/
def IsRankOneIdempotent (x : Model R) : Prop := trace x = 1 ∧ adjoint x = 0

abbrev IdempotentPoint (R : Type u) [CommRing R] :=
  {x : Model R // IsRankOneIdempotent x}

structure ChartPoint (R : Type u) [CommRing R] where
  diagonal : Rˣ
  nextBlock : Zorn R
  prevBlock : Zorn R
  equation : (diagonal : R) ^ 2 - (diagonal : R) +
    norm R nextBlock + norm R prevBlock = 0

/-- The coordinate reconstruction on the principal open of the indicated diagonal. -/
def chartCoordinates (i : Fin 3) (a : Rˣ) (c d : Zorn R) : Model R :=
  (fun s => if s = i then (a : R) else if s = cyclicNext i then
      (↑a⁻¹ : R) * norm R d else (↑a⁻¹ : R) * norm R c,
    fun s => if s = i then (↑a⁻¹ : R) • conjugate (norm R) (c * d)
      else if s = cyclicNext i then c else d)

def ChartEquationsType : Prop :=
  ∀ (R : Type u) [CommRing R] (i : Fin 3) (a : Rˣ) (x : Model R),
    x.1 i = (a : R) →
    (IsRankOneIdempotent x ↔
      x = chartCoordinates i a (x.2 (cyclicNext i)) (x.2 (cyclicPrev i)) ∧
      (a : R) ^ 2 - (a : R) + norm R (x.2 (cyclicNext i)) +
        norm R (x.2 (cyclicPrev i)) = 0)

def ChartEquivalenceType : Prop :=
  ∀ (R : Type u) [CommRing R] (i : Fin 3),
    ∃ e : ChartPoint R ≃ {x : Model R // IsRankOneIdempotent x ∧ IsUnit (x.1 i)},
      ∀ p, (e p).val = chartCoordinates i p.diagonal p.nextBlock p.prevBlock

def IdempotentsType : Prop :=
  ∀ (R : Type u) [CommRing R] (x : Model R),
    IsRankOneIdempotent x → modelOp x cubicUnit = x

/-- The second standard-axis corner, with diagonal coordinates (0,a,1-a). -/
def secondCoordinates (a : R) (c : Zorn R) : Model R :=
  (fun i => if i = 0 then 0 else if i = 1 then a else 1 - a, Pi.single 0 c)

/-- The frame is determined by its first two members. The projector condition
means that the second member is in the Peirce-zero space of the first. -/
def IsFramePair (x y : Model R) : Prop :=
  IsRankOneIdempotent x ∧ IsRankOneIdempotent y ∧ modelOp (cubicUnit - x) y = y

abbrev FramePairPoint (R : Type u) [CommRing R] :=
  {p : Model R × Model R // IsFramePair p.1 p.2}

/-- Preservation equations for points of the split quadratic automorphism group. -/
def IsSplitAutomorphism (g : Model R ≃ₗ[R] Model R) : Prop :=
  g cubicUnit = cubicUnit ∧ ∀ x y, g (modelOp x y) = modelOp (g x) (g y)

/-- The evaluation maps land in the incidence schemes over every test ring. -/
def OrbitValuesType : Prop :=
  ∀ (R : Type u) [CommRing R] (g : Model R ≃ₗ[R] Model R), IsSplitAutomorphism g →
    (∀ x, IsRankOneIdempotent (g x) ↔ IsRankOneIdempotent x) ∧
    (∀ x y, IsFramePair (g x) (g y) ↔ IsFramePair x y) ∧
    IsFramePair (g (frameAxis 0)) (g (frameAxis 1))

def SecondEquationsType : Prop :=
  ∀ (R : Type u) [CommRing R] (x : Model R),
    IsFramePair (frameAxis 0) x ↔
      x = secondCoordinates (x.1 1) (x.2 0) ∧
      x.1 1 * (1 - x.1 1) = norm R (x.2 0)

def SecondEquivalenceType : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ e : {p : R × Zorn R // p.1 * (1 - p.1) = norm R p.2} ≃
        {x : Model R // IsFramePair (frameAxis 0) x},
      ∀ p, (e p).val = secondCoordinates p.val.1 p.val.2

end Points

section Differential

open _root_.Specs.LinearAlgebraicGroups.Albert (QuadraticJordan)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (infinitesimal)
open TrialitySpecification (modelBaseChange)
open ShortDirectionSpecification (splitDerivations frameEvaluation)
open scoped TensorProduct DualNumber

/-- Reduction of an Albert vector over the dual numbers. -/
def reduceModel (k : Type u) [CommRing k] : Model (DualNumber k) → Model k :=
  mapModel (TrivSqZeroExt.fstHom k k k).toRingHom

/-- Evaluation of the automorphism represented by the tangent vector at a frame axis. -/
noncomputable def axisJet {k : Type u} [CommRing k]
    (D : Module.End k (Model k)) (i : Fin 3) : Model (DualNumber k) :=
  modelBaseChange k (DualNumber k) (infinitesimal D (1 ⊗ₜ[k] frameAxis i))

def FirstOrbitDifferentialType : Prop :=
  ∀ (k : Type u) [Field k] (J : QuadraticJordan k (Model k)),
    J.unit = cubicUnit → (∀ x y, J.groundOp x y = modelOp x y) →
    ∀ x : IdempotentPoint (DualNumber k), reduceModel k x.val = frameAxis 0 →
      ∃ D : splitDerivations J, axisJet D.val 0 = x.val

def SecondOrbitDifferentialType : Prop :=
  ∀ (k : Type u) [Field k] (J : QuadraticJordan k (Model k)),
    J.unit = cubicUnit → (∀ x y, J.groundOp x y = modelOp x y) →
    ∀ x : {x : Model (DualNumber k) // IsFramePair (frameAxis 0) x},
      reduceModel k x.val = frameAxis 1 →
        ∃ D : splitDerivations J, D.val (frameAxis 0) = 0 ∧ axisJet D.val 1 = x.val

def OrderedFrameDifferentialType : Prop :=
  ∀ (k : Type u) [Field k] (J : QuadraticJordan k (Model k)),
    J.unit = cubicUnit → (∀ x y, J.groundOp x y = modelOp x y) →
    (∀ p : FramePairPoint (DualNumber k),
      reduceModel k p.val.1 = frameAxis 0 → reduceModel k p.val.2 = frameAxis 1 →
      ∃ D : splitDerivations J, axisJet D.val 0 = p.val.1 ∧ axisJet D.val 1 = p.val.2) ∧
    Function.Surjective ((frameEvaluation k).domRestrict (splitDerivations J)) ∧
    Module.finrank k (Fin 3 → Zorn k) = 24

end Differential

section Schemes

open AlgebraicGeometry CategoryTheory MvPolynomial

variable (k : Type u) [CommRing k]

/-- Signed Zorn coordinates: the norm is a sum of products of the two columns. -/
abbrev ZornIndex := Option (Fin 3) ⊕ Option (Fin 3)

abbrev CoordinateIndex := Fin 3 ⊕ (Fin 3 × ZornIndex)

def modelOfVariables {S : Type v} [CommRing S] (z : CoordinateIndex → S) : Model S :=
  (fun i => z (.inl i), fun i => (Zorn.pairedFunctions S).symm (fun j => z (.inr (i, j))))

def modelVariables {S : Type v} [CommRing S] (x : Model S) : CoordinateIndex → S
  | .inl i => x.1 i
  | .inr (i, j) => Zorn.pairedFunctions S (x.2 i) j

noncomputable def genericIdempotent : Model (MvPolynomial CoordinateIndex k) :=
  modelOfVariables X

/-- The defining ideal of the zero-adjoint, trace-one affine scheme. -/
noncomputable def idempotentIdeal : Ideal (MvPolynomial CoordinateIndex k) :=
  Ideal.span (insert (trace (genericIdempotent k) - 1)
    (Set.range fun i => (adjoint (genericIdempotent k)).1 i) ∪
    Set.range fun (ij : Fin 3 × ZornIndex) =>
      Zorn.pairedFunctions _ ((adjoint (genericIdempotent k)).2 ij.1) ij.2)

abbrev IdempotentRing := MvPolynomial CoordinateIndex k ⧸ idempotentIdeal k

noncomputable def diagonalCoordinate (i : Fin 3) : IdempotentRing k :=
  Ideal.Quotient.mk _ (X (.inl i))

noncomputable abbrev firstScheme : Scheme := Spec (CommRingCat.of (IdempotentRing k))

noncomputable def firstStructure : firstScheme k ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (IdempotentRing k)))

/-- One scalar variable and two variables for each hyperbolic pair. -/
abbrev QuadricIndex (ι : Type v) := Option (ι × Bool)

noncomputable def quadricEquation (ι : Type v) [Fintype ι] :
    MvPolynomial (QuadricIndex ι) k :=
  X none ^ 2 - X none + ∑ j : ι, X (some (j, false)) * X (some (j, true))

abbrev QuadricRing (ι : Type v) [Fintype ι] :=
  MvPolynomial (QuadricIndex ι) k ⧸ Ideal.span {quadricEquation k ι}

noncomputable def quadricScalar (ι : Type v) [Fintype ι] : QuadricRing k ι :=
  Ideal.Quotient.mk _ (X none)

abbrev SecondRing := QuadricRing k (Option (Fin 3))

abbrev ChartRing :=
  Localization.Away (quadricScalar k (Bool × Option (Fin 3)))

noncomputable abbrev secondScheme : Scheme := Spec (CommRingCat.of (SecondRing k))

noncomputable def secondStructure : secondScheme k ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (SecondRing k)))

noncomputable def idempotentOfHom {S : Type v} [CommRing S] [Algebra k S]
    (f : IdempotentRing k →ₐ[k] S) : Model S :=
  modelOfVariables fun j => f (Ideal.Quotient.mk _ (X j))

/-- The explicit affine presentation represents the equations over every test algebra. -/
def FirstRepresentationType : Prop :=
  ∀ (k : Type u) [CommRing k] (S : Type v) [CommRing S] [Algebra k S],
    ∃ e : (IdempotentRing k →ₐ[k] S) ≃ IdempotentPoint S,
      ∀ f, (e f).val = idempotentOfHom k f

noncomputable def quadricOfHom (ι : Type v) [Fintype ι]
    {S : Type w} [CommRing S] [Algebra k S] (f : QuadricRing k ι →ₐ[k] S) :
    QuadricIndex ι → S :=
  fun j => f (Ideal.Quotient.mk _ (X j))

/-- Convert the two signed hyperbolic columns to the octonion block. -/
def octonionOfPairs {S : Type v} [CommRing S] (z : Option (Fin 3) × Bool → S) : Zorn S :=
  (Zorn.pairedFunctions S).symm (Sum.elim (fun j => z (j, false)) (fun j => z (j, true)))

def SecondRepresentationType : Prop :=
  ∀ (k : Type u) [CommRing k] (S : Type v) [CommRing S] [Algebra k S],
    ∃ e : (SecondRing k →ₐ[k] S) ≃ {x : Model S // IsFramePair (frameAxis 0) x},
      ∀ f, (e f).val =
        secondCoordinates (quadricOfHom k _ f none)
          (octonionOfPairs fun j => quadricOfHom k _ f (some j))

def ChartRingsType : Prop :=
  ∀ (k : Type u) [CommRing k] (i : Fin 3),
    Nonempty (Localization.Away (diagonalCoordinate k i) ≃ₐ[k] ChartRing k)

def ChartCoverType : Prop :=
  ∀ (k : Type u) [CommRing k],
    (⨆ i : Fin 3, PrimeSpectrum.basicOpen (diagonalCoordinate k i)) = ⊤

def FirstGeometryType : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k],
    Smooth (firstStructure k) ∧ IrreducibleSpace (firstScheme k) ∧
    ringKrullDim (IdempotentRing k) = 16

def SecondGeometryType : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k],
    Smooth (secondStructure k) ∧ IrreducibleSpace (secondScheme k) ∧
    ringKrullDim (SecondRing k) = 8

/-- The two frame entries use disjoint copies of the Albert coordinates. -/
abbrev FrameIndex := Bool × CoordinateIndex

abbrev FrameEquationIndex := (Bool × (Unit ⊕ CoordinateIndex)) ⊕ CoordinateIndex

def frameEquation {S : Type v} [CommRing S] (x : Bool → Model S) : FrameEquationIndex → S
  | .inl (b, .inl _) => trace (x b) - 1
  | .inl (b, .inr j) => modelVariables (adjoint (x b)) j
  | .inr j => modelVariables (modelOp (cubicUnit - x false) (x true) - x true) j

noncomputable def genericFrame (b : Bool) : Model (MvPolynomial FrameIndex k) :=
  modelOfVariables fun j => X (b, j)

/-- The two trace and adjoint equations together with the Peirce projector equation. -/
noncomputable def frameIdeal : Ideal (MvPolynomial FrameIndex k) :=
  Ideal.span (Set.range (frameEquation (genericFrame k)))

abbrev FrameRing := MvPolynomial FrameIndex k ⧸ frameIdeal k

noncomputable abbrev frameScheme : Scheme := Spec (CommRingCat.of (FrameRing k))

noncomputable def frameOfHom {S : Type v} [CommRing S] [Algebra k S]
    (f : FrameRing k →ₐ[k] S) : Model S × Model S :=
  (modelOfVariables fun j => f (Ideal.Quotient.mk _ (X (false, j))),
   modelOfVariables fun j => f (Ideal.Quotient.mk _ (X (true, j))))

def FrameRepresentationType : Prop :=
  ∀ (k : Type u) [CommRing k] (S : Type v) [CommRing S] [Algebra k S],
    ∃ e : (FrameRing k →ₐ[k] S) ≃ FramePairPoint S,
      ∀ f, (e f).val = frameOfHom k f

/-- The image of the ordered standard frame under the split automorphism
group on geometric points, viewed as a subset of the affine incidence scheme. -/
def frameOrbit : Set (PrimeSpectrum (FrameRing k)) :=
  {p | ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (f : FrameRing k →ₐ[k] K)
        (g : Model K ≃ₗ[K] Model K),
    IsSplitAutomorphism g ∧
    frameOfHom k f = (g (frameAxis 0), g (frameAxis 1)) ∧
    RingHom.ker f.toRingHom = p.asIdeal}

def OrderedFrameOpenOrbitType : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k], IsOpen (frameOrbit k) ∧ (frameOrbit k).Nonempty

end Schemes

end LinearAlgebraicGroups.Albert.IdempotentSpecification
