import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.ZornModel
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Smooth.Basic

namespace LinearAlgebraicGroups.Composition.PeirceSpecification

open scoped Matrix TensorProduct

universe u v w z
open Specification

set_option linter.checkUnivs false
variable {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]

/-- The points of the trace-one, norm-zero quadric, evaluated in the given scalar ring. -/
def QuadricPoint (n : QuadraticForm R C) :=
  {e : C // AdjointSpecification.trace n e = 1 ∧ n e = 0}

def quadricPointType :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C],
    QuadraticForm R C → Type v

variable {n : QuadraticForm R C}

def complement (e : QuadricPoint n) : C := 1 - e.val

variable [IsScalarTower R C C] [SMulCommClass R C C]

/-- One simultaneous eigenspace of multiplication on both sides by the quadric point. -/
def corner (e : QuadricPoint n) (i j : R) : Submodule R C :=
  ((LinearMap.mul R C e.val - i • LinearMap.id).ker) ⊓
  (((LinearMap.mul R C).flip e.val - j • LinearMap.id).ker)

def cornerType :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    {n : QuadraticForm R C} [IsScalarTower R C C] [SMulCommClass R C C],
    QuadricPoint n → R → R → Submodule R C

/-- The pairing of the upper and lower Peirce summands with the Zorn sign convention. -/
def pairing (e : QuadricPoint n) : corner e 1 0 →ₗ[R] corner e 0 1 →ₗ[R] R :=
  (-n.polarBilin).compl₁₂ (corner e 1 0).subtype (corner e 0 1).subtype

def pairingType :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    {n : QuadraticForm R C} [IsScalarTower R C C] [SMulCommClass R C C]
    (e : QuadricPoint n), corner e 1 0 →ₗ[R] corner e 0 1 →ₗ[R] R

def complementaryIdempotents : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C},
    OctonionNormConditions n → ∀ (e : QuadricPoint n),
      AdjointSpecification.trace n (complement e) = 1 ∧ n (complement e) = 0 ∧
      e.val * e.val = e.val ∧ complement e * complement e = complement e ∧
      e.val * complement e = 0 ∧ complement e * e.val = 0 ∧ e.val + complement e = 1

/-- The two defining differentials have a right inverse at every point of the quadric. -/
def independentDifferentials : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C},
    OctonionNormConditions n → ∀ (e : QuadricPoint n),
      Function.Surjective ((AdjointSpecification.trace n).prod (n.polarBilin e.val))

def projections : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C},
    OctonionNormConditions n → ∀ (e : QuadricPoint n),
      let L := LinearMap.mul R C e.val
      let P := (LinearMap.mul R C).flip e.val
      L.comp L = L ∧ P.comp P = P ∧ L.comp P = P.comp L

def scalarCorners : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C},
    OctonionNormConditions n → ∀ (e : QuadricPoint n),
      corner e 1 1 = R ∙ e.val ∧ corner e 0 0 = R ∙ complement e

def offDiagonalProducts : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C},
    OctonionNormConditions n → ∀ (e : QuadricPoint n),
      (∀ x y : corner e 1 0, x.val * y.val ∈ corner e 0 1) ∧
      (∀ x y : corner e 0 1, x.val * y.val ∈ corner e 1 0) ∧
      (∀ (x : corner e 1 0) (y : corner e 0 1),
        x.val * y.val = pairing e x y • e.val ∧
        y.val * x.val = pairing e x y • complement e)

def directDecomposition : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C},
    OctonionNormConditions n → ∀ (e : QuadricPoint n),
      ∃ d : (R × corner e 1 0 × corner e 0 1 × R) ≃ₗ[R] C,
        ∀ x, d x = x.1 • e.val + x.2.1.val + x.2.2.1.val + x.2.2.2 • complement e

def perfectPairing : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C},
    OctonionNormConditions n → ∀ (e : QuadricPoint n), (pairing e).IsPerfPair

def pointsOfIsotropicNorm : Prop :=
  ∀ {R : Type u} {C : Type v} [Field R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C},
    OctonionNormConditions n → Specification.isotropic n → Nonempty (QuadricPoint n)

def pointsOverAlgebraicallyClosed : Prop :=
  ∀ {R : Type u} {C : Type v} [Field R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C},
    OctonionNormConditions n → ∀ [IsAlgClosed R], Nonempty (QuadricPoint n)


def projectiveCorners : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C},
    OctonionNormConditions n → ∀ (e : QuadricPoint n),
      Module.Finite R (corner e 1 0) ∧ Module.Projective R (corner e 1 0) ∧
      Module.Finite R (corner e 0 1) ∧ Module.Projective R (corner e 0 1)

def cornerRank : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C},
    OctonionNormConditions n → ∀ (e : QuadricPoint n) (p : PrimeSpectrum R),
      Module.rankAtStalk (corner e 1 0) p = 3 ∧ Module.rankAtStalk (corner e 0 1) p = 3

/-- The two eigenvalues of an idempotent acting as a projection. -/
def eigenvalue (R : Type u) [CommRing R] : Bool → R
  | true => 1
  | false => 0

def baseChangeCorners : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C}
    (h : OctonionNormConditions n) (e : QuadricPoint n)
    (S : Type w) [CommRing S] [Algebra R S],
    letI := h.projective
    ∃ eS : QuadricPoint (normBaseChange S n),
      eS.val = (1 : S) ⊗ₜ[R] e.val ∧
      ∀ i j : Bool,
        let U := corner e (eigenvalue _ i) (eigenvalue _ j)
        let US := corner eS (eigenvalue _ i) (eigenvalue _ j)
        ∃ E : (S ⊗[R] U) ≃ₗ[S] US,
          ∀ s (x : U), (E (s ⊗ₜ[R] x)).val = s ⊗ₜ[R] x.val

def baseChangePairing : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C}
    (h : OctonionNormConditions n) (e : QuadricPoint n)
    (S : Type w) [CommRing S] [Algebra R S],
    letI := h.projective
    ∃ e' : QuadricPoint (normBaseChange S n),
      e'.val = (1 : S) ⊗ₜ[R] e.val ∧
      ∃ (E : (S ⊗[R] corner e 1 0) ≃ₗ[S] corner e' 1 0)
        (F : (S ⊗[R] corner e 0 1) ≃ₗ[S] corner e' 0 1),
        (∀ s x, (E (s ⊗ₜ[R] x)).val = s ⊗ₜ[R] x.val) ∧
        (∀ t y, (F (t ⊗ₜ[R] y)).val = t ⊗ₜ[R] y.val) ∧
        ∀ s t x y, pairing e' (E (s ⊗ₜ[R] x)) (F (t ⊗ₜ[R] y)) =
          s * t * algebraMap R S (pairing e x y)

def normInCorners : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C},
    OctonionNormConditions n → ∀ (e : QuadricPoint n) (a b : R)
      (x : corner e 1 0) (y : corner e 0 1),
      n (a • e.val + x.val + y.val + b • complement e) = a * b - pairing e x y

def crossPairingIdentity : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C},
    OctonionNormConditions n → ∀ (e : QuadricPoint n)
      (x x' : corner e 1 0) (y y' : corner e 0 1),
      ∃ (u : corner e 1 0) (v : corner e 0 1),
        u.val = y.val * y'.val ∧ v.val = x.val * x'.val ∧
        pairing e u v = pairing e x y' * pairing e x' y - pairing e x y * pairing e x' y'

/-- The scalar triple product defining the upper and lower orientations. -/
def volume (U : Submodule R C) (x : Fin 3 → U) : R :=
  AdjointSpecification.trace n ((x 0).val * ((x 1).val * (x 2).val))

def alternatingVolume : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C},
    OctonionNormConditions n → ∀ (e : QuadricPoint n),
      (∃ A : (↥(corner e 1 0)) [⋀^Fin 3]→ₗ[R] R, ∀ x, A x = volume (n := n) _ x) ∧
      (∃ A : (↥(corner e 0 1)) [⋀^Fin 3]→ₗ[R] R, ∀ x, A x = volume (n := n) _ x)

/-- An ordered basis of the upper corner with volume equal to one. -/
def OrientedBasis (e : QuadricPoint n) :=
  {b : Module.Basis (Fin 3) R (corner e 1 0) // volume (n := n) _ b = 1}

/-- A norm-preserving unital isomorphism from the coordinate Zorn algebra. -/
structure ZornIsomorphism (n : QuadraticForm R C) where
  toLinearEquiv : Zorn R ≃ₗ[R] C
  map_one : toLinearEquiv 1 = 1
  map_mul : ∀ x y, toLinearEquiv (x * y) = toLinearEquiv x * toLinearEquiv y
  map_norm : ∀ x, n (toLinearEquiv x) = ZornSpecification.norm R x

def orientedBasisExists : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C},
    OctonionNormConditions n → ∀ (e : QuadricPoint n),
      Nonempty (Module.Basis (Fin 3) R (corner e 1 0)) → Nonempty (OrientedBasis e)

def isotropicFieldSplit : Prop :=
  ∀ {R : Type u} {C : Type v} [Field R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C},
    OctonionNormConditions n → Specification.isotropic n → Nonempty (ZornIsomorphism n)

/-- The map on scalar-extended vectors induced by a morphism of test algebras. -/
def tensorMap {M : Type v} [AddCommGroup M] [Module R M]
    {S : Type w} [CommRing S] [Algebra R S] {T : Type z} [CommRing T] [Algebra R T]
    (f : S →ₐ[R] T) : (S ⊗[R] M) →ₗ[R] (T ⊗[R] M) :=
  f.toLinearMap.rTensor M

/-- A universal point represents the quadric if evaluating it gives a unique ring map for
each trace-one, norm-zero vector over every test algebra. -/
def RepresentsQuadric [Module.Projective R C]
    {A : Type z} [CommRing A] [Algebra R A]
    (e : QuadricPoint (normBaseChange A n)) : Prop :=
  ∀ (S : Type w) [CommRing S] [Algebra R S],
    Function.Injective (fun f : A →ₐ[R] S => tensorMap (M := C) f e.val) ∧
      ∀ x : QuadricPoint (normBaseChange S n),
        ∃ f : A →ₐ[R] S, tensorMap f e.val = x.val

/-- The trace-one norm-zero functor is represented by a smooth, surjective affine scheme. -/
def quadricScheme : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C}
    (h : OctonionNormConditions n),
    letI := h.projective
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A)
      (e : QuadricPoint (normBaseChange A n)),
      RepresentsQuadric.{u, v, w, u} e ∧ Algebra.Smooth R A ∧
        Function.Surjective (PrimeSpectrum.comap (algebraMap R A)) ∧ Module.FaithfullyFlat R A

/-- Principal opens on which the upper corner of a quadric point has a volume-one basis. -/
def localOrientedBases : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C}
    (h : OctonionNormConditions n) (A : Type w) [CommRing A] [Algebra R A],
    letI := h.projective
    ∀ (e : QuadricPoint (normBaseChange A n)) (p : PrimeSpectrum A),
      ∃ r : A, r ∉ p.asIdeal ∧
        ∃ e' : QuadricPoint (normBaseChange (Localization.Away r) n),
          e'.val = tensorMap (IsScalarTower.toAlgHom R A (Localization.Away r)) e.val ∧
            Nonempty (OrientedBasis e')

def faithfullyFlatSplit : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C}
    (h : OctonionNormConditions n),
    letI := h.projective
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Algebra.Smooth R S ∧ Module.FaithfullyFlat R S ∧ Nonempty (ZornIsomorphism (normBaseChange S n))

abbrev SplitVars := Option (Option (Fin 5))

def scalarVar : SplitVars := none
def upperVar : Fin 3 → SplitVars := ![some (some 0), some (some 1), some (some 2)]
def lowerVar : Fin 3 → SplitVars := ![some none, some (some 3), some (some 4)]

/-- After eliminating the second scalar coordinate by the trace equation, the split quadric
has one equation in seven variables. -/
noncomputable def splitEquation (R : Type u) [CommRing R] : MvPolynomial SplitVars R :=
  MvPolynomial.X scalarVar ^ 2 - MvPolynomial.X scalarVar +
    ∑ i, MvPolynomial.X (upperVar i) * MvPolynomial.X (lowerVar i)

abbrev SplitQuadricRing (R : Type u) [CommRing R] :=
  MvPolynomial SplitVars R ⧸ Ideal.span {splitEquation R}

/-- The split quadric has geometrically integral fibers of dimension six. -/
def splitQuadricFibers : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type w) [Field K] [Algebra R K],
    IsDomain (K ⊗[R] SplitQuadricRing R) ∧ ringKrullDim (K ⊗[R] SplitQuadricRing R) = 6

/-- The evaluation of a norm-preserving Zorn isomorphism on the first scalar idempotent
and on the three standard upper columns. -/
def zornFrameEquivalence : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C},
    OctonionNormConditions n →
    ∃ E : ZornIsomorphism n ≃ (Σ e : QuadricPoint n, OrientedBasis e),
      ∀ F,
        (E F).1.val = F.toLinearEquiv (ZornSpecification.first R) ∧
        ∀ i : Fin 3, ((E F).2.val i).val = F.toLinearEquiv (Zorn.ofCoordinates (0, Pi.single i 1, 0, 0))

/-- The unital algebra automorphisms of the split octonions over a test ring. -/
def SplitAutomorphism (R : Type u) [CommRing R] :=
  {F : Zorn R ≃ₗ[R] Zorn R // F 1 = 1 ∧ ∀ x y : Zorn R, F (x * y) = F x * F y}

def splitAutomorphismFrameEquivalence : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ E : SplitAutomorphism R ≃ (Σ e : QuadricPoint (ZornSpecification.norm R), OrientedBasis e),
      ∀ F,
        (E F).1.val = F.val (ZornSpecification.first R) ∧
        ∀ i : Fin 3, ((E F).2.val i).val = F.val (Zorn.ofCoordinates (0, Pi.single i 1, 0, 0))

/-- On each fiber the right action is the determinant-one change of oriented basis. -/
def orientedFrameAction : Prop :=
  ∀ {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
    [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C},
    OctonionNormConditions n → ∀ (e : QuadricPoint n),
      ∃ act : OrientedBasis e → Matrix.SpecialLinearGroup (Fin 3) R → OrientedBasis e,
        (∀ b g j, (act b g).val j = ∑ i, g i j • b.val i) ∧
        (∀ b, act b 1 = b ∧ Function.Bijective (act b)) ∧
        ∀ b g h, act (act b g) h = act b (g * h)

def RepresentsSplitQuadric (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] : Prop :=
  ∃ e : QuadricPoint (normBaseChange A (ZornSpecification.norm R)),
    RepresentsQuadric.{u, u, w, u} e ∧ Algebra.Smooth R A

/-- The explicit split hypersurface represents the trace-one norm-zero functor. -/
def splitQuadricScheme : Prop :=
  ∀ (R : Type u) [CommRing R], RepresentsSplitQuadric.{u, w} R (SplitQuadricRing R)

/-- Principal-open trivializations of the evaluation map. The upper columns give the
trivializations, and the displayed formula is compatible with scalar extension. -/
def splitFrameCharts : Prop :=
  ∀ (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (e : QuadricPoint (normBaseChange A (ZornSpecification.norm R))) (p : PrimeSpectrum A),
    ∃ r : A, r ∉ p.asIdeal ∧
      ∃ b : Fin 3 → Zorn (Localization.Away r),
        ∀ (S : Type w) [CommRing S] [Algebra R S] (f : Localization.Away r →ₐ[R] S),
          let x := ZornSpecification.baseChange R S
            (tensorMap (f.comp (IsScalarTower.toAlgHom R A (Localization.Away r))) e.val)
          ∃ E : Matrix.SpecialLinearGroup (Fin 3) S ≃
            {F : SplitAutomorphism S // F.val (ZornSpecification.first S) = x},
            ∀ g i, (E g).val.val (Zorn.ofCoordinates (0, Pi.single i 1, 0, 0)) =
              ∑ j, g j i • ZornSpecification.mapCoordinates f.toRingHom (b j)

/-- Affine representation of the split automorphism functor and its idempotent evaluation map. -/
def SplitEvaluationOver (R A D : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [CommRing D] [Algebra R D] (ρ : A →ₐ[R] D) : Prop :=
  ∃ e : QuadricPoint (normBaseChange A (ZornSpecification.norm R)),
    RepresentsQuadric.{u, u, w, u} e ∧
      ∃ E : ∀ (S : Type w) [CommRing S] [Algebra R S],
        (D →ₐ[R] S) ≃ SplitAutomorphism S,
        (∀ (S : Type w) [CommRing S] [Algebra R S] (f : D →ₐ[R] S),
          (E S f).val (ZornSpecification.first S) =
            ZornSpecification.baseChange R S (tensorMap (f.comp ρ) e.val)) ∧
        ∀ (S T : Type w) [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
          (f : D →ₐ[R] S) (g : S →ₐ[R] T) (x : Zorn S),
          (E T (g.comp f)).val (ZornSpecification.mapCoordinates g.toRingHom x) =
            ZornSpecification.mapCoordinates g.toRingHom ((E S f).val x)

def splitEvaluationScheme : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D)
      (ρ : SplitQuadricRing R →ₐ[R] D),
      Algebra.FinitePresentation R D ∧ SplitEvaluationOver.{u, w} R (SplitQuadricRing R) D ρ

/-- The determinant-one equation for the group acting on oriented frames. -/
noncomputable def sl3Equation (R : Type u) [CommRing R] :
    Unit → MvPolynomial (Fin 3 × Fin 3) R :=
  fun _ => (Matrix.of fun i j => MvPolynomial.X (i, j) :
    Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3 × Fin 3) R)).det - 1

abbrev SL3Ring (R : Type u) [CommRing R] :=
  MvPolynomial (Fin 3 × Fin 3) R ⧸ Ideal.span (Set.range (sl3Equation R))

def specialLinearThreeScheme : Prop :=
  ∀ (R : Type u) [CommRing R],
    Algebra.Smooth R (SL3Ring R) ∧
      ∃ E : ∀ (S : Type w) [CommRing S] [Algebra R S],
        (SL3Ring R →ₐ[R] S) ≃ Matrix.SpecialLinearGroup (Fin 3) S,
        ∀ (S T : Type w) [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
          (f : SL3Ring R →ₐ[R] S) (g : S →ₐ[R] T),
          E T (g.comp f) = Matrix.SpecialLinearGroup.map g.toRingHom (E S f)

/-- The column formula for a local frame chart gives a natural transformation on all
test algebras, with the usual base change of determinant-one matrices. -/
def splitFrameChartNaturality : Prop :=
  ∀ (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (e : QuadricPoint (normBaseChange A (ZornSpecification.norm R))) (b : Fin 3 → Zorn A)
    (F : ∀ (S : Type w) [CommRing S] [Algebra R S] (_ : A →ₐ[R] S),
      Matrix.SpecialLinearGroup (Fin 3) S → SplitAutomorphism S),
    (∀ (S : Type w) [CommRing S] [Algebra R S] (f : A →ₐ[R] S) g,
      (F S f g).val (ZornSpecification.first S) =
        ZornSpecification.baseChange R S (tensorMap f e.val)) →
    (∀ (S : Type w) [CommRing S] [Algebra R S] (f : A →ₐ[R] S) g (i : Fin 3),
      (F S f g).val (Zorn.ofCoordinates (0, Pi.single i 1, 0, 0)) =
        ∑ j, g j i • ZornSpecification.mapCoordinates f.toRingHom (b j)) →
    ∀ (S T : Type w) [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
      (f : A →ₐ[R] S) (h : S →ₐ[R] T) g (x : Zorn S),
      (F T (h.comp f) (Matrix.SpecialLinearGroup.map h.toRingHom g)).val
          (ZornSpecification.mapCoordinates h.toRingHom x) =
        ZornSpecification.mapCoordinates h.toRingHom ((F S f g).val x)

/-- The determinant-one group is the stabilizer under composition of the first idempotent. -/
def splitStabilizer : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ E : Matrix.SpecialLinearGroup (Fin 3) R ≃
      {F : SplitAutomorphism R // F.val (ZornSpecification.first R) = ZornSpecification.first R},
      ∀ g h, (E (g * h)).val.val = (E h).val.val.trans (E g).val.val

end LinearAlgebraicGroups.Composition.PeirceSpecification
