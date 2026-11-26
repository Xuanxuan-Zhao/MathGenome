import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SpinFunctor
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Fintype.Prod
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

namespace LinearAlgebraicGroups.Albert.SplitSpinSpecification

open Matrix
open scoped Matrix TensorProduct

noncomputable section

universe u

abbrev PairIndex (m : ℕ) := Fin m ⊕ Fin m

abbrev Block (m : ℕ) (R : Type*) := Matrix (Fin m) (Fin m) R

/-- In these coordinates the creation space precedes the contraction space. -/
def hyperbolicNorm {m : ℕ} {R : Type*} [CommRing R] (v : PairIndex m → R) : R :=
  (fun i => v (Sum.inl i)) ⬝ᵥ (fun i => v (Sum.inr i))

/-- A matrix is alternating when its associated bilinear form vanishes on the diagonal. -/
def IsAlternating {m : ℕ} {R : Type*} [CommRing R] (P : Block m R) : Prop :=
  ∀ x : Fin m → R, x ⬝ᵥ (P *ᵥ x) = 0

def AlternatingEntriesType : Prop :=
  ∀ (m : ℕ) (R : Type*) [CommRing R] (P : Block m R),
    IsAlternating P ↔ (∀ i, P i i = 0) ∧ (∀ i j, P i j = -P j i)

def lower {m : ℕ} {R : Type*} [CommRing R] (P : Block m R) :
    Matrix (PairIndex m) (PairIndex m) R :=
  fromBlocks 1 0 P 1

def middle {m : ℕ} {R : Type*} [CommRing R] (A : Block m R) :
    Matrix (PairIndex m) (PairIndex m) R :=
  fromBlocks A 0 0 (A⁻¹)ᵀ

def upper {m : ℕ} {R : Type*} [CommRing R] (Q : Block m R) :
    Matrix (PairIndex m) (PairIndex m) R :=
  fromBlocks 1 Q 0 1

def PreservesNorm {m : ℕ} {R : Type*} [CommRing R]
    (g : Matrix (PairIndex m) (PairIndex m) R) : Prop :=
  ∀ v, hyperbolicNorm (g *ᵥ v) = hyperbolicNorm v

def OrthogonalChartType : Prop :=
  ∀ (m : ℕ) (R : Type*) [CommRing R] (g : Matrix (PairIndex m) (PairIndex m) R),
    IsUnit g.toBlocks₁₁.det →
    (PreservesNorm g ↔
      ∃! pq : Block m R × Block m R,
        IsAlternating pq.1 ∧ IsAlternating pq.2 ∧
          g = lower pq.1 * middle g.toBlocks₁₁ * upper pq.2)

/-- The determinant equation on the middle block in the spin chart. -/
def NormOneBlock (m : ℕ) (R : Type*) [CommRing R] :=
  {p : Block m R × Rˣ // (p.2 : R) ^ 2 * p.1.det = 1}

/-- Scale coordinate row `i` by `t` and leave the remaining rows intact. -/
def scaleRow {m : ℕ} {R : Type*} [CommRing R] (i : Fin m) (t : R) (A : Block m R) :
    Block m R :=
  updateRow A i (t • A i)

def NormalizeMiddleType : Prop :=
  ∀ (m : ℕ) (R : Type*) [CommRing R] (i : Fin m),
    ∃ e : NormOneBlock m R ≃ ({A : Block m R // A.det = 1} × Rˣ),
      ∀ p, (e p).1.val = scaleRow i ((p.val.2 : R) ^ 2) p.val.1 ∧ (e p).2 = p.val.2

abbrev FreeModule (R : Type*) (m : ℕ) := Fin m → R

abbrev HyperbolicModule (R : Type*) [CommRing R] (m : ℕ) :=
  Module.Dual R (FreeModule R m) × FreeModule R m

abbrev integralForm (m : ℕ) : QuadraticForm ℤ (HyperbolicModule ℤ m) :=
  QuadraticForm.dualProd ℤ _

/-- The hyperbolic basis in creation-contraction order. -/
def hyperbolicBasis (R : Type*) [CommRing R] (m : ℕ) :
    Module.Basis (Lex (PairIndex m)) R (HyperbolicModule R m) :=
  ((Pi.basisFun R (Fin m)).dualBasis.prod (Pi.basisFun R (Fin m))).reindex
    ((Equiv.sumComm (Fin m) (Fin m)).trans toLex)

def NonreducedMuTwoType : Prop :=
  ∀ (K : Type*) [Field K], (2 : K) = 0 → ¬ IsReduced (SpinSpecification.muTwoCoordinateRing K)

def ScalarKernelType : Prop :=
  ∀ m, SpinSpecification.HasScalarSchemeKernel (integralForm m)

abbrev ScalarClifford (m : ℕ) (S : Type*) [CommRing S] [Algebra ℤ S] :=
  SpinSpecification.ScalarClifford (integralForm m) S

abbrev ExtendedModule (m : ℕ) (S : Type*) [CommRing S] [Algebra ℤ S] :=
  letI : Module ℤ S := Algebra.toModule
  S ⊗[ℤ] HyperbolicModule ℤ m

def VectorCoordinatesType : Prop :=
  ∀ (m : ℕ) (S : Type*) [CommRing S] [Algebra ℤ S] (x : ExtendedModule m S),
    SpinSpecification.ExtendedForm (integralForm m) S (hyperbolicBasis ℤ m) x =
      hyperbolicNorm ((Module.Basis.equivFun ((hyperbolicBasis ℤ m).baseChange S)) x)

/-- Coordinates of the action on Clifford vectors, in the fixed split basis. -/
def vectorMatrix (m : ℕ) {S : Type*} [CommRing S] [Algebra ℤ S]
    (g : ExtendedModule m S ≃ₗ[S] ExtendedModule m S) :
    Matrix (PairIndex m) (PairIndex m) S :=
  LinearMap.toMatrix ((hyperbolicBasis ℤ m).baseChange S)
    ((hyperbolicBasis ℤ m).baseChange S) g.toLinearMap

def HasActionMatrix (m : ℕ) {S : Type*} [CommRing S] [Algebra ℤ S]
    (a : (ScalarClifford m S)ˣ) (M : Matrix (PairIndex m) (PairIndex m) S) : Prop :=
  ∃ g : ExtendedModule m S ≃ₗ[S] ExtendedModule m S,
    SpinSpecification.IsVectorAction (integralForm m) S a g ∧ vectorMatrix m g = M

/-- The point functor of the indicated open in the spin scheme. -/
def SpinChart (m : ℕ) (S : Type*) [CommRing S] [Algebra ℤ S] :=
  {a : (ScalarClifford m S)ˣ // a ∈ SpinSpecification.spinUnits (integralForm m) S ∧
    ∃ M, HasActionMatrix m a M ∧ IsUnit M.toBlocks₁₁.det}

structure ChartParameters (m : ℕ) (S : Type*) [CommRing S] where
  P : Block m S
  Q : Block m S
  A : Block m S
  u : Sˣ
  alternatingP : IsAlternating P
  alternatingQ : IsAlternating Q
  normOne : (u : S) ^ 2 * A.det = 1

abbrev AlternatingIndex (m : ℕ) := {ij : Fin m × Fin m // ij.1 < ij.2}

def AlternatingDimensionType : Prop :=
  ∀ m, Fintype.card (AlternatingIndex m) = m.choose 2 ∧
    2 * Fintype.card (AlternatingIndex m) + m ^ 2 = 2 * m ^ 2 - m

def ChartParametersType : Prop :=
  ∀ (m : ℕ) (S : Type*) [CommRing S] (i : Fin m),
    ∃ e : ChartParameters m S ≃
        ((AlternatingIndex m → S) × (AlternatingIndex m → S) ×
          {A : Block m S // A.det = 1} × Sˣ),
      ∀ p,
        (∀ ij, (e p).1 ij = p.P ij.val.1 ij.val.2) ∧
        (∀ ij, (e p).2.1 ij = p.Q ij.val.1 ij.val.2) ∧
        (e p).2.2.1.val = scaleRow i ((p.u : S) ^ 2) p.A ∧ (e p).2.2.2 = p.u

def SpinMatrixType : Prop :=
  ∀ (m : ℕ) (S : Type*) [CommRing S] [Algebra ℤ S] (a : (ScalarClifford m S)ˣ),
    a ∈ SpinSpecification.spinUnits (integralForm m) S →
      ∃! M, HasActionMatrix m a M ∧ PreservesNorm M

/-- The natural chart equivalence over every test algebra, with its matrix factorization. -/
def CliffordChartType : Prop :=
  ∀ m : ℕ, 0 < m →
    ∃ e : ∀ (S : Type u) [CommRing S] [Algebra ℤ S], ChartParameters m S ≃ SpinChart m S,
      (∀ (S : Type u) [CommRing S] [Algebra ℤ S] (p : ChartParameters m S),
        HasActionMatrix m (e S p).val (lower p.P * middle p.A * upper p.Q)) ∧
      (∀ (S T : Type u) [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T] (f : S →ₐ[ℤ] T)
        (p : ChartParameters m S) (q : ChartParameters m T),
        q.P = p.P.map f → q.Q = p.Q.map f → q.A = p.A.map f →
        q.u = Units.map f.toMonoidHom p.u →
          (e T q).val = Units.map
            (SpinSpecification.coefficientMap (integralForm m) S f).toMonoidHom (e S p).val) ∧
      ∀ (S : Type u) [CommRing S] [Algebra ℤ S] (ζ : rootsOfUnity 2 S)
        (p q : ChartParameters m S),
        q.P = p.P → q.Q = p.Q → q.A = p.A → q.u = ζ.val * p.u →
          (e S q).val =
            Units.map (algebraMap S (ScalarClifford m S)).toMonoidHom ζ.val * (e S p).val

/-- Signed swaps in the pairs indexed by `J`. -/
def signedSwitch (m : ℕ) (R : Type*) [CommRing R] (J : Finset (Fin m)) :
    Matrix (PairIndex m) (PairIndex m) R :=
  let A := diagonal fun i : Fin m => if i ∈ J then (0 : R) else 1
  let B := diagonal fun i : Fin m => if i ∈ J then (-1 : R) else 0
  fromBlocks A B B A

def SignedSwitchType : Prop :=
  ∀ (m : ℕ) (R : Type*) [CommRing R] (J : Finset (Fin m)),
    PreservesNorm (signedSwitch m R J) ∧ signedSwitch m R J * signedSwitch m R J = 1

abbrev EvenSwitches (m : ℕ) := {J : Finset (Fin m) // Even J.card}

/-- An alternating lower shear in the standard chart can meet each even switch translate. -/
def EvenSwitchOverlapType : Prop :=
  ∀ (m : ℕ) (R : Type*) [CommRing R] (J : EvenSwitches m),
    ∃ P : Block m R, IsAlternating P ∧
      IsUnit (signedSwitch m R J.val * lower P).toBlocks₁₁.det

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

/-- The integral spin scheme, its standard open, and its covering by translated opens.
All descriptions of the opens specify their entire functors of points. -/
def SpinGeometryType : Prop :=
  ∀ m : ℕ, 0 < m →
    ∃ (G : SpinSpecification.GroupScheme ℤ)
      (e : ∀ S : CommAlgCat ℤ,
        SpinSpecification.SchemePoints G S →* (ScalarClifford m S)ˣ)
      (s : EvenSwitches m → SpinSpecification.SchemePoints G (CommAlgCat.of ℤ ℤ))
      (U : EvenSwitches m → G.X.left.Opens),
      SpinSpecification.IsSpinPointRepresentation (integralForm m) G e ∧
      (∀ J, HasActionMatrix m (e _ (s J)) (signedSwitch m ℤ J.val)) ∧
      (∀ J (S : CommAlgCat ℤ) (a : SpinSpecification.SchemePoints G S),
        let sS := (algSpec (CommRingCat.of ℤ)).map
          (CommAlgCat.ofHom (Algebra.ofId ℤ S)).op ≫ s J
        (∀ x, a.left x ∈ U J) ↔
          ∃ M, HasActionMatrix m (e S (sS * a)) M ∧ IsUnit M.toBlocks₁₁.det) ∧
      (⨆ J, U J) = ⊤ ∧
      (∀ J, GeometricallyConnected ((U J).ι ≫ G.X.hom)) ∧
      SmoothOfRelativeDimension (2 * m ^ 2 - m) G.X.hom ∧
      GeometricallyConnected G.X.hom

end

end LinearAlgebraicGroups.Albert.SplitSpinSpecification
