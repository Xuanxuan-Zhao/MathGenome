import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SpinFunctor
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility

namespace LinearAlgebraicGroups.Specs.Arithmetic.SpinHyperbolicDynamics

open AlgebraicGeometry CategoryTheory CliffordAlgebra Module
open LinearAlgebraicGroups.Albert.SpinSpecification
open LinearAlgebraicGroups.CocharacterDynamics
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open scoped TensorProduct CategoryTheory.MonObj

universe u

noncomputable section

variable {F : Type u} [Field F] {V : Type u} [AddCommGroup V] [Module F V]

/-- A hyperbolic pair with respect to the full polar form. -/
structure HyperbolicPair (q : QuadraticForm F V) where
  e : V
  f : V
  q_e : q e = 0
  q_f : q f = 0
  polar_ef : q.polarBilin e f = 1

def HyperbolicPair.swap {q : QuadraticForm F V} (h : HyperbolicPair q) : HyperbolicPair q :=
  ⟨h.f, h.e, h.q_f, h.q_e, (QuadraticMap.polar_comm q _ _).trans h.polar_ef⟩

def perpendicular (q : QuadraticForm F V) (h : HyperbolicPair q) : Submodule F V :=
  LinearMap.ker (q.polarBilin h.e) ⊓ LinearMap.ker (q.polarBilin h.f)

def IsRegular (q : QuadraticForm F V) : Prop :=
  LinearMap.ker q.polarBilin = ⊥ ∨
    ∃ r : V, q r ≠ 0 ∧ LinearMap.ker q.polarBilin = F ∙ r

abbrev vectorOver (R : TestAlgebra F) (v : V) : R ⊗[F] V := 1 ⊗ₜ[F] v

variable (q : QuadraticForm F V) (h : HyperbolicPair q)
  {I : Type u} [LinearOrder I] (b : Basis I F V)

def perpendicularOver (R : TestAlgebra F) : Submodule R (R ⊗[F] V) :=
  let Q := ExtendedForm q R b
  LinearMap.ker (Q.polarBilin (vectorOver R h.e)) ⊓
    LinearMap.ker (Q.polarBilin (vectorOver R h.f))

def diagonal (R : TestAlgebra F) (s : Rˣ) : ScalarClifford q R :=
  let E := vectors q R (vectorOver R h.e)
  let L := vectors q R (vectorOver R h.f)
  (s : R) • (E * L) + (↑s⁻¹ : R) • (L * E)

def shearValue (R : TestAlgebra F) (w : R ⊗[F] V) : ScalarClifford q R :=
  1 + vectors q R (vectorOver R h.e) * vectors q R w

def shearAction {R : TestAlgebra F} (w x : R ⊗[F] V) : R ⊗[F] V :=
  let Q := ExtendedForm q R b
  let e := vectorOver R h.e
  x + Q.polarBilin w x • e - Q.polarBilin e x • w - (Q.polarBilin e x * Q w) • e

variable {G : LinearAlgebraicGroups.Specs.GroupScheme F}
  (rep : ∀ R : TestAlgebra F, GroupPoints G R →* (ScalarClifford q R)ˣ)

def IsDiagonal (cochar : Cocharacter G) : Prop :=
  ∀ (R : TestAlgebra F) (s : Rˣ),
    (rep R (cocharacterPoint cochar R s)).val = diagonal q h R s

def CocharacterExists : Prop :=
  ∀ {F : Type u} [Field F] {V : Type u} [AddCommGroup V] [Module F V]
    {I : Type u} [LinearOrder I] (q : QuadraticForm F V) (_b : Basis I F V) (h : HyperbolicPair q)
    {G : LinearAlgebraicGroups.Specs.GroupScheme F}
    (rep : ∀ R : TestAlgebra F, GroupPoints G R →* (ScalarClifford q R)ˣ),
    IsSpinPointRepresentation q G rep → ∃ cochar : Cocharacter G, IsDiagonal q h rep cochar

/-- The diagonal acts with weights two, negative two, and zero on the
two distinguished vectors and their simultaneous perpendicular. -/
def CocharacterWeights : Prop :=
  ∀ {F : Type u} [Field F] {V : Type u} [AddCommGroup V] [Module F V]
    {I : Type u} [LinearOrder I] (q : QuadraticForm F V) (b : Basis I F V)
    (h : HyperbolicPair q) {G : LinearAlgebraicGroups.Specs.GroupScheme F}
    (rep : ∀ R : TestAlgebra F, GroupPoints G R →* (ScalarClifford q R)ˣ)
    (cochar : Cocharacter G),
    IsSpinPointRepresentation q G rep → IsDiagonal q h rep cochar →
    ∀ (R : TestAlgebra F) (s : Rˣ),
      ∃ A : (R ⊗[F] V) ≃ₗ[R] (R ⊗[F] V),
        IsVectorAction q R (rep R (cocharacterPoint cochar R s)) A ∧
        A (vectorOver R h.e) = (s : R) ^ 2 • vectorOver R h.e ∧
        A (vectorOver R h.f) = (↑s⁻¹ : R) ^ 2 • vectorOver R h.f ∧
        ∀ w : perpendicularOver q h b R, A w.val = w.val

/-- The two shears have the displayed orthogonal action and contract to the
identity over every commutative test algebra. -/
def ShearsContract : Prop :=
  ∀ {F : Type u} [Field F] {V : Type u} [AddCommGroup V] [Module F V]
    {I : Type u} [LinearOrder I] (q : QuadraticForm F V) (b : Basis I F V)
    (h : HyperbolicPair q) {G : LinearAlgebraicGroups.Specs.GroupScheme F}
    (rep : ∀ R : TestAlgebra F, GroupPoints G R →* (ScalarClifford q R)ˣ)
    (cochar : Cocharacter G),
    IsSpinPointRepresentation q G rep → IsDiagonal q h rep cochar →
    (∀ (R : TestAlgebra F) (w : perpendicularOver q h b R), ∃ g : GroupPoints G R,
      (rep R g).val = shearValue q h R w ∧ HasLimit cochar g 1 ∧
      ∀ x, conjugate q R (rep R g) (vectors q R x) =
        vectors q R (shearAction q h b w x)) ∧
    (∀ (R : TestAlgebra F) (w : perpendicularOver q h.swap b R), ∃ g : GroupPoints G R,
      (rep R g).val = shearValue q h.swap R w ∧ HasLimit (oppositeCocharacter cochar) g 1 ∧
      ∀ x, conjugate q R (rep R g) (vectors q R x) =
        vectors q R (shearAction q h.swap b w x))

/-- In characteristic zero the two contracting functors consist of the
respective shears. -/
def ContractingPoints : Prop :=
  ∀ {F : Type u} [Field F] [CharZero F] {V : Type u} [AddCommGroup V] [Module F V]
    {I : Type u} [LinearOrder I] [Fintype I] (q : QuadraticForm F V) (b : Basis I F V)
    (h : HyperbolicPair q) (_ : IsRegular q) {G : LinearAlgebraicGroups.Specs.GroupScheme F}
    (rep : ∀ R : TestAlgebra F, GroupPoints G R →* (ScalarClifford q R)ˣ)
    (cochar : Cocharacter G),
    IsSpinPointRepresentation q G rep → IsDiagonal q h rep cochar →
    (∀ (R : TestAlgebra F) (g : GroupPoints G R), HasLimit cochar g 1 →
      ∃! w : perpendicularOver q h b R, (rep R g).val = shearValue q h R w) ∧
    (∀ (R : TestAlgebra F) (g : GroupPoints G R), HasLimit (oppositeCocharacter cochar) g 1 →
      ∃! w : perpendicularOver q h.swap b R, (rep R g).val = shearValue q h.swap R w)

def CentralizerAction : Prop :=
  ∀ {F : Type u} [Field F] [Infinite F] {V : Type u} [AddCommGroup V] [Module F V]
    {I : Type u} [LinearOrder I] (q : QuadraticForm F V) (b : Basis I F V)
    (h : HyperbolicPair q) {G : LinearAlgebraicGroups.Specs.GroupScheme F}
    (rep : ∀ R : TestAlgebra F, GroupPoints G R →* (ScalarClifford q R)ˣ)
    (cochar : Cocharacter G),
    IsSpinPointRepresentation q G rep → IsDiagonal q h rep cochar →
    let R := CommAlgCat.of F F
    ∀ (g : GroupPoints G R), Centralizes cochar g →
      ∃ (A : (R ⊗[F] V) ≃ₗ[R] (R ⊗[F] V)) (s : Fˣ),
        IsVectorAction q R (rep R g) A ∧
        A (vectorOver R h.e) = (s : F) • vectorOver R h.e ∧
        A (vectorOver R h.f) = (↑s⁻¹ : F) • vectorOver R h.f ∧
        (perpendicularOver q h b R).map A.toLinearMap = perpendicularOver q h b R

/-- For a hyperbolic plane the displayed cocharacter identifies its spin
group with the multiplicative group. -/
def HyperbolicPlaneTorus : Prop :=
  ∀ {F : Type u} [Field F] {V : Type u} [AddCommGroup V] [Module F V]
    {I : Type u} [LinearOrder I] (q : QuadraticForm F V) (_b : Basis I F V)
    (h : HyperbolicPair q), perpendicular q h = ⊥ →
    ∀ {G : LinearAlgebraicGroups.Specs.GroupScheme F}, IsAffine G.X.left →
    ∀ (rep : ∀ R : TestAlgebra F, GroupPoints G R →* (ScalarClifford q R)ˣ)
      (cochar : Cocharacter G),
    IsSpinPointRepresentation q G rep → IsDiagonal q h rep cochar → IsIso cochar

def Noncentrality : Prop :=
  ∀ {F : Type u} [Field F] [Infinite F] {V : Type u} [AddCommGroup V] [Module F V]
    {I : Type u} [LinearOrder I] [Fintype I] (q : QuadraticForm F V) (_b : Basis I F V)
    (h : HyperbolicPair q), IsRegular q →
    ∀ (G : AffineAlgebraicGroup F),
    ∀ (rep : ∀ R : TestAlgebra F, GroupPoints G.val R →* (ScalarClifford q R)ˣ)
      (cochar : Cocharacter G.val),
    IsSpinPointRepresentation q G.val rep → IsDiagonal q h rep cochar →
    IsAbsolutelyAlmostSimple G →
      (∃ w : perpendicular q h, q w.val ≠ 0) ∧
      ∃ g : GroupPoints G.val (CommAlgCat.of F F), ¬ Centralizes cochar g

end
end LinearAlgebraicGroups.Specs.Arithmetic.SpinHyperbolicDynamics
