import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.LowerRankHermitianModels
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Batteries.Tactic.OpenPrivate

/-! The split models and faithfully flat forms of NA13-C04.04. -/

namespace LinearAlgebraicGroups.Albert.SplitSpecification

open _root_.Specs.LinearAlgebraicGroups.Albert
open _root_.LinearAlgebraicGroups.Composition
open HermitianSpecification CubicSpecification LowerRankSpecification
open QuadraticOperatorSpecification (applyOperator)
open scoped TensorProduct
open TensorProduct

set_option linter.style.haveILetI false

universe u v w

section Laws

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- The data of a unital para-quadratic algebra, before imposing the two Jordan identities. -/
structure ParaQuadratic (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]
    [Module R M] extends QuadraticOperatorLaw R M where
  unit : M
  op_unit (S : Type u) [CommRing S] [Algebra R S] : op S (1 ⊗ₜ[R] unit) = 1

namespace ParaQuadratic

variable (J : ParaQuadratic R M)

/-- The law underlying a unital quadratic Jordan algebra. -/
def ofJordan (J : QuadraticJordan R M) : ParaQuadratic R M :=
  ⟨J.toQuadraticOperatorLaw, J.unit, J.op_unit⟩

def groundOp (x : M) : Module.End R M :=
  (TensorProduct.lid R M).conj (J.op R (1 ⊗ₜ[R] x))

def JordanAt (S : Type u) [CommRing S] [Algebra R S] : Prop :=
  (∀ x y : S ⊗[R] M, J.op S (J.op S x y) = J.op S x * J.op S y * J.op S x) ∧
  (∀ x y z : S ⊗[R] M, J.op S x (J.toQuadraticOperatorLaw.triple S y x z) =
    J.toQuadraticOperatorLaw.triple S (J.op S x y) z x)

def IsJordan : Prop := ∀ (S : Type u) [CommRing S] [Algebra R S], J.JordanAt S

/-- Isomorphism of the pointed operator laws on all test algebras. -/
def IsIso (K : ParaQuadratic R N) (e : M ≃ₗ[R] N) : Prop :=
  e J.unit = K.unit ∧
    ∀ (S : Type u) [CommRing S] [Algebra R S] (x y : S ⊗[R] M),
      e.toLinearMap.baseChange S (J.op S x y) =
        K.op S (e.toLinearMap.baseChange S x) (e.toLinearMap.baseChange S y)

/-- The same conditions evaluated on the original modules. -/
def IsGroundIso (K : ParaQuadratic R N) (e : M ≃ₗ[R] N) : Prop :=
  e J.unit = K.unit ∧ ∀ x y, e (J.groundOp x y) = K.groundOp (e x) (e y)

variable (S : Type u) [CommRing S] [Algebra R S]

/-- Operator of the extended law, via the associativity isomorphism for scalar extension. -/
noncomputable def extendedOp (T : Type u) [CommRing T] [Algebra S T] :
    QuadraticMap T (T ⊗[S] (S ⊗[R] M)) (Module.End T (T ⊗[S] (S ⊗[R] M))) :=
  letI := towerAlgebra R S T
  let e := iteratedTensorEquiv (R := R) (S := S) (M := M) T
  e.symm.conj.toLinearMap.compQuadraticMap ((J.op T).comp e.toLinearMap)

theorem extendedOp_apply (T : Type u) [CommRing T] [Algebra S T]
    (x y : T ⊗[S] (S ⊗[R] M)) :
    letI := towerAlgebra R S T
    let e := iteratedTensorEquiv (R := R) (S := S) (M := M) T
    e (J.extendedOp S T x y) = J.op T (e x) (e y) := by
  letI := towerAlgebra R S T
  let e := iteratedTensorEquiv (R := R) (S := S) (M := M) T
  change e (e.symm (J.op T (e x) (e y))) = _
  exact e.apply_symm_apply _

open private towerScalars iteratedTensorEquiv_natural from MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.QuadraticJordan

/-- Scalar extension of the pointed law, before any Jordan axioms are imposed. -/
noncomputable def baseChange : ParaQuadratic S (S ⊗[R] M) where
  op := J.extendedOp S
  unit := 1 ⊗ₜ[R] J.unit
  natural {T W} _ _ _ _ f x y := by
    letI := towerAlgebra R S T
    letI := towerAlgebra R S W
    letI := towerScalars R S T
    letI := towerScalars R S W
    apply (iteratedTensorEquiv (R := R) (S := S) W).injective
    rw [iteratedTensorEquiv_natural, J.extendedOp_apply, J.extendedOp_apply,
      iteratedTensorEquiv_natural, iteratedTensorEquiv_natural, J.natural]
  op_unit T _ _ := by
    letI := towerAlgebra R S T
    apply LinearMap.ext
    intro y
    apply (iteratedTensorEquiv (R := R) (S := S) T).injective
    change iteratedTensorEquiv (R := R) (S := S) T
      (J.extendedOp S T (1 ⊗ₜ[S] (1 ⊗ₜ[R] J.unit)) y) = _
    rw [J.extendedOp_apply, AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
      J.op_unit, Module.End.one_apply, Module.End.one_apply]

end ParaQuadratic
end Laws

/-- The four possible split composition inputs. -/
inductive SplitRank
  | scalar | pair | quaternion | octonion
  deriving DecidableEq

instance : Fintype SplitRank where
  elems := {.scalar, .pair, .quaternion, .octonion}
  complete i := by cases i <;> simp

def SplitRank.hermitianRank : SplitRank → ℕ
  | .scalar => 6
  | .pair => 9
  | .quaternion => 15
  | .octonion => 27

abbrev SplitRank.Input (R : Type u) : SplitRank → Type u
  | .scalar => R
  | .pair => R × R
  | .quaternion => SplitQuaternion R
  | .octonion => Zorn R

instance (R : Type u) [CommRing R] (i : SplitRank) : NonAssocRing (i.Input R) := by
  cases i
  · exact inferInstanceAs (NonAssocRing R)
  · exact inferInstanceAs (NonAssocRing (R × R))
  · exact inferInstanceAs (NonAssocRing (SplitQuaternion R))
  · exact inferInstanceAs (NonAssocRing (Zorn R))

instance (R : Type u) [CommRing R] (i : SplitRank) : Module R (i.Input R) := by
  cases i
  · exact inferInstanceAs (Module R R)
  · exact inferInstanceAs (Module R (R × R))
  · exact inferInstanceAs (Module R (SplitQuaternion R))
  · exact inferInstanceAs (Module R (Zorn R))

def SplitRank.norm (R : Type u) [CommRing R] (i : SplitRank) : QuadraticForm R (i.Input R) :=
  match i with
  | .scalar => scalarNorm R
  | .pair => pairNorm R
  | .quaternion => quaternionNorm R
  | .octonion => zornNorm R

abbrev SplitRank.Model (R : Type u) (i : SplitRank) := Coordinates R (i.Input R)

section Forms

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The split Hermitian model of a specified type is characterized by its unit and
operator in Hermitian coordinates. These determine the entire natural law. -/
def IsSplitModel (J : ParaQuadratic R M) (i : SplitRank) : Prop :=
  ∃ e : M ≃ₗ[R] i.Model R, e J.unit = cubicUnit ∧
    ∀ x y, e (J.groundOp x y) = applyOperator (i.norm R) (untwisted R) (e x) (e y)

def OnComponent (J : ParaQuadratic R M) (B : Type u) [CommRing B] [Algebra R B]
    (i : SplitRank) : Prop :=
  ∃ e : B ⊗[R] M ≃ₗ[B] i.Model B, e (1 ⊗ₜ[R] J.unit) = cubicUnit ∧
    ∀ x y, e (J.op B x y) = applyOperator (i.norm B) (untwisted B) (e x) (e y)

/-- For a disconnected base the four models occur on the four (possibly empty)
clopen rank pieces, presented here by the corresponding product of rings. -/
def IsSplit (J : ParaQuadratic R M) : Prop :=
  (∃ i, IsSplitModel J i) ∨
    ∃ (B : SplitRank → Type u) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra R (B i)),
      Function.Bijective (algebraMap R (∀ i, B i)) ∧ ∀ i, OnComponent J (B i) i

/-- A Freudenthal algebra is a faithfully flat form of the split models. -/
def IsFreudenthal (J : ParaQuadratic R M) : Prop :=
  ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
    Module.FaithfullyFlat R S ∧ IsSplit (J.baseChange S)

/-- An Albert algebra is a Freudenthal algebra of constant rank 27. -/
def IsAlbert (J : ParaQuadratic R M) : Prop :=
  IsFreudenthal J ∧ ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = 27

/-- The reduced weighted model uses (H_3(C,Γ)) and its extended operators. -/
def IsReducedModel {A : Type w} [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A}
    (h : Specification.OctonionNormConditions n) (γ : Fin 3 → Rˣ)
    (J : ParaQuadratic R (Coordinates R A)) : Prop :=
  letI := h.projective
  J.unit = cubicUnit ∧
    ∀ (S : Type u) [CommRing S] [Algebra R S] (x y : S ⊗[R] Coordinates R A),
      coordinatesBaseChange S (J.op S x y) =
        applyOperator (Specification.normBaseChange S n) (baseChangedWeights S γ)
          (coordinatesBaseChange S x) (coordinatesBaseChange S y)

end Forms

namespace Types
set_option linter.checkUnivs false

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

set_option linter.checkUnivs false in
def BaseChangeType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M],
    ParaQuadratic R M → ∀ (S : Type u) [CommRing S] [Algebra R S],
      ParaQuadratic S (S ⊗[R] M)

noncomputable abbrev baseChangeValue := @ParaQuadratic.baseChange

def IsSplitModelType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M],
    ParaQuadratic R M → SplitRank → Prop

def FormPredicateType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M],
    ParaQuadratic R M → Prop

def IsReducedModelType :=
  ∀ {R : Type u} [CommRing R] {A : Type v} [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    Specification.OctonionNormConditions n → (Fin 3 → Rˣ) →
    ParaQuadratic R (Coordinates R A) → Prop

def SplitModelExistsType : Prop :=
  ∀ (R : Type u) [CommRing R] (i : SplitRank),
    ∃ K : QuadraticJordan R (i.Model R), K.unit = cubicUnit ∧
      ∀ x y, K.groundOp x y = applyOperator (i.norm R) (untwisted R) x y

def SplitModelRankType : Prop :=
  ∀ (R : Type u) [CommRing R] (i : SplitRank),
    Module.Finite R (i.Model R) ∧ Module.Free R (i.Model R) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (i.Model R) p = i.hermitianRank

def SplitModelIsoType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : ParaQuadratic R M) (i : SplitRank),
    IsSplitModel J i ↔ ∃ K : QuadraticJordan R (i.Model R),
      K.unit = cubicUnit ∧
      (∀ x y, K.groundOp x y = applyOperator (i.norm R) (untwisted R) x y) ∧
      ∃ e : M ≃ₗ[R] i.Model R, J.IsIso (ParaQuadratic.ofJordan K) e

def SplitRankLocusType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : ParaQuadratic R M) {B : SplitRank → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)],
    Function.Bijective (algebraMap R (∀ i, B i)) → (∀ i, OnComponent J (B i) i) →
    ∀ i : SplitRank, Set.range (PrimeSpectrum.comap (algebraMap R (B i))) =
      {p | Module.rankAtStalk M p = i.hermitianRank} ∧
      IsClopen {p : PrimeSpectrum R | Module.rankAtStalk M p = i.hermitianRank}

def GroundIsoType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (J : ParaQuadratic R M) (K : ParaQuadratic R N) (e : M ≃ₗ[R] N),
    J.IsIso K e ↔ J.IsGroundIso K e

def ScalarExtensionOperatorType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : ParaQuadratic R M) (S : Type u) [CommRing S] [Algebra R S]
    (x y : S ⊗[R] M), (J.baseChange S).groundOp x y = J.op S x y

def JordanDescentType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : ParaQuadratic R M) (S : Type u) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S],
    (J.baseChange S).IsJordan → J.IsJordan

def SplitJordanType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : ParaQuadratic R M), IsSplit J → J.IsJordan

def FreudenthalJordanType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : ParaQuadratic R M), IsFreudenthal J → J.IsJordan

def FreudenthalFiniteProjectiveType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : ParaQuadratic R M), IsFreudenthal J → Module.Finite R M ∧ Module.Projective R M

def FreudenthalRankType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : ParaQuadratic R M), IsFreudenthal J → IsLocallyConstant (Module.rankAtStalk (R := R) M) ∧
      ∀ p : PrimeSpectrum R, ∃ i : SplitRank, Module.rankAtStalk M p = i.hermitianRank

def AlbertSplitType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : ParaQuadratic R M),
    IsAlbert J ↔ ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Module.FaithfullyFlat R S ∧ OnComponent J S .octonion

def UnitSquareRootType : Prop :=
  ∀ (R : Type u) [CommRing R] (a : Rˣ), ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
    Module.FaithfullyFlat R S ∧ Nonempty (Module.Basis (Fin 2) R S) ∧
      ∃ b : Sˣ, b ^ 2 = Units.map (algebraMap R S) a

def ReducedAlbertType : Prop :=
  ∀ {R : Type u} [CommRing R] {A : Type v} [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A}
    (h : Specification.OctonionNormConditions n) (γ : Fin 3 → Rˣ)
    (J : ParaQuadratic R (Coordinates R A)), IsReducedModel h γ J → IsAlbert J

def WeightedReducedModelType : Prop :=
  ∀ {R : Type u} [CommRing R] {A : Type v} [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A}
    (h : Specification.OctonionNormConditions n) (γ : Fin 3 → Rˣ),
    ∃ K : QuadraticJordan R (Coordinates R A),
      IsReducedModel h γ (ParaQuadratic.ofJordan K) ∧ IsAlbert (ParaQuadratic.ofJordan K)

end Types

end LinearAlgebraicGroups.Albert.SplitSpecification
