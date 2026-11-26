import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SpinFunctor
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.ExactOperations

/-! Scalar extension for the Clifford spin model and its marked cocharacter in F12. -/

namespace LinearAlgebraicGroups.Specs.Arithmetic.SpinScalarExtension

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct
open CliffordAlgebra
open LinearAlgebraicGroups.Albert
open SpinSpecification (ScalarClifford vectors reversion spinUnits coefficientMap
  IsSpinPointRepresentation)
open CliffordSpecification (coefficientForm)
open AdjointRepresentation (GroupPoints)
open CharacterDescent (Cocharacter)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Unipotent (baseChangedAlgebraicGroup)

universe u v w

noncomputable section

local notation "𝔾ₘ(" k ")" => specGroup (groupAlgebra k IntegerCharacters)

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- Extension commutes with the polar radical, and the possible regular
radical line keeps its marked generator of nonzero quadratic value. -/
def PolarRadicalExtension : Prop :=
  ∀ {K F : Type u} [Field K] [Field F] [Algebra K F]
    {V : Type v} [AddCommGroup V] [Module K V] [Module.Finite K V]
    {I : Type w} [LinearOrder I] (q : QuadraticForm K V) (b : Module.Basis I K V),
    let Q := coefficientForm F q b
    LinearMap.ker Q.polarBilin = (LinearMap.ker q.polarBilin).baseChange F ∧
    (LinearMap.ker q.polarBilin = ⊥ → LinearMap.ker Q.polarBilin = ⊥) ∧
    ∀ r : V, q r ≠ 0 → LinearMap.ker q.polarBilin = K ∙ r →
      Q (1 ⊗ₜ[K] r) ≠ 0 ∧ LinearMap.ker Q.polarBilin = F ∙ (1 ⊗ₜ[K] r)

/-- Both vectors and their full polar pairing extend with the same hyperbolic equations. -/
def HyperbolicPairExtension : Prop :=
  ∀ {K F : Type u} [CommRing K] [CommRing F] [Algebra K F]
    {V : Type v} [AddCommGroup V] [Module K V]
    {I : Type w} [LinearOrder I] (q : QuadraticForm K V) (b : Module.Basis I K V)
    (e f : V), q e = 0 → q f = 0 → q.polarBilin e f = 1 →
    let Q := coefficientForm F q b
    Q (1 ⊗ₜ[K] e) = 0 ∧ Q (1 ⊗ₜ[K] f) = 0 ∧
      Q.polarBilin (1 ⊗ₜ[K] e) (1 ⊗ₜ[K] f) = 1

/-- The test algebra over the original field used by A01. -/
abbrev restricted (K : Type u) [Field K] (R : TestAlgebra F) [Algebra K F] :
    TestAlgebra K :=
  (restrictTestAlgebra K F).obj R

/-- The vector module on a test algebra is unchanged by cancelling the intermediate
field in a successive extension of scalars. -/
def vectorComparison (R : TestAlgebra F) :
    (R ⊗[F] (F ⊗[K] V)) ≃ₗ[R] ((restricted K R) ⊗[K] V) := by
  letI : Algebra K R := ((algebraMap F R).comp (algebraMap K F)).toAlgebra
  letI : IsScalarTower K F R := IsScalarTower.of_algebraMap_eq' rfl
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange K F R R V

/-- The quadratic and polar forms in the two models agree on every test algebra. -/
def TestQuadraticFormComparison : Prop :=
  ∀ {K F : Type u} [Field K] [Field F] [Algebra K F]
    {V : Type v} [AddCommGroup V] [Module K V]
    {I : Type w} [LinearOrder I] (q : QuadraticForm K V) (b : Module.Basis I K V)
    (R : TestAlgebra F),
    let Q := coefficientForm R (coefficientForm F q b) (b.baseChange F)
    let P := coefficientForm (restricted K R) q b
    (∀ x, Q x = P (vectorComparison R x)) ∧
    (∀ x y, Q.polarBilin x y = P.polarBilin (vectorComparison R x) (vectorComparison R y))

/-- The multiplicative-group comparison is normalized on the point of every unit. -/
def IsMultiplicativeComparison
    (c : 𝔾ₘ(F) ≅ (groupBaseChange K F).obj (𝔾ₘ(K))) : Prop :=
  ∀ (R : TestAlgebra F) (s : Rˣ),
    baseChangePoint K F (𝔾ₘ(K)).X R (unitPoint R s ≫ c.hom.hom.hom) =
      unitPoint (restricted K R) s

def MultiplicativeComparison : Prop :=
  ∀ {K F : Type u} [Field K] [Field F] [Algebra K F],
    ∃ c : 𝔾ₘ(F) ≅ (groupBaseChange K F).obj (𝔾ₘ(K)),
      IsMultiplicativeComparison c

/-- The Clifford diagonal giving the cocharacter of the marked hyperbolic pair. -/
def HasSpinCocharacterFormula {G : GroupScheme K} (q : QuadraticForm K V)
    (ρ : ∀ R : TestAlgebra K, GroupPoints G R →* (ScalarClifford q R)ˣ)
    (e f : V) (c : Cocharacter G) : Prop :=
  ∀ (R : TestAlgebra K) (s : Rˣ),
    let E := vectors q R (1 ⊗ₜ[K] e)
    let L := vectors q R (1 ⊗ₜ[K] f)
    (ρ R (cocharacterPoint c R s)).val = (s : R) • (E * L) + (↑s⁻¹ : R) • (L * E)

/-- The actual scheme base change represents the extended Clifford spin functor.
The algebra comparison intertwines the vector inclusion, reversion, grading,
and every change of test algebra. The compatible multiplicative-group comparison
identifies any cocharacter with the marked Clifford formula after scalar extension. -/
def SpinRepresentationExtension : Prop :=
  ∀ {K F : Type u} [Field K] [Field F] [Algebra K F]
    {V : Type u} [AddCommGroup V] [Module K V]
    {I : Type w} [LinearOrder I] (q : QuadraticForm K V) (b : Module.Basis I K V)
    (G : AffineAlgebraicGroup K)
    (ρ : ∀ R : TestAlgebra K, GroupPoints G.val R →* (ScalarClifford q R)ˣ),
    IsSpinPointRepresentation q G.val ρ →
    let Q := coefficientForm F q b
    let H := baseChangedAlgebraicGroup F G
    ∃ (A : ∀ R : TestAlgebra F, ScalarClifford q (restricted K R) ≃ₐ[R] ScalarClifford Q R)
      (ρF : ∀ R : TestAlgebra F, GroupPoints H.val R →* (ScalarClifford Q R)ˣ),
      (∀ (R : TestAlgebra F) (x : R ⊗[F] (F ⊗[K] V)),
        A R (vectors q (restricted K R) (vectorComparison R x)) = vectors Q R x) ∧
      (∀ (R : TestAlgebra F) (x : ScalarClifford q (restricted K R)),
        A R (reversion q (restricted K R) x) = reversion Q R (A R x)) ∧
      (∀ (R : TestAlgebra F) (j : ZMod 2) (x : ScalarClifford q (restricted K R)),
        A R x ∈ (evenOdd Q j).baseChange R ↔
          x ∈ (evenOdd q j).baseChange (restricted K R)) ∧
      (∀ {R S : TestAlgebra F} (a : R ⟶ S) (x : ScalarClifford q (restricted K R)),
        A S (coefficientMap q (restricted K R) ((restrictTestAlgebra K F).map a).hom x) =
          coefficientMap Q R a.hom (A R x)) ∧
      (∀ (R : TestAlgebra F) (a : (ScalarClifford q (restricted K R))ˣ),
        Units.map (A R).toMonoidHom a ∈ spinUnits Q R ↔ a ∈ spinUnits q (restricted K R)) ∧
      (∀ (R : TestAlgebra F) (p : GroupPoints H.val R),
        ρF R p = Units.map (A R).toMonoidHom
          (ρ (restricted K R) (baseChangePoint K F G.val.X R p))) ∧
      IsSpinPointRepresentation Q H.val ρF ∧
      (∀ (e f : V), q e = 0 → q f = 0 → q.polarBilin e f = 1 →
        ∀ (c : Cocharacter G.val), HasSpinCocharacterFormula q ρ e f c →
        ∀ (m : 𝔾ₘ(F) ≅ (groupBaseChange K F).obj (𝔾ₘ(K))),
          IsMultiplicativeComparison m →
          let cF : Cocharacter H.val := m.hom ≫ (groupBaseChange K F).map c
          (∀ (R : TestAlgebra F) (s : Rˣ),
            baseChangePoint K F G.val.X R (cocharacterPoint cF R s) =
              cocharacterPoint c (restricted K R) s) ∧
          HasSpinCocharacterFormula Q ρF (1 ⊗ₜ[K] e) (1 ⊗ₜ[K] f) cF ∧
          ∀ d : Cocharacter H.val,
            HasSpinCocharacterFormula Q ρF (1 ⊗ₜ[K] e) (1 ⊗ₜ[K] f) d → d = cF)

end
end LinearAlgebraicGroups.Specs.Arithmetic.SpinScalarExtension
