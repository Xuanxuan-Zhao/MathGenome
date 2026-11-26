import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TypeAMatrixDescentData
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.UnitaryNormEquations
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.InnerTypeA
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SpecialLinearDatum
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.PinnedEquivalence
import Mathlib.Data.ZMod.Basic
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Degree
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.ProjectiveClassification

open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.OuterTypeAModels

open Matrix
open RM03.Brauer.SemilinearDescent (AlgebraAction)

abbrev Mat (K : Type u) (n : ℕ) := Matrix (Fin n) (Fin n) K

/-- A parity on the Galois group, with the identity denoting its even coset. -/
abbrev DiagramCharacter (F K : Type u) [Field F] [Field K] [Algebra F K] :=
  Gal(K/F) →* Multiplicative (ZMod 2)

/-- The additive lift of one semilinear group automorphism. In odd parity
the corresponding group automorphism first inverts its argument. -/
structure MatrixLift {F K : Type u} [Field F] [Field K] [Algebra F K]
    (n : ℕ) (σ : Gal(K/F)) (p : Multiplicative (ZMod 2)) where
  toAddEquiv : Mat K n ≃+ Mat K n
  map_one : toAddEquiv 1 = 1
  map_smul : ∀ (a : K) (x : Mat K n), toAddEquiv (a • x) = σ a • toAddEquiv x
  map_mul_even : p = 1 → ∀ x y, toAddEquiv (x * y) = toAddEquiv x * toAddEquiv y
  map_mul_odd : p ≠ 1 → ∀ x y, toAddEquiv (x * y) = toAddEquiv y * toAddEquiv x

variable {F K : Type u} [Field F] [Field K] [Algebra F K] {n : ℕ}

/-- The comparison with a Galois action after transport to the split matrix group.
The equation here is an equation on points, supplied by the original scheme
action and individual inner or transpose-inverse presentations. -/
def LiftsAction (χ : DiagramCharacter F K)
    (β : ∀ σ : Gal(K/F), MatrixLift n σ (χ σ))
    (s : Gal(K/F) →* MulAut (SpecialLinearGroup (Fin n) K)) : Prop :=
  ∀ σ x, (s σ x).val =
    (β σ).toAddEquiv (if χ σ = 1 then x.val else x⁻¹.val)

/-- An inner/transpose-inverse presentation gives the required additive lifts.
The matrices are representatives of projective conjugations. -/
def MatrixLiftsExist : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] {n : ℕ}
    (χ : DiagramCharacter F K) (g : ∀ _ : Gal(K/F), (Mat K n)ˣ)
    (s : Gal(K/F) →* MulAut (SpecialLinearGroup (Fin n) K)),
    (∀ σ x, (s σ x).val =
      (g σ : Mat K n) *
        (if χ σ = 1 then x.val.map σ else ((x⁻¹).val.map σ).transpose) *
        (↑(g σ)⁻¹ : Mat K n)) →
    ∃ β : ∀ σ : Gal(K/F), MatrixLift n σ (χ σ),
      LiftsAction χ β s ∧
      ∀ σ x, (β σ).toAddEquiv x =
        (g σ : Mat K n) * (if χ σ = 1 then x.map σ else (x.map σ).transpose) *
          (↑(g σ)⁻¹ : Mat K n)

/-- The whole matrix algebra inherits an action with the indicated parity. -/
def MatrixActionLaw : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] {n : ℕ}, 2 ≤ n →
    ∀ (χ : DiagramCharacter F K) (β : ∀ σ : Gal(K/F), MatrixLift n σ (χ σ))
      (s : Gal(K/F) →* MulAut (SpecialLinearGroup (Fin n) K)), LiftsAction χ β s →
      (∀ x, (β 1).toAddEquiv x = x) ∧
      (∀ σ τ x, (β (σ * τ)).toAddEquiv x = (β σ).toAddEquiv ((β τ).toAddEquiv x))

/-- For the trivial diagram character the whole action descends the matrix
algebra, with the same projective cocycle as conjugation on the split group. -/
def FixedInnerAlgebra : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] {n : ℕ}, 2 ≤ n →
    ∀ (β : ∀ σ : Gal(K/F), MatrixLift n σ ((1 : DiagramCharacter F K) σ))
      (s : Gal(K/F) →* MulAut (SpecialLinearGroup (Fin n) K)),
      LiftsAction 1 β s →
      ∃ (ρ : AlgebraAction F K (Mat K n))
        (c : RM03.Brauer.ProjectiveClassification.Cocycle F K n),
        (∀ σ x, ρ.act σ x = (β σ).toAddEquiv x) ∧
        RM03.Brauer.ProjectiveClassification.Implements ρ c ∧
        let A := ρ.fixedSubalgebra
        _root_.Specs.RM03.CSA.isCentralSimple F A ∧
        _root_.Specs.RM03.CSA.degree F A = n ∧
        ∃ e : (K ⊗[F] A) ≃ₐ[K] Mat K n,
          RM03.Brauer.ProjectiveClassification.IsTransport ρ e ∧
          ∀ a x, e (a ⊗ₜ[F] x) = a • (x : Mat K n)

/-- The fixed field attached to the even diagram action. -/
abbrev DiagramField (χ : DiagramCharacter F K) := IntermediateField.fixedField χ.ker

/-- Descent over the even subgroup, with the action and multiplication on the
ambient matrices specified. The resulting involution is induced by every odd
operator and acts nontrivially on the quadratic centre. -/
def DescendsOuter {F K : Type u} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] {n : ℕ}
    (χ : DiagramCharacter F K) (β : ∀ σ : Gal(K/F), MatrixLift n σ (χ σ)) : Prop :=
  let E := DiagramField χ
  Module.finrank F E = 2 ∧
    ∃ (ρ : AlgebraAction E K (Mat K n)),
      (∀ (σ : χ.ker) x, ρ.act (IntermediateField.subgroupEquivAlgEquiv χ.ker σ) x =
        (β σ.val).toAddEquiv x) ∧
      let A := ρ.fixedSubalgebra
      _root_.Specs.RM03.CSA.isCentralSimple E A ∧
      _root_.Specs.RM03.CSA.degree E A = n ∧
      (∃ e : (K ⊗[E] A) ≃ₐ[K] Mat K n, ∀ a x, e (a ⊗ₜ[E] x) = a • (x : Mat K n)) ∧
      ∃ (bar : Gal(E/F)) (star : A ≃+* Aᵐᵒᵖ),
        bar ≠ 1 ∧
        (∀ a : E, star (algebraMap E A a) =
          MulOpposite.op (algebraMap E A (bar a))) ∧
        (∀ x : A, (star ((star x).unop)).unop = x) ∧
        (∀ (σ : Gal(K/F)) (_ : χ σ ≠ 1) (x : A),
          ((star x).unop : Mat K n) = (β σ).toAddEquiv (x : Mat K n)) ∧
        ∀ (σ : Gal(K/F)) (_ : χ σ ≠ 1) (a : E), (bar a : K) = σ (a : K)

def FixedAlgebraWithInvolution : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] {n : ℕ}, 2 ≤ n →
    ∀ (χ : DiagramCharacter F K), Function.Surjective χ →
    ∀ (β : ∀ σ : Gal(K/F), MatrixLift n σ (χ σ))
      (s : Gal(K/F) →* MulAut (SpecialLinearGroup (Fin n) K)),
      LiftsAction χ β s → DescendsOuter χ β

open Pinning (BasedRootDatum BasedIso)

/-- A simple-coroot basis and the Cartan pairings determine the integral
based datum, including its full character lattice. -/
def BasedDatumComparison : Prop :=
  ∀ (P Q : BasedRootDatum.{u})
    (bP : Module.Basis P.base.support ℤ P.Y) (bQ : Module.Basis Q.base.support ℤ Q.Y)
    (_hbP : ∀ i, bP i = P.datum.coroot i) (_hbQ : ∀ i, bQ i = Q.datum.coroot i)
    (e : P.base.support ≃ Q.base.support),
    (∀ i j : P.base.support, P.datum.pairing i j = Q.datum.pairing (e i) (e j)) →
    ∃ f : BasedIso P Q, ∀ i : P.base.support, f.val.indexEquiv i = (e i).val

/-- Simply connected based data of type A, presented with the ordered
simple coroot basis and Cartan chain. -/
def HasSimplyConnectedTypeA (r : ℕ) (P : BasedRootDatum.{u}) : Prop :=
  ∃ (e : Fin r ≃ P.base.support) (b : Module.Basis P.base.support ℤ P.Y),
    (∀ i, b i = P.datum.coroot i) ∧
    ∀ i j : Fin r, P.datum.pairing (e i) (e j) =
      if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0

/-- A pinned split group with the simply connected type A chain identifies
with the actual pinned determinant-one matrix group. -/
def SplitMatrixComparison : Prop :=
  ∀ {k : Type u} [Field k] (r : ℕ) (S : AffineAlgebraicGroup k)
    (_s : GeneralLinearStructure.SpecialMatrixPoints S (r + 1)),
    ∃ (A : RootGroups.AdditiveLine k) (Q : Pinning.PinnedGroup A),
      Q.pair.G = S ∧
      ∀ (P : Pinning.PinnedGroup A) (D : Pinning.AttachedDatum P.pair),
        HasSimplyConnectedTypeA r D.toBased → Nonempty (Pinning.PinnedIso P Q)

section Forms

open CategoryTheory
open TypeAMatrixDescentData GeneralLinearStructure
open Unipotent (Index)
open AutomorphismSequence (IsSeparableForm)
open _root_.LinearAlgebraicGroups.UnitaryNormEquations (SecondKind IsSpecialUnitary)
open _root_.Specs.RM03.CSA (isCentralSimple degree)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)

/-- The original group represents the reduced-norm-one functor, with its
multiplication and maps of coefficients coming from the scalar-extended algebra. -/
def RepresentsNormOne {A : Type u} [Ring A] [Algebra F A] (hA : isCentralSimple F A)
    {ι : Type u} [Fintype ι] (b : Module.Basis ι F A) (H : AffineAlgebraicGroup F) : Prop :=
  ∃ point : ∀ R : TestAlgebra F, Points H.val.X R ≃ {x : R ⊗[F] A // normAt hA b x = 1},
    (∀ R (x y : ((groupPointsFunctor F).obj H.val).obj R), (point R (x * y)).val = (point R x).val * (point R y).val) ∧
    ∀ {R S : TestAlgebra F} (f : R ⟶ S) (x : Points H.val.X R),
      (point S (mapPoints f x)).val =
        Algebra.TensorProduct.map f.hom (.id F A) (point R x).val

/-- The original group represents the two special unitary equations over
every commutative ground-field algebra. -/
def RepresentsUnitary {E A : Type u} [Field E] [Algebra F E] [Ring A]
    [Algebra F A] [Algebra E A] [IsScalarTower F E A] (hA : isCentralSimple E A)
    {ι : Type u} [Fintype ι] (b : Module.Basis ι E A) (star : SecondKind F E A)
    (H : AffineAlgebraicGroup F) : Prop :=
  ∃ point : ∀ R : TestAlgebra F, Points H.val.X R ≃ {x : (R ⊗[F] A)ˣ // IsSpecialUnitary hA b star x},
    (∀ R (x y : ((groupPointsFunctor F).obj H.val).obj R), (point R (x * y)).val = (point R x).val * (point R y).val) ∧
    ∀ {R S : TestAlgebra F} (f : R ⟶ S) (x : Points H.val.X R),
      (point S (mapPoints f x)).val =
        Units.map (Algebra.TensorProduct.map f.hom (.id F A)).toMonoidHom (point R x).val

/-- The matrix formula of the transported action on the original group
trivialization, including changes of test algebra above a field automorphism. -/
def HasMatrixTransport {G H : AffineAlgebraicGroup F} (s : SpecialMatrixPoints G n)
    (i : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val)
    (χ : DiagramCharacter F K) (g : Gal(K/F) → GL (Index.{u} n) K) : Prop :=
  ∀ σ {R S : TestAlgebra K} (f : (restrictTestAlgebra F K).obj R ⟶ (restrictTestAlgebra F K).obj S),
    IsSemilinearTestMap σ f → ∀ x y, IsTransportedPoint i f x y →
    let B := GeneralLinearGroup.map (algebraMap K S) (g σ)
    let X := baseChangeMatrix s R x
    (baseChangeMatrix s S y).val = B.val *
      (if χ σ = 1 then X.val.map f.hom.toRingHom else (X⁻¹).val.transpose.map f.hom.toRingHom) *
        (B⁻¹).val

/-- Classify the form with its original parity. In the nontrivial case the
centre is the fixed field of its even subgroup and the adjoint is the
restriction of each odd lift. -/
def HasTypeAModel [FiniteDimensional F K] [IsGalois F K] (H : AffineAlgebraicGroup F)
    (χ : DiagramCharacter F K) (β : ∀ σ : Gal(K/F), MatrixLift n σ (χ σ)) : Prop :=
  (χ = 1 →
    ∃ ρ : AlgebraAction F K (Mat K n),
      (∀ σ x, ρ.act σ x = (β σ).toAddEquiv x) ∧
      let A := ρ.fixedSubalgebra
      ∃ (hA : isCentralSimple F A), degree F A = n ∧
        ∃ (ι : Type u) (_ : Fintype ι) (b : Module.Basis ι F A), RepresentsNormOne hA b H) ∧
  (Function.Surjective χ →
    let E := DiagramField χ
    Module.finrank F E = 2 ∧ Algebra.IsSeparable F E ∧
    ∃ ρ : AlgebraAction E K (Mat K n),
      (∀ (σ : χ.ker) x, ρ.act (IntermediateField.subgroupEquivAlgEquiv χ.ker σ) x =
        (β σ.val).toAddEquiv x) ∧
      let A := ρ.fixedSubalgebra
      ∃ (hA : isCentralSimple E A), degree E A = n ∧
        ∃ star : SecondKind F E A,
          (∀ (σ : Gal(K/F)) (_ : χ σ ≠ 1) (x : A),
            ((star.adjoint x).unop : Mat K n) = (β σ).toAddEquiv x.val) ∧
          (∀ (σ : Gal(K/F)) (_ : χ σ ≠ 1) (a : E), (star.conjugation a : K) = σ (a : K)) ∧
          ∃ (ι : Type u) (_ : Fintype ι) (b : Module.Basis ι E A), RepresentsUnitary hA b star H)

/-- The descended model associated to the given matrix trivialization. -/
def MatrixModelAt [FiniteDimensional F K] [IsGalois F K]
    {G H : AffineAlgebraicGroup F} (s : SpecialMatrixPoints G n)
    (i : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val) : Prop :=
  ∃ (χ : DiagramCharacter F K) (g : Gal(K/F) → GL (Index.{u} n) K)
    (β : ∀ σ : Gal(K/F), MatrixLift n σ (χ σ)),
    HasMatrixTransport s i χ g ∧
    (∀ χ' g', HasMatrixTransport s i χ' g' → χ' = χ) ∧
    (∀ σ x, (β σ).toAddEquiv x =
      (g σ).val.submatrix ULift.up ULift.up *
        (if χ σ = 1 then x.map σ else (x.map σ).transpose) *
          (g σ)⁻¹.val.submatrix ULift.up ULift.up) ∧
    (∀ x, (β 1).toAddEquiv x = x) ∧
    (∀ σ τ x, (β (σ * τ)).toAddEquiv x = (β σ).toAddEquiv ((β τ).toAddEquiv x)) ∧
    (χ = 1 ∨ Function.Surjective χ) ∧ HasTypeAModel H χ β

/-- Assemble the matrix action and the group-scheme model for any finite
Galois splitting of the given form. -/
def TypeAModelForTrivialization : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    {n : ℕ}, 3 ≤ n → ∀ {G H : AffineAlgebraicGroup F} (s : SpecialMatrixPoints G n)
    (i : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val),
    MatrixModelAt s i

/-- Every separable form is covered by the finite-level comparison. -/
def TypeAForms : Prop :=
  ∀ {F : Type u} [Field F] {n : ℕ}, 3 ≤ n →
    ∀ {G H : AffineAlgebraicGroup F} (s : SpecialMatrixPoints G n), IsSeparableForm G H →
    ∃ (K : Type u) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K) (_ : IsGalois F K)
      (i : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val),
      MatrixModelAt s i

/-- A chosen embedding of the quadratic centre in `L` selects the factor of
the extended algebra whose reduced-norm-one group is the base change of the form. -/
def SplitCentreTypeAModel : Prop :=
  ∀ {F E A L : Type u} [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    [Field L] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
    [Ring A] [Algebra F A] [Algebra E A] [IsScalarTower F E A]
    (hA : isCentralSimple E A) {ι : Type u} [Fintype ι] (b : Module.Basis ι E A)
    (star : SecondKind F E A) {H : AffineAlgebraicGroup F},
    RepresentsUnitary hA b star H →
    ∃ hL : isCentralSimple L (L ⊗[E] A),
      degree L (L ⊗[E] A) = degree E A ∧
      RepresentsNormOne hL (b.baseChange L) (Unipotent.baseChangedAlgebraicGroup L H)

/-- Absolute type and simple connectedness are measured on the full root
datum of a split Borel pair over a separable closure. -/
def HasAbsoluteSimplyConnectedTypeA (r : ℕ) (H : AffineAlgebraicGroup F) : Prop :=
  ∃ (L : Type u) (_ : Field L) (_ : Algebra F L) (_ : IsSepClosure F L)
    (P : Pinning.SplitBorelPair L),
    P.G = Unipotent.baseChangedAlgebraicGroup L H ∧
    GeometricRadicals.IsSemisimple P.G ∧ SimplyConnectedLattice.GeometricallySimplyConnected P.G ∧
      ∃ (D : Pinning.AttachedDatum P) (e : Fin r ≃ D.toBased.base.support),
        ∀ i j : Fin r, D.toBased.datum.pairing (e i) (e j) =
          if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0

/-- The actual integral datum identifies the group with the split matrix
group after passage to the separable closure. -/
def AbsoluteTypeAMatrixForm : Prop :=
  ∀ {F : Type u} [Field F] {r : ℕ} {G H : AffineAlgebraicGroup F}
    (_s : SpecialMatrixPoints G (r + 1)),
    HasAbsoluteSimplyConnectedTypeA r H → IsSeparableForm G H

/-- The inner and outer scheme models for simply connected groups of
absolute type A with at least two simple roots. -/
def AbsoluteTypeAForms : Prop :=
  ∀ {F : Type u} [Field F] {r : ℕ}, 2 ≤ r →
    ∀ (H : AffineAlgebraicGroup F), HasAbsoluteSimplyConnectedTypeA r H →
    ∃ (G : AffineAlgebraicGroup F) (s : SpecialMatrixPoints G (r + 1))
      (K : Type u) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K) (_ : IsGalois F K)
      (i : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val),
      MatrixModelAt s i

end Forms

end LinearAlgebraicGroups.Specs.OuterTypeAModels
