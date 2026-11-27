import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.KahlerDifferentials
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.SemifreeAlgebras
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.IndexedSemiFree

open CategoryTheory
open CochainComplex.HomComplex (δ)
open scoped DirectSum

universe u v

namespace DerivedFormalization.Affine.SemifreeDifferentials

open Semifree (Variables StagedPresentation variableTerm)
open Kahler (Derivation DifferentialModel value)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom homComplex component compose ofStrict)
open Specs.DerivedFormalization.Affine.Tensor
  (act term ModuleTensor regular)
open Specs.DerivedFormalization.DG.IndexedSemiFree (Presentation)

noncomputable section

variable {k : Type u} [Field k] [CharZero k]

/-- The finite-support homogeneous coefficients of the right multiples of the variables. -/
abbrev Coefficients (B : CommDGAlgebra.{u,v} k) (V : Variables.{v}) (n : ℤ) :=
  ⨁ x : V.Index, B.complex.X (n + -V.degree x)

def multiples {B : CommDGAlgebra.{u,v} k} {V : Variables.{v}} {M : B.Module}
    (e : ∀ x, term M (V.degree x)) (n : ℤ) : Coefficients B V n →ₗ[k] term M n := by
  classical
  exact DirectSum.toModule k _ _ fun x => act M (V.degree x) (n + -V.degree x) n (by omega) (e x)

/-- The basis consists of the indicated elements, using their actual right multiples. -/
def IsGradedBasis {B : CommDGAlgebra.{u,v} k} {V : Variables.{v}} {M : B.Module}
    (e : ∀ x, term M (V.degree x)) : Prop :=
  ∀ n, Function.Bijective (multiples e n)

def level (V : Variables.{v}) (x : V.Index) : ℕ := (-V.degree x).toNat

/-- A presentation of the original module in which stage `l` attaches the
generators of level `l`. The stage numbered zero is the initial zero module. -/
def HasCellPresentation {B : CommDGAlgebra.{u,v} k} {V : Variables.{v}}
    {M : B.Module} (e : ∀ x, term M (V.degree x)) : Prop :=
  ∃ (F : Presentation.{u,v,0,v} M) (index : ∀ l, F.index l ≃ {x : V.Index // level V x = l}),
    (∀ l (s : F.index l), (F.family l).degree s = V.degree (index l s).val) ∧
    ∀ l (s : F.index l),
      HEq (((F.into (l+1)).app ()).f ((F.family l).degree s)
        ((F.extension l).generator s)) (e (index l s).val)

variable {A P : NonpositiveCDGA.{u,v} k} {V : Variables.{v}} {f : A ⟶ P}

/-- The element `∂x` in the actual representing module. -/
abbrev generator (E : StagedPresentation A V f)
    (O : DifferentialModel (f : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra)) (x : V.Index) :
    term O.module (V.degree x) :=
  value O.symbol (V.degree x) (V.degree x) (add_zero _)
    (E.component _ (variableTerm A V x))

def SemifreeBasis : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {A P : NonpositiveCDGA.{u,v} k} {V : Variables.{v}} {f : A ⟶ P}
    (E : StagedPresentation A V f) (O : DifferentialModel
      (f : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra)),
    ∃ basis : IsGradedBasis (generator E O),
      (∀ x, ((O.module.complex ()).d (V.degree x) (V.degree x+1)) (generator E O x) =
        value O.symbol (V.degree x+1) (V.degree x+1) (add_zero _)
          (P.complex.d (V.degree x) (V.degree x+1) (E.component _ (variableTerm A V x)))) ∧
      (∀ x y, (LinearEquiv.ofBijective _ (basis (V.degree x+1))).symm
        (((O.module.complex ()).d (V.degree x) (V.degree x+1)) (generator E O x)) y ≠ 0 →
          level V y < level V x) ∧
      HasCellPresentation (generator E O)

/-- On coefficients of a right graded basis, scalar extension applies the
given algebra map in each degree. -/
def changeCoefficients {P B : CommDGAlgebra.{u,v} k} (g : P ⟶ B)
    (V : Variables.{v}) (n : ℤ) : Coefficients P V n →ₗ[k] Coefficients B V n :=
  DirectSum.lmap fun x => (g.chainMap.f (n + -V.degree x)).hom

def SemifreeAfterBaseChange : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k)
    {A P : NonpositiveCDGA.{u,v} k} {V : Variables.{v}} {f : A ⟶ P}
    (E : StagedPresentation A V f) (O : DifferentialModel
      (f : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra))
    {B : CommDGAlgebra.{u,v} k} (g : P.toCommDGAlgebra ⟶ B),
    T.Formulas g (regular B) →
    let e : ∀ x, term (T.obj g O.module (regular B)) (V.degree x) := fun x =>
      T.tmul g (V.degree x) 0 (V.degree x) (add_zero _) (generator E O x) B.one
    ∃ (basis : IsGradedBasis (generator E O)) (baseChangedBasis : IsGradedBasis e),
      HasCellPresentation e ∧
      (∀ n (a : Coefficients P.toCommDGAlgebra V n),
        multiples e n (changeCoefficients g V n a) =
          T.tmul g n 0 n (add_zero n) (multiples (generator E O) n a) B.one) ∧
      (∀ x, (LinearEquiv.ofBijective _ (baseChangedBasis (V.degree x+1))).symm
          (((T.obj g O.module (regular B)).complex ()).d (V.degree x) (V.degree x+1) (e x)) =
        changeCoefficients g V (V.degree x+1)
          ((LinearEquiv.ofBijective _ (basis (V.degree x+1))).symm
            (((O.module.complex ()).d (V.degree x) (V.degree x+1)) (generator E O x))))

/-- The representing isomorphism evaluates module maps on the universal
symbol, with the graded commutator on derivations. -/
structure HomDerivationComparison {Q P : CommDGAlgebra.{u,v} k} {g : Q ⟶ P}
    (O : DifferentialModel g) (M : P.Module) where
  cochains : ModuleCochain.{u,v} k
  derivations (r : ℤ) : cochains.X r ≃ₗ[k] Derivation g M r
  identification : cochains ≅ homComplex O.module M
  commutator (r : ℤ) (D : cochains.X r) :
    (derivations (r+1) (cochains.d r (r+1) D)).val = δ r (r+1) (derivations r D).val
  evaluation (r i p : ℤ) (h : i+r=p) (D : cochains.X r) (x : P.complex.X i) :
    component (identification.hom.f r D) () i p h (value O.symbol i i (add_zero i) x) =
      value (derivations r D) i p h x

abbrev HomDerivationComparison.readout {Q P : CommDGAlgebra.{u,v} k} {g : Q ⟶ P}
    {O : DifferentialModel g} {M : P.Module} (C : HomDerivationComparison O M)
    {r : ℤ} (F : gradedHom O.module M r) : Derivation g M r :=
  C.derivations r (C.identification.inv.f r F)

def HomDerivations : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {A P : NonpositiveCDGA.{u,v} k} (f : A ⟶ P),
    ∃ (O : DifferentialModel (f : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra))
      (coordinates : ∀ n, term O.module n ≃ₗ[k] Kahler.QuotientModel.Degree
        (f : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra) n)
      (C : ∀ M : P.Module, HomDerivationComparison O M),
      (∀ n (x : P.complex.X n), coordinates n (value O.symbol n n (add_zero n) x) =
        Kahler.QuotientModel.symbolClass (f : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra) n x) ∧
      ∀ (M N : P.Module) (b : M ⟶ N) (r : ℤ) (F : gradedHom O.module M r)
        (i p : ℤ) (h : i+r=p) (x : P.complex.X i),
        value ((C N).readout (compose O.module M N 0 r r (zero_add r) (ofStrict b) F)) i p h x =
          ((b.app ()).f p) (value ((C M).readout F) i p h x)

end
end DerivedFormalization.Affine.SemifreeDifferentials
