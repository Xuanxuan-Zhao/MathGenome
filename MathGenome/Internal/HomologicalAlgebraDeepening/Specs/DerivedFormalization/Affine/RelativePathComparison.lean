import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.KahlerDifferentials
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.PolynomialPath
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.SemifreeLifting

open CategoryTheory

universe u v

namespace Specs.DerivedFormalization.Affine.RelativePathComparison

open _root_.DerivedFormalization.Affine
open _root_.DerivedFormalization.Affine.Kahler (DifferentialModel value)
open Specs.DerivedFormalization.Affine.PolynomialPath
  (AlgebraPathModel RelativePathModel ModulePathModel mapCoefficients)
open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor regular term)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom component HomotopyEquation)

/-- Lift the prescribed pair through the relative endpoint fibration, with the
constant path on the base and the prescribed augmentation to B. -/
def RelativePathLifting : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A P Q B : NonpositiveCDGA.{u,v} k}
    (aP : A ⟶ P) (aQ : A ⟶ Q) (p : P ⟶ B) (q : Q ⟶ B)
    {U : AlgebraPathModel Q.toCommDGAlgebra} {V : AlgebraPathModel B.toCommDGAlgebra}
    (R : RelativePathModel q U V) (f₀ f₁ : P ⟶ Q),
    Semifree.IsSemifree A aP →
    NonpositiveCDGA.DegreewiseSurjective q → NonpositiveCDGA.IsQuasiIso q →
    aP ≫ f₀ = aQ → aP ≫ f₁ = aQ → f₀ ≫ q = p → f₁ ≫ q = p →
    ∃ H : P ⟶ R.truncated,
      aP ≫ H = aQ ≫ R.constants ∧
      H ≫ R.endpoints ≫ R.first = f₀ ∧
      H ≫ R.endpoints ≫ R.second = f₁ ∧
      H ≫ R.endpoints ≫ R.first ≫ q = p

section Comparison

variable {k : Type u} [Field k] [CharZero k]
variable {A P B : CommDGAlgebra.{u,v} k} {aP : A ⟶ P}

/-- The universal differential symbol followed by extension of scalars along p. -/
noncomputable def baseChangedSymbol (T : ModuleTensor.{u,v} k) (p : P ⟶ B)
    (O : DifferentialModel aP) (i : ℤ) :
    P.complex.X i →ₗ[k] term ((T.baseChange p).obj O.module) i where
  toFun x := T.tmul p (N := regular B) i 0 i (add_zero i)
    (value O.symbol i i (add_zero i) x) B.one
  map_add' x y := by
    simp only [ModuleTensor.tmul, Tensor.pure, DG.BalancedTensor.tmul,
      DG.BalancedTensor.rawTmul, map_add, TensorProduct.add_tmul]
  map_smul' c x := by
    simp only [RingHom.id_apply, ModuleTensor.tmul, Tensor.pure, DG.BalancedTensor.tmul,
      DG.BalancedTensor.rawTmul, map_smul, ← TensorProduct.smul_tmul']

end Comparison

/-- Apply the relative differential to the coefficients of a given path and
integrate. The base may change along a map A → A' as in a comparison of
resolved transitivity sequences. Both scalar extensions are to the same B. -/
def PathToCotangentHomotopy : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A A' P Q B : NonpositiveCDGA.{u,v} k}
    (a : A ⟶ A') (aP : A ⟶ P) (aQ : A' ⟶ Q) (p : P ⟶ B) (q : Q ⟶ B)
    {U : AlgebraPathModel Q.toCommDGAlgebra} {V : AlgebraPathModel B.toCommDGAlgebra}
    (R : RelativePathModel q U V) (H : P ⟶ R.truncated),
    aP ≫ H = a ≫ aQ ≫ R.constants →
    H ≫ R.endpoints ≫ R.first ≫ q = p →
    ∀ (T : ModuleTensor.{u,v} k)
      (OP : DifferentialModel (aP : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra))
      (OQ : DifferentialModel (aQ : A'.toCommDGAlgebra ⟶ Q.toCommDGAlgebra)),
    let p' : P.toCommDGAlgebra ⟶ B.toCommDGAlgebra := p
    let q' : Q.toCommDGAlgebra ⟶ B.toCommDGAlgebra := q
    let LP := (T.baseChange p').obj OP.module
    let LQ := (T.baseChange q').obj OQ.module
    T.Formulas p' (regular B.toCommDGAlgebra) →
    T.Formulas q' (regular B.toCommDGAlgebra) →
    ∀ W : ModulePathModel LQ,
    let hPath : P.toCommDGAlgebra ⟶ U.obj :=
      (H : P.toCommDGAlgebra ⟶ R.truncated.toCommDGAlgebra) ≫
      R.includeTruncation ≫ R.includeRelative
    let f₀ := H ≫ R.endpoints ≫ R.first
    let f₁ := H ≫ R.endpoints ≫ R.second
    ∃ F : LP ⟶ W.obj,
      (∀ (i : ℤ) (x : P.complex.X i),
        let z := U.coordinates i (hPath.chainMap.f i x)
        W.coordinates i ((F.app ()).f i (baseChangedSymbol T p' OP i x)) =
          (mapCoefficients (baseChangedSymbol T q' OQ i) z.1,
            mapCoefficients (baseChangedSymbol T q' OQ (i-1)) z.2)) ∧
      (∀ (f : P ⟶ Q) (c : k), (f = f₀ ∧ c = 0 ∨ f = f₁ ∧ c = 1) →
        ∀ (i j n : ℤ) (e : i+j=n) (x : P.complex.X i) (b : B.complex.X j),
          ((F ≫ W.evaluation c).app ()).f n
            (T.tmul p' (N := regular B.toCommDGAlgebra) i j n e
              (value OP.symbol i i (add_zero i) x) b) =
            T.tmul q' (N := regular B.toCommDGAlgebra) i j n e
              (value OQ.symbol i i (add_zero i) (f.chainMap.f i x)) b) ∧
      ∃ h : gradedHom LP LQ (-1),
        HomotopyEquation (F ≫ W.evaluation 1) (F ≫ W.evaluation 0) h ∧
        ∀ (i j : ℤ) (e : i+(-1)=j) (x : term LP i),
          component h () i j e x = component W.homotopy () i j e ((F.app ()).f i x)

end Specs.DerivedFormalization.Affine.RelativePathComparison
