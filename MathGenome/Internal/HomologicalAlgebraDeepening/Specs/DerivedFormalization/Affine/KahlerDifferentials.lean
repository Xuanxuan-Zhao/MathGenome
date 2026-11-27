import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.Tensor
import Mathlib.Algebra.DirectSum.Module

open CategoryTheory
open CochainComplex.HomComplex

universe u v

namespace DerivedFormalization.Affine.Kahler

open Specs.DerivedFormalization.Affine.Tensor (term act signedLeft restrict regular ModuleTensor)
open Specs.DerivedFormalization.DG.HomComplex (Family RightLinear gradedHom component homComplex)

variable {k : Type u} [Field k] [CharZero k]
variable {A Q : CommDGAlgebra.{u,v} k}

/-- The relative graded Leibniz and scalar relations. In the right-module
formula the sign in the second term is independent of the degree of the
derivation: the latter sign cancels when converting the left action. -/
structure IsDerivation (f : A ⟶ Q) {M : Q.Module} {r : ℤ}
    (D : Cochain Q.complex (M.complex ()) r) : Prop where
  relative (i p : ℤ) (h : i+r=p) (a : A.complex.X i) :
    D.v i p h (f.chainMap.f i a) = 0
  leibniz (i j n ir jr nr : ℤ) (h : i+j=n)
      (hi : i+r=ir) (hj : j+r=jr) (hn : n+r=nr)
      (x : Q.complex.X i) (y : Q.complex.X j) :
    D.v n nr hn (Q.mul i j n h x y) =
      act M ir j nr (by omega) (D.v i ir hi x) y +
        (i*j).negOnePow • act M jr i nr (by omega) (D.v j jr hj y) x

def derivationSubmodule (f : A ⟶ Q) (M : Q.Module) (r : ℤ) :
    Submodule k (Cochain Q.complex (M.complex ()) r) where
  carrier := {D | IsDerivation f D}
  zero_mem' := by
    constructor <;> intros <;> simp
  add_mem' := by
    intro D E hD hE
    constructor
    · intro i p h a
      simp only [Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply]
      rw [hD.relative i p h a, hE.relative i p h a, add_zero]
    · intro i j n ir jr nr h hi hj hn x y
      simp only [Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply, map_add,
        hD.leibniz i j n ir jr nr h hi hj hn x y,
        hE.leibniz i j n ir jr nr h hi hj hn x y, smul_add]
      abel
  smul_mem' := by
    intro c D hD
    constructor
    · intro i p h a
      simp only [Cochain.smul_v, ModuleCat.hom_smul, LinearMap.smul_apply]
      rw [hD.relative i p h a, smul_zero]
    · intro i j n ir jr nr h hi hj hn x y
      simp only [Cochain.smul_v, ModuleCat.hom_smul, LinearMap.smul_apply, map_smul,
        hD.leibniz i j n ir jr nr h hi hj hn x y, smul_add, Units.smul_def]
      rw [smul_comm c ((i*j).negOnePow : ℤ)]

abbrev Derivation (f : A ⟶ Q) (M : Q.Module) (r : ℤ) :=
  ↥(derivationSubmodule f M r)

abbrev value {f : A ⟶ Q} {M : Q.Module} {r : ℤ} (D : Derivation f M r)
    (i p : ℤ) (h : i+r=p) := D.val.v i p h

namespace QuotientModel

open scoped DirectSum Classical
noncomputable section

variable {f : A ⟶ Q} {M : Q.Module} {r : ℤ}

abbrev Index (Q : CommDGAlgebra.{u,v} k) := Σ i : ℤ, Q.complex.X i
abbrev Coeff (Q : CommDGAlgebra.{u,v} k) (n : ℤ) (p : Index Q) : Type v :=
  Q.complex.X (n-p.1)
abbrev Raw (Q : CommDGAlgebra.{u,v} k) (n : ℤ) := ⨁ p : Index Q, Coeff Q n p

def single (Q : CommDGAlgebra.{u,v} k) (i j n : ℤ) (h : i+j=n)
    (x : Q.complex.X i) : Q.complex.X j →ₗ[k] Raw Q n := by
  obtain rfl : j = n-i := by omega
  exact DirectSum.lof k (Index Q) (Coeff Q n) ⟨i, x⟩

theorem raw_ext {n : ℤ} {P : Type*} [AddCommGroup P] [Module k P]
    {F G : Raw Q n →ₗ[k] P}
    (e : ∀ (i j : ℤ) (h : i+j=n) (x : Q.complex.X i) (y : Q.complex.X j),
      F (single Q i j n h x y) = G (single Q i j n h x y)) : F = G := by
  apply DirectSum.linearMap_ext
  rintro ⟨i, x⟩
  exact LinearMap.ext (e i (n-i) (by omega) x)

def evalRaw (D : Derivation f M r) (n p : ℤ) (h : n+r=p) :
    Raw Q n →ₗ[k] term M p :=
  DirectSum.toModule k (Index Q) _ fun ⟨i,x⟩ =>
    act M (i+r) (n-i) p (by omega) (value D i (i+r) rfl x)

theorem evalRaw_single (D : Derivation f M r) (i j n ir p : ℤ)
    (h : i+j=n) (hi : i+r=ir) (hp : n+r=p) (x : Q.complex.X i) (y : Q.complex.X j) :
    evalRaw D n p hp (single Q i j n h x y) =
      act M ir j p (by omega) (value D i ir hi x) y := by
  obtain rfl : j=n-i := by omega
  subst ir
  change (DirectSum.toModule k (Index Q) (term M p) _)
    (DirectSum.lof k (Index Q) (Coeff Q n) ⟨i, x⟩ y) = _
  rw [DirectSum.toModule_lof]

/-- Impose precisely the relations detected by homogeneous relative derivations.
The resulting module still lies in the universe of the algebra terms. -/
def relations (f : A ⟶ Q) (n : ℤ) : Submodule k (Raw Q n) where
  carrier := {z | ∀ (M : Q.Module) (r : ℤ) (D : Derivation f M r),
    evalRaw D n (n+r) rfl z = 0}
  zero_mem' M r D := map_zero _
  add_mem' {x y} hx hy M r D := by
    rw [map_add, hx M r D, hy M r D, add_zero]
  smul_mem' c x hx M r D := by
    rw [map_smul, hx M r D, smul_zero]

abbrev Degree (f : A ⟶ Q) (n : ℤ) := Raw Q n ⧸ relations f n
abbrev mkDegree (f : A ⟶ Q) (n : ℤ) := (relations f n).mkQ

/-- The class of the homogeneous symbol with unit coefficient. -/
def symbolClass (f : A ⟶ Q) (n : ℤ) (x : Q.complex.X n) : Degree f n :=
  mkDegree f n (single Q n 0 n (add_zero n) x Q.one)

end
end QuotientModel

set_option linter.checkUnivs false in
def OmegaDegreeType :=
  ∀ {k : Type u} [Field k] [CharZero k] {A Q : CommDGAlgebra.{u,v} k}, (A ⟶ Q) → ℤ → Type v

set_option linter.checkUnivs false in
def UniversalSymbolType :=
  ∀ {k : Type u} [Field k] [CharZero k] {A Q : CommDGAlgebra.{u,v} k}
    (f : A ⟶ Q) (n : ℤ), Q.complex.X n → QuotientModel.Degree f n

/-- The Koszul left-module form of the same derivation rule. -/
def KoszulRule : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A Q : CommDGAlgebra.{u,v} k}
    (f : A ⟶ Q) (M : Q.Module) (r : ℤ) (D : Cochain Q.complex (M.complex ()) r),
    IsDerivation f D ↔
      (∀ i p (h : i+r=p) a, D.v i p h (f.chainMap.f i a) = 0) ∧
      (∀ i j n ir jr nr (h : i+j=n) (hi : i+r=ir) (hj : j+r=jr) (hn : n+r=nr) x y,
        D.v n nr hn (Q.mul i j n h x y) =
          act M ir j nr (by omega) (D.v i ir hi x) y +
            (r*i).negOnePow • signedLeft M i jr nr (by omega) x (D.v j jr hj y))

/-- Right-linear homogeneous maps become Koszul-linear for the induced left actions. -/
def KoszulLinearity : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {Q : CommDGAlgebra.{u,v} k}
    (M N : Q.Module) (r : ℤ) (F : Family M N r),
    RightLinear F ↔
      ∀ (i j n ir nr : ℤ) (h : i+j=n) (hi : i+r=ir) (hn : n+r=nr)
        (x : term M i) (a : Q.complex.X j),
        (F ()).v n nr hn (signedLeft M j i n (by omega) a x) =
          (r*j).negOnePow • signedLeft N j ir nr (by omega) a ((F ()).v i ir hi x)

/-- Construction and universal property for a concrete module and its symbol map. -/
structure DifferentialModel (f : A ⟶ Q) where
  module : Q.Module
  symbol : Derivation f module 0
  closed : δ 0 1 symbol.val = 0
  represents (M : Q.Module) (r : ℤ) :
    ∀ D : Derivation f M r, ∃! F : gradedHom module M r,
      ∀ i p (h : i+r=p) (x : Q.complex.X i),
        component F () i p h (value symbol i i (add_zero i) x) = value D i p h x

variable {f : A ⟶ Q}

/-- The canonical representing equivalence identifies the two cochain complexes. -/
def DifferentialModel.RepresentsComplex (O : DifferentialModel f) (M : Q.Module) : Prop :=
  ∃ (C : ModuleCochain.{u,v} k)
    (e : ∀ r : ℤ, C.X r ≃ₗ[k] Derivation f M r)
    (I : C ≅ homComplex O.module M),
    (∀ (r : ℤ) (D : C.X r),
      (e (r+1) (C.d r (r+1) D)).val = δ r (r+1) (e r D).val) ∧
    (∀ (r i p : ℤ) (h : i+r=p) (D : C.X r) (x : Q.complex.X i),
      component (I.hom.f r D) () i p h (value O.symbol i i (add_zero i) x) =
        value (e r D) i p h x)

/-- The comparison in a square is determined by the pullback of the
target universal derivation and scalar extension on homogeneous tensors. -/
def DifferentialModel.SquareComparison {A' Q' : CommDGAlgebra.{u,v} k}
    {f' : A' ⟶ Q'} (T : ModuleTensor.{u,v} k) (O : DifferentialModel f)
    (O' : DifferentialModel f') (g : Q ⟶ Q') : Prop :=
  ∃! c : T.obj g O.module (regular Q') ⟶ O'.module,
    ∀ (i j n : ℤ) (h : i+j=n) (x : Q.complex.X i) (b : Q'.complex.X j),
      (c.app ()).f n (T.tmul g (N := regular Q') i j n h
        (value O.symbol i i (add_zero i) x) b) =
      act O'.module i j n h (value O'.symbol i i (add_zero i) (g.chainMap.f i x)) b

/-- Relative differentials for every cdga map, with an all-degree representation
and the canonical comparisons. The case of a common base takes its identity map. -/
def DifferentialsConstruction : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    ∃ (T : ModuleTensor.{u,v} k)
      (O : ∀ {A Q : CommDGAlgebra.{u,v} k} (f : A ⟶ Q), DifferentialModel f),
    (∀ {Q Q' : CommDGAlgebra.{u,v} k} (g : Q ⟶ Q'), T.Formulas g (regular Q')) ∧
    (∀ {A Q : CommDGAlgebra.{u,v} k} (f : A ⟶ Q) (i : ℤ) (x : Q.complex.X i),
      ((O f).module.complex ()).d i (i+1) (value (O f).symbol i i (add_zero i) x) =
        value (O f).symbol (i+1) (i+1) (add_zero (i+1)) (Q.complex.d i (i+1) x)) ∧
    (∀ {A Q : CommDGAlgebra.{u,v} k} (f : A ⟶ Q) (M : Q.Module),
      (O f).RepresentsComplex M) ∧
    (∀ {A Q A' Q' : CommDGAlgebra.{u,v} k} (f : A ⟶ Q) (f' : A' ⟶ Q')
      (a : A ⟶ A') (g : Q ⟶ Q'), f ≫ g = a ≫ f' →
      (O f).SquareComparison T (O f') g)

end DerivedFormalization.Affine.Kahler
