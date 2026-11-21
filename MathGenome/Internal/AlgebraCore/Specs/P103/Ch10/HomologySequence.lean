import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.Complexes
import Mathlib.Algebra.Exact.Basic

/-! Long exact sequences, paper.tex 2300–2336. The generic adjacent-degree
statement applies to both integer chain and integer cochain complexes. All
rings are unital, possibly noncommutative or zero; right modules use Rᵐᵒᵖ.
Homology and its maps are the upstream explicit quotient constructions. -/
namespace P103.Specs.Ch10.HomologySequence
open CategoryTheory P103.Specs.Ch10.Complexes
universe u v w
variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
variable {A B C : HomologicalComplex (ModuleCat.{v} R) c}

/-- Precisely degreewise short exactness, without a splitting assumption. -/
def DegreewiseExact (i : A ⟶ B) (p : B ⟶ C) : Prop :=
  ∀ n, Function.Injective (i.f n).hom ∧
    Function.Exact (i.f n).hom (p.f n).hom ∧ Function.Surjective (p.f n).hom

/-- Formula for every pair of lifts, fixing the positive sign and expressing
independence of both lifts and homology representatives. -/
def Connecting (i : A ⟶ B) (p : B ⟶ C) (n m : ι)
    (δ : Homology C n →ₗ[R] Homology A m) : Prop :=
  ∀ (z : cycles C n) (b : B.X n) (a : cycles A m),
    (p.f n).hom b = z.val → (i.f m).hom a.val = (B.d n m).hom b →
      δ (homologyClass C n z) = homologyClass A m a

/-- These three assertions, repeated in all degrees, are the entire long
exact sequence. No endpoint term is suppressed. -/
def SequenceExact (i : A ⟶ B) (p : B ⟶ C) (n m : ι)
    (δ : Homology C n →ₗ[R] Homology A m) : Prop :=
  Function.Exact (homologyMap i n) (homologyMap p n) ∧
  Function.Exact (homologyMap p n) δ ∧
  Function.Exact δ (homologyMap i m)

def sequenceType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex (ModuleCat.{v} R) c}
    (i : A ⟶ B) (p : B ⟶ C), DegreewiseExact i p →
    ∀ (n m : ι), c.Rel n m →
    ∃! δ : Homology C n →ₗ[R] Homology A m,
      Connecting i p n m δ ∧ SequenceExact i p n m δ

def chainSequenceType : Prop :=
  ∀ {R : Type u} [Ring R] {A B C : Chain.{u,v} R}
    (i : A ⟶ B) (p : B ⟶ C), DegreewiseExact i p →
    ∃ δ : ∀ n : ℤ, Homology C n →ₗ[R] Homology A (n - 1),
      ∀ n, Connecting i p n (n - 1) (δ n) ∧ SequenceExact i p n (n - 1) (δ n)

def cochainSequenceType : Prop :=
  ∀ {R : Type u} [Ring R] {A B C : Cochain.{u,v} R}
    (i : A ⟶ B) (p : B ⟶ C), DegreewiseExact i p →
    ∃ δ : ∀ n : ℤ, Homology C n →ₗ[R] Homology A (n + 1),
      ∀ n, Connecting i p n (n + 1) (δ n) ∧ SequenceExact i p n (n + 1) (δ n)

/-- Explicit specialization to the side convention for right modules. -/
def sequenceRightType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c}
    (i : A ⟶ B) (p : B ⟶ C), DegreewiseExact i p →
    ∀ (n m : ι), c.Rel n m →
    ∃! δ : Homology C n →ₗ[Rᵐᵒᵖ] Homology A m,
      Connecting i p n m δ ∧ SequenceExact i p n m δ

/-- All squares of the induced sequences commute, including the connecting
square, for every map of degreewise short exact sequences. -/
def naturalityType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex (ModuleCat.{v} R) c}
    {A' B' C' : HomologicalComplex (ModuleCat.{v} R) c}
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (α : A ⟶ A') (β : B ⟶ B') (γ : C ⟶ C')
    (_hi : i ≫ β = α ≫ i') (_hp : p ≫ γ = β ≫ p'),
    DegreewiseExact i p → DegreewiseExact i' p' →
    ∀ (n m : ι), c.Rel n m →
    ∀ (δ : Homology C n →ₗ[R] Homology A m)
      (ε : Homology C' n →ₗ[R] Homology A' m),
      Connecting i p n m δ → Connecting i' p' n m ε →
      (homologyMap β n).comp (homologyMap i n) =
        (homologyMap i' n).comp (homologyMap α n) ∧
      (homologyMap γ n).comp (homologyMap p n) =
        (homologyMap p' n).comp (homologyMap β n) ∧
      (homologyMap α m).comp δ = ε.comp (homologyMap γ n) ∧
      (homologyMap β m).comp (homologyMap i m) =
        (homologyMap i' m).comp (homologyMap α m) ∧
      (homologyMap γ m).comp (homologyMap p m) =
        (homologyMap p' m).comp (homologyMap β m)

/-- Terms outside any specified support range give actual zero homology terms. -/
def homologySupportedType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c) (s : Set ι),
    SupportedIn C s → ∀ n, n ∉ s → Subsingleton (Homology C n)

/-- Endpoint consequences apply in particular whenever the indicated complex
is supported away from that degree. They cover each of the three exact terms. -/
def zeroEndpointsType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex (ModuleCat.{v} R) c}
    (i : A ⟶ B) (p : B ⟶ C) (n m : ι)
    (δ : Homology C n →ₗ[R] Homology A m), SequenceExact i p n m δ →
    (Subsingleton (Homology A n) → Function.Injective (homologyMap p n)) ∧
    (Subsingleton (Homology C n) → Function.Surjective (homologyMap i n) ∧
      Function.Injective (homologyMap i m)) ∧
    (Subsingleton (Homology A m) → Function.Surjective (homologyMap p n)) ∧
    (Subsingleton (Homology B n) → Function.Injective δ) ∧
    (Subsingleton (Homology B m) → Function.Surjective δ)

end P103.Specs.Ch10.HomologySequence
