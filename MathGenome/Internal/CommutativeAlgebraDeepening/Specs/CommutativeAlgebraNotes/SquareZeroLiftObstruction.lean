import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SquareZeroLiftGraph
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.ULift

/-! The conormal obstruction to lifting across a square-zero extension. -/

noncomputable section

namespace CommutativeAlgebraNotes.SquareZeroLift.Presentation

open CategoryTheory Abelian Algebra.Extension

universe u v w t n z

/-- A linear map transported to the universe lifts of its domain and codomain. -/
def uliftLinearMap {R M M' : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid M']
    [Module R M] [Module R M'] (f : M →ₗ[R] M') : ULift.{z} M →ₗ[R] ULift.{z} M' :=
  ULift.moduleEquiv.symm.toLinearMap.comp (f.comp ULift.moduleEquiv.toLinearMap)

variable {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
  [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
  (p : Presentation e B σ)

/-- The coefficient map descends along the canonical surjection `IP' → K`. -/
def FactorsThrough (c : e.CoefficientMap (B := B) N) (κ : p.K →ₗ[B] N) : Prop :=
  ∀ i : p.IP, κ (p.toK i) = p.prescribed c i

/-- The map on `K` is the restriction of a `B`-linear map on `Q/Q²`. -/
def Extends (κ : p.K →ₗ[B] N) : Prop :=
  ∃ ρ : p.Conormal →ₗ[B] N, ρ.comp p.K.subtype = κ

/-- The conormal sequence with the inclusion and the natural reduction modulo `IP'`.
The modules are transported by their canonical linear equivalences to a common universe. -/
def conormalSequence : ShortComplex (ModuleCat.{max u w t n} B) :=
  ShortComplex.moduleCatMk
    (uliftLinearMap.{max u w t n} p.K.subtype)
    (uliftLinearMap.{max u w t n} p.conormalReduction) (by
      apply LinearMap.ext
      intro x
      obtain ⟨i, hi⟩ := (p.mem_K (x.down : p.Conormal)).mp x.down.property
      have hz : p.conormalReduction (x.down : p.Conormal) = 0 := by
        rw [← hi]
        let q : p.J := ⟨p.reduce i.val, p.IP_le_Q i.property⟩
        change Cotangent.mk q = 0
        have hq : q = 0 := Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.mpr i.property)
        rw [hq, map_zero]
      exact congrArg ULift.up hz)

/-- The connecting class in `Ext¹_B(J/J², N)` of a map from `K`. -/
def connectingClass (h : p.conormalSequence.{u,v,w,t,n}.ShortExact) (κ : p.K →ₗ[B] N) :
    Ext.{max u w t n} p.conormalSequence.{u,v,w,t,n}.X₃
      (ModuleCat.of B (ULift.{max u w t n} N)) 1 :=
  Ext.δ h 0 1 rfl (Ext.mk₀ (ModuleCat.ofHom (uliftLinearMap.{max u w t n} κ)))

end CommutativeAlgebraNotes.SquareZeroLift.Presentation

namespace Specs.CommutativeAlgebraNotes.SquareZeroLiftObstruction

open CommutativeAlgebraNotes.SquareZeroLift

universe u v w t n l s

/-- A factorization of the prescribed map through `K` is unique if it exists. -/
def factorsThroughUniqueType : Prop :=
  ∀ {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
    [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
    (p : Presentation e B σ) {c : e.CoefficientMap (B := B) N}
    {κ κ' : p.K →ₗ[B] N},
    p.FactorsThrough c κ → p.FactorsThrough c κ' → κ = κ'

/-- Every lift, in any universe, implies the criterion for the given presentation. -/
def factorizationAndExtensionOfLiftType : Prop :=
  ∀ {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
    [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
    (p : Presentation e B σ) {c : e.CoefficientMap (B := B) N}
    (_L : Lift.{u,v,w,n,l} e c),
    ∃ κ : p.K →ₗ[B] N, p.FactorsThrough c κ ∧ p.Extends κ

/-- The criterion gives a lift in a universe independent of the presentation. -/
def liftIffFactorizationAndExtensionType : Prop :=
  ∀ {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
    [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
    (p : Presentation e B σ) (c : e.CoefficientMap (B := B) N),
    Nonempty (Lift.{u,v,w,n,max u w n} e c) ↔
      ∃ κ : p.K →ₗ[B] N, p.FactorsThrough c κ ∧ p.Extends κ

/-- The conormal sequence is short exact, and extension is equivalent to zero boundary. -/
def extensionIffConnectingClassEqZeroType : Prop :=
  ∀ {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
    [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] {e : BaseExtension A' A} (p : Presentation e B σ),
    ∃ h : p.conormalSequence.{u,v,w,t,n}.ShortExact,
      ∀ κ : p.K →ₗ[B] N, p.Extends κ ↔ p.connectingClass h κ = 0

/-- A lift exists exactly when the prescribed map descends and its connecting class vanishes. -/
def liftIffFactorizationAndVanishingType : Prop :=
  ∀ {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
    [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
    (p : Presentation e B σ) (c : e.CoefficientMap (B := B) N),
    ∃ h : p.conormalSequence.{u,v,w,t,n}.ShortExact,
      Nonempty (Lift.{u,v,w,n,max u w n} e c) ↔
        ∃ κ : p.K →ₗ[B] N, p.FactorsThrough c κ ∧ p.connectingClass h κ = 0

/-- The factorization and extension test has the same truth value for any two presentations. -/
def liftCriterionIndependentType : Prop :=
  ∀ {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {τ : Type s} {N : Type n}
    [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
    (p : Presentation e B σ) (q : Presentation e B τ)
    (c : e.CoefficientMap (B := B) N),
    (∃ κ : p.K →ₗ[B] N, p.FactorsThrough c κ ∧ p.Extends κ) ↔
      ∃ κ : q.K →ₗ[B] N, q.FactorsThrough c κ ∧ q.Extends κ

end Specs.CommutativeAlgebraNotes.SquareZeroLiftObstruction
