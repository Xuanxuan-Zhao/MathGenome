import Mathlib.RingTheory.Length
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Multiset.AddSub

/-!
Independent interfaces for paper.tex 536–565 (Jordan–Hölder and length).
The ring is associative and unital, with neither commutativity nor nontriviality
assumed. Taking the scalar ring to be an opposite ring gives right modules.
A full composition series is a Mathlib `CompositionSeries (Submodule R M)`
with head bottom and last top. Its steps are strict covers; thus its factors
are the nonzero simple modules `CompositionFactor R M s i`.
Isomorphism classes below identify modules by actual R-linear equivalences.
Their multiset records every factor, including its multiplicity.
-/

universe u v

namespace P103.Ch02.FiniteLength

/-- The upper term modulo the preceding term, viewed inside that upper term. -/
abbrev CompositionFactor (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :=
  s i.succ ⧸ (s i.castSucc).comap (s i.succ).subtype

/-- Equality of classes means isomorphism as R-modules, not equal cardinality. -/
def moduleIsomorphismSetoid (R : Type u) [Ring R] : Setoid (ModuleCat.{v} R) where
  r X Y := Nonempty (X ≃ₗ[R] Y)
  iseqv := ⟨fun _ => ⟨LinearEquiv.refl R _⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Multiset of isomorphism classes of all successive quotient modules. -/
noncomputable def compositionFactors (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    (s : CompositionSeries (Submodule R M)) :
    Multiset (Quotient (moduleIsomorphismSetoid.{u, v} R)) :=
  ∑ i : Fin s.length,
    Multiset.ofList [Quotient.mk (moduleIsomorphismSetoid R)
      (ModuleCat.of R (CompositionFactor R M s i))]

end P103.Ch02.FiniteLength

namespace P103.Specs.Ch02.FiniteLength

open P103.Ch02.FiniteLength

def composition_series_iffType : Prop :=
  ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M],
    (∃ s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤) ↔
      IsNoetherian R M ∧ IsArtinian R M

def composition_factor_simpleType : Prop :=
  ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length),
    IsSimpleModule R (CompositionFactor R M s i)

def composition_factor_nonzeroType : Prop :=
  ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length),
    Nontrivial (CompositionFactor R M s i)

def module_class_eq_iffType : Prop :=
  ∀ (R : Type u) [Ring R] (X Y : ModuleCat.{v} R),
    Quotient.mk (moduleIsomorphismSetoid R) X =
      Quotient.mk (moduleIsomorphismSetoid R) Y ↔ Nonempty (X ≃ₗ[R] Y)

def jordan_holder_isomorphismsType : Prop :=
  ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (s t : CompositionSeries (Submodule R M))
    (_hs₀ : s.head = ⊥) (_hs₁ : s.last = ⊤)
    (_ht₀ : t.head = ⊥) (_ht₁ : t.last = ⊤),
    ∃ e : Fin s.length ≃ Fin t.length, ∀ i,
      Nonempty (CompositionFactor R M s i ≃ₗ[R] CompositionFactor R M t (e i))

def compositionFactors_eqType : Prop :=
  ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (s t : CompositionSeries (Submodule R M))
    (_hs₀ : s.head = ⊥) (_hs₁ : s.last = ⊤)
    (_ht₀ : t.head = ⊥) (_ht₁ : t.last = ⊤),
    compositionFactors R M s = compositionFactors R M t

/-- A natural-number length, defined without choosing a series.
Outside finite-length modules the value is immaterial; all series and additivity
statements below impose the original finite-length hypotheses. -/
noncomputable def lengthValue (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] : ℕ :=
  (Module.length R M).toNat

def lengthType := ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M], ℕ

def length_eq_seriesType : Prop :=
  ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (s : CompositionSeries (Submodule R M)) (_hs₀ : s.head = ⊥) (_hs₁ : s.last = ⊤),
    lengthValue R M = s.length

def length_add_short_exactType : Prop :=
  ∀ (R A B C : Type*) [Ring R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (_hf : Function.Injective f) (_he : Function.Exact f g) (_hg : Function.Surjective g)
    (_hA : IsFiniteLength R A) (_hB : IsFiniteLength R B) (_hC : IsFiniteLength R C),
    lengthValue R B = lengthValue R A + lengthValue R C

def length_zeroType : Prop :=
  ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] [Subsingleton M],
    lengthValue R M = 0

end P103.Specs.Ch02.FiniteLength
