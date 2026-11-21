import Mathlib.RingTheory.Regular.RegularSequence

/-! Independent specifications for paper.tex, RK-01 (including its following conventions).
Rings may be zero; modules need not be finite. Indices are zero-based, so take j
is the source ideal I_j and position i acts on the quotient by I_i. -/

universe u v
open scoped Pointwise
namespace AdvCommAlg.RegularSequence.Specs

def prefixIdealType := ∀ {R : Type u} [CommRing R], List R → ℕ → Ideal R

def prefixIdealValue : prefixIdealType.{u} :=
  fun {_} _ x j => Ideal.ofList (x.take j)

def PrefixQuotientType := ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], List R → ℕ → Type v

def PrefixQuotientValue : PrefixQuotientType.{u, v} :=
  fun {R} _ M _ _ x j => M ⧸ (Ideal.ofList (x.take j) • ⊤ : Submodule R M)

def WeaklyRegularType := ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], List R → Prop

def WeaklyRegularValue : WeaklyRegularType.{u, v} :=
  fun {_} _ M _ _ => RingTheory.Sequence.IsWeaklyRegular M

def RegularType := ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], List R → Prop

def RegularValue : RegularType.{u, v} :=
  fun {_} _ M _ _ => RingTheory.Sequence.IsRegular M

def RingRegularType := ∀ {R : Type u} [CommRing R], List R → Prop

def RingRegularValue : RingRegularType.{u} :=
  fun {R} _ => RingTheory.Sequence.IsRegular R

def prefixIdeal_eq_spanType : Prop :=
  ∀ {R : Type u} [CommRing R] (x : List R) (j : ℕ), prefixIdealValue x j = Ideal.span {a | a ∈ x.take j}

def prefixIdeal_zeroType : Prop :=
  ∀ {R : Type u} [CommRing R] (x : List R), prefixIdealValue x 0 = ⊥

def weaklyRegular_iff_injectiveType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], ∀ (x : List R), RingTheory.Sequence.IsWeaklyRegular M x ↔
  ∀ i : Fin x.length, Function.Injective
    (fun q : M ⧸ (Ideal.ofList (x.take i.val) • ⊤ : Submodule R M) => x[i.val] • q)

def regular_iff_injective_nonzeroType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], ∀ (x : List R), RingTheory.Sequence.IsRegular M x ↔
  (∀ i : Fin x.length, Function.Injective
    (fun q : M ⧸ (Ideal.ofList (x.take i.val) • ⊤ : Submodule R M) => x[i.val] • q)) ∧
  Nontrivial (M ⧸ (Ideal.ofList x • ⊤ : Submodule R M))

def weaklyRegular_nilType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], RingTheory.Sequence.IsWeaklyRegular M ([] : List R)

def regular_nil_iffType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], RingTheory.Sequence.IsRegular M ([] : List R) ↔ Nontrivial M

def weaklyRegular_of_subsingletonType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], ∀ [Subsingleton M] (x : List R), RingTheory.Sequence.IsWeaklyRegular M x

def not_regular_of_subsingletonType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], ∀ [Subsingleton M] (x : List R), ¬ RingTheory.Sequence.IsRegular M x

def weaklyRegular_unit_consType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], ∀ (a : R) (x : List R), IsUnit a → RingTheory.Sequence.IsWeaklyRegular M (a :: x)

def not_regular_unit_consType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], ∀ (a : R) (x : List R), IsUnit a → ¬ RingTheory.Sequence.IsRegular M (a :: x)

def unit_first_quotient_subsingletonType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], ∀ (a : R) (x : List R), IsUnit a →
  Subsingleton (M ⧸ (Ideal.ofList ((a :: x).take 1) • ⊤ : Submodule R M))

def regular_prefix_quotient_nonzeroType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], ∀ (x : List R), RingTheory.Sequence.IsRegular M x → ∀ j : ℕ,
  Nontrivial (M ⧸ (Ideal.ofList (x.take j) • ⊤ : Submodule R M))

def ringRegular_iffType : Prop :=
  ∀ {R : Type u} [CommRing R] (x : List R), RingTheory.Sequence.IsRegular R x ↔ RingTheory.Sequence.IsRegular R x

end AdvCommAlg.RegularSequence.Specs
