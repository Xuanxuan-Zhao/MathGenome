import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.Definitions

/-! Weak and proper regular sequences, paper.tex:2107–2121, RK-01.
The predicates and all quotient actions are the canonical Mathlib ones. -/

universe u v
open scoped Pointwise
namespace AdvCommAlg.RegularSequence

def prefixIdeal {R : Type u} [CommRing R] (x : List R) (j : ℕ) : Ideal R :=
  Ideal.ofList (x.take j)

abbrev PrefixQuotient {R : Type u} [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] (x : List R) (j : ℕ) :=
  M ⧸ (prefixIdeal x j • ⊤ : Submodule R M)

abbrev WeaklyRegular {R : Type u} [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] (x : List R) : Prop :=
  RingTheory.Sequence.IsWeaklyRegular M x

abbrev Regular {R : Type u} [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] (x : List R) : Prop :=
  RingTheory.Sequence.IsRegular M x

abbrev RingRegular {R : Type u} [CommRing R] (x : List R) : Prop :=
  Regular R x

variable {R : Type u} [CommRing R]

theorem prefixIdeal_eq_span (x : List R) (j : ℕ) :
    prefixIdeal x j = Ideal.span {a | a ∈ x.take j} := rfl

theorem prefixIdeal_zero (x : List R) : prefixIdeal x 0 = ⊥ := by
  simp [prefixIdeal]

theorem weaklyRegular_iff_injective (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) : WeaklyRegular M x ↔
      ∀ i : Fin x.length, Function.Injective
        (fun q : PrefixQuotient M x i.val => x[i.val] • q) :=
  RingTheory.Sequence.isWeaklyRegular_iff_Fin M x

theorem regular_iff_injective_nonzero (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) : Regular M x ↔
      (∀ i : Fin x.length, Function.Injective
        (fun q : PrefixQuotient M x i.val => x[i.val] • q)) ∧
      Nontrivial (M ⧸ (Ideal.ofList x • ⊤ : Submodule R M)) := by
  change RingTheory.Sequence.IsRegular M x ↔ _
  rw [RingTheory.Sequence.isRegular_iff, RingTheory.Sequence.isWeaklyRegular_iff_Fin]
  simp only [PrefixQuotient, prefixIdeal,
    Submodule.Quotient.nontrivial_iff, ne_comm, IsSMulRegular]
  rfl

theorem weaklyRegular_nil (M : Type v) [AddCommGroup M] [Module R M] :
    WeaklyRegular M ([] : List R) := RingTheory.Sequence.IsWeaklyRegular.nil R M

theorem regular_nil_iff (M : Type v) [AddCommGroup M] [Module R M] :
    Regular M ([] : List R) ↔ Nontrivial M := by
  constructor
  · exact fun h => h.nontrivial
  · intro h
    have := h
    exact RingTheory.Sequence.IsRegular.nil R M

theorem weaklyRegular_of_subsingleton (M : Type v) [AddCommGroup M] [Module R M]
    [Subsingleton M] (x : List R) : WeaklyRegular M x := by
  constructor
  intro i hi q q' h
  exact Subsingleton.elim _ _

theorem not_regular_of_subsingleton (M : Type v) [AddCommGroup M] [Module R M]
    [Subsingleton M] (x : List R) : ¬ Regular M x := by
  intro h
  exact not_nontrivial M h.nontrivial

theorem weaklyRegular_unit_cons (M : Type v) [AddCommGroup M] [Module R M]
    (a : R) (x : List R) (ha : IsUnit a) : WeaklyRegular M (a :: x) := by
  have htop : a • (⊤ : Submodule R M) = ⊤ := by
    rw [← Submodule.ideal_span_singleton_smul,
      Ideal.span_singleton_eq_top.mpr ha, Submodule.top_smul]
  have : Subsingleton (QuotSMulTop a M) :=
    Submodule.Quotient.subsingleton_iff.mpr htop
  exact (RingTheory.Sequence.isWeaklyRegular_cons_iff M a x).mpr
    ⟨ha.isSMulRegular M, weaklyRegular_of_subsingleton _ x⟩

theorem not_regular_unit_cons (M : Type v) [AddCommGroup M] [Module R M]
    (a : R) (x : List R) (ha : IsUnit a) : ¬ Regular M (a :: x) := by
  intro h
  apply h.top_ne_smul
  rw [Ideal.ofList_cons, Ideal.span_singleton_eq_top.mpr ha, top_sup_eq, Submodule.top_smul]

theorem unit_first_quotient_subsingleton (M : Type v) [AddCommGroup M] [Module R M]
    (a : R) (x : List R) (ha : IsUnit a) :
    Subsingleton (PrefixQuotient M (a :: x) 1) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  simp only [prefixIdeal, List.take_succ_cons, List.take_zero, Ideal.ofList_cons,
    Ideal.ofList_nil, sup_bot_eq, Ideal.span_singleton_eq_top.mpr ha, Submodule.top_smul]

theorem regular_prefix_quotient_nonzero (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (hx : Regular M x) (j : ℕ) :
    Nontrivial (PrefixQuotient M x j) := by
  apply Submodule.Quotient.nontrivial_iff.mpr
  apply ne_top_of_le_ne_top hx.top_ne_smul.symm
  apply Submodule.smul_mono_left
  exact Ideal.span_mono (fun _ h => List.mem_of_mem_take h)

theorem ringRegular_iff (x : List R) : RingRegular x ↔ Regular R x := Iff.rfl

end AdvCommAlg.RegularSequence
