import Mathlib.Algebra.Lie.AdjointAction.Derivation
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CharacteristicRadical
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Engel
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Nilradical

universe u v w
namespace LieAlgebrasAndRepresentations

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} [Field k]
variable {L : Type v} [LieRing L] [LieAlgebra k L]

/-- The sum of the internally nilpotent ideals. -/
def nilradical (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L] :
    LieIdeal k L := sSup {I : LieIdeal k L | LieRing.IsNilpotent I}

theorem nilpotent_ideal_le_nilradical (I : LieIdeal k L) (hI : LieRing.IsNilpotent I) :
    I ≤ nilradical k L := le_sSup hI

theorem nilradical_le_radical : nilradical k L ≤ radical k L := by
  apply sSup_le
  intro I hI
  have : LieRing.IsNilpotent I := hI
  exact solvable_ideal_le_radical I (inferInstance : LieAlgebra.IsSolvable I)

section Module
variable {V : Type w} [AddCommGroup V] [Module k V]
  [LieRingModule L V] [LieModule k L V]

/-- Powers of the action commute with a Lie module map. -/
theorem map_toEnd_pow {W : Type*} [AddCommGroup W] [Module k W]
    [LieRingModule L W] [LieModule k L W]
    (f : V →ₗ⁅k,L⁆ W) (x : L) (n : ℕ) (v : V) :
    f (((LieModule.toEnd k L V x)^n) v) = ((LieModule.toEnd k L W x)^n) (f v) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    simp only [pow_succ', Module.End.mul_apply, LieModule.toEnd_apply_apply,
      LieModuleHom.map_lie, hn]

/-- Nilpotence can be checked on an invariant subspace and its quotient. -/
theorem isNilpotent_toEnd_iff_submodule_quotient (E : LieSubmodule k L V) (x : L) :
    IsNilpotent (LieModule.toEnd k L V x) ↔
      IsNilpotent (LieModule.toEnd k L E x) ∧
      IsNilpotent (LieModule.toEnd k L (V ⧸ E) x) := by
  constructor
  · rintro ⟨n, hn⟩
    constructor
    · refine ⟨n, ?_⟩
      ext v
      have h := map_toEnd_pow E.incl x n v
      simpa only [hn, LinearMap.zero_apply, map_zero, LieSubmodule.incl_apply, ZeroMemClass.coe_zero] using h
    · refine ⟨n, ?_⟩
      ext v
      obtain ⟨v, rfl⟩ := LieSubmodule.Quotient.surjective_mk' E v
      have h := map_toEnd_pow (LieSubmodule.Quotient.mk' E) x n v
      simpa only [hn, LinearMap.zero_apply, map_zero] using h.symm
  · rintro ⟨⟨n, hn⟩, ⟨m, hm⟩⟩
    refine ⟨n + m, ?_⟩
    ext v
    have hv : ((LieModule.toEnd k L V x)^m) v ∈ E := by
      apply (LieSubmodule.Quotient.mk_eq_zero E).mp
      rw [map_toEnd_pow, hm, LinearMap.zero_apply]
    have h := map_toEnd_pow E.incl x n ⟨_, hv⟩
    rw [hn, LinearMap.zero_apply, map_zero] at h
    simpa only [pow_add, Module.End.mul_apply, LieSubmodule.incl_apply, LinearMap.zero_apply] using h.symm

variable [CharZero k] [IsAlgClosed k] [FiniteDimensional k L]
  [FiniteDimensional k V]

/-- Within a solvable algebra, nilpotent action elements are closed under addition. -/
theorem isNilpotent_toEnd_add_of_solvable_of_isAlgClosed
    (V : Type w) [AddCommGroup V] [Module k V] [LieRingModule L V]
    [LieModule k L V] [FiniteDimensional k V] [LieAlgebra.IsSolvable L]
    (x y : L) (hx : IsNilpotent (LieModule.toEnd k L V x))
    (hy : IsNilpotent (LieModule.toEnd k L V y)) :
    IsNilpotent (LieModule.toEnd k L V (x + y)) := by
  classical
  obtain hV | hV := subsingleton_or_nontrivial V
  · exact ⟨1, Subsingleton.elim _ _⟩
  obtain ⟨χ, z, hz, he⟩ := common_eigenvector (k := k) (G := L) (V := V)
  let E : LieSubmodule k L V := LieModule.weightSpaceOfIsLieTower k V χ
  have hzE : z ∈ E := (LieModule.mem_weightSpace χ z).mpr he
  have hE : E ≠ ⊥ := by
    intro h
    rw [h] at hzE
    exact hz hzE
  have hscalar (a : L) : LieModule.toEnd k L E a = χ a • LinearMap.id := by
    ext v
    exact (LieModule.mem_weightSpace χ v.val).mp v.property a
  obtain ⟨hxE, hxQ⟩ := (isNilpotent_toEnd_iff_submodule_quotient E x).mp hx
  obtain ⟨hyE, hyQ⟩ := (isNilpotent_toEnd_iff_submodule_quotient E y).mp hy
  apply (isNilpotent_toEnd_iff_submodule_quotient E (x + y)).mpr
  constructor
  · rw [map_add]
    apply Commute.isNilpotent_add _ hxE hyE
    rw [hscalar, hscalar]
    exact ((Commute.refl (LinearMap.id : Module.End k E)).smul_left _).smul_right _
  · exact isNilpotent_toEnd_add_of_solvable_of_isAlgClosed (V ⧸ E) x y hxQ hyQ
termination_by Module.finrank k V
decreasing_by
  have hd := E.toSubmodule.finrank_quotient_add_finrank
  have hp : 0 < Module.finrank k E :=
    Module.finrank_pos_iff.mpr ((LieSubmodule.nontrivial_iff_ne_bot k L V).mpr hE)
  change Module.finrank k (V ⧸ E.toSubmodule) < Module.finrank k V
  change Module.finrank k E.toSubmodule > 0 at hp
  omega

/-- A solvable ideal's commutators with the ambient algebra act nilpotently.
A nonzero weight space is ambient-stable; on it the ideal acts by scalars,
so those commutators act by zero. Then pass to the quotient. -/
theorem isNilpotent_toEnd_lie_of_solvable_ideal_of_isAlgClosed
    (V : Type w) [AddCommGroup V] [Module k V] [LieRingModule L V]
    [LieModule k L V] [FiniteDimensional k V]
    (I : LieIdeal k L) [LieAlgebra.IsSolvable I] (x : I) (y : L) :
    IsNilpotent (LieModule.toEnd k L V ⁅y, (x : L)⁆) := by
  classical
  obtain hV | hV := subsingleton_or_nontrivial V
  · exact ⟨1, Subsingleton.elim _ _⟩
  obtain ⟨χ, z, hz, he⟩ := common_eigenvector (k := k) (G := I) (V := V)
  let E : LieSubmodule k L V := LieModule.weightSpaceOfIsLieTower k V χ
  have hzE : z ∈ E := (LieModule.mem_weightSpace χ z).mpr he
  have hE : E ≠ ⊥ := by
    intro h
    rw [h] at hzE
    exact hz hzE
  have hscalar : LieModule.toEnd k L E (x : L) = χ x • LinearMap.id := by
    ext v
    exact (LieModule.mem_weightSpace χ v.val).mp v.property x
  have hzero : LieModule.toEnd k L E ⁅y, (x : L)⁆ = 0 := by
    rw [LieHom.map_lie, hscalar]
    change (LieModule.toEnd k L E y) * (χ x • 1) -
      (χ x • 1) * (LieModule.toEnd k L E y) = 0
    simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_self]
  apply (isNilpotent_toEnd_iff_submodule_quotient E _).mpr
  exact ⟨hzero ▸ IsNilpotent.zero,
    isNilpotent_toEnd_lie_of_solvable_ideal_of_isAlgClosed (V ⧸ E) I x y⟩
termination_by Module.finrank k V
decreasing_by
  have hd := E.toSubmodule.finrank_quotient_add_finrank
  have hp : 0 < Module.finrank k E :=
    Module.finrank_pos_iff.mpr ((LieSubmodule.nontrivial_iff_ne_bot k L V).mpr hE)
  change Module.finrank k (V ⧸ E.toSubmodule) < Module.finrank k V
  change Module.finrank k E.toSubmodule > 0 at hp
  omega

end Module

section Descent
open scoped TensorProduct
variable [CharZero k] [FiniteDimensional k L]
variable {V : Type w} [AddCommGroup V] [Module k V]
  [LieRingModule L V] [LieModule k L V] [FiniteDimensional k V]

omit [CharZero k] [FiniteDimensional k L] in
/-- Nilpotence of an action endomorphism descends and ascends along a
faithful extension of fields. -/
theorem isNilpotent_toEnd_baseChange_iff
    (K : Type*) [Field K] [Algebra k K] (x : L) :
    IsNilpotent (LieModule.toEnd K (K ⊗[k] L) (K ⊗[k] V) (1 ⊗ₜ[k] x)) ↔
      IsNilpotent (LieModule.toEnd k L V x) := by
  rw [LieModule.toEnd_baseChange]
  exact IsNilpotent.map_iff (f := Module.End.baseChangeHom k K V)
    (LinearMap.baseChangeHom_injective k V K)

theorem isNilpotent_toEnd_add_of_solvable [LieAlgebra.IsSolvable L]
    (x y : L) (hx : IsNilpotent (LieModule.toEnd k L V x))
    (hy : IsNilpotent (LieModule.toEnd k L V y)) :
    IsNilpotent (LieModule.toEnd k L V (x + y)) := by
  let K := AlgebraicClosure k
  apply (isNilpotent_toEnd_baseChange_iff (V := V) K (x + y)).mp
  rw [TensorProduct.tmul_add]
  apply isNilpotent_toEnd_add_of_solvable_of_isAlgClosed (K ⊗[k] V)
  · exact (isNilpotent_toEnd_baseChange_iff (V := V) K x).mpr hx
  · exact (isNilpotent_toEnd_baseChange_iff (V := V) K y).mpr hy

theorem isNilpotent_toEnd_lie_of_solvable_ideal
    (I : LieIdeal k L) [LieAlgebra.IsSolvable I] (x : I) (y : L) :
    IsNilpotent (LieModule.toEnd k L V ⁅y, (x : L)⁆) := by
  let K := AlgebraicClosure k
  have : LieAlgebra.IsSolvable (I.baseChange K) := solvable_ideal_baseChange I K
  have hx : 1 ⊗ₜ[k] (x : L) ∈ I.baseChange K :=
    Submodule.tmul_mem_baseChange_of_mem 1 x.property
  apply (isNilpotent_toEnd_baseChange_iff (V := V) K ⁅y, (x : L)⁆).mp
  have h := isNilpotent_toEnd_lie_of_solvable_ideal_of_isAlgClosed
    (K ⊗[k] V) (I.baseChange K) ⟨_, hx⟩ (1 ⊗ₜ[k] y)
  simpa only [LieAlgebra.ExtendScalars.bracket_tmul, one_mul] using h

end Descent

/-- An internally nilpotent ideal has nilpotent adjoint action on the
ambient algebra: one application enters the ideal, and the remaining
applications are its own nilpotent adjoint action. -/
theorem isNilpotent_ad_of_mem_nilpotent_ideal (I : LieIdeal k L)
    [LieRing.IsNilpotent I] (x : I) : IsNilpotent (LieAlgebra.ad k L (x : L)) := by
  apply (isNilpotent_toEnd_iff_submodule_quotient I (x : L)).mpr
  constructor
  · exact LieModule.isNilpotent_toEnd_of_isNilpotent (R := k) (L := I) (M := I) x
  · have hzero : LieModule.toEnd k L (L ⧸ I) (x : L) = 0 := by
      ext z
      obtain ⟨z, rfl⟩ := LieSubmodule.Quotient.surjective_mk' I z
      change (LieSubmodule.Quotient.mk' I) ⁅(x : L), z⁆ = 0
      apply (LieSubmodule.Quotient.mk_eq_zero I).mpr
      simpa only [lie_skew, LieSubmodule.mem_toSubmodule] using I.neg_mem (I.lie_mem (x := z) x.property)
    rw [hzero]
    exact IsNilpotent.zero

section Nilradical
variable [CharZero k] [FiniteDimensional k L]

/-- The source's set of radical elements with nilpotent ambient adjoints,
with linear and ideal closure proved using the solvable-ideal action. -/
def nilpotentRadical (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L] : LieIdeal k L where
  carrier := {x | x ∈ radical k L ∧ IsNilpotent (LieAlgebra.ad k L x)}
  zero_mem' := ⟨(radical k L).zero_mem, by rw [map_zero]; exact IsNilpotent.zero⟩
  add_mem' := by
    intro x y hx hy
    have := radical_solvable k L
    refine ⟨(radical k L).add_mem hx.1 hy.1, ?_⟩
    exact isNilpotent_toEnd_add_of_solvable (V := L)
      (⟨x, hx.1⟩ : radical k L) (⟨y, hy.1⟩ : radical k L) hx.2 hy.2
  smul_mem' := by
    intro a x hx
    refine ⟨(radical k L).smul_mem a hx.1, ?_⟩
    rw [map_smul]
    exact hx.2.smul a
  lie_mem := by
    intro y x hx
    have := radical_solvable k L
    exact ⟨(radical k L).lie_mem hx.1,
      isNilpotent_toEnd_lie_of_solvable_ideal (V := L) (radical k L) ⟨x, hx.1⟩ y⟩

theorem nilpotentRadical_nilpotent : LieRing.IsNilpotent (nilpotentRadical k L) := by
  apply (engel_criterion k (nilpotentRadical k L)).mpr
  intro x
  exact LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad
    (nilpotentRadical k L : LieSubalgebra k L) x.property.2

theorem nilpotentRadical_eq_nilradical : nilpotentRadical k L = nilradical k L := by
  apply le_antisymm
  · exact nilpotent_ideal_le_nilradical _ nilpotentRadical_nilpotent
  · apply sSup_le
    intro I hI x hx
    have : LieRing.IsNilpotent I := hI
    exact ⟨solvable_ideal_le_radical I (inferInstance : LieAlgebra.IsSolvable I) hx,
      isNilpotent_ad_of_mem_nilpotent_ideal I ⟨x, hx⟩⟩

theorem nilradical_nilpotent (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L] :
    LieRing.IsNilpotent (nilradical k L) := by
  rw [← nilpotentRadical_eq_nilradical]
  exact nilpotentRadical_nilpotent

theorem mem_nilradical_iff (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L] (x : L) :
    x ∈ nilradical k L ↔ x ∈ radical k L ∧ IsNilpotent (LieAlgebra.ad k L x) := by
  rw [← nilpotentRadical_eq_nilradical]
  rfl

/-- The adjoints of radical elements form a solvable ideal in all
derivations, because every derivation preserves the radical. Applying
the solvable-ideal commutator lemma to its natural action on `L` proves
the stronger characteristic inclusion. -/
theorem derivation_radical_mem_nilradical (k : Type u) (L : Type v)
    [Field k] [CharZero k] [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    (D : LieDerivation k L L) (x : L) (hx : x ∈ radical k L) :
    D x ∈ nilradical k L := by
  apply (mem_nilradical_iff k L (D x)).mpr
  refine ⟨derivation_mem_radical k L D x hx, ?_⟩
  let f : radical k L →ₗ⁅k⁆ LieDerivation k L L :=
    (LieDerivation.ad k L).comp (radical k L).incl
  let J : LieIdeal k (LieDerivation k L L) :=
    { toSubmodule := f.range.toSubmodule
      lie_mem := by
        intro A B hB
        obtain ⟨z, rfl⟩ := hB
        refine ⟨⟨A (z : L), derivation_mem_radical k L A z z.property⟩, ?_⟩
        exact (LieDerivation.lie_der_ad_eq_ad_der A (z : L)).symm }
  have := radical_solvable k L
  have : LieAlgebra.IsSolvable J := inferInstanceAs (LieAlgebra.IsSolvable f.range)
  let : LieRingModule (LieDerivation k L L) L :=
    LieRingModule.compLieHom L (LieDerivation.toLinearMapLieHom k L)
  let : LieModule k (LieDerivation k L L) L :=
    LieModule.compLieHom L (LieDerivation.toLinearMapLieHom k L)
  have hz : LieDerivation.ad k L x ∈ J := ⟨⟨x, hx⟩, rfl⟩
  have h := isNilpotent_toEnd_lie_of_solvable_ideal (V := L) J ⟨_, hz⟩ D
  change IsNilpotent ((⁅D, LieDerivation.ad k L x⁆).toLinearMap) at h
  rw [LieDerivation.lie_der_ad_eq_ad_der, LieDerivation.coe_ad_apply_eq_ad_apply] at h
  exact h

theorem derivation_nilradical_mem (k : Type u) (L : Type v)
    [Field k] [CharZero k] [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    (D : LieDerivation k L L) (x : L) (hx : x ∈ nilradical k L) :
    D x ∈ nilradical k L :=
  derivation_radical_mem_nilradical k L D x (nilradical_le_radical hx)

theorem bracket_radical_le_nilradical (k : Type u) (L : Type v)
    [Field k] [CharZero k] [LieRing L] [LieAlgebra k L] [FiniteDimensional k L] :
    ⁅(⊤ : LieIdeal k L), radical k L⁆ ≤ nilradical k L := by
  apply (LieSubmodule.lie_le_iff _ _ _).mpr
  intro y _ x hx
  simpa using derivation_radical_mem_nilradical k L (LieDerivation.ad k L y) x hx

end Nilradical

end LieAlgebrasAndRepresentations
