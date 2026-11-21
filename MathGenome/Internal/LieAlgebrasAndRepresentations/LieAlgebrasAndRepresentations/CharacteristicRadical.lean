import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.KillingCriterion
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CharacteristicRadical
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.RingTheory.Flat.Equalizer

/-! LA-B08-Radical: source equation (2.6), scalar extension, and the
characteristic property of the radical (source lines 1021–1056). The stronger
nilradical assertions of LA-B08 belong to the separately allocated goal. -/

universe u v w t
namespace LieAlgebrasAndRepresentations
open scoped TensorProduct

variable {k : Type u} [Field k] [CharZero k]
variable {L : Type v} [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]

/-- Trace forms add over a submodule and its quotient. -/
theorem traceForm_submodule_add_quotient
    {V : Type w} [AddCommGroup V] [Module k V]
    [LieRingModule L V] [LieModule k L V] [FiniteDimensional k V]
    (E : LieSubmodule k L V) (x y : L) :
    LieModule.traceForm k L V x y =
      LieModule.traceForm k L E x y + LieModule.traceForm k L (V ⧸ E) x y := by
  classical
  let bE := Module.finBasis k E
  let bQ := Module.finBasis k (V ⧸ E)
  rw [LieModule.traceForm_apply_apply, LieModule.traceForm_apply_apply,
    LieModule.traceForm_apply_apply, LinearMap.trace_eq_matrix_trace k (bE.sumQuot bQ),
    LinearMap.trace_eq_matrix_trace k bE, LinearMap.trace_eq_matrix_trace k bQ]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
    LinearMap.comp_apply, LieModule.toEnd_apply_apply, Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [Module.Basis.sumQuot_inl]
    exact Module.Basis.sumQuot_repr_inl bE bQ (⁅x, ⁅y, bE i⁆⁆ : E) i
  · apply Finset.sum_congr rfl
    intro i _
    rw [Module.Basis.sumQuot_repr_inr]
    change bQ.repr ((LieSubmodule.Quotient.mk' E) ⁅x, ⁅y, _⁆⁆) i = _
    rw [LieModuleHom.map_lie, LieModuleHom.map_lie]
    change bQ.repr ⁅x, ⁅y, Submodule.Quotient.mk _⁆⁆ i = _
    rw [Module.Basis.sumQuot_inr]

/-- A solvable ideal is orthogonal to the derived algebra in every trace
form. Over an algebraically closed field, induct on the representation by
quotienting by a nonzero common weight space of the ideal. This space is
stable under the entire algebra, and the ideal acts there by scalars. -/
theorem traceForm_solvable_ideal_of_isAlgClosed [IsAlgClosed k]
    (V : Type w) [AddCommGroup V] [Module k V]
    [LieRingModule L V] [LieModule k L V] [FiniteDimensional k V]
    (I : LieIdeal k L) [LieAlgebra.IsSolvable I]
    (x : I) (y : L) (hy : y ∈ LieAlgebra.derivedSeries k L 1) :
    LieModule.traceForm k L V (x : L) y = 0 := by
  classical
  obtain hV | hV := subsingleton_or_nontrivial V
  · have hz : (LieModule.toEnd k L V (x : L)).comp (LieModule.toEnd k L V y) = 0 :=
      Subsingleton.elim _ _
    simp only [LieModule.traceForm_apply_apply, hz, map_zero]
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
  have htrace : LieModule.traceForm k L E (x : L) y = 0 := by
    rw [LieModule.traceForm_apply_apply, hscalar, LinearMap.smul_comp,
      LinearMap.id_comp, map_smul]
    have hy' : y ∈ LieModule.lowerCentralSeries k L L 1 := by
      simpa [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ,
        LieAlgebra.derivedSeriesOfIdeal_zero,
        LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero] using hy
    rw [LieModule.trace_toEnd_eq_zero_of_mem_lcs k L E (le_refl 1) hy', smul_zero]
  rw [traceForm_submodule_add_quotient E, htrace, zero_add]
  exact traceForm_solvable_ideal_of_isAlgClosed (V ⧸ E) I x y hy
termination_by Module.finrank k V
decreasing_by
  have hd := E.toSubmodule.finrank_quotient_add_finrank
  have hp : 0 < Module.finrank k E :=
    Module.finrank_pos_iff.mpr ((LieSubmodule.nontrivial_iff_ne_bot k L V).mpr hE)
  change Module.finrank k (V ⧸ E.toSubmodule) < Module.finrank k V
  change Module.finrank k E.toSubmodule > 0 at hp
  omega

/-- Scalar extension of a solvable ideal is solvable. -/
theorem solvable_ideal_baseChange (I : LieIdeal k L) [LieAlgebra.IsSolvable I]
    (K : Type t) [Field K] [Algebra k K] :
    LieAlgebra.IsSolvable (I.baseChange K) := by
  obtain ⟨n, hn⟩ := LieAlgebra.IsSolvable.solvable k I
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hn
  apply LieAlgebra.IsSolvable.mk (R := K) (k := n)
  rw [LieIdeal.derivedSeries_eq_bot_iff, LieAlgebra.derivedSeriesOfIdeal_baseChange,
    hn, LieSubmodule.baseChange_bot]

/-- Descent of the trace identity from an algebraic closure. No closure
hypothesis remains in the conclusion. -/
theorem traceForm_solvable_ideal
    {V : Type w} [AddCommGroup V] [Module k V]
    [LieRingModule L V] [LieModule k L V] [FiniteDimensional k V]
    (I : LieIdeal k L) [LieAlgebra.IsSolvable I]
    (x : I) (y : L) (hy : y ∈ LieAlgebra.derivedSeries k L 1) :
    LieModule.traceForm k L V (x : L) y = 0 := by
  let K := AlgebraicClosure k
  let IK := I.baseChange K
  haveI : LieAlgebra.IsSolvable IK := solvable_ideal_baseChange I K
  have hxK : 1 ⊗ₜ[k] (x : L) ∈ IK :=
    Submodule.tmul_mem_baseChange_of_mem 1 x.property
  have hyK : 1 ⊗ₜ[k] y ∈ LieAlgebra.derivedSeries K (K ⊗[k] L) 1 := by
    rw [LieAlgebra.derivedSeries_baseChange]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hy
  have h := traceForm_solvable_ideal_of_isAlgClosed (K ⊗[k] V) IK ⟨_, hxK⟩ _ hyK
  rw [LieModule.traceForm_baseChange] at h
  simpa only [LinearMap.BilinForm.baseChange_tmul, one_mul, Algebra.smul_def,
    mul_one, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective k K)] using h

/-- The radical is the orthogonal complement of the derived algebra for the
Killing form. The reverse inclusion is Cartan's solvability criterion on
that orthogonal ideal, using restriction of the ambient Killing form. -/
theorem radical_eq_killingCompl_derived (k : Type u) (L : Type v)
    [Field k] [CharZero k] [LieRing L] [LieAlgebra k L] [FiniteDimensional k L] :
    radical k L = (LieAlgebra.derivedSeries k L 1).killingCompl k L := by
  apply le_antisymm
  · intro x hx
    apply (LieIdeal.mem_killingCompl k L _).mpr
    intro y hy
    rw [LieModule.traceForm_comm]
    haveI := radical_solvable k L
    exact traceForm_solvable_ideal (V := L) (radical k L) ⟨x, hx⟩ y hy
  · let J := (LieAlgebra.derivedSeries k L 1).killingCompl k L
    apply solvable_ideal_le_radical J
    apply (killing_criterion (k := k) (G := J)).mpr
    intro x hx y
    change killingForm k J x y = 0
    rw [killingForm_restrict_ideal]
    exact (LieIdeal.mem_killingCompl k L _).mp y.property x
      (LieIdeal.derivedSeries_map_le (f := J.incl) 1 (LieIdeal.mem_map hx))

/-- Every derivation is skew-adjoint for the Killing form. -/
theorem killingForm_derivation (D : LieDerivation k L L) (x y : L) :
    killingForm k L (D x) y + killingForm k L x (D y) = 0 := by
  have hD (z : L) : LieAlgebra.ad k L (D z) =
      D.toLinearMap * LieAlgebra.ad k L z - LieAlgebra.ad k L z * D.toLinearMap := by
    ext w
    change ⁅D z, w⁆ = D ⁅z, w⁆ - ⁅z, D w⁆
    rw [LieDerivation.apply_lie_eq_add]
    abel
  have h := congrArg (LinearMap.trace k L)
    (show LieAlgebra.ad k L (D x) * LieAlgebra.ad k L y +
        LieAlgebra.ad k L x * LieAlgebra.ad k L (D y) =
        D.toLinearMap * (LieAlgebra.ad k L x * LieAlgebra.ad k L y) -
          (LieAlgebra.ad k L x * LieAlgebra.ad k L y) * D.toLinearMap from by
      rw [hD, hD]
      simp only [sub_mul, mul_sub, mul_assoc]
      abel)
  simp only [map_add, map_sub, LinearMap.trace_mul_comm k D.toLinearMap,
    sub_self] at h
  exact h

/-- Derivations preserve the linear span of brackets. -/
theorem derivation_mem_derived (D : LieDerivation k L L) (y : L)
    (hy : y ∈ LieAlgebra.derivedSeries k L 1) :
    D y ∈ LieAlgebra.derivedSeries k L 1 := by
  replace hy : y ∈ Submodule.span k {⁅a, b⁆ | (a : L) (b : L)} := by
    rw [← LieAlgebra.coe_derivedSeries_one_eq]
    exact hy
  suffices h : D y ∈ Submodule.span k {⁅a, b⁆ | (a : L) (b : L)} by
    rw [← LieAlgebra.coe_derivedSeries_one_eq] at h
    exact h
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, b, rfl⟩ := hz
    rw [LieDerivation.apply_lie_eq_add]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨a, D b, rfl⟩)
      (Submodule.subset_span ⟨D a, b, rfl⟩)
  | zero => simp
  | add z w _ _ hz hw => simpa using Submodule.add_mem _ hz hw
  | smul a z _ hz => simpa using Submodule.smul_mem _ a hz

/-- The characteristic property of the radical follows from its orthogonal
description and the derivation identity for the Killing form. -/
theorem derivation_mem_radical (k : Type u) (L : Type v)
    [Field k] [CharZero k] [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    (D : LieDerivation k L L) (x : L) (hx : x ∈ radical k L) :
    D x ∈ radical k L := by
  rw [radical_eq_killingCompl_derived] at hx ⊢
  apply (LieIdeal.mem_killingCompl k L _).mpr
  intro y hy
  have hz := (LieIdeal.mem_killingCompl k L _).mp hx (D y) (derivation_mem_derived D y hy)
  have h := killingForm_derivation D y x
  change killingForm k L (D y) x = 0 at hz
  change killingForm k L y (D x) = 0
  simpa only [hz, zero_add] using h

/-- Orthogonal complements commute with field extension. This includes
degenerate forms: it is the kernel of the map to the dual of the subspace,
and both kernels and finite-dimensional duals commute with base change. -/
theorem orthogonal_baseChange
    (B : LinearMap.BilinForm k L) (I : Submodule k L)
    (K : Type t) [Field K] [Algebra k K] :
    (B.baseChange K).orthogonal (I.baseChange K) = (B.orthogonal I).baseChange K := by
  let f : L →ₗ[k] Module.Dual k I := B.flip.compl₂ I.subtype
  let ibc := TensorProduct.isBaseChange k I K
  let e := ibc.toDualBaseChange
  let G := e.toLinearMap.comp (f.baseChange K)
  have hG : G = (B.baseChange K).flip.compl₂ (I.subtype.baseChange K) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    apply TensorProduct.AlgebraTensorModule.ext
    intro b y
    change e (a ⊗ₜ[k] f x) (b ⊗ₜ[k] y) =
      (B.baseChange K) (b ⊗ₜ[k] (y : L)) (a ⊗ₜ[k] x)
    rw [show b ⊗ₜ[k] y = b • (1 ⊗ₜ[k] y) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
    have h := ibc.toDualBaseChange_tmul a (f x) y
    change e (a ⊗ₜ[k] f x) (1 ⊗ₜ[k] y) = _ at h
    rw [h]
    simp [f, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]
  have hf : f.ker = B.orthogonal I := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
      LinearMap.BilinForm.mem_orthogonal_iff]
    exact ⟨fun h y hy => h ⟨y, hy⟩, fun h y => h y y.property⟩
  have hker : G.ker = (B.baseChange K).orthogonal (I.baseChange K) := by
    rw [hG]
    ext z
    simp only [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply]
    change (∀ y : K ⊗[k] I, (B.baseChange K) ((I.subtype.baseChange K) y) z = 0) ↔ _
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    change _ ↔ ∀ y ∈ LinearMap.range (I.subtype.baseChange K), _
    simp only [LinearMap.mem_range, forall_exists_index]
    constructor
    · intro h y a ha
      rw [← ha]
      exact h a
    · intro h y
      exact h _ y rfl
  rw [← hker, LinearMap.ker_comp, e.ker, Submodule.comap_bot]
  rw [show (f.baseChange K).ker = f.ker.baseChange K from
    Module.Flat.ker_lTensor_eq K K f]
  rw [hf]

/-- The solvable radical commutes with arbitrary extension of its
characteristic-zero ground field. -/
theorem radical_baseChange (k : Type u) (L : Type v)
    [Field k] [CharZero k] [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    (K : Type w) [Field K] [Algebra k K] :
    radical K (K ⊗[k] L) = (radical k L).baseChange K := by
  haveI : CharZero K := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective k K)
  rw [radical_eq_killingCompl_derived, radical_eq_killingCompl_derived,
    LieAlgebra.derivedSeries_baseChange]
  apply (LieSubmodule.toSubmodule_inj _ _).mp
  simp only [LieIdeal.toSubmodule_killingCompl, LieSubmodule.coe_baseChange]
  simp only [_root_.killingForm, LieModule.traceForm_baseChange]
  exact orthogonal_baseChange _ _ K

end LieAlgebrasAndRepresentations
