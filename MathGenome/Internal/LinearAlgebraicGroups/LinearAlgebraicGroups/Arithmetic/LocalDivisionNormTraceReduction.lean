import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalDivisionNormTraceReduction
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.ReducedNorm
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SubfieldSplitting
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency.types false

open scoped WithZero TensorProduct
open ValuativeRel RM03.CSA

namespace LinearAlgebraicGroups.Arithmetic.LocalDivisionNormTraceReduction

private theorem baseValue_le_one {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (a : F) : baseValue F a ≤ 1 ↔ valuation F a ≤ 1 := by
  unfold baseValue
  rw [← map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)]
  exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).toOrderIso.le_iff_le

private theorem reducedTrace_map {F B L : Type*} [Field F] [DivisionRing B] [Algebra F B]
    [Field L] [Algebra F L] (hB : IsCentralSimple F B)
    (e : BaseChange F L B ≃ₐ[L] Matrix (Fin (degree F B)) (Fin (degree F B)) L) (x : B) :
    algebraMap F L (reducedTrace hB x) = (e (1 ⊗ₜ[F] x)).trace := by
  have : Nonempty (Fin (degree F B)) := ⟨⟨0, degree_pos hB⟩⟩
  rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, ← reducedCharpoly_map hB x e]
  unfold reducedTrace
  rw [map_neg, Polynomial.coeff_map]
  rfl

theorem reductionOfNormTrace : ReductionOfNormTrace := by
  classical
  intro F _ _ _ _ B _ _ hB vB
  dsimp only
  set n := _root_.Specs.RM03.CSA.degree F B
  intro hF L _ _ _ i vL hdeg _ hL τ hgen π t hπ ht hconj hpow
  letI := rightSubfieldModule i
  intro b hb hint ℓ _ _ _ r hker hscalar e he g hg x
  have hn : 0 < n := degree_pos hB
  let O := vL.valuationSubring
  let ρ : O →+* ℓ := e.toRingHom.comp (IsLocalRing.residue O)
  -- Split over the embedded field using left multiplication in the given right basis.
  have hBdiv : IsCentralDivision F B := hB.2
  letI := Algebra.TensorProduct.rightAlgebra (R := F) (A := B) (B := L)
  obtain ⟨act, hact⟩ := subfieldTensorAction_isomorphism i hBdiv hdeg
  let split := ((baseChangeEquivTensor F L B).trans act).trans (LinearMap.toMatrixAlgEquiv b)
  let M : Matrix (Fin n) (Fin n) L := split (1 ⊗ₜ[F] (x : B))
  have hM (p q : Fin n) : M p q = b.repr ((x : B) * b q) p := by
    change LinearMap.toMatrix b b (act ((baseChangeEquivTensor F L B) (1 ⊗ₜ[F] (x : B)))) p q = _
    rw [LinearMap.toMatrix_apply]
    change b.repr (act ((baseChangeEquivTensor F L B) (1 ⊗ₜ[F] (x : B))) (b q)) p = _
    rw [show (baseChangeEquivTensor F L B) (1 ⊗ₜ[F] (x : B)) = (x : B) ⊗ₜ[F] (1 : L) from rfl]
    change b.repr (act.toAlgHom ((x : B) ⊗ₜ[F] (1 : L)) (b q)) p = _
    rw [hact, subfieldTensorAction_tmul, map_one, mul_one]
  have hπlt : vB (π : B) < 1 := by simp [hπ]
  have hbint (q : Fin n) : b q ∈ vB.integer := by
    rw [vB.mem_integer_iff, hb, map_pow]
    exact pow_le_one₀ zero_le hπlt.le
  -- Left multiplication by an integer preserves the integral coordinate lattice.
  let A : Matrix (Fin n) (Fin n) O := fun p q =>
    ⟨M p q, (hM p q).symm ▸ (hint _).mp (vB.integer.mul_mem x.2 (hbint q)) p⟩
  have hA : A.map (O.subtype : O →+* L) = M := rfl
  have hvalue (a : F) : vL (algebraMap F L a) = baseValue F a := by
    apply (pow_left_inj₀ zero_le zero_le hn.ne').mp
    rw [← hL, i.commutes, hF]
  have hbase (a : F) : algebraMap F L a ∈ O ↔ a ∈ Integers F := by
    change vL (algebraMap F L a) ≤ 1 ↔ valuation F a ≤ 1
    rw [hvalue, baseValue_le_one]
  have htlt : baseValue F t < 1 := by simp [ht]
  let tL : O := ⟨algebraMap F L t, by
    change vL (algebraMap F L t) ≤ 1
    exact (hvalue t).trans_le htlt.le⟩
  let incl : O →+* vB.integer :=
    i.toRingHom.restrict O.toSubring vB.integer (fun a ha => by
      change vB (i a) ≤ 1
      rw [hL]
      exact pow_le_one₀ zero_le ha)
  have hrL (a : O) : r (incl a) = ρ a := he a (incl a) rfl
  have htL : ρ tL = 0 := by
    rw [← hrL]
    apply (hker _).2
    change vB (i (algebraMap F L t)) < 1
    rw [i.commutes, hF]
    exact pow_lt_one₀ zero_le htlt hn.ne'
  let a (j : Fin n) : O := ⟨b.repr (x : B) j, (hint _).mp x.2 j⟩
  let zeroIndex : Fin n := ⟨0, hn⟩
  have hxsum : (x : B) = ∑ j : Fin n, (π : B) ^ (j : ℕ) * i (a j : L) := by
    conv_rhs => enter [2, j]; rw [← hb, ← rightSubfield_smul]
    exact (b.sum_repr (x : B)).symm
  -- Only the constant basis coefficient survives reduction in the division algebra.
  let πO : vB.integer := ⟨(π : B), hπlt.le⟩
  have hπO : r πO = 0 := (hker _).2 hπlt
  have hxres : r x = ρ (a zeroIndex) := by
    have hs : x = ∑ j : Fin n, πO ^ (j : ℕ) * incl (a j) := by
      apply Subtype.ext
      push_cast
      exact hxsum
    rw [hs, map_sum, Finset.sum_eq_single zeroIndex]
    · simp [zeroIndex, hrL]
    · intro j _ hj
      have hj' : (j : ℕ) ≠ 0 := fun hz => hj (Fin.ext hz)
      rw [map_mul, map_pow, hπO, zero_pow hj', zero_mul]
    · simp
  have hmove1 (a : L) : i a * (π : B) = (π : B) * i (τ⁻¹ a) := by
    simpa using (hconj (τ⁻¹ a)).symm
  have hmove (k : ℕ) (a : L) :
      i a * (π : B) ^ k = (π : B) ^ k * i (((τ⁻¹) ^ k) a) := by
    induction k generalizing a with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, hmove1, ← mul_assoc, ← pow_succ,
        pow_succ' (τ⁻¹) k, AlgEquiv.mul_apply]
  have hinv (a : L) : vL (τ⁻¹ a) = vL a := by
    have hv := congrArg vB (hmove1 a)
    rw [map_mul, map_mul, hL, hL] at hv
    apply (pow_left_inj₀ zero_le zero_le hn.ne').mp
    exact (mul_left_cancel₀ (by simp [hπ]) ((mul_comm _ _).trans hv)).symm
  have htwistVal (k : ℕ) (a : L) : vL (((τ⁻¹) ^ k) a) = vL a := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, hinv, ih]
  let twist (j q : Fin n) : O :=
    ⟨((τ⁻¹) ^ (q : ℕ)) (a j : L), (htwistVal _ _).trans_le (a j).2⟩
  -- When the exponent reaches n, use π^n = t and retain t in the coefficient.
  let shift (j q : Fin n) : Fin n :=
    ⟨if (j : ℕ) + (q : ℕ) < n then (j : ℕ) + (q : ℕ) else (j : ℕ) + (q : ℕ) - n,
      by have := j.isLt; have := q.isLt; split <;> omega⟩
  let c (j q : Fin n) : O :=
    if (j : ℕ) + (q : ℕ) < n then twist j q else tL * twist j q
  have hterm (j q : Fin n) :
      (π : B) ^ (j : ℕ) * i (a j : L) * b q = (c j q : L) • b (shift j q) := by
    rw [hb q, mul_assoc, hmove, ← mul_assoc, ← pow_add, rightSubfield_smul, hb]
    by_cases hjq : (j : ℕ) + (q : ℕ) < n
    · simp only [c, shift, ite_eq_left hjq]
      rfl
    · simp only [c, shift, ite_eq_right hjq]
      change _ = (π : B) ^ ((j : ℕ) + (q : ℕ) - n) *
        i (algebraMap F L t * (((τ⁻¹) ^ (q : ℕ)) (a j : L)))
      rw [map_mul, i.commutes, ← hpow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]
  have hcol (q : Fin n) :
      (x : B) * b q = ∑ j : Fin n, (c j q : L) • b (shift j q) := by
    rw [hxsum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => hterm j q)
  have hentry (p q : Fin n) : A p q = ∑ j : Fin n,
      if shift j q = p then c j q else 0 := by
    apply Subtype.ext
    change M p q = _
    rw [hM, hcol]
    simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply,
      Module.Basis.repr_self_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : shift j q = p <;> simp [h]
  let Abar := A.map ρ
  have hbar (p q : Fin n) : Abar p q = ∑ j : Fin n,
      if shift j q = p then ρ (c j q) else 0 := by
    change ρ (A p q) = _
    rw [hentry, map_sum]
    exact Finset.sum_congr rfl (fun j _ => by
      by_cases h : shift j q = p <;> simp [h])
  -- Terms with positive j either lie below the diagonal or carry a factor of t.
  have habove (p q j : Fin n) (hpq : p ≤ q) (hj : j ≠ zeroIndex) :
      (if shift j q = p then ρ (c j q) else 0) = 0 := by
    by_cases hjq : (j : ℕ) + (q : ℕ) < n
    · have hne : shift j q ≠ p := by
        intro h
        have h' := congrArg Fin.val h
        change (if (j : ℕ) + (q : ℕ) < n then (j : ℕ) + (q : ℕ)
          else (j : ℕ) + (q : ℕ) - n) = (p : ℕ) at h'
        rw [ite_eq_left hjq] at h'
        exact hj (Fin.ext (by change (j : ℕ) = 0; change (p : ℕ) ≤ (q : ℕ) at hpq; omega))
      simp [hne]
    · simp [c, hjq, htL]
  have hshift0 (q : Fin n) : shift zeroIndex q = q := by
    apply Fin.ext
    simp [shift, zeroIndex, q.isLt]
  have hdiag (q : Fin n) : Abar q q = ρ (twist zeroIndex q) := by
    rw [hbar, Finset.sum_eq_single zeroIndex]
    · simp [hshift0, c, zeroIndex, q.isLt]
    · exact fun j _ hj => habove q q j le_rfl hj
    · simp
  have htri : Abar.IsLowerTriangular := by
    intro p q hpq
    change p < q at hpq
    rw [hbar]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j = zeroIndex
    · simp [hj, hshift0, hpq.ne']
    · exact habove p q j hpq.le hj
  -- Powers of the inverse generator enumerate all residue automorphisms.
  haveI : FiniteDimensional F L := Module.finite_of_finrank_pos (hdeg.symm ▸ hn)
  have hinvgen : Subgroup.zpowers τ⁻¹ = ⊤ := Subgroup.zpowers_inv.trans hgen
  have horder : orderOf τ⁻¹ = n :=
    (orderOf_eq_card_of_zpowers_eq_top hinvgen).trans
      ((IsGalois.card_aut_eq_finrank F L).trans hdeg)
  let conjugates : Fin n ≃ (ℓ ≃ₐ[BaseResidue F] ℓ) :=
    (finCongr horder.symm).trans <|
      (finEquivZPowers (isOfFinOrder_of_finite τ⁻¹)).trans <|
        ((MulEquiv.subgroupCongr hinvgen).trans Subgroup.topEquiv).toEquiv.trans g.toEquiv
  have hconjugates (q : Fin n) : conjugates q = g ((τ⁻¹) ^ (q : ℕ)) := rfl
  have hdiag' (q : Fin n) : Abar q q = conjugates q (r x) := by
    rw [hdiag, hconjugates, hxres]
    exact hg _ _ _ rfl
  have hnorm : ρ A.det = algebraMap (BaseResidue F) ℓ (Algebra.norm (BaseResidue F) (r x)) := by
    rw [ρ.map_det]
    change Abar.det = _
    rw [Matrix.det_of_isLowerTriangular _ htri, Algebra.norm_eq_prod_automorphisms]
    exact Fintype.prod_equiv conjugates _ _ hdiag'
  have htrace : ρ A.trace =
      algebraMap (BaseResidue F) ℓ (Algebra.trace (BaseResidue F) ℓ (r x)) := by
    rw [AddMonoidHom.map_trace ρ, trace_eq_sum_automorphisms]
    exact Fintype.sum_equiv conjugates _ _ hdiag'
  have hnormL : (A.det : L) = algebraMap F L (reducedNorm hB (x : B)) := by
    change O.subtype A.det = _
    rw [RingHom.map_det]
    change (A.map (O.subtype : O →+* L)).det = _
    rw [hA]
    exact (reducedNorm_map hB (x : B) split).symm
  have htraceL : (A.trace : L) = algebraMap F L (reducedTrace hB (x : B)) := by
    change O.subtype A.trace = _
    rw [AddMonoidHom.map_trace O.subtype, hA]
    exact (reducedTrace_map hB split (x : B)).symm
  -- The unramified valuation equality pulls integrality back to F.
  let normF : Integers F := ⟨reducedNorm hB (x : B),
    (hbase _).mp (hnormL ▸ A.det.2)⟩
  let traceF : Integers F := ⟨reducedTrace hB (x : B),
    (hbase _).mp (htraceL ▸ A.trace.2)⟩
  have hreduceScalar (aF : Integers F) (aL : O)
      (ha : (aL : L) = algebraMap F L (aF : F)) :
      ρ aL = algebraMap (BaseResidue F) ℓ (IsLocalRing.residue _ aF) := by
    rw [← hrL]
    apply hscalar
    change i (aL : L) = _
    rw [ha, i.commutes]
  refine ⟨normF, traceF, rfl, rfl, ?_, ?_⟩
  · apply (algebraMap (BaseResidue F) ℓ).injective
    rw [← hreduceScalar normF A.det hnormL, hnorm]
  · apply (algebraMap (BaseResidue F) ℓ).injective
    rw [← hreduceScalar traceF A.trace htraceL, htrace]

end LinearAlgebraicGroups.Arithmetic.LocalDivisionNormTraceReduction
