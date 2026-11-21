import MathGenome.Internal.Specs.D07.Ch22.TensorQuotients
import MathGenome.Internal.D07.Foundations.IntegerArithmetic
import Mathlib.Data.Int.GCD

/-! Quotient tensors and signed integer cyclic modules, paper.tex:6820–6853. -/
noncomputable section
universe u v w
namespace D07.Ch22.TensorQuotients
open Specs.D07.Ch22.TensorQuotients
open scoped TensorProduct
attribute [-instance] AddCommGroup.toIntModule

theorem relationsImages : RelationsImages.{u, v, w} := by
  intro R _ M _ _ N _ _ U V
  unfold relations
  rw [TensorProduct.range_map_eq_span_tmul, TensorProduct.range_map_eq_span_tmul,
    ← Submodule.span_union]
  congr 1
  ext t
  constructor
  · rintro (⟨m, hm, n, rfl⟩ | ⟨m, n, hn, rfl⟩)
    · exact Or.inl ⟨⟨m, hm⟩, n, rfl⟩
    · exact Or.inr ⟨m, ⟨n, hn⟩, rfl⟩
  · rintro (⟨m, n, rfl⟩ | ⟨m, n, rfl⟩)
    · exact Or.inl ⟨m, m.property, n, rfl⟩
    · exact Or.inr ⟨m, n, n.property, rfl⟩

theorem quotientIsomorphism : QuotientIsomorphism.{u, v, w} := by
  intro R _ M _ _ N _ _ U V
  let e := (TensorProduct.quotientTensorQuotientEquiv U V).trans
    (Submodule.quotEquivOfEq _ _ (relationsImages R M N U V).symm)
  refine ⟨e, ?_, ?_⟩
  · intro m n
    rfl
  · intro m n
    apply e.injective
    rw [e.apply_symm_apply]
    rfl

theorem idealActionEquality : IdealActionEquality.{u, w} := by
  intro R _ N _ _ I
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨a, ha, n, rfl⟩
    exact Submodule.smul_mem_smul ha (Submodule.mem_top : n ∈ (⊤ : Submodule R N))
  · apply Submodule.smul_le.mpr
    intro a ha n _
    exact Submodule.subset_span ⟨a, ha, n, rfl⟩

theorem idealActionFiniteSums : IdealActionFiniteSums.{u, w} := by
  intro R _ N _ _ I x
  rw [idealActionEquality R N I]
  simpa only [Set.range_id, Submodule.span_univ, id_eq, exists_prop] using
    (Submodule.mem_ideal_smul_span_iff_exists_sum I (id : N → N) x)

theorem idealTensorImage : IdealTensorImage.{u, w} := by
  intro R _ N _ _ I
  rw [TensorProduct.range_map_eq_span_tmul, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨t, ⟨a, n, rfl⟩, rfl⟩
    exact ⟨a, a.property, n, rfl⟩
  · rintro ⟨a, ha, n, rfl⟩
    exact ⟨a ⊗ₜ[R] n, ⟨⟨a, ha⟩, n, rfl⟩, rfl⟩

theorem idealQuotientIsomorphism : IdealQuotientIsomorphism.{u, w} := by
  intro R _ N _ _ I
  let e := (TensorProduct.quotTensorEquivQuotSMul N I).trans
    (Submodule.quotEquivOfEq _ _ (idealActionEquality R N I).symm)
  refine ⟨e, ?_, ?_⟩
  · intro r n
    simp [e]
  · intro n
    apply e.injective
    rw [e.apply_symm_apply]
    simpa using (show e (Ideal.Quotient.mk I 1 ⊗ₜ[R] n) =
      (idealAction I N).mkQ ((1 : R) • n) by simp [e]).symm

/-- Multiplication takes precisely the two relation families to I + J. -/
theorem idealRelationsMap {R : Type u} [CommRing R] (I J : Ideal R) :
    Submodule.map (TensorProduct.lid R R).toLinearMap (relations I J) = I ⊔ J := by
  apply le_antisymm
  · rintro _ ⟨t, ht, rfl⟩
    induction ht using Submodule.span_induction with
    | mem t ht =>
      rcases ht with ⟨a, ha, b, rfl⟩ | ⟨a, b, hb, rfl⟩
      · exact Submodule.mem_sup_left (I.mul_mem_right b ha)
      · exact Submodule.mem_sup_right (J.mul_mem_left a hb)
    | zero => simp
    | add x y _ _ hx hy => simpa using (I ⊔ J).add_mem hx hy
    | smul r x _ hx => simpa using (I ⊔ J).smul_mem r hx
  · apply sup_le
    · intro a ha
      refine ⟨a ⊗ₜ[R] (1 : R), Submodule.subset_span (Or.inl ⟨a, ha, 1, rfl⟩), ?_⟩
      simp
    · intro b hb
      refine ⟨(1 : R) ⊗ₜ[R] b, Submodule.subset_span (Or.inr ⟨1, b, hb, rfl⟩), ?_⟩
      simp

theorem cyclicPairIsomorphism : CyclicPairIsomorphism := by
  intro m n
  let I : Ideal ℤ := Ideal.span {m}
  let J : Ideal ℤ := Ideal.span {n}
  obtain ⟨e, he, _⟩ := quotientIsomorphism ℤ ℤ ℤ I J
  have h : I ⊔ J = Ideal.span ({m, n} : Set ℤ) := by
    rw [← Ideal.span_union]
    rfl
  let f := Submodule.Quotient.equiv (relations I J) (I ⊔ J)
    (TensorProduct.lid ℤ ℤ) (idealRelationsMap I J)
  refine ⟨e.trans (f.trans (Submodule.quotEquivOfEq _ _ h)), ?_⟩
  intro a b
  change (Submodule.quotEquivOfEq _ _ h) (f (e (I.mkQ a ⊗ₜ[ℤ] J.mkQ b))) = _
  rw [he a b]
  rfl

/-- The divisibility half and the Bézout half identify the actual integer ideals. -/
theorem gcdIdealEquality : GcdIdealEquality := by
  intro m n
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro a ha
    rcases Set.mem_insert_iff.mp ha with ha | ha
    · subst a
      exact Ideal.mem_span_singleton.mpr (Int.gcd_dvd_left m n)
    · have : a = n := Set.mem_singleton_iff.mp ha
      subst a
      exact Ideal.mem_span_singleton.mpr (Int.gcd_dvd_right m n)
  · apply Ideal.span_le.mpr
    intro a ha
    have : a = (Int.gcd m n : ℤ) := Set.mem_singleton_iff.mp ha
    subst a
    rw [Int.gcd_eq_gcd_ab]
    exact Ideal.add_mem _
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert m {n})))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem m rfl)))

theorem cyclicGcdIsomorphism : CyclicGcdIsomorphism := by
  intro m n
  obtain ⟨e, he⟩ := cyclicPairIsomorphism m n
  refine ⟨e.trans (Submodule.quotEquivOfEq _ _ (gcdIdealEquality m n)), ?_⟩
  intro a b
  rw [LinearEquiv.trans_apply, he]
  rfl

theorem cyclicBoundaries : CyclicBoundaries := by
  have hzero : Ideal.span ({(0 : ℤ)} : Set ℤ) = ⊥ := by simp
  let e0 : cyclic 0 ≃ₗ[ℤ] ℤ := Submodule.quotEquivOfEqBot _ hzero
  have he0 (a : ℤ) : e0 (Ideal.Quotient.mk _ a) = a := rfl
  have hunit (m : ℤ) (hm : IsUnit m) : Subsingleton (cyclic m) :=
    Submodule.Quotient.subsingleton_iff.mpr (Ideal.span_singleton_eq_top.mpr hm)
  refine ⟨⟨e0, he0⟩, hunit, ?_, ?_, D07.Foundations.IntegerArithmetic.gcd_zero⟩
  · refine ⟨(TensorProduct.congr e0 e0).trans (TensorProduct.lid ℤ ℤ), ?_⟩
    intro a b
    simp only [LinearEquiv.trans_apply, TensorProduct.congr_tmul, he0,
      TensorProduct.lid_tmul, smul_eq_mul]
  · intro m n h
    rcases h with hm | hn
    · have := hunit m hm
      infer_instance
    · have := hunit n hn
      infer_instance

end D07.Ch22.TensorQuotients
