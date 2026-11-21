import MathGenome.Internal.Specs.D05.Foundations.QuotientBasisUnits
import MathGenome.Internal.D05.Foundations.IdealsGcd
import MathGenome.Internal.D05.M02.Basis

/-! The quotient basis and unit criterion of paper.tex:383. -/

noncomputable section

namespace D05.Foundations.QuotientBasisUnits

open Polynomial

theorem uniqueRepresentative : D05.Specs.QuotientBasisUnits.uniqueRepresentative := by
  intro K _ q hq z
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  refine ⟨p %ₘ q, ⟨degree_modByMonic_lt p hq, ?_⟩, ?_⟩
  · exact AdjoinRoot.mk_leftInverse hq (AdjoinRoot.mk q p)
  · rintro r ⟨hr, heq⟩
    have heq' := congrArg (AdjoinRoot.modByMonicHom hq) heq
    simpa only [AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hq).mpr hr]
      using heq'

theorem residueBasis : D05.Specs.QuotientBasisUnits.residueBasis := by
  intro K _ q hq
  refine ⟨(AdjoinRoot.powerBasis' hq).basis, ?_⟩
  intro i
  rw [map_pow]
  change (AdjoinRoot.powerBasis' hq).basis i = (AdjoinRoot.powerBasis' hq).gen ^ (i : ℕ)
  exact (AdjoinRoot.powerBasis' hq).basis_eq_pow i

/-- A quotient inverse is equivalent to a Bézout identity. This works even
for the zero quotient: no nontriviality of the quotient is used. -/
theorem isUnit_mk_iff_isCoprime {K : Type*} [Field K] (q f : Polynomial K) :
    IsUnit (AdjoinRoot.mk q f) ↔ IsCoprime f q := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp h
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective z
    have hzero : AdjoinRoot.mk q (f * g - 1) = 0 := by
      simpa only [map_sub, map_mul, map_one, sub_eq_zero] using hz
    obtain ⟨v, hv⟩ := AdjoinRoot.mk_eq_zero.mp hzero
    refine ⟨g, -v, ?_⟩
    calc
      g * f + -v * q = f * g - q * v := by ring
      _ = 1 := by rw [← hv]; ring
  · rintro ⟨u, v, huv⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨AdjoinRoot.mk q u, ?_⟩
    have h := congrArg (AdjoinRoot.mk q) huv
    simpa only [map_add, map_mul, map_one, AdjoinRoot.mk_self, mul_zero, zero_mul, add_zero,
      mul_comm] using h

theorem isUnit_iff_gcd_eq_one : D05.Specs.QuotientBasisUnits.isUnit_iff_gcd_eq_one := by
  intro K _ q hq f
  rw [isUnit_mk_iff_isCoprime]
  constructor
  · intro h
    exact (IdealsGcd.monicGcd_monic (Or.inr hq.ne_zero)).eq_one_of_isUnit
      (h.isUnit_of_dvd' (IdealsGcd.monicGcd_dvd_left f q)
        (IdealsGcd.monicGcd_dvd_right f q))
  · intro h
    obtain ⟨u, v, huv⟩ :=
      (IdealsGcd.gcdProperties K f q (Or.inr hq.ne_zero)).2.2.2.2.2
    exact ⟨u, v, huv.symm.trans h⟩

theorem irreducibleQuotientIsField :
    D05.Specs.QuotientBasisUnits.irreducibleQuotientIsField := by
  intro K _ q _ hq
  exact AdjoinRoot.isField_iff_irreducible.mpr hq

theorem constantOneQuotient : D05.Specs.QuotientBasisUnits.constantOneQuotient := by
  intro K _
  have hzero : (1 : AdjoinRoot (1 : Polynomial K)) = 0 := by
    simpa only [map_one] using (AdjoinRoot.mk_self (f := (1 : Polynomial K)))
  have : Subsingleton (AdjoinRoot (1 : Polynomial K)) := subsingleton_of_zero_eq_one hzero.symm
  refine ⟨natDegree_one, inferInstance, not_isField_of_subsingleton _, ?_⟩
  obtain ⟨b, hb⟩ := residueBasis K (1 : Polynomial K) monic_one
  exact ⟨b.reindex (finCongr natDegree_one), fun i => Fin.elim0 i⟩

end D05.Foundations.QuotientBasisUnits
