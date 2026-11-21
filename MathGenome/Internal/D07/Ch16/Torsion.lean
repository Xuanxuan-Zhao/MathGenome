import MathGenome.Internal.Specs.D07.Ch16.Torsion
import MathGenome.Internal.D07.Ch16.PidSubmodulesFinite
import Mathlib.RingTheory.Polynomial.Quotient

/-! K07.16.torsion, paper.tex:3122–3144. -/

universe u v w

namespace D07.Ch16.Torsion

open Specs.D07.Ch16.Torsion

theorem torsionMembership : TorsionMembership.{u, v} := by
  intro R _ _ M _ _ x
  rw [Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, nonZeroDivisors.coe_ne_zero r, hr⟩
  · rintro ⟨r, hr, hx⟩
    exact ⟨⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩, hx⟩

theorem torsionSubmodule : TorsionSubmodule.{u, v} := by
  intro R _ _ M _ _
  refine ⟨Submodule.torsion R M, ?_⟩
  ext x
  exact torsionMembership R M x

theorem torsionWitnessClosure : TorsionWitnessClosure.{u, v} := by
  intro R _ _ M _ _ r s x y hr hs hx hy
  refine ⟨mul_ne_zero hr hs, ?_, ?_, ?_⟩
  · rw [smul_add, mul_comm r s, mul_smul, hx, smul_zero,
      mul_comm s r, mul_smul, hy, smul_zero, add_zero]
  · rw [smul_neg, hx, neg_zero]
  · intro a
    rw [smul_comm r a, hx, smul_zero]

theorem quotientTorsionFree : QuotientTorsionFree.{u, v} := by
  intro R _ _ M _ _
  infer_instance

theorem quotientCanonical : QuotientCanonical.{u, v, w} := by
  intro R _ _ M _ _
  refine ⟨Submodule.ker_mkQ _, ?_⟩
  intro N _ _ f
  refine ⟨(Submodule.torsion R M).mapQ (Submodule.torsion R N) f ?_, ?_⟩
  · intro x hx
    obtain ⟨r, hr, hx⟩ := (torsionMembership R M x).mp hx
    apply (torsionMembership R N (f x)).mpr
    exact ⟨r, hr, by rw [← f.map_smul, hx, f.map_zero]⟩
  · intro x
    rfl

theorem torsionFinite : TorsionFinite.{u, v} := by
  intro R _ _ _ M _ _ _
  exact PidSubmodulesFinite.submoduleFinite R M (Submodule.torsion R M)

theorem commonAnnihilator : CommonAnnihilator.{u, v} := by
  intro R _ _ _ M _ _ _
  let T := Submodule.torsion R M
  let : Module.Finite R T := torsionFinite R M
  obtain ⟨r, hr, hreg⟩ :=
    Submodule.annihilator_top_inter_nonZeroDivisors
      (Submodule.torsion_isTorsion (R := R) (M := M))
  refine ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hreg, ?_⟩
  intro x hx
  have h := Submodule.mem_annihilator.mp hr (⟨x, hx⟩ : T) Submodule.mem_top
  exact congrArg Subtype.val h

theorem zeroTorsionAnnihilator : ZeroTorsionAnnihilator.{u, v} := by
  intro R _ _ M _ _ hT
  refine ⟨one_ne_zero, ?_⟩
  intro x hx
  rw [hT, Submodule.mem_bot] at hx
  simp [hx]

theorem polynomialQuotientExample : PolynomialQuotientExample.{u} := by
  intro k _
  have hX : ∀ x : PolynomialXQuotient k, (Polynomial.X : Polynomial k) • x = 0 := by
    intro x
    change (Ideal.Quotient.mk _ Polynomial.X) * x = 0
    have h : Ideal.Quotient.mk
        (Ideal.span ({Polynomial.X} : Set (Polynomial k))) Polynomial.X = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rw [h, zero_mul]
  have e : PolynomialXQuotient k ≃+* k := by
    have hI : Ideal.span ({Polynomial.X - Polynomial.C (0 : k)} : Set (Polynomial k)) =
        Ideal.span ({Polynomial.X} : Set (Polynomial k)) := by
      rw [Polynomial.C_0, sub_zero]
    exact (Ideal.quotientEquivAlgOfEq k hI.symm).toRingEquiv.trans
      (Polynomial.quotientSpanXSubCAlgEquiv (0 : k)).toRingEquiv
  refine ⟨Polynomial.X_ne_zero, hX,
    fun x => ⟨Polynomial.X, Polynomial.X_ne_zero, hX x⟩, ⟨e⟩, ?_⟩
  intro hk
  exact e.toEquiv.infinite_iff.mpr hk

theorem integerExampleTorsion : IntegerExampleTorsion := by
  apply Submodule.ext
  intro x
  rw [torsionMembership]
  change (∃ r : ℤ, r ≠ 0 ∧ r • x = 0) ↔ x.1 = 0
  constructor
  · rintro ⟨r, hr, hx⟩
    have h := congrArg Prod.fst hx
    change r * x.1 = 0 at h
    exact (mul_eq_zero.mp h).resolve_left hr
  · intro hx
    refine ⟨2, by decide, ?_⟩
    apply Prod.ext
    · simp [hx]
    · change (2 : ℤ) • x.2 = 0
      rw [zsmul_eq_mul]
      change (2 : ZMod 2) * x.2 = 0
      rw [show (2 : ZMod 2) = 0 by decide, zero_mul]

/-- The span of (1,e) is precisely its graph over the integer coordinate. -/
theorem mem_span_pair (e : ZMod 2) (x : IntegerExample) :
    x ∈ Submodule.span ℤ {((1, e) : IntegerExample)} ↔
      x.2 = (x.1 : ZMod 2) * e := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨n, rfl⟩
    simp [zsmul_eq_mul]
  · intro hx
    refine ⟨x.1, ?_⟩
    apply Prod.ext
    · simp
    · simpa [zsmul_eq_mul] using hx.symm

/-- Both graph submodules project isomorphically onto the integer coordinate. -/
noncomputable def spanPairEquivInt (e : ZMod 2) :
    (Submodule.span ℤ {((1, e) : IntegerExample)}) ≃ₗ[ℤ] ℤ :=
  LinearEquiv.ofBijective
    ((LinearMap.fst ℤ ℤ (ZMod 2)).comp
      (Submodule.span ℤ {((1, e) : IntegerExample)}).subtype) (by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply Prod.ext hxy
      change x.val.2 = y.val.2
      rw [(mem_span_pair e x).mp x.property, (mem_span_pair e y).mp y.property]
      rw [show x.val.1 = y.val.1 from hxy]
    · intro n
      refine ⟨⟨n • ((1, e) : IntegerExample),
        Submodule.smul_mem _ n (Submodule.mem_span_singleton_self _)⟩, ?_⟩
      simp)

theorem spanPair_isCompl (e : ZMod 2) :
    IsCompl finitePart (Submodule.span ℤ {((1, e) : IntegerExample)}) := by
  apply isCompl_iff.mpr
  constructor
  · apply Submodule.disjoint_def.mpr
    intro x hx hy
    change x.1 = 0 at hx
    have h := (mem_span_pair e x).mp hy
    apply Prod.ext hx
    simpa [hx] using h
  · apply codisjoint_iff.mpr
    apply top_unique
    intro x _
    apply Submodule.mem_sup.mpr
    refine ⟨(0, x.2 - (x.1 : ZMod 2) * e), ?_,
      x.1 • ((1, e) : IntegerExample), ?_, ?_⟩
    · rfl
    · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · ext <;> simp [zsmul_eq_mul]

theorem distinctFreeComplements : DistinctFreeComplements := by
  refine ⟨?_, spanPair_isCompl 0, spanPair_isCompl 1,
    ⟨spanPairEquivInt 0⟩, ⟨spanPairEquivInt 1⟩⟩
  intro h
  have hm : ((1, 0) : IntegerExample) ∈ diagonal := by
    rw [← h]
    exact Submodule.mem_span_singleton_self _
  have := (mem_span_pair 1 _).mp hm
  norm_num at this

end D07.Ch16.Torsion
