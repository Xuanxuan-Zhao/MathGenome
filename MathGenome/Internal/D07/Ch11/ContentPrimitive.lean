import MathGenome.Internal.Specs.D07.Ch11.ContentPrimitive
import MathGenome.Internal.D07.Ch10.UfdPrimeIrreducible

/-! Contents and primitive parts with normalization-independent conclusions. -/

universe u
namespace D07.Ch11.ContentPrimitive
open Polynomial Specs.D07.Ch11.ContentPrimitive

theorem contentIsGcd : ContentIsGcd.{u} := by
  intro R _ _ _ f
  let := contentStructure R
  change IsContent f f.content
  refine ⟨fun n => content_dvd_coeff n, ?_⟩
  intro d hd
  exact dvd_content_iff_C_dvd.mpr ((C_dvd_iff_dvd_coeff _ _).mpr hd)

theorem contentZero : ContentZero.{u} := by
  intro R _ _ _
  let := contentStructure R
  exact Polynomial.content_zero

theorem contentEqZero : ContentEqZero.{u} := by
  intro R _ _ _ f c hc
  constructor
  · intro h
    ext n
    exact zero_dvd_iff.mp (h ▸ hc.1 n)
  · intro h
    apply zero_dvd_iff.mp
    apply hc.2 0
    intro n
    simp [h]

theorem contentUnique : ContentUnique.{u} := by
  intro R _ _ _ f c d hc hd
  exact associated_of_dvd_dvd (hd.2 c hc.1) (hc.2 d hd.1)

theorem contentAssociateChoice : ContentAssociateChoice.{u} := by
  intro R _ _ _ f c
  constructor
  · exact fun hc => contentUnique R f c (content f) hc (contentIsGcd R f)
  · intro h
    refine ⟨fun n => h.dvd.trans ((contentIsGcd R f).1 n), ?_⟩
    intro d hd
    exact ((contentIsGcd R f).2 d hd).trans h.symm.dvd

theorem primitiveIffUnitContent : PrimitiveIffUnitContent.{u} := by
  intro R _ _ _ f c hc
  constructor
  · intro hf
    exact ⟨hf.ne_zero, hf c ((C_dvd_iff_dvd_coeff _ _).mpr hc.1)⟩
  · rintro ⟨_, hu⟩ d hd
    exact isUnit_of_dvd_unit (hc.2 d ((C_dvd_iff_dvd_coeff _ _).mp hd)) hu

theorem primitiveIffNoCommonPrime : PrimitiveIffNoCommonPrime.{u} := by
  intro R _ _ _ f hf
  constructor
  · intro h p hp hall
    exact hp.not_isUnit (h p ((C_dvd_iff_dvd_coeff _ _).mpr hall))
  · intro h d hd
    by_contra hdu
    have hd0 : d ≠ 0 := by
      intro he
      apply hf
      ext n
      exact zero_dvd_iff.mp (he ▸ (C_dvd_iff_dvd_coeff _ _).mp hd n)
    obtain ⟨p, hp, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd0
    exact h p (D07.Ch10.UfdPrimeIrreducible.irreducibleIsPrime R p hp)
      (fun n => hpd.trans ((C_dvd_iff_dvd_coeff _ _).mp hd n))

theorem zeroNotPrimitive : ZeroNotPrimitive.{u} := by
  intro R _ _ _ h
  exact h.ne_zero rfl

/-- Universal content forces the quotient by it to be primitive. Cancelling
c from c*d|c leaves d a unit; this avoids any normalization assumption. -/
lemma primitive_of_content_factor {R : Type u} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {f g : R[X]} {c : R}
    (hf : f ≠ 0) (hc : IsContent f c) (he : f = C c * g) : g.IsPrimitive := by
  have hc0 : c ≠ 0 := fun h => hf ((contentEqZero R f c hc).mp h)
  intro d hd
  have hcd : c * d ∣ c := by
    apply hc.2 (c * d)
    intro n
    rw [he, coeff_C_mul]
    exact mul_dvd_mul_left c ((C_dvd_iff_dvd_coeff _ _).mp hd n)
  obtain ⟨a, ha⟩ := hcd
  apply IsUnit.of_mul_eq_one a
  apply mul_left_cancel₀ hc0
  simpa only [mul_assoc, mul_one] using ha.symm

theorem primitivePartExists : PrimitivePartExists.{u} := by
  intro R _ _ _ f c hf hc
  obtain ⟨g, hg⟩ := (C_dvd_iff_dvd_coeff _ _).mpr hc.1
  refine ⟨g, ⟨hg, primitive_of_content_factor hf hc hg⟩, ?_⟩
  intro h hh
  have hc0 : C c ≠ 0 := by
    rw [ne_eq, C_eq_zero]
    exact fun hz => hf ((contentEqZero R f c hc).mp hz)
  exact mul_left_cancel₀ hc0 (hh.1.symm.trans hg)

theorem primitivePartCoefficients : PrimitivePartCoefficients.{u} := by
  intro R _ _ _ f g c he n
  rw [he, coeff_C_mul]

theorem primitivePartUnitChange : PrimitivePartUnitChange.{u} := by
  intro R _ _ _ f g h c v hf hg hh
  have hc0 : C c ≠ 0 := by
    intro hz
    apply hf
    rw [hg, hz, zero_mul]
  apply mul_left_cancel₀ hc0
  rw [← mul_assoc, ← C_mul, ← hh, ← hg]

theorem monicPrimitive : MonicPrimitive.{u} := by
  intro R _ _ _ f hf
  exact hf.isPrimitive

theorem valuationBoundary : ValuationBoundary.{u} := by
  intro R _ _ _ p hp
  refine ⟨emultiplicity_zero_right p, ?_⟩
  intro a ha
  have hfin := FiniteMultiplicity.of_prime_left hp ha
  refine ⟨multiplicity p a, hfin.emultiplicity_eq_multiplicity, ?_, ?_⟩
  · exact pow_multiplicity_dvd p a
  · exact hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)

theorem contentValuation : ContentValuation.{u} := by
  intro R _ _ _ f c p hc _
  apply ENat.eq_of_forall_natCast_le_iff
  intro k
  rw [← pow_dvd_iff_le_emultiplicity, Finset.le_inf_iff]
  simp_rw [← pow_dvd_iff_le_emultiplicity]
  constructor
  · intro h n _
    exact h.trans (hc.1 n)
  · intro h
    apply hc.2 (p ^ k)
    intro n
    by_cases hn : n ∈ f.support
    · exact h n hn
    · rw [notMem_support_iff.mp hn]
      exact dvd_zero _

theorem primitivePartValuations : PrimitivePartValuations.{u} := by
  intro R _ _ _ f g c p hf hc hp he
  have hc0 : c ≠ 0 := fun hz => hf ((contentEqZero R f c hc).mp hz)
  have hfin := FiniteMultiplicity.of_prime_left hp hc0
  constructor
  · intro n
    rw [he, coeff_C_mul, emultiplicity_mul hp]
    rw [hfin.emultiplicity_eq_multiplicity]
    generalize emultiplicity p (g.coeff n) = k
    induction k using ENat.recTopCoe with
    | top => rfl
    | coe k => exact_mod_cast (Nat.add_sub_cancel_left (multiplicity p c) k).symm
  · have hg := primitive_of_content_factor hf hc he
    have hg1 : IsContent g (1 : R) := by
      refine ⟨fun _ => one_dvd _, ?_⟩
      intro d hd
      exact (hg d ((C_dvd_iff_dvd_coeff _ _).mpr hd)).dvd
    rw [← contentValuation R g 1 p hg1 hp]
    exact emultiplicity_of_one_right hp.not_isUnit

end D07.Ch11.ContentPrimitive
