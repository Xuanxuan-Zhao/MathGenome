import MathGenome.Internal.Specs.D07.Ch22.LocalizationConstruction

/-!
K07.22.localization_construction, paper.tex:7044–7080.

The canonical localization is a quotient by an Ore relation. The first lemma
checks that its equality relation is exactly the paper's annihilated cross
difference, without any cancellation assumption. Its quotient and ring
operations therefore implement precisely the stated construction, even when
zero belongs to the denominator submonoid or the ring is the zero ring.
-/

universe u

namespace D07.Ch22.LocalizationConstruction

open Specs.D07.Ch22.LocalizationConstruction

/-- Convert the canonical quotient relation to the source's cross difference. -/
theorem fractionEquality : FractionEquality.{u} := by
  intro R _ S a b s t
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  simp only [mul_sub, sub_eq_zero]

/-- In particular, the source relation is an equivalence relation. -/
theorem relationEquivalence : RelationEquivalence.{u} := by
  intro R _ S
  have eq_iff (p q : R × S) :
      Localization.mk p.1 p.2 = Localization.mk q.1 q.2 ↔ FractionRel S p q :=
    fractionEquality R S p.1 q.1 p.2 q.2
  exact ⟨fun p => (eq_iff p p).mp rfl,
    fun {p q} h => (eq_iff q p).mp ((eq_iff p q).mpr h).symm,
    fun {p q r} hpq hqr =>
      (eq_iff p r).mp (((eq_iff p q).mpr hpq).trans ((eq_iff q r).mpr hqr))⟩

/-- Every canonical fraction is a class of a pair from R × S. -/
theorem fractionRepresentatives : FractionRepresentatives.{u} := by
  intro R _ S x
  exact Localization.induction_on x fun p => ⟨p.1, p.2, rfl⟩

/-- An explicit identification of the quotient by the source relation. -/
theorem quotientRepresentation : QuotientRepresentation.{u} := by
  intro R _ S
  let f : Quot (FractionRel S) → Localization S :=
    Quot.lift (fun p : R × S => Localization.mk p.1 p.2)
      (fun p q h => (fractionEquality R S p.1 q.1 p.2 q.2).mpr h)
  have hinj : Function.Injective f := by
    intro x y
    refine Quot.inductionOn x ?_
    intro p
    refine Quot.inductionOn y ?_
    intro q h
    exact Quot.sound ((fractionEquality R S p.1 q.1 p.2 q.2).mp h)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨a, s, h⟩ := fractionRepresentatives R S x
    exact ⟨Quot.mk _ (a, s), h.symm⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun _ => rfl⟩

/-- The built-in addition is the displayed source formula. -/
theorem additionFormula : AdditionFormula.{u} := by
  intro R _ S a b s t
  simpa only [mul_comm, add_comm] using (Localization.add_mk a s b t)

theorem multiplicationFormula : MultiplicationFormula.{u} := by
  intro R _ S a b s t
  exact Localization.mk_mul a b s t

theorem negationFormula : NegationFormula.{u} := by
  intro R _ S a s
  exact Localization.neg_mk a s

/-- The pair operations descend, as a consequence of their exact formulas and
of the equality criterion, rather than any regularity of the denominators. -/
theorem operationsWellDefined : OperationsWellDefined.{u} := by
  intro R _ S p p' q q' hp hq
  have eq_iff (x y : R × S) :
      Localization.mk x.1 x.2 = Localization.mk y.1 y.2 ↔ FractionRel S x y :=
    fractionEquality R S x.1 y.1 x.2 y.2
  have ep := (eq_iff p p').mpr hp
  have eq := (eq_iff q q').mpr hq
  refine ⟨(eq_iff _ _).mp ?_, (eq_iff _ _).mp ?_, (eq_iff _ _).mp ?_⟩
  · change Localization.mk (p.1 * (q.2 : R) + q.1 * (p.2 : R)) (p.2 * q.2) =
      Localization.mk (p'.1 * (q'.2 : R) + q'.1 * (p'.2 : R)) (p'.2 * q'.2)
    rw [← additionFormula R S, ← additionFormula R S, ep, eq]
  · change Localization.mk (p.1 * q.1) (p.2 * q.2) =
      Localization.mk (p'.1 * q'.1) (p'.2 * q'.2)
    rw [← multiplicationFormula R S, ← multiplicationFormula R S, ep, eq]
  · change Localization.mk (-p.1) p.2 = Localization.mk (-p'.1) p'.2
    rw [← negationFormula R S, ← negationFormula R S, ep]

/-- The identities and the source's additive-inverse equation. -/
theorem identityFormulas : IdentityFormulas.{u} := by
  intro R _ S
  refine ⟨Localization.mk_zero 1, Localization.mk_one, Localization.mk_zero, ?_⟩
  intro a s
  rw [← negationFormula R S]
  exact add_neg_cancel _

/-- The operations whose representative formulas were checked above satisfy
all the commutative unital ring laws. -/
theorem ringLaws : RingLaws.{u} := by
  intro R _ S
  exact ⟨add_assoc, add_comm, zero_add, add_zero, neg_add_cancel, add_neg_cancel,
    mul_assoc, mul_comm, one_mul, mul_one, mul_add, add_mul⟩

/-- The source map lambda is the canonical unital ring homomorphism. -/
def localizationMap (R : Type u) [CommRing R] (S : Submonoid R) :
    R →+* Localization S := algebraMap R (Localization S)

theorem canonicalMapFormula : CanonicalMapFormula.{u} := by
  intro R _ S a
  exact (Localization.mk_one_eq_algebraMap a).symm

/-- The image of s has precisely the stated inverse 1/s, on both sides. -/
theorem denominatorUnits : DenominatorUnits.{u} := by
  intro R _ S s
  have hinv : algebraMap R (Localization S) (s : R) * Localization.mk 1 s = 1 := by
    rw [canonicalMapFormula R S, Localization.mk_mul, mul_one, one_mul]
    exact Localization.mk_self s
  exact ⟨IsLocalization.map_units (Localization S) s, hinv,
    (mul_comm _ _).trans hinv⟩

end D07.Ch22.LocalizationConstruction
