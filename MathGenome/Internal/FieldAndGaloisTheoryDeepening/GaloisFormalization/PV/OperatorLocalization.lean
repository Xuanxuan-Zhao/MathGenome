import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.OperatorRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.OperatorLocalization
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace GaloisFormalization.PV

universe u v w z

open scoped nonZeroDivisors

/-- The total quotient ring of a commutative ring. -/
abbrev TotalQuotientRing (R : Type u) [CommRing R] := FractionRing R

namespace Operator

variable {R : Type u} {S : Type v} {K : Type w} {L : Type z}
variable [CommRing R] [CommRing S] [CommRing K] [CommRing L]

/-- The ring map recording a ring homomorphism and the image of a derivation. -/
private def derivationGraph (d : Derivation ℤ R R) (f : R →+* S) :
    R →+* TrivSqZeroExt S S where
  toFun r := ⟨f r, f (d r)⟩
  map_one' := by ext <;> simp
  map_mul' r s := by
    apply TrivSqZeroExt.ext
    · exact _root_.map_mul f r s
    · change f (d (r * s)) = f r * f (d s) + f (d r) * f s
      rw [d.leibniz]
      simp only [smul_eq_mul, _root_.map_add, _root_.map_mul, mul_comm (f s)]
  map_zero' := by ext <;> simp
  map_add' r s := by
    apply TrivSqZeroExt.ext
    · exact _root_.map_add f r s
    · change f (d (r + s)) = f (d r) + f (d s)
      rw [d.map_add, _root_.map_add]

private def derivationOfSection (f : R →+* TrivSqZeroExt R R)
    (hf : ∀ r, (f r).fst = r) : Derivation ℤ R R :=
  Derivation.mk'
    ({ toFun := fun r => (f r).snd
       map_zero' := by rw [_root_.map_zero]; rfl
       map_add' := fun a b => by rw [_root_.map_add]; rfl } : R →+ R).toIntLinearMap
    (fun a b => by
      change (f (a * b)).snd = a * (f b).snd + b * (f a).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, hf]
      simp [hf, smul_eq_mul, mul_comm])

section DerivationLocalization

variable [Algebra R L] (M : Submonoid R) [IsLocalization M L]

private noncomputable def localizeDerivationGraph (d : Derivation ℤ R R) :
    L →+* TrivSqZeroExt L L :=
  IsLocalization.lift (M := M) (g := derivationGraph d (algebraMap R L))
    (fun s => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (IsLocalization.map_units L s))

private theorem localizeDerivationGraph_algebraMap (d : Derivation ℤ R R) (r : R) :
    localizeDerivationGraph M d (algebraMap R L r) =
      derivationGraph d (algebraMap R L) r :=
  IsLocalization.lift_eq _ _

/-- Extend a derivation to any localization by a multiplicative submonoid. -/
noncomputable def localizeDerivation (d : Derivation ℤ R R) : Derivation ℤ L L :=
  derivationOfSection (localizeDerivationGraph M d) <| by
    have h : (TrivSqZeroExt.fstHom L L L).toRingHom.comp (localizeDerivationGraph M d) =
        RingHom.id L := by
      apply IsLocalization.ringHom_ext M
      ext r
      rw [RingHom.comp_apply, RingHom.comp_apply, localizeDerivationGraph_algebraMap]
      rfl
    exact RingHom.congr_fun h

@[simp] theorem localizeDerivation_algebraMap (d : Derivation ℤ R R) (r : R) :
    localizeDerivation M d (algebraMap R L r) = algebraMap R L (d r) :=
  congrArg TrivSqZeroExt.snd (localizeDerivationGraph_algebraMap M d r)

theorem derivation_mk' (δ : Derivation ℤ L L) (r : R) (s : M) :
    δ (IsLocalization.mk' L r s) =
      IsLocalization.mk' L 1 s * δ (algebraMap R L r) -
        (algebraMap R L r * IsLocalization.mk' L 1 s ^ 2) * δ (algebraMap R L (s : R)) := by
  have hi : δ (IsLocalization.mk' L 1 s) =
      -(IsLocalization.mk' L 1 s ^ 2) * δ (algebraMap R L (s : R)) :=
    δ.leibniz_of_mul_eq_one (by rw [IsLocalization.mk'_spec, map_one])
  rw [IsLocalization.mk'_eq_mul_mk'_one, δ.leibniz, hi]
  simp only [smul_eq_mul, mul_assoc, neg_mul, mul_neg, sub_eq_add_neg]
  exact add_comm _ _

theorem localizedDerivation_quotientRule : Specs.localizedDerivationQuotientRule.{u, z} := by
  intro R L _ _ _ M _ d δ h r s
  let a := algebraMap R L
  let inv := IsLocalization.mk' L 1 s
  have hinv : a (s : R) * inv = 1 := by
    change algebraMap R L (s : R) * IsLocalization.mk' L 1 s = 1
    rw [IsLocalization.mk'_spec', map_one]
  have hsq : IsLocalization.mk' L 1 (s * s) = inv ^ 2 := by
    change IsLocalization.mk' L 1 (s * s) = IsLocalization.mk' L 1 s ^ 2
    rw [pow_two, ← IsLocalization.mk'_mul, one_mul]
  rw [derivation_mk' M, h, h, Specs.derivationFractionValue,
    IsLocalization.mk'_eq_mul_mk'_one (S := L) (d r * (s : R) - r * d (s : R)) (s * s),
    hsq, map_sub, _root_.map_mul, _root_.map_mul, sub_mul]
  change inv * a (d r) - (a r * inv ^ 2) * a (d (s : R)) =
    a (d r) * a (s : R) * inv ^ 2 - a r * a (d (s : R)) * inv ^ 2
  congr 1
  · calc
      inv * a (d r) = a (s : R) * inv * (inv * a (d r)) := by rw [hinv, one_mul]
      _ = a (d r) * a (s : R) * inv ^ 2 := by rw [pow_two]; ac_rfl
  · ac_rfl

theorem localizeDerivation_mk' (d : Derivation ℤ R R) (r : R) (s : M) :
    localizeDerivation M d (IsLocalization.mk' L r s) = Specs.derivationFractionValue M d r s :=
  localizedDerivation_quotientRule M d (localizeDerivation M d)
    (localizeDerivation_algebraMap M d) r s

include M in
theorem localizedDerivation_ext {δ ε : Derivation ℤ L L}
    (h : ∀ r, δ (algebraMap R L r) = ε (algebraMap R L r)) : δ = ε := by
  apply Derivation.ext
  intro x
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (M := M) x
  rw [derivation_mk' M, derivation_mk' M, h, h]

theorem localizedDerivation_existsUnique : Specs.localizedDerivationExistsUnique.{u, z} := by
  intro R L _ _ _ M _ d
  refine ⟨localizeDerivation M d, localizeDerivation_algebraMap M d, ?_⟩
  intro δ h
  exact localizedDerivation_ext M (fun r => (h r).trans (localizeDerivation_algebraMap M d r).symm)

end DerivationLocalization

section FractionEquiv

theorem ringEquiv_mem_nonZeroDivisors_iff (e : R ≃+* S) (s : R) :
    e s ∈ S⁰ ↔ s ∈ R⁰ := by
  constructor
  · exact mem_nonZeroDivisors_of_injective e.injective
  · intro hs
    have h := Set.mem_image_of_mem e hs
    change e s ∈ (R⁰).map e.toMonoidHom at h
    exact (MulEquivClass.map_nonZeroDivisors e) ▸ h

variable [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]

/-- The map of total quotient rings induced by a ring isomorphism. -/
noncomputable def fractionRingEquiv (e : R ≃+* S) : K ≃+* L :=
  IsFractionRing.ringEquivOfRingEquiv e

@[simp] theorem fractionRingEquiv_algebraMap (e : R ≃+* S) (r : R) :
    fractionRingEquiv e (algebraMap R K r) = algebraMap S L (e r) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap e r

@[simp] theorem fractionRingEquiv_symm (e : R ≃+* S) :
    (fractionRingEquiv (K := K) (L := L) e).symm = fractionRingEquiv e.symm :=
  IsFractionRing.ringEquivOfRingEquiv_symm e

theorem fractionRingEquiv_mk' (e : R ≃+* S) (r : R) (s : R⁰) :
    fractionRingEquiv e (IsLocalization.mk' K r s) =
      IsLocalization.mk' L (e r) ⟨e s, (ringEquiv_mem_nonZeroDivisors_iff e s).2 s.2⟩ :=
  IsLocalization.ringEquivOfRingEquiv_mk' (S := K) (Q := L) (MulEquivClass.map_nonZeroDivisors e) r s

theorem fractionRingEquiv_onFractions : Specs.fractionRingEquivOnFractions.{u, v, w, z} := by
  intro R S K L _ _ _ _ _ _ _ _ e r s
  exact ⟨(ringEquiv_mem_nonZeroDivisors_iff e s).2 s.2, fractionRingEquiv_mk' e r s⟩

theorem fractionOperatorEmbedding_injective (R : Type u) (K : Type w)
    [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K] :
    Function.Injective (algebraMap R K) :=
  IsFractionRing.injective R K

end FractionEquiv

section FractionOperator

variable {kind : OperatorKind} [Algebra R K] [IsFractionRing R K]

/-- Extend an operator to a ring obtained by inverting the non-zero-divisors. -/
noncomputable def fractionOperator (D : Operator kind R) : Operator kind K :=
  match kind, D with
  | .differential, d => differential (localizeDerivation R⁰ (toDerivation d))
  | .difference, σ => difference (fractionRingEquiv (toRingEquiv σ))

theorem fractionOperator_commutes (D : Operator kind R) :
    D.IsAlgebra (fractionOperator (K := K) D) := by
  intro r
  cases kind with
  | differential => exact (localizeDerivation_algebraMap R⁰ D.toDerivation r).symm
  | difference => exact (fractionRingEquiv_algebraMap D.toRingEquiv r).symm

theorem fractionOperator_isExtension (D : Operator kind R) :
    D.IsExtension (fractionOperator (K := K) D) :=
  ⟨fractionOperator_commutes D, fractionOperatorEmbedding_injective R K⟩

theorem fractionOperator_existsUnique : Specs.fractionOperatorExistsUnique.{u, w} := by
  intro kind R K _ _ _ _ D
  change Operator kind R at D
  show ∃! E : Operator kind K, D.IsAlgebra E
  refine ⟨fractionOperator (K := K) D, fractionOperator_commutes D, ?_⟩
  intro E h
  cases kind with
  | differential =>
    exact localizedDerivation_ext R⁰ (fun r => (h r).symm.trans
      (fractionOperator_commutes D r))
  | difference =>
    apply _root_.RingEquiv.toRingHom_injective
    apply IsLocalization.ringHom_ext R⁰
    exact _root_.RingHom.ext (fun r => (h r).symm.trans (fractionOperator_commutes D r))

/-- The canonical operator on the total quotient ring. -/
noncomputable abbrev totalQuotient (D : Operator kind R) : Operator kind (TotalQuotientRing R) :=
  fractionOperator D

@[simp] theorem fractionOperator_differential (d : Operator .differential R) :
    (fractionOperator (K := K) d).toDerivation = localizeDerivation R⁰ d.toDerivation := rfl

@[simp] theorem fractionOperator_difference (σ : Operator .difference R) :
    (fractionOperator (K := K) σ).toRingEquiv = fractionRingEquiv σ.toRingEquiv := rfl

theorem fractionOperator_difference_mk' (σ : Operator .difference R) (r : R) (s : R⁰) :
    fractionOperator (K := K) σ (IsLocalization.mk' K r s) =
      IsLocalization.mk' K (σ r)
        ⟨σ s, (ringEquiv_mem_nonZeroDivisors_iff σ.toRingEquiv s).2 s.2⟩ :=
  fractionRingEquiv_mk' σ.toRingEquiv r s

end FractionOperator

section FractionOperatorEquiv

variable {kind : OperatorKind} [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L]

theorem fractionRingEquiv_commutes {D : Operator kind R} {E : Operator kind S}
    {D' : Operator kind K} {E' : Operator kind L} (e : D.RingEquiv E)
    (hD : D.IsAlgebra D') (hE : E.IsAlgebra E') :
    D'.Commutes E' (fractionRingEquiv (K := K) (L := L) e.val) := by
  let f : K ≃+* L := fractionRingEquiv e.val
  have hf (r : R) : f (algebraMap R K r) = algebraMap S L (e.val r) :=
    fractionRingEquiv_algebraMap e.val r
  have he (r : R) : e.val (D r) = E (e.val r) := e.prop r
  have hbase (r : R) : f (D' (algebraMap R K r)) = E' (f (algebraMap R K r)) :=
    calc
      f (D' (algebraMap R K r)) = f (algebraMap R K (D r)) := congrArg f (hD r).symm
      _ = algebraMap S L (e.val (D r)) := hf (D r)
      _ = algebraMap S L (E (e.val r)) := congrArg (algebraMap S L) (he r)
      _ = E' (algebraMap S L (e.val r)) := hE (e.val r)
      _ = E' (f (algebraMap R K r)) := congrArg E' (hf r).symm
  cases kind with
  | differential =>
    have h : derivationGraph D'.toDerivation f.toRingHom =
        (derivationGraph E'.toDerivation (_root_.RingHom.id L)).comp f.toRingHom := by
      apply IsLocalization.ringHom_ext R⁰
      apply _root_.RingHom.ext
      intro r
      apply TrivSqZeroExt.ext
      · rfl
      · exact hbase r
    intro x
    exact congrArg TrivSqZeroExt.snd (_root_.RingHom.congr_fun h x)
  | difference =>
    have h : f.toRingHom.comp D'.toRingEquiv.toRingHom =
        E'.toRingEquiv.toRingHom.comp f.toRingHom := by
      apply IsLocalization.ringHom_ext R⁰
      apply _root_.RingHom.ext
      exact hbase
    exact _root_.RingHom.congr_fun h

/-- Extend a compatible isomorphism to the total rings of fractions. -/
noncomputable def fractionOperatorEquiv {D : Operator kind R} {E : Operator kind S}
    (e : D.RingEquiv E) : (fractionOperator (K := K) D).RingEquiv (fractionOperator (K := L) E) :=
  ⟨fractionRingEquiv e.val,
    fractionRingEquiv_commutes e (fractionOperator_commutes D) (fractionOperator_commutes E)⟩

@[simp] theorem fractionOperatorEquiv_algebraMap {D : Operator kind R} {E : Operator kind S}
    (e : D.RingEquiv E) (r : R) :
    (fractionOperatorEquiv (K := K) (L := L) e).val (algebraMap R K r) =
      algebraMap S L (e.val r) :=
  fractionRingEquiv_algebraMap e.val r

theorem fractionOperatorEquiv_existsUnique : Specs.fractionOperatorEquivExistsUnique.{u, v, w, z} := by
  intro kind R S K L _ _ _ _ _ _ _ _ D E D' E' e hD hE
  refine ⟨⟨fractionRingEquiv e.val, fractionRingEquiv_commutes e hD hE⟩,
    fractionRingEquiv_algebraMap e.val, ?_⟩
  intro f hf
  apply Subtype.ext
  apply _root_.RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext R⁰
  exact _root_.RingHom.ext (fun r => (hf r).trans (fractionRingEquiv_algebraMap e.val r).symm)

end FractionOperatorEquiv

section Quotient

variable {kind : OperatorKind}

private def quotientDerivationGraph (d : Operator .differential R) (I : _root_.Ideal R)
    (hI : d.IsStable (I : Set R)) : (R ⧸ I) →+* TrivSqZeroExt (R ⧸ I) (R ⧸ I) :=
  _root_.Ideal.Quotient.lift I (derivationGraph d.toDerivation (_root_.Ideal.Quotient.mk I)) <| by
    intro x hx
    apply TrivSqZeroExt.ext
    · exact _root_.Ideal.Quotient.eq_zero_iff_mem.mpr hx
    · exact _root_.Ideal.Quotient.eq_zero_iff_mem.mpr (hI.apply_mem hx)

/-- The derivation descends through a differential ideal. -/
def quotientDerivation (d : Operator .differential R) (I : _root_.Ideal R)
    (hI : d.IsStable (I : Set R)) : Derivation ℤ (R ⧸ I) (R ⧸ I) :=
  derivationOfSection (quotientDerivationGraph d I hI) <| by
    intro x
    obtain ⟨r, rfl⟩ := _root_.Ideal.Quotient.mk_surjective x
    rfl

private theorem map_ideal_eq_of_stable (σ : Operator .difference R) (I : _root_.Ideal R)
    (hI : σ.IsStable (I : Set R)) : I.map σ.toRingEquiv.toRingHom = I := by
  change I.map (σ.toRingEquiv : R →+* R) = I
  rw [_root_.Ideal.map_comap_of_equiv σ.toRingEquiv]
  ext x
  change σ.toRingEquiv.symm x ∈ I ↔ x ∈ I
  constructor
  · intro hx
    have hy := hI.apply_mem hx
    change σ.toRingEquiv (σ.toRingEquiv.symm x) ∈ I at hy
    simpa only [_root_.RingEquiv.apply_symm_apply] using hy
  · exact hI.symm_apply_mem

/-- The difference automorphism descends through an ideal stable in both directions. -/
def quotientDifference (σ : Operator .difference R) (I : _root_.Ideal R)
    (hI : σ.IsStable (I : Set R)) : (R ⧸ I) ≃+* (R ⧸ I) :=
  _root_.Ideal.quotientEquiv I I σ.toRingEquiv (map_ideal_eq_of_stable σ I hI).symm

/-- The induced operator on the quotient by a stable ideal. -/
def quotient (D : Operator kind R) (I : _root_.Ideal R) (hI : D.IsStable (I : Set R)) :
    Operator kind (R ⧸ I) :=
  match kind, D with
  | .differential, d => differential (quotientDerivation d I hI)
  | .difference, σ => difference (quotientDifference σ I hI)

@[simp] theorem quotient_mk (D : Operator kind R) (I : _root_.Ideal R)
    (hI : D.IsStable (I : Set R)) (r : R) :
    quotient D I hI (_root_.Ideal.Quotient.mk I r) = _root_.Ideal.Quotient.mk I (D r) := by
  cases kind <;> rfl

theorem quotient_commutes (D : Operator kind R) (I : _root_.Ideal R)
    (hI : D.IsStable (I : Set R)) : D.Commutes (quotient D I hI) (_root_.Ideal.Quotient.mk I) :=
  fun r => (quotient_mk D I hI r).symm

theorem quotientOperator_existsUnique : Specs.quotientOperatorExistsUnique.{u} := by
  intro kind R _ D I hI
  change Operator kind R at D
  show ∃! E : Operator kind (R ⧸ I), D.Commutes E (_root_.Ideal.Quotient.mk I)
  refine ⟨quotient D I hI, quotient_commutes D I hI, ?_⟩
  intro E h
  have he (x : R ⧸ I) : E x = quotient D I hI x := by
    obtain ⟨r, rfl⟩ := _root_.Ideal.Quotient.mk_surjective x
    exact (h r).symm.trans (quotient_commutes D I hI r)
  cases kind with
  | differential => exact Derivation.ext he
  | difference => exact _root_.RingEquiv.ext he

@[simp] theorem quotientDifference_symm_mk (σ : Operator .difference R)
    (I : _root_.Ideal R) (hI : σ.IsStable (I : Set R)) (r : R) :
    (quotientDifference σ I hI).symm (_root_.Ideal.Quotient.mk I r) =
      _root_.Ideal.Quotient.mk I (σ.toRingEquiv.symm r) := rfl

theorem quotientDifference_inverse : Specs.quotientDifferenceInverse.{u} := by
  intro R _ σ I τ h r
  exact (Commutes.difference_symm (D := σ) (E := τ) h r).symm

end Quotient

end Operator

end GaloisFormalization.PV
