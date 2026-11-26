import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.DenseRegularOpen
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.FinitePowerSeriesNormalization
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivationHypersurface
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivationsOfNonPowers
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SeparableInseparableTower
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Etale.Locus
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Localization.Integral
import Batteries.Tactic.OpenPrivate

noncomputable section

namespace CommutativeAlgebraNotes.Excellence

open scoped nonZeroDivisors
open Function

set_option linter.style.haveILetI false

private theorem regularRing_of_isLocalization {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (M : Submonoid A) [IsLocalization M B] (h : RegularRing A) :
    RegularRing B := by
  intro q hq
  let p := q.comap (algebraMap A B)
  letI := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    M (Localization.AtPrime q) q
  letI := h p
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (Localization.AtPrime q)).toRingEquiv

private theorem nonemptyRegularOpen_of_away {A : Type*} [CommRing A] [IsDomain A]
    {a : A} (ha : a ≠ 0) (h : RegularRing (Localization.Away a)) :
    Specs.HasNonemptyRegularOpen A := by
  refine ⟨PrimeSpectrum.basicOpen a, PrimeSpectrum.isOpen_basicOpen, ?_, ?_⟩
  · exact ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa using ha⟩
  · intro p hp
    let B := Localization.Away a
    have hd : Disjoint (Submonoid.powers a : Set A) (p.asIdeal : Set A) := by
      rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
    let q := p.asIdeal.map (algebraMap A B)
    letI : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.powers a) B p.asIdeal p.isPrime hd
    have hq : q.comap (algebraMap A B) = p.asIdeal :=
      IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers a) B p.isPrime hd
    letI := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers a) (Localization.AtPrime q) q
    letI := h q
    have he : PrimeSpectrum.comap (algebraMap A B) ⟨q, inferInstance⟩ = p :=
      PrimeSpectrum.ext hq
    have hr : PrimeSpectrum.comap (algebraMap A B) ⟨q, inferInstance⟩ ∈ regularLocus A :=
      show IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap A B))) from
        IsRegularLocalRing.of_ringEquiv
          (IsLocalization.algEquiv (q.comap (algebraMap A B)).primeCompl
            (Localization.AtPrime q) (Localization.AtPrime (q.comap (algebraMap A B)))).toRingEquiv
    exact he ▸ hr

/-- The embedding of a principal localization into the fraction field. -/
private def awayToFraction {A F : Type*} [CommRing A] [IsDomain A] [Field F]
    [Algebra A F] [IsFractionRing A F] (a : A) (ha : a ≠ 0) :
    Localization.Away a →+* F :=
  Localization.awayLift (algebraMap A F) a
    (IsUnit.mk0 _ ((map_eq_zero_iff _ (IsFractionRing.injective A F)).not.mpr ha))

@[simp] private theorem awayToFraction_algebraMap {A F : Type*}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F]
    {a : A} (ha : a ≠ 0) (x : A) :
    awayToFraction (F := F) a ha (algebraMap A (Localization.Away a) x) =
      algebraMap A F x :=
  IsLocalization.Away.lift_eq a
    (IsUnit.mk0 _ ((map_eq_zero_iff _ (IsFractionRing.injective A F)).not.mpr ha)) x

private theorem awayToFraction_injective {A F : Type*}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F]
    {a : A} (ha : a ≠ 0) : Injective (awayToFraction (F := F) a ha) := by
  apply (injective_iff_map_eq_zero _).2
  intro z hz
  obtain ⟨n, x, hx⟩ := IsLocalization.Away.surj a z
  have hx' := congrArg (awayToFraction (F := F) a ha) hx
  simp only [map_mul, map_pow, hz, zero_mul, awayToFraction_algebraMap] at hx'
  rw [← map_zero (algebraMap A F)] at hx'
  have ex : x = 0 := IsFractionRing.injective A F hx'.symm
  have hu := IsLocalization.Away.algebraMap_pow_isUnit (S := Localization.Away a) a n
  apply hu.mul_left_cancel (b := z) (c := 0)
  simpa only [ex, map_zero, mul_zero] using (mul_comm _ _).trans hx

/-- A finite type subalgebra of a fraction field lies in one principal localization. -/
private theorem exists_hom_to_away {S A B F : Type*}
    [CommRing S] [CommRing A] [IsDomain A] [CommRing B] [Field F]
    [Algebra S A] [Algebra S B] [Algebra S F] [Algebra A F] [IsScalarTower S A F]
    [IsFractionRing A F] [Algebra.FiniteType S B] (f : B →ₐ[S] F) :
    ∃ (a : A) (ha : a ≠ 0) (g : B →+* Localization.Away a),
      (awayToFraction a ha).comp g = f.toRingHom := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := S) (A := B)
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples A⁰ s f
  let a := (d : A)
  have ha : a ≠ 0 := nonZeroDivisors.ne_zero d.prop
  let F' := Localization.Away a
  let h : F' →+* F := awayToFraction a ha
  have hi : Injective h := awayToFraction_injective ha
  have hS : ∀ t : S, algebraMap S F t ∈ h.range := fun t =>
    ⟨algebraMap A F' (algebraMap S A t), by
      rw [show h (algebraMap A F' (algebraMap S A t)) = algebraMap A F (algebraMap S A t)
        from awayToFraction_algebraMap ha _, ← IsScalarTower.algebraMap_apply]⟩
  let T : Subalgebra S F := { h.range with algebraMap_mem' := hS }
  have hsT : ∀ x : B, f x ∈ T := by
    have hle : Algebra.adjoin S (s : Set B) ≤ T.comap f := by
      apply Algebra.adjoin_le
      intro x hx
      obtain ⟨y, hy⟩ := hd x hx
      change f x ∈ h.range
      let v : F' := IsLocalization.Away.invSelf a
      refine ⟨algebraMap A F' y * v, ?_⟩
      have hv : (algebraMap A F a) * h v = 1 := by
        have e := congrArg h (IsLocalization.Away.mul_invSelf (S := F') (x := a))
        rw [map_mul, map_one] at e
        change awayToFraction (F := F) a ha (algebraMap A (Localization.Away a) a) *
          h v = 1 at e
        rwa [awayToFraction_algebraMap] at e
      change algebraMap A F y = a • f x at hy
      rw [map_mul, show h (algebraMap A F' y) = algebraMap A F y
        from awayToFraction_algebraMap ha _, hy, Algebra.smul_def]
      calc
        _ = f x * (algebraMap A F a * h v) := by ring
        _ = f x := by rw [hv, mul_one]
    intro x
    exact hle (hs.symm ▸ (show x ∈ (⊤ : Subalgebra S B) from trivial))
  let e : F' ≃+* h.range := RingEquiv.ofBijective h.rangeRestrict
    ⟨fun _ _ e ↦ hi (congrArg Subtype.val e), h.rangeRestrict_surjective⟩
  let g := e.symm.toRingHom.comp (f.toRingHom.codRestrict h.range hsT)
  exact ⟨a, ha, g, by
    ext x
    exact congrArg Subtype.val (e.apply_symm_apply ⟨f x, hsT x⟩)⟩

/-- Two finite type models in a common fraction field have a common localization. -/
private theorem regularOpen_of_fractionModel {S A B F : Type*}
    [CommRing S] [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field F]
    [Algebra S A] [Algebra S B] [Algebra S F] [Algebra A F] [Algebra B F]
    [IsScalarTower S A F] [IsScalarTower S B F] [IsFractionRing A F] [IsFractionRing B F]
    [Algebra.FiniteType S A] [Algebra.FiniteType S B]
    (hB : RegularRing B) : Specs.HasNonemptyRegularOpen A := by
  obtain ⟨b, hb, f, hf⟩ := exists_hom_to_away (A := B) (IsScalarTower.toAlgHom S A F)
  let D := Localization.Away b
  let j : D →+* F := awayToFraction b hb
  let j' : D →ₐ[S] F :=
    ⟨j, fun s ↦ by
      rw [IsScalarTower.algebraMap_apply S B D, IsScalarTower.algebraMap_apply S B F]
      exact awayToFraction_algebraMap hb _⟩
  obtain ⟨a, ha, g, hg⟩ := exists_hom_to_away (A := A) j'
  let C := Localization.Away a
  let i : C →+* F := awayToFraction a ha
  have hi : Injective i := awayToFraction_injective ha
  have hj : Injective j := awayToFraction_injective hb
  have hgf (x : A) : g (f x) = algebraMap A C x := by
    apply hi
    change (i.comp g) (f x) = _
    rw [hg]
    change (j.comp f) x = _
    rw [hf]
    exact (awayToFraction_algebraMap ha x).symm
  letI : Algebra D C := g.toAlgebra
  letI : IsLocalization.Away (f a) C := by
    apply IsLocalization.Away.mk (f a)
    · change IsUnit (g (f a))
      rw [hgf]
      exact IsLocalization.Away.algebraMap_isUnit a
    · intro z
      obtain ⟨n, x, hx⟩ := IsLocalization.Away.surj a z
      refine ⟨n, f x, ?_⟩
      change z * g (f a) ^ n = g (f x)
      simpa only [hgf] using hx
    · intro x y h
      have eg : x = y := hj <| by
        have hcomp : i.comp g = j := hg
        rw [← hcomp]
        exact congrArg i h
      subst y
      exact ⟨0, by simp⟩
  exact nonemptyRegularOpen_of_away ha
    (regularRing_of_isLocalization (Submonoid.powers (f a))
      (regularRing_of_isLocalization (Submonoid.powers b) hB))

/-- A polynomial subalgebra with algebraic fraction extension. -/
private theorem exists_polynomial_base (R A : Type*) [CommRing R] [IsDomain R]
    [CommRing A] [IsDomain A] [Algebra R A] [Algebra.FiniteType R A]
    (hRA : Injective (algebraMap R A)) :
    ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A),
      letI : Algebra (MvPolynomial (Fin n) R) A := f.toRingHom.toAlgebra
      Injective f ∧ Algebra.IsAlgebraic (MvPolynomial (Fin n) R) A := by
  classical
  letI := (faithfulSMul_iff_algebraMap_injective R A).mpr hRA
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  haveI : Algebra.IsAlgebraic (Algebra.adjoin R (s : Set A)) A := by
    rw [hs]
    exact (Algebra.isIntegral_of_surjective
      (R := (⊤ : Subalgebra R A)) (B := A) (fun x ↦ ⟨⟨x, trivial⟩, rfl⟩)).isAlgebraic
  obtain ⟨t, ht, ht'⟩ := exists_isTranscendenceBasis_subset (R := R) (s : Set A)
  letI : Fintype t := ((s.finite_toSet).subset ht).fintype
  let e := (Fintype.equivFin t).symm
  let x : Fin (Fintype.card t) → A := fun i ↦ e i
  have hx : IsTranscendenceBasis R x := ht'.comp_equiv e
  let f := MvPolynomial.aeval x (R := R)
  have hf := (algebraicIndependent_iff_injective_aeval.mp hx.1)
  refine ⟨_, f, hf, ?_⟩
  letI : Algebra (MvPolynomial (Fin (Fintype.card t)) R) A := f.toRingHom.toAlgebra
  let E := Algebra.adjoin R (Set.range x)
  letI : Algebra (MvPolynomial (Fin (Fintype.card t)) R) E :=
    hx.1.aevalEquiv.toRingHom.toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin (Fintype.card t)) R) E A :=
    IsScalarTower.of_algebraMap_eq fun z ↦ (hx.1.algebraMap_aevalEquiv z).symm
  haveI : Algebra.IsAlgebraic E A := hx.isAlgebraic
  letI : Algebra.IsIntegral (MvPolynomial (Fin (Fintype.card t)) R) E :=
    Algebra.isIntegral_of_surjective hx.1.aevalEquiv.surjective
  exact ⟨fun z ↦ (Algebra.IsAlgebraic.isAlgebraic (R := E) z).restrictScalars_of_isIntegral _⟩

/-- Finiteness of the generic extension in an algebraic finite-type domain. -/
private theorem finite_fractionExtension (S A : Type*) [CommRing S] [IsDomain S]
    [CommRing A] [IsDomain A] [Algebra S A] [Algebra.FiniteType S A] [Algebra.IsAlgebraic S A]
    (h : Injective (algebraMap S A)) :
    letI : Algebra (FractionRing S) (FractionRing A) :=
      (IsFractionRing.lift (K := FractionRing S)
        (g := (algebraMap A (FractionRing A)).comp (algebraMap S A))
        ((IsFractionRing.injective A (FractionRing A)).comp h)).toAlgebra
    Module.Finite (FractionRing S) (FractionRing A) := by
  let F := FractionRing A
  let K := FractionRing S
  letI : Algebra K F :=
    (IsFractionRing.lift (K := K) (g := (algebraMap A F).comp (algebraMap S A))
      ((IsFractionRing.injective A F).comp h)).toAlgebra
  letI : IsScalarTower S K F := IsScalarTower.of_algebraMap_eq fun a ↦
    (IsScalarTower.algebraMap_apply S A F a).trans
      (IsFractionRing.lift_algebraMap (K := K) (g := (algebraMap A F).comp (algebraMap S A))
        ((IsFractionRing.injective A F).comp h) a).symm
  letI : FaithfulSMul S F := (faithfulSMul_iff_algebraMap_injective S F).mpr (by
    rw [IsScalarTower.algebraMap_eq S A F]
    exact (IsFractionRing.injective A F).comp h)
  letI : Module.IsTorsionFree S F :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective S F)
  letI : Algebra.IsAlgebraic S F := (IsFractionRing.isAlgebraic_iff' S A F).mp inferInstance
  letI : Algebra.IsAlgebraic K F := (IsFractionRing.comap_isAlgebraic_iff (A := S) (K := K) (C := F)).mp inferInstance
  letI : Algebra.EssFiniteType A F := .of_isLocalization F A⁰
  letI : Algebra.EssFiniteType S F := .comp S A F
  letI : Algebra.EssFiniteType K F := .of_comp S K F
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

open private regularRing_of_etale from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularAuxiliaryRings

/-- A separable finite generic extension is étale after shrinking the target. -/
private theorem regularAway_of_separableFractionExtension
    {B C M N : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [CommRing C] [IsDomain C] [Field M] [Field N]
    [Algebra B C] [Algebra B M] [Algebra B N] [Algebra C N] [Algebra M N]
    [IsScalarTower B C N] [IsScalarTower B M N]
    [IsFractionRing B M] [IsFractionRing C N] [Algebra.FiniteType B C]
    [Algebra.IsSeparable M N] (hB : RegularRing B) :
    ∃ (c : C), c ≠ 0 ∧ RegularRing (Localization.Away c) := by
  letI : Algebra.FormallyEtale B M := .of_isLocalization B⁰
  letI : Algebra.FormallyEtale M N := .of_isSeparable _ _
  letI : Algebra.FormallyEtale B N := .comp B M N
  let P : Ideal C := ⊥
  letI : IsLocalization P.primeCompl N := by
    change IsLocalization (⊥ : Ideal C).primeCompl N
    rw [Ideal.primeCompl_bot]
    infer_instance
  letI : Algebra.IsEtaleAt B P := .of_equiv
    ((IsLocalization.algEquiv P.primeCompl N (Localization.AtPrime P)).restrictScalars B)
  letI : Algebra.FinitePresentation B C := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨c, hc, het⟩ := Algebra.exists_etale_of_isEtaleAt (R := B) P
  let D := Localization.Away c
  have hsmall := Algebra.FiniteType.small (R := B) (S := D)
  let E := Shrink D
  let e : E ≃ₐ[B] D := Shrink.algEquiv B _
  letI : Algebra.Etale B E := Algebra.Etale.of_equiv e.symm
  letI : IsRegularRing E := regularRing_of_etale B E hB
  letI : IsRegularRing D := IsRegularRing.of_ringEquiv e.toRingEquiv
  exact ⟨c, by simpa [P] using hc, (regularRing_iff D).mpr inferInstance⟩

private theorem regularOpen_of_charZeroBase (R A : Type*) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [CharZero R] [CommRing A] [IsDomain A]
    [Algebra R A] [Algebra.FiniteType R A] (hinj : Injective (algebraMap R A))
    (hR : RegularRing R) : Specs.HasNonemptyRegularOpen A := by
  obtain ⟨n, f, hf, halg⟩ := exists_polynomial_base R A hinj
  let S := MvPolynomial (Fin n) R
  letI : Algebra S A := f.toRingHom.toAlgebra
  letI : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq fun r ↦ (f.commutes r).symm
  letI : Algebra.FiniteType S A := .of_restrictScalars_finiteType R S A
  letI : Algebra.IsAlgebraic S A := halg
  let K := FractionRing S
  let F := FractionRing A
  letI : Algebra K F :=
    (IsFractionRing.lift (K := K) (g := (algebraMap A F).comp (algebraMap S A))
      ((IsFractionRing.injective A F).comp hf)).toAlgebra
  letI : IsScalarTower S K F := IsScalarTower.of_algebraMap_eq fun r ↦
    (IsScalarTower.algebraMap_apply S A F r).trans
      (IsFractionRing.lift_algebraMap (K := K) (g := (algebraMap A F).comp (algebraMap S A))
        ((IsFractionRing.injective A F).comp hf) r).symm
  letI : Module.Finite K F := finite_fractionExtension S A hf
  letI : CharZero S := charZero_of_injective_ringHom (MvPolynomial.C_injective (Fin n) R)
  letI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective S K)
  letI : Algebra.IsSeparable K F := finiteExtension_isSeparable_of_charZero K F
  obtain ⟨a, ha, hreg⟩ := regularAway_of_separableFractionExtension (C := A) (M := K) (N := F)
    (regularRing_mvPolynomial R (Fin n) hR)
  exact nonemptyRegularOpen_of_away ha hreg

/-- Completeness passes to a quotient of a Noetherian complete local ring. -/
private theorem quotient_isAdicComplete {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (I : Ideal R) [I.IsPrime] :
    letI : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
    IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ I)) (R ⧸ I) := by
  let Q := R ⧸ I
  letI : IsLocalRing Q := .of_surjective' _ Ideal.Quotient.mk_surjective
  let m := IsLocalRing.maximalIdeal R
  have h : IsPrecomplete m Q := by
    apply (AdicCompletion.of_surjective_iff (I := m) (M := Q)).mp
    let f := (Ideal.Quotient.mkₐ R I).toLinearMap
    intro y
    obtain ⟨x, rfl⟩ := AdicCompletion.map_surjective m (f := f) Ideal.Quotient.mk_surjective y
    obtain ⟨r, rfl⟩ := AdicCompletion.of_surjective (I := m) (M := R) x
    exact ⟨f r, (AdicCompletion.map_of m f r).symm⟩
  have hm : m.map (algebraMap R Q) = IsLocalRing.maximalIdeal Q :=
    IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  letI : IsPrecomplete (IsLocalRing.maximalIdeal Q) Q :=
    hm ▸ (IsPrecomplete.map_algebraMap_iff (S := Q) (I := m) (M := Q)).mpr h
  exact {}


private theorem isFractionRing_of_closure {B F : Type*}
    [CommRing B] [IsDomain B] [Field F] [Algebra B F]
    (hinj : Injective (algebraMap B F))
    (h : Subfield.closure ((algebraMap B F).range : Set F) = ⊤) : IsFractionRing B F := by
  let g : FractionRing B →ₐ[B] F :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId B F) hinj
  have he : g.toRingHom.fieldRange = ⊤ := (IsFractionRing.lift_fieldRange hinj).trans h
  exact IsFractionRing.of_algEquiv
    (AlgEquiv.ofBijective g ⟨g.injective, RingHom.fieldRange_eq_top_iff.mp he⟩)

private theorem isFractionRing_away {B F : Type*} [CommRing B] [IsDomain B]
    [Field F] [Algebra B F] [IsFractionRing B F] {b : B} (hb : b ≠ 0) :
    letI : Algebra (Localization.Away b) F := (awayToFraction b hb).toAlgebra
    IsFractionRing (Localization.Away b) F := by
  let D := Localization.Away b
  letI : Algebra D F := (awayToFraction b hb).toAlgebra
  letI : IsScalarTower B D F := IsScalarTower.of_algebraMap_eq fun x ↦
    (awayToFraction_algebraMap hb x).symm
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers b) D F

universe u v

/-- A finite-type regular model equipped with its given fraction field. -/
private def HasRegularFractionModel (S : Type u) (F : Type v)
    [CommRing S] [Field F] [Algebra S F] : Prop :=
  ∃ (B : Type v) (_ : CommRing B) (_ : IsDomain B)
    (_ : Algebra S B) (_ : Algebra B F),
    Algebra.FiniteType S B ∧ IsFractionRing B F ∧ IsScalarTower S B F ∧ RegularRing B

private theorem fractionModel_self (S : Type u) (K : Type v)
    [CommRing S] [IsDomain S] [IsNoetherianRing S] [Field K] [Algebra S K]
    [IsFractionRing S K] (hS : RegularRing S) :
    HasRegularFractionModel S K := by
  have hsmall : Small.{v} S := small_of_injective (IsFractionRing.injective S K)
  let B := Shrink.{v} S
  let e : B ≃ₐ[S] S := Shrink.algEquiv S S
  letI : Algebra B K := ((algebraMap S K).comp e.toRingHom).toAlgebra
  letI : IsScalarTower S B K := IsScalarTower.of_algebraMap_eq fun s ↦ by
    change algebraMap S K s = algebraMap S K (e (algebraMap S B s))
    rw [e.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  have hB : Algebra.FiniteType S B := Algebra.FiniteType.equiv inferInstance e.symm
  have hK : IsFractionRing B K :=
    (IsFractionRing.isFractionRing_iff_of_base_ringEquiv K e.symm.toRingEquiv).mp inferInstance
  letI : IsRegularRing S := (regularRing_iff S).mp hS
  letI : IsRegularRing B := IsRegularRing.of_ringEquiv e.toRingEquiv.symm
  exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    hB, hK, inferInstance, (regularRing_iff B).mpr inferInstance⟩

/-- A field which is essentially of finite type has a finite-type fraction model. -/
private theorem essFiniteType_fractionModel {B N : Type*}
    [CommRing B] [Field N] [Algebra B N] [Algebra.EssFiniteType B N] :
    IsFractionRing (Algebra.EssFiniteType.subalgebra B N) N := by
  let C := Algebra.EssFiniteType.subalgebra B N
  have he : Algebra.EssFiniteType.submonoid B N = C⁰ := by
    ext x
    change IsUnit (x : N) ↔ x ∈ C⁰
    rw [isUnit_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero]
    exact (map_eq_zero_iff C.val Subtype.val_injective).not
  change IsLocalization C⁰ N
  rw [← he]
  infer_instance

private theorem fractionModel_separableStep
    {S : Type u} {M N : Type v} [CommRing S] [IsNoetherianRing S]
    [Field M] [Field N] [Algebra S M] [Algebra S N] [Algebra M N] [IsScalarTower S M N]
    [Module.Finite M N] [Algebra.IsSeparable M N]
    (hM : HasRegularFractionModel S M) : HasRegularFractionModel S N := by
  obtain ⟨B, _, _, _, _, hft, hfrac, ht, hB⟩ := hM
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing S B
  letI : Algebra B N := ((algebraMap M N).comp (algebraMap B M)).toAlgebra
  letI : IsScalarTower B M N := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower S B N := IsScalarTower.of_algebraMap_eq fun s ↦ by
    rw [IsScalarTower.algebraMap_apply S M N, IsScalarTower.algebraMap_apply S B M]
    rfl
  letI : Algebra.EssFiniteType B M := .of_isLocalization M B⁰
  letI : Algebra.EssFiniteType B N := .comp B M N
  let C := Algebra.EssFiniteType.subalgebra B N
  letI : IsFractionRing C N := essFiniteType_fractionModel
  obtain ⟨c, hc, hreg⟩ := regularAway_of_separableFractionExtension (C := C) (M := M) (N := N) hB
  let D := Localization.Away c
  letI : IsDomain D := IsLocalization.Away.isDomain D hc
  letI : Algebra D N := (awayToFraction c hc).toAlgebra
  letI : IsScalarTower S B C := .of_algebraMap_eq fun s ↦ by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply S B N s
  letI : Algebra.FiniteType S C := .trans (S := B) hft inferInstance
  letI : IsScalarTower S D N := IsScalarTower.of_algebraMap_eq (R := S) (S := D) (A := N)
    fun s ↦ by
      change algebraMap S N s = awayToFraction c hc (algebraMap S D s)
      rw [IsScalarTower.algebraMap_apply S C D, awayToFraction_algebraMap]
      rfl

  exact ⟨D, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, isFractionRing_away hc, inferInstance, hreg⟩


open Polynomial IntermediateField

/-- For a simple degree-p extension, descend the binomial and its root to a model. -/
private theorem fractionModel_binomial {S : Type u} {F : Type v}
    [CommRing S] [IsDomain S] [Field F] [Algebra (FractionRing S) F]
    (p : ℕ) [CharP (FractionRing S) p] (hp : p.Prime)
    (M : IntermediateField (FractionRing S) F) (z : F)
    (hz : z ∉ M) (B : Type v) [CommRing B] [IsDomain B] [Algebra S B]
    [Algebra S M] [Algebra B M] [IsFractionRing B M] [IsScalarTower S B M]
    (a : B) (ha : z ^ p = (algebraMap B M a : F)) :
    let N := (IntermediateField.adjoin M ({z} : Set F)).restrictScalars (FractionRing S)
    letI : Algebra S N := ((algebraMap (FractionRing S) N).comp
      (algebraMap S (FractionRing S))).toAlgebra
    ∀ [IsScalarTower S (FractionRing S) M] [Algebra.FiniteType S B],
      RegularRing (AdjoinRoot (X ^ p - C a)) → HasRegularFractionModel S N := by
  intro N _ _ hreg
  letI : Algebra S N := ((algebraMap (FractionRing S) N).comp
    (algebraMap S (FractionRing S))).toAlgebra
  let f : B[X] := X ^ p - C a
  let D := AdjoinRoot f
  have hN : M ≤ N := fun x hx ↦
    (IntermediateField.adjoin M ({z} : Set F)).algebraMap_mem ⟨x, hx⟩
  let iMN := IntermediateField.inclusion hN
  letI : Algebra B N := (iMN.toRingHom.comp (algebraMap B M)).toAlgebra
  have ht : ∀ s : S, algebraMap S N s = algebraMap B N (algebraMap S B s) := by
    intro s
    apply Subtype.ext
    change (algebraMap (FractionRing S) F (algebraMap S (FractionRing S) s)) =
      (algebraMap B M (algebraMap S B s) : F)
    rw [← IsScalarTower.algebraMap_apply S B M, IsScalarTower.algebraMap_apply S (FractionRing S) M]
    rfl
  letI : IsScalarTower S B N := .of_algebraMap_eq ht
  let z' : N := ⟨z, IntermediateField.mem_adjoin_simple_self M z⟩
  have hf : f.eval₂ (algebraMap B N) z' = 0 := by
    apply Subtype.ext
    change N.val.toRingHom (eval₂ (algebraMap B N) z' f) = N.val.toRingHom 0
    rw [Polynomial.hom_eval₂, map_zero]
    change f.eval₂ ((algebraMap M F).comp (algebraMap B M)) z = 0
    simp [f, ha]
  let φ : D →ₐ[B] N := AdjoinRoot.liftAlgHom f (Algebra.ofId B N) z' hf
  have hφ : Injective φ := by
    apply (injective_iff_map_eq_zero _).2
    intro x hx
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
    apply AdjoinRoot.mk_eq_zero.mpr
    apply (Polynomial.map_dvd_map (algebraMap B M) (IsFractionRing.injective B M)
      (Polynomial.monic_X_pow_sub_C a hp.ne_zero)).mp
    rw [show f.map (algebraMap B M) = minpoly M z by
      rw [minpoly_eq_X_pow_sub_C_of_pow_mem _ _ p hp M z (algebraMap B M a) hz ha]
      simp [f]]
    apply minpoly.dvd M z
    change q.eval₂ (algebraMap B N) z' = 0 at hx
    have hx' := congrArg N.val.toRingHom hx
    rw [Polynomial.hom_eval₂, map_zero] at hx'
    change q.eval₂ ((algebraMap M F).comp (algebraMap B M)) z = 0 at hx'
    rwa [Polynomial.aeval_def, Polynomial.eval₂_map]
  letI : IsDomain D := hφ.isDomain φ.toRingHom
  letI : Algebra D N := φ.toRingHom.toAlgebra
  letI : IsScalarTower S D N := .of_algebraMap_eq fun s ↦
    ((φ.restrictScalars S).commutes s).symm
  have hclosure : Subfield.closure ((algebraMap D N).range : Set N) = ⊤ := by
    let T := Subfield.closure ((algebraMap D N).range : Set N)
    have hT (x : M) : iMN x ∈ T := by
      obtain ⟨a₁, a₂, _, rfl⟩ := IsFractionRing.div_surjective B x
      rw [map_div₀]
      apply div_mem <;> exact Subfield.subset_closure ⟨algebraMap B D _, φ.commutes _⟩
    have hzT : z' ∈ T := Subfield.subset_closure
      ⟨AdjoinRoot.root f, AdjoinRoot.liftAlgHom_root _ _ _ _⟩
    let U : IntermediateField M F :=
      (T.map N.val.toRingHom).toIntermediateField fun x ↦ ⟨iMN x, hT x, rfl⟩
    have hle : IntermediateField.adjoin M ({z} : Set F) ≤ U := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact ⟨z', hzT, rfl⟩
    apply top_unique
    intro x _
    obtain ⟨y, hy, e⟩ := hle (show (x : F) ∈ IntermediateField.adjoin M ({z} : Set F) from x.2)
    exact (Subtype.ext e : y = x) ▸ hy
  exact ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    isFractionRing_of_closure hφ hclosure, inferInstance, hreg⟩

private def DetectsNonPowers (S : Type u) [CommRing S] [IsDomain S] (p : ℕ) : Prop :=
  ∀ (B : Type v) [CommRing B] [IsDomain B] [Algebra S B] [Algebra.FiniteType S B]
    (M : Type v) [Field M] [Algebra S M] [Algebra B M] [IsScalarTower S B M]
    [IsFractionRing B M] [Algebra (FractionRing S) M] [IsScalarTower S (FractionRing S) M]
    [Module.Finite (FractionRing S) M] (c : B),
    (¬ ∃ x : M, x ^ p = algebraMap B M c) → ∃ D : Derivation ℤ B B, D c ≠ 0

private theorem fractionModel_pureStep {S : Type u} {F : Type v}
    [CommRing S] [IsDomain S] [IsNoetherianRing S] [Field F] [Algebra (FractionRing S) F]
    (p : ℕ) [CharP (FractionRing S) p] (hp : p.Prime) (hdet : DetectsNonPowers.{u,v} S p)
    [Module.Finite (FractionRing S) F]
    (M : IntermediateField (FractionRing S) F) (b : F) (hb : b ∉ M) (hpow : b ^ p ∈ M) :
    letI : Algebra S M := ((algebraMap (FractionRing S) M).comp
      (algebraMap S (FractionRing S))).toAlgebra
    let N := (IntermediateField.adjoin M ({b} : Set F)).restrictScalars (FractionRing S)
    letI : Algebra S N := ((algebraMap (FractionRing S) N).comp
      (algebraMap S (FractionRing S))).toAlgebra
    HasRegularFractionModel S M → HasRegularFractionModel S N := by
  intro N hM
  let K := FractionRing S
  letI : Algebra S M := ((algebraMap K M).comp (algebraMap S K)).toAlgebra
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsScalarTower S K M := .of_algebraMap_eq' rfl
  obtain ⟨B, _, _, _, _, hft, hfrac, hSBM, hB⟩ := hM
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing S B
  obtain ⟨⟨a, d⟩, had⟩ := IsLocalization.surj B⁰ (⟨b ^ p, hpow⟩ : M)
  let c : B := a * (d : B) ^ (p - 1)
  let δ : M := algebraMap B M d
  have hδ : δ ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.prop
  let z : F := b * (δ : F)
  have hz : z ∉ M := by
    intro hz
    have hz' := M.div_mem hz δ.prop
    rw [show z / (δ : F) = b from mul_div_cancel_right₀ _ (Subtype.val_injective.ne hδ)] at hz'
    exact hb hz'
  have hzpow : z ^ p = (algebraMap B M c : F) := by
    have e := congrArg (fun x : M ↦ (x : F)) had
    change b ^ p * (δ : F) = (algebraMap B M a : F) at e
    have hp' : (δ : F) ^ p = (δ : F) ^ (p - 1) * (δ : F) := by
      conv_lhs => rw [← Nat.sub_add_cancel hp.one_le]
      exact pow_succ _ _
    calc
      z ^ p = b ^ p * (δ : F) ^ p := mul_pow _ _ _
      _ = (b ^ p * (δ : F)) * (δ : F) ^ (p - 1) := by rw [hp']; ring
      _ = (algebraMap B M c : F) := by
        rw [e]
        simp only [c, map_mul, map_pow, IntermediateField.coe_mul, IntermediateField.coe_pow]
        rfl
  letI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  have hc : ¬ ∃ x : M, x ^ p = algebraMap B M c := by
    rintro ⟨x, hx⟩
    apply hz
    have he : (x : F) ^ p = z ^ p := by
      rw [hzpow, ← IntermediateField.coe_pow, hx]
    have he' : (x : F) = z := frobenius_inj F p he
    exact he' ▸ x.prop
  obtain ⟨D, hD⟩ := hdet B M c hc
  let L := Localization.Away (D c)
  letI : IsDomain L := IsLocalization.Away.isDomain L hD
  let j : L →+* M := awayToFraction (D c) hD
  letI : Algebra L M := j.toAlgebra
  letI : IsFractionRing L M := isFractionRing_away hD
  letI : IsScalarTower S L M := .of_algebraMap_eq fun s ↦ by
    rw [IsScalarTower.algebraMap_apply S B L]
    change algebraMap S M s = j (algebraMap B L (algebraMap S B s))
    rw [show j (algebraMap B L (algebraMap S B s)) = _ from awayToFraction_algebraMap hD _]
    exact IsScalarTower.algebraMap_apply S B M s
  obtain ⟨E, hE, _⟩ := exists_localization_derivation (L := L) (Submonoid.powers (D c)) D
  let c' := algebraMap B L c
  have hu : IsUnit (E c') := by
    rw [hE]
    exact IsLocalization.Away.algebraMap_isUnit (D c)
  have reg := regularRing_quotient_X_pow_sub_C_of_isUnit_derivation
    (regularRing_of_isLocalization (Submonoid.powers (D c)) hB) E c' hu p hp.one_le
  have hza : z ^ p = (algebraMap L M c' : F) := by
    rw [hzpow]
    exact congrArg Subtype.val (awayToFraction_algebraMap hD c).symm
  have h := fractionModel_binomial p hp M z hz L c' hza reg
  have en : IntermediateField.adjoin M ({z} : Set F) = IntermediateField.adjoin M {b} :=
    IntermediateField.adjoin_simple_mul_algebraMap b δ hδ
  have en' := congrArg (IntermediateField.restrictScalars K) en
  exact (congrArg (fun P : IntermediateField K F ↦
    letI : Algebra S P := ((algebraMap K P).comp (algebraMap S K)).toAlgebra
    HasRegularFractionModel S P) en') ▸ h


private theorem fractionModel_tower {S : Type u} {F : Type v}
    [CommRing S] [IsDomain S] [IsNoetherianRing S] [Field F] [Algebra S F]
    [Algebra (FractionRing S) F] [IsScalarTower S (FractionRing S) F]
    [Module.Finite (FractionRing S) F] (p : ℕ) [CharP (FractionRing S) p]
    (hp : p.Prime) (hdet : DetectsNonPowers.{u,v} S p) (hS : RegularRing S) :
    HasRegularFractionModel S F := by
  let K := FractionRing S
  let V (M : IntermediateField K F) : Prop :=
    letI : Algebra S M := ((algebraMap K M).comp (algebraMap S K)).toAlgebra
    HasRegularFractionModel S M
  have hbot : V ⊥ := by
    let M : IntermediateField K F := ⊥
    letI : Algebra S M := ((algebraMap K M).comp (algebraMap S K)).toAlgebra
    letI : IsScalarTower S K M := .of_algebraMap_eq' rfl
    let e := (IntermediateField.botEquiv K F).symm.restrictScalars S
    letI : IsFractionRing S M := IsFractionRing.of_algEquiv e
    exact fractionModel_self S M hS
  have hstep {M N : IntermediateField K F} (h : IsSimpleFieldStep p M N) :
      V M → V N := by
    obtain ⟨b, rfl, hb, hsep | hpow⟩ := h
    · let E := IntermediateField.adjoin M ({b} : Set F)
      let N := E.restrictScalars K
      have hm : M ≤ N := fun x hx ↦ E.algebraMap_mem ⟨x, hx⟩
      let i := IntermediateField.inclusion hm
      letI : Algebra M N := i.toRingHom.toAlgebra
      letI : Algebra S M := ((algebraMap K M).comp (algebraMap S K)).toAlgebra
      letI : Algebra S N := ((algebraMap K N).comp (algebraMap S K)).toAlgebra
      letI : IsScalarTower K M N := .of_algebraMap_eq fun x ↦ (i.commutes x).symm
      letI : IsScalarTower S M N := .of_algebraMap_eq fun s ↦
        IsScalarTower.algebraMap_apply K M N (algebraMap S K s)
      letI : Module.Finite M N := Module.Finite.of_restrictScalars_finite K M N
      let j : N →ₐ[M] F := ⟨N.val.toRingHom, fun _ ↦ rfl⟩
      have hs : E ≤ separableClosure M F := IntermediateField.adjoin_le_iff.mpr (by
        rw [Set.singleton_subset_iff]
        exact mem_separableClosure_iff.mpr hsep)
      letI : Algebra.IsSeparable M N :=
        ⟨fun x ↦ IsSeparable.of_algHom M j (mem_separableClosure_iff.mp (hs x.prop))⟩
      exact fractionModel_separableStep (S := S) (M := M) (N := N)
    · exact fractionModel_pureStep p hp hdet M b hb hpow
  have hreach {N : IntermediateField K F}
      (h : Relation.ReflTransGen (IsSimpleFieldStep p) ⊥ N) : V N := by
    induction h with
    | refl => exact hbot
    | tail _ h ih => exact hstep h ih
  have htop := hreach (finiteExtension_has_simpleTower K F p hp)
  let N : IntermediateField K F := ⊤
  letI : Algebra S N := ((algebraMap K N).comp (algebraMap S K)).toAlgebra
  obtain ⟨B, _, _, _, _, hft, hfrac, ht, hB⟩ := htop
  let e : N ≃ₐ[K] F := IntermediateField.topEquiv
  letI : Algebra B F := (e.toRingHom.comp (algebraMap B N)).toAlgebra
  let e' : N ≃ₐ[B] F := { e.toRingEquiv with commutes' := fun _ ↦ rfl }
  letI : IsScalarTower S B F := .of_algebraMap_eq fun s ↦ by
    change algebraMap S F s = e (algebraMap B N (algebraMap S B s))
    rw [← IsScalarTower.algebraMap_apply S B N]
    change algebraMap S F s = e (algebraMap K N (algebraMap S K s))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply S K F]
  exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    hft, IsFractionRing.of_algEquiv e', inferInstance, hB⟩

open _root_.Specs.CommutativeAlgebraNotes.FrobeniusCoefficientDefinitions

private theorem coefficientTower_detectsNonPowers (k : Type u) [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (r s : ℕ) :
    DetectsNonPowers.{u,v} (CoefficientTowerBase k r s) p := by
  intro B _ _ _ _ M _ _ _ _ _ alg _ _ c hc
  let S := CoefficientTowerBase k r s
  let K := FractionRing S
  have hs : Injective (algebraMap S M) := by
    rw [IsScalarTower.algebraMap_eq S K M]
    exact (algebraMap K M).injective.comp (IsFractionRing.injective S K)
  have hb : Injective (algebraMap S B) := Injective.of_comp
    (g := algebraMap S B) (f := algebraMap B M) (by
      rwa [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq])
  let f : K →+* M := IsFractionRing.lift (K := K)
    (g := (algebraMap B M).comp (algebraMap S B)) ((IsFractionRing.injective B M).comp hb)
  have he : f = algebraMap K M := by
    apply IsFractionRing.ringHom_ext (A := S)
    intro x
    calc
      f (algebraMap S K x) = algebraMap B M (algebraMap S B x) :=
        IsFractionRing.lift_algebraMap _ _
      _ = algebraMap S M x := (IsScalarTower.algebraMap_apply S B M x).symm
      _ = algebraMap K M (algebraMap S K x) := IsScalarTower.algebraMap_apply S K M x
  have he' : alg = f.toAlgebra :=
    Algebra.algebra_ext _ _ fun x ↦ (RingHom.congr_fun he x).symm
  have hf : letI : Algebra K M := f.toAlgebra; Module.Finite K M :=
    he' ▸ ‹Module.Finite K M›
  exact @exists_derivation_ne_zero_of_not_pth_power k _ p _ _ r s B _ _ _ _ hb M _ _ _ hf c hc

private theorem regularOpen_of_powerSeries (k : Type u) [Field k]
    (r : ℕ) (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [IsDomain A]
    [Algebra (MvPowerSeries (Fin r) k) A] [Algebra.FiniteType (MvPowerSeries (Fin r) k) A]
    (hinj : Injective (algebraMap (MvPowerSeries (Fin r) k) A))
    (hR : IsRegularLocalRing (MvPowerSeries (Fin r) k)) : Specs.HasNonemptyRegularOpen A := by
  let R := MvPowerSeries (Fin r) k
  letI : IsRegularLocalRing R := hR
  letI : IsDomain R := NoZeroDivisors.to_isDomain R
  obtain ⟨s, f, hf, halg⟩ := exists_polynomial_base R A hinj
  let S := CoefficientTowerBase k r s
  letI : Algebra S A := f.toRingHom.toAlgebra
  letI : IsScalarTower R S A := .of_algebraMap_eq fun x ↦ (f.commutes x).symm
  letI : Algebra.FiniteType S A := .of_restrictScalars_finiteType R S A
  letI : Algebra.IsAlgebraic S A := halg
  let K := FractionRing S
  let F := FractionRing A
  letI : Algebra K F :=
    (IsFractionRing.lift (K := K) (g := (algebraMap A F).comp (algebraMap S A))
      ((IsFractionRing.injective A F).comp hf)).toAlgebra
  letI : IsScalarTower S K F := .of_algebraMap_eq fun x ↦
    (IsScalarTower.algebraMap_apply S A F x).trans
      (IsFractionRing.lift_algebraMap (K := K) (g := (algebraMap A F).comp (algebraMap S A))
        ((IsFractionRing.injective A F).comp hf) x).symm
  letI : Module.Finite K F := finite_fractionExtension S A hf
  letI : CharP K p := charP_of_injective_algebraMap (IsFractionRing.injective S K) p
  have hS : RegularRing S := regularRing_mvPolynomial R (Fin s)
    (AdvCommAlg.CohenMacaulay.regularLocal_localization_atPrime R)
  obtain ⟨B, _, _, _, _, hft, hfrac, ht, hB⟩ :=
    fractionModel_tower (F := F) p (Fact.out : p.Prime)
      (coefficientTower_detectsNonPowers k p r s) hS
  exact regularOpen_of_fractionModel (S := S) (A := A) (B := B) (F := F) hB

open _root_.Specs.CommutativeAlgebraNotes.CoefficientRings.FinitePowerSeriesNormalization

private theorem regularOpen_of_completeDomain (Q : Type u) (A : Type v)
    [CommRing Q] [IsLocalRing Q] [IsNoetherianRing Q] [IsDomain Q]
    [IsAdicComplete (IsLocalRing.maximalIdeal Q) Q] [CommRing A] [IsDomain A]
    [Algebra Q A] [Algebra.FiniteType Q A] (hQA : Injective (algebraMap Q A)) :
    Specs.HasNonemptyRegularOpen A := by
  obtain ⟨d, _, h | h⟩ := CoefficientRings.finitePowerSeriesNormalization Q
  · obtain ⟨_, h⟩ := h
    obtain ⟨_, _, f, _, _, _, _, _, _, hnorm⟩ := h
    obtain ⟨_, _, hreg, _, _, hf, _, hfinite, _⟩ := hnorm
    let k := IsLocalRing.ResidueField Q
    let S := MvPowerSeries (Fin d) k
    letI : Algebra S Q := f.toAlgebra
    letI : Algebra S A := ((algebraMap Q A).comp f).toAlgebra
    letI : IsScalarTower S Q A := .of_algebraMap_eq' rfl
    letI : IsRegularLocalRing S := hreg
    letI : Module.Finite S Q := hfinite
    letI : Algebra.FiniteType S A := .trans (S := Q) inferInstance inferInstance
    have hi : Injective (algebraMap S A) := hQA.comp hf
    rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hz
    · letI : Fact (ringChar k).Prime := ⟨hp⟩
      exact regularOpen_of_powerSeries k d (ringChar k) A hi hreg
    · letI : CharZero k := (CharP.ringChar_zero_iff_CharZero (R := k)).mp hz
      letI : CharZero S := charZero_of_injective_ringHom MvPowerSeries.C_injective
      exact regularOpen_of_charZeroBase S A hi
        (AdvCommAlg.CohenMacaulay.regularLocal_localization_atPrime S)
  · obtain ⟨p, _, _, _, h⟩ := h
    obtain ⟨_, _, _, _, Λ, _, _, _, hchar, _, _, _, _, _, f, _, _, _, _, _, _, _, hnorm⟩ := h
    obtain ⟨_, hdom, hreg, _, _, hf, _, hfinite, _⟩ := hnorm
    let S := MvPowerSeries (Fin (d - 1)) Λ
    letI : Algebra S Q := f.toAlgebra
    letI : Algebra S A := ((algebraMap Q A).comp f).toAlgebra
    letI : IsScalarTower S Q A := .of_algebraMap_eq' rfl
    letI : IsDomain S := hdom
    letI : IsRegularLocalRing S := hreg
    letI : Module.Finite S Q := hfinite
    letI : Algebra.FiniteType S A := .trans (S := Q) inferInstance inferInstance
    letI : CharZero Λ := hchar
    letI : CharZero S := charZero_of_injective_ringHom MvPowerSeries.C_injective
    exact regularOpen_of_charZeroBase S A (hQA.comp hf)
      (AdvCommAlg.CohenMacaulay.regularLocal_localization_atPrime S)

/-- A finite-type domain over a Noetherian complete local ring has a nonempty regular open. -/
theorem denseRegularOpen_completeLocal : Specs.denseRegularOpen_completeLocalType.{u,v} := by
  intro R A _ _ _ _ _ _ _ _
  let f := algebraMap R A
  let I := RingHom.ker f
  letI : I.IsPrime := RingHom.ker_isPrime f
  let Q := R ⧸ I
  letI : IsLocalRing Q := .of_surjective' _ Ideal.Quotient.mk_surjective
  letI : IsAdicComplete (IsLocalRing.maximalIdeal Q) Q := quotient_isAdicComplete I
  letI : Algebra Q A := (RingHom.kerLift f).toAlgebra
  letI : IsScalarTower R Q A := .of_algebraMap_eq' rfl
  letI : Algebra.FiniteType Q A := .of_restrictScalars_finiteType R Q A
  exact regularOpen_of_completeDomain Q A (RingHom.kerLift_injective _)

/-- A finite-type domain over any field has a nonempty regular open. -/
theorem denseRegularOpen_field : Specs.denseRegularOpen_fieldType.{u,v} := by
  intro k A _ _ _ _ _
  exact denseRegularOpen_completeLocal k A

/-- A finite-type domain over the integers has a nonempty regular open. -/
theorem denseRegularOpen_int : Specs.denseRegularOpen_intType.{v} := by
  intro A _ _ _
  let f := algebraMap ℤ A
  by_cases h : Injective f
  · exact regularOpen_of_charZeroBase ℤ A h ((regularRing_iff ℤ).mpr inferInstance)
  · let I := RingHom.ker f
    have hi : I ≠ ⊥ := fun hI ↦ h ((RingHom.injective_iff_ker_eq_bot f).mpr hI)
    letI : I.IsMaximal := Ideal.IsPrime.isMaximal (RingHom.ker_isPrime f) hi
    let k := ℤ ⧸ I
    letI : Field k := Ideal.Quotient.field I
    letI : Algebra k A := (RingHom.kerLift f).toAlgebra
    letI : IsScalarTower ℤ k A := .of_algebraMap_eq' rfl
    letI : Algebra.FiniteType k A := .of_restrictScalars_finiteType ℤ k A
    exact denseRegularOpen_field k A

end CommutativeAlgebraNotes.Excellence
