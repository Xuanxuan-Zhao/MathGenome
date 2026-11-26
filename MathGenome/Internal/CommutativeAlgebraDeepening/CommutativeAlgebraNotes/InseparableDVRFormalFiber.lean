import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.InseparableDVRFormalFiber
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.NonexcellentDVRCompletion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ExcellentBasicRings
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ExcellentFiniteAlgebrasAndLocalizations
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.DedekindDomain.Dvr
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.AlgebraCore.P103.Ch07.RegularDomain

noncomputable section

open scoped Polynomial PowerSeries LaurentSeries TensorProduct
open Polynomial Algebra

namespace CommutativeAlgebraNotes.InseparableDVRFormalFiber

open NonexcellentDVRCompletion.Specs
open _root_.CommutativeAlgebraNotes.InseparableDVRFormalFiber.Specs

open private tensorChangeBase geometricallyRegular_fiber_of_localRingEquiv
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FiniteAndLocalizedGRings

section PolynomialBaseChange

/-- Scalar extension commutes with taking the polynomial quotient by a single relation. -/
private theorem tensorAdjoinRoot {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (g : R[X]) :
    ∃ e : S ⊗[R] AdjoinRoot g ≃ₐ[S] AdjoinRoot (g.map (algebraMap R S)),
      e (1 ⊗ₜ[R] AdjoinRoot.root g) = AdjoinRoot.root (g.map (algebraMap R S)) := by
  let q := g.map (algebraMap R S)
  let h := AdjoinRoot.mapAlgHom (Algebra.ofId R S) g q (dvd_refl q)
  let forward : S ⊗[R] AdjoinRoot g →ₐ[S] AdjoinRoot q :=
    Algebra.TensorProduct.lift (Algebra.ofId S _) h (fun _ _ => Commute.all _ _)
  let x : S ⊗[R] AdjoinRoot g := 1 ⊗ₜ AdjoinRoot.root g
  have hx : q.eval₂ (algebraMap S (S ⊗[R] AdjoinRoot g)) x = 0 := by
    have he : (algebraMap S (S ⊗[R] AdjoinRoot g)).comp (algebraMap R S) =
        (Algebra.TensorProduct.includeRight (R := R) (A := S)).toRingHom.comp
          (algebraMap R (AdjoinRoot g)) :=
      (IsScalarTower.algebraMap_eq R S _).symm.trans
        (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := AdjoinRoot g)).comp_algebraMap.symm
    rw [show q = g.map (algebraMap R S) from rfl, eval₂_map, he]
    let i : AdjoinRoot g →+* S ⊗[R] AdjoinRoot g :=
      Algebra.TensorProduct.includeRight.toRingHom
    change g.eval₂ (i.comp (algebraMap R (AdjoinRoot g))) (i (AdjoinRoot.root g)) = 0
    rw [← hom_eval₂, ← aeval_def, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  let backward : AdjoinRoot q →ₐ[S] S ⊗[R] AdjoinRoot g :=
    AdjoinRoot.liftAlgHom q (Algebra.ofId S _) x hx
  have hroot : forward x = AdjoinRoot.root q := by
    simp only [forward, x, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact AdjoinRoot.map_root (algebraMap R S) g q (dvd_refl q)
  refine ⟨AlgEquiv.ofAlgHom forward backward ?_ ?_, hroot⟩
  · apply AdjoinRoot.algHom_ext
    change forward (backward (AdjoinRoot.root q)) = AdjoinRoot.root q
    rw [show backward (AdjoinRoot.root q) = x from AdjoinRoot.liftAlgHom_root _ _ _ _, hroot]
  · apply Algebra.TensorProduct.ext
    · exact AlgHom.ext fun s => (backward.comp forward).commutes s
    · apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgHom.id_apply]
      change backward (forward x) = x
      rw [hroot]
      exact AdjoinRoot.liftAlgHom_root _ _ _ _

end PolynomialBaseChange

/-- Compare a base-changed fibre before and after identifying its two scalar fields. -/
private theorem compareFiberPresentation {R K L M T Q : Type*}
    [CommRing R] [CommRing K] [CommRing L] [CommRing M] [CommRing T] [CommRing Q]
    [Algebra R L] [Algebra K L] [Algebra R M] [Algebra K M] [Algebra R T] [Algebra M Q]
    (base : R ≃+* K)
    (hL : ∀ x : R, algebraMap R L x = algebraMap K L (base x))
    (hM : ∀ x : R, algebraMap R M x = algebraMap K M (base x))
    (g : T ≃ₐ[R] M) (e : M ⊗[K] L ≃ₐ[M] Q) :
    ∃ t : (L ⊗[R] T) ≃+* Q, ∀ l m, t (l ⊗ₜ[R] g.symm m) = e (m ⊗ₜ[K] l) := by
  let t₁ := Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) g
  let t₂ := tensorChangeBase base (RingEquiv.refl M) hL hM
  let t₃ := Algebra.TensorProduct.comm K L M
  let t := (t₁.trans t₂).toRingEquiv.trans (t₃.toRingEquiv.trans e.toRingEquiv)
  refine ⟨t, fun l a => ?_⟩
  change e (t₃ (t₂ (t₁ (l ⊗ₜ[R] g.symm a)))) = e (a ⊗ₜ[K] l)
  simp [t₁, t₂, t₃, tensorChangeBase, Algebra.TensorProduct.mapRingHom_tmul]

section FieldExtension

variable (p : ℕ) [Fact p.Prime] (f : (ZMod p)⟦X⟧)

local notation "M" => (ZMod p)⸨X⸩
local notation "K" => generatedField p f
local notation "L" => ExtendedField p f
local notation "α" => (f : M)

private theorem series_not_mem (hf : SeriesTranscendental (ZMod p) f) : α ∉ K := by
  classical
  let F := rationalField (ZMod p)
  let D := IntermediateField.adjoin F {α ^ p}
  have hD : D.restrictScalars (ZMod p) = K :=
    IntermediateField.restrictScalars_adjoin_eq_sup (ZMod p) F _
  intro hmem
  have hm : α ∈ D := by
    change α ∈ D.restrictScalars (ZMod p)
    rwa [hD]
  obtain ⟨r, s, hs⟩ := (IntermediateField.mem_adjoin_simple_iff F α).mp hm
  have ne_f : α ≠ 0 := by
    intro h
    apply hf
    exact ⟨X, X_ne_zero, by simp [h]⟩
  have hden : aeval (α ^ p) s ≠ 0 := by
    intro h
    exact ne_f (by simpa [h] using hs)
  have hpoly : expand F p s * X = expand F p r := by
    by_contra hn
    apply hf
    refine ⟨expand F p s * X - expand F p r, sub_ne_zero.mpr hn, ?_⟩
    rw [map_sub, map_mul, aeval_X, expand_aeval, expand_aeval, sub_eq_zero, mul_comm]
    exact (eq_div_iff hden).mp hs
  have hp := (Fact.out : p.Prime)
  have hne : expand F p s ≠ 0 := by
    apply (expand_ne_zero hp.pos).mpr
    intro h
    exact hden (by simp [h])
  have hdeg := congrArg (fun q : F[X] => q.natDegree % p) hpoly
  rw [natDegree_mul_X hne, natDegree_expand, natDegree_expand, Nat.add_mod] at hdeg
  simp [Nat.mod_eq_of_lt hp.one_lt] at hdeg

private theorem laurentCharP : CharP M p :=
  charP_of_injective_algebraMap (algebraMap (ZMod p) M).injective p

private def powerInBase : K :=
  ⟨α ^ p, NonexcellentDVRCompletion.pow_mem_generatedField p f⟩

private abbrev extensionPolynomial : K[X] := X ^ p - C (powerInBase p f)

private theorem extensionPolynomial_root : aeval α (extensionPolynomial p f) = 0 := by
  simp [powerInBase]

private theorem extensionPolynomial_monic : (extensionPolynomial p f).Monic :=
  monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero

private theorem extensionPolynomial_irreducible (hf : SeriesTranscendental (ZMod p) f) :
    Irreducible (extensionPolynomial p f) := by
  apply X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime)
  intro x hx
  let : CharP M p := laurentCharP p
  have hpow : ((x : M) ^ p) = α ^ p :=
    ((generatedField p f).val.map_pow x p).symm.trans (congrArg (fun y : K => (y : M)) hx)
  have heq : (x : M) = α := frobenius_inj M p hpow
  exact series_not_mem p f hf (heq ▸ x.property)

private theorem generator_integral : IsIntegral K α :=
  ⟨extensionPolynomial p f, extensionPolynomial_monic p f, extensionPolynomial_root p f⟩

private theorem generator_minpoly (hf : SeriesTranscendental (ZMod p) f) :
    minpoly K α = extensionPolynomial p f :=
  (minpoly.eq_of_irreducible_of_monic (extensionPolynomial_irreducible p f hf)
    (extensionPolynomial_root p f) (extensionPolynomial_monic p f)).symm

theorem extensionDegree (hf : SeriesTranscendental (ZMod p) f) : ExtensionDegree p f := by
  let b := IntermediateField.adjoin.powerBasis (generator_integral p f)
  have hd : b.dim = p := by
    change (minpoly K α).natDegree = p
    rw [generator_minpoly p f hf]
    exact natDegree_X_pow_sub_C
  exact ⟨b, rfl, hd, b.finrank.trans hd⟩

theorem fiberPresentation (hf : SeriesTranscendental (ZMod p) f) : FiberPresentation p f := by
  have hmap : (extensionPolynomial p f).map (algebraMap K M) = FiberPolynomial p f := by
    simp [powerInBase]
  let e₁ : AdjoinRoot (extensionPolynomial p f) ≃ₐ[K] L :=
    (AdjoinRoot.algEquivOfEq K _ _ (generator_minpoly p f hf).symm).trans
      (IntermediateField.adjoinRootEquivAdjoin K (generator_integral p f))
  have he₁ : e₁.symm (extendedGenerator p f) = AdjoinRoot.root (extensionPolynomial p f) := by
    rw [AlgEquiv.symm_apply_eq]
    simp only [e₁, AlgEquiv.trans_apply, AdjoinRoot.algEquivOfEq_root,
      IntermediateField.adjoinRootEquivAdjoin_apply_root]
    rfl
  let e₂ := Algebra.TensorProduct.congr (AlgEquiv.refl : M ≃ₐ[M] M) e₁.symm
  obtain ⟨e₃, he₃⟩ := tensorAdjoinRoot (S := M) (extensionPolynomial p f)
  let e₄ := AdjoinRoot.algEquivOfEq M _ _ hmap
  let e := e₂.trans (e₃.trans e₄)
  refine ⟨e, ?_, ?_⟩
  · change e₄ (e₃ (e₂ (1 ⊗ₜ extendedGenerator p f))) = _
    simp [e₂, he₁, he₃, e₄, AdjoinRoot.algEquivOfEq_root]
  · let R := GenericResidueField K
    let := residueExtensionAlgebra p f
    dsimp only
    intro g
    exact compareFiberPresentation (R := R) («K» := K) («L» := L)
      («M» := M) (T := GenericFiber K) (genericResidueEquiv K).toRingEquiv
      (fun _ => rfl) (fun _ => rfl) g e

theorem fiberPolynomialFactorization : FiberPolynomialFactorization p f := by
  let : CharP M p := laurentCharP p
  change X ^ p - C (α ^ p) = (X - C α) ^ p
  rw [sub_pow_char, map_pow]

theorem fiberNilpotent : FiberNilpotent p f := by
  change AdjoinRoot.mk (FiberPolynomial p f) (X - C α) ≠ 0 ∧
    (AdjoinRoot.mk (FiberPolynomial p f) (X - C α)) ^ p = 0
  constructor
  · intro hz
    have hdiv : FiberPolynomial p f ∣ X - C α := by
      simpa only [← (AdjoinRoot.mk (FiberPolynomial p f)).map_zero, AdjoinRoot.mk_eq_mk,
        sub_zero] using hz
    have hle := natDegree_le_of_dvd hdiv (X_sub_C_ne_zero α)
    rw [natDegree_X_pow_sub_C, natDegree_X_sub_C] at hle
    exact (Nat.not_le_of_lt (Fact.out : p.Prime).one_lt) hle
  · rw [← map_pow, ← show FiberPolynomial p f = (X - C α) ^ p from
      fiberPolynomialFactorization p f, AdjoinRoot.mk_self]

private theorem regularRing_isReduced {A : Type*} [CommRing A]
    (h : Excellence.RegularRing A) : IsReduced A := by
  apply isReduced_ofLocalizationMaximal
  intro J hJ
  let : J.IsMaximal := hJ
  let T := Localization.AtPrime J
  let : IsRegularLocalRing T := h J
  let : IsDomain T :=
    P103.RegularDomain.domain T ((IsRegularLocalRing.iff_finrank_cotangentSpace T).mp inferInstance)
  infer_instance

private theorem eq_zero_of_nilpotent_of_equiv {A B : Type*} [CommRing A] [CommRing B]
    [IsReduced A] (e : A ≃+* B) {z : B} (hz : IsNilpotent z) : z = 0 := by
  apply e.symm.injective
  rw [map_zero]
  exact (hz.map e.symm.toRingHom).eq_zero

theorem genericFiber_notGeometricallyRegular (hf : SeriesTranscendental (ZMod p) f) :
    ¬ Excellence.GeometricallyRegular (GenericResidueField K) (GenericFiber K) := by
  let R := GenericResidueField K
  let := residueExtensionAlgebra p f
  let : Algebra R K := (genericResidueEquiv K).toRingEquiv.toRingHom.toAlgebra
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite R K :=
    Module.Finite.of_surjective (Algebra.linearMap R K) (genericResidueEquiv K).surjective
  obtain ⟨b, -, -, -⟩ := extensionDegree p f hf
  let : Module.Finite K L := b.finite
  let : Module.Finite R L := Module.Finite.trans K L
  obtain ⟨_, g, _⟩ :=
    NonexcellentDVRCompletion.genericFiberIdentification K (rationalField_le_generatedField p f)
  obtain ⟨_, _, he⟩ := fiberPresentation p f hf
  obtain ⟨e, _⟩ := he g
  intro h
  let : IsReduced (L ⊗[R] GenericFiber K) := regularRing_isReduced (h L).2
  obtain ⟨hne, hpow⟩ := fiberNilpotent p f
  let z := AdjoinRoot.mk (FiberPolynomial p f) (X - C α)
  have hz : IsNilpotent z := ⟨p, hpow⟩
  exact hne (eq_zero_of_nilpotent_of_equiv (A := L ⊗[R] GenericFiber K) e hz)

private theorem notGRing [IsNoetherianRing (valuationRing K)]
    (hfail : ¬ Excellence.GeometricallyRegular (GenericResidueField K) (GenericFiber K)) :
    ¬ Excellence.IsGRing (valuationRing K) := by
  let V := valuationRing K
  let I := maximalIdeal K
  let A := Localization.AtPrime I
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let : IsNoetherianRing C :=
    P103.Ch07.CompletedNoetherian.completed_noetherian A (IsLocalRing.maximalIdeal A)
  let e : A ≃+* V := (IsLocalization.atUnits V I.primeCompl
    (fun _ hx => IsLocalRing.notMem_maximalIdeal.mp hx)).symm.toRingEquiv
  intro h
  have hg := ((Excellence.regularMap_algebraMap_iff A C).mp (h I)).2
  exact hfail (geometricallyRegular_fiber_of_localRingEquiv e ⊥ (hg ((⊥ : Ideal V).comap e.toRingHom)))

end FieldExtension

theorem inseparableExample : InseparableExample := by
  intro p hp f hf
  obtain ⟨hmem, hfrac, hval, hdvr, hunif, hquot, hcomp, hinv, hfinv, hgen⟩ :=
    NonexcellentDVRCompletion.construction p f
  let K := generatedField p f
  let : IsDiscreteValuationRing (valuationRing K) := hdvr
  have hfail := genericFiber_notGeometricallyRegular p f hf
  have hG := notGRing p f hfail
  exact ⟨hdvr, hmem, hfrac, hval, hunif, hquot, hcomp, hinv, hfinv, hgen,
    extensionDegree p f hf, fiberPresentation p f hf, fiberPolynomialFactorization p f,
    fiberNilpotent p f, hfail, hG, fun ⟨_, h', _, _⟩ => hG h'⟩

theorem excellentPolynomialDVR : ExcellentPolynomialDVR := by
  intro p hp
  let P := polynomialIdeal (ZMod p)
  let : P.IsPrime := (Ideal.span_singleton_prime X_ne_zero).mpr prime_X
  let A := Localization.AtPrime P
  have hP : P ≠ ⊥ := by
    simp [P]
  exact ⟨IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (ZMod p)[X] hP A,
    Excellence.Excellent.of_isLocalization P.primeCompl
      (Excellence.finiteTypeField_excellent (ZMod p) (ZMod p)[X])⟩

theorem exampleOfInseparableFormalFiber : ExampleType :=
  ⟨NonexcellentDVRCompletion.existsTranscendentalSeries, inseparableExample, excellentPolynomialDVR⟩

end CommutativeAlgebraNotes.InseparableDVRFormalFiber
