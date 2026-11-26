import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.IntegralSmoothPropagation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

open Algebra AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct nonZeroDivisors

namespace LinearAlgebraicGroups.Albert

/-- A standard smooth chart embeds in the generic fiber of its étale map from
a polynomial ring. That generic fiber is reduced since it is étale over a field. -/
private theorem smooth_reduced_over_field (K B : Type) [Field K] [CommRing B]
    [Algebra K B] [Algebra.Smooth K B] : IsReduced B := by
  constructor
  intro x hx
  apply eq_zero_of_localization
  intro q hq
  obtain ⟨f, hfq, hf⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K q
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hf.out
  let := P.isStandardSmoothOfRelativeDimension (n := P.dimension) rfl
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    P.dimension K (Localization.Away f)
  let C := MvPolynomial (Fin P.dimension) K
  let D := Localization.Away f
  let : Algebra C D := g.toRingHom.toAlgebra
  have : Algebra.Etale C D := hg
  let F := FractionRing C
  have : IsReduced (F ⊗[C] D) := Algebra.FormallyUnramified.isReduced_of_field F _
  have hι : Function.Injective (Algebra.TensorProduct.includeRight :
      D →ₐ[C] F ⊗[C] D) :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective C F)
  have : IsReduced D :=
    ⟨fun x hx ↦ hι (by simpa using (hx.map (Algebra.TensorProduct.includeRight :
      D →ₐ[C] F ⊗[C] D)).eq_zero)⟩
  let g' : D →+* Localization.AtPrime q :=
    IsLocalization.Away.lift f (IsLocalization.map_units _ (⟨f, hfq⟩ : q.primeCompl))
  have hxd : algebraMap B D x = 0 := (hx.map (algebraMap B D)).eq_zero
  simpa only [map_zero, g', IsLocalization.Away.lift_eq] using congrArg g' hxd

private theorem domain_of_smooth_irreducible (K B : Type) [Field K] [CommRing B]
    [Algebra K B] [Algebra.Smooth K B] [IrreducibleSpace (PrimeSpectrum B)] : IsDomain B := by
  have := smooth_reduced_over_field K B
  have h : (⊥ : Ideal B).IsPrime := by
    simpa [(nilradical_eq_bot_iff (R := B)).mpr ‹IsReduced B›] using
      (PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical (R := B)).mp inferInstance
  have : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  refine (isDomain_iff_noZeroDivisors_and_nontrivial B).mpr ⟨⟨fun {a b} hab ↦ ?_⟩, ‹_›⟩
  simpa using h.mem_or_mem (show a * b ∈ (⊥ : Ideal B) by simpa using hab)

private theorem smooth_domain_field_fiber
    {A : Type} [CommRing A]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k],
      Algebra.Smooth k (k ⊗[ℤ] A) ∧ IrreducibleSpace (PrimeSpectrum (k ⊗[ℤ] A)))
    (k : Type) [Field k] : Algebra.Smooth k (k ⊗[ℤ] A) ∧ IsDomain (k ⊗[ℤ] A) := by
  let K := AlgebraicClosure k
  obtain ⟨hs, hi⟩ := h K
  have : Algebra.Smooth K (K ⊗[ℤ] A) := hs
  have : IrreducibleSpace (PrimeSpectrum (K ⊗[ℤ] A)) := hi
  let E := Algebra.TensorProduct.cancelBaseChange ℤ k K K A
  have : Algebra.Smooth K (K ⊗[k] (k ⊗[ℤ] A)) := Algebra.Smooth.of_equiv E.symm
  have : IsDomain (K ⊗[ℤ] A) := domain_of_smooth_irreducible K _
  let ι : (k ⊗[ℤ] A) →+* (K ⊗[ℤ] A) :=
    E.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
  have hι : Function.Injective ι := E.injective.comp <|
    Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap k K))
  exact ⟨Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat K, hι.isDomain ι⟩

private theorem torsion_mem_prime_multiple {A : Type} [CommRing A]
    (e : A →ₐ[ℤ] ℤ) (d : ℕ)
    (charts : ∀ (k : Type) [Field k], ∃ f : A, algebraMap ℤ k (e f) ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension d ℤ (Localization.Away f))
    (fibers : ∀ (k : Type) [Field k], IsDomain (k ⊗[ℤ] A))
    (p : ℤ) (hp : Prime p) {x : A} (hx : ∃ n : ℤ⁰, n • x = 0) :
    ∃ y : A, x = p • y ∧ ∃ n : ℤ⁰, n • y = 0 := by
  let I : Ideal ℤ := Ideal.span {p}
  have : I.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have : I.IsMaximal := Ideal.IsPrime.isMaximal inferInstance (by simpa [I] using hp.ne_zero)
  let k := ℤ ⧸ I
  let : Field k := Ideal.Quotient.field I
  obtain ⟨f, hf, hs⟩ := charts k
  have : Algebra.IsStandardSmooth ℤ (Localization.Away f) := hs.isStandardSmooth
  have : Algebra.Smooth ℤ (Localization.Away f) := inferInstance
  let D := Localization.Away f
  have hflat := Algebra.Smooth.flat ℤ (Localization.Away f)
  have hmodule : (inferInstance : Module ℤ (Localization.Away f)) =
      (inferInstance : Algebra ℤ (Localization.Away f)).toModule := Subsingleton.elim _ _
  have : Module.Flat ℤ (Localization.Away f) :=
    (congrArg (fun M ↦ @Module.Flat ℤ (Localization.Away f) _ _ M) hmodule).mpr hflat
  obtain ⟨n, hn⟩ := hx
  change (n : ℤ) • x = 0 at hn
  have hloc : algebraMap A D x = 0 := by
    have h : (n : ℤ) • algebraMap A D x = 0 := by
      simpa only [map_zsmul, map_zero] using congrArg (algebraMap A D) hn
    exact (smul_eq_zero.mp h).resolve_left (nonZeroDivisors.coe_ne_zero n)
  obtain ⟨⟨_, ⟨m, rfl⟩⟩, hm⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers f) D x).mp hloc
  have : IsDomain (k ⊗[ℤ] A) := fibers k
  let ι : A →ₐ[ℤ] k ⊗[ℤ] A := Algebra.TensorProduct.includeRight
  let ev : k ⊗[ℤ] A →ₐ[k] k :=
    (Algebra.TensorProduct.rid ℤ k k).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id k k) e)
  have hf' : ι f ≠ 0 := by
    intro h
    apply hf
    simpa [ι, ev] using congrArg ev h
  have hx' : ι x = 0 := by
    have h : ι f ^ m * ι x = 0 := by
      simpa only [map_mul, map_pow, map_zero] using congrArg ι hm
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hf')
  let E := Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I
  have hxI : x ∈ I.map (algebraMap ℤ A) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply E.injective
    change E (Ideal.Quotient.mk _ x) = E 0
    rw [map_zero, show E (Ideal.Quotient.mk _ x) = ι x from rfl]
    exact hx'
  rw [show I.map (algebraMap ℤ A) = Ideal.span {algebraMap ℤ A p} by simp [I, Ideal.map_span],
    Ideal.mem_span_singleton] at hxI
  obtain ⟨y, hy⟩ := hxI
  have hxy : x = p • y := hy.trans (Algebra.smul_def p y).symm
  refine ⟨y, hxy, ⟨(⟨p, mem_nonZeroDivisors_of_ne_zero hp.ne_zero⟩ : ℤ⁰) * n, ?_⟩⟩
  change (p * (n : ℤ)) • y = 0
  rwa [mul_comm, mul_smul, ← hxy]

private theorem flat_of_augmentation_charts {A : Type} [CommRing A]
    [Algebra.FinitePresentation ℤ A] (e : A →ₐ[ℤ] ℤ) (d : ℕ)
    (charts : ∀ (k : Type) [Field k], ∃ f : A, algebraMap ℤ k (e f) ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension d ℤ (Localization.Away f))
    (fibers : ∀ (k : Type) [Field k], IsDomain (k ⊗[ℤ] A)) :
    Module.Flat ℤ A := by
  classical
  -- The integer torsion is an A-submodule and has a common nonzero annihilator.
  let T := Submodule.torsion' A A ℤ⁰
  have := Algebra.FiniteType.isNoetherianRing ℤ A
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian T
  have hmem (x : s) : (x : A) ∈ T := hs ▸ Submodule.subset_span x.property
  choose c hc using fun x : s ↦ (Submodule.mem_torsion'_iff ℤ⁰ (x : A)).mp (hmem x)
  let a : ℤ⁰ := ∏ x : s, c x
  have ha : ∀ x ∈ T, (a : ℤ) • x = 0 := by
    have hle : T ≤ (DistribSMul.toLinearMap A A (a : ℤ)).ker := by
      rw [← hs, Submodule.span_le]
      intro x hx
      let i : s := ⟨x, hx⟩
      change (a : ℤ) • x = 0
      have ha' : a = (∏ j ∈ Finset.univ.erase i, c j) * c i :=
        (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
      rw [ha']
      change (((∏ j ∈ Finset.univ.erase i, c j : ℤ⁰) : ℤ) * (c i : ℤ)) • x = 0
      rw [mul_smul, show (c i : ℤ) • x = 0 from hc i, smul_zero]
    exact fun x hx ↦ hle hx
  -- Surjectivity of multiplication by each prime on T removes the prime factors.
  have cancel (b : ℤ) : b ≠ 0 → (∀ x ∈ T, b • x = 0) → ∀ x ∈ T, x = 0 := by
    induction b using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => simp
    | h₂ b hb =>
      intro _ h x hx
      apply hb.smul_left_cancel.mp
      simpa only [smul_zero] using h x hx
    | h₃ b p hb hp ih =>
      intro _ h
      apply ih hb
      intro x hx
      obtain ⟨y, hxy, hy⟩ := torsion_mem_prime_multiple e d charts fibers p hp hx
      rw [hxy, smul_smul, mul_comm]
      exact h y hy
  apply (IsDedekindDomain.flat_iff_torsion_eq_bot (R := ℤ) (M := A)).mpr
  exact bot_unique fun x hx ↦ cancel a (nonZeroDivisors.coe_ne_zero a) ha x hx

private theorem rankAtStalk_eq_of_chart {A : Type} [CommRing A] [Algebra.Smooth ℤ A]
    (f : A) (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n ℤ (Localization.Away f)]
    (q : PrimeSpectrum (Localization.Away f)) :
    Module.rankAtStalk Ω[A⁄ℤ] (q.comap (algebraMap A (Localization.Away f))) = n := by
  let D := Localization.Away f
  have : Nontrivial D := q.nontrivial
  have : Algebra.FormallyEtale A D := Algebra.FormallyEtale.of_isLocalization (.powers f)
  have : Algebra.IsStandardSmooth ℤ D :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let E := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℤ A D
  change Module.rankAtStalk Ω[A⁄ℤ] (q.comap (algebraMap A D)) = n
  rw [← Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_of_equiv E,
    Module.rankAtStalk_eq_finrank_of_free]
  change Cardinal.toNat (Module.rank D Ω[D⁄ℤ]) = n
  rw [Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := ℤ) (S := D) n,
    Cardinal.toNat_natCast]

private theorem smooth_of_relative_dimension {A : Type} [CommRing A]
    [Algebra.Smooth ℤ A] [PreconnectedSpace (PrimeSpectrum A)]
    (f : A) (d : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension d ℤ (Localization.Away f)]
    [Nontrivial (Localization.Away f)] :
    SmoothOfRelativeDimension d (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) := by
  have hr : ∀ x : PrimeSpectrum A, Module.rankAtStalk Ω[A⁄ℤ] x = d := by
    let q : PrimeSpectrum (Localization.Away f) := Classical.choice inferInstance
    intro x
    have hl := Module.isLocallyConstant_rankAtStalk (R := A) (M := Ω[A⁄ℤ])
    exact (hl.apply_eq_of_preconnectedSpace x _).trans (rankAtStalk_eq_of_chart f d q)
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)]
  rw [RingHom.locally_iff_span_eq_top]
  by_contra h
  obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ h
  obtain ⟨g, hgq, hg⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth ℤ q
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hg.out
  have hstd := P.isStandardSmoothOfRelativeDimension (n := P.dimension) rfl
  have hq' : (⟨q, hq.isPrime⟩ : PrimeSpectrum A) ∈
      Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    exact hgq
  obtain ⟨r, -⟩ := hq'
  have hdim : P.dimension = d := (rankAtStalk_eq_of_chart g P.dimension r).symm.trans (hr _)
  apply hgq (hle (Ideal.subset_span ?_))
  change ((algebraMap A (Localization.Away g)).comp
    (algebraMap ℤ A)).IsStandardSmoothOfRelativeDimension d
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact hdim ▸ hstd

private theorem spec_field_to_spec_int (k : Type) [Field k]
    (y : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℤ)) :
    y = Spec.map (CommRingCat.ofHom (algebraMap ℤ k)) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  congr 1
  ext n
  exact map_intCast _ _

private theorem smooth_integral_of_flat {A : Type} [CommRing A]
    [Algebra.FinitePresentation ℤ A] [Module.Flat ℤ A]
    (fibers : ∀ (k : Type) [Field k], Algebra.Smooth k (k ⊗[ℤ] A)) :
    Algebra.Smooth ℤ A := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℤ A))
  have : LocallyOfFinitePresentation f := (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have : Flat f := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hf : Smooth f := by
    apply Smooth.of_smooth_fiberToSpecResidueField
    intro y
    let k := (Spec (CommRingCat.of ℤ)).residueField y
    change Smooth (pullback.snd f ((Spec (CommRingCat.of ℤ)).fromSpecResidueField y))
    rw [spec_field_to_spec_int k ((Spec (CommRingCat.of ℤ)).fromSpecResidueField y)]
    have hp := isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct ℤ k A).flip
    have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (k ⊗[ℤ] A)))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr (fibers k))
    rw [← hp.isoPullback_inv_snd]
    exact smooth_comp _ _
  exact RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hf)

/-- Smooth irreducible geometric fibers and integral standard smooth augmentation
charts imply smoothness of the stated relative dimension and geometric connectedness. -/
theorem integralSmoothPropagation :
    Specs.LinearAlgebraicGroups.Albert.IntegralSmoothPropagation.IntegralSmoothPropagationType := by
  intro A _ _ e d charts geometric
  have fibers (k : Type) [Field k] := smooth_domain_field_fiber geometric k
  have : Module.Flat ℤ A := flat_of_augmentation_charts e d charts (fun k _ ↦ (fibers k).2)
  have : Algebra.Smooth ℤ A := smooth_integral_of_flat (fun k _ ↦ (fibers k).1)
  have : IsDomain A := by
    have : IsDomain (ℚ ⊗[ℤ] A) := (fibers ℚ).2
    let ι : A →ₐ[ℤ] ℚ ⊗[ℤ] A := Algebra.TensorProduct.includeRight
    exact (Algebra.TensorProduct.includeRight_injective (A := ℚ) (B := A)
      (IsFractionRing.injective ℤ ℚ)).isDomain ι
  obtain ⟨f, hf, hs⟩ := charts ℚ
  let g := (algebraMap ℤ ℚ).comp e.toRingHom
  let g' : Localization.Away f →+* ℚ := IsLocalization.Away.lift f (g := g) (isUnit_iff_ne_zero.mpr hf)
  have : Nontrivial (Localization.Away f) := g'.domain_nontrivial
  refine ⟨smooth_of_relative_dimension f d, ⟨?_⟩⟩
  intro k hk y Y fst snd h
  rw [spec_field_to_spec_int k y] at h
  have : IsDomain (k ⊗[ℤ] A) := (fibers k).2
  have hp := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct ℤ k A).flip
  let E := h.isoPullback ≪≫ hp.isoPullback.symm
  exact E.hom.homeomorph.connectedSpace_iff.mpr (inferInstanceAs
    (ConnectedSpace (Spec (CommRingCat.of (k ⊗[ℤ] A)))))

end LinearAlgebraicGroups.Albert
