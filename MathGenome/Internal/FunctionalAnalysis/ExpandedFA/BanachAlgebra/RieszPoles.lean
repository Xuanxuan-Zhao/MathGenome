import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.RieszSplitting
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.RieszPoles

noncomputable section
set_option maxHeartbeats 300000
namespace ExpandedFA.BanachAlgebra.RieszPoles
open Set Filter
open scoped Topology
open ContourCalculus HolomorphicHomomorphism HolomorphicSpectralMapping RieszSplitting
open Specs.ExpandedFA.BanachAlgebra.Conventions
universe u

theorem isolated_splitting : Spec.IsolatedSplitting.{u} := by
  intro X _ _ _ T lam hlam
  obtain ⟨hmem, U, hU, hlamU, hUS⟩ := hlam
  have he : spectrum ℂ T \ {lam} = spectrum ℂ T \ U := by
    ext z
    simp only [Set.mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨hz, hne⟩
      refine ⟨hz, fun hzU => hne ?_⟩
      exact mem_singleton_iff.mp (hUS ▸ (show z ∈ U ∩ spectrum ℂ T from ⟨hzU, hz⟩))
    · rintro ⟨hz, hnU⟩
      exact ⟨hz, fun he => hnU (he ▸ hlamU)⟩
  have hK : IsCompact (spectrum ℂ T \ {lam}) := by
    rw [he]
    exact (spectrum.isCompact T).diff hU
  have hd : Disjoint ({lam} : Set ℂ) (spectrum ℂ T \ {lam}) := disjoint_sdiff_self_right
  obtain ⟨U₁, U₂, ho₁, ho₂, hdU, hs₁, hs₂, _⟩ :=
    separating_neighborhoods {lam} (spectrum ℂ T \ {lam}) isCompact_singleton hK hd
  refine ⟨hK, U₁, U₂, ho₁, ho₂, hdU, hs₁ (mem_singleton lam), hs₂, ?_⟩
  intro f hf₁ hf₂
  apply riesz_splitting X T {lam} (spectrum ℂ T \ {lam}) isCompact_singleton hK hd
    _ U₁ U₂ f ho₁ ho₂ hdU hs₁ hs₂ hf₁ hf₂
  change spectrum ℂ T = {lam} ∪ (spectrum ℂ T \ {lam})
  exact (union_sdiff_cancel (singleton_subset_iff.mpr hmem)).symm

lemma restrictions_unique {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {T : X →L[ℂ] X} {M : Submodule ℂ X} {S R : M →L[ℂ] M}
    (hS : ∀ x : M, (S x : X) = T x) (hR : ∀ x : M, (R x : X) = T x) : S = R := by
  ext x
  exact (hS x).trans (hR x).symm

theorem complement_invertible : Spec.ComplementInvertible.{u} := by
  intro X _ _ _ T P lam K hsplit hlam S hS
  obtain ⟨_, _, _, _, R₁, R₂, _, hR₂, _, hspec₂, _⟩ := hsplit
  have he : S = R₂ := restrictions_unique hS hR₂
  subst S
  have hu : IsUnit (algebraMap ℂ ((1 - P).range →L[ℂ] (1 - P).range) lam - R₂) := by
    exact not_not.mp (fun hn => hlam (hspec₂ ▸ hn))
  simpa only [neg_sub] using hu.neg

section Singleton
variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- A holomorphic extension of the scaled resolvent kills the corresponding
power when the spectrum consists of one point. This is Cauchy's theorem,
not an assumption about Laurent coefficients. -/
lemma shifted_pow_eq_zero_of_extension (hA : IsUnitalBanachAlgebra A)
    (a : A) (lam : ℂ) (hspec : spectrum ℂ a = {lam}) (m : ℕ)
    (g : ℂ → A) (hg : AnalyticAt ℂ g lam)
    (heq : ∀ᶠ z in 𝓝[≠] lam, (z - lam) ^ m • resolvent a z = g z) :
    (a - algebraMap ℂ A lam) ^ m = 0 := by
  have hd : ∀ᶠ z in 𝓝 lam, DifferentiableAt ℂ g z :=
    hg.eventually_analyticAt.mono (fun _ hz => hz.differentiableAt)
  rw [eventually_nhdsWithin_iff] at heq
  obtain ⟨U, hUs, hU, hlam⟩ := mem_nhds_iff.mp (hd.and heq)
  have hKU : spectrum ℂ a ⊆ U := by rw [hspec]; exact singleton_subset_iff.mpr hlam
  let Γ := selectedCycle (spectrum ℂ a) U
  have hΓ := selected_cycle_admissible A hA a U hU hKU
  have htr : Γ.trace ⊆ U := fun z hz => (hΓ.1 hz).1
  have hgd : DifferentiableOn ℂ g U := fun z hz => (hUs hz).1.differentiableWithinAt
  have hzero : cycleIntegral Γ g = 0 := by
    have hh := vector_cauchy_of_scalar homological_cauchy U Γ Cycle.empty g hU htr
      (by simp)
      (by intro z hz; rw [empty_winding]; exact hΓ.2.2.2 z hz)
      hgd
    simpa using hh
  have hp := polynomial_agreement A hA a U ((Polynomial.X - Polynomial.C lam) ^ m) hU hKU
  have hp' : holomorphicValue A a U (fun z => (z - lam) ^ m) =
      (a - algebraMap ℂ A lam) ^ m := by simpa using hp
  rw [← hp']
  change (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    cycleIntegral Γ (fun z => (z - lam) ^ m • resolvent a z) = 0
  have hi : cycleIntegral Γ (fun z => (z - lam) ^ m • resolvent a z) =
      cycleIntegral Γ g := by
    apply cycleIntegral_congr Γ
    intro z hz
    exact (hUs (htr hz)).2 (by
      intro he
      apply (hΓ.1 hz).2
      change z ∈ spectrum ℂ a
      rw [hspec]
      exact mem_singleton_iff.mpr he)
  rw [hi, hzero, smul_zero]

lemma resolvent_extension_of_negative_order (a : A) (lam : ℂ) (m : ℕ)
    (hm : 0 < m)
    (horder : meromorphicOrderAt (resolvent a) lam = ((-(m : ℤ) : ℤ) : WithTop ℤ)) :
    ∃ g : ℂ → A, AnalyticAt ℂ g lam ∧ g lam ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] lam, (z - lam) ^ m • resolvent a z = g z := by
  have hne : meromorphicOrderAt (resolvent a) lam ≠ 0 := by
    rw [horder]
    exact_mod_cast (show -(m : ℤ) ≠ 0 by omega)
  have hmer := meromorphicAt_of_meromorphicOrderAt_ne_zero hne
  obtain ⟨g, hg, hgn, he⟩ := (meromorphicOrderAt_eq_int_iff hmer).mp horder
  refine ⟨g, hg, hgn, ?_⟩
  filter_upwards [he, self_mem_nhdsWithin] with z hz hzne
  have hzl : z - lam ≠ 0 := sub_ne_zero.mpr hzne
  rw [hz, smul_smul]
  simp [zpow_neg, zpow_natCast, hzl]

lemma shifted_pow_eq_zero_of_pole (hA : IsUnitalBanachAlgebra A)
    (a : A) (lam : ℂ) (hspec : spectrum ℂ a = {lam}) (m : ℕ) (hm : 0 < m)
    (horder : meromorphicOrderAt (resolvent a) lam = ((-(m : ℤ) : ℤ) : WithTop ℤ)) :
    (a - algebraMap ℂ A lam) ^ m = 0 := by
  obtain ⟨g, hg, _, he⟩ := resolvent_extension_of_negative_order a lam m hm horder
  exact shifted_pow_eq_zero_of_extension hA a lam hspec m g hg he

/-- The polynomial numerator of the finite nilpotent resolvent expansion. -/
def resolventNumerator (a : A) (lam : ℂ) (m : ℕ) (z : ℂ) : A :=
  ∑ i ∈ Finset.range m, (z - lam) ^ (m - 1 - i) • (a - algebraMap ℂ A lam) ^ i

lemma resolventNumerator_analytic (a : A) (lam : ℂ) (m : ℕ) (z : ℂ) :
    AnalyticAt ℂ (resolventNumerator a lam m) z := by
  apply Finset.analyticAt_fun_sum
  intro i hi
  exact ((analyticAt_id.sub analyticAt_const).pow _).smul analyticAt_const

lemma resolventNumerator_at_center (a : A) (lam : ℂ) (m : ℕ) (hm : 0 < m) :
    resolventNumerator a lam m lam = (a - algebraMap ℂ A lam) ^ (m - 1) := by
  classical
  unfold resolventNumerator
  rw [Finset.sum_eq_single (m - 1)]
  · simp
  · intro i hi hne
    have hexp : m - 1 - i ≠ 0 := by
      have hi' := Finset.mem_range.mp hi
      omega
    simp [zero_pow hexp]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

lemma resolventNumerator_right (a : A) (lam : ℂ) (m : ℕ) (z : ℂ) :
    (algebraMap ℂ A z - a) * resolventNumerator a lam m z =
      (z - lam) ^ m • (1 : A) - (a - algebraMap ℂ A lam) ^ m := by
  have hc : Commute (a - algebraMap ℂ A lam) (algebraMap ℂ A (z - lam)) :=
    (Algebra.commutes (z - lam) _).symm
  have hh := hc.mul_neg_geom_sum₂ m
  have hshift : algebraMap ℂ A (z - lam) - (a - algebraMap ℂ A lam) =
      algebraMap ℂ A z - a := by rw [map_sub]; abel
  rw [hshift] at hh
  simp only [← map_pow] at hh
  simpa only [resolventNumerator, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one] using hh

lemma resolvent_eq_numerator (a : A) (lam : ℂ) (m : ℕ)
    (hnil : (a - algebraMap ℂ A lam) ^ m = 0) (z : ℂ) (hz : z ≠ lam)
    (hunit : IsUnit (algebraMap ℂ A z - a)) :
    resolvent a z = ((z - lam) ^ m)⁻¹ • resolventNumerator a lam m z := by
  have he := resolventNumerator_right a lam m z
  rw [hnil, sub_zero] at he
  have he' : (algebraMap ℂ A z - a) *
      (((z - lam) ^ m)⁻¹ • resolventNumerator a lam m z) = 1 := by
    rw [mul_smul_comm, he, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (sub_ne_zero.mpr hz)), one_smul]
  have hh := congrArg (fun b : A => Ring.inverse (algebraMap ℂ A z - a) * b) he'
  simpa only [resolvent, ← mul_assoc, Ring.inverse_mul_cancel _ hunit, one_mul, mul_one] using hh.symm

lemma analyticAt_resolvent_of_isUnit (a : A) (lam : ℂ)
    (hu : IsUnit (algebraMap ℂ A lam - a)) : AnalyticAt ℂ (resolvent a) lam := by
  have hl : AnalyticAt ℂ (fun z : ℂ => z • (1 : A) - a) lam :=
    (analyticAt_id.smul analyticAt_const).sub analyticAt_const
  have hi : AnalyticAt ℂ Ring.inverse (lam • (1 : A) - a) := by
    apply analyticOnNhd_inverse
    change IsUnit (lam • (1 : A) - a)
    simpa only [Algebra.algebraMap_eq_smul_one] using hu
  change AnalyticAt ℂ (fun z => Ring.inverse (algebraMap ℂ A z - a)) lam
  simpa only [Algebra.algebraMap_eq_smul_one, Function.comp_def] using
    hi.comp (f := fun z : ℂ => z • (1 : A) - a) hl

end Singleton

section Blocks
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Continuous compression to a projection range. -/
def compressBlock (P : X →L[ℂ] X) :
    (X →L[ℂ] X) →L[ℂ] (P.range →L[ℂ] P.range) :=
  (ContinuousLinearMap.compL ℂ P.range X P.range P.rangeRestrict).comp
    ((ContinuousLinearMap.compL ℂ P.range X X).flip P.range.subtypeL)

/-- Continuous inclusion of a block, followed by the coordinate projection. -/
def liftBlock (P : X →L[ℂ] X) :
    (P.range →L[ℂ] P.range) →L[ℂ] (X →L[ℂ] X) :=
  (ContinuousLinearMap.compL ℂ X P.range X P.range.subtypeL).comp
    ((ContinuousLinearMap.compL ℂ X P.range P.range).flip P.rangeRestrict)

lemma liftBlock_injective (P : X →L[ℂ] X) (hP : P * P = P) :
    Function.Injective (liftBlock P) := by
  intro S R he
  ext x
  have hx : P.rangeRestrict (x : X) = x := Subtype.ext (projection_fixed hP x.property)
  have hh := congrArg (fun Q : X →L[ℂ] X => Q x) he
  change (S (P.rangeRestrict (x : X)) : X) = (R (P.rangeRestrict (x : X)) : X) at hh
  rwa [hx] at hh

lemma compress_resolvent (T P : X →L[ℂ] X) (hP : P * P = P) (hc : Commute T P)
    (S : P.range →L[ℂ] P.range) (hS : ∀ x : P.range, (S x : X) = T x)
    (z : ℂ) (hT : IsUnit (algebraMap ℂ (X →L[ℂ] X) z - T))
    (hSu : IsUnit (algebraMap ℂ (P.range →L[ℂ] P.range) z - S)) :
    compressBlock P (resolvent T z) = resolvent S z := by
  have hi : (algebraMap ℂ (P.range →L[ℂ] P.range) z - S) *
      compressBlock P (resolvent T z) = 1 := by
    ext x
    change z • P (resolvent T z x) - (S (compressBlock P (resolvent T z) x) : X) = x
    rw [hS]
    change z • P (resolvent T z x) - T (P (resolvent T z x)) = x
    have hcomm (v : X) : T (P v) = P (T v) :=
      congrArg (fun Q : X →L[ℂ] X => Q v) hc.eq
    rw [hcomm, ← map_smul, ← map_sub]
    have hi := congrArg (fun Q : X →L[ℂ] X => Q x)
      (Ring.mul_inverse_cancel _ hT)
    change z • resolvent T z x - T (resolvent T z x) = (x : X) at hi
    rw [hi]
    exact projection_fixed hP x.property
  have hh := congrArg (fun Q => resolvent S z * Q) hi
  simpa only [resolvent, ← mul_assoc, Ring.inverse_mul_cancel _ hSu, one_mul, mul_one] using hh

lemma resolvent_blocks (T P : X →L[ℂ] X) (hc : Commute T P)
    (S₁ : P.range →L[ℂ] P.range) (S₂ : (1 - P).range →L[ℂ] (1 - P).range)
    (h₁ : ∀ x : P.range, (S₁ x : X) = T x)
    (h₂ : ∀ x : (1 - P).range, (S₂ x : X) = T x)
    (z : ℂ)
    (hu₁ : IsUnit (algebraMap ℂ (P.range →L[ℂ] P.range) z - S₁))
    (hu₂ : IsUnit (algebraMap ℂ ((1 - P).range →L[ℂ] (1 - P).range) z - S₂)) :
    resolvent T z = liftBlock P (resolvent S₁ z) + liftBlock (1 - P) (resolvent S₂ z) := by
  have hu : IsUnit (algebraMap ℂ (X →L[ℂ] X) z - T) := by
    by_contra hn
    rcases spectrum_subset_union hc S₁ S₂ h₁ h₂ hn with h | h
    · exact h hu₁
    · exact h hu₂
  have hi : (algebraMap ℂ (X →L[ℂ] X) z - T) *
      (liftBlock P (resolvent S₁ z) + liftBlock (1 - P) (resolvent S₂ z)) = 1 := by
    ext x
    have hh₁ := congrArg (fun Q : P.range →L[ℂ] P.range => (Q (P.rangeRestrict x) : X))
      (Ring.mul_inverse_cancel _ hu₁)
    have hh₂ := congrArg (fun Q : (1 - P).range →L[ℂ] (1 - P).range =>
      (Q ((1 - P).rangeRestrict x) : X)) (Ring.mul_inverse_cancel _ hu₂)
    change z • (resolvent S₁ z (P.rangeRestrict x) : X) -
      (S₁ (resolvent S₁ z (P.rangeRestrict x)) : X) = P x at hh₁
    change z • (resolvent S₂ z ((1 - P).rangeRestrict x) : X) -
      (S₂ (resolvent S₂ z ((1 - P).rangeRestrict x)) : X) = (1 - P) x at hh₂
    rw [h₁] at hh₁
    rw [h₂] at hh₂
    change z • ((resolvent S₁ z (P.rangeRestrict x) : X) +
        (resolvent S₂ z ((1 - P).rangeRestrict x) : X)) -
      T ((resolvent S₁ z (P.rangeRestrict x) : X) +
        (resolvent S₂ z ((1 - P).rangeRestrict x) : X)) = x
    rw [smul_add, map_add, add_sub_add_comm, hh₁, hh₂]
    simp
  have hh := congrArg (fun Q => resolvent T z * Q) hi
  simpa only [resolvent, ← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul, mul_one] using hh.symm

end Blocks

section PoleBlock
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma unit_of_singleton_spectrum {A : Type*} [Ring A] [Algebra ℂ A]
    {a : A} {lam z : ℂ} (h : spectrum ℂ a = {lam}) (hz : z ≠ lam) :
    IsUnit (algebraMap ℂ A z - a) := by
  apply not_not.mp
  intro hn
  exact hz (mem_singleton_iff.mp (h ▸ hn))

lemma pole_of_nilpotent_block (T P : X →L[ℂ] X) (lam : ℂ) (K : Set ℂ)
    (hsplit : RieszSplitting.Spec.SplittingData T P {lam} K) (hlam : lam ∉ K)
    (S : P.range →L[ℂ] P.range) (hS : ∀ x : P.range, (S x : X) = T x)
    (m : ℕ) (hnil : Spec.NilpotentOfOrder
      (S - algebraMap ℂ (P.range →L[ℂ] P.range) lam) m) : Spec.PoleOfOrder T lam m := by
  obtain ⟨hP, hc, hcl₁, hcl₂, R₁, R₂, h₁, h₂, hspec₁, hspec₂, _⟩ := hsplit
  have he : S = R₁ := restrictions_unique hS h₁
  subst S
  haveI : CompleteSpace P.range := hcl₁.isComplete.completeSpace_coe
  haveI : CompleteSpace (1 - P).range := hcl₂.isComplete.completeSpace_coe
  have hu₂ : IsUnit (algebraMap ℂ ((1 - P).range →L[ℂ] (1 - P).range) lam - R₂) :=
    not_not.mp (fun hn => hlam (hspec₂ ▸ hn))
  let G₁ : ℂ → (X →L[ℂ] X) := fun z => liftBlock P (resolventNumerator R₁ lam m z)
  let G₂ : ℂ → (X →L[ℂ] X) := fun z => liftBlock (1 - P) (resolvent R₂ z)
  let G : ℂ → (X →L[ℂ] X) := fun z => G₁ z + (z - lam) ^ m • G₂ z
  have hg₁ : AnalyticAt ℂ G₁ lam := by
    change AnalyticAt ℂ ((liftBlock P) ∘ resolventNumerator R₁ lam m) lam
    apply AnalyticAt.comp
    · exact ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := P.range →L[ℂ] P.range)
        (F := X →L[ℂ] X) (liftBlock P) _
    · exact resolventNumerator_analytic R₁ lam m lam
  have hg₂ : AnalyticAt ℂ G₂ lam := by
    change AnalyticAt ℂ ((liftBlock (1 - P)) ∘ resolvent R₂) lam
    apply AnalyticAt.comp
    · exact ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := (1 - P).range →L[ℂ] (1 - P).range)
        (F := X →L[ℂ] X) (liftBlock (1 - P)) _
    · exact analyticAt_resolvent_of_isUnit R₂ lam hu₂
  have hg : AnalyticAt ℂ G lam :=
    hg₁.add (((analyticAt_id.sub analyticAt_const).pow m).smul hg₂)
  have hgn : G lam ≠ 0 := by
    have hv : G lam = liftBlock P ((R₁ - algebraMap ℂ (P.range →L[ℂ] P.range) lam) ^ (m - 1)) := by
      change liftBlock P (resolventNumerator R₁ lam m lam) + (lam - lam) ^ m • G₂ lam = _
      rw [sub_self, zero_pow (Nat.ne_of_gt hnil.1), zero_smul, add_zero,
        resolventNumerator_at_center R₁ lam m hnil.1]
    rw [hv]
    exact fun hz => hnil.2.2 ((liftBlock_injective P hP) (hz.trans (map_zero (liftBlock P)).symm))
  have hevent : ∀ᶠ z in 𝓝 lam, z ∈ resolventSet ℂ R₂ :=
    (spectrum.isOpen_resolventSet (𝕜 := ℂ) R₂).mem_nhds hu₂
  have hrep : ∀ᶠ z in 𝓝[≠] lam,
      resolvent T z = (z - lam) ^ (-(m : ℤ)) • G z := by
    filter_upwards [hevent.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz₂ hz
    have hz₁ := unit_of_singleton_spectrum hspec₁ hz
    rw [resolvent_blocks T P hc R₁ R₂ h₁ h₂ z hz₁ hz₂,
      resolvent_eq_numerator R₁ lam m hnil.2.1 z hz hz₁, map_smul]
    dsimp only [G, G₁, G₂]
    rw [smul_add, smul_smul]
    simp only [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (sub_ne_zero.mpr hz)), one_smul]
  have hmer : MeromorphicAt (resolvent T) lam :=
    MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr ⟨-(m : ℤ), G, hg, hrep⟩
  exact ⟨hnil.1, (meromorphicOrderAt_eq_int_iff hmer).mpr ⟨G, hg, hgn, hrep⟩⟩

lemma block_pow_eq_zero_of_pole (T P : X →L[ℂ] X) (lam : ℂ) (K : Set ℂ)
    (hsplit : RieszSplitting.Spec.SplittingData T P {lam} K) (hlam : lam ∉ K)
    (S : P.range →L[ℂ] P.range) (hS : ∀ x : P.range, (S x : X) = T x)
    (m : ℕ) (hpole : Spec.PoleOfOrder T lam m) :
    (S - algebraMap ℂ (P.range →L[ℂ] P.range) lam) ^ m = 0 := by
  obtain ⟨hP, hc, hcl₁, hcl₂, R₁, R₂, h₁, h₂, hspec₁, hspec₂, _⟩ := hsplit
  have heS : S = R₁ := restrictions_unique hS h₁
  subst S
  rcases subsingleton_or_nontrivial P.range with hM | hM
  · letI := hM
    exact Subsingleton.elim _ _
  letI := hM
  haveI : CompleteSpace P.range := hcl₁.isComplete.completeSpace_coe
  haveI : CompleteSpace (1 - P).range := hcl₂.isComplete.completeSpace_coe
  obtain ⟨g, hg, _, he⟩ := resolvent_extension_of_negative_order T lam m hpole.1 hpole.2
  have hu₂ : IsUnit (algebraMap ℂ ((1 - P).range →L[ℂ] (1 - P).range) lam - R₂) :=
    not_not.mp (fun hn => hlam (hspec₂ ▸ hn))
  have hevent : ∀ᶠ z in 𝓝 lam, z ∈ resolventSet ℂ R₂ :=
    (spectrum.isOpen_resolventSet (𝕜 := ℂ) R₂).mem_nhds hu₂
  have hg₁ : AnalyticAt ℂ (fun z => compressBlock P (g z)) lam := by
    change AnalyticAt ℂ ((compressBlock P) ∘ g) lam
    apply AnalyticAt.comp
    · exact ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := X →L[ℂ] X)
        (F := P.range →L[ℂ] P.range) (compressBlock P) _
    · exact hg
  have he₁ : ∀ᶠ z in 𝓝[≠] lam,
      (z - lam) ^ m • resolvent R₁ z = compressBlock P (g z) := by
    filter_upwards [hevent.filter_mono nhdsWithin_le_nhds, he, self_mem_nhdsWithin]
      with z hz₂ hez hz
    have hz₁ := unit_of_singleton_spectrum hspec₁ hz
    have hzT : IsUnit (algebraMap ℂ (X →L[ℂ] X) z - T) := by
      by_contra hn
      rcases spectrum_subset_union hc R₁ R₂ h₁ h₂ hn with h | h
      · exact h hz₁
      · exact h hz₂
    calc
      _ = compressBlock P ((z - lam) ^ m • resolvent T z) := by
        rw [map_smul, compress_resolvent T P hP hc R₁ h₁ z hzT hz₁]
      _ = _ := congrArg (compressBlock P) hez
  have hA : IsUnitalBanachAlgebra (P.range →L[ℂ] P.range) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  exact shifted_pow_eq_zero_of_extension hA R₁ lam hspec₁ m
    (fun z => compressBlock P (g z)) hg₁ he₁

/-- Exact order is recovered from the least nilpotent exponent, so no
nonvanishing Laurent coefficient is silently assumed. -/
theorem pole_iff_nilpotent : Spec.PoleNilpotence.{u} := by
  intro X _ _ _ T P lam K hsplit hlam S hS m
  constructor
  · intro hpole
    have hpow := block_pow_eq_zero_of_pole T P lam K hsplit hlam S hS m hpole
    have hspec : spectrum ℂ S = {lam} := by
      obtain ⟨_, _, _, _, R₁, _, h₁, _, hspec₁, _⟩ := hsplit
      rw [restrictions_unique hS h₁]
      exact hspec₁
    haveI : Nontrivial P.range := not_subsingleton_iff_nontrivial.mp (by
      intro hM
      letI := hM
      have hh := spectrum.of_subsingleton S (R := ℂ)
      rw [hspec] at hh
      exact singleton_ne_empty lam hh)
    let N := S - algebraMap ℂ (P.range →L[ℂ] P.range) lam
    have hn : IsNilpotent N := ⟨m, hpow⟩
    have hnil : Spec.NilpotentOfOrder N (nilpotencyClass N) :=
      ⟨pos_nilpotencyClass_iff.mpr hn, pow_nilpotencyClass hn, pow_pred_nilpotencyClass hn⟩
    have hp := pole_of_nilpotent_block T P lam K hsplit hlam S hS (nilpotencyClass N) hnil
    have hm : m = nilpotencyClass N := by
      have he : ((-(m : ℤ) : ℤ) : WithTop ℤ) = ((-(nilpotencyClass N : ℤ) : ℤ) : WithTop ℤ) :=
        hpole.2.symm.trans hp.2
      have he' : -(m : ℤ) = -(nilpotencyClass N : ℤ) := WithTop.coe_injective he
      omega
    rw [hm]
    exact hnil
  · exact pole_of_nilpotent_block T P lam K hsplit hlam S hS m

end PoleBlock

/-- The pole criterion applied to the actual Riesz cutoff at any isolated
spectral point, together with the closed spectral splitting and complementary
invertibility. -/
theorem isolated_riesz_poles : Spec.IsolatedPoleSplitting.{u} := by
  intro X _ _ _ T lam hlam U₁ U₂ f ho₁ ho₂ hdU hlamU hKU₂ hf₁ hf₂
  have hK := (isolated_splitting X T lam hlam).1
  have hd : Disjoint ({lam} : Set ℂ) (spectrum ℂ T \ {lam}) := disjoint_sdiff_self_right
  have hspec : AlgebraSpectrumValue ℂ (X →L[ℂ] X) T = {lam} ∪ (spectrum ℂ T \ {lam}) :=
    (union_sdiff_cancel (singleton_subset_iff.mpr hlam.1)).symm
  have hs := riesz_splitting X T {lam} (spectrum ℂ T \ {lam}) isCompact_singleton hK hd hspec
    U₁ U₂ f ho₁ ho₂ hdU (singleton_subset_iff.mpr hlamU) hKU₂ hf₁ hf₂
  refine ⟨hs, ?_⟩
  have hsave := hs
  obtain ⟨_, _, _, _, S₁, S₂, h₁, h₂, _⟩ := hs
  have hn : lam ∉ spectrum ℂ T \ {lam} := fun h => h.2 (mem_singleton lam)
  exact ⟨S₁, S₂, h₁, h₂, complement_invertible X T _ lam _ hsave hn S₂ h₂,
    pole_iff_nilpotent X T _ lam _ hsave hn S₁ h₁⟩

end ExpandedFA.BanachAlgebra.RieszPoles
