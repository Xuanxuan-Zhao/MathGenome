import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.EventuallyCompactSpectralMapping
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.PointSpectralMapping
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.SpectralInclusion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.RieszSchauder
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! Spectral mapping for eventually compact C₀ semigroups.
The bounded-operator argument uses a stabilized compact-defect splitting.
It does not require a compact resolvent of the generator. -/
noncomputable section
open scoped NNReal

namespace ExpandedFA.Semigroups.EventuallyCompactSpectralMapping
open EventuallyCompactSpectralMappingSpec
open Fredholm.CompactDefectStabilizationSpec

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- An injective operator commuting with a finite-dimensional kernel of a
power is onto that kernel. The complementary power range is already in
its range whenever the original operator factors through it. -/
lemma surjective_of_compact_defect (L : X →L[ℂ] X) (n : ℕ) (hn : 0 < n)
    (hcompact : Compactness.IsCompactLinearMap (L ^ n).toLinearMap)
    (hinj : Function.Injective ((1 : X →L[ℂ] X) - L)) : Function.Surjective ((1 : X →L[ℂ] X) - L) := by
  let K := L ^ n
  let f : Module.End ℂ X := (1 - K).toLinearMap
  let g : Module.End ℂ X := (1 - L).toLinearMap
  obtain ⟨p, hp, hsplit⟩ := Fredholm.riesz_decomposition K hcompact
  have hd := (hsplit p le_rfl).2.2
  let N := kernelChain K p
  haveI : FiniteDimensional ℂ N := hd.2.2.1
  have hcomm : Commute f g := by
    have hc : Commute (1 - L ^ n) (1 - L) :=
      (Commute.one_right (1 - L ^ n)).sub_right
        ((Commute.one_left L).sub_left ((Commute.refl L).pow_left n))
    exact hc.map (ContinuousLinearMap.toLinearMapRingHom :
      (X →L[ℂ] X) →+* Module.End ℂ X)
  have hN (x : X) (hx : x ∈ N) : g x ∈ N := by
    change (f ^ p) (g x) = 0
    have he := congrArg (fun e : Module.End ℂ X => e x) (hcomm.pow_left p).eq
    change (f ^ p) (g x) = g ((f ^ p) x) at he
    rw [he]
    change (f ^ p) x = 0 at hx
    rw [hx, map_zero]
  let gN : N →ₗ[ℂ] N := g.restrict hN
  have hinjN : Function.Injective gN := by
    intro x y hxy
    apply Subtype.ext
    exact hinj (congrArg Subtype.val hxy)
  have hsurjN : Function.Surjective gN :=
    (LinearMap.injective_iff_surjective).mp hinjN
  have hfactor : (1 - L) * (∑ i ∈ Finset.range n, L ^ i) = 1 - K :=
    mul_neg_geom_sum L n
  intro x
  obtain ⟨P, Q, hPQ⟩ := hd.2.2.2.2.1
  obtain ⟨v, hv⟩ := hsurjN (P x)
  have hr : (Q x : X) ∈ LinearMap.range f := by
    exact f.iterateRange.monotone hp (Q x).property
  obtain ⟨w, hw⟩ := hr
  refine ⟨(v : X) + (∑ i ∈ Finset.range n, L ^ i) w, ?_⟩
  rw [map_add]
  have hv' : (1 - L) (v : X) = (P x : X) := congrArg Subtype.val hv
  have hw' : (1 - L) ((∑ i ∈ Finset.range n, L ^ i) w) = (Q x : X) := by
    rw [← mul_apply_eq_comp, hfactor]
    exact hw
  rw [hv', hw']
  exact (hPQ x).1

/-- Nonzero spectral values of a power-compact bounded operator are eigenvalues.
The proof only needs the compact-defect decomposition and the open mapping
bridge between algebraic and bounded inverses on a Banach space. -/
theorem power_compact_spectrum_iff_eigenvalue : PowerCompactSpectrumEigenvalue := by
  intro X _ _ _ B n hn hB μ hμ
  constructor
  · intro hμspec
    by_contra! hne
    let L : X →L[ℂ] X := μ⁻¹ • B
    have hcompact : Compactness.IsCompactLinearMap (L ^ n).toLinearMap := by
      rw [show L ^ n = μ⁻¹ ^ n • B ^ n from smul_pow _ _ _]
      exact Fredholm.compact_smul (B ^ n) hB (μ⁻¹ ^ n)
    have hinj : Function.Injective ((1 : X →L[ℂ] X) - L) := by
      apply LinearMap.ker_eq_bot.mp
      apply bot_unique
      intro x hx
      have hx' : x - μ⁻¹ • B x = 0 := hx
      have hBx : B x = μ • x := by
        have h := congrArg (fun y : X => μ • y) (sub_eq_zero.mp hx')
        simpa only [smul_inv_smul₀ hμ] using h.symm
      by_contra hx0
      exact hne x hx0 hBx
    have hsurj := surjective_of_compact_defect L n hn hcompact hinj
    have hbij : Function.Bijective (algebraMap ℂ (X →L[ℂ] X) μ - B) := by
      have hscale : algebraMap ℂ (X →L[ℂ] X) μ - B = μ • (1 - L) := by
        simp only [L, smul_sub, smul_smul, mul_inv_cancel₀ hμ, one_smul,
          Algebra.algebraMap_eq_smul_one]
      rw [hscale]
      constructor
      · intro x y h
        apply hinj
        have hh := congrArg (fun z : X => μ⁻¹ • z) h
        simpa only [smul_apply, inv_smul_smul₀ hμ] using hh
      · intro y
        obtain ⟨x, hx⟩ := hsurj (μ⁻¹ • y)
        refine ⟨x, ?_⟩
        change μ • ((1 - L) x) = y
        rw [hx, smul_inv_smul₀ hμ]
    exact (spectrum.mem_iff.mp hμspec) (ContinuousLinearMap.isUnit_iff_bijective.mpr hbij)
  · rintro ⟨x, hx, hBx⟩
    rw [spectrum.mem_iff, ContinuousLinearMap.isUnit_iff_bijective]
    intro hbij
    apply hx
    apply hbij.1
    change μ • x - B x = μ • (0 : X) - B 0
    simp [hBx]

/-- Compactness persists at all later times by composition with a bounded
semigroup operator. -/
theorem compact_at_later_time (T : C0Semigroup ℂ X) (t₀ : ℝ≥0)
    (hcompact : Compactness.IsCompactLinearMap (T.operators t₀).toLinearMap)
    (t : ℝ≥0) (ht : t₀ ≤ t) :
    Compactness.IsCompactLinearMap (T.operators t).toLinearMap := by
  have hc := (Compactness.compact_iff_isCompactOperator _).mp hcompact
  apply (Compactness.compact_iff_isCompactOperator _).mpr
  have he : (T.operators t : X → X) = T.operators t₀ ∘ T.operators (t - t₀) := by
    funext x
    rw [Function.comp_apply, ← T.add_apply, add_tsub_cancel_of_le ht]
  rw [show ((T.operators t).toLinearMap : X → X) = T.operators t by rfl, he]
  exact hc.comp_clm (T.operators (t - t₀))

/-- Each positive-time operator has a compact positive power. -/
theorem exists_compact_power (T : C0Semigroup ℂ X) (hT : EventuallyCompact T)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ n : ℕ, 0 < n ∧ Compactness.IsCompactLinearMap ((T.operators t) ^ n).toLinearMap := by
  obtain ⟨t₀, ht₀, hc⟩ := hT
  obtain ⟨n, hn⟩ := exists_nat_gt ((t₀ : ℝ) / (t : ℝ))
  have htime : t₀ ≤ n • t := by
    change (t₀ : ℝ) ≤ ↑(n • t)
    simpa only [NNReal.coe_nsmul, NNReal.coe_mul, NNReal.coe_natCast, nsmul_eq_mul] using
      (div_lt_iff₀ (show (0 : ℝ) < t from ht)).mp hn |>.le
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := (div_nonneg t₀.coe_nonneg t.coe_nonneg).trans_lt hn
    exact_mod_cast this
  have hp (m : ℕ) : T.operators (m • t) = (T.operators t) ^ m := by
    induction m with
    | zero => change T.operators 0 = 1; rw [T.at_zero]; rfl
    | succ m hm => rw [succ_nsmul, T.add_time, hm, pow_succ]; rfl
  exact ⟨n, hn0, hp n ▸ compact_at_later_time T t₀ hc (n • t) htime⟩

/-- Eventual compactness upgrades general point spectral mapping to full
spectral mapping at every positive time. -/
theorem full_spectral_mapping : FullSpectralMapping := by
  intro X _ _ _ T hT t ht
  ext μ
  constructor
  · rintro ⟨hμ, hμ0⟩
    have hμne : μ ≠ 0 := by simpa using hμ0
    obtain ⟨n, hn, hc⟩ := exists_compact_power T hT t ht
    obtain ⟨x, hx, hBx⟩ := (power_compact_spectrum_iff_eigenvalue
      (T.operators t) n hn hc μ hμne).mp hμ
    obtain ⟨ζ, hζ, y, hy, hAy⟩ :=
      PointSpectralMapping.time_eigenvalue_lifts T t ht μ hμne x hx hBx
    refine ⟨ζ, ?_, hζ⟩
    intro hR
    obtain ⟨R⟩ := hR
    have hh := R.left_inverse y
    change C0SemigroupSpec.generatorValue T y = ζ • (y : X) at hAy
    rw [hAy, sub_self, map_zero] at hh
    exact hy hh.symm
  · intro hμ
    have hi := SpectralInclusion.spectral_inclusion T t ht
    apply hi
    simpa only [Complex.real_smul] using hμ

/-- Restriction to a complete invariant subspace, with its inherited norm. -/
def restrictSemigroup (T : C0Semigroup ℂ X) (V : Submodule ℂ X) [CompleteSpace V]
    (hV : ∀ t : ℝ≥0, ∀ x ∈ V, T.operators t x ∈ V) : C0Semigroup ℂ V where
  operators t := (T.operators t).restrict (hV t)
  at_zero := by ext x; exact T.zero_apply x
  add_time t s := by ext x; exact T.add_apply t s x
  strong_zero x := tendsto_subtype_rng.mpr (T.strong_zero x)

@[simp] lemma restrictSemigroup_apply (T : C0Semigroup ℂ X) (V : Submodule ℂ X)
    [CompleteSpace V] (hV : ∀ t : ℝ≥0, ∀ x ∈ V, T.operators t x ∈ V)
    (t : ℝ≥0) (x : V) :
    ((restrictSemigroup T V hV).operators t x : X) = T.operators t x := rfl

/-- Exact-domain generator limits pass along any bounded intertwining map. -/
lemma hasGeneratorLimit_intertwine {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] [CompleteSpace Y] (S : C0Semigroup ℂ X)
    (T : C0Semigroup ℂ Y) (J : X →L[ℂ] Y)
    (hJ : ∀ t x, J (S.operators t x) = T.operators t (J x))
    {x y : X} (h : HasGeneratorLimit S x y) :
    HasGeneratorLimit T (J x) (J y) := by
  have hh := J.continuous.tendsto y |>.comp h
  change Filter.Tendsto (fun r => differenceQuotient T r (J x)) _ _
  apply hh.congr'
  filter_upwards [] with r
  simp only [Function.comp_apply, differenceQuotient, C0SemigroupSpec.differenceQuotientValue,
    smul_apply, sub_apply, ContinuousLinearMap.id_apply,
    map_smul, map_sub, hJ]

/-- A finite-dimensional C₀ semigroup has its entire space as generator
domain. Density suffices; there is no norm-continuity assumption. -/
lemma finite_dimensional_generator_domain (T : C0Semigroup ℂ X)
    [FiniteDimensional ℂ X] : (generator T).domain = ⊤ := by
  have hc := (generator T).domain.closed_of_finiteDimensional
  apply SetLike.coe_injective
  simpa [hc.closure_eq] using T.generator_domain_dense.closure_eq

/-- Every vector of a finite-dimensional invariant subspace belongs to the
original exact generator domain. -/
lemma finite_invariant_subspace_mem_domain (T : C0Semigroup ℂ X)
    (V : Submodule ℂ X) [FiniteDimensional ℂ V]
    (hV : ∀ t : ℝ≥0, ∀ x ∈ V, T.operators t x ∈ V) (x : V) :
    (x : X) ∈ (generator T).domain := by
  let S := restrictSemigroup T V hV
  have hx : x ∈ (generator S).domain := by rw [finite_dimensional_generator_domain S]; trivial
  exact ⟨_, hasGeneratorLimit_intertwine S T V.subtypeL (fun _ _ => rfl)
    (generator_has_limit S ⟨x, hx⟩)⟩

/-- The bounded matrix generator of a finite-dimensional semigroup, obtained
from its exact domain, which has already been proved to be the whole space. -/
def finiteGenerator (T : C0Semigroup ℂ X) [FiniteDimensional ℂ X] : X →L[ℂ] X :=
  let D : X →ₗ[ℂ] (generator T).domain :=
    { toFun := fun x => ⟨x, by rw [finite_dimensional_generator_domain T]; trivial⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  ((generator T).toFun.comp D).toContinuousLinearMap

lemma finiteGenerator_has_limit (T : C0Semigroup ℂ X) [FiniteDimensional ℂ X]
    (x : X) : HasGeneratorLimit T x (finiteGenerator T x) :=
  generator_has_limit T _

lemma finiteGenerator_agrees (T : C0Semigroup ℂ X) [FiniteDimensional ℂ X]
    (x : (generator T).domain) : finiteGenerator T x = generator T x := rfl

/-- On a finite-dimensional space the unbounded-domain convention gives
exactly the usual spectrum of the bounded matrix generator. -/
lemma finite_generator_spectrum (T : C0Semigroup ℂ X) [FiniteDimensional ℂ X] :
    C0SemigroupSpec.spectrumValue (generator T) = _root_.spectrum ℂ (finiteGenerator T) := by
  ext ζ
  rw [spectrum.mem_iff, ContinuousLinearMap.isUnit_iff_bijective]
  constructor
  · intro h hbij
    let C : X →L[ℂ] X := algebraMap ℂ (X →L[ℂ] X) ζ - finiteGenerator T
    let e : X ≃L[ℂ] X := ContinuousLinearEquiv.ofBijective C
      (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
    apply h
    refine ⟨⟨e.symm.toContinuousLinearMap, fun y => ?_, fun y => ?_, fun x => ?_⟩⟩
    · rw [finite_dimensional_generator_domain T]; trivial
    · change C (e.symm y) = y
      exact e.apply_symm_apply y
    · change e.symm (C x) = (x : X)
      exact e.symm_apply_apply x
  · intro h hR
    obtain ⟨R⟩ := hR
    apply h
    constructor
    · intro x y hxy
      have hi (z : X) : R.inverse ((algebraMap ℂ (X →L[ℂ] X) ζ - finiteGenerator T) z) = z :=
        R.left_inverse ⟨z, by rw [finite_dimensional_generator_domain T]; trivial⟩
      exact (hi x).symm.trans ((congrArg R.inverse hxy).trans (hi y))
    · intro y
      exact ⟨R.inverse y, R.right_inverse y⟩

/-- Bounded coordinates for complementary invariant subspaces intertwine
the restricted semigroups, by uniqueness of the two coordinates. -/
lemma coordinates_intertwine (T : C0Semigroup ℂ X) (V W : Submodule ℂ X)
    [CompleteSpace V] [CompleteSpace W]
    (hV : ∀ t : ℝ≥0, ∀ x ∈ V, T.operators t x ∈ V)
    (hW : ∀ t : ℝ≥0, ∀ x ∈ W, T.operators t x ∈ W)
    (P : X →L[ℂ] V) (Q : X →L[ℂ] W)
    (hPQ : ∀ x, (P x : X) + Q x = x ∧
      ∀ v : V, ∀ w : W, (v : X) + w = x → v = P x ∧ w = Q x) :
    (∀ t x, P (T.operators t x) = (restrictSemigroup T V hV).operators t (P x)) ∧
    (∀ t x, Q (T.operators t x) = (restrictSemigroup T W hW).operators t (Q x)) := by
  have h (t : ℝ≥0) (x : X) := (hPQ (T.operators t x)).2
    ((restrictSemigroup T V hV).operators t (P x))
    ((restrictSemigroup T W hW).operators t (Q x)) (by
      change T.operators t (P x) + T.operators t (Q x) = T.operators t x
      rw [← map_add, (hPQ x).1])
  exact ⟨fun t x => (h t x).1.symm, fun t x => (h t x).2.symm⟩

/-- Resolvents of the exact-domain restricted generators assemble to a
bounded resolvent on the original space. -/
def resolventOfDecomposition (T : C0Semigroup ℂ X) (V W : Submodule ℂ X)
    [CompleteSpace V] [CompleteSpace W]
    (hV : ∀ t : ℝ≥0, ∀ x ∈ V, T.operators t x ∈ V)
    (hW : ∀ t : ℝ≥0, ∀ x ∈ W, T.operators t x ∈ W)
    (P : X →L[ℂ] V) (Q : X →L[ℂ] W)
    (hPQ : ∀ x, (P x : X) + Q x = x ∧
      ∀ v : V, ∀ w : W, (v : X) + w = x → v = P x ∧ w = Q x)
    (ζ : ℂ)
    (RV : Unbounded.ResolventInverse (generator (restrictSemigroup T V hV)) ζ)
    (RW : Unbounded.ResolventInverse (generator (restrictSemigroup T W hW)) ζ) :
    Unbounded.ResolventInverse (generator T) ζ := by
  let S := restrictSemigroup T V hV
  let U := restrictSemigroup T W hW
  let B : X →L[ℂ] X := V.subtypeL.comp (RV.inverse.comp P) +
    W.subtypeL.comp (RW.inverse.comp Q)
  have hlim (y : X) : HasGeneratorLimit T (B y) (ζ • B y - y) := by
    have hRV : HasGeneratorLimit S (RV.inverse (P y)) (ζ • RV.inverse (P y) - P y) := by
      have he := RV.right_inverse (P y)
      have hh := generator_has_limit S ⟨RV.inverse (P y), RV.mem_domain (P y)⟩
      have he' : generator S ⟨RV.inverse (P y), RV.mem_domain (P y)⟩ =
          ζ • RV.inverse (P y) - P y := by
        apply eq_sub_iff_add_eq.mpr
        simpa only [add_comm] using (sub_eq_iff_eq_add.mp he).symm
      change C0SemigroupSpec.generatorValue _ _ = _ at he'
      exact he' ▸ hh
    have hRW : HasGeneratorLimit U (RW.inverse (Q y)) (ζ • RW.inverse (Q y) - Q y) := by
      have he := RW.right_inverse (Q y)
      have hh := generator_has_limit U ⟨RW.inverse (Q y), RW.mem_domain (Q y)⟩
      have he' : generator U ⟨RW.inverse (Q y), RW.mem_domain (Q y)⟩ =
          ζ • RW.inverse (Q y) - Q y := by
        apply eq_sub_iff_add_eq.mpr
        simpa only [add_comm] using (sub_eq_iff_eq_add.mp he).symm
      change C0SemigroupSpec.generatorValue _ _ = _ at he'
      exact he' ▸ hh
    have hVlim := hasGeneratorLimit_intertwine S T V.subtypeL (fun _ _ => rfl) hRV
    have hWlim := hasGeneratorLimit_intertwine U T W.subtypeL (fun _ _ => rfl) hRW
    have hh : HasGeneratorLimit T (B y)
        ((ζ • (RV.inverse (P y) : X) - (P y : X)) +
          (ζ • (RW.inverse (Q y) : X) - (Q y : X))) := by
      simpa only [HasGeneratorLimit, C0SemigroupSpec.hasGeneratorLimitValue, B,
        add_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
        map_add, map_sub, map_smul] using hVlim.add hWlim
    convert hh using 1
    simp only [B, add_apply, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply]
    conv_lhs => rhs; rw [← (hPQ y).1]
    rw [smul_add]
    abel
  refine ⟨B, fun y => ⟨_, hlim y⟩, ?_, ?_⟩
  · intro y
    have he := generator_limit_unique T _ _ _ (generator_has_limit T ⟨B y, ⟨_, hlim y⟩⟩) (hlim y)
    change C0SemigroupSpec.generatorValue T _ = _ at he
    change ζ • B y - C0SemigroupSpec.generatorValue T _ = y
    exact (congrArg (fun z : X => ζ • B y - z) he).trans (sub_sub_cancel _ _)
  · intro x
    obtain ⟨hP, hQ⟩ := coordinates_intertwine T V W hV hW P Q hPQ
    have hPx := hasGeneratorLimit_intertwine T S P hP (generator_has_limit T x)
    have hQx := hasGeneratorLimit_intertwine T U Q hQ (generator_has_limit T x)
    let px : (generator S).domain := ⟨P x, ⟨_, hPx⟩⟩
    let qx : (generator U).domain := ⟨Q x, ⟨_, hQx⟩⟩
    have hAP : generator S px = P (generator T x) :=
      generator_limit_unique S _ _ _ (generator_has_limit S px) hPx
    have hAQ : generator U qx = Q (generator T x) :=
      generator_limit_unique U _ _ _ (generator_has_limit U qx) hQx
    have hleftP := RV.left_inverse px
    have hleftQ := RW.left_inverse qx
    rw [hAP] at hleftP
    rw [hAQ] at hleftQ
    change (RV.inverse (P (ζ • (x : X) - generator T x)) : X) +
      (RW.inverse (Q (ζ • (x : X) - generator T x)) : X) = (x : X)
    simp only [P.map_sub, P.map_smul, Q.map_sub, Q.map_smul]
    rw [hleftP, hleftQ]
    exact (hPQ x).1

/-- Commuting maps preserve both the kernel and range of every power. -/
lemma invariant_power_kernel_range (f g : Module.End ℂ X) (hc : Commute f g) (p : ℕ) :
    (∀ x ∈ LinearMap.ker (f ^ p), g x ∈ LinearMap.ker (f ^ p)) ∧
    (∀ x ∈ LinearMap.range (f ^ p), g x ∈ LinearMap.range (f ^ p)) := by
  have hcomm (x : X) : (f ^ p) (g x) = g ((f ^ p) x) :=
    congrArg (fun e : Module.End ℂ X => e x) (hc.pow_left p).eq
  constructor
  · intro x hx
    change (f ^ p) (g x) = 0
    rw [hcomm, LinearMap.mem_ker.mp hx, map_zero]
  · rintro x ⟨v, rfl⟩
    exact ⟨g v, hcomm v⟩

/-- The stabilized compact-defect subspaces for a nonzero time eigenvalue
are invariant under every operator in the semigroup. -/
lemma compact_time_decomposition (T : C0Semigroup ℂ X) (t₀ : ℝ≥0)
    (hc : Compactness.IsCompactLinearMap (T.operators t₀).toLinearMap)
    (μ : ℂ) (hμ : μ ≠ 0) :
    ∃ p : ℕ, 1 ≤ p ∧ Decomposition (μ⁻¹ • T.operators t₀) p ∧
      (∀ t : ℝ≥0, ∀ x ∈ kernelChain (μ⁻¹ • T.operators t₀) p, T.operators t x ∈
        kernelChain (μ⁻¹ • T.operators t₀) p) ∧
      (∀ t : ℝ≥0, ∀ x ∈ rangeChain (μ⁻¹ • T.operators t₀) p, T.operators t x ∈
        rangeChain (μ⁻¹ • T.operators t₀) p) := by
  let K := μ⁻¹ • T.operators t₀
  obtain ⟨p, hp, hd⟩ := Fredholm.riesz_decomposition K
    (Fredholm.compact_smul (T.operators t₀) hc μ⁻¹)
  have hcomm (t : ℝ≥0) : Commute (ContinuousLinearMap.id ℂ X - K).toLinearMap
      (T.operators t).toLinearMap := by
    ext x
    change T.operators t x - μ⁻¹ • T.operators t₀ (T.operators t x) =
      T.operators t (x - μ⁻¹ • T.operators t₀ x)
    rw [map_sub, map_smul, T.operators_commute]
  refine ⟨p, hp, (hd p le_rfl).2.2, ?_, ?_⟩
  · intro t
    exact (invariant_power_kernel_range _ _ (hcomm t) p).1
  · intro t
    exact (invariant_power_kernel_range _ _ (hcomm t) p).2

/-- Spectrum of an exact-domain generator is contained in the union of the
generator spectra of its two invariant complemented summands. -/
lemma generator_spectrum_subset_union (T : C0Semigroup ℂ X) (V W : Submodule ℂ X)
    [CompleteSpace V] [CompleteSpace W]
    (hV : ∀ t : ℝ≥0, ∀ x ∈ V, T.operators t x ∈ V)
    (hW : ∀ t : ℝ≥0, ∀ x ∈ W, T.operators t x ∈ W)
    (P : X →L[ℂ] V) (Q : X →L[ℂ] W)
    (hPQ : ∀ x, (P x : X) + Q x = x ∧
      ∀ v : V, ∀ w : W, (v : X) + w = x → v = P x ∧ w = Q x) :
    C0SemigroupSpec.spectrumValue (generator T) ⊆
      C0SemigroupSpec.spectrumValue (generator (restrictSemigroup T V hV)) ∪
      C0SemigroupSpec.spectrumValue (generator (restrictSemigroup T W hW)) := by
  intro ζ hζ
  by_contra h
  have hVspec : ζ ∉ C0SemigroupSpec.spectrumValue (generator (restrictSemigroup T V hV)) :=
    fun h' => h (Or.inl h')
  have hWspec : ζ ∉ C0SemigroupSpec.spectrumValue (generator (restrictSemigroup T W hW)) :=
    fun h' => h (Or.inr h')
  have hRV : Nonempty (Unbounded.ResolventInverse (generator (restrictSemigroup T V hV)) ζ) :=
    not_not.mp hVspec
  have hRW : Nonempty (Unbounded.ResolventInverse (generator (restrictSemigroup T W hW)) ζ) :=
    not_not.mp hWspec
  exact hζ ⟨resolventOfDecomposition T V W hV hW P Q hPQ ζ hRV.some hRW.some⟩

/-- A complementary resolvent annihilates all generalized eigenvectors in
that summand. This controls every power kernel, with all intermediate
unbounded domains retained. -/
lemma generalized_eigenspace_le_of_complement_resolvent
    (T : C0Semigroup ℂ X) (V W : Submodule ℂ X)
    [CompleteSpace V] [CompleteSpace W]
    (hV : ∀ t : ℝ≥0, ∀ x ∈ V, T.operators t x ∈ V)
    (hW : ∀ t : ℝ≥0, ∀ x ∈ W, T.operators t x ∈ W)
    (P : X →L[ℂ] V) (Q : X →L[ℂ] W)
    (hPQ : ∀ x, (P x : X) + Q x = x ∧
      ∀ v : V, ∀ w : W, (v : X) + w = x → v = P x ∧ w = Q x)
    (ζ : ℂ) (RW : Unbounded.ResolventInverse (generator (restrictSemigroup T W hW)) ζ) :
    generatorGeneralizedEigenspace (generator T) ζ ≤ V := by
  let U := restrictSemigroup T W hW
  have hQ := (coordinates_intertwine T V W hV hW P Q hPQ).2
  have hQzero (v : V) : Q (v : X) = 0 :=
    ((hPQ v).2 v 0 (by simp)).2.symm
  apply iSup_le
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    rintro x ⟨u, hu, rfl⟩
    have hshift : Q (ζ • (u : X) - generator T u) = 0 :=
      hQzero ⟨_, ih hu⟩
    have hQlim := hasGeneratorLimit_intertwine T U Q hQ (generator_has_limit T u)
    let qu : (generator U).domain := ⟨Q u, ⟨_, hQlim⟩⟩
    have hAQ : generator U qu = Q (generator T u) :=
      generator_limit_unique U _ _ _ (generator_has_limit U qu) hQlim
    have he := RW.left_inverse qu
    rw [hAQ] at he
    change RW.inverse (ζ • Q (u : X) - Q (generator T u)) = Q (u : X) at he
    rw [← Q.map_smul, ← Q.map_sub, hshift, map_zero] at he
    have hx : (P (u : X) : X) = (u : X) := by
      simpa only [← he, Submodule.coe_zero, add_zero] using (hPQ (u : X)).1
    change (u : X) ∈ V
    rw [← hx]
    exact (P (u : X)).property

/-- The complement of the compact Riesz space has no generator spectrum
in the logarithmic fiber of the removed nonzero time eigenvalue. -/
lemma complementary_generator_resolvent (T : C0Semigroup ℂ X)
    (t₀ : ℝ≥0) (ht₀ : 0 < t₀) (μ : ℂ) (hμ : μ ≠ 0) (p : ℕ)
    (hd : Decomposition (μ⁻¹ • T.operators t₀) p)
    (hW : ∀ t : ℝ≥0, ∀ x ∈ rangeChain (μ⁻¹ • T.operators t₀) p,
      T.operators t x ∈ rangeChain (μ⁻¹ • T.operators t₀) p)
    [CompleteSpace (rangeChain (μ⁻¹ • T.operators t₀) p)]
    (ζ : ℂ) (hζ : Complex.exp ((t₀ : ℂ) * ζ) = μ) :
    Nonempty (Unbounded.ResolventInverse
      (generator (restrictSemigroup T (rangeChain (μ⁻¹ • T.operators t₀) p) hW)) ζ) := by
  let W := rangeChain (μ⁻¹ • T.operators t₀) p
  let U := restrictSemigroup T W hW
  obtain ⟨e, he⟩ := hd.2.2.2.2.2.2.2.2
  have hfactor : algebraMap ℂ (W →L[ℂ] W) μ - U.operators t₀ = μ • e.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change μ • (x : X) - T.operators t₀ x = μ • (e x : X)
    rw [he]
    simp only [sub_apply, ContinuousLinearMap.id_apply,
      smul_apply, smul_sub, smul_inv_smul₀ hμ]
  have hunit : IsUnit (algebraMap ℂ (W →L[ℂ] W) μ - U.operators t₀) := by
    rw [hfactor, ContinuousLinearMap.isUnit_iff_bijective]
    exact hμ.isUnit.smul_bijective.comp e.bijective
  have hnot : ζ ∉ C0SemigroupSpec.spectrumValue (generator U) := by
    intro hz
    have hi := (SpectralInclusion.spectral_inclusion U t₀ ht₀) ⟨ζ, hz, rfl⟩
    have hexp : Complex.exp ((t₀ : ℝ) • ζ) = μ := by
      simpa only [Complex.real_smul] using hζ
    change Complex.exp ((t₀ : ℝ) • ζ) ∈ _root_.spectrum ℂ (U.operators t₀) \ {0} at hi
    rw [hexp] at hi
    exact (spectrum.mem_iff.mp hi.1) hunit
  exact not_not.mp hnot

/-- Each nonzero logarithmic fiber of a compact time operator is controlled
by one finite-dimensional invariant Riesz space and its actual matrix
generator. Its complement has a genuine bounded exact-domain resolvent. -/
lemma finite_spectral_fiber (T : C0Semigroup ℂ X) (t₀ : ℝ≥0) (ht₀ : 0 < t₀)
    (hc : Compactness.IsCompactLinearMap (T.operators t₀).toLinearMap)
    (μ : ℂ) (hμ : μ ≠ 0) :
    ∃ (V : Submodule ℂ X) (_ : FiniteDimensional ℂ V)
      (hV : ∀ t : ℝ≥0, ∀ x ∈ V, T.operators t x ∈ V),
      ∀ ζ : ℂ, Complex.exp ((t₀ : ℂ) * ζ) = μ →
        (ζ ∈ C0SemigroupSpec.spectrumValue (generator T) →
          ζ ∈ _root_.spectrum ℂ (finiteGenerator (restrictSemigroup T V hV))) ∧
        generatorGeneralizedEigenspace (generator T) ζ ≤ V := by
  obtain ⟨p, hp, hd, hV, hW⟩ := compact_time_decomposition T t₀ hc μ hμ
  let V := kernelChain (μ⁻¹ • T.operators t₀) p
  let W := rangeChain (μ⁻¹ • T.operators t₀) p
  haveI : FiniteDimensional ℂ V := hd.2.2.1
  haveI : IsClosed (W : Set X) := hd.2.2.2.1
  haveI : CompleteSpace W := IsClosed.completeSpace_coe
  obtain ⟨P, Q, hPQ⟩ := hd.2.2.2.2.1
  refine ⟨V, inferInstance, hV, fun ζ hζ => ?_⟩
  have hRW := complementary_generator_resolvent T t₀ ht₀ μ hμ p hd hW ζ hζ
  constructor
  · intro hspec
    have hunion := generator_spectrum_subset_union T V W hV hW P Q hPQ hspec
    have hS : ζ ∈ C0SemigroupSpec.spectrumValue (generator (restrictSemigroup T V hV)) :=
      hunion.resolve_right (fun h => h hRW)
    rwa [finite_generator_spectrum] at hS
  · exact generalized_eigenspace_le_of_complement_resolvent T V W hV hW P Q hPQ ζ hRW.some

/-- A compact-time logarithmic fiber contains only finitely many generator
spectral values. Each is an eigenvalue of finite algebraic multiplicity. -/
lemma generator_spectral_fiber_properties (T : C0Semigroup ℂ X) (t₀ : ℝ≥0)
    (ht₀ : 0 < t₀) (hc : Compactness.IsCompactLinearMap (T.operators t₀).toLinearMap)
    (μ : ℂ) (hμ : μ ≠ 0) :
    {ζ : ℂ | ζ ∈ C0SemigroupSpec.spectrumValue (generator T) ∧
      Complex.exp ((t₀ : ℂ) * ζ) = μ}.Finite ∧
    ∀ ζ ∈ C0SemigroupSpec.spectrumValue (generator T),
      Complex.exp ((t₀ : ℂ) * ζ) = μ →
        ζ ∈ PointSpectralMappingSpec.generatorPointSpectrum (generator T) ∧
        FiniteDimensional ℂ (generatorGeneralizedEigenspace (generator T) ζ) := by
  obtain ⟨V, hfd, hV, hdata⟩ := finite_spectral_fiber T t₀ ht₀ hc μ hμ
  letI : FiniteDimensional ℂ V := hfd
  let S := restrictSemigroup T V hV
  let G := finiteGenerator S
  have hfin : (_root_.spectrum ℂ G).Finite := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact Module.End.finite_spectrum G.toLinearMap
  refine ⟨hfin.subset (fun ζ hζ => (hdata ζ hζ.2).1 hζ.1), ?_⟩
  intro ζ hspec hζ
  have hζG : ζ ∈ _root_.spectrum ℂ G := (hdata ζ hζ).1 hspec
  have heigen : Module.End.HasEigenvalue G.toLinearMap ζ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr (by
      rwa [ContinuousLinearMap.spectrum_eq] at hζG)
  obtain ⟨y, hy⟩ := heigen.exists_hasEigenvector
  have hGy : G y = ζ • y := hy.apply_eq_smul
  have hlim := hasGeneratorLimit_intertwine S T V.subtypeL (fun _ _ => rfl)
    (finiteGenerator_has_limit S y)
  have hlim' : HasGeneratorLimit T (y : X) (ζ • (y : X)) := by
    have hval : (G y : X) = ζ • (y : X) := congrArg Subtype.val hGy
    exact hval ▸ hlim
  let dy : (generator T).domain := ⟨y, ⟨_, hlim'⟩⟩
  refine ⟨⟨dy, ?_, ?_⟩, Submodule.finiteDimensional_of_le (hdata ζ hζ).2⟩
  · intro hz
    apply hy.2
    exact Subtype.ext hz
  · exact generator_limit_unique T _ _ _ (generator_has_limit T dy) hlim'

/-- Compactness at one positive time bounds the number of generator spectral
values in every closed right half-plane. Finiteness of the time spectrum
away from zero is combined with finite matrix spectra in each fiber. -/
lemma generator_spectrum_finite_right_half_plane (T : C0Semigroup ℂ X)
    (hT : EventuallyCompact T) (a : ℝ) :
    {ζ : ℂ | ζ ∈ C0SemigroupSpec.spectrumValue (generator T) ∧ a ≤ ζ.re}.Finite := by
  obtain ⟨t₀, ht₀, hc⟩ := hT
  let f : ℂ → ℂ := fun ζ => Complex.exp ((t₀ : ℂ) * ζ)
  let S : Set ℂ := {ζ | ζ ∈ C0SemigroupSpec.spectrumValue (generator T) ∧ a ≤ ζ.re}
  have hcompactfinite := Fredholm.compact_spectrum_finite_away_from_zero
    (T.operators t₀) hc (Real.exp ((t₀ : ℝ) * a)) (Real.exp_pos _)
  have himage : (f '' S).Finite := hcompactfinite.subset (by
    rintro μ ⟨ζ, hζ, rfl⟩
    constructor
    · have hi := (SpectralInclusion.spectral_inclusion T t₀ ht₀) ⟨ζ, hζ.1, rfl⟩
      simpa only [f, Complex.real_smul] using hi.1
    · change Real.exp ((t₀ : ℝ) * a) ≤ ‖Complex.exp ((t₀ : ℂ) * ζ)‖
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hζ.2 t₀.coe_nonneg))
  apply Set.Finite.of_finite_fibers f himage
  rintro μ ⟨ζ, hζ, rfl⟩
  have hμ : f ζ ≠ 0 := Complex.exp_ne_zero _
  have hf := (generator_spectral_fiber_properties T t₀ ht₀ hc (f ζ) hμ).1
  apply hf.subset
  rintro η ⟨hη, hηf⟩
  exact ⟨hη.1, hηf⟩

/-- Local finiteness in right half-planes implies isolation of every
spectral point; no nonempty-spectrum convention is required. -/
lemma isolated_of_finite_right_half_planes (S : Set ℂ)
    (hS : ∀ a : ℝ, {ζ : ℂ | ζ ∈ S ∧ a ≤ ζ.re}.Finite) (ζ : ℂ) (hζ : ζ ∈ S) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ η ∈ S, dist η ζ < ε → η = ζ := by
  let F : Set ℂ := {η | η ∈ S ∧ ζ.re - 1 ≤ η.re} \ {ζ}
  have hF : F.Finite := (hS (ζ.re - 1)).sdiff
  have hζF : ζ ∈ Fᶜ := by simp [F]
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hF.isClosed.isOpen_compl ζ hζF
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro η hη hd
  have hdδ : dist η ζ < δ := hd.trans_le (min_le_left _ _)
  have hd1 : dist η ζ < 1 := hd.trans_le (min_le_right _ _)
  have hre : |η.re - ζ.re| ≤ dist η ζ := by
    simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (η - ζ)
  have hηright : ζ.re - 1 ≤ η.re := by
    have hlow := neg_abs_le (η.re - ζ.re)
    linarith
  have hηnot : η ∉ F := hball hdδ
  by_contra hne
  exact hηnot ⟨⟨hη, hηright⟩, by simpa using hne⟩

/-- A finite-dimensional Riesz summand and its invariant complement give
actual semigroup restrictions and an exact-domain complementary resolvent.
This also certifies the spectral meaning of finite algebraic multiplicity. -/
theorem finite_riesz_decompositions : FiniteRieszDecompositions := by
  intro X _ _ _ T hT ζ
  obtain ⟨t₀, ht₀, hc⟩ := hT
  let μ := Complex.exp ((t₀ : ℂ) * ζ)
  have hμ : μ ≠ 0 := Complex.exp_ne_zero _
  obtain ⟨p, hp, hd, hV, hW⟩ := compact_time_decomposition T t₀ hc μ hμ
  let V := kernelChain (μ⁻¹ • T.operators t₀) p
  let W := rangeChain (μ⁻¹ • T.operators t₀) p
  haveI : FiniteDimensional ℂ V := hd.2.2.1
  haveI : IsClosed (W : Set X) := hd.2.2.2.1
  haveI : CompleteSpace W := IsClosed.completeSpace_coe
  refine ⟨V, W, inferInstance, inferInstance, restrictSemigroup T V hV,
    restrictSemigroup T W hW, hd.1, inferInstance, fun _ _ => rfl, fun _ _ => rfl,
    finite_invariant_subspace_mem_domain T V hV, ?_⟩
  exact complementary_generator_resolvent T t₀ ht₀ μ hμ p hd hW ζ rfl

/-- The complete generator spectral structure for eventual compactness.
Isolation, finite algebraic multiplicity and right-half-plane finiteness
are derived, never included in the semigroup or generator hypotheses. -/
theorem generator_spectral_structure : GeneratorSpectralStructure := by
  intro X _ _ _ T hT
  obtain ⟨t₀, ht₀, hc⟩ := hT
  have hfinite := generator_spectrum_finite_right_half_plane T ⟨t₀, ht₀, hc⟩
  refine ⟨?_, hfinite⟩
  intro ζ hζ
  have hμ : Complex.exp ((t₀ : ℂ) * ζ) ≠ 0 := Complex.exp_ne_zero _
  obtain ⟨heig, hmult⟩ := (generator_spectral_fiber_properties T t₀ ht₀ hc _ hμ).2 ζ hζ rfl
  exact ⟨heig, isolated_of_finite_right_half_planes _ hfinite ζ hζ, hmult,
    finite_riesz_decompositions T ⟨t₀, ht₀, hc⟩ ζ⟩

end ExpandedFA.Semigroups.EventuallyCompactSpectralMapping
