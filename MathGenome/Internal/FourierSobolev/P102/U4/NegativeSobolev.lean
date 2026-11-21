import MathGenome.Internal.FourierSobolev.Specs.P102.U4.NegativeSobolev
import MathGenome.Internal.FourierSobolev.P102.U4.ZeroExtension
import MathGenome.Internal.FourierSobolev.P102.U4.NegativeLpRepresentation
import MathGenome.Internal.FourierSobolev.P102.U4.NegativeLpPairingNorm
import Mathlib.Analysis.Normed.Module.HahnBanach

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped Distributions ENNReal
namespace P102.U4

abbrev negativeSobolev : NegativeSobolevExpected.SpaceType := @NegativeSobolev

/-- The order-one multi-indices are exactly zero and the coordinate singletons. -/
def firstOrderIndexEquiv (d : ℕ) : Option (Fin d) ≃ SobolevIndex d 1 := by
  classical
  let f : Option (Fin d) → SobolevIndex d 1 := fun j =>
    j.elim (zeroSobolevIndex d 1) (negativeFirstSobolevIndex d)
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some j =>
        have := congrArg (fun α : SobolevIndex d 1 => α.val.card) h
        change (0 : ℕ) = 1 at this
        omega
    | some i =>
      cases b with
      | none =>
        have := congrArg (fun α : SobolevIndex d 1 => α.val.card) h
        change (1 : ℕ) = 0 at this
        omega
      | some j =>
        congr 1
        have := congrArg Subtype.val h
        simpa [f, negativeFirstSobolevIndex] using this
  · intro α
    by_cases h : α.val.card = 0
    · refine ⟨none, ?_⟩
      apply Subtype.ext
      exact (Multiset.card_eq_zero.mp h).symm
    · have hc : α.val.card = 1 := by have := α.property; omega
      obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp hc
      exact ⟨some j, Subtype.ext hj.symm⟩

@[simp] theorem firstOrderIndexEquiv_none (d : ℕ) :
    firstOrderIndexEquiv d none = zeroSobolevIndex d 1 := rfl

@[simp] theorem firstOrderIndexEquiv_some (d : ℕ) (j : Fin d) :
    firstOrderIndexEquiv d (some j) = negativeFirstSobolevIndex d j := rfl

/-- Unfolding the finite index set gives the source's signed formula. -/
theorem negative_pairing_formula : NegativeSobolevExpected.PairingFormula := by
  intro d 𝕜 _ Ω p _ a u
  rw [negativePairing, ← Equiv.sum_comp (firstOrderIndexEquiv d)]
  simp only [Fintype.sum_option, firstOrderIndexEquiv_none, firstOrderIndexEquiv_some,
    zeroSobolevIndex, negativeFirstSobolevIndex, Multiset.card_zero, pow_zero, one_mul,
    Multiset.card_singleton, pow_one, neg_one_mul, Finset.sum_neg_distrib,
    sub_eq_add_neg]
  rfl

theorem negative_divergence_formula : NegativeSobolevExpected.DivergenceFormula := by
  intro d 𝕜 _ Ω p a
  rw [divergenceDistribution, ← Equiv.sum_comp (firstOrderIndexEquiv d)]
  simp only [Fintype.sum_option, firstOrderIndexEquiv_none, firstOrderIndexEquiv_some]
  rw [show (zeroSobolevIndex d 1).val = 0 from rfl, derivative_zero]
  rfl

variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Norm-one scalar multiplication followed by integration gives Holder's bound. -/
theorem lp_bilinear_bound (a : DomainLp 𝕜 Ω (ENNReal.conjExponent p))
    (u : DomainLp 𝕜 Ω p) :
    ‖(ContinuousLinearMap.mul 𝕜 𝕜).lpPairing
      (volume.restrict (Ω : Set (Space d))) p (ENNReal.conjExponent p) u a‖ ≤ ‖a‖ * ‖u‖ := by
  rw [ContinuousLinearMap.lpPairing]
  change ‖L1.integralCLM' 𝕜 ((ContinuousLinearMap.mul 𝕜 𝕜).holder 1 u a)‖ ≤ _
  rw [← L1.integral_eq']
  calc
    _ ≤ ‖(ContinuousLinearMap.mul 𝕜 𝕜).holder 1 u a‖ := L1.norm_integral_le _
    _ ≤ ‖ContinuousLinearMap.mul 𝕜 𝕜‖ * ‖u‖ * ‖a‖ :=
      ContinuousLinearMap.norm_holder_apply_apply_le _ _ _
    _ ≤ 1 * ‖u‖ * ‖a‖ := by gcongr; exact ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜
    _ = _ := by ring

/-- The signed pairing as a continuous functional, before its sharp norm estimate. -/
def negativeOfCoefficients (a : NegativeCoefficients 𝕜 Ω p) : NegativeSobolev 𝕜 Ω p :=
  ∑ α : SobolevIndex d 1, ((-1 : 𝕜) ^ α.val.card) •
    (((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing
      (volume.restrict (Ω : Set (Space d))) p (ENNReal.conjExponent p)).flip (a α)).comp
      ((PiLp.proj 1 _ α).comp
        ((sobolevSubmodule 𝕜 Ω 1 p).subtypeL.comp (sobolevZeroSubmodule 𝕜 Ω 1 p).subtypeL))

theorem negativeOfCoefficients_pairing (a : NegativeCoefficients 𝕜 Ω p)
    (u : SobolevZero 𝕜 Ω 1 p) : negativeOfCoefficients Ω p a u = negativePairing a u := by
  simp only [negativeOfCoefficients, negativePairing, sum_apply,
    smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro α _
  congr 1
  rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => mul_comm _ _

theorem negativeOfCoefficients_norm (a : NegativeCoefficients 𝕜 Ω p) :
    ‖negativeOfCoefficients Ω p a‖ ≤ ‖a‖ := by
  refine @ContinuousLinearMap.opNorm_le_bound 𝕜 𝕜 (SobolevZero 𝕜 Ω 1 p) 𝕜
    _ _ _ _ _ _ (RingHom.id 𝕜) (negativeOfCoefficients Ω p a) ‖a‖ (norm_nonneg a) (fun u => ?_)
  simp only [negativeOfCoefficients, sum_apply, smul_apply, ContinuousLinearMap.comp_apply]
  change ‖∑ α : SobolevIndex d 1, (-1 : 𝕜) ^ α.val.card •
    (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing
      (volume.restrict (Ω : Set (Space d))) p (ENNReal.conjExponent p)
      (sobolevDerivative u.val α) (a α)‖ ≤ _
  calc
    _ ≤ ∑ α : SobolevIndex d 1, ‖(-1 : 𝕜) ^ α.val.card •
        (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing
        (volume.restrict (Ω : Set (Space d))) p (ENNReal.conjExponent p)
        (sobolevDerivative u.val α) (a α)‖ := norm_sum_le _ _
    _ = ∑ α : SobolevIndex d 1, ‖(ContinuousLinearMap.mul 𝕜 𝕜).lpPairing
        (volume.restrict (Ω : Set (Space d))) p (ENNReal.conjExponent p)
        (sobolevDerivative u.val α) (a α)‖ := by simp
    _ ≤ ∑ α : SobolevIndex d 1, ‖a‖ * ‖sobolevDerivative u.val α‖ := by
      apply Finset.sum_le_sum
      intro α _
      exact (lp_bilinear_bound Ω p (a α) _).trans
        (mul_le_mul_of_nonneg_right (norm_le_pi_norm a α) (norm_nonneg _))
    _ = ‖a‖ * ‖u‖ := by rw [← Finset.mul_sum, ← sobolev_norm]; rfl

theorem negative_converse : NegativeSobolevExpected.Converse := by
  intro d 𝕜 _ Ω p _ a
  exact ⟨negativeOfCoefficients Ω p a, negativeOfCoefficients_pairing Ω p a,
    negativeOfCoefficients_norm Ω p a⟩

/-- The exact norm-preserving extension needed by the representation proof.
Apply Hahn--Banach twice to the two literal closed subspaces, avoiding a
renorming or an additional hypothesis on the boundary. -/
theorem negative_normPreserving_extension (f : NegativeSobolev 𝕜 Ω p) :
    ∃ g : SobolevTuple 𝕜 Ω 1 p →L[𝕜] 𝕜,
      (∀ u : SobolevZero 𝕜 Ω 1 p, g u.val.val = f u) ∧ ‖g‖ = ‖f‖ := by
  obtain ⟨h, hh, hn⟩ := exists_extension_norm_eq (sobolevZeroSubmodule 𝕜 Ω 1 p) f
  obtain ⟨g, hg, gn⟩ := exists_extension_norm_eq (sobolevSubmodule 𝕜 Ω 1 p) h
  exact ⟨g, fun u => (hg u.val).trans (hh u), gn.trans hn⟩

theorem negative_empty : NegativeSobolevExpected.EmptyDomain := by
  intro d 𝕜 _ p _ f
  ext u
  have hu : u = 0 := Subtype.ext (sobolev_empty 1 p u.val)
  simp [hu]

/-- A test has its unique canonical Sobolev class in the closure defining W₀. -/
def testSobolevZero (φ : TestSpace 𝕜 Ω) : SobolevZero 𝕜 Ω 1 p := by
  let u := (zeroExtension_smoothInclusion Ω 1 p φ).choose
  have hu : sobolevUnderlying u = testToDomainLp Ω p φ :=
    (zeroExtension_smoothInclusion Ω 1 p φ).choose_spec
  exact ⟨u, (smoothSobolevSubmodule 𝕜 Ω 1 p).le_topologicalClosure ⟨φ, hu.symm⟩⟩

@[simp] theorem testSobolevZero_underlying (φ : TestSpace 𝕜 Ω) :
    sobolevUnderlying (testSobolevZero Ω p φ).val = testToDomainLp Ω p φ :=
  (zeroExtension_smoothInclusion Ω 1 p φ).choose_spec

theorem testSobolevZero_unique (φ : TestSpace 𝕜 Ω) (u : SobolevZero 𝕜 Ω 1 p)
    (hu : sobolevUnderlying u.val = testToDomainLp Ω p φ) : u = testSobolevZero Ω p φ := by
  apply Subtype.ext
  exact sobolevUnderlying_injective Ω 1 p (hu.trans (testSobolevZero_underlying Ω p φ).symm)

/-- Density can be used without imposing a boundary regularity condition on Ω. -/
theorem negative_ext_tests {f g : NegativeSobolev 𝕜 Ω p}
    (h : ∀ φ : TestSpace 𝕜 Ω, f (testSobolevZero Ω p φ) = g (testSobolevZero Ω p φ)) :
    f = g := by
  obtain ⟨F, hF, _⟩ := negative_normPreserving_extension Ω p f
  obtain ⟨G, hG, _⟩ := negative_normPreserving_extension Ω p g
  have hc : IsClosed {v : Sobolev 𝕜 Ω 1 p | F v.val = G v.val} :=
    isClosed_eq (F.continuous.comp continuous_subtype_val) (G.continuous.comp continuous_subtype_val)
  have hs : (smoothSobolevSubmodule 𝕜 Ω 1 p : Set (Sobolev 𝕜 Ω 1 p)) ⊆
      {v | F v.val = G v.val} := by
    rintro v ⟨φ, hφ⟩
    have hv : v = (testSobolevZero Ω p φ).val :=
      sobolevUnderlying_injective Ω 1 p (hφ.symm.trans (testSobolevZero_underlying Ω p φ).symm)
    change F v.val = G v.val
    rw [hv, hF, hG, h φ]
  ext u
  have hu := (closure_minimal hs hc) u.property
  change F u.val.val = G u.val.val at hu
  rwa [hF, hG] at hu

/-- The smooth class has the expected derivative classes, for every retained index. -/
theorem testSobolevZero_derivative (φ : TestSpace 𝕜 Ω) (α : SobolevIndex d 1) :
    sobolevDerivative (testSobolevZero Ω p φ).val α =
      testToDomainLp Ω p (testPartialWord Ω (α.val.sort (· ≤ ·)) φ) := by
  symm
  apply sobolev_derivative_unique Ω 1 p
  rw [testSobolevZero_underlying, regular_testToDomainLp, regular_testToDomainLp]
  rw [derivative_classicalCompatibility d 𝕜 Ω α.val φ
    (φ.contDiff.of_le (by simp)).contDiffOn]
  congr 1
  exact (testPartialWord_coe Ω _ φ).symm

/-- Equality with the ordinary distribution, with the sign from transposition. -/
theorem divergenceDistribution_test (a : NegativeCoefficients 𝕜 Ω p) (φ : TestSpace 𝕜 Ω) :
    divergenceDistribution a φ = negativePairing a (testSobolevZero Ω p φ) := by
  simp only [divergenceDistribution, negativePairing, sum_apply, distributionPartial,
    smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro α _
  congr 1
  rw [regular_pairing d 𝕜 Ω _ (domainLp_locallyIntegrable Ω (ENNReal.conjExponent p) _),
    testSobolevZero_derivative]
  apply integral_congr_ae
  filter_upwards [testToDomainLp_ae Ω p (testPartialWord Ω (α.val.sort (· ≤ ·)) φ)] with x hx
  rw [hx]

/-- The distribution assigned to a representing tuple determines its functional. -/
theorem divergenceDistribution_eq_iff (a b : NegativeCoefficients 𝕜 Ω p) :
    divergenceDistribution a = divergenceDistribution b ↔
      negativeOfCoefficients Ω p a = negativeOfCoefficients Ω p b := by
  constructor
  · intro h
    apply negative_ext_tests Ω p
    intro φ
    rw [negativeOfCoefficients_pairing, negativeOfCoefficients_pairing,
      ← divergenceDistribution_test, ← divergenceDistribution_test, h]
  · intro h
    ext φ
    rw [divergenceDistribution_test, divergenceDistribution_test,
      ← negativeOfCoefficients_pairing, ← negativeOfCoefficients_pairing, h]

/-- A literal single coordinate in the sum-norm ambient space. -/
def sobolevTupleSingle (α : SobolevIndex d 1) :
    DomainLp 𝕜 Ω p →ₗᵢ[𝕜] SobolevTuple 𝕜 Ω 1 p := by
  classical
  exact
    { toLinearMap := (WithLp.linearEquiv 1 𝕜 (SobolevIndex d 1 → DomainLp 𝕜 Ω p)).symm.toLinearMap.comp
        (LinearMap.single 𝕜 (fun _ : SobolevIndex d 1 => DomainLp 𝕜 Ω p) α)
      norm_map' := by
        intro v
        change ‖(WithLp.toLp 1 (Pi.single α v) : SobolevTuple 𝕜 Ω 1 p)‖ = ‖v‖
        rw [PiLp.norm_eq_of_L1]
        simp [Pi.single_apply, apply_ite] }

theorem sobolevTuple_sum_single (v : SobolevTuple 𝕜 Ω 1 p) :
    (∑ α : SobolevIndex d 1, sobolevTupleSingle Ω p α (v α)) = v := by
  classical
  apply PiLp.ext
  intro β
  change (∑ α : SobolevIndex d 1, WithLp.toLp 1 (Pi.single α (v α))).ofLp β = v.ofLp β
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp [Pi.single_apply]

/-- The precise scalar duality input, separated from the Sobolev argument.
This is used as an explicit argument to the assembly below, not as an axiom. -/
def ScalarLpDuality : Prop :=
  ∀ g : DomainLp 𝕜 Ω p →L[𝕜] 𝕜,
    ∃ a : DomainLp 𝕜 Ω (ENNReal.conjExponent p),
      (∀ v, g v = (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing
        (volume.restrict (Ω : Set (Space d))) p (ENNReal.conjExponent p) v a) ∧ ‖a‖ = ‖g‖

/-- Finite-product Hahn--Banach assembly: only scalar Lp duality remains external. -/
theorem negative_attainment_of_scalarLpDuality (hLp : ScalarLpDuality (𝕜 := 𝕜) Ω p)
    (f : NegativeSobolev 𝕜 Ω p) :
    ∃ a : NegativeCoefficients 𝕜 Ω p, NegativeRepresents a f ∧ ‖a‖ = ‖f‖ := by
  classical
  obtain ⟨g, hg, hn⟩ := negative_normPreserving_extension Ω p f
  let gα (α : SobolevIndex d 1) : DomainLp 𝕜 Ω p →L[𝕜] 𝕜 :=
    g.comp (sobolevTupleSingle Ω p α).toContinuousLinearMap
  choose b hb hbn using fun α => hLp (gα α)
  let a : NegativeCoefficients 𝕜 Ω p := fun α => (-1 : 𝕜) ^ α.val.card • b α
  have hbound : ‖a‖ ≤ ‖f‖ := by
    apply pi_norm_le_iff_of_nonneg (norm_nonneg f) |>.mpr
    intro α
    dsimp [a]
    rw [norm_smul]
    simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul, hbn]
    rw [← hn]
    apply (gα α).opNorm_le_bound (norm_nonneg g)
    intro v
    exact (g.le_opNorm _).trans_eq (by
          change ‖g‖ * ‖sobolevTupleSingle Ω p α v‖ = ‖g‖ * ‖v‖
          rw [(sobolevTupleSingle Ω p α).norm_map])
  have hrep : NegativeRepresents a f := by
    intro u
    rw [← negativeOfCoefficients_pairing, ← hg u]
    simp only [negativeOfCoefficients, sum_apply, smul_apply, ContinuousLinearMap.comp_apply]
    change g u.val.val = ∑ α : SobolevIndex d 1,
      (-1 : 𝕜) ^ α.val.card •
        (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing
          (volume.restrict (Ω : Set (Space d))) p (ENNReal.conjExponent p)
          (sobolevDerivative u.val α) (a α)
    rw [← sobolevTuple_sum_single Ω p u.val.val, map_sum]
    apply Finset.sum_congr rfl
    intro α _
    change gα α (sobolevDerivative u.val α) = _
    rw [hb]
    dsimp [a]
    rw [map_smul]
    have hs : ((-1 : 𝕜) ^ α.val.card) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      simp
    simp only [smul_eq_mul, ← mul_assoc, ← pow_two, hs, one_mul]
  refine ⟨a, hrep, le_antisymm hbound ?_⟩
  have he : f = negativeOfCoefficients Ω p a := by
    ext u
    rw [hrep, negativeOfCoefficients_pairing]
  rw [he]
  exact negativeOfCoefficients_norm Ω p a

theorem negative_norm_le_of_represents (a : NegativeCoefficients 𝕜 Ω p)
    (f : NegativeSobolev 𝕜 Ω p) (ha : NegativeRepresents a f) : ‖f‖ ≤ ‖a‖ := by
  have hf : f = negativeOfCoefficients Ω p a := by
    ext u
    exact (ha u).trans (negativeOfCoefficients_pairing Ω p a u).symm
  rw [hf]
  exact negativeOfCoefficients_norm Ω p a

/-- Surjectivity of the coefficient pairing gives a canonical injective
ordinary-distribution realization. No topology on a distribution dual is substituted. -/
theorem negative_realization_of_representations
    (hrep : ∀ f : NegativeSobolev 𝕜 Ω p, ∃ a : NegativeCoefficients 𝕜 Ω p, NegativeRepresents a f) :
    ∃ R : NegativeSobolev 𝕜 Ω p →ₗ[𝕜] DistributionSpace 𝕜 Ω,
      IsNegativeRealization Ω p R ∧
      ∀ (a : NegativeCoefficients 𝕜 Ω p) (f : NegativeSobolev 𝕜 Ω p),
        NegativeRepresents a f → R f = divergenceDistribution a := by
  classical
  let a (f : NegativeSobolev 𝕜 Ω p) := (hrep f).choose
  have ha (f : NegativeSobolev 𝕜 Ω p) : NegativeRepresents (a f) f := (hrep f).choose_spec
  have hv (f : NegativeSobolev 𝕜 Ω p) (φ : TestSpace 𝕜 Ω) :
      divergenceDistribution (a f) φ = f (testSobolevZero Ω p φ) := by
    rw [divergenceDistribution_test, ← ha f]
  let R : NegativeSobolev 𝕜 Ω p →ₗ[𝕜] DistributionSpace 𝕜 Ω :=
    { toFun := fun f => divergenceDistribution (a f)
      map_add' := by
        intro f g
        ext φ
        change divergenceDistribution (a (f + g)) φ =
          divergenceDistribution (a f) φ + divergenceDistribution (a g) φ
        rw [hv, hv, hv]
        rfl
      map_smul' := by
        intro c f
        ext φ
        change divergenceDistribution (a (c • f)) φ = c • divergenceDistribution (a f) φ
        rw [hv, hv]
        rfl }
  have hR (f : NegativeSobolev 𝕜 Ω p) (φ : TestSpace 𝕜 Ω) :
      R f φ = f (testSobolevZero Ω p φ) := hv f φ
  refine ⟨R, ⟨?_, ?_⟩, ?_⟩
  · intro f g he
    apply negative_ext_tests Ω p
    intro φ
    rw [← hR, ← hR, he]
  · intro f φ u hu
    rw [hR, ← testSobolevZero_unique Ω p φ u hu]
  · intro a f haf
    ext φ
    rw [hR, divergenceDistribution_test, haf]

/-- The minimum and infimum are real-valued, and their lower bound holds for
every representing tuple, not just the selected Hahn--Banach witness. -/
theorem negative_minimum_of_attainment (f : NegativeSobolev 𝕜 Ω p)
    (hatt : ∃ a : NegativeCoefficients 𝕜 Ω p, NegativeRepresents a f ∧ ‖a‖ = ‖f‖) :
    IsLeast {t : ℝ | ∃ a : NegativeCoefficients 𝕜 Ω p, NegativeRepresents a f ∧ t = ‖a‖} ‖f‖ ∧
      ‖f‖ = sInf {t : ℝ | ∃ a : NegativeCoefficients 𝕜 Ω p, NegativeRepresents a f ∧ t = ‖a‖} := by
  obtain ⟨a, ha, hn⟩ := hatt
  have hleast : IsLeast {t : ℝ | ∃ a : NegativeCoefficients 𝕜 Ω p,
      NegativeRepresents a f ∧ t = ‖a‖} ‖f‖ := by
    refine ⟨⟨a, ha, hn.symm⟩, ?_⟩
    rintro t ⟨b, hb, rfl⟩
    exact negative_norm_le_of_represents Ω p b f hb
  exact ⟨hleast, hleast.csInf_eq.symm⟩

/-- Complete assembly after the precise scalar Lp representation input. -/
theorem negative_representation_of_scalarLpDuality (hLp : ScalarLpDuality (𝕜 := 𝕜) Ω p) :
    NegativeSobolevExpected.RepresentationAt (𝕜 := 𝕜) Ω p := by
  have hatt := negative_attainment_of_scalarLpDuality Ω p hLp
  obtain ⟨R, hR, hdist⟩ := negative_realization_of_representations Ω p
    (fun f => (hatt f).imp (fun _ h => h.1))
  refine ⟨R, hR, ?_, hdist, fun f => negative_minimum_of_attainment Ω p f (hatt f)⟩
  intro f
  obtain ⟨a, ha, hn⟩ := hatt f
  exact ⟨a, ha, hdist a f ha, hn⟩

/-- The infimum comparison uses an attaining max-norm tuple and bounds applying
to every tuple. Thus it also applies to any other prescribed equivalent norm. -/
theorem negative_equivalentNormInfimum_of_attainment
    (hatt : ∀ f : NegativeSobolev 𝕜 Ω p,
      ∃ a : NegativeCoefficients 𝕜 Ω p, NegativeRepresents a f ∧ ‖a‖ = ‖f‖)
    (N : NegativeCoefficients 𝕜 Ω p → ℝ) (c C : ℝ) (hc : 0 < c)
    (hN : ∀ a, c * ‖a‖ ≤ N a ∧ N a ≤ C * ‖a‖) (f : NegativeSobolev 𝕜 Ω p) :
    c * ‖f‖ ≤ sInf {t : ℝ | ∃ a : NegativeCoefficients 𝕜 Ω p,
      NegativeRepresents a f ∧ t = N a} ∧
    sInf {t : ℝ | ∃ a : NegativeCoefficients 𝕜 Ω p,
      NegativeRepresents a f ∧ t = N a} ≤ C * ‖f‖ := by
  obtain ⟨a, ha, hn⟩ := hatt f
  have hlower : ∀ t ∈ {t : ℝ | ∃ a : NegativeCoefficients 𝕜 Ω p,
      NegativeRepresents a f ∧ t = N a}, c * ‖f‖ ≤ t := by
    rintro t ⟨b, hb, rfl⟩
    exact (mul_le_mul_of_nonneg_left (negative_norm_le_of_represents Ω p b f hb) hc.le).trans
      (hN b).1
  refine ⟨le_csInf ⟨N a, a, ha, rfl⟩ hlower, ?_⟩
  exact (csInf_le ⟨c * ‖f‖, hlower⟩ ⟨a, ha, rfl⟩).trans (by simpa [hn] using (hN a).2)

/-- Uniform comparison for every finite Lq product norm, including q = infinity. -/
theorem negative_productNormInfimum_of_attainment
    (hatt : ∀ f : NegativeSobolev 𝕜 Ω p,
      ∃ a : NegativeCoefficients 𝕜 Ω p, NegativeRepresents a f ∧ ‖a‖ = ‖f‖)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ f : NegativeSobolev 𝕜 Ω p,
      c * ‖f‖ ≤ sInf {t : ℝ | ∃ a : NegativeCoefficients 𝕜 Ω p,
        NegativeRepresents a f ∧ t = ‖WithLp.toLp q a‖} ∧
      sInf {t : ℝ | ∃ a : NegativeCoefficients 𝕜 Ω p,
        NegativeRepresents a f ∧ t = ‖WithLp.toLp q a‖} ≤ C * ‖f‖ := by
  let e := PiLp.continuousLinearEquiv q 𝕜
    (fun _ : SobolevIndex d 1 => DomainLp 𝕜 Ω (ENNReal.conjExponent p))
  let C : ℝ := ‖e.symm.toContinuousLinearMap‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨1, C, zero_lt_one, hC, ?_⟩
  apply negative_equivalentNormInfimum_of_attainment Ω p hatt _ 1 C zero_lt_one
  intro a
  constructor
  · rw [one_mul]
    apply pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.mpr
    intro α
    exact PiLp.norm_apply_le (WithLp.toLp q a) α
  · have h := e.symm.toContinuousLinearMap.le_opNorm a
    change ‖WithLp.toLp q a‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖a‖ at h
    exact h.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg a))

/-- In dimension zero the sole coefficient is the zero-order coefficient. -/
theorem negative_zeroDimension_of_attainment {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space 0)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hatt : ∀ f : NegativeSobolev 𝕜 Ω p,
      ∃ a : NegativeCoefficients 𝕜 Ω p, NegativeRepresents a f ∧ ‖a‖ = ‖f‖)
    (f : NegativeSobolev 𝕜 Ω p) :
    ∃ a₀ : DomainLp 𝕜 Ω (ENNReal.conjExponent p), ‖a₀‖ = ‖f‖ ∧
      ∀ u, f u = ∫ x in Ω, a₀ x * sobolevUnderlying u.val x := by
  obtain ⟨a, ha, hn⟩ := hatt f
  have hidx (α : SobolevIndex 0 1) : α = zeroSobolevIndex 0 1 := by
    apply Subtype.ext
    apply Multiset.eq_zero_iff_forall_notMem.mpr
    intro i
    exact Fin.elim0 i
  refine ⟨a (zeroSobolevIndex 0 1), ?_, ?_⟩
  · rw [← hn]
    apply le_antisymm (norm_le_pi_norm _ _) ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr ?_)
    intro α
    rw [hidx α]
  · intro u
    rw [ha, negative_pairing_formula]
    simp

/-- Finite-product assembly from scalar Lp duality. -/
theorem negative_reduction : NegativeSobolevExpected.Reduction := by
  intro hLp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d 𝕜 _ Ω p _ hp hpt
    obtain ⟨R, hR, _⟩ := negative_representation_of_scalarLpDuality (𝕜 := 𝕜) Ω p (hLp (𝕜 := 𝕜) Ω p hp hpt)
    exact ⟨R, hR⟩
  · intro d 𝕜 _ Ω p _ hp hpt
    exact negative_representation_of_scalarLpDuality (𝕜 := 𝕜) Ω p (hLp (𝕜 := 𝕜) Ω p hp hpt)
  · intro d 𝕜 _ Ω p _ hp hpt q _
    exact negative_productNormInfimum_of_attainment Ω p
      (negative_attainment_of_scalarLpDuality Ω p (hLp (𝕜 := 𝕜) Ω p hp hpt)) q
  · intro d 𝕜 _ Ω p _ hp hpt N c C hc _ hN f
    exact negative_equivalentNormInfimum_of_attainment Ω p
      (negative_attainment_of_scalarLpDuality Ω p (hLp (𝕜 := 𝕜) Ω p hp hpt)) N c C hc hN f
  · intro 𝕜 _ Ω p _ hp hpt f
    exact negative_zeroDimension_of_attainment Ω p
      (negative_attainment_of_scalarLpDuality Ω p (hLp (𝕜 := 𝕜) Ω p hp hpt)) f

/-- The two scalar prerequisites give the exact bilinear dual representation.
The representing coefficient is in Lp′ on the arbitrary open domain. -/
theorem negative_scalar_duality : NegativeSobolevExpected.ScalarDualityInput := by
  intro d 𝕜 _ Ω p _ hp hpt g
  obtain ⟨a, ha⟩ := negative_lp_representation_pairing (𝕜 := 𝕜) Ω p hp hpt g
  refine ⟨a, ha, ?_⟩
  have hg : g = ((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing
      (volume.restrict (Ω : Set (Space d))) p (ENNReal.conjExponent p)).flip a := by
    ext v
    exact ha v
  rw [hg]
  exact (negative_lp_pairing_norm (𝕜 := 𝕜) Ω p hp hpt a).symm

/-- Restriction to compact smooth tests realizes the dual injectively as
ordinary distributions. -/
theorem negative_realization : NegativeSobolevExpected.Realization :=
  (negative_reduction negative_scalar_duality).1

/-- Every functional has an Lp′ divergence representation with full Sobolev
pairing; the maximum coefficient norm attains the dual norm. -/
theorem negative_representation : NegativeSobolevExpected.Representation :=
  (negative_reduction negative_scalar_duality).2.1

/-- The infimum for every finite Lq coefficient product norm is equivalent to
the dual norm, with constants uniform in the functional. -/
theorem negative_productNormEquivalence : NegativeSobolevExpected.ProductNormEquivalence :=
  (negative_reduction negative_scalar_duality).2.2.1

/-- The same infimum comparison for any prescribed equivalent coefficient norm. -/
theorem negative_equivalentNormInfimum : NegativeSobolevExpected.EquivalentNormInfimum :=
  (negative_reduction negative_scalar_duality).2.2.2.1

/-- In dimension zero the single coefficient f₀ represents the dual element. -/
theorem negative_zeroDimension : NegativeSobolevExpected.ZeroDimension :=
  (negative_reduction negative_scalar_duality).2.2.2.2

end P102.U4
