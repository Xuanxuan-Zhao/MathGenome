import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.EventuallyCompactAsymptotics
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.EventuallyCompactSpectralMapping
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.SpectralRadius
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.LaplaceResolvent
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.GeneratorDeterminesSemigroup
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Projection
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.RieszSplitting
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Topology.Algebra.Module.Complement

noncomputable section
open Filter Topology Set
open scoped NNReal

namespace ExpandedFA.Semigroups.EventuallyCompactAsymptotics
open EventuallyCompactAsymptoticsSpec EventuallyCompactSpectralMappingSpec
open EventuallyCompactSpectralMapping

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The spectral bound is a lower bound for every admissible exponential rate.
This direction holds without eventual compactness. -/
lemma spectralBound_le_rate (T : C0Semigroup ℂ X) {M ω : ℝ}
    (h : HasExponentialBound T M ω) : spectralBound (generator T) ≤ (ω : EReal) := by
  apply sSup_le
  rintro _ ⟨ζ, hζ, rfl⟩
  apply EReal.coe_le_coe_iff.mpr
  by_contra hle
  have hlt : ω < ζ.re := lt_of_not_ge hle
  exact hζ ⟨LaplaceResolvent.inverse T M ω ζ h hlt⟩

lemma spectralBound_le_growthBound (T : C0Semigroup ℂ X) :
    spectralBound (generator T) ≤ growthBound T := by
  apply le_sInf
  rintro _ ⟨ω, rfl, M, hM⟩
  exact spectralBound_le_rate T hM

/-- A single time estimate at rate ω propagates to all times, with one
constant absorbing the bounded residual interval. -/
lemma exponential_bound_of_time_norm (T : C0Semigroup ℂ X)
    (r : ℝ≥0) (hr : 0 < r) (ω : ℝ)
    (hbound : ‖T.operators r‖ ≤ Real.exp (ω * (r : ℝ))) :
    ∃ M : ℝ, HasExponentialBound T M ω := by
  obtain ⟨C, hC, hCr⟩ := T.bounded_on_interval r
  have hr' : 0 < (r : ℝ) := hr
  refine ⟨C * Real.exp (|ω| * (r : ℝ)), ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le hC
      (Real.one_le_exp (mul_nonneg (abs_nonneg _) r.coe_nonneg))
  · intro t
    let n : ℕ := ⌊(t : ℝ) / (r : ℝ)⌋₊
    have hnle : (n : ℝ) * (r : ℝ) ≤ (t : ℝ) :=
      (le_div_iff₀ hr').mp (Nat.floor_le (div_nonneg t.coe_nonneg hr'.le))
    have hnlt : (t : ℝ) < ((n : ℝ) + 1) * (r : ℝ) :=
      (div_lt_iff₀ hr').mp (Nat.lt_floor_add_one ((t : ℝ) / (r : ℝ)))
    let s : ℝ≥0 := ⟨(t : ℝ) - (n : ℝ) * (r : ℝ), sub_nonneg.mpr hnle⟩
    have hs : s ≤ r := by
      change (t : ℝ) - (n : ℝ) * (r : ℝ) ≤ (r : ℝ)
      nlinarith
    have hdecomp : n • r + s = t := by
      apply NNReal.coe_injective
      simp only [nsmul_eq_mul, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast]
      change (n : ℝ) * (r : ℝ) + ((t : ℝ) - (n : ℝ) * (r : ℝ)) = (t : ℝ)
      ring
    have hexp : ω * (r : ℝ) * n ≤ ω * (t : ℝ) + |ω| * (r : ℝ) := by
      have hprod : -ω * (s : ℝ) ≤ |ω| * (r : ℝ) :=
        (mul_le_mul_of_nonneg_right (neg_le_abs ω) s.coe_nonneg).trans
          (mul_le_mul_of_nonneg_left (show (s : ℝ) ≤ (r : ℝ) from hs) (abs_nonneg _))
      change -ω * ((t : ℝ) - (n : ℝ) * (r : ℝ)) ≤ _ at hprod
      nlinarith
    calc
      ‖T.operators t‖ = ‖T.operators (n • r + s)‖ := by rw [hdecomp]
      _ ≤ ‖T.operators (n • r)‖ * ‖T.operators s‖ := by
        rw [T.add_time]
        exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ Real.exp (ω * (r : ℝ)) ^ n * C :=
        mul_le_mul (T.norm_nsmul_time_le (Real.exp_pos _).le hbound n)
          (hCr s hs) (norm_nonneg _) (pow_nonneg (Real.exp_pos _).le _)
      _ = Real.exp (ω * (r : ℝ) * n) * C := by rw [← Real.exp_nat_mul]; congr 2; ring
      _ ≤ Real.exp (ω * (t : ℝ) + |ω| * (r : ℝ)) * C :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) (by linarith)
      _ = C * Real.exp (|ω| * (r : ℝ)) * Real.exp (ω * (t : ℝ)) := by
        rw [Real.exp_add]
        ring

/-- Integer time operators are exactly powers of the time-one operator. -/
lemma operators_nat (T : C0Semigroup ℂ X) (n : ℕ) :
    T.operators (n : ℝ≥0) = T.operators 1 ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, pow_zero, T.at_zero]; rfl
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, T.add_time, ih, pow_succ]
    rfl

/-- Gelfand's formula and a residual time interval turn a strict spectral
radius bound for T(1) into an exponential estimate at the requested rate. -/
lemma exponential_bound_of_time_one_spectrum (T : C0Semigroup ℂ X) (ω : ℝ)
    (hspec : ∀ μ ∈ _root_.spectrum ℂ (T.operators 1), ‖μ‖ < Real.exp ω) :
    ∃ M : ℝ, HasExponentialBound T M ω := by
  classical
  by_cases hX : Subsingleton X
  · letI := hX
    refine ⟨1, le_rfl, fun t => ?_⟩
    have hz : T.operators t = 0 := Subsingleton.elim _ _
    rw [hz, norm_zero]
    positivity
  · letI : Nontrivial X := not_subsingleton_iff_nontrivial.mp hX
    let E := X →L[ℂ] X
    have hE : BanachAlgebra.IsUnitalBanachAlgebra E :=
      ⟨inferInstance, inferInstance, inferInstance⟩
    let B := T.operators 1
    obtain ⟨⟨μ, hμ, hμr⟩, _⟩ := BanachAlgebra.algebraSpectralRadius_maximum E hE B
    have hrad : Specs.ExpandedFA.BanachAlgebra.Conventions.AlgebraSpectralRadiusValue
        ℂ E B < Real.exp ω := hμr ▸ hspec μ hμ
    have hlim := BanachAlgebra.algebraSpectralRadius_root_limit E hE B
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hrad)).exists
    have hpow : ‖B ^ (n + 1)‖ ≤ Real.exp ω ^ (n + 1) := by
      calc
        ‖B ^ (n + 1)‖ =
            (‖B ^ (n + 1)‖ ^ (1 / ((n + 1 : ℕ) : ℝ))) ^ (n + 1) := by
          simpa only [one_div] using
            (Real.rpow_inv_natCast_pow (norm_nonneg (B ^ (n + 1))) (Nat.succ_ne_zero n)).symm
        _ ≤ Real.exp ω ^ (n + 1) :=
          pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) hn.le _
    apply exponential_bound_of_time_norm T ((n + 1 : ℕ) : ℝ≥0) (by positivity) ω
    rw [operators_nat]
    simpa only [Real.exp_nat_mul, mul_comm ω, NNReal.coe_natCast] using hpow

/-- Every rate strictly above the extended-real spectral bound is admissible
for an eventually compact semigroup. In particular, when the spectrum is
empty every real rate is admissible. -/
lemma exponential_bound_above_spectralBound (T : C0Semigroup ℂ X)
    (hT : EventuallyCompact T) (ω : ℝ)
    (hω : spectralBound (generator T) < (ω : EReal)) :
    ∃ M : ℝ, HasExponentialBound T M ω := by
  apply exponential_bound_of_time_one_spectrum T ω
  intro μ hμ
  by_cases hzero : μ = 0
  · simpa [hzero] using Real.exp_pos ω
  · have hm : μ ∈ _root_.spectrum ℂ (T.operators 1) \ {0} := ⟨hμ, hzero⟩
    rw [full_spectral_mapping T hT 1 zero_lt_one] at hm
    obtain ⟨ζ, hζ, rfl⟩ := hm
    have hz : (ζ.re : EReal) ≤ spectralBound (generator T) :=
      le_sSup ⟨ζ, hζ, rfl⟩
    have hre : ζ.re < ω := EReal.coe_lt_coe_iff.mp (hz.trans_lt hω)
    simpa only [NNReal.coe_one, Complex.ofReal_one, one_mul, Complex.norm_exp]
      using Real.exp_lt_exp.mpr hre

/-- The growth and spectral bounds agree as extended reals; no logarithm of
zero or nonempty-spectrum convention is needed. -/
theorem growth_spectral_bound_equality : GrowthSpectralBoundEquality := by
  intro X _ _ _ T hT
  change growthBound T = spectralBound (generator T)
  apply le_antisymm
  · by_contra h
    obtain ⟨ω, hω, hωg⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
    obtain ⟨M, hM⟩ := exponential_bound_above_spectralBound T hT ω hω
    have hg : growthBound T ≤ (ω : EReal) := sInf_le ⟨ω, rfl, M, hM⟩
    exact (not_lt_of_ge hg) hωg
  · exact spectralBound_le_growthBound T

/-- Local finiteness of a spectrum in closed right half-planes turns a
spectral cut with no points on its boundary into a strict gap on the left. -/
lemma spectral_gap_below_cut (S : Set ℂ)
    (hfin : ∀ b : ℝ, {ζ : ℂ | ζ ∈ S ∧ b ≤ ζ.re}.Finite)
    (a : ℝ) (hcut : ∀ ζ ∈ S, ζ.re ≠ a) :
    ∃ b : ℝ, b < a ∧ ∀ ζ ∈ S, ζ.re ≤ a → ζ.re ≤ b := by
  classical
  let F : Set ℂ := {ζ | ζ ∈ S ∧ a - 1 ≤ ζ.re ∧ ζ.re ≤ a}
  have hF : F.Finite := (hfin (a - 1)).subset (fun _ h => ⟨h.1, h.2.1⟩)
  by_cases hne : F.Nonempty
  · obtain ⟨ζ, hζ, hmax⟩ := hF.isCompact.exists_isMaxOn hne Complex.continuous_re.continuousOn
    refine ⟨max (a - 1) ζ.re, max_lt (by linarith) (lt_of_le_of_ne hζ.2.2 (hcut ζ hζ.1)), ?_⟩
    intro η hη hηa
    by_cases hlow : a - 1 ≤ η.re
    · exact (hmax ⟨hη, hlow, hηa⟩).trans (le_max_right _ _)
    · exact (le_of_not_ge hlow).trans (le_max_left _ _)
  · refine ⟨a - 1, by linarith, fun ζ hζ hζa => ?_⟩
    by_contra h
    exact hne ⟨ζ, hζ, le_of_not_ge h, hζa⟩

/-- When every spectral value lies strictly left of a, eventual compactness
upgrades this pointwise condition to an actual exponential estimate at a. -/
lemma exponential_bound_of_spectrum_left (T : C0Semigroup ℂ X)
    (hT : EventuallyCompact T) (a : ℝ)
    (hleft : ∀ ζ ∈ spectrum (generator T), ζ.re < a) :
    ∃ M : ℝ, HasExponentialBound T M a := by
  obtain ⟨b, hba, hb⟩ := spectral_gap_below_cut (spectrum (generator T))
    (generator_spectrum_finite_right_half_plane T hT) a
    (fun ζ hζ => (hleft ζ hζ).ne)
  have hsb : spectralBound (generator T) ≤ (b : EReal) := by
    apply sSup_le
    rintro _ ⟨ζ, hζ, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (hb ζ hζ (hleft ζ hζ).le)
  exact exponential_bound_above_spectralBound T hT a
    (hsb.trans_lt (EReal.coe_lt_coe_iff.mpr hba))

/-- The expansion with an empty spectral sum, including the empty-spectrum
case, follows from the strict complementary spectral gap. -/
lemma finite_expansion_of_spectrum_left (T : C0Semigroup ℂ X)
    (hT : EventuallyCompact T) (a : ℝ)
    (hleft : ∀ ζ ∈ spectrum (generator T), ζ.re < a) : HasFiniteExpansion T a := by
  classical
  obtain ⟨M, hM, hbound⟩ := exponential_bound_of_spectrum_left T hT a hleft
  refine ⟨∅, fun _ => 0, fun _ => 0, fun _ => 0, T.operators, M, ?_, ?_, ?_,
    by linarith, ?_, hbound⟩
  · intro ζ
    simp only [Finset.notMem_empty, false_iff, not_and]
    exact fun hζ => not_lt_of_ge (hleft ζ hζ).le
  · simp
  · simp
  · simp

local instance : NormedAlgebra ℚ (X →L[ℂ] X) :=
  NormedAlgebra.restrictScalars ℚ ℂ (X →L[ℂ] X)

local instance : NormedAlgebra ℝ (X →L[ℂ] X) :=
  NormedAlgebra.restrictScalars ℝ ℂ (X →L[ℂ] X)

/-- The exponential of a bounded operator gives a C₀ semigroup. -/
def exponentialSemigroup (G : X →L[ℂ] X) : C0Semigroup ℂ X where
  operators t := NormedSpace.exp ((t : ℝ) • G)
  at_zero := by simp [NormedSpace.exp_zero]; rfl
  add_time t s := by
    change NormedSpace.exp (((t : ℝ) + (s : ℝ)) • G) = _
    rw [add_smul, NormedSpace.exp_add_of_commute
      ((Commute.refl G).smul_left _ |>.smul_right _)]
    rfl
  strong_zero x := by
    have hc : Continuous (fun r : ℝ => NormedSpace.exp (r.toNNReal.toReal • G) x) :=
      (NormedSpace.exp_continuous.comp
        (NNReal.continuous_coe.comp continuous_real_toNNReal |>.smul continuous_const)).clm_apply
          continuous_const
    simpa only [Real.toNNReal_zero, NNReal.coe_zero, zero_smul,
      NormedSpace.exp_zero, one_apply_eq_self] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- The generator limit of the operator exponential is the original bounded
operator, with no finite-dimensional assumption. -/
lemma exponentialSemigroup_has_limit (G : X →L[ℂ] X) (x : X) :
    HasGeneratorLimit (exponentialSemigroup G) x (G x) := by
  have hd : HasDerivAt (fun r : ℝ => NormedSpace.exp (r • G)) G 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      (hasDerivAt_exp_smul_const G (0 : ℝ))
  have hl := hd.tendsto_slope_zero_right
  have heval := (ContinuousLinearMap.apply ℂ X x).continuous.tendsto G |>.comp hl
  apply heval.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [Function.comp_apply, zero_add]
  change (r⁻¹ • (NormedSpace.exp (r • G) - NormedSpace.exp ((0 : ℝ) • G))) x =
    differenceQuotient (exponentialSemigroup G) r x
  rw [C0Semigroup.differenceQuotient_real]
  simp only [zero_smul, NormedSpace.exp_zero, smul_apply, sub_apply, one_apply_eq_self,
    exponentialSemigroup, Real.coe_toNNReal _ (le_of_lt hr)]

/-- Finite-dimensional semigroups are the exponential of their actual
canonical generator; its whole-domain property has already been proved. -/
lemma finite_semigroup_eq_exp (T : C0Semigroup ℂ X) [FiniteDimensional ℂ X]
    (t : ℝ≥0) : T.operators t = NormedSpace.exp ((t : ℝ) • finiteGenerator T) := by
  let S := exponentialSemigroup (finiteGenerator T)
  have heq : generator T = generator S := by
    apply (Unbounded.equality_iff _ _).mpr
    have hS : (generator S).domain = ⊤ := finite_dimensional_generator_domain S
    refine ⟨(finite_dimensional_generator_domain T).trans hS.symm, ?_⟩
    intro x hxT hxS
    exact generator_limit_unique T x _ _ (generator_has_limit T ⟨x, hxT⟩)
      (finiteGenerator_has_limit T x) |>.trans
      (generator_limit_unique S x _ _ (exponentialSemigroup_has_limit _ x)
        (generator_has_limit S ⟨x, hxS⟩))
  exact GeneratorDeterminesSemigroup.generator_determines_semigroup T S heq t

/-- The recursive root spaces of the exact-domain generator coincide, on a
finite-dimensional space, with the kernels of powers of its matrix shift. -/
lemma finite_generator_root_space (T : C0Semigroup ℂ X) [FiniteDimensional ℂ X]
    (ζ : ℂ) (n : ℕ) :
    generatorRootSpace (generator T) ζ n =
      LinearMap.ker ((ζ • (1 : Module.End ℂ X) - (finiteGenerator T).toLinearMap) ^ n) := by
  let F : Module.End ℂ X := ζ • 1 - (finiteGenerator T).toLinearMap
  induction n with
  | zero =>
    ext x
    simp [generatorRootSpace, F, LinearMap.mem_ker]
  | succ n ih =>
    ext x
    change x ∈ ((generatorRootSpace (generator T) ζ n).comap
      (generatorShift (generator T) ζ)).map (generator T).domain.subtype ↔ _
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [Submodule.mem_comap, ih, LinearMap.mem_ker] at hu
      change (F ^ n) (F (u : X)) = 0 at hu
      change (F ^ (n + 1)) (u : X) = 0
      simpa only [pow_succ, Module.End.mul_apply] using hu
    · intro hx
      have hdom : x ∈ (generator T).domain := by
        rw [finite_dimensional_generator_domain T]; trivial
      refine ⟨⟨x, hdom⟩, ?_, rfl⟩
      rw [Submodule.mem_comap, ih, LinearMap.mem_ker]
      change (F ^ n) (F x) = 0
      change (F ^ (n + 1)) x = 0 at hx
      simpa only [pow_succ, Module.End.mul_apply] using hx

/-- This bridge checks both the opposite shift sign and the full unbounded
power domains, rather than identifying generalized eigenspaces by name. -/
lemma finite_generator_generalized_eigenspace (T : C0Semigroup ℂ X)
    [FiniteDimensional ℂ X] (ζ : ℂ) :
    generatorGeneralizedEigenspace (generator T) ζ =
      Module.End.maxGenEigenspace (finiteGenerator T).toLinearMap ζ := by
  unfold generatorGeneralizedEigenspace
  rw [← Module.End.iSup_genEigenspace_eq]
  congr 1
  funext n
  rw [finite_generator_root_space, Module.End.genEigenspace_nat]
  have hneg : ζ • (1 : Module.End ℂ X) - (finiteGenerator T).toLinearMap =
      (-1 : ℂ) • ((finiteGenerator T).toLinearMap - ζ • 1) := by
    rw [neg_one_smul, neg_sub]
  rw [hneg, smul_pow, LinearMap.ker_smul _ _ (pow_ne_zero _ (by norm_num))]

/-- The analytic exponential terminates at any vanishing power. -/
lemma exp_nilpotent_smul (N : X →L[ℂ] X) (m : ℕ) (hm : N ^ m = 0) (z : ℂ) :
    NormedSpace.exp (z • N) =
      ∑ j ∈ Finset.range m, (z ^ j / (Nat.factorial j : ℂ)) • N ^ j := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  dsimp only
  rw [tsum_eq_sum (s := Finset.range m)]
  · apply Finset.sum_congr rfl
    intro j _
    rw [smul_pow, smul_smul, div_eq_mul_inv, mul_comm]
  · intro j hj
    have hpow : N ^ j = 0 := pow_eq_zero_of_le (Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))) hm
    simp only [smul_pow, hpow, smul_zero]

/-- Jordan's exponential formula for a scalar plus a nilpotent operator. -/
lemma exp_scalar_add_nilpotent (N : X →L[ℂ] X) (m : ℕ) (hm : N ^ m = 0)
    (z ζ : ℂ) :
    NormedSpace.exp (z • (ζ • (1 : X →L[ℂ] X) + N)) =
      Complex.exp (z * ζ) •
        (∑ j ∈ Finset.range m, (z ^ j / (Nat.factorial j : ℂ)) • N ^ j) := by
  have hc : Commute ((z * ζ) • (1 : X →L[ℂ] X)) (z • N) := by
    exact (Commute.one_left (z • N)).smul_left _
  have hscalar : NormedSpace.exp ((z * ζ) • (1 : X →L[ℂ] X)) =
      Complex.exp (z * ζ) • (1 : X →L[ℂ] X) := by
    calc
      _ = algebraMap ℂ (X →L[ℂ] X) (NormedSpace.exp (z * ζ)) :=
        (NormedSpace.algebraMap_exp_comm (𝔸 := X →L[ℂ] X) (z * ζ)).symm
      _ = _ := by rw [← Complex.exp_eq_exp_ℂ, Algebra.algebraMap_eq_smul_one]
  rw [smul_add, smul_smul, NormedSpace.exp_add_of_commute hc, hscalar,
    exp_nilpotent_smul N m hm z, smul_mul_assoc, one_mul]

/-- The matrix exponential on a projected Jordan block. The assumptions
specify the action of the actual matrix generator and the supported nilpotent. -/
lemma exp_mul_projection (G P N : X →L[ℂ] X) (ζ : ℂ) (m : ℕ)
    (hGP : G * P = ζ • P + N) (hNP : N * P = N) (hPN : P * N = N)
    (hm : N ^ m = 0) (z : ℂ) :
    NormedSpace.exp (z • G) * P = Complex.exp (z * ζ) •
      (∑ j ∈ Finset.range m, (z ^ j / (Nat.factorial j : ℂ)) • (N ^ j * P)) := by
  have hc : Commute P N := by exact hPN.trans hNP.symm
  have hs : SemiconjBy P (z • (ζ • (1 : X →L[ℂ] X) + N)) (z • G) := by
    change P * (z • (ζ • 1 + N)) = (z • G) * P
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [mul_add, mul_smul_comm, mul_one, hPN, hGP]
  rw [← hs.exp_right.eq, exp_scalar_add_nilpotent N m hm z ζ, mul_smul_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_smul_comm, (hc.pow_right j).eq]

/-- Finite-dimensional semigroups have the asserted polynomial-exponential
formula on each supported Jordan block of their canonical generator. -/
lemma finite_semigroup_mul_projection (T : C0Semigroup ℂ X) [FiniteDimensional ℂ X]
    (P N : X →L[ℂ] X) (ζ : ℂ) (m : ℕ)
    (hGP : finiteGenerator T * P = ζ • P + N)
    (hNP : N * P = N) (hPN : P * N = N) (hm : N ^ m = 0) (t : ℝ≥0) :
    T.operators t * P = Complex.exp ((t : ℂ) * ζ) •
      (∑ j ∈ Finset.range m,
        ((t : ℂ) ^ j / (Nat.factorial j : ℂ)) • (N ^ j * P)) := by
  rw [finite_semigroup_eq_exp]
  exact exp_mul_projection (finiteGenerator T) P N ζ m hGP hNP hPN hm (t : ℂ)

section MatrixProjections
variable [FiniteDimensional ℂ X]

/-- Sum of the generalized eigenspaces other than the chosen one. -/
def matrixSpectralComplement (G : X →L[ℂ] X) (ζ : ℂ) : Submodule ℂ X :=
  ⨆ η : ℂ, ⨆ (_ : η ≠ ζ), Module.End.maxGenEigenspace G.toLinearMap η

lemma matrix_spectral_isCompl (G : X →L[ℂ] X) (ζ : ℂ) :
    IsCompl (Module.End.maxGenEigenspace G.toLinearMap ζ)
      (matrixSpectralComplement G ζ) := by
  let f : Module.End ℂ X := G.toLinearMap
  refine ⟨f.independent_maxGenEigenspace.disjoint_biSup (fun h => h rfl), ?_⟩
  apply codisjoint_iff.mpr
  apply top_unique
  rw [← f.iSup_maxGenEigenspace_eq_top]
  apply iSup_le
  intro η
  by_cases hη : η = ζ
  · simpa only [hη] using le_sup_left
  · exact le_sup_of_le_right (le_iSup_of_le η (le_iSup_of_le hη le_rfl))

/-- The continuous projection onto one generalized eigenspace along all the
others. It is defined also at nonspectral parameters, where its range is zero. -/
def matrixSpectralProjection (G : X →L[ℂ] X) (ζ : ℂ) : X →L[ℂ] X :=
  ((Module.End.maxGenEigenspace G.toLinearMap ζ).projection
    (matrixSpectralComplement G ζ) (matrix_spectral_isCompl G ζ)).toContinuousLinearMap

lemma matrix_projection_range (G : X →L[ℂ] X) (ζ : ℂ) :
    LinearMap.range (matrixSpectralProjection G ζ).toLinearMap =
      Module.End.maxGenEigenspace G.toLinearMap ζ :=
  Submodule.range_projection _

lemma matrix_projection_idempotent (G : X →L[ℂ] X) (ζ : ℂ) :
    IsIdempotentElem (matrixSpectralProjection G ζ) := by
  ext x
  exact congrArg (fun f : Module.End ℂ X => f x)
    (Submodule.isIdempotentElem_projection (matrix_spectral_isCompl G ζ)).eq

lemma matrix_projection_mem (G : X →L[ℂ] X) (ζ : ℂ) (x : X) :
    matrixSpectralProjection G ζ x ∈ Module.End.maxGenEigenspace G.toLinearMap ζ :=
  Submodule.projection_apply_mem _ _

lemma matrix_projection_eq_self (G : X →L[ℂ] X) (ζ : ℂ) (x : X)
    (hx : x ∈ Module.End.maxGenEigenspace G.toLinearMap ζ) :
    matrixSpectralProjection G ζ x = x :=
  Submodule.projection_apply_of_mem_left _ hx

lemma matrix_projection_eq_zero (G : X →L[ℂ] X) {ζ η : ℂ} (hη : η ≠ ζ) (x : X)
    (hx : x ∈ Module.End.maxGenEigenspace G.toLinearMap η) :
    matrixSpectralProjection G ζ x = 0 := by
  apply Submodule.projection_apply_of_mem_right (matrix_spectral_isCompl G ζ)
  have hle : Module.End.maxGenEigenspace G.toLinearMap η ≤ matrixSpectralComplement G ζ :=
    le_iSup_of_le η (le_iSup_of_le hη le_rfl)
  exact hle hx

lemma matrix_projections_orthogonal (G : X →L[ℂ] X) {ζ η : ℂ} (hζη : ζ ≠ η) :
    matrixSpectralProjection G ζ * matrixSpectralProjection G η = 0 := by
  ext x
  exact matrix_projection_eq_zero G hζη.symm _ (matrix_projection_mem G η x)

/-- Spectral projections commute with every map commuting with the matrix.
Both the range and the specified complementary sum are preserved. -/
lemma matrix_projection_commutes (G H : X →L[ℂ] X) (hGH : Commute G H) (ζ : ℂ) :
    Commute (matrixSpectralProjection G ζ) H := by
  let f : Module.End ℂ X := G.toLinearMap
  let P := matrixSpectralProjection G ζ
  have hc : Commute f H.toLinearMap := hGH.map ContinuousLinearMap.toLinearMapRingHom
  have hv : ∀ η, MapsTo H (f.maxGenEigenspace η) (f.maxGenEigenspace η) :=
    f.mapsTo_maxGenEigenspace_of_comm hc
  have hw : matrixSpectralComplement G ζ ≤ (matrixSpectralComplement G ζ).comap H.toLinearMap := by
    apply iSup_le
    intro η
    apply iSup_le
    intro hη x hx
    have hle : f.maxGenEigenspace η ≤ matrixSpectralComplement G ζ :=
      le_iSup_of_le η (le_iSup_of_le hη le_rfl)
    exact hle (hv η hx)
  ext x
  have hPx : P x ∈ f.maxGenEigenspace ζ := matrix_projection_mem G ζ x
  have hres : x - P x ∈ matrixSpectralComplement G ζ :=
    Submodule.sub_projection_mem _ _
  change P (H x) = H (P x)
  calc
    P (H x) = P (H (P x + (x - P x))) := by congr 2; abel
    _ = P (H (P x)) + P (H (x - P x)) := by rw [map_add, map_add]
    _ = H (P x) + 0 := by
      rw [matrix_projection_eq_self G ζ _ (hv ζ hPx)]
      congr 1
      exact Submodule.projection_apply_of_mem_right _ (hw hres)
    _ = H (P x) := add_zero _

lemma matrix_generalized_eq_bot (G : X →L[ℂ] X) (ζ : ℂ)
    (hζ : ζ ∉ _root_.spectrum ℂ G) :
    Module.End.maxGenEigenspace G.toLinearMap ζ = ⊥ := by
  let f : Module.End ℂ X := G.toLinearMap
  by_contra hne
  have he : f.HasEigenvalue ζ :=
    Module.End.HasUnifEigenvalue.lt (k := ⊤) zero_lt_one hne
  apply hζ
  rw [ContinuousLinearMap.spectrum_eq]
  exact Module.End.hasEigenvalue_iff_mem_spectrum.mp he

/-- The finite set of matrix spectral parameters, including the empty set
on a zero-dimensional space. -/
def matrixSpectrum (G : X →L[ℂ] X) : Finset ℂ :=
  (Module.End.finite_spectrum G.toLinearMap).toFinset

@[simp] lemma mem_matrixSpectrum (G : X →L[ℂ] X) (ζ : ℂ) :
    ζ ∈ matrixSpectrum G ↔ ζ ∈ _root_.spectrum ℂ G := by
  simp only [matrixSpectrum, Set.Finite.mem_toFinset, ContinuousLinearMap.spectrum_eq]

lemma sum_matrix_projections (G : X →L[ℂ] X) :
    ∑ ζ ∈ matrixSpectrum G, matrixSpectralProjection G ζ = 1 := by
  classical
  let f : Module.End ℂ X := G.toLinearMap
  have hblock (η : ℂ) (x : X) (hx : x ∈ f.maxGenEigenspace η) :
      (∑ ζ ∈ matrixSpectrum G, matrixSpectralProjection G ζ) x = x := by
    by_cases hη : η ∈ matrixSpectrum G
    · rw [ContinuousLinearMap.sum_apply, Finset.sum_eq_single η]
      · exact matrix_projection_eq_self G η x hx
      · intro ζ _ hζη
        exact matrix_projection_eq_zero G hζη.symm x hx
      · exact fun h => (h hη).elim
    · have hx0 : x = 0 := by
        have hb := matrix_generalized_eq_bot G η (by simpa only [mem_matrixSpectrum] using hη)
        change x ∈ Module.End.maxGenEigenspace G.toLinearMap η at hx
        simpa only [hb, Submodule.mem_bot] using hx
      simp only [hx0, map_zero]
  ext x
  have hx : x ∈ ⨆ η, f.maxGenEigenspace η := by
    rw [f.iSup_maxGenEigenspace_eq_top]; trivial
  change (∑ ζ ∈ matrixSpectrum G, matrixSpectralProjection G ζ) x = x
  exact Submodule.iSup_induction _ (motive := fun x =>
    (∑ ζ ∈ matrixSpectrum G, matrixSpectralProjection G ζ) x = x) hx hblock (by simp)
    (fun x y hx hy => by simp only [map_add, hx, hy])

/-- The nilpotent part extended by zero off its spectral block. -/
def matrixNilpotent (G : X →L[ℂ] X) (ζ : ℂ) : X →L[ℂ] X :=
  (G - ζ • 1) * matrixSpectralProjection G ζ

lemma matrix_nilpotent_support (G : X →L[ℂ] X) (ζ : ℂ) :
    matrixNilpotent G ζ * matrixSpectralProjection G ζ = matrixNilpotent G ζ ∧
    matrixSpectralProjection G ζ * matrixNilpotent G ζ = matrixNilpotent G ζ := by
  let P := matrixSpectralProjection G ζ
  have hid : P * P = P := (matrix_projection_idempotent G ζ).eq
  have hPF : Commute P (G - ζ • 1) :=
    (matrix_projection_commutes G G (Commute.refl G) ζ).sub_right
      ((Commute.one_right P).smul_right ζ)
  constructor
  · change ((G - ζ • 1) * P) * P = (G - ζ • 1) * P
    rw [mul_assoc, hid]
  · change P * ((G - ζ • 1) * P) = (G - ζ • 1) * P
    rw [← mul_assoc, hPF.eq, mul_assoc, hid]

lemma matrix_nilpotent_pow (G : X →L[ℂ] X) (ζ : ℂ) :
    matrixNilpotent G ζ ^ (Module.finrank ℂ X + 1) = 0 := by
  let P := matrixSpectralProjection G ζ
  let F := G - ζ • 1
  have hPF : Commute F P :=
    ((matrix_projection_commutes G G (Commute.refl G) ζ).sub_right
      ((Commute.one_right P).smul_right ζ)).symm
  change (F * P) ^ (Module.finrank ℂ X + 1) = 0
  rw [hPF.mul_pow, (matrix_projection_idempotent G ζ).pow_succ_eq]
  ext x
  have hx := matrix_projection_mem G ζ x
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank] at hx
  have hx' := (Module.End.genEigenspace G.toLinearMap ζ).monotone
    (show (Module.finrank ℂ X : ℕ∞) ≤ ((Module.finrank ℂ X + 1 : ℕ) : ℕ∞) by
      exact_mod_cast Nat.le_succ (Module.finrank ℂ X)) hx
  have he : (F ^ (Module.finrank ℂ X + 1)).toLinearMap =
      ((G.toLinearMap : Module.End ℂ X) - ζ • 1) ^ (Module.finrank ℂ X + 1) :=
    by simp only [F, ContinuousLinearMap.toLinearMap_pow, ContinuousLinearMap.toLinearMap_sub,
      ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_one]
  have hz := Module.End.mem_genEigenspace_nat.mp hx'
  change (((G.toLinearMap : Module.End ℂ X) - ζ • 1) ^
    (Module.finrank ℂ X + 1)) (P x) = 0 at hz
  rw [← he] at hz
  exact hz

lemma matrix_generator_on_projection (G : X →L[ℂ] X) (ζ : ℂ) :
    G * matrixSpectralProjection G ζ =
      ζ • matrixSpectralProjection G ζ + matrixNilpotent G ζ := by
  unfold matrixNilpotent
  rw [sub_mul, smul_mul_assoc, one_mul]
  abel

/-- The full matrix Jordan expansion uses the actual finite spectral set.
No diagonalizability or positive-dimension assumption is needed. -/
lemma finite_semigroup_jordan_expansion (T : C0Semigroup ℂ X) (t : ℝ≥0) :
    T.operators t = ∑ ζ ∈ matrixSpectrum (finiteGenerator T),
      Complex.exp ((t : ℂ) * ζ) •
        (∑ j ∈ Finset.range (Module.finrank ℂ X + 1),
          ((t : ℂ) ^ j / (Nat.factorial j : ℂ)) •
            (matrixNilpotent (finiteGenerator T) ζ ^ j *
              matrixSpectralProjection (finiteGenerator T) ζ)) := by
  classical
  have hformula (ζ : ℂ) := finite_semigroup_mul_projection T
    (matrixSpectralProjection (finiteGenerator T) ζ)
    (matrixNilpotent (finiteGenerator T) ζ) ζ (Module.finrank ℂ X + 1)
    (matrix_generator_on_projection (finiteGenerator T) ζ)
    (matrix_nilpotent_support (finiteGenerator T) ζ).1
    (matrix_nilpotent_support (finiteGenerator T) ζ).2
    (matrix_nilpotent_pow (finiteGenerator T) ζ) t
  conv_lhs => rw [← mul_one (T.operators t), ← sum_matrix_projections (finiteGenerator T)]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ζ _ => hformula ζ)

end MatrixProjections

/-- The bounded generator on a finite invariant subspace agrees with the
original unbounded generator on every vector of that subspace. -/
lemma finite_invariant_generator_agrees (T : C0Semigroup ℂ X)
    (V : Submodule ℂ X) [FiniteDimensional ℂ V]
    (hV : ∀ t : ℝ≥0, ∀ x ∈ V, T.operators t x ∈ V)
    (x : V) (hx : (x : X) ∈ (generator T).domain) :
    generator T ⟨x, hx⟩ = (finiteGenerator (restrictSemigroup T V hV) x : X) := by
  exact generator_limit_unique T _ _ _ (generator_has_limit T ⟨x, hx⟩)
    (hasGeneratorLimit_intertwine (restrictSemigroup T V hV) T V.subtypeL
      (fun _ _ => rfl) (finiteGenerator_has_limit _ x))

/-- Every iterated root condition restricts correctly to a finite invariant
subspace, including all its intermediate exact generator domains. -/
lemma finite_invariant_root_space (T : C0Semigroup ℂ X)
    (V : Submodule ℂ X) [FiniteDimensional ℂ V]
    (hV : ∀ t : ℝ≥0, ∀ x ∈ V, T.operators t x ∈ V) (ζ : ℂ) (n : ℕ) :
    (generatorRootSpace (generator T) ζ n).comap V.subtype =
      generatorRootSpace (generator (restrictSemigroup T V hV)) ζ n := by
  let S := restrictSemigroup T V hV
  let G := finiteGenerator S
  let F : Module.End ℂ V := ζ • 1 - G.toLinearMap
  rw [finite_generator_root_space (restrictSemigroup T V hV) ζ n]
  change (generatorRootSpace (generator T) ζ n).comap V.subtype = LinearMap.ker (F ^ n)
  induction n with
  | zero => ext x; simp [generatorRootSpace, LinearMap.mem_ker]
  | succ n ih =>
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, heq⟩ := hx
      have hux : (u : X) = (x : X) := heq
      have hxdom : (x : X) ∈ (generator T).domain := hux ▸ u.property
      have hAu : generator T u = (G x : X) := by
        have he : u = ⟨x, hxdom⟩ := Subtype.ext hux
        rw [he]
        exact finite_invariant_generator_agrees T V hV x hxdom
      have hshift : generatorShift (generator T) ζ u = (F x : X) := by
        change ζ • (u : X) - generator T u = ζ • (x : X) - (G x : X)
        rw [hux, hAu]
      have hFx : F x ∈ (generatorRootSpace (generator T) ζ n).comap V.subtype := by
        change (F x : X) ∈ generatorRootSpace (generator T) ζ n
        rw [← hshift]
        exact hu
      rw [ih, LinearMap.mem_ker] at hFx
      change (F ^ (n + 1)) x = 0
      simpa only [pow_succ, Module.End.mul_apply] using hFx
    · intro hx
      have hxdom := finite_invariant_subspace_mem_domain T V hV x
      have hAx := finite_invariant_generator_agrees T V hV x hxdom
      have hshift : generatorShift (generator T) ζ ⟨x, hxdom⟩ = (F x : X) := by
        change ζ • (x : X) - generator T ⟨x, hxdom⟩ =
          ζ • (x : X) - (G x : X)
        rw [hAx]
      have hFx : F x ∈ (generatorRootSpace (generator T) ζ n).comap V.subtype := by
        rw [ih, LinearMap.mem_ker]
        change (F ^ (n + 1)) x = 0 at hx
        simpa only [pow_succ, Module.End.mul_apply] using hx
      change (x : X) ∈ ((generatorRootSpace (generator T) ζ n).comap
        (generatorShift (generator T) ζ)).map (generator T).domain.subtype
      refine ⟨⟨x, hxdom⟩, ?_, rfl⟩
      change generatorShift (generator T) ζ ⟨x, hxdom⟩ ∈ generatorRootSpace (generator T) ζ n
      rw [hshift]
      exact hFx

/-- If a finite invariant subspace contains the full generalized eigenspace,
its matrix eigenspace maps onto that exact ambient space. The containment can
be supplied by a genuine complementary resolvent, as in the upstream splitting. -/
lemma finite_invariant_generalized_eigenspace (T : C0Semigroup ℂ X)
    (V : Submodule ℂ X) [FiniteDimensional ℂ V]
    (hV : ∀ t : ℝ≥0, ∀ x ∈ V, T.operators t x ∈ V) (ζ : ℂ)
    (hζ : generatorGeneralizedEigenspace (generator T) ζ ≤ V) :
    (Module.End.maxGenEigenspace (finiteGenerator (restrictSemigroup T V hV)).toLinearMap ζ).map
      V.subtype = generatorGeneralizedEigenspace (generator T) ζ := by
  rw [← finite_generator_generalized_eigenspace]
  unfold generatorGeneralizedEigenspace
  rw [Submodule.map_iSup]
  apply iSup_congr
  intro n
  rw [← finite_invariant_root_space T V hV ζ n, Submodule.map_comap_eq,
    Submodule.range_subtype]
  exact inf_eq_right.mpr ((le_iSup (generatorRootSpace (generator T) ζ) n).trans hζ)

/-- Restricting to a complete invariant subspace preserves eventual
compactness; compactness of its unit-ball image is in the inherited norm. -/
lemma eventuallyCompact_restrict (T : C0Semigroup ℂ X) (hT : EventuallyCompact T)
    (V : Submodule ℂ X) [CompleteSpace V]
    (hV : ∀ t : ℝ≥0, ∀ x ∈ V, T.operators t x ∈ V) :
    EventuallyCompact (restrictSemigroup T V hV) := by
  obtain ⟨t₀, ht₀, hc⟩ := hT
  refine ⟨t₀, ht₀, ?_⟩
  apply (Compactness.compact_iff_isCompactOperator _).mpr
  exact ((Compactness.compact_iff_isCompactOperator _).mp hc).restrict' (hV t₀)

/-- The complementary semigroup estimate transfers to the ambient
remainder, with the coordinate map norm absorbed into the constant. -/
lemma restricted_remainder_bound (T : C0Semigroup ℂ X) (hT : EventuallyCompact T)
    (W : Submodule ℂ X) [CompleteSpace W]
    (hW : ∀ t : ℝ≥0, ∀ x ∈ W, T.operators t x ∈ W) (a : ℝ)
    (hleft : ∀ ζ ∈ spectrum (generator (restrictSemigroup T W hW)), ζ.re < a)
    (Q : X →L[ℂ] W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ≥0,
      ‖W.subtypeL.comp (((restrictSemigroup T W hW).operators t).comp Q)‖ ≤
        C * Real.exp (a * (t : ℝ)) := by
  let U := restrictSemigroup T W hW
  obtain ⟨M, hM, hbound⟩ := exponential_bound_of_spectrum_left U
    (eventuallyCompact_restrict T hT W hW) a hleft
  refine ⟨M * ‖Q‖, mul_nonneg (by linarith) (norm_nonneg Q), fun t => ?_⟩
  calc
    ‖W.subtypeL.comp ((U.operators t).comp Q)‖ ≤
        ‖W.subtypeL‖ * (‖U.operators t‖ * ‖Q‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg W.subtypeL))
    _ ≤ 1 * (M * Real.exp (a * (t : ℝ)) * ‖Q‖) :=
      mul_le_mul W.norm_subtypeL_le
        (mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg Q))
        (mul_nonneg (norm_nonneg (U.operators t)) (norm_nonneg Q)) zero_le_one
    _ = (M * ‖Q‖) * Real.exp (a * (t : ℝ)) := by ring

end ExpandedFA.Semigroups.EventuallyCompactAsymptotics

namespace ExpandedFA.Semigroups.EventuallyCompactAsymptotics
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Extend an endomorphism of a complemented subspace by zero along the
chosen coordinate map. -/
def liftEnd (V : Submodule ℂ X) (Q : X →L[ℂ] V) (H : V →L[ℂ] V) : X →L[ℂ] X :=
  V.subtypeL.comp (H.comp Q)

@[simp] lemma liftEnd_apply (V : Submodule ℂ X) (Q : X →L[ℂ] V)
    (H : V →L[ℂ] V) (x : X) : liftEnd V Q H x = (H (Q x) : X) := rfl

@[simp] lemma liftEnd_zero (V : Submodule ℂ X) (Q : X →L[ℂ] V) :
    liftEnd V Q 0 = 0 := by ext; rfl

@[simp] lemma liftEnd_add (V : Submodule ℂ X) (Q : X →L[ℂ] V)
    (H K : V →L[ℂ] V) : liftEnd V Q (H + K) = liftEnd V Q H + liftEnd V Q K := by
  ext; rfl

@[simp] lemma liftEnd_smul (V : Submodule ℂ X) (Q : X →L[ℂ] V)
    (z : ℂ) (H : V →L[ℂ] V) : liftEnd V Q (z • H) = z • liftEnd V Q H := by
  ext; rfl

lemma liftEnd_sum {ι : Type*} (V : Submodule ℂ X) (Q : X →L[ℂ] V)
    (s : Finset ι) (H : ι → V →L[ℂ] V) :
    liftEnd V Q (∑ j ∈ s, H j) = ∑ j ∈ s, liftEnd V Q (H j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => simp [hj, ih]

lemma liftEnd_mul (V : Submodule ℂ X) (Q : X →L[ℂ] V)
    (hQ : ∀ x : V, Q x = x) (H K : V →L[ℂ] V) :
    liftEnd V Q (H * K) = liftEnd V Q H * liftEnd V Q K := by
  ext x
  change (H (K (Q x)) : X) = (H (Q (K (Q x))) : X)
  rw [hQ]

/-- The projection factor makes the zeroth power lift correctly. -/
lemma liftEnd_pow_mul (V : Submodule ℂ X) (Q : X →L[ℂ] V)
    (hQ : ∀ x : V, Q x = x) (N P : V →L[ℂ] V) (j : ℕ) :
    liftEnd V Q (N ^ j * P) = liftEnd V Q N ^ j * liftEnd V Q P := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc, liftEnd_mul V Q hQ, ih, ← mul_assoc, ← pow_succ']

lemma liftEnd_pow_succ (V : Submodule ℂ X) (Q : X →L[ℂ] V)
    (hQ : ∀ x : V, Q x = x) (N : V →L[ℂ] V) (j : ℕ) :
    liftEnd V Q (N ^ (j + 1)) = liftEnd V Q N ^ (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, liftEnd_mul V Q hQ, ih, ← pow_succ]

lemma liftEnd_range (V : Submodule ℂ X) (Q : X →L[ℂ] V)
    (hQ : ∀ x : V, Q x = x) (H : V →L[ℂ] V) :
    LinearMap.range (liftEnd V Q H).toLinearMap = (LinearMap.range H.toLinearMap).map V.subtype := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨H (Q y), ⟨Q y, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨(z : X), by simp [hQ]⟩

lemma liftEnd_commute (V : Submodule ℂ X) (Q : X →L[ℂ] V)
    (B : X →L[ℂ] X) (S P : V →L[ℂ] V)
    (hBQ : ∀ x, Q (B x) = S (Q x))
    (hBS : ∀ x : V, B x = (S x : X)) (hPS : Commute P S) :
    Commute (liftEnd V Q P) B := by
  ext x
  change (P (Q (B x)) : X) = B (P (Q x))
  rw [hBQ, hBS]
  exact congrArg (fun y : V => (y : X)) (congrArg (fun f : V →L[ℂ] V => f (Q x)) hPS.eq)

lemma invariant_projection_coordinate (V W : Submodule ℂ X) (hVW : V.IsTopCompl W)
    (B : X →L[ℂ] X) (hV : ∀ x ∈ V, B x ∈ V) (hW : ∀ x ∈ W, B x ∈ W)
    (x : X) :
    V.projectionOntoL W hVW (B x) = ⟨B (V.projectionOntoL W hVW x), hV _ (by exact (V.projectionOntoL W hVW x).property)⟩ := by
  apply Subtype.ext
  have hdecomp := Submodule.projectionL_add_projectionL_eq_self hVW x
  change V.projectionL W hVW (B x) = B (V.projectionL W hVW x)
  conv_lhs => rw [← hdecomp, map_add, map_add]
  rw [Submodule.projectionL_apply_left hVW ⟨B (V.projectionL W hVW x), hV _ (Submodule.projectionL_apply_mem hVW x)⟩]
  rw [Submodule.projectionL_apply_eq_zero_of_mem_right hVW (hW _ (Submodule.projectionL_apply_mem hVW.symm x)), add_zero]


variable [CompleteSpace X]
open EventuallyCompactSpectralMapping

lemma restricted_projection_coordinate (T : C0Semigroup ℂ X)
    (V W : Submodule ℂ X) [CompleteSpace V] [CompleteSpace W] (hVW : V.IsTopCompl W)
    (hV : ∀ t : ℝ≥0, ∀ x ∈ V, T.operators t x ∈ V)
    (hW : ∀ t : ℝ≥0, ∀ x ∈ W, T.operators t x ∈ W)
    (t : ℝ≥0) (x : X) :
    V.projectionOntoL W hVW (T.operators t x) =
      (restrictSemigroup T V hV).operators t (V.projectionOntoL W hVW x) :=
  invariant_projection_coordinate V W hVW (T.operators t) (hV t) (hW t) x

lemma restricted_semigroup_decomposition (T : C0Semigroup ℂ X)
    (V W : Submodule ℂ X) [CompleteSpace V] [CompleteSpace W] (hVW : V.IsTopCompl W)
    (hV : ∀ t : ℝ≥0, ∀ x ∈ V, T.operators t x ∈ V)
    (hW : ∀ t : ℝ≥0, ∀ x ∈ W, T.operators t x ∈ W) (t : ℝ≥0) :
    T.operators t = liftEnd V (V.projectionOntoL W hVW)
      ((restrictSemigroup T V hV).operators t) +
      W.subtypeL.comp (((restrictSemigroup T W hW).operators t).comp
        (W.projectionOntoL V hVW.symm)) := by
  ext x
  change T.operators t x = T.operators t (V.projectionL W hVW x) +
    T.operators t (W.projectionL V hVW.symm x)
  rw [← map_add, Submodule.projectionL_add_projectionL_eq_self]

section LiftedMatrix
variable (V : Submodule ℂ X) [FiniteDimensional ℂ V]
    (Q : X →L[ℂ] V) (hQ : ∀ x : V, Q x = x)
include hQ

lemma lifted_matrix_range (G : V →L[ℂ] V) (ζ : ℂ) :
    LinearMap.range (liftEnd V Q (matrixSpectralProjection G ζ)).toLinearMap =
      (Module.End.maxGenEigenspace G.toLinearMap ζ).map V.subtype := by
  rw [liftEnd_range V Q hQ, matrix_projection_range]

lemma lifted_matrix_idempotent (G : V →L[ℂ] V) (ζ : ℂ) :
    liftEnd V Q (matrixSpectralProjection G ζ) *
      liftEnd V Q (matrixSpectralProjection G ζ) =
        liftEnd V Q (matrixSpectralProjection G ζ) := by
  rw [← liftEnd_mul V Q hQ, (matrix_projection_idempotent G ζ).eq]

lemma lifted_matrix_support (G : V →L[ℂ] V) (ζ : ℂ) :
    liftEnd V Q (matrixNilpotent G ζ) * liftEnd V Q (matrixSpectralProjection G ζ) =
      liftEnd V Q (matrixNilpotent G ζ) ∧
    liftEnd V Q (matrixSpectralProjection G ζ) * liftEnd V Q (matrixNilpotent G ζ) =
      liftEnd V Q (matrixNilpotent G ζ) := by
  constructor
  · rw [← liftEnd_mul V Q hQ, (matrix_nilpotent_support G ζ).1]
  · rw [← liftEnd_mul V Q hQ, (matrix_nilpotent_support G ζ).2]

lemma lifted_matrix_nilpotent (G : V →L[ℂ] V) (ζ : ℂ) :
    liftEnd V Q (matrixNilpotent G ζ) ^ (Module.finrank ℂ V + 1) = 0 := by
  rw [← liftEnd_pow_succ V Q hQ, matrix_nilpotent_pow, liftEnd_zero]

lemma lifted_matrix_orthogonal (G : V →L[ℂ] V) {ζ η : ℂ} (hζη : ζ ≠ η) :
    liftEnd V Q (matrixSpectralProjection G ζ) *
      liftEnd V Q (matrixSpectralProjection G η) = 0 := by
  rw [← liftEnd_mul V Q hQ, matrix_projections_orthogonal G hζη, liftEnd_zero]

lemma lifted_finite_jordan_expansion (S : C0Semigroup ℂ V) (t : ℝ≥0) :
    liftEnd V Q (S.operators t) = ∑ ζ ∈ matrixSpectrum (finiteGenerator S),
      Complex.exp ((t : ℂ) * ζ) •
        (∑ j ∈ Finset.range (Module.finrank ℂ V + 1),
          ((t : ℂ) ^ j / (Nat.factorial j : ℂ)) •
            (liftEnd V Q (matrixNilpotent (finiteGenerator S) ζ) ^ j *
              liftEnd V Q (matrixSpectralProjection (finiteGenerator S) ζ))) := by
  classical
  rw [finite_semigroup_jordan_expansion, liftEnd_sum]
  apply Finset.sum_congr rfl
  intro ζ _
  rw [liftEnd_smul, liftEnd_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [liftEnd_smul, liftEnd_pow_mul V Q hQ]

end LiftedMatrix
end ExpandedFA.Semigroups.EventuallyCompactAsymptotics

namespace ExpandedFA.Semigroups.EventuallyCompactAsymptotics
open EventuallyCompactAsymptoticsSpec EventuallyCompactSpectralMappingSpec
open EventuallyCompactSpectralMapping
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Every eigenvalue of the generator on a finite invariant subspace is an
ambient generator spectral value, using the actual one-sided derivative domain. -/
lemma finite_invariant_spectrum_subset (T : C0Semigroup ℂ X)
    (V : Submodule ℂ X) [FiniteDimensional ℂ V]
    (hV : ∀ t : ℝ≥0, ∀ x ∈ V, T.operators t x ∈ V) :
    _root_.spectrum ℂ (finiteGenerator (restrictSemigroup T V hV)) ⊆
      spectrum (generator T) := by
  intro ζ hζ
  let S := restrictSemigroup T V hV
  let G := finiteGenerator S
  have heigen : Module.End.HasEigenvalue G.toLinearMap ζ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr (by
      rwa [ContinuousLinearMap.spectrum_eq] at hζ)
  obtain ⟨y, hy⟩ := heigen.exists_hasEigenvector
  have hGy : G y = ζ • y := hy.apply_eq_smul
  have hlim := hasGeneratorLimit_intertwine S T V.subtypeL (fun _ _ => rfl)
    (finiteGenerator_has_limit S y)
  have hlim' : HasGeneratorLimit T (y : X) (ζ • (y : X)) := by
    have hval : (G y : X) = ζ • (y : X) := congrArg Subtype.val hGy
    exact hval ▸ hlim
  let dy : (generator T).domain := ⟨y, ⟨_, hlim'⟩⟩
  have hAy : generator T dy = ζ • (y : X) :=
    generator_limit_unique T _ _ _ (generator_has_limit T dy) hlim'
  intro hres
  obtain ⟨R⟩ := hres
  have hz := R.left_inverse dy
  rw [hAy, sub_self, map_zero] at hz
  exact hy.2 (Subtype.ext hz.symm)

/-- The outer modulus condition at one positive time forces the finite
matrix generator spectrum strictly to the right of the prescribed cut. -/
lemma finite_spectrum_right_of_time_spectrum (T : C0Semigroup ℂ X)
    [FiniteDimensional ℂ X] (t₀ : ℝ≥0) (ht₀ : 0 < t₀) (a : ℝ)
    (houter : ∀ μ ∈ _root_.spectrum ℂ (T.operators t₀),
      Real.exp (a * (t₀ : ℝ)) < ‖μ‖) :
    ∀ ζ ∈ _root_.spectrum ℂ (finiteGenerator T), a < ζ.re := by
  intro ζ hζ
  have hgen : ζ ∈ C0SemigroupSpec.spectrumValue (generator T) := by
    rwa [finite_generator_spectrum]
  have htime := SpectralInclusion.spectral_inclusion T t₀ ht₀ ⟨ζ, hgen, rfl⟩
  have hn := houter _ htime.1
  rw [Complex.norm_exp] at hn
  have hmul : a * (t₀ : ℝ) < (t₀ : ℝ) * ζ.re := by
    simpa only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using Real.exp_lt_exp.mp hn
  have ht₀' : 0 < (t₀ : ℝ) := ht₀
  nlinarith

/-- With the complementary generator strictly to the left and the finite
matrix generator strictly to the right, its spectrum is the exact ambient
right spectral set. Coordinates carry their full uniqueness property. -/
lemma finite_invariant_spectrum_eq_right (T : C0Semigroup ℂ X)
    (V W : Submodule ℂ X) [FiniteDimensional ℂ V] [CompleteSpace W]
    (hV : ∀ t : ℝ≥0, ∀ x ∈ V, T.operators t x ∈ V)
    (hW : ∀ t : ℝ≥0, ∀ x ∈ W, T.operators t x ∈ W)
    (P : X →L[ℂ] V) (Q : X →L[ℂ] W)
    (hPQ : ∀ x, (P x : X) + Q x = x ∧
      ∀ v : V, ∀ w : W, (v : X) + w = x → v = P x ∧ w = Q x)
    (a : ℝ)
    (hleft : ∀ ζ ∈ spectrum (generator (restrictSemigroup T W hW)), ζ.re < a)
    (hright : ∀ ζ ∈ _root_.spectrum ℂ
      (finiteGenerator (restrictSemigroup T V hV)), a < ζ.re) :
    _root_.spectrum ℂ (finiteGenerator (restrictSemigroup T V hV)) =
      {ζ : ℂ | ζ ∈ spectrum (generator T) ∧ a < ζ.re} := by
  ext ζ
  constructor
  · intro hζ
    exact ⟨finite_invariant_spectrum_subset T V hV hζ, hright ζ hζ⟩
  · rintro ⟨hζ, hζa⟩
    have hunion := generator_spectrum_subset_union T V W hV hW P Q hPQ hζ
    have hVspec : ζ ∈ C0SemigroupSpec.spectrumValue
        (generator (restrictSemigroup T V hV)) :=
      hunion.resolve_right (fun hw => (not_lt_of_ge hζa.le) (hleft ζ hw))
    rwa [finite_generator_spectrum] at hVspec

/-- Every ambient right generalized eigenspace lies entirely in the finite
summand, because the complementary generator has a genuine two-sided resolvent. -/
lemma generalized_eigenspace_le_of_spectrum_left (T : C0Semigroup ℂ X)
    (V W : Submodule ℂ X) [CompleteSpace V] [CompleteSpace W]
    (hV : ∀ t : ℝ≥0, ∀ x ∈ V, T.operators t x ∈ V)
    (hW : ∀ t : ℝ≥0, ∀ x ∈ W, T.operators t x ∈ W)
    (P : X →L[ℂ] V) (Q : X →L[ℂ] W)
    (hPQ : ∀ x, (P x : X) + Q x = x ∧
      ∀ v : V, ∀ w : W, (v : X) + w = x → v = P x ∧ w = Q x)
    (a : ℝ)
    (hleft : ∀ ζ ∈ spectrum (generator (restrictSemigroup T W hW)), ζ.re < a)
    (ζ : ℂ) (hζ : a < ζ.re) :
    generatorGeneralizedEigenspace (generator T) ζ ≤ V := by
  have hnot : ζ ∉ spectrum (generator (restrictSemigroup T W hW)) :=
    fun hmem => (not_lt_of_ge hζ.le) (hleft ζ hmem)
  have hres : Nonempty (Unbounded.ResolventInverse
      (generator (restrictSemigroup T W hW)) ζ) := not_not.mp hnot
  exact generalized_eigenspace_le_of_complement_resolvent T V W hV hW P Q hPQ ζ hres.some

/-- Matrix spectral projections commute with the corresponding finite
semigroup at every nonnegative time. -/
lemma matrix_projection_semigroup_commutes (T : C0Semigroup ℂ X)
    [FiniteDimensional ℂ X] (ζ : ℂ) (t : ℝ≥0) :
    Commute (matrixSpectralProjection (finiteGenerator T) ζ) (T.operators t) := by
  rw [finite_semigroup_eq_exp]
  exact ((matrix_projection_commutes (finiteGenerator T) (finiteGenerator T)
    (Commute.refl _) ζ).smul_right (t : ℝ)).exp_right

end ExpandedFA.Semigroups.EventuallyCompactAsymptotics

namespace ExpandedFA.Semigroups.EventuallyCompactAsymptotics
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The continuous projections of topological complementary subspaces give
precisely the unique-coordinate interface for exact generator decompositions. -/
lemma topCompl_coordinates (V W : Submodule ℂ X) (hVW : V.IsTopCompl W) :
    ∀ x, ((V.projectionOntoL W hVW) x : X) + (W.projectionOntoL V hVW.symm) x = x ∧
      ∀ v : V, ∀ w : W, (v : X) + w = x →
        v = (V.projectionOntoL W hVW) x ∧ w = (W.projectionOntoL V hVW.symm) x := by
  intro x
  refine ⟨Submodule.projectionL_add_projectionL_eq_self hVW x, ?_⟩
  intro v w hvw
  constructor
  · have h := congrArg (V.projectionOntoL W hVW) hvw
    simpa only [map_add, Submodule.projectionOntoL_apply_left,
      Submodule.projectionOntoL_apply_right, add_zero] using h
  · have h := congrArg (W.projectionOntoL V hVW.symm) hvw
    simpa only [map_add, Submodule.projectionOntoL_apply_left,
      Submodule.projectionOntoL_apply_right, zero_add] using h

end ExpandedFA.Semigroups.EventuallyCompactAsymptotics

namespace ExpandedFA.Semigroups.EventuallyCompactAsymptotics
open EventuallyCompactAsymptoticsSpec EventuallyCompactSpectralMappingSpec
open EventuallyCompactSpectralMapping
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma compact_cut_decomposition (T : C0Semigroup ℂ X) (hT : EventuallyCompact T)
    (a : ℝ) (hcut : ∀ ζ ∈ spectrum (generator T), ζ.re ≠ a) :
    ∃ (P : X →L[ℂ] X) (cV : CompleteSpace P.range)
      (cW : CompleteSpace (1 - P).range),
      letI := cV
      letI := cW
      ∃ (hV : ∀ t : ℝ≥0, ∀ x ∈ P.range, T.operators t x ∈ P.range)
        (hW : ∀ t : ℝ≥0, ∀ x ∈ (1 - P).range, T.operators t x ∈ (1 - P).range),
        Submodule.IsTopCompl P.range (1 - P).range ∧ FiniteDimensional ℂ P.range ∧
        (∀ ζ ∈ spectrum (generator (restrictSemigroup T (1 - P).range hW)), ζ.re < a) ∧
        (∀ ζ ∈ spectrum (generator (restrictSemigroup T P.range hV)), a < ζ.re) := by
  classical
  obtain ⟨t₀, ht₀, hKc⟩ := hT
  let K := T.operators t₀
  let r := Real.exp ((t₀ : ℝ) * a)
  have hr : 0 < r := Real.exp_pos _
  have ht : 0 < (t₀ : ℝ) := ht₀
  have hcircle : ∀ μ ∈ _root_.spectrum ℂ K, ‖μ‖ ≠ r := by
    intro μ hμ heq
    have hμ0 : μ ≠ 0 := by intro h; rw [h, norm_zero] at heq; linarith
    have hm : μ ∈ _root_.spectrum ℂ (T.operators t₀) \ {0} := ⟨hμ, by simpa using hμ0⟩
    rw [full_spectral_mapping T ⟨t₀, ht₀, hKc⟩ t₀ ht₀] at hm
    obtain ⟨ζ, hζ, rfl⟩ := hm
    apply hcut ζ hζ
    have hexp : Real.exp ((t₀ : ℝ) * ζ.re) = Real.exp ((t₀ : ℝ) * a) := by
      simpa only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero] using heq
    exact (mul_left_cancel₀ (ne_of_gt ht) (Real.exp_injective hexp))
  let K₁ : Set ℂ := {μ | μ ∈ _root_.spectrum ℂ K ∧ r ≤ ‖μ‖}
  let K₂ : Set ℂ := {μ | μ ∈ _root_.spectrum ℂ K ∧ ‖μ‖ ≤ r}
  have hc₁ : IsCompact K₁ := (spectrum.isCompact K).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hc₂ : IsCompact K₂ := (spectrum.isCompact K).inter_right
    (isClosed_le continuous_norm continuous_const)
  have hd : Disjoint K₁ K₂ := by
    apply Set.disjoint_left.mpr
    intro μ h₁ h₂
    exact hcircle μ h₁.1 (le_antisymm h₂.2 h₁.2)
  have hspec : _root_.spectrum ℂ K = K₁ ∪ K₂ := by
    ext μ
    exact ⟨fun h => (le_total r ‖μ‖).elim (fun hr => Or.inl ⟨h, hr⟩)
      (fun hr => Or.inr ⟨h, hr⟩), fun h => h.elim And.left And.left⟩
  obtain ⟨U₁, U₂, ho₁, ho₂, hdU, hs₁, hs₂, hfd⟩ :=
    BanachAlgebra.RieszSplitting.separating_neighborhoods K₁ K₂ hc₁ hc₂ hd
  let f : ℂ → ℂ := U₁.indicator (fun _ => 1)
  have hf₁ : EqOn f (fun _ => 1) U₁ := by intro μ hμ; exact indicator_of_mem hμ _
  have hf₂ : EqOn f (fun _ => 0) U₂ := by
    intro μ hμ
    exact indicator_of_notMem (fun hm => Set.disjoint_left.mp hdU hm hμ) _
  let P := BanachAlgebra.ContourCalculus.holomorphicValue (X →L[ℂ] X) K (U₁ ∪ U₂) f
  have hsplit := BanachAlgebra.RieszSplitting.riesz_splitting X K K₁ K₂
    hc₁ hc₂ hd hspec U₁ U₂ f ho₁ ho₂ hdU hs₁ hs₂ hf₁ hf₂
  change BanachAlgebra.RieszSplitting.Spec.SplittingData K P K₁ K₂ at hsplit
  obtain ⟨hP, hcomm, hclosedV, hclosedW, R₁, R₂, heR₁, heR₂, hsR₁, hsR₂, e, he, hesymm⟩ := hsplit
  letI cV : CompleteSpace P.range := hclosedV.completeSpace_coe
  letI cW : CompleteSpace (1 - P).range := hclosedW.completeSpace_coe
  change _root_.spectrum ℂ R₁ = K₁ at hsR₁
  change _root_.spectrum ℂ R₂ = K₂ at hsR₂
  have hKU : _root_.spectrum ℂ K ⊆ U₁ ∪ U₂ := by
    rw [hspec]; exact union_subset_union hs₁ hs₂
  have hcP (t : ℝ≥0) : Commute (T.operators t) P := by
    change T.operators t * P = P * T.operators t
    exact BanachAlgebra.HolomorphicHomomorphism.operator_commutation X K
      (T.operators t) (U₁ ∪ U₂) f (ho₁.union ho₂) hKU hfd
      (by ext x; exact T.operators_commute _ _ x)
  have hV : ∀ t : ℝ≥0, ∀ x ∈ P.range, T.operators t x ∈ P.range :=
    fun t => BanachAlgebra.RieszSplitting.invariant_range (hcP t)
  have hW : ∀ t : ℝ≥0, ∀ x ∈ (1 - P).range, T.operators t x ∈ (1 - P).range :=
    fun t => BanachAlgebra.RieszSplitting.invariant_range ((Commute.one_right _).sub_right (hcP t))
  have hRV : (restrictSemigroup T P.range hV).operators t₀ = R₁ := by
    ext x; exact (heR₁ x).symm
  have hRW : (restrictSemigroup T (1 - P).range hW).operators t₀ = R₂ := by
    ext x; exact (heR₂ x).symm
  have hnzero : (0 : ℂ) ∉ _root_.spectrum ℂ R₁ := by
    rw [hsR₁]
    intro hz
    have hz' : r ≤ ‖(0 : ℂ)‖ := hz.2
    exact (not_le_of_gt hr) (by simpa using hz')
  have hunit : IsUnit R₁ := by
    have hh : IsUnit (algebraMap ℂ (P.range →L[ℂ] P.range) 0 - R₁) := not_not.mp hnzero
    simpa using hh.neg
  obtain ⟨J, hRJ, hJR⟩ := isUnit_iff_exists.mp hunit
  have hcR : IsCompactOperator R₁ := by
    rw [← hRV]
    exact ((Compactness.compact_iff_isCompactOperator _).mp hKc).restrict' (hV t₀)
  have hcId : IsCompactOperator (id : P.range → P.range) := by
    have hh := hcR.clm_comp J
    have heq : (fun x : P.range => J (R₁ x)) = id := by
      funext x
      exact congrArg (fun H : P.range →L[ℂ] P.range => H x) hJR
    exact heq ▸ hh
  have hfin : FiniteDimensional ℂ P.range := FiniteDimensional.of_isCompactOperator_id hcId
  have hcompl : Submodule.IsTopCompl P.range (1 - P).range := by
    have hker : P.ker = (1 - P).range :=
      LinearMap.IsIdempotentElem.ker_eq_range_one_sub (by
        change P.toLinearMap * P.toLinearMap = P.toLinearMap
        exact congrArg ContinuousLinearMap.toLinearMap hP)
    rw [← hker]
    exact ContinuousLinearMap.IsIdempotentElem.isTopCompl hP
  refine ⟨P, cV, cW, hV, hW, hcompl, hfin, ?_, ?_⟩
  · intro ζ hζ
    have hi := (SpectralInclusion.spectral_inclusion (restrictSemigroup T (1 - P).range hW)
      t₀ ht₀) ⟨ζ, hζ, rfl⟩
    have himem : Complex.exp ((t₀ : ℝ) • ζ) ∈ K₂ := by
      rw [← hsR₂, ← hRW]; exact hi.1
    have hnorm : ‖Complex.exp ((t₀ : ℝ) • ζ)‖ < r :=
      lt_of_le_of_ne himem.2 (hcircle _ himem.1)
    have hexp : Real.exp ((t₀ : ℝ) * ζ.re) < Real.exp ((t₀ : ℝ) * a) := by
      simpa only [Complex.norm_exp, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero] using hnorm
    have hh := Real.exp_lt_exp.mp hexp
    nlinarith
  · intro ζ hζ
    have hi := (SpectralInclusion.spectral_inclusion (restrictSemigroup T P.range hV)
      t₀ ht₀) ⟨ζ, hζ, rfl⟩
    have himem : Complex.exp ((t₀ : ℝ) • ζ) ∈ K₁ := by
      rw [← hsR₁, ← hRV]; exact hi.1
    have hnorm : r < ‖Complex.exp ((t₀ : ℝ) • ζ)‖ :=
      lt_of_le_of_ne himem.2 (hcircle _ himem.1).symm
    have hexp : Real.exp ((t₀ : ℝ) * a) < Real.exp ((t₀ : ℝ) * ζ.re) := by
      simpa only [Complex.norm_exp, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero] using hnorm
    have hh := Real.exp_lt_exp.mp hexp
    nlinarith

end ExpandedFA.Semigroups.EventuallyCompactAsymptotics

namespace ExpandedFA.Semigroups.EventuallyCompactAsymptotics
open EventuallyCompactAsymptoticsSpec EventuallyCompactSpectralMappingSpec
open EventuallyCompactSpectralMapping
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma finite_expansion_of_decomposition (T : C0Semigroup ℂ X) (hT : EventuallyCompact T)
    (a : ℝ) (V W : Submodule ℂ X) [CompleteSpace V] [CompleteSpace W]
    [FiniteDimensional ℂ V]
    (hV : ∀ t : ℝ≥0, ∀ x ∈ V, T.operators t x ∈ V)
    (hW : ∀ t : ℝ≥0, ∀ x ∈ W, T.operators t x ∈ W)
    (P : X →L[ℂ] V) (Q : X →L[ℂ] W)
    (hPQ : ∀ x, (P x : X) + Q x = x ∧
      ∀ v : V, ∀ w : W, (v : X) + w = x → v = P x ∧ w = Q x)
    (hleft : ∀ ζ ∈ spectrum (generator (restrictSemigroup T W hW)), ζ.re < a)
    (hspec : ∀ ζ : ℂ, ζ ∈ matrixSpectrum (finiteGenerator (restrictSemigroup T V hV)) ↔
      ζ ∈ spectrum (generator T) ∧ a < ζ.re)
    (hroot : ∀ ζ ∈ matrixSpectrum (finiteGenerator (restrictSemigroup T V hV)),
      (Module.End.maxGenEigenspace (finiteGenerator (restrictSemigroup T V hV)).toLinearMap ζ).map
        V.subtype = generatorGeneralizedEigenspace (generator T) ζ)
    (hcomm : ∀ ζ : ℂ, ∀ t : ℝ≥0,
      Commute (matrixSpectralProjection (finiteGenerator (restrictSemigroup T V hV)) ζ)
        ((restrictSemigroup T V hV).operators t)) : HasFiniteExpansion T a := by
  classical
  let S := restrictSemigroup T V hV
  let G := finiteGenerator S
  let p := matrixSpectralProjection G
  let n := matrixNilpotent G
  let s := matrixSpectrum G
  let pX := fun ζ => liftEnd V P (p ζ)
  let nX := fun ζ => liftEnd V P (n ζ)
  have hPi (v : V) : P (v : X) = v := ((hPQ v).2 v 0 (by simp)).1.symm
  have hinter := coordinates_intertwine T V W hV hW P Q hPQ
  have hsupport (ζ : ℂ) : nX ζ * pX ζ = nX ζ ∧ pX ζ * nX ζ = nX ζ := by
    constructor
    · change liftEnd V P (n ζ) * liftEnd V P (p ζ) = _
      rw [← liftEnd_mul V P hPi, (matrix_nilpotent_support G ζ).1]
    · change liftEnd V P (p ζ) * liftEnd V P (n ζ) = _
      rw [← liftEnd_mul V P hPi, (matrix_nilpotent_support G ζ).2]
  obtain ⟨C, hC, hbound⟩ := restricted_remainder_bound T hT W hW a hleft Q
  refine ⟨s, pX, nX, fun _ => Module.finrank ℂ V + 1,
    fun t => W.subtypeL.comp (((restrictSemigroup T W hW).operators t).comp Q),
    C, hspec, ?_, ?_, hC, ?_, hbound⟩
  · intro ζ hζ
    refine ⟨Nat.succ_pos _, (generator_spectral_structure T hT).1 ζ ((hspec ζ).mp hζ).1 |>.2.2.1,
      ?_, ?_, (hsupport ζ).1, (hsupport ζ).2, ?_, ?_, ?_, ?_⟩
    · change LinearMap.range (liftEnd V P (p ζ)).toLinearMap = _
      rw [liftEnd_range V P hPi, matrix_projection_range]
      exact hroot ζ hζ
    · change liftEnd V P (p ζ) * liftEnd V P (p ζ) = _
      rw [← liftEnd_mul V P hPi, (matrix_projection_idempotent G ζ).eq]
    · change liftEnd V P (n ζ) ^ (Module.finrank ℂ V + 1) = 0
      rw [← liftEnd_pow_succ V P hPi, matrix_nilpotent_pow, liftEnd_zero]
    · intro x
      exact finite_invariant_subspace_mem_domain T V hV (p ζ (P x))
    · intro x hx
      have hA := finite_invariant_generator_agrees T V hV (p ζ (P x)) hx
      change C0SemigroupSpec.generatorValue T ⟨(p ζ (P x) : X), hx⟩ =
        ζ • pX ζ x + nX ζ (pX ζ x)
      change C0SemigroupSpec.generatorValue T _ = _ at hA
      refine hA.trans ?_
      have hG := congrArg (fun H : V →L[ℂ] V => (H (P x) : X))
        (matrix_generator_on_projection G ζ)
      change (G (p ζ (P x)) : X) = _
      change (G (p ζ (P x)) : X) = ζ • (p ζ (P x) : X) + (n ζ (P x) : X) at hG
      rw [hG]
      congr 1
      exact (congrArg (fun H : X →L[ℂ] X => H x) (hsupport ζ).1).symm
    · intro t
      exact liftEnd_commute V P (T.operators t) (S.operators t) (p ζ)
        (hinter.1 t) (fun _ => rfl) (hcomm ζ t)
  · intro ζ hζ η hη hne
    change liftEnd V P (p ζ) * liftEnd V P (p η) = 0
    rw [← liftEnd_mul V P hPi, matrix_projections_orthogonal G hne, liftEnd_zero]
  · intro t
    have hdecomp : T.operators t = liftEnd V P (S.operators t) +
        W.subtypeL.comp (((restrictSemigroup T W hW).operators t).comp Q) := by
      ext x
      change T.operators t x = T.operators t (P x) + T.operators t (Q x)
      rw [← map_add, (hPQ x).1]
    rw [hdecomp]
    congr 1
    -- The finite sum is transported through the bounded inclusion and coordinate maps.
    rw [finite_semigroup_jordan_expansion S t]
    rw [liftEnd_sum]
    apply Finset.sum_congr rfl
    intro ζ hζ
    rw [liftEnd_smul, liftEnd_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [liftEnd_smul, liftEnd_pow_mul V P hPi]

end ExpandedFA.Semigroups.EventuallyCompactAsymptotics

namespace ExpandedFA.Semigroups.EventuallyCompactAsymptotics
open EventuallyCompactAsymptoticsSpec EventuallyCompactSpectralMappingSpec
open EventuallyCompactSpectralMapping

/-- Every line avoiding the generator spectrum gives the full finite
exponential-polynomial expansion, with its uniform remainder estimate. -/
theorem finite_exponential_polynomial_expansion : FiniteExponentialPolynomialExpansion := by
  intro X _ _ _ T hT a hcut
  obtain ⟨B, cV, cW, hdata⟩ := compact_cut_decomposition T hT a hcut
  letI := cV
  letI := cW
  obtain ⟨hV, hW, hcompl, hfin, hleft, hright⟩ := hdata
  letI := hfin
  let V := B.range
  let W := (1 - B).range
  let P := V.projectionOntoL W hcompl
  let Q := W.projectionOntoL V hcompl.symm
  have hPQ := topCompl_coordinates V W hcompl
  have hr : ∀ ζ ∈ _root_.spectrum ℂ
      (finiteGenerator (restrictSemigroup T V hV)), a < ζ.re := by
    intro ζ hζ
    have hgen : ζ ∈ C0SemigroupSpec.spectrumValue (generator (restrictSemigroup T V hV)) := by
      rwa [finite_generator_spectrum]
    exact hright ζ hgen
  have hspecEq := finite_invariant_spectrum_eq_right T V W hV hW P Q hPQ a hleft hr
  have hspec : ∀ ζ : ℂ, ζ ∈ matrixSpectrum (finiteGenerator (restrictSemigroup T V hV)) ↔
      ζ ∈ spectrum (generator T) ∧ a < ζ.re := by
    intro ζ
    rw [mem_matrixSpectrum, hspecEq]
    rfl
  apply finite_expansion_of_decomposition T hT a V W hV hW P Q hPQ hleft hspec
  · intro ζ hζ
    apply finite_invariant_generalized_eigenspace T V hV ζ
    exact generalized_eigenspace_le_of_spectrum_left T V W hV hW P Q hPQ a hleft ζ
      ((hspec ζ).mp hζ).2
  · exact matrix_projection_semigroup_commutes (restrictSemigroup T V hV)

end ExpandedFA.Semigroups.EventuallyCompactAsymptotics
