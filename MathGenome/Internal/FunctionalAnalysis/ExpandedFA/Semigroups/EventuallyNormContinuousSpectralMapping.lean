import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.EventuallyNormContinuousSpectralMapping
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.SpectralInclusion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.Characters
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Tactic.Module
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
open scoped NNReal
open Filter Set Topology MeasureTheory

namespace ExpandedFA.Semigroups.EventuallyNormContinuousSpectralMapping

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The inclusion which holds without any norm-continuity assumption. -/
theorem exponential_spectrum_subset (T : C0Semigroup ℂ X) (t : ℝ≥0) (ht : 0 < t) :
    (fun ζ : ℂ => Complex.exp ((t : ℝ) • ζ)) ''
        C0SemigroupSpec.spectrumValue (C0SemigroupSpec.generatorValue T) ⊆
      _root_.spectrum ℂ (T.operators t) \ {0} :=
  SpectralInclusion.spectral_inclusion T t ht

/-- A scalar semigroup nonzero at one positive time is nonzero at every time. -/
theorem scalar_ne_zero (f : ℝ≥0 → ℂ)
    (hadd : ∀ s t, f (s + t) = f s * f t)
    {t : ℝ≥0} (ht : 0 < t) (hf : f t ≠ 0) (s : ℝ≥0) : f s ≠ 0 := by
  have hpow (n : ℕ) : f (n • t) = f t ^ n := by
    induction n with
    | zero =>
      have he := hadd 0 t
      rw [zero_add] at he
      have h0 : f 0 = 1 := (mul_eq_right₀ hf).mp he.symm
      simpa using h0
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  obtain ⟨n, hn⟩ := exists_nat_gt ((s : ℝ) / (t : ℝ))
  have hst : s ≤ n • t := by
    have ht' : (0 : ℝ) < t := ht
    have hn' : (s : ℝ) < (n : ℝ) * t := (div_lt_iff₀ ht').mp hn
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_nsmul, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast] using hn'.le
  intro hs
  have h := hadd s (n • t - s)
  rw [add_tsub_cancel_of_le hst, hs, zero_mul, hpow] at h
  exact (pow_ne_zero n hf) h

/-- Tail continuity of a nonvanishing scalar semigroup propagates to every time.
This does not assert operator-norm continuity of the original semigroup at zero. -/
theorem scalar_continuous (f : ℝ≥0 → ℂ)
    (hadd : ∀ s t, f (s + t) = f s * f t)
    (hnz : ∀ s, f s ≠ 0) {b : ℝ≥0}
    (hc : ContinuousOn f (Ioi b)) : Continuous f := by
  let a : ℝ≥0 := b + 1
  have ha : b < a := by dsimp [a]; exact lt_add_one b
  have heq (s : ℝ≥0) : f s = f (a + s) / f a := by
    rw [hadd, mul_div_cancel_left₀ _ (hnz a)]
  apply continuous_iff_continuousAt.mpr
  intro s
  have has : b < a + s := ha.trans_le (le_add_of_nonneg_right (show 0 ≤ s from zero_le))
  have hca : ContinuousAt f (a + s) := (hc _ has).continuousAt (Ioi_mem_nhds has)
  have hh : ContinuousAt (fun r : ℝ≥0 => f (a + r) / f a) s :=
    (hca.comp (continuous_const.add continuous_id).continuousAt).div_const (f a)
  simpa only [← heq] using hh

/-- The commutant and bicommutant use the original bounded operators. -/
def commutant (T : C0Semigroup ℂ X) : Subalgebra ℂ (X →L[ℂ] X) :=
  Subalgebra.centralizer ℂ (Set.range T.operators)

def semigroupAlgebra (T : C0Semigroup ℂ X) : Subalgebra ℂ (X →L[ℂ] X) :=
  Subalgebra.centralizer ℂ (commutant T : Set (X →L[ℂ] X))

theorem operator_mem_commutant (T : C0Semigroup ℂ X) (t : ℝ≥0) :
    T.operators t ∈ commutant T := by
  intro Q hQ
  obtain ⟨s, rfl⟩ := hQ
  change (T.operators s).comp (T.operators t) =
    (T.operators t).comp (T.operators s)
  rw [← T.add_time, ← T.add_time, add_comm]

theorem operator_mem_semigroupAlgebra (T : C0Semigroup ℂ X) (t : ℝ≥0) :
    T.operators t ∈ semigroupAlgebra T := by
  intro Q hQ
  exact (hQ _ ⟨t, rfl⟩).symm

theorem semigroupAlgebra_le_commutant (T : C0Semigroup ℂ X) :
    semigroupAlgebra T ≤ commutant T := by
  intro Q hQ P hP
  obtain ⟨t, rfl⟩ := hP
  exact hQ _ (operator_mem_commutant T t)

/-- Multiplication is inherited unchanged from bounded endomorphisms. -/
instance semigroupAlgebraNormedCommRing (T : C0Semigroup ℂ X) :
    NormedCommRing (semigroupAlgebra T) :=
  { (semigroupAlgebra T).normedRing with
    mul_comm := by
      intro P Q
      apply Subtype.ext
      exact Q.property _ (semigroupAlgebra_le_commutant T P.property) }

instance semigroupAlgebraCompleteSpace (T : C0Semigroup ℂ X) :
    CompleteSpace (semigroupAlgebra T) :=
  (Set.isClosed_centralizer (commutant T : Set (X →L[ℂ] X))).completeSpace_coe

/-- Any centralizer, hence the bicommutant, is inverse closed. -/
theorem centralizer_isUnit_iff (S : Set (X →L[ℂ] X))
    (Q : Subalgebra.centralizer ℂ S) :
    IsUnit Q ↔ IsUnit (Q : X →L[ℂ] X) := by
  constructor
  · exact fun h => h.map (Subalgebra.val _)
  · rintro ⟨u, hu⟩
    have hui : (↑u⁻¹ : X →L[ℂ] X) ∈ Subalgebra.centralizer ℂ S := by
      intro P hP
      apply Commute.units_inv_right
      change P * (u : X →L[ℂ] X) = (u : X →L[ℂ] X) * P
      rw [hu]
      exact Q.property P hP
    refine ⟨⟨Q, ⟨↑u⁻¹, hui⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      change (Q : X →L[ℂ] X) * ↑u⁻¹ = 1
      rw [← hu]
      exact u.mul_inv
    · apply Subtype.ext
      change ↑u⁻¹ * (Q : X →L[ℂ] X) = 1
      rw [← hu]
      exact u.inv_mul

/-- The bicommutant has precisely the ambient operator spectrum. -/
theorem semigroupAlgebra_spectrum (T : C0Semigroup ℂ X) (Q : semigroupAlgebra T) :
    _root_.spectrum ℂ Q = _root_.spectrum ℂ (Q : X →L[ℂ] X) := by
  ext z
  simp only [_root_.spectrum.mem_iff]
  exact not_congr (centralizer_isUnit_iff _ (algebraMap ℂ _ z - Q))

/-- The time operators in the closed commutative algebra. -/
def algebraOperator (T : C0Semigroup ℂ X) (t : ℝ≥0) : semigroupAlgebra T :=
  ⟨T.operators t, operator_mem_semigroupAlgebra T t⟩

@[simp] theorem algebraOperator_zero (T : C0Semigroup ℂ X) :
    algebraOperator T 0 = 1 := by
  apply Subtype.ext
  exact T.at_zero

@[simp] theorem algebraOperator_add (T : C0Semigroup ℂ X) (s t : ℝ≥0) :
    algebraOperator T (s + t) = algebraOperator T s * algebraOperator T t := by
  apply Subtype.ext
  exact T.add_time s t

/-- Every ambient spectral value is the value of a bounded character on the
bicommutant. The nontrivial-space requirement is needed only for this helper. -/
theorem spectral_character [Nontrivial X] (T : C0Semigroup ℂ X)
    (t : ℝ≥0) {z : ℂ} (hz : z ∈ _root_.spectrum ℂ (T.operators t)) :
    ∃ φ : semigroupAlgebra T →L[ℂ] ℂ,
      φ 1 = 1 ∧ (∀ P Q, φ (P * Q) = φ P * φ Q) ∧ φ (algebraOperator T t) = z := by
  have hz' : z ∈ _root_.spectrum ℂ (algebraOperator T t) := by
    rwa [semigroupAlgebra_spectrum]
  have hs := BanachAlgebra.Characters.spectrum_characters
    (semigroupAlgebra T) (algebraOperator T t)
  change _root_.spectrum ℂ (algebraOperator T t) = _ at hs
  rw [hs] at hz'
  obtain ⟨χ, hχ⟩ := hz'
  obtain ⟨φ, hφ, _, _⟩ := BanachAlgebra.Characters.automatic_boundedness
    (semigroupAlgebra T) χ
  refine ⟨φ, ?_, ?_, ?_⟩
  · change φ.toLinearMap 1 = 1
    rw [hφ]
    exact BanachAlgebra.Characters.character_map_one χ
  · intro P Q
    change φ.toLinearMap (P * Q) = φ.toLinearMap P * φ.toLinearMap Q
    rw [hφ]
    exact χ.property.2 P Q
  · change φ.toLinearMap (algebraOperator T t) = z
    rw [hφ]
    exact hχ

/-- Eventual norm continuity passes to bounded scalar tests on the algebra. -/
theorem character_tail_continuous (T : C0Semigroup ℂ X)
    (φ : semigroupAlgebra T →L[ℂ] ℂ) {b : ℝ≥0}
    (hT : ContinuousOn T.operators (Ioi b)) :
    ContinuousOn (fun t => φ (algebraOperator T t)) (Ioi b) := by
  have hc : ContinuousOn (algebraOperator T) (Ioi b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact ((continuousOn_iff_continuous_domRestrict).mp hT).subtype_mk
      (fun t => operator_mem_semigroupAlgebra T t.val)
  exact φ.continuous.comp_continuousOn hc

/-- Commuting bounded maps preserve the exact derivative domain and derivative. -/
theorem hasGeneratorLimit_commuting (T : C0Semigroup ℂ X)
    (Q : X →L[ℂ] X) (hQ : Q ∈ commutant T) {x y : X}
    (hxy : C0SemigroupSpec.hasGeneratorLimitValue T x y) :
    C0SemigroupSpec.hasGeneratorLimitValue T (Q x) (Q y) := by
  have hlim := (Q.continuous.tendsto y).comp hxy
  apply hlim.congr'
  filter_upwards [] with h
  simp only [Function.comp_apply, C0SemigroupSpec.differenceQuotientValue,
    smul_apply, sub_apply,
    ContinuousLinearMap.id_apply, map_smul, map_sub]
  congr 1
  have hh := congrArg (fun P : X →L[ℂ] X => P x) (hQ _ ⟨h.toNNReal, rfl⟩)
  exact congrArg (fun v : X => v - Q x) hh.symm

/-- All bounded two-sided generator resolvents belong to the bicommutant. -/
theorem resolvent_mem_semigroupAlgebra (T : C0Semigroup ℂ X) (ζ : ℂ)
    (R : Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue T) ζ) :
    R.inverse ∈ semigroupAlgebra T := by
  intro Q hQ
  ext x
  let v : (C0SemigroupSpec.generatorValue T).domain := ⟨R.inverse x, R.mem_domain x⟩
  have hlim := hasGeneratorLimit_commuting T Q hQ (generator_has_limit T v)
  have hv : Q (R.inverse x) ∈ (C0SemigroupSpec.generatorValue T).domain :=
    ⟨Q (C0SemigroupSpec.generatorValue T v), hlim⟩
  have hA : C0SemigroupSpec.generatorValue T ⟨Q (R.inverse x), hv⟩ =
      Q (C0SemigroupSpec.generatorValue T v) :=
    generator_limit_unique T _ _ _ (generator_has_limit T ⟨_, hv⟩) hlim
  have hh := R.left_inverse ⟨Q (R.inverse x), hv⟩
  rw [hA, ← Q.map_smul, ← Q.map_sub, R.right_inverse x] at hh
  exact hh.symm

/-- The ordinary resolvent identity follows just from the two inverse laws,
with the original partial-map domain retained. -/
theorem resolvent_difference (A : Unbounded.Operator ℂ X X) (α ζ : ℂ)
    (R : Unbounded.ResolventInverse A α) (S : Unbounded.ResolventInverse A ζ)
    (x : X) : (α - ζ) • R.inverse (S.inverse x) = S.inverse x - R.inverse x := by
  have h := R.left_inverse ⟨S.inverse x, S.mem_domain x⟩
  have hA : A ⟨S.inverse x, S.mem_domain x⟩ = ζ • S.inverse x - x := by
    have hh := S.right_inverse x
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using (sub_eq_iff_eq_add.mp hh).symm)
  rw [hA] at h
  have he : α • S.inverse x - (ζ • S.inverse x - x) =
      (α - ζ) • S.inverse x + x := by module
  rw [he, map_add, map_smul] at h
  exact eq_sub_of_add_eq h

/-- A generator resolvent at ζ makes I − (α−ζ)R(α,A) invertible. -/
theorem isUnit_resolvent_defect (A : Unbounded.Operator ℂ X X) (α ζ : ℂ)
    (R : Unbounded.ResolventInverse A α) (S : Unbounded.ResolventInverse A ζ) :
    IsUnit (1 - (α - ζ) • R.inverse) := by
  let c := α - ζ
  have hRS (x : X) : c • R.inverse (S.inverse x) = S.inverse x - R.inverse x :=
    resolvent_difference A α ζ R S x
  have hSR (x : X) : c • S.inverse (R.inverse x) = S.inverse x - R.inverse x := by
    have h := resolvent_difference A ζ α S R x
    have hc : ζ - α = -c := by dsimp [c]; ring
    rw [hc, neg_smul] at h
    exact neg_injective (by simpa only [neg_sub] using h)
  refine ⟨⟨1 - c • R.inverse, 1 + c • S.inverse, ?_, ?_⟩, rfl⟩
  · ext x
    simp only [mul_apply_eq_comp, sub_apply,
      add_apply, one_apply_eq_self,
      smul_apply, map_add, map_smul]
    calc
      _ = x + c • S.inverse x - c • R.inverse x -
          c • (c • R.inverse (S.inverse x)) := by module
      _ = x := by rw [hRS]; module
  · ext x
    simp only [mul_apply_eq_comp, sub_apply,
      add_apply, one_apply_eq_self,
      smul_apply, map_sub, map_smul]
    calc
      _ = x - c • R.inverse x + c • S.inverse x -
          c • (c • S.inverse (R.inverse x)) := by module
      _ = x := by rw [hSR]; module

/-- A nonzero character value of a resolvent identifies a genuine generator
spectral value. Inverse closedness of the bicommutant is essential here. -/
theorem generator_spectrum_of_character_resolvent (T : C0Semigroup ℂ X)
    (φ : semigroupAlgebra T →L[ℂ] ℂ) (hφ1 : φ 1 = 1)
    (hφmul : ∀ P Q, φ (P * Q) = φ P * φ Q) (α ζ : ℂ)
    (R : Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue T) α)
    (hφR : φ ⟨R.inverse, resolvent_mem_semigroupAlgebra T α R⟩ = (α - ζ)⁻¹)
    (hne : α - ζ ≠ 0) :
    ζ ∈ C0SemigroupSpec.spectrumValue (C0SemigroupSpec.generatorValue T) := by
  rintro ⟨S⟩
  let r : semigroupAlgebra T := ⟨R.inverse, resolvent_mem_semigroupAlgebra T α R⟩
  let d : semigroupAlgebra T := 1 - (α - ζ) • r
  have hd : IsUnit d := (centralizer_isUnit_iff _ d).mpr
    (isUnit_resolvent_defect _ α ζ R S)
  obtain ⟨u, hu⟩ := hd
  have hzero : φ d = 0 := by
    change φ (1 - (α - ζ) • r) = 0
    rw [map_sub, map_smul, hφ1]
    change 1 - (α - ζ) * φ ⟨R.inverse, resolvent_mem_semigroupAlgebra T α R⟩ = 0
    rw [hφR, mul_inv_cancel₀ hne, sub_self]
  have hh := hφmul d (↑u⁻¹)
  have hdu : d * (↑u⁻¹ : semigroupAlgebra T) = 1 := by rw [← hu]; exact u.mul_inv
  rw [hdu, hφ1, hzero, zero_mul] at hh
  exact one_ne_zero hh

/-! The analytic ingredients are proved below from the accepted generator
and Laplace interfaces. In particular no norm continuity at zero is used. -/

/-- Classification of continuous, nonvanishing scalar semigroups. -/
theorem scalar_exponential (f : ℝ≥0 → ℂ) (hf : Continuous f)
    (h0 : f 0 = 1) (hadd : ∀ s t, f (s + t) = f s * f t)
    (_hnz : ∀ s, f s ≠ 0) :
    ∃ ζ : ℂ, ∀ s : ℝ≥0, f s = Complex.exp ((s : ℝ) • ζ) := by
  let S : C0Semigroup ℂ ℂ :=
    { operators := fun s => f s • ContinuousLinearMap.id ℂ ℂ
      at_zero := by rw [h0]; exact one_smul _ _
      add_time := by
        intro s t
        ext x
        simp only [smul_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.comp_apply, hadd, smul_eq_mul]
        ring
      strong_zero := by
        intro x
        have hc : Continuous (fun r : ℝ => f r.toNNReal * x) :=
          (hf.comp continuous_real_toNNReal).mul continuous_const
        simpa only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
          Real.toNNReal_zero, h0, one_mul] using
          (hc.tendsto 0).mono_left nhdsWithin_le_nhds }
  have h1 : (1 : ℂ) ∈ (generator S).domain := by
    have hh := S.generator_domain_dense (1 : ℂ)
    rwa [(generator S).domain.closed_of_finiteDimensional.closure_eq] at hh
  let v : (generator S).domain := ⟨1, h1⟩
  let ζ := generator S v
  let g : ℝ → ℂ := fun r => Complex.exp (-(r : ℂ) * ζ) * f r.toNNReal
  have hder (r : ℝ) (hr : r ∈ Ici (0 : ℝ)) :
      HasDerivWithinAt g 0 (Ici 0) r := by
    have hdf : HasDerivWithinAt (fun s : ℝ => f s.toNNReal)
        (f r.toNNReal * ζ) (Ici 0) r := by
      simpa only [S, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
        v, mul_one] using S.hasDerivWithinAt_orbit v r hr
    have hde : HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ) * ζ))
        (Complex.exp (-(r : ℂ) * ζ) * -ζ) r := by
      simpa only [Pi.neg_apply, Complex.ofRealCLM_apply, neg_mul,
        Complex.ofReal_one, one_mul] using
        ((Complex.ofRealCLM.hasDerivAt.neg.mul_const ζ).cexp)
    convert hde.hasDerivWithinAt.mul hdf using 1; ring
  have hconst (r : ℝ) (hr : 0 ≤ r) : g r = 1 := by
    have hh : ‖g r - g 0‖ ≤ 0 * ‖r - 0‖ :=
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f' := fun _ : ℝ => (0 : ℂ)) hder (fun _ _ => (norm_zero : ‖(0 : ℂ)‖ = 0).le)
        (convex_Ici (0 : ℝ)) (by simp) hr
    have hg0 : g 0 = 1 := by simp [g, h0]
    simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero, hg0] using hh
  refine ⟨ζ, fun r => ?_⟩
  have hh := hconst r r.coe_nonneg
  change Complex.exp (-((r : ℝ) : ℂ) * ζ) * f (r : ℝ).toNNReal = 1 at hh
  rw [Real.toNNReal_coe] at hh
  apply (mul_left_cancel₀ (Complex.exp_ne_zero (-((r : ℝ) : ℂ) * ζ)))
  rw [hh]
  rw [← Complex.exp_add]
  simp only [Complex.real_smul, neg_mul, neg_add_cancel, Complex.exp_zero]


/-- Evaluate a bounded multiplicative functional on a vector Laplace integral
by first shifting into a norm-continuous tail. The general closed subalgebra
form makes this lemma independent of the parent's bicommutant construction. -/
theorem character_laplace_value (T : C0Semigroup ℂ X)
    (B : Subalgebra ℂ (X →L[ℂ] X)) (hB : IsClosed (B : Set (X →L[ℂ] X)))
    (hmem : ∀ s, T.operators s ∈ B) (φ : B →L[ℂ] ℂ)
    (hmul : ∀ P Q, φ (P * Q) = φ P * φ Q)
    (b : ℝ≥0) (hc : ContinuousOn T.operators (Ioi b))
    (M ω α : ℝ) (ζ : ℂ) (hbound : C0SemigroupSpec.exponentialBoundValue T M ω)
    (hαω : ω < α) (hαζ : ζ.re < α)
    (hexp : ∀ s, φ ⟨T.operators s, hmem s⟩ = Complex.exp ((s : ℝ) • ζ))
    (R : X →L[ℂ] X) (hRmem : R ∈ B)
    (hRform : ∀ x, R x = ∫ s : ℝ in Ioi 0,
      LaplaceResolventSpec.orbit T (α : ℂ) x s) :
    φ ⟨R, hRmem⟩ = ((α : ℂ) - ζ)⁻¹ := by
  let : CompleteSpace B := hB.completeSpace_coe
  let u : ℝ≥0 → B := fun s => ⟨T.operators s, hmem s⟩
  let a : ℝ≥0 := b + 1
  have ha : b < a := by dsimp [a]; exact lt_add_one b
  let F : ℝ → B := fun s => LaplaceResolventSpec.kernel (α : ℂ) s • u (a + s.toNNReal)
  have hFcont : Continuous F := by
    have ht : Continuous (fun s : ℝ => T.operators (a + s.toNNReal)) :=
      hc.comp_continuous (continuous_const.add continuous_real_toNNReal)
        (fun s => ha.trans_le (le_add_of_nonneg_right (show 0 ≤ s.toNNReal from zero_le)))
    have hu : Continuous (fun s : ℝ => u (a + s.toNNReal)) := ht.subtype_mk _
    exact (LaplaceResolvent.continuous_kernel (α : ℂ)).smul hu
  have hFbound {s : ℝ} (hs : 0 ≤ s) :
      ‖F s‖ ≤ (‖T.operators a‖ * M) * Real.exp (-(α - ω) * s) := by
    change ‖LaplaceResolventSpec.kernel (α : ℂ) s • T.operators (a + s.toNNReal)‖ ≤ _
    rw [norm_smul, LaplaceResolvent.norm_kernel]
    change Real.exp (-α * s) * ‖T.operators (a + s.toNNReal)‖ ≤ _
    have hTs : ‖T.operators s.toNNReal‖ ≤ M * Real.exp (ω * s) := by
      simpa only [Real.coe_toNNReal _ hs] using hbound.2 s.toNNReal
    have hp : ‖T.operators (a + s.toNNReal)‖ ≤
        ‖T.operators a‖ * (M * Real.exp (ω * s)) := by
      rw [T.add_time]
      exact (norm_mul_le (T.operators a) (T.operators s.toNNReal)).trans
        (mul_le_mul_of_nonneg_left hTs (norm_nonneg _))
    calc
      _ ≤ Real.exp (-α * s) * (‖T.operators a‖ * (M * Real.exp (ω * s))) :=
        mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
      _ = _ := by
        rw [show -(α - ω) * s = -α * s + ω * s by ring, Real.exp_add]
        ring
  have hFi : IntegrableOn F (Ioi (0 : ℝ)) := by
    have hi : IntegrableOn (fun s : ℝ => Real.exp (-(α - ω) * s)) (Ioi 0) := by
      simpa only [pow_zero, one_mul] using
        LaplaceResolvent.scalar_moment_integrable 0 (sub_pos.mpr hαω)
    apply (hi.const_mul (‖T.operators a‖ * M)).mono' hFcont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hFbound hs.le
  have hInt : (∫ s : ℝ in Ioi 0, F s) = (⟨R, hRmem⟩ : B) * u a := by
    apply Subtype.ext
    ext x
    let E : B →L[ℂ] X :=
      (ContinuousLinearMap.apply ℂ X x).comp B.toSubmodule.subtypeL
    have hi := E.integral_comp_comm hFi
    change (∫ s : ℝ in Ioi 0, (F s : X →L[ℂ] X) x) =
      ((∫ s : ℝ in Ioi 0, F s : B) : X →L[ℂ] X) x at hi
    rw [← hi]
    change (∫ s : ℝ in Ioi 0, (F s : X →L[ℂ] X) x) = R (T.operators a x)
    rw [hRform]
    apply integral_congr_ae
    filter_upwards [] with s
    change LaplaceResolventSpec.kernel (α : ℂ) s • T.operators (a + s.toNNReal) x =
      LaplaceResolventSpec.kernel (α : ℂ) s • T.operators s.toNNReal (T.operators a x)
    rw [add_comm a, T.add_time, ContinuousLinearMap.comp_apply]
  have hre : (ζ - (α : ℂ)).re < 0 := by
    simpa only [Complex.sub_re, Complex.ofReal_re, sub_neg] using hαζ
  have hscalar : (∫ s : ℝ in Ioi 0, Complex.exp ((ζ - (α : ℂ)) * s)) =
      ((α : ℂ) - ζ)⁻¹ := by
    rw [integral_exp_mul_complex_Ioi hre 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [show ζ - (α : ℂ) = -((α : ℂ) - ζ) by ring]
    simp only [div_neg, neg_div, neg_neg, one_div]
  have hpoint {s : ℝ} (hs : 0 ≤ s) :
      φ (F s) = Complex.exp ((ζ - (α : ℂ)) * s) * Complex.exp ((a : ℝ) • ζ) := by
    change φ (LaplaceResolventSpec.kernel (α : ℂ) s • u (a + s.toNNReal)) = _
    rw [map_smul]
    change LaplaceResolventSpec.kernel (α : ℂ) s *
      φ ⟨T.operators (a + s.toNNReal), hmem _⟩ = _
    rw [hexp, LaplaceResolventSpec.kernel, ← Complex.exp_eq_exp_ℂ]
    simp only [NNReal.coe_add, Real.coe_toNNReal _ hs, Complex.real_smul]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hval : φ ⟨R, hRmem⟩ * φ (u a) = ((α : ℂ) - ζ)⁻¹ * φ (u a) := by
    calc
      _ = φ ((⟨R, hRmem⟩ : B) * u a) := (hmul _ _).symm
      _ = φ (∫ s : ℝ in Ioi 0, F s) := congrArg φ hInt.symm
      _ = ∫ s : ℝ in Ioi 0, φ (F s) := (φ.integral_comp_comm hFi).symm
      _ = ∫ s : ℝ in Ioi 0,
          Complex.exp ((ζ - (α : ℂ)) * s) * Complex.exp ((a : ℝ) • ζ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact hpoint hs.le
      _ = ((α : ℂ) - ζ)⁻¹ * Complex.exp ((a : ℝ) • ζ) := by
        rw [integral_mul_const, hscalar]
      _ = _ := by rw [show φ (u a) = Complex.exp ((a : ℝ) • ζ) from hexp a]
  exact mul_right_cancel₀ (by
    rw [show φ (u a) = Complex.exp ((a : ℝ) • ζ) from hexp a]
    exact Complex.exp_ne_zero _) hval

/-- Full spectral mapping under eventual operator-norm continuity. -/
theorem spectral_mapping : EventuallyNormContinuousSpectralMappingSpec.SpectralMapping := by
  intro X _ _ _ T he t ht
  apply Set.Subset.antisymm
  · intro z hz
    rcases subsingleton_or_nontrivial X with hX | hX
    · let := hX
      have hs := _root_.spectrum.of_subsingleton (R := ℂ) (T.operators t)
      rw [hs] at hz
      exact False.elim hz.1
    · let := hX
      obtain ⟨φ, hφ1, hφmul, hφt⟩ := spectral_character T t hz.1
      let f : ℝ≥0 → ℂ := fun s => φ (algebraOperator T s)
      have hf0 : f 0 = 1 := by dsimp [f]; rw [algebraOperator_zero, hφ1]
      have hfadd (s r : ℝ≥0) : f (s + r) = f s * f r := by
        dsimp [f]
        rw [algebraOperator_add, hφmul]
      have hft : f t ≠ 0 := by
        dsimp [f]
        rw [hφt]
        exact hz.2
      have hfnz (s : ℝ≥0) : f s ≠ 0 := scalar_ne_zero f hfadd ht hft s
      obtain ⟨b, hb⟩ := he
      have hfc : Continuous f := scalar_continuous f hfadd hfnz
        (character_tail_continuous T φ hb)
      obtain ⟨ζ, hζ⟩ := scalar_exponential f hfc hf0 hfadd hfnz
      obtain ⟨M, ω, hbound⟩ := T.exponential_bound
      let α : ℝ := max ω ζ.re + 1
      have hαω : ω < α := (le_max_left _ _).trans_lt (lt_add_one _)
      have hαζ : ζ.re < α := (le_max_right _ _).trans_lt (lt_add_one _)
      have hαω' : ω < RCLike.re (α : ℂ) := by simpa using hαω
      obtain ⟨R, hRform⟩ := LaplaceResolvent.laplace_inverse T M ω (α : ℂ) hbound hαω'
      have hRval : φ ⟨R.inverse, resolvent_mem_semigroupAlgebra T (α : ℂ) R⟩ =
          ((α : ℂ) - ζ)⁻¹ :=
        character_laplace_value T (semigroupAlgebra T)
          (Set.isClosed_centralizer _) (operator_mem_semigroupAlgebra T) φ hφmul
          b hb M ω α ζ hbound hαω hαζ hζ R.inverse
          (resolvent_mem_semigroupAlgebra T (α : ℂ) R) hRform
      have hne : (α : ℂ) - ζ ≠ 0 := by
        intro heq
        have hre := congrArg Complex.re (sub_eq_zero.mp heq)
        change α = ζ.re at hre
        exact (ne_of_gt hαζ) hre
      have hζspec := generator_spectrum_of_character_resolvent T φ hφ1 hφmul
        (α : ℂ) ζ R hRval hne
      exact ⟨ζ, hζspec, (hζ t).symm.trans hφt⟩
  · exact exponential_spectrum_subset T t ht

end ExpandedFA.Semigroups.EventuallyNormContinuousSpectralMapping
