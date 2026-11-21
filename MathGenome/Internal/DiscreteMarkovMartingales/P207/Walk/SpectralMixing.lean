import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.SpectralMixing
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Walk.ReversibleDirichletForm
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.TotalVariation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Module

open scoped BigOperators
universe u v
namespace P207.Markov.SpectralMixing
noncomputable section
open WeightedSpace

namespace Interfaces
abbrev meanZero : Spec.meanZeroType.{u} := @SpectralMixing.meanZero
abbrev Invariant : Spec.InvariantType.{u} := @SpectralMixing.Invariant
abbrev restricted : Spec.restrictedType.{u} := @SpectralMixing.restricted
abbrev eigenAbsSet : Spec.eigenAbsSetType.{v} := @SpectralMixing.eigenAbsSet
abbrev radius : Spec.radiusType.{v} := @SpectralMixing.radius
abbrev halfLazy : Spec.halfLazyType.{v} := @SpectralMixing.halfLazy
abbrev density : Spec.densityType.{u} := @SpectralMixing.density
abbrev centeredDensity : Spec.densityType.{u} := @SpectralMixing.centeredDensity
end Interfaces

variable {S : Type u} [Fintype S] (π : ProbabilityLaw S) (hπ : ∀ i, 0 < π i)
  (P : StochasticMatrix S)

@[simp] theorem mem_meanZero (f : WeightedSpace π hπ) :
    f ∈ meanZero π hπ ↔ ∑ i, (π i).toReal * f i = 0 := Iff.rfl

theorem mean_preserved (hb : DetailedBalance P π) (f : WeightedSpace π hπ) :
    (∑ x, (π x).toReal * transitionLinear π hπ P f x) = ∑ x, (π x).toReal * f x := by
  change (∑ x, (π x).toReal * ∑ y, realMatrix P x y * f y) = _
  simp only [Finset.mul_sum, ← mul_assoc]
  exact flow_column π P hb f

theorem invariant (hb : DetailedBalance P π) : Invariant π hπ P := by
  intro f hf
  exact (mean_preserved π hπ P hb f).trans hf

theorem restricted_symmetric (hb : DetailedBalance P π) (h : Invariant π hπ P) :
    (restricted π hπ P h).IsSymmetric := by
  exact (transition_selfAdjoint π hπ P hb).isSymmetric.restrict_invariant h

/-- The mean-zero subspace is nontrivial as soon as there are two states. -/
theorem meanZero_nontrivial [Nontrivial S] : Nontrivial (meanZero π hπ) := by
  classical
  obtain ⟨i, j, hij⟩ := exists_pair_ne S
  let f : WeightedSpace π hπ := fun x =>
    (if x = i then (π i).toReal⁻¹ else 0) - (if x = j then (π j).toReal⁻¹ else 0)
  have hp : ∀ x, (π x).toReal ≠ 0 := fun x => ne_of_gt
    (ENNReal.toReal_pos (ne_of_gt (hπ x)) (π.apply_ne_top x))
  have hf : f ∈ meanZero π hπ := by
    change (∑ x, (π x).toReal * f x) = 0
    simp [f, mul_sub, Finset.sum_sub_distrib, mul_ite, hp]
  have hn : (⟨f, hf⟩ : meanZero π hπ) ≠ 0 := by
    intro he
    have := congrArg (fun g : meanZero π hπ => (g : WeightedSpace π hπ) i) he
    change f i = (0 : ℝ) at this
    simp [f, hij, hp] at this
  exact ⟨⟨⟨f, hf⟩, 0, hn⟩⟩

section Spectral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)

include hT

/-- A real orthonormal eigenbasis of the operator itself. -/
theorem eigenbasis_exists :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
      (lam : Fin (Module.finrank ℝ E) → ℝ),
      (∀ k, Module.End.HasEigenvector T (lam k) (b k)) ∧
      (∀ a, Module.End.HasEigenvalue T a ↔ ∃ k, lam k = a) := by
  refine ⟨hT.eigenvectorBasis rfl, hT.eigenvalues rfl,
    hT.hasEigenvector_eigenvectorBasis rfl, ?_⟩
  intro a
  constructor
  · exact hT.exists_eigenvalues_eq rfl
  · rintro ⟨k, rfl⟩
    exact hT.hasEigenvalue_eigenvalues rfl k

theorem eigenAbsSet_eq_range : eigenAbsSet T = Set.range (fun k => |hT.eigenvalues rfl k|) := by
  ext a
  constructor
  · rintro ⟨lam, hlam, rfl⟩
    obtain ⟨k, hk⟩ := hT.exists_eigenvalues_eq rfl hlam
    exact ⟨k, congrArg abs hk⟩
  · rintro ⟨k, rfl⟩
    exact ⟨_, hT.hasEigenvalue_eigenvalues rfl k, rfl⟩

theorem radius_isGreatest [Nontrivial E] : IsGreatest (eigenAbsSet T) (radius T) := by
  have : Nonempty (Fin (Module.finrank ℝ E)) :=
    Fin.pos_iff_nonempty.mp (Module.finrank_pos (R := ℝ) (M := E))
  rw [radius, eigenAbsSet_eq_range T hT]
  exact (Set.range_nonempty _).isGreatest_csSup (Set.finite_range _)


theorem radius_nonneg [Nontrivial E] : 0 ≤ radius T := by
  obtain ⟨lam, hlam, he⟩ := (radius_isGreatest T hT).1
  exact he ▸ abs_nonneg lam

/-- Diagonalization gives the norm bound with the actual maximum eigenvalue. -/
theorem norm_le_radius [Nontrivial E] (f : E) : ‖T f‖ ≤ radius T * ‖f‖ := by
  let b := hT.eigenvectorBasis rfl
  let lam := hT.eigenvalues rfl
  have hr := radius_nonneg T hT
  have hbound (k) : |lam k| ≤ radius T :=
    (radius_isGreatest T hT).2 ⟨lam k, hT.hasEigenvalue_eigenvalues rfl k, rfl⟩
  have parseval (x : E) : (∑ k, (b.repr x k)^2) = ‖x‖^2 := by
    simpa only [OrthonormalBasis.repr_apply_apply] using b.sum_sq_inner_right x
  have hsq : ‖T f‖^2 ≤ (radius T * ‖f‖)^2 := by
    rw [← parseval (T f)]
    calc
      (∑ k, (b.repr (T f) k)^2) = ∑ k, (lam k)^2 * (b.repr f k)^2 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [show b.repr (T f) k = lam k * b.repr f k from
          hT.eigenvectorBasis_apply_self_apply rfl f k, mul_pow]
      _ ≤ ∑ k, (radius T)^2 * (b.repr f k)^2 := by
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (lam k)) hr).2 (hbound k)
      _ = (radius T * ‖f‖)^2 := by rw [← Finset.mul_sum, parseval, mul_pow]
  nlinarith [norm_nonneg (T f), mul_nonneg hr (norm_nonneg f)]

theorem power_norm_le [Nontrivial E] (n : ℕ) (f : E) :
    ‖(T ^ n) f‖ ≤ radius T ^ n * ‖f‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    calc
      ‖T ((T ^ n) f)‖ ≤ radius T * ‖(T ^ n) f‖ := norm_le_radius T hT _
      _ ≤ radius T * (radius T ^ n * ‖f‖) :=
        mul_le_mul_of_nonneg_left ih (radius_nonneg T hT)
      _ = radius T ^ (n + 1) * ‖f‖ := by rw [pow_succ]; ring

omit [FiniteDimensional ℝ E] hT in
/-- Every eigenvalue of a contraction lies in [-1,1]. -/
theorem abs_eigenvalue_le_one (hc : ∀ f, ‖T f‖ ≤ ‖f‖)
    {a : ℝ} (ha : Module.End.HasEigenvalue T a) : |a| ≤ 1 := by
  obtain ⟨v, hv, hn⟩ := ha.exists_hasEigenvector
  have he := Module.End.mem_eigenspace_iff.mp hv
  have hh := hc v
  rw [he, norm_smul, Real.norm_eq_abs] at hh
  have hp := norm_pos_iff.mpr hn
  nlinarith

omit [FiniteDimensional ℝ E] hT in
/-- Recover the original eigenvalue from a half-lazy eigenvector. -/
theorem halfLazy_eigenvalue {a : ℝ} (ha : Module.End.HasEigenvalue (halfLazy T) a) :
    Module.End.HasEigenvalue T (2 * a - 1) := by
  obtain ⟨v, hv, hn⟩ := ha.exists_hasEigenvector
  have he : (1 / 2 : ℝ) • (v + T v) = a • v := Module.End.mem_eigenspace_iff.mp hv
  apply Module.End.hasEigenvalue_of_hasEigenvector
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hn⟩
  calc
    T v = (2 : ℝ) • ((1 / 2 : ℝ) • (v + T v)) - v := by module
    _ = (2 : ℝ) • (a • v) - v := by rw [he]
    _ = (2 * a - 1) • v := by module

omit [FiniteDimensional ℝ E] hT in
theorem halfLazy_nonneg (hc : ∀ f, ‖T f‖ ≤ ‖f‖)
    {a : ℝ} (ha : Module.End.HasEigenvalue (halfLazy T) a) : 0 ≤ a := by
  have hh := (abs_le.mp (abs_eigenvalue_le_one T hc (halfLazy_eigenvalue T ha))).1
  linarith

theorem halfLazy_radius_lt_one [Nontrivial E] (hc : ∀ f, ‖T f‖ ≤ ‖f‖)
    (hno : ¬Module.End.HasEigenvalue T 1) : radius (halfLazy T) < 1 := by
  have hs : (halfLazy T).IsSymmetric := by
    intro f g
    simp only [halfLazy, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
      real_inner_smul_left, inner_smul_right, inner_add_left, inner_add_right, hT f g]
  obtain ⟨a, ha, he⟩ := (radius_isGreatest (halfLazy T) hs).1
  have hnn := halfLazy_nonneg T hc ha
  have hb := abs_le.mp (abs_eigenvalue_le_one T hc (halfLazy_eigenvalue T ha))
  rw [he, abs_of_nonneg hnn]
  have hne : a ≠ 1 := by
    intro ha1
    apply hno
    simpa only [ha1, mul_one, show (2 : ℝ) - 1 = 1 by norm_num] using halfLazy_eigenvalue T ha
  exact lt_of_le_of_ne (by linarith) hne

end Spectral

/-- Half-lazification of the restriction agrees with the full operator on H₀. -/
theorem halfLazy_restricted_coe (h : Invariant π hπ P) (f : meanZero π hπ) :
    ((halfLazy (restricted π hπ P h) f : meanZero π hπ) : WeightedSpace π hπ) =
      halfLazy (transitionLinear π hπ P) (f : WeightedSpace π hπ) := rfl

/-- Restriction does not change the inherited contraction bound. -/
theorem restricted_norm_le (hb : DetailedBalance P π) (h : Invariant π hπ P)
    (f : meanZero π hπ) : ‖restricted π hπ P h f‖ ≤ ‖f‖ :=
  transition_norm_le π hπ P hb f

theorem restricted_no_one [Nonempty S] (hb : DetailedBalance P π) (hi : Irreducible P)
    (h : Invariant π hπ P) : ¬Module.End.HasEigenvalue (restricted π hπ P h) 1 := by
  rintro he
  obtain ⟨f, hf, hn⟩ := he.exists_hasEigenvector
  have hfix : transitionLinear π hπ P (f : WeightedSpace π hπ) = f := by
    have he := Module.End.mem_eigenspace_iff.mp hf
    rw [one_smul] at he
    have hh := congrArg (fun g : meanZero π hπ => (g : WeightedSpace π hπ)) he
    exact hh
  have hk : (f : WeightedSpace π hπ) ∈ LinearMap.ker
      (LinearMap.id - transitionLinear π hπ P) := by
    change (f : WeightedSpace π hπ) - transitionLinear π hπ P f = 0
    rw [hfix, sub_self]
  obtain ⟨c, hc⟩ := (ker_iff_constant π hπ P hb hi f).mp hk
  have hmass : (∑ x, (π x).toReal) = 1 := by
    simpa only [tsum_fintype] using tsum_mass π
  have hc0 : c = 0 := by
    have hm := f.prop
    change (∑ x, (π x).toReal * (f : WeightedSpace π hπ) x) = 0 at hm
    simpa only [hc, ← Finset.sum_mul, hmass, one_mul] using hm
  apply hn
  apply Subtype.ext
  funext x
  change (f : WeightedSpace π hπ) x = 0
  rw [hc, hc0]

theorem mass_sum (μ : ProbabilityLaw S) : (∑ x, (μ x).toReal) = 1 := by
  simpa only [tsum_fintype] using tsum_mass μ

omit [Fintype S] in
include hπ in
theorem mass_ne_zero (x : S) : (π x).toReal ≠ 0 := ne_of_gt
  (ENNReal.toReal_pos (ne_of_gt (hπ x)) (π.apply_ne_top x))

/-- Detailed balance converts probability row evolution into function evolution. -/
theorem density_succ (hb : DetailedBalance P π) (i : S) (n : ℕ) :
    density π hπ P i (n+1) = transitionLinear π hπ P (density π hπ P i n) := by
  funext x
  change realMatrix (power P (n+1)) i x / (π x).toReal =
    ∑ y, realMatrix P x y * (realMatrix (power P n) i y / (π y).toReal)
  rw [power_succ, realMatrix_comp, Matrix.mul_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y hy
  have hh := congrArg (fun r : ℝ => realMatrix (power P n) i y * r)
    (real_detailedBalance π P hb x y)
  field_simp [mass_ne_zero π hπ x, mass_ne_zero π hπ y]
  nlinarith

theorem centeredDensity_mem (i : S) (n : ℕ) :
    centeredDensity π hπ P i n ∈ meanZero π hπ := by
  change (∑ x, (π x).toReal * ((power P n i x).toReal / (π x).toReal - 1)) = 0
  simp only [mul_sub, mul_one, mul_div_cancel₀ _ (mass_ne_zero π hπ _), Finset.sum_sub_distrib]
  rw [mass_sum, mass_sum, sub_self]

theorem centeredDensity_succ (hb : DetailedBalance P π) (i : S) (n : ℕ) :
    centeredDensity π hπ P i (n+1) =
      transitionLinear π hπ P (centeredDensity π hπ P i n) := by
  funext x
  change density π hπ P i (n+1) x - 1 =
    ∑ y, realMatrix P x y * (density π hπ P i n y - 1)
  rw [density_succ π hπ P hb]
  change (∑ y, realMatrix P x y * density π hπ P i n y) - 1 = _
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, realMatrix_finite_rowsum]

theorem centeredDensity_power (hb : DetailedBalance P π) (i : S) (n : ℕ) :
    (transitionLinear π hπ P ^ n) (centeredDensity π hπ P i 0) =
      centeredDensity π hπ P i n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, centeredDensity_succ π hπ P hb]

theorem restricted_power_coe (h : Invariant π hπ P) (n : ℕ) (f : meanZero π hπ) :
    (((restricted π hπ P h ^ n) f : meanZero π hπ) : WeightedSpace π hπ) =
      (transitionLinear π hπ P ^ n) (f : WeightedSpace π hπ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    exact congrArg (transitionLinear π hπ P) ih

/-- The exact initial chi-square norm, including its sharp point-dependent constant. -/
theorem centeredDensity_zero_norm_sq (i : S) :
    ‖centeredDensity π hπ P i 0‖^2 = (π i).toReal⁻¹ - 1 := by
  classical
  have hz (x : S) : density π hπ P i 0 x =
      if x = i then (π i).toReal⁻¹ else 0 := by
    simp only [density, power_zero, identity_apply]
    split_ifs with hx
    · subst x; simp
    · simp
  have he (x : S) :
      (π x).toReal * (density π hπ P i 0 x - 1) * (density π hπ P i 0 x - 1) =
        (if x = i then (π i).toReal * (((π i).toReal⁻¹ - 1)^2 - 1) else 0) +
          (π x).toReal := by
    rw [hz]
    split_ifs with hx
    · subst x; ring
    · ring
  rw [weighted_norm_sq]
  change (∑ x, (π x).toReal * (density π hπ P i 0 x - 1) *
    (density π hπ P i 0 x - 1)) = _
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, mass_sum]
  field_simp [mass_ne_zero π hπ i]
  ring

theorem centeredDensity_zero_norm (i : S) :
    ‖centeredDensity π hπ P i 0‖ = Real.sqrt ((π i).toReal⁻¹ - 1) := by
  rw [← centeredDensity_zero_norm_sq π hπ P i, Real.sqrt_sq (norm_nonneg _)]

/-- Cauchy--Schwarz with the constant function one for the probability weight. -/
theorem weighted_abs_sum_le (f : WeightedSpace π hπ) :
    (∑ x, (π x).toReal * |f x|) ≤ ‖f‖ := by
  let one : WeightedSpace π hπ := fun _ => 1
  let af : WeightedSpace π hπ := fun x => |f x|
  have h1 : ‖one‖ = 1 := by
    have he := weighted_norm_sq π hπ one
    change ‖one‖ ^ 2 = ∑ x, (π x).toReal * 1 * 1 at he
    simp only [mul_one, mass_sum] at he
    nlinarith [norm_nonneg one]
  have ha : ‖af‖ = ‖f‖ := by
    have he : ‖af‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [weighted_norm_sq, weighted_norm_sq]
      apply Finset.sum_congr rfl
      intro x hx
      change (π x).toReal * |f x| * |f x| = (π x).toReal * f x * f x
      simp only [mul_assoc, ← sq, sq_abs]
    nlinarith [norm_nonneg af, norm_nonneg f]
  have hc := real_inner_le_norm one af
  rw [h1, ha, one_mul] at hc
  change (∑ x, (π x).toReal * one x * af x) ≤ ‖f‖ at hc
  simpa only [one, af, mul_one] using hc

/-- The event-normalized total variation distance is at most half the density norm. -/
theorem tv_le_density_norm (i : S) (n : ℕ) :
    totalVariation (power P n i) π ≤ (1 / 2 : ℝ) * ‖centeredDensity π hπ P i n‖ := by
  rw [totalVariation_eq_half_tsum, tsum_fintype]
  have he (x : S) : |(power P n i x).toReal - (π x).toReal| =
      (π x).toReal * |centeredDensity π hπ P i n x| := by
    have hh : (power P n i x).toReal - (π x).toReal =
        (π x).toReal * centeredDensity π hπ P i n x := by
      change (power P n i x).toReal - (π x).toReal =
        (π x).toReal * ((power P n i x).toReal / (π x).toReal - 1)
      field_simp [mass_ne_zero π hπ x]
    rw [hh, abs_mul, abs_of_nonneg (ENNReal.toReal_nonneg (a := π x))]
  simp_rw [he]
  exact mul_le_mul_of_nonneg_left (weighted_abs_sum_le π hπ _) (by norm_num)

/-- The sharp TV estimate for the spectral radius of the genuine restriction. -/
theorem tv_bound [Nontrivial S] (hb : DetailedBalance P π) (h : Invariant π hπ P)
    (i : S) (n : ℕ) :
    totalVariation (power P n i) π ≤
      (1 / 2 : ℝ) * Real.sqrt ((π i).toReal⁻¹ - 1) * radius (restricted π hπ P h)^n := by
  have hH0 : Nontrivial (meanZero π hπ) := meanZero_nontrivial π hπ
  let f : meanZero π hπ := ⟨centeredDensity π hπ P i 0, centeredDensity_mem π hπ P i 0⟩
  have hc : (((restricted π hπ P h ^ n) f : meanZero π hπ) : WeightedSpace π hπ) =
      centeredDensity π hπ P i n := by
    rw [restricted_power_coe]
    exact centeredDensity_power π hπ P hb i n
  have hn := power_norm_le (restricted π hπ P h) (restricted_symmetric π hπ P hb h) n f
  change ‖(((restricted π hπ P h ^ n) f : meanZero π hπ) : WeightedSpace π hπ)‖ ≤
    radius (restricted π hπ P h)^n * ‖centeredDensity π hπ P i 0‖ at hn
  rw [hc, centeredDensity_zero_norm] at hn
  calc
    totalVariation (power P n i) π ≤ (1 / 2 : ℝ) * ‖centeredDensity π hπ P i n‖ :=
      tv_le_density_norm π hπ P i n
    _ ≤ (1 / 2 : ℝ) * (radius (restricted π hπ P h)^n *
        Real.sqrt ((π i).toReal⁻¹ - 1)) := mul_le_mul_of_nonneg_left hn (by norm_num)
    _ = _ := by ring

/-- Paper W25, spectral TV mixing and the strict spectral bound after half-lazification. -/
theorem spectral_tv : Spec.spectral_tv.{u} := by
  intro S _ _ _ _ P π hi hr
  let hπ := stationary_positive P π hi hr.1
  have hb := (reversible_iff_detailedBalance P π).mp hr
  let h := invariant π hπ P hb
  let T := restricted π hπ P h
  have hH0 : Nontrivial (meanZero π hπ) := meanZero_nontrivial π hπ
  have hs : T.IsSymmetric := restricted_symmetric π hπ P hb h
  have hl : (halfLazy T).IsSymmetric := by
    intro f g
    simp only [halfLazy, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
      real_inner_smul_left, inner_smul_right, inner_add_left, inner_add_right, hs f g]
  exact ⟨hπ, h, eigenbasis_exists T hs, radius_isGreatest T hs,
    tv_bound π hπ P hb h,
    fun _ ha => halfLazy_nonneg (transitionLinear π hπ P)
      (transition_norm_le π hπ P hb) ha,
    radius_isGreatest (halfLazy T) hl,
    halfLazy_radius_lt_one T hs (restricted_norm_le π hπ P hb h)
      (restricted_no_one π hπ P hb hi h)⟩

end
end P207.Markov.SpectralMixing
