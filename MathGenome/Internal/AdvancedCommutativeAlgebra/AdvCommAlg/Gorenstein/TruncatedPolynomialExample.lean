import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.SocleCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.TruncatedPolynomialExample
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section
universe u
namespace AdvCommAlg.Gorenstein.TruncatedPolynomial
open Polynomial
variable (k : Type u) [Field k] (n : ℕ)

lemma t_pow : t k n ^ n = 0 := by
  rw [t, AdjoinRoot.root, ← map_pow, AdjoinRoot.mk_self]

lemma artinian : IsArtinianRing (Ring k n) := by
  let : Module.Finite k (Ring k n) := (monic_X_pow n).finite_adjoinRoot
  exact IsArtinianRing.of_finite k (Ring k n)

def augmentation (hn : 1 ≤ n) : Ring k n →ₐ[k] k :=
  AdjoinRoot.liftAlgHom _ (AlgHom.id k k) 0 (by simp [Nat.ne_of_gt hn])

@[simp] lemma augmentation_t (hn : 1 ≤ n) : augmentation k n hn (t k n) = 0 := by
  simp [augmentation, t]

@[simp] lemma augmentation_mk (hn : 1 ≤ n) (p : k[X]) :
    augmentation k n hn (AdjoinRoot.mk _ p) = p.coeff 0 := by
  simp [augmentation]

lemma augmentation_surjective (hn : 1 ≤ n) : Function.Surjective (augmentation k n hn) := by
  intro c
  exact ⟨algebraMap k (Ring k n) c, (augmentation k n hn).commutes c⟩

lemma augmentation_ker (hn : 1 ≤ n) :
    RingHom.ker (augmentation k n hn).toRingHom = Ideal.span {t k n} := by
  ext z
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    constructor
    · intro hp
      have hp0 : p.coeff 0 = 0 := by simpa using hp
      obtain ⟨q, hq⟩ := X_dvd_iff.mpr hp0
      rw [hq, map_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
    · intro hz
      have hle : Ideal.span {t k n} ≤ RingHom.ker (augmentation k n hn).toRingHom := by
        apply Ideal.span_le.mpr
        intro a ha
        simp only [Set.mem_singleton_iff] at ha
        subst a
        exact augmentation_t k n hn
      exact hle hz

lemma isLocal (hn : 1 ≤ n) : IsLocalRing (Ring k n) := by
  have hmax : (Ideal.span {t k n} : Ideal (Ring k n)).IsMaximal := by
    rw [← augmentation_ker k n hn]
    exact RingHom.ker_isMaximal_of_surjective _ (augmentation_surjective k n hn)
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨Ideal.span {t k n}, hmax, ?_⟩
  intro J hJ
  have ht : t k n ∈ J := by
    apply hJ.isPrime.mem_of_pow_mem n
    rw [t_pow]
    exact J.zero_mem
  exact (hmax.eq_of_le hJ.ne_top (Ideal.span_le.mpr (by simpa))).symm

lemma maximalIdeal_eq (hn : 1 ≤ n) [IsLocalRing (Ring k n)] :
    IsLocalRing.maximalIdeal (Ring k n) = Ideal.span {t k n} := by
  rw [← augmentation_ker k n hn]
  exact (IsLocalRing.ker_eq_maximalIdeal _ (augmentation_surjective k n hn)).symm

/-- Evaluation at zero identifies the residue field with the coefficient field. -/
def residueEquiv (hn : 1 ≤ n) [IsLocalRing (Ring k n)] :
    IsLocalRing.ResidueField (Ring k n) ≃ₐ[k] k :=
  (Ideal.quotientEquivAlgOfEq k
    ((maximalIdeal_eq k n hn).trans (augmentation_ker k n hn).symm)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (augmentation_surjective k n hn))

lemma top_power_ne_zero (hn : 1 ≤ n) : t k n ^ (n - 1) ≠ 0 := by
  change AdjoinRoot.root ((X : k[X]) ^ n) ^ (n - 1) ≠ 0
  rw [AdjoinRoot.root, ← map_pow]
  apply AdjoinRoot.mk_ne_zero_of_degree_lt (monic_X_pow n)
    (pow_ne_zero _ X_ne_zero)
  simp only [degree_X_pow, Nat.cast_lt]
  omega

/-- Multiplication on the last power factors through the constant coefficient. -/
lemma mul_top_power (hn : 1 ≤ n) (z : Ring k n) :
    z * t k n ^ (n - 1) = augmentation k n hn z • t k n ^ (n - 1) := by
  have hz : z - algebraMap k (Ring k n) (augmentation k n hn z) ∈
      RingHom.ker (augmentation k n hn).toRingHom := by
    change augmentation k n hn (z - algebraMap k (Ring k n) (augmentation k n hn z)) = 0
    rw [map_sub, (augmentation k n hn).commutes]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  rw [augmentation_ker k n hn] at hz
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hz
  have ht : t k n * t k n ^ (n - 1) = 0 := by
    rw [← pow_succ', Nat.sub_add_cancel hn, t_pow]
  have hzero : (z - algebraMap k (Ring k n) (augmentation k n hn z)) *
      t k n ^ (n - 1) = 0 := by
    rw [hr, mul_right_comm, ht, zero_mul]
  rw [sub_mul, sub_eq_zero, ← Algebra.smul_def] at hzero
  exact hzero

lemma mem_socle_iff_mul (hn : 1 ≤ n) [IsLocalRing (Ring k n)] (z : Ring k n) :
    z ∈ socle (Ring k n) (Ring k n) ↔ t k n * z = 0 := by
  rw [mem_socle_iff]
  constructor
  · intro h
    apply h
    rw [maximalIdeal_eq k n hn]
    exact Ideal.subset_span (by simp)
  · intro hz a ha
    rw [maximalIdeal_eq k n hn] at ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp ha
    change (t k n * r) * z = 0
    rw [mul_right_comm, hz, zero_mul]

lemma socle_description (hn : 1 ≤ n) [IsLocalRing (Ring k n)] (z : Ring k n) :
    z ∈ socle (Ring k n) (Ring k n) ↔ ∃ c : k, z = c • t k n ^ (n - 1) := by
  rw [mem_socle_iff_mul k n hn]
  constructor
  · induction z using AdjoinRoot.induction_on with
    | ih p =>
      intro hz
      have hd : (X : k[X]) ^ n ∣ X * p := by
        apply AdjoinRoot.mk_eq_zero.mp
        simpa only [map_mul, t, AdjoinRoot.root] using hz
      have hn' : n = (n - 1) + 1 := by omega
      rw [hn', pow_succ', mul_dvd_mul_iff_left X_ne_zero] at hd
      obtain ⟨q, rfl⟩ := hd
      refine ⟨augmentation k n hn (AdjoinRoot.mk _ q), ?_⟩
      rw [map_mul, map_pow]
      change t k n ^ (n - 1) * AdjoinRoot.mk _ q = _
      rw [mul_comm, mul_top_power k n hn]
  · rintro ⟨c, rfl⟩
    rw [mul_smul_comm, ← pow_succ', Nat.sub_add_cancel hn, t_pow, smul_zero]

lemma socle_finrank (hn : 1 ≤ n) [IsLocalRing (Ring k n)] :
    Module.finrank (IsLocalRing.ResidueField (Ring k n))
      (socle (Ring k n) (Ring k n)) = 1 := by
  let v : socle (Ring k n) (Ring k n) :=
    ⟨t k n ^ (n - 1), (socle_description k n hn _).mpr ⟨1, by simp⟩⟩
  have hv : v ≠ 0 := by
    intro h
    exact top_power_ne_zero k n hn (congrArg Subtype.val h)
  apply (finrank_eq_one_iff_of_nonzero' v hv).mpr
  intro w
  obtain ⟨c, hc⟩ := (socle_description k n hn w.val).mp w.property
  refine ⟨IsLocalRing.residue (Ring k n) (algebraMap k (Ring k n) c), ?_⟩
  change (algebraMap (Ring k n) (IsLocalRing.ResidueField (Ring k n))
    (algebraMap k (Ring k n) c)) • v = w
  rw [algebraMap_smul]
  apply Subtype.ext
  change (algebraMap k (Ring k n) c) * t k n ^ (n - 1) = w.val
  rw [← Algebra.smul_def, ← hc]

lemma localGorenstein (hn : 1 ≤ n) [IsLocalRing (Ring k n)] :
    LocalGorenstein (Ring k n) := by
  let : IsArtinianRing (Ring k n) := artinian k n
  have : Module.Injective (Ring k n) (Ring k n) :=
    selfInjective_of_socle_finrank_one (socle_finrank k n hn)
  apply (finiteInjectiveDimension_iff_exists_bound (Ring k n) (Ring k n)).mpr
  have := Module.injective_object_of_injective_module (Ring k n) (Ring k n)
  exact ⟨0, inferInstance⟩

/-- The truncated polynomial ring is Artinian local with residue field k,
nonzero one-dimensional socle generated by t^(n-1), and is Gorenstein. -/
theorem truncatedPolynomial_example : Specs.exampleType.{u} := by
  intro k _ n hn
  refine ⟨artinian k n, isLocal k n hn, ?_⟩
  let := isLocal k n hn
  refine ⟨inferInstance, ⟨residueEquiv k n hn⟩, top_power_ne_zero k n hn,
    socle_description k n hn, socle_finrank k n hn, localGorenstein k n hn⟩

end AdvCommAlg.Gorenstein.TruncatedPolynomial
