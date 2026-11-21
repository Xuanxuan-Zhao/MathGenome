import MathGenome.Internal.LinearPDE.P201Specs.Common.SobolevScalars
import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.Holder

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace MeasureTheory
open scoped ENNReal ContDiff
namespace P201.SobolevScalars
open P102.U4

variable {n : ℕ} {K L : Type} [RCLike K] [RCLike L] {Ω : Domain n}

/-- Postcomposition of tests commutes with every coordinate partial. -/
lemma partialWord_postcomp_real (F : K →L[ℝ] L) (φ : Test K Ω) (l : List (Fin n)) :
    partialWord (F ∘ φ) l = F ∘ partialWord φ l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [partialWord, ih]
    ext x
    rw [fderiv_comp x F.differentiableAt
      ((partialWord_contDiff φ.contDiff l).differentiable (by simp)).differentiableAt]
    simp

lemma testPartial_postcomp (F : K →L[ℝ] L) (φ : Test K Ω) (l : List (Fin n)) :
    testPartialWord Ω l (TestFunction.postcompCLM F φ) =
      TestFunction.postcompCLM F (testPartialWord Ω l φ) := by
  ext x
  have h₁ := congrFun (testPartialWord_coe Ω l (TestFunction.postcompCLM F φ)) x
  have h₂ := congrFun (testPartialWord_coe Ω l φ) x
  rw [h₁]
  change partialWord (F ∘ φ) l x = F ((testPartialWord Ω l φ) x)
  rw [h₂]
  exact congrFun (partialWord_postcomp_real F φ l) x

lemma integrable_test_smul (φ : Test ℝ Ω) (v : Lp K Ω 2) :
    Integrable (fun x => φ x • v x) (domainMeasure Ω) := by
  exact (memLp_one_iff_integrable).mp
    ((φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport).smul (Lp.memLp v))

/-- Pairing against a real test, retaining the original scalar field of v. -/
def realPair (φ : Test ℝ Ω) (v : Lp K Ω 2) : K :=
  ∫ x, φ x • v x ∂domainMeasure Ω

lemma realPair_comp (F : K →L[ℝ] L) (φ : Test ℝ Ω) (v : Lp K Ω 2) :
    realPair φ (F.compLp v) = F (realPair φ v) := by
  unfold realPair
  calc
    _ = ∫ x, F (φ x • v x) ∂domainMeasure Ω := by
      apply integral_congr_ae
      filter_upwards [F.coeFn_compLp v] with x hx
      simp only [hx, map_smul]
    _ = _ := F.integral_comp_comm (integrable_test_smul φ v)

/-- A scalar test splits into its two real component tests. -/
lemma pairing_split (φ : Test K Ω) (v : Lp K Ω 2) :
    lpTestPairing Ω 2 φ v =
      realPair (TestFunction.postcompCLM (RCLike.reCLM : K →L[ℝ] ℝ) φ) v +
      (RCLike.I : K) *
        realPair (TestFunction.postcompCLM (RCLike.imCLM : K →L[ℝ] ℝ) φ) v := by
  rw [lpTestPairing_eq_integral]
  let r := TestFunction.postcompCLM (RCLike.reCLM : K →L[ℝ] ℝ) φ
  let i := TestFunction.postcompCLM (RCLike.imCLM : K →L[ℝ] ℝ) φ
  change (∫ x, v x * φ x ∂domainMeasure Ω) = realPair r v + RCLike.I * realPair i v
  unfold realPair
  rw [← integral_const_mul, ← integral_add (integrable_test_smul r v)
    ((integrable_test_smul i v).const_mul _)]
  apply integral_congr_ae
  filter_upwards [] with x
  change v x * φ x = RCLike.re (φ x) • v x + RCLike.I * (RCLike.im (φ x) • v x)
  simp only [RCLike.real_smul_eq_coe_mul]
  calc
    _ = v x * ((RCLike.re (φ x) : K) + RCLike.im (φ x) * RCLike.I) :=
      congrArg (v x * ·) (RCLike.re_add_im (φ x)).symm
    _ = _ := by ring

lemma pairing_ofReal (φ : Test ℝ Ω) (v : Lp K Ω 2) :
    lpTestPairing Ω 2 (TestFunction.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] K) φ) v =
      realPair φ v := by
  rw [lpTestPairing_eq_integral]
  unfold realPair
  apply integral_congr_ae
  filter_upwards [] with x
  change v x * (φ x : K) = φ x • v x
  rw [RCLike.real_smul_eq_coe_mul, mul_comm]

/-- Real tests characterize the same weak derivative graph, for any RCLike field. -/
lemma mem_hilbert_iff_real (k : ℕ)
    (u : PiLp 2 (fun _ : SobolevIndex n k => Lp K Ω 2)) :
    u ∈ P201Specs.hilbertSubmodule K Ω k ↔
      ∀ (α : SobolevIndex n k) (φ : Test ℝ Ω), realPair φ (u α) =
        (-1 : ℝ) ^ α.val.card •
          realPair (testPartialWord Ω (α.val.sort (· ≤ ·)) φ) (u (zeroSobolevIndex n k)) := by
  change P201Specs.hilbertTupleToSum K Ω k u ∈ sobolevSubmodule K Ω k 2 ↔ _
  rw [mem_sobolevSubmodule_iff]
  change (∀ (α : SobolevIndex n k) (φ : Test K Ω), lpTestPairing Ω 2 φ (u α) =
    (-1 : K) ^ α.val.card * lpTestPairing Ω 2
      (testPartialWord Ω (α.val.sort (· ≤ ·)) φ) (u (zeroSobolevIndex n k))) ↔ _
  constructor
  · intro h α φ
    have he := h α (TestFunction.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] K) φ)
    rw [testPartial_postcomp, pairing_ofReal, pairing_ofReal] at he
    simpa only [RCLike.real_smul_eq_coe_mul, RCLike.ofReal_pow,
      RCLike.ofReal_neg, RCLike.ofReal_one] using he
  · intro h α φ
    rw [pairing_split φ, pairing_split (testPartialWord Ω _ φ)]
    rw [← testPartial_postcomp, ← testPartial_postcomp]
    rw [h α, h α]
    simp only [RCLike.real_smul_eq_coe_mul, RCLike.ofReal_pow,
      RCLike.ofReal_neg, RCLike.ofReal_one]
    ring

/-- Coordinatewise application of a real continuous linear map to the finite L² product. -/
def tupleMap (F : K →L[ℝ] L) (Ω : Domain n) (k : ℕ) :
    PiLp 2 (fun _ : SobolevIndex n k => Lp K Ω 2) →L[ℝ]
      PiLp 2 (fun _ : SobolevIndex n k => Lp L Ω 2) :=
  (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.piMap (fun _ => F.compLpL 2 (domainMeasure Ω))).comp
      (PiLp.continuousLinearEquiv 2 ℝ _).toContinuousLinearMap)

@[simp] lemma tupleMap_apply (F : K →L[ℝ] L) (k : ℕ)
    (u : PiLp 2 (fun _ : SobolevIndex n k => Lp K Ω 2)) (α : SobolevIndex n k) :
    tupleMap F Ω k u α = F.compLp (u α) := rfl

lemma tupleMap_mem (F : K →L[ℝ] L) (k : ℕ) (u : H K Ω k) :
    tupleMap F Ω k u.val ∈ P201Specs.hilbertSubmodule L Ω k := by
  rw [mem_hilbert_iff_real]
  intro α φ
  simp only [tupleMap_apply, realPair_comp]
  rw [(mem_hilbert_iff_real k u.val).mp u.property α φ, map_smul]

/-- Real scalar postcomposition on the actual H^k space. -/
def mapH (F : K →L[ℝ] L) (Ω : Domain n) (k : ℕ) : H K Ω k →L[ℝ] H L Ω k where
  toFun u := ⟨tupleMap F Ω k u.val, tupleMap_mem F k u⟩
  map_add' u v := by apply Subtype.ext; exact map_add (tupleMap F Ω k) u.val v.val
  map_smul' c u := by apply Subtype.ext; exact map_smul (tupleMap F Ω k) c u.val
  cont := ((tupleMap F Ω k).continuous.comp continuous_subtype_val).subtype_mk _

@[simp] lemma mapH_coordinate (F : K →L[ℝ] L) (k : ℕ) (u : H K Ω k)
    (α : SobolevIndex n k) :
    sobolevDerivative (hToW L Ω k (mapH F Ω k u)) α =
      F.compLp (sobolevDerivative (hToW K Ω k u) α) := rfl

@[simp] lemma mapH_underlying (F : K →L[ℝ] L) (k : ℕ) (u : H K Ω k) :
    hUnderlying Ω k (mapH F Ω k u) = F.compLp (hUnderlying Ω k u) := rfl

lemma mapH_underlying_ae (F : K →L[ℝ] L) (k : ℕ) (u : H K Ω k) :
    ∀ᵐ x ∂domainMeasure Ω,
      hUnderlying Ω k (mapH F Ω k u) x = F (hUnderlying Ω k u x) :=
  F.coeFn_compLp _

lemma mapH_reconstruction (k : ℕ) (u : H K Ω k) :
    u = mapH (RCLike.ofRealCLM : ℝ →L[ℝ] K) Ω k
        (mapH (RCLike.reCLM : K →L[ℝ] ℝ) Ω k u) +
      (RCLike.I : K) • mapH (RCLike.ofRealCLM : ℝ →L[ℝ] K) Ω k
        (mapH (RCLike.imCLM : K →L[ℝ] ℝ) Ω k u) := by
  apply hilbertUnderlyingInjective Ω k
  rw [map_add, map_smul]
  apply Lp.ext
  let a := mapH (RCLike.reCLM : K →L[ℝ] ℝ) Ω k u
  let b := mapH (RCLike.imCLM : K →L[ℝ] ℝ) Ω k u
  let A := mapH (RCLike.ofRealCLM : ℝ →L[ℝ] K) Ω k a
  let B := mapH (RCLike.ofRealCLM : ℝ →L[ℝ] K) Ω k b
  filter_upwards [Lp.coeFn_add (hUnderlying Ω k A) ((RCLike.I : K) • hUnderlying Ω k B),
    Lp.coeFn_smul (RCLike.I : K) (hUnderlying Ω k B),
    mapH_underlying_ae (RCLike.ofRealCLM : ℝ →L[ℝ] K) k a,
    mapH_underlying_ae (RCLike.ofRealCLM : ℝ →L[ℝ] K) k b,
    mapH_underlying_ae (RCLike.reCLM : K →L[ℝ] ℝ) k u,
    mapH_underlying_ae (RCLike.imCLM : K →L[ℝ] ℝ) k u] with x hadd hsmul hA hB ha hb
  change hUnderlying Ω k u x = _
  rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, hA, hB]
  change hUnderlying Ω k u x = (hUnderlying Ω k a x : K) + RCLike.I * (hUnderlying Ω k b x : K)
  rw [ha, hb, mul_comm RCLike.I]
  exact (RCLike.re_add_im _).symm

/-- Smooth compactly supported classes map to smooth compactly supported classes. -/
lemma mapH_smooth (F : K →L[ℝ] L) (k : ℕ) (u : H K Ω k)
    (hu : hToW K Ω k u ∈ smoothSobolevSubmodule K Ω k 2) :
    hToW L Ω k (mapH F Ω k u) ∈ smoothSobolevSubmodule L Ω k 2 := by
  obtain ⟨φ, hφ⟩ := hu
  refine ⟨TestFunction.postcompCLM F φ, ?_⟩
  change testToDomainLp Ω 2 (TestFunction.postcompCLM F φ) =
    hUnderlying Ω k (mapH F Ω k u)
  apply Lp.ext
  have hφ' : testToDomainLp Ω 2 φ = hUnderlying Ω k u := hφ
  filter_upwards [testToDomainLp_ae Ω 2 (TestFunction.postcompCLM F φ),
    testToDomainLp_ae Ω 2 φ, mapH_underlying_ae F k u] with x h₁ h₂ h₃
  rw [h₁, h₃, ← hφ', h₂]
  rfl

lemma mapH_zero (F : K →L[ℝ] L) (u : H10 K Ω) :
    mapH F Ω 1 u.val ∈ P201Specs.hZeroSubmodule L Ω := by
  let S := (smoothSobolevSubmodule K Ω 1 2).comap (hToW K Ω 1).toLinearMap
  let T := (smoothSobolevSubmodule L Ω 1 2).comap (hToW L Ω 1).toLinearMap
  have hm : MapsTo (mapH F Ω 1) (S : Set _) (T : Set _) := by
    intro v hv
    exact mapH_smooth F 1 v hv
  exact hm.closure (mapH F Ω 1).continuous u.property

/-- Restriction of scalar transport to the actual H¹₀ closure. -/
def mapH10 (F : K →L[ℝ] L) (Ω : Domain n) : H10 K Ω →L[ℝ] H10 L Ω where
  toFun u := ⟨mapH F Ω 1 u.val, mapH_zero F u⟩
  map_add' u v := by apply Subtype.ext; exact map_add (mapH F Ω 1) u.val v.val
  map_smul' c u := by apply Subtype.ext; exact map_smul (mapH F Ω 1) c u.val
  cont := ((mapH F Ω 1).continuous.comp continuous_subtype_val).subtype_mk _

@[simp] lemma mapH10_inclusion (F : K →L[ℝ] L) (u : H10 K Ω) :
    (mapH10 F Ω u).val = mapH F Ω 1 u.val := rfl

/-- Coordinate action also holds for the first derivatives, simultaneously a.e. -/
lemma mapH_first_ae (F : K →L[ℝ] L) (u : H K Ω 1) :
    ∀ᵐ x ∂domainMeasure Ω, ∀ j : Fin n,
      hFirstDerivative (mapH F Ω 1 u) j x = F (hFirstDerivative u j x) :=
  ae_all_iff.mpr fun _ => F.coeFn_compLp _

/-- Identity energy in the manuscript's order of scalar multiplication. -/
lemma energy_identity (u v : H K Ω 1) :
    ellipticEnergyForm Ω (fun _ => 1) u v =
      ∫ x, ∑ j, hFirstDerivative u j x * star (hFirstDerivative v j x) ∂domainMeasure Ω := by
  change (∫ x, ∑ i, ∑ j, (1 : Matrix (Fin n) (Fin n) K) i j *
    hFirstDerivative u j x * star (hFirstDerivative v i x) ∂domainMeasure Ω) = _
  apply integral_congr_ae
  filter_upwards [] with x
  simp [Matrix.one_apply]

/-- Mixed energy uses a real second argument and values in the first field. -/
def mixedEnergy (u : H K Ω 1) (v : H ℝ Ω 1) : K :=
  ∫ x, ∑ j, hFirstDerivative v j x • hFirstDerivative u j x ∂domainMeasure Ω

lemma mixed_integrable (u : H K Ω 1) (v : H ℝ Ω 1) :
    Integrable (fun x => ∑ j, hFirstDerivative v j x • hFirstDerivative u j x)
      (domainMeasure Ω) := by
  apply integrable_finsetSum
  intro j _
  exact memLp_one_iff_integrable.mp ((Lp.memLp (hFirstDerivative v j)).smul
    (Lp.memLp (hFirstDerivative u j)))

lemma mixed_map (F : K →L[ℝ] L) (u : H K Ω 1) (v : H ℝ Ω 1) :
    mixedEnergy (mapH F Ω 1 u) v = F (mixedEnergy u v) := by
  unfold mixedEnergy
  rw [← F.integral_comp_comm (mixed_integrable u v)]
  apply integral_congr_ae
  filter_upwards [mapH_first_ae F u] with x hx
  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl fun j _ => by rw [hx j]

lemma energy_real (u v : H ℝ Ω 1) :
    ellipticEnergyForm Ω (fun _ => 1) u v = mixedEnergy u v := by
  rw [energy_identity (K := ℝ) u v]
  unfold mixedEnergy
  congr 1
  funext x
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

lemma energy_ofReal_right (u : H K Ω 1) (v : H ℝ Ω 1) :
    ellipticEnergyForm Ω (fun _ => 1) u
      (mapH (RCLike.ofRealCLM : ℝ →L[ℝ] K) Ω 1 v) = mixedEnergy u v := by
  rw [energy_identity (K := K) u (mapH (RCLike.ofRealCLM : ℝ →L[ℝ] K) Ω 1 v)]
  unfold mixedEnergy
  apply integral_congr_ae
  filter_upwards [mapH_first_ae (RCLike.ofRealCLM : ℝ →L[ℝ] K) v] with x hx
  apply Finset.sum_congr rfl
  intro j _
  rw [hx j]
  change hFirstDerivative u j x * star (hFirstDerivative v j x : K) =
    hFirstDerivative v j x • hFirstDerivative u j x
  rw [RCLike.star_def, RCLike.conj_ofReal, RCLike.real_smul_eq_coe_mul]
  exact mul_comm _ _

lemma firstDerivative_add (u w : H K Ω 1) (j : Fin n) :
    hFirstDerivative (u + w) j = hFirstDerivative u j + hFirstDerivative w j := rfl

lemma firstDerivative_smul (c : K) (u : H K Ω 1) (j : Fin n) :
    hFirstDerivative (c • u) j = c • hFirstDerivative u j := rfl

lemma mixed_add (u w : H K Ω 1) (v : H ℝ Ω 1) :
    mixedEnergy (u + w) v = mixedEnergy u v + mixedEnergy w v := by
  unfold mixedEnergy
  rw [← integral_add (mixed_integrable u v) (mixed_integrable w v)]
  apply integral_congr_ae
  have ha : ∀ᵐ x ∂domainMeasure Ω, ∀ j : Fin n,
      hFirstDerivative (u + w) j x = hFirstDerivative u j x + hFirstDerivative w j x :=
    ae_all_iff.mpr fun j => Lp.coeFn_add (hFirstDerivative u j) (hFirstDerivative w j)
  filter_upwards [ha] with x hx
  simp only [hx, smul_add, Finset.sum_add_distrib]

lemma mixed_smul (c : K) (u : H K Ω 1) (v : H ℝ Ω 1) :
    mixedEnergy (c • u) v = c • mixedEnergy u v := by
  unfold mixedEnergy
  rw [← integral_smul]
  apply integral_congr_ae
  have ha : ∀ᵐ x ∂domainMeasure Ω, ∀ j : Fin n,
      hFirstDerivative (c • u) j x = c • hFirstDerivative u j x :=
    ae_all_iff.mpr fun j => Lp.coeFn_smul c (hFirstDerivative u j)
  filter_upwards [ha] with x hx
  simp only [hx, smul_comm _ c, Finset.smul_sum]

/-- The imaginary component enters with a minus sign because the test is conjugated. -/
lemma energy_split_right (u v : H K Ω 1) :
    ellipticEnergyForm Ω (fun _ => 1) u v =
      mixedEnergy u (mapH (RCLike.reCLM : K →L[ℝ] ℝ) Ω 1 v) -
      (RCLike.I : K) * mixedEnergy u (mapH (RCLike.imCLM : K →L[ℝ] ℝ) Ω 1 v) := by
  rw [energy_identity (K := K) u v]
  unfold mixedEnergy
  rw [← integral_const_mul, ← integral_sub
    (mixed_integrable u (mapH (RCLike.reCLM : K →L[ℝ] ℝ) Ω 1 v))
    ((mixed_integrable u (mapH (RCLike.imCLM : K →L[ℝ] ℝ) Ω 1 v)).const_mul _)]
  apply integral_congr_ae
  filter_upwards [mapH_first_ae (RCLike.reCLM : K →L[ℝ] ℝ) v,
    mapH_first_ae (RCLike.imCLM : K →L[ℝ] ℝ) v] with x hr hi
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [hr j, hi j]
  change hFirstDerivative u j x * star (hFirstDerivative v j x) =
    RCLike.re (hFirstDerivative v j x) • hFirstDerivative u j x -
      RCLike.I * (RCLike.im (hFirstDerivative v j x) • hFirstDerivative u j x)
  rw [RCLike.star_def, RCLike.conj_eq_re_sub_im]
  simp only [RCLike.real_smul_eq_coe_mul]
  ring

lemma harmonic_synthesis (a b : H ℝ Ω 1)
    (ha : ∀ v : H10 ℝ Ω, ellipticEnergyForm Ω (fun _ => 1) a v.val = 0)
    (hb : ∀ v : H10 ℝ Ω, ellipticEnergyForm Ω (fun _ => 1) b v.val = 0)
    (v : H10 K Ω) :
    ellipticEnergyForm Ω (fun _ => 1)
      (mapH (RCLike.ofRealCLM : ℝ →L[ℝ] K) Ω 1 a +
        (RCLike.I : K) • mapH (RCLike.ofRealCLM : ℝ →L[ℝ] K) Ω 1 b) v.val = 0 := by
  have hm (w : H10 ℝ Ω) :
      mixedEnergy (mapH (RCLike.ofRealCLM : ℝ →L[ℝ] K) Ω 1 a +
        (RCLike.I : K) • mapH (RCLike.ofRealCLM : ℝ →L[ℝ] K) Ω 1 b) w.val = 0 := by
    rw [mixed_add, mixed_smul, mixed_map, mixed_map, ← energy_real a w.val, ← energy_real b w.val,
      ha w, hb w]
    simp only [map_zero, smul_zero, add_zero]
  rw [energy_split_right]
  have hr := hm (mapH10 (RCLike.reCLM : K →L[ℝ] ℝ) Ω v)
  have hi := hm (mapH10 (RCLike.imCLM : K →L[ℝ] ℝ) Ω v)
  simp only [mapH10_inclusion] at hr hi
  rw [hr, hi, mul_zero, sub_zero]

lemma harmonic_detection (u : H K Ω 1)
    (hu : ∀ v : H10 K Ω, ellipticEnergyForm Ω (fun _ => 1) u v.val = 0) :
    (∀ v : H10 ℝ Ω, ellipticEnergyForm Ω (fun _ => 1)
      (mapH (RCLike.reCLM : K →L[ℝ] ℝ) Ω 1 u) v.val = 0) ∧
    (∀ v : H10 ℝ Ω, ellipticEnergyForm Ω (fun _ => 1)
      (mapH (RCLike.imCLM : K →L[ℝ] ℝ) Ω 1 u) v.val = 0) := by
  have hm (v : H10 ℝ Ω) : mixedEnergy u v.val = 0 := by
    rw [← energy_ofReal_right]
    exact hu (mapH10 (RCLike.ofRealCLM : ℝ →L[ℝ] K) Ω v)
  constructor
  · intro v
    rw [energy_real, mixed_map, hm v]
    exact map_zero (RCLike.reCLM : K →L[ℝ] ℝ)
  · intro v
    rw [energy_real, mixed_map, hm v]
    exact map_zero (RCLike.imCLM : K →L[ℝ] ℝ)

/-- Real and imaginary scalar transport, with no additional hypothesis. -/
theorem scalar_transport : P201Specs.SobolevScalars.ScalarTransportStatement := by
  intro n Ω K _
  exact ⟨{
    reMap := mapH (RCLike.reCLM : K →L[ℝ] ℝ) Ω
    imMap := mapH (RCLike.imCLM : K →L[ℝ] ℝ) Ω
    ofRealMap := mapH (RCLike.ofRealCLM : ℝ →L[ℝ] K) Ω
    re_coordinate := fun _ _ _ => rfl
    im_coordinate := fun _ _ _ => rfl
    ofReal_coordinate := fun _ _ _ => rfl
    re_underlying := fun k u => mapH_underlying_ae (RCLike.reCLM : K →L[ℝ] ℝ) k u
    im_underlying := fun k u => mapH_underlying_ae (RCLike.imCLM : K →L[ℝ] ℝ) k u
    ofReal_underlying := fun k u => mapH_underlying_ae (RCLike.ofRealCLM : ℝ →L[ℝ] K) k u
    reconstruction := mapH_reconstruction
    reZero := mapH10 (RCLike.reCLM : K →L[ℝ] ℝ) Ω
    imZero := mapH10 (RCLike.imCLM : K →L[ℝ] ℝ) Ω
    ofRealZero := mapH10 (RCLike.ofRealCLM : ℝ →L[ℝ] K) Ω
    reZero_inclusion := fun _ => rfl
    imZero_inclusion := fun _ => rfl
    ofRealZero_inclusion := fun _ => rfl
    harmonic_synthesis := harmonic_synthesis
    harmonic_detection := harmonic_detection }⟩

end P201.SobolevScalars
