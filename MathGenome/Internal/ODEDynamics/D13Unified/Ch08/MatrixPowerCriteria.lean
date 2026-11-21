import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch08.MatrixPowerCriteria
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Matrix.Norms.Operator NNReal ENNReal Topology
open Filter
namespace D13Unified.Ch08.MatrixPowerCriteria

/-- Gelfand's formula identifies the convergence radius of the resolvent series. -/
lemma resolventSeries_radius_inv {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (a : A) :
    let p : FormalMultilinearSeries ℂ ℂ A :=
      fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a ^ n)
    p.radius⁻¹ = spectralRadius ℂ a := by
  let p : FormalMultilinearSeries ℂ ℂ A :=
    fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a ^ n)
  change p.radius⁻¹ = spectralRadius ℂ a
  calc
    p.radius⁻¹ = _ := p.radius_inv_eq_limsup
    _ = spectralRadius ℂ a := by
      have h := (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a).limsup_eq
      convert h using 1
      congr 1
      funext n
      have hn : ‖ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a ^ n)‖₊ = ‖a ^ n‖₊ :=
        Subtype.ext (ContinuousMultilinearMap.norm_mkPiRing _)
      simpa only [p, hn] using
        ENNReal.coe_rpow_of_nonneg ‖a ^ n‖₊ (one_div_nonneg.mpr (Nat.cast_nonneg n))

/-- Any positive rate above the spectral radius bounds all powers. -/
lemma geometric_bound_of_spectralRadius_lt {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] (a : A) (r : ℝ)
    (hr : 0 < r) (hρ : spectralRadius ℂ a < ENNReal.ofReal r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖a ^ n‖ ≤ C * r ^ n := by
  let p : FormalMultilinearSeries ℂ ℂ A :=
    fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a ^ n)
  let s : ℝ≥0 := NNReal.mk r hr.le
  have hs : s ≠ 0 := by exact fun h => hr.ne' (congrArg (fun x : ℝ≥0 => (x : ℝ)) h)
  have hrad : ((s⁻¹ : ℝ≥0) : ℝ≥0∞) < p.radius := by
    rw [ENNReal.coe_inv hs, ENNReal.inv_lt_iff_inv_lt]
    calc
      p.radius⁻¹ = spectralRadius ℂ a := resolventSeries_radius_inv a
      _ < (s : ℝ≥0∞) := by simpa only [ENNReal.ofReal, Real.toNNReal_of_nonneg hr.le, s] using hρ
  obtain ⟨C, hC, hbound⟩ := p.norm_mul_pow_le_of_lt_radius hrad
  refine ⟨C, hC, fun n => ?_⟩
  have hn := hbound n
  simp only [p, ContinuousMultilinearMap.norm_mkPiRing, NNReal.coe_inv] at hn
  change ‖a ^ n‖ * r⁻¹ ^ n ≤ C at hn
  rwa [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (pow_pos hr n)] at hn

theorem prescribedRate : Specs.D13Unified.Ch08.MatrixPowerCriteria.prescribedRate := by
  intro d M r hr hρ _
  exact geometric_bound_of_spectralRadius_lt M r hr hρ

/-- A geometric bound forces every spectral value below the chosen rate. -/
lemma norm_spectralValue_le_rate {d : ℕ} (M : CMatrix d) {r : ℝ}
    (hr : 0 < r) (h : GeometricBound M r) {z : ℂ} (hz : z ∈ spectrum ℂ M) :
    ‖z‖ ≤ r := by
  cases d with
  | zero => simp only [spectrum.of_subsingleton, Set.mem_empty_iff_false] at hz
  | succ d =>
    obtain ⟨C, _, hC⟩ := h
    by_contra! hzr
    have hratio : 1 < ‖z‖ / r := (one_lt_div hr).mpr hzr
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hratio
    have hzn : z ^ n ∈ spectrum ℂ (M ^ n) := by
      rw [spectrum.map_pow]
      exact ⟨z, hz, rfl⟩
    have hnorm : ‖z‖ ^ n ≤ C * r ^ n := by
      simpa only [norm_pow] using (spectrum.norm_le_norm_of_mem hzn).trans (hC n)
    have := (div_le_iff₀ (pow_pos hr n)).mpr hnorm
    rw [← div_pow] at this
    exact (not_lt_of_ge this) hn

theorem geometricCriterion : Specs.D13Unified.Ch08.MatrixPowerCriteria.geometricCriterion := by
  intro d M
  constructor
  · rintro ⟨r, hr, hr1, h⟩ z hz
    exact (norm_spectralValue_le_rate M hr h hz).trans_lt hr1
  · intro h
    have hρ : spectralRadius ℂ M < (1 : ℝ≥0∞) := by
      apply spectralRadius_lt_of_forall_quasispectrum_lt (r := 1)
      intro z hz
      rw [quasispectrum_eq_spectrum_union_zero] at hz
      rcases hz with hz | hz
      · exact_mod_cast h z hz
      · simpa only [Set.mem_singleton_iff.mp hz, nnnorm_zero] using (zero_lt_one : (0 : ℝ≥0) < 1)
    have hfinite : spectralRadius ℂ M ≠ ⊤ := ne_top_of_lt hρ
    have hreal : (spectralRadius ℂ M).toReal < 1 := by
      exact (ENNReal.toReal_lt_toReal hfinite ENNReal.one_ne_top).mpr hρ
    let r : ℝ := ((spectralRadius ℂ M).toReal + 1) / 2
    have hr : 0 < r := by dsimp [r]; positivity
    have hr1 : r < 1 := by dsimp [r]; linarith
    have hρr : spectralRadius ℂ M < ENNReal.ofReal r := by
      apply (ENNReal.lt_ofReal_iff_toReal_lt hfinite).mpr
      dsimp [r]; linarith
    exact ⟨r, hr, hr1, prescribedRate M r hr hρr hr1⟩

@[simp] lemma complexify_pow {d : ℕ} (M : RMatrix d) (n : ℕ) :
    complexify (M ^ n) = complexify M ^ n :=
  Matrix.map_pow M (algebraMap ℝ ℂ) n

@[simp] lemma norm_complexify {d : ℕ} (M : RMatrix d) : ‖complexify M‖ = ‖M‖ := by
  have h : ‖complexify M‖₊ = ‖M‖₊ := by
    simp only [Matrix.linfty_opNNNorm_def, complexify, Matrix.map_apply,
      nnnorm_algebraMap, nnnorm_one, mul_one]
  exact congrArg (fun x : ℝ≥0 => (x : ℝ)) h

@[simp] lemma norm_complexify_pow {d : ℕ} (M : RMatrix d) (n : ℕ) :
    ‖complexify M ^ n‖ = ‖M ^ n‖ := by rw [← complexify_pow, norm_complexify]

lemma geometricBound_complexify_iff {d : ℕ} (M : RMatrix d) (r : ℝ) :
    GeometricBound (complexify M) r ↔ GeometricBound M r := by
  simp only [GeometricBound, norm_complexify_pow]

lemma powerBounded_complexify_iff {d : ℕ} (M : RMatrix d) :
    PowerBounded (complexify M) ↔ PowerBounded M := by
  simp only [PowerBounded, norm_complexify_pow]

theorem realPrescribedRate : Specs.D13Unified.Ch08.MatrixPowerCriteria.realPrescribedRate := by
  intro d M r hr hρ hr1
  exact (geometricBound_complexify_iff M r).mp (prescribedRate _ r hr hρ hr1)

theorem realGeometricCriterion : Specs.D13Unified.Ch08.MatrixPowerCriteria.realGeometricCriterion := by
  intro d M
  simpa only [geometricBound_complexify_iff] using geometricCriterion (complexify M)

lemma complexify_mulVec_re {d : ℕ} (M : RMatrix d) (v : Fin d → ℂ) :
    (fun i => ((complexify M).mulVec v i).re) = M.mulVec (fun i => (v i).re) := by
  ext i
  simp [complexify, Matrix.mulVec, dotProduct, Complex.mul_re]

lemma complexify_mulVec_im {d : ℕ} (M : RMatrix d) (v : Fin d → ℂ) :
    (fun i => ((complexify M).mulVec v i).im) = M.mulVec (fun i => (v i).im) := by
  ext i
  simp [complexify, Matrix.mulVec, dotProduct, Complex.mul_im]

lemma complex_vector_norm_le {d : ℕ} (v : Fin d → ℂ) :
    ‖v‖ ≤ ‖fun i => (v i).re‖ + ‖fun i => (v i).im‖ := by
  apply (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro i
  exact (Complex.norm_le_abs_re_add_abs_im _).trans
    (add_le_add (norm_le_pi_norm (fun i => (v i).re) i)
      (norm_le_pi_norm (fun i => (v i).im) i))

lemma unboundedOrbit_ne_zero {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    (M : Matrix (Fin d) (Fin d) 𝕜) {v : Fin d → 𝕜} (h : UnboundedOrbit M v) : v ≠ 0 := by
  intro hv
  obtain ⟨n, hn⟩ := h 0
  simp only [hv, Matrix.mulVec_zero, norm_zero, lt_self_iff_false] at hn

theorem witnessTransfer : Specs.D13Unified.Ch08.MatrixPowerCriteria.witnessTransfer := by
  intro d M v h
  by_cases hre : UnboundedOrbit M (fun i => (v i).re)
  · exact Or.inl ⟨unboundedOrbit_ne_zero M hre, hre⟩
  · right
    have him : UnboundedOrbit M (fun i => (v i).im) := by
      by_contra him
      simp only [UnboundedOrbit, not_forall, not_exists, not_lt] at hre him
      obtain ⟨C, hC⟩ := hre
      obtain ⟨D, hD⟩ := him
      obtain ⟨n, hn⟩ := h (C + D)
      have hnorm := complex_vector_norm_le ((complexify M ^ n).mulVec v)
      rw [← complexify_pow, complexify_mulVec_re, complexify_mulVec_im] at hnorm
      rw [← complexify_pow] at hn
      exact (not_lt_of_ge (hnorm.trans (add_le_add (hC n) (hD n)))) hn
    exact ⟨unboundedOrbit_ne_zero M him, him⟩

lemma norm_matrix_le_sum_column_norm {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    (M : Matrix (Fin d) (Fin d) 𝕜) :
    ‖M‖ ≤ ∑ j, ‖fun i => M i j‖ := by
  have h : ‖M‖₊ ≤ ∑ j, ‖fun i => M i j‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro i _
    exact Finset.sum_le_sum fun j _ => nnnorm_le_pi_nnnorm (fun i => M i j) i
  simpa only [NNReal.coe_sum, coe_nnnorm] using (NNReal.coe_le_coe.mpr h)

/-- Finite dimensionality gives a single vector with an unbounded orbit,
 without a uniform-boundedness assumption on arbitrary infinite families. -/
lemma exists_unboundedOrbit_of_not_powerBounded {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    (M : Matrix (Fin d) (Fin d) 𝕜) (h : ¬ PowerBounded M) :
    ∃ v : Fin d → 𝕜, v ≠ 0 ∧ UnboundedOrbit M v := by
  classical
  by_contra! hall
  have hb : ∀ j : Fin d, ∃ C : ℝ, ∀ n : ℕ, ‖(M ^ n).mulVec (Pi.single j 1)‖ ≤ C := by
    intro j
    have hne : (Pi.single j 1 : Fin d → 𝕜) ≠ 0 := by
      intro hzero
      have := congrFun hzero j
      simp at this
    have := hall (Pi.single j 1) hne
    simpa only [UnboundedOrbit, not_forall, not_exists, not_lt] using this
  choose C hC using hb
  apply h
  refine ⟨∑ j, C j, fun n => ?_⟩
  apply (norm_matrix_le_sum_column_norm (M ^ n)).trans
  apply Finset.sum_le_sum
  intro j _
  have heq : (M ^ n).mulVec (Pi.single j 1) = (fun i => (M ^ n) i j) := by
    ext i
    simp only [Matrix.mulVec_single_one, Matrix.col_apply]
  have hc := hC j n
  rw [heq] at hc
  exact hc

lemma norm_spectralValue_le_one_of_powerBounded {d : ℕ} (M : CMatrix d)
    (h : PowerBounded M) {z : ℂ} (hz : z ∈ spectrum ℂ M) : ‖z‖ ≤ 1 := by
  cases d with
  | zero => simp only [spectrum.of_subsingleton, Set.mem_empty_iff_false] at hz
  | succ d =>
    obtain ⟨C, hC⟩ := h
    by_contra! hzr
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hzr
    have hzn : z ^ n ∈ spectrum ℂ (M ^ n) := by
      rw [spectrum.map_pow]
      exact ⟨z, hz, rfl⟩
    have hnorm : ‖z‖ ^ n ≤ C := by
      simpa only [norm_pow] using (spectrum.norm_le_norm_of_mem hzn).trans (hC n)
    exact (not_lt_of_ge hnorm) hn

lemma exists_geometric_bound_of_spectrum_lt_one {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] (a : A)
    (h : ∀ z ∈ spectrum ℂ a, ‖z‖ < 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖a ^ n‖ ≤ C * r ^ n := by
  have hρ : spectralRadius ℂ a < (1 : ℝ≥0∞) := by
    apply spectralRadius_lt_of_forall_quasispectrum_lt (r := 1)
    intro z hz
    rw [quasispectrum_eq_spectrum_union_zero] at hz
    rcases hz with hz | hz
    · exact_mod_cast h z hz
    · simpa only [Set.mem_singleton_iff.mp hz, nnnorm_zero] using (zero_lt_one : (0 : ℝ≥0) < 1)
  have hfinite : spectralRadius ℂ a ≠ ⊤ := ne_top_of_lt hρ
  have hreal : (spectralRadius ℂ a).toReal < 1 :=
    (ENNReal.toReal_lt_toReal hfinite ENNReal.one_ne_top).mpr hρ
  let r : ℝ := ((spectralRadius ℂ a).toReal + 1) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hρr : spectralRadius ℂ a < ENNReal.ofReal r := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt hfinite).mpr
    dsimp [r]; linarith
  exact ⟨r, hr, hr1, geometric_bound_of_spectralRadius_lt a r hr hρr⟩

section Endomorphisms
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Vectors whose forward linear orbit is bounded form a subspace. -/
def boundedVectors (T : Module.End ℂ V) : Submodule ℂ V where
  carrier := {v | ∃ C : ℝ, ∀ n : ℕ, ‖(T ^ n) v‖ ≤ C}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro v w ⟨C, hC⟩ ⟨D, hD⟩
    exact ⟨C + D, fun n => by simpa only [map_add] using
      (norm_add_le ((T ^ n) v) ((T ^ n) w)).trans (add_le_add (hC n) (hD n))⟩
  smul_mem' := by
    rintro a v ⟨C, hC⟩
    exact ⟨‖a‖ * C, fun n => by simpa only [map_smul, norm_smul] using
      (mul_le_mul_of_nonneg_left (hC n) (norm_nonneg a))⟩

lemma pow_apply_eigenvector (T : Module.End ℂ V) {z : ℂ} {v : V}
    (hv : T v = z • v) (n : ℕ) : (T ^ n) v = z ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ', Module.End.mul_apply, ih, hv, smul_smul, mul_comm]

lemma eigenvector_mem_boundedVectors (T : Module.End ℂ V) {z : ℂ} (hz : ‖z‖ ≤ 1)
    {v : V} (hv : T v = z • v) : v ∈ boundedVectors T := by
  refine ⟨‖v‖, fun n => ?_⟩
  rw [pow_apply_eigenvector T hv, norm_smul, norm_pow]
  exact mul_le_of_le_one_left (norm_nonneg v) (pow_le_one₀ (norm_nonneg z) hz)

/-- Powers of a length-two Jordan chain. -/
lemma pow_apply_chain (T : Module.End ℂ V) {z : ℂ} {v w : V}
    (hv : T v = z • v) (hw : T w = z • w + v) (n : ℕ) :
    (T ^ (n + 1)) w = z ^ (n + 1) • w + ((n + 1 : ℕ) : ℂ) • (z ^ n • v) := by
  induction n with
  | zero => simpa using hw
  | succ n ih =>
    rw [show n + 1 + 1 = (n + 1) + 1 from rfl, pow_succ', Module.End.mul_apply, ih]
    simp only [map_add, map_smul, hw, hv, smul_add, smul_smul]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    module

/-- A nontrivial unit-circle chain forces an unbounded orbit. -/
lemma chain_not_mem_boundedVectors (T : Module.End ℂ V) {z : ℂ} (hz : ‖z‖ = 1)
    {v w : V} (hv0 : v ≠ 0) (hv : T v = z • v) (hw : T w = z • w + v) :
    w ∉ boundedVectors T := by
  rintro ⟨C, hC⟩
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  obtain ⟨n, hn⟩ := exists_nat_gt ((C + ‖w‖) / ‖v‖)
  have hlower : C + ‖w‖ < ((n + 1 : ℕ) : ℝ) * ‖v‖ := by
    have := (div_lt_iff₀ hpos).mp hn
    push_cast
    nlinarith
  have hp := pow_apply_chain T hv hw n
  have hnorm : ((n + 1 : ℕ) : ℝ) * ‖v‖ ≤ C + ‖w‖ := by
    calc
      ((n + 1 : ℕ) : ℝ) * ‖v‖ = ‖((n + 1 : ℕ) : ℂ) • (z ^ n • v)‖ := by
        rw [norm_smul, norm_smul, Complex.norm_natCast, norm_pow, hz, one_pow, one_mul]
      _ = ‖(T ^ (n + 1)) w - z ^ (n + 1) • w‖ := by rw [hp, add_sub_cancel_left]
      _ ≤ ‖(T ^ (n + 1)) w‖ + ‖z ^ (n + 1) • w‖ := norm_sub_le _ _
      _ ≤ C + ‖w‖ := by simpa [norm_smul, norm_pow, hz] using add_le_add_right (hC (n + 1)) ‖w‖
  exact (not_lt_of_ge hnorm) hlower

lemma genEigenspace_eq_eigenspace_of_bounded (T : Module.End ℂ V)
    (hbound : ∀ v : V, v ∈ boundedVectors T) {z : ℂ} (hz : ‖z‖ = 1) :
    T.genEigenspace z ⊤ = T.eigenspace z := by
  let N : Module.End ℂ V := T - z • 1
  have hstep : ∀ w : V, N (N w) = 0 → N w = 0 := by
    intro w hww
    by_contra hv0
    have hv : T (N w) = z • (N w) := by
      have hh : T (N w) - z • (N w) = 0 := hww
      exact sub_eq_zero.mp hh
    have hw : T w = z • w + N w := by
      dsimp [N]
      abel
    exact chain_not_mem_boundedVectors T hz hv0 hv hw (hbound w)
  have hker : ∀ k : ℕ, ∀ x : V, (N ^ k) x = 0 → N x = 0 := by
    intro k
    induction k with
    | zero => intro x hx; simpa using congrArg N hx
    | succ k ih =>
      intro x hx
      apply hstep
      apply ih (N x)
      simpa only [pow_succ, Module.End.mul_apply] using hx
  apply le_antisymm
  · intro x hx
    obtain ⟨k, hk⟩ := Module.End.mem_genEigenspace_top.mp hx
    apply Module.End.mem_eigenspace_iff.mpr
    exact sub_eq_zero.mp (hker k x hk)
  · exact (T.genEigenspace z).monotone le_top

/-- On a generalized eigenspace, the restricted operator has no other spectral value. -/
lemma spectrum_restrict_genEigenspace_subset [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) (z : ℂ) :
    let P := T.genEigenspace z ⊤
    let hinv : ∀ x ∈ P, T x ∈ P := Module.End.genEigenspace_mem_invtSubmodule T z ⊤
    ∀ μ ∈ spectrum ℂ (T.restrict hinv), μ = z := by
  intro P hinv μ hμ
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ).exists_hasEigenvector
  by_contra hne
  have hveigen : (v : V) ∈ T.eigenspace μ := by
    apply Module.End.mem_eigenspace_iff.mpr
    exact congrArg Subtype.val hv.apply_eq_smul
  have hvzero : (v : V) = 0 :=
    (Submodule.disjoint_def.mp (T.disjoint_genEigenspace (Ne.symm hne) ⊤ 1)) _ v.property hveigen
  exact hv.2 (Subtype.val_injective (by simpa using hvzero))

set_option maxHeartbeats 2000000 in
lemma genEigenspace_le_boundedVectors_of_norm_lt_one [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) {z : ℂ} (hz : ‖z‖ < 1) :
    T.genEigenspace z ⊤ ≤ boundedVectors T := by
  let P := T.genEigenspace z ⊤
  let hinv : ∀ x ∈ P, T x ∈ P := Module.End.genEigenspace_mem_invtSubmodule T z ⊤
  let g : Module.End ℂ P := T.restrict hinv
  let F : P →L[ℂ] P := LinearMap.toContinuousLinearMap g
  have hspec : ∀ μ ∈ spectrum ℂ F, ‖μ‖ < 1 := by
    intro μ hμ
    rw [ContinuousLinearMap.spectrum_eq] at hμ
    have hμz : μ = z := spectrum_restrict_genEigenspace_subset T z μ hμ
    simpa only [hμz] using hz
  obtain ⟨r, hr, hr1, C, hC, hpow⟩ := exists_geometric_bound_of_spectrum_lt_one F hspec
  intro v hv
  let x : P := ⟨v, hv⟩
  have hF (y : P) : (F y : V) = T (y : V) := by
    simp only [F, LinearMap.coe_toContinuousLinearMap', g, LinearMap.restrict_apply]
  have hval (n : ℕ) : ((F ^ n) x : V) = (T ^ n) v := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ' F, mul_apply_eq_comp, hF, ih,
        pow_succ' T, Module.End.mul_apply]

  refine ⟨C * ‖v‖, fun n => ?_⟩
  rw [← hval n]
  change ‖(F ^ n) x‖ ≤ C * ‖x‖
  calc
    ‖(F ^ n) x‖ ≤ ‖F ^ n‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * r ^ n * ‖x‖ := mul_le_mul_of_nonneg_right (hpow n) (norm_nonneg _)
    _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right hC.le (pow_le_one₀ hr.le hr1.le)) (norm_nonneg _)

lemma boundedVectors_eq_top_of_closedSemisimpleSpectrum {d : ℕ} (M : CMatrix d)
    (h : ClosedSemisimpleSpectrum M) : boundedVectors M.toLin' = ⊤ := by
  let T : Module.End ℂ (Fin d → ℂ) := M.toLin'
  have hle : (⨆ z : ℂ, T.maxGenEigenspace z) ≤ boundedVectors T := by
    apply iSup_le
    intro z v hv
    by_cases hv0 : v = 0
    · simpa only [hv0] using (boundedVectors T).zero_mem
    have heigen : T.HasEigenvalue z := by
      obtain ⟨k, hk⟩ := Module.End.mem_genEigenspace_top.mp hv
      apply Module.End.hasEigenvalue_of_hasGenEigenvalue (k := k)
      exact (Submodule.ne_bot_iff _).mpr ⟨v, Module.End.mem_genEigenspace_nat.mpr hk, hv0⟩
    have hspec : z ∈ spectrum ℂ M := by
      have hh := heigen.mem_spectrum
      change z ∈ spectrum ℂ M.toLin' at hh
      rwa [Matrix.spectrum_toLin'] at hh
    rcases (h.1 z hspec).eq_or_lt with hunit | hstrict
    · have hve : v ∈ T.eigenspace z := by rwa [← h.2 z hspec hunit]
      exact eigenvector_mem_boundedVectors T hunit.le (Module.End.mem_eigenspace_iff.mp hve)
    · exact genEigenspace_le_boundedVectors_of_norm_lt_one T hstrict hv
  rw [Module.End.iSup_maxGenEigenspace_eq_top] at hle
  exact top_unique hle


lemma genEigenspace_eq_eigenspace_of_trivial_chains (T : Module.End ℂ V) (z : ℂ)
    (h : ∀ v w : V, T v = z • v → T w = z • w + v → v = 0) :
    T.genEigenspace z ⊤ = T.eigenspace z := by
  let N : Module.End ℂ V := T - z • 1
  have hstep : ∀ w : V, N (N w) = 0 → N w = 0 := by
    intro w hww
    have hv : T (N w) = z • (N w) := sub_eq_zero.mp hww
    have hw : T w = z • w + N w := by dsimp [N]; abel
    exact h (N w) w hv hw
  have hker : ∀ k : ℕ, ∀ x : V, (N ^ k) x = 0 → N x = 0 := by
    intro k
    induction k with
    | zero => intro x hx; simpa using congrArg N hx
    | succ k ih =>
      intro x hx
      apply hstep
      apply ih (N x)
      simpa only [pow_succ, Module.End.mul_apply] using hx
  apply le_antisymm
  · intro x hx
    obtain ⟨k, hk⟩ := Module.End.mem_genEigenspace_top.mp hx
    apply Module.End.mem_eigenspace_iff.mpr
    exact sub_eq_zero.mp (hker k x hk)
  · exact (T.genEigenspace z).monotone le_top

lemma trivial_chains_of_genEigenspace_eq_eigenspace (T : Module.End ℂ V) (z : ℂ)
    (h : T.genEigenspace z ⊤ = T.eigenspace z)
    (v w : V) (hv : T v = z • v) (hw : T w = z • w + v) : v = 0 := by
  have hwgen : w ∈ T.genEigenspace z ⊤ := by
    apply Module.End.mem_genEigenspace_top.mpr
    refine ⟨2, ?_⟩
    simp only [LinearMap.mem_ker, pow_two, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply]
    rw [hw]
    simp only [add_sub_cancel_left, hv, sub_self]
  rw [h, Module.End.mem_eigenspace_iff] at hwgen
  rw [hwgen] at hw
  exact (add_eq_left.mp hw.symm)

end Endomorphisms

lemma powerBounded_apply_mem {d : ℕ} (M : CMatrix d) (h : PowerBounded M)
    (v : Fin d → ℂ) : v ∈ boundedVectors M.toLin' := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C * ‖v‖, fun n => ?_⟩
  have hmatrix := (Matrix.linfty_opNorm_mulVec (M ^ n) v).trans
    (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg v))
  simpa only [← Matrix.toLin'_pow, Matrix.toLin'_apply] using hmatrix

lemma closedSemisimpleSpectrum_of_powerBounded {d : ℕ} (M : CMatrix d)
    (h : PowerBounded M) : ClosedSemisimpleSpectrum M := by
  refine ⟨fun z hz => norm_spectralValue_le_one_of_powerBounded M h hz, ?_⟩
  intro z _ hz
  exact genEigenspace_eq_eigenspace_of_bounded M.toLin' (powerBounded_apply_mem M h) hz

theorem unboundedWitness : Specs.D13Unified.Ch08.MatrixPowerCriteria.unboundedWitness := by
  intro d M h
  apply exists_unboundedOrbit_of_not_powerBounded M
  exact fun hb => h (closedSemisimpleSpectrum_of_powerBounded M hb)

theorem realUnboundedWitness : Specs.D13Unified.Ch08.MatrixPowerCriteria.realUnboundedWitness := by
  intro d M h
  obtain ⟨v, _, hv⟩ := unboundedWitness (complexify M) h
  rcases witnessTransfer M v hv with hre | him
  · exact ⟨_, hre⟩
  · exact ⟨_, him⟩


lemma powerBounded_of_closedSemisimpleSpectrum {d : ℕ} (M : CMatrix d)
    (h : ClosedSemisimpleSpectrum M) : PowerBounded M := by
  by_contra hnot
  obtain ⟨v, _, hv⟩ := exists_unboundedOrbit_of_not_powerBounded M hnot
  have hb : v ∈ boundedVectors M.toLin' := by rw [boundedVectors_eq_top_of_closedSemisimpleSpectrum M h]; trivial
  obtain ⟨C, hC⟩ := hb
  obtain ⟨n, hn⟩ := hv C
  have hnC := hC n
  rw [← Matrix.toLin'_pow] at hnC
  exact (not_lt_of_ge hnC) hn

theorem boundedCriterion : Specs.D13Unified.Ch08.MatrixPowerCriteria.boundedCriterion := by
  intro d M
  exact ⟨closedSemisimpleSpectrum_of_powerBounded M, powerBounded_of_closedSemisimpleSpectrum M⟩

theorem jordanConditionBridge : Specs.D13Unified.Ch08.MatrixPowerCriteria.jordanConditionBridge := by
  intro d M
  constructor
  · rintro ⟨hclosed, hsemi⟩
    refine ⟨hclosed, ?_⟩
    intro z hz v w hv hw
    by_cases hv0 : v = 0
    · exact hv0
    have hspec : z ∈ spectrum ℂ M := by
      have he : Module.End.HasEigenvector M.toLin' z v :=
        ⟨Module.End.mem_eigenspace_iff.mpr hv, hv0⟩
      have hh := (Module.End.hasEigenvalue_of_hasEigenvector he).mem_spectrum
      rwa [Matrix.spectrum_toLin'] at hh
    exact trivial_chains_of_genEigenspace_eq_eigenspace M.toLin' z
      (hsemi z hspec hz) v w hv hw
  · rintro ⟨hclosed, hchain⟩
    refine ⟨hclosed, fun z _ hz => ?_⟩
    exact genEigenspace_eq_eigenspace_of_trivial_chains M.toLin' z (hchain z hz)

theorem jordanBoundedCriterion : Specs.D13Unified.Ch08.MatrixPowerCriteria.jordanBoundedCriterion := by
  intro d M
  exact (boundedCriterion M).trans (jordanConditionBridge M)

theorem realBoundedCriterion : Specs.D13Unified.Ch08.MatrixPowerCriteria.realBoundedCriterion := by
  intro d M
  exact (powerBounded_complexify_iff M).symm.trans (boundedCriterion (complexify M))

theorem eigenvalueBridge : Specs.D13Unified.Ch08.MatrixPowerCriteria.eigenvalueBridge := by
  intro d M z
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin']

theorem jordanUnboundedWitness : Specs.D13Unified.Ch08.MatrixPowerCriteria.jordanUnboundedWitness := by
  intro d M h
  exact unboundedWitness M (fun hb => h ((jordanConditionBridge M).mp hb))

theorem realJordanBoundedCriterion : Specs.D13Unified.Ch08.MatrixPowerCriteria.realJordanBoundedCriterion := by
  intro d M
  exact (realBoundedCriterion M).trans (jordanConditionBridge (complexify M))

theorem realJordanUnboundedWitness : Specs.D13Unified.Ch08.MatrixPowerCriteria.realJordanUnboundedWitness := by
  intro d M h
  exact realUnboundedWitness M (fun hb => h ((jordanConditionBridge (complexify M)).mp hb))

end D13Unified.Ch08.MatrixPowerCriteria
