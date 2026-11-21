import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.SupNorm
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.SupSpace
import Mathlib.Topology.Order.Compact

/-!
K03.16.sup_space: the canonical scalar continuous-function spaces on compact
real sets. All algebraic and metric structures are Mathlib's existing ones.
Maximum attainment uses the extreme-value theorem for the continuous modulus;
the canonical norm bounds identify this maximum with the norm. The strict
norm criterion identifies convergence with the upstream uniform convergence.
-/
namespace SingleVariableAnalysis

open scoped Topology

theorem supSpace_compact_subtype {K : Set ℝ} (hK : IsCompact K) : CompactSpace K :=
  isCompact_iff_compactSpace.mp hK

/-- A continuous modulus on a nonempty compact real set attains the canonical norm. -/
theorem supSpace_norm_attains {K : Set ℝ} [CompactSpace K]
    {E : Type*} [NormedAddCommGroup E] (hK : K.Nonempty) (f : C(K, E)) :
    ∃ x : K, ‖f‖ = ‖f x‖ ∧ ∀ y : K, ‖f y‖ ≤ ‖f x‖ := by
  let : Nonempty K := hK.to_subtype
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    f.continuous.norm.continuousOn
  have hmax : ∀ y : K, ‖f y‖ ≤ ‖f x‖ := fun y => hx (Set.mem_univ y)
  exact ⟨x, le_antisymm ((f.norm_le (norm_nonneg _)).mpr hmax)
    (f.norm_coe_le_norm x), hmax⟩

/-- The canonical metric on compact-domain continuous maps is the uniform metric. -/
theorem supSpace_tendsto_iff_uniform {K : Set ℝ} [CompactSpace K]
    {E : Type*} [NormedAddCommGroup E] (F : ℕ → C(K, E)) (f : C(K, E)) :
    Filter.Tendsto F Filter.atTop (𝓝 f) ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x : K, ‖F n x - f x‖ < ε := by
  simp only [Metric.tendsto_atTop, dist_eq_norm]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun n hn x => ((F n - f).norm_coe_le_norm x).trans_lt (hN n hn)⟩
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun n hn => ((F n - f).norm_lt_iff hε).mpr (hN n hn)⟩

/-- The manuscript's C(K,ℝ) is the existing continuous-map type. -/
abbrev RealContinuousSpace (K : Set ℝ) := C(K, ℝ)

theorem realSupSpace_representation :
    ∀ (K : Set ℝ),
    (∀ f : C(K, ℝ), Continuous (f : K → ℝ)) ∧
    (∀ u : K → ℝ, Continuous u → ∃! f : C(K, ℝ), (f : K → ℝ) = u) := by
  intro K
  refine ⟨fun f => f.continuous, ?_⟩
  intro u hu
  refine ⟨⟨u, hu⟩, rfl, ?_⟩
  intro g hg
  exact ContinuousMap.coe_injective hg

theorem realSupSpace_pointwise :
    ∀ (K : Set ℝ) (f g : C(K, ℝ)) (c : ℝ) (x : K),
    (f + g) x = f x + g x ∧ (c • f) x = c * f x ∧
    (-f) x = -f x ∧ (f - g) x = f x - g x ∧ (0 : C(K, ℝ)) x = 0 := by
  intro K f g c x
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem realSupSpace_norm_maximum :
    ∀ (K : Set ℝ) [CompactSpace K], K.Nonempty →
    ∀ f : C(K, ℝ), ∃ x : K, ‖f‖ = |f x| ∧
      ∀ y : K, |f y| ≤ |f x| := by
  intro K _ hK f
  simpa only [Real.norm_eq_abs] using
    supSpace_norm_attains hK f

theorem realSupSpace_norm_laws :
    ∀ (K : Set ℝ) [CompactSpace K] (f g : C(K, ℝ)) (c : ℝ),
    0 ≤ ‖f‖ ∧ (‖f‖ = 0 ↔ f = 0) ∧ ‖f + g‖ ≤ ‖f‖ + ‖g‖ ∧
    ‖c • f‖ = |c| * ‖f‖ ∧ ‖-f‖ = ‖f‖ ∧ ‖(0 : C(K, ℝ))‖ = 0 := by
  intro K _ f g c
  refine ⟨norm_nonneg _, norm_eq_zero, norm_add_le _ _, ?_, norm_neg _, norm_zero⟩
  simpa only [Real.norm_eq_abs] using norm_smul c f

theorem realSupSpace_distance :
    ∀ (K : Set ℝ) [CompactSpace K] (f g : C(K, ℝ)),
    dist f g = ‖f - g‖ := by
  intro K _ f g
  exact dist_eq_norm f g

theorem realSupSpace_norm_converges_iff_uniform :
    ∀ (K : Set ℝ) [CompactSpace K] (F : ℕ → C(K, ℝ)) (f : C(K, ℝ)),
    Filter.Tendsto (fun n => ‖F n - f‖) Filter.atTop (𝓝 0) ↔
      RealUniformConverges (fun n x => F n x) f := by
  intro K _ F f
  rw [← tendsto_iff_norm_sub_tendsto_zero]
  simpa only [RealUniformConverges, Real.norm_eq_abs] using
    supSpace_tendsto_iff_uniform F f

theorem realSupSpace_tendsto_iff_uniform :
    ∀ (K : Set ℝ) [CompactSpace K] (F : ℕ → C(K, ℝ)) (f : C(K, ℝ)),
    Filter.Tendsto F Filter.atTop (𝓝 f) ↔
      RealUniformConverges (fun n x => F n x) f := by
  intro K _ F f
  simpa only [RealUniformConverges, Real.norm_eq_abs] using
    supSpace_tendsto_iff_uniform F f

theorem realSupSpace_sup_error_eq_norm :
    ∀ (K : Set ℝ) [CompactSpace K] (F : ℕ → C(K, ℝ)) (f : C(K, ℝ)) (n : ℕ),
    realSupError (fun m x => F m x) f n =
      ENNReal.ofReal ‖F n - f‖ := by
  intro K _ F f n
  simpa only [realSupError, ← ofReal_norm, Real.norm_eq_abs,
    ContinuousMap.sub_apply] using (F n - f).enorm_eq_iSup_enorm.symm

theorem realSupSpace_empty :
    (∀ f : C((∅ : Set ℝ), ℝ), f = 0) ∧
    (∀ f : C((∅ : Set ℝ), ℝ), ‖f‖ = 0) := by
  have hz : ∀ f : C((∅ : Set ℝ), ℝ), f = 0 := by
    intro f
    ext x
    exact x.property.elim
  exact ⟨hz, fun f => by rw [hz f, norm_zero]⟩

/-- The manuscript's C(K,ℂ) is the existing continuous-map type. -/
abbrev ComplexContinuousSpace (K : Set ℝ) := C(K, ℂ)

theorem complexSupSpace_representation :
    ∀ (K : Set ℝ),
    (∀ f : C(K, ℂ), Continuous (f : K → ℂ)) ∧
    (∀ u : K → ℂ, Continuous u → ∃! f : C(K, ℂ), (f : K → ℂ) = u) := by
  intro K
  refine ⟨fun f => f.continuous, ?_⟩
  intro u hu
  refine ⟨⟨u, hu⟩, rfl, ?_⟩
  intro g hg
  exact ContinuousMap.coe_injective hg

theorem complexSupSpace_pointwise :
    ∀ (K : Set ℝ) (f g : C(K, ℂ)) (c : ℂ) (x : K),
    (f + g) x = f x + g x ∧ (c • f) x = c * f x ∧
    (-f) x = -f x ∧ (f - g) x = f x - g x ∧ (0 : C(K, ℂ)) x = 0 := by
  intro K f g c x
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem complexSupSpace_norm_maximum :
    ∀ (K : Set ℝ) [CompactSpace K], K.Nonempty →
    ∀ f : C(K, ℂ), ∃ x : K, ‖f‖ = ‖f x‖ ∧
      ∀ y : K, ‖f y‖ ≤ ‖f x‖ := by
  intro K _ hK f
  simpa only [norm_norm] using
    supSpace_norm_attains hK f

theorem complexSupSpace_norm_laws :
    ∀ (K : Set ℝ) [CompactSpace K] (f g : C(K, ℂ)) (c : ℂ),
    0 ≤ ‖f‖ ∧ (‖f‖ = 0 ↔ f = 0) ∧ ‖f + g‖ ≤ ‖f‖ + ‖g‖ ∧
    ‖c • f‖ = ‖c‖ * ‖f‖ ∧ ‖-f‖ = ‖f‖ ∧ ‖(0 : C(K, ℂ))‖ = 0 := by
  intro K _ f g c
  refine ⟨norm_nonneg _, norm_eq_zero, norm_add_le _ _, ?_, norm_neg _, norm_zero⟩
  simpa only [norm_norm] using norm_smul c f

theorem complexSupSpace_distance :
    ∀ (K : Set ℝ) [CompactSpace K] (f g : C(K, ℂ)),
    dist f g = ‖f - g‖ := by
  intro K _ f g
  exact dist_eq_norm f g

theorem complexSupSpace_norm_converges_iff_uniform :
    ∀ (K : Set ℝ) [CompactSpace K] (F : ℕ → C(K, ℂ)) (f : C(K, ℂ)),
    Filter.Tendsto (fun n => ‖F n - f‖) Filter.atTop (𝓝 0) ↔
      ComplexUniformConverges (fun n x => F n x) f := by
  intro K _ F f
  rw [← tendsto_iff_norm_sub_tendsto_zero]
  simpa only [ComplexUniformConverges] using
    supSpace_tendsto_iff_uniform F f

theorem complexSupSpace_tendsto_iff_uniform :
    ∀ (K : Set ℝ) [CompactSpace K] (F : ℕ → C(K, ℂ)) (f : C(K, ℂ)),
    Filter.Tendsto F Filter.atTop (𝓝 f) ↔
      ComplexUniformConverges (fun n x => F n x) f := by
  intro K _ F f
  simpa only [ComplexUniformConverges] using
    supSpace_tendsto_iff_uniform F f

theorem complexSupSpace_sup_error_eq_norm :
    ∀ (K : Set ℝ) [CompactSpace K] (F : ℕ → C(K, ℂ)) (f : C(K, ℂ)) (n : ℕ),
    complexSupError (fun m x => F m x) f n =
      ENNReal.ofReal ‖F n - f‖ := by
  intro K _ F f n
  simpa only [complexSupError, ofReal_norm,
    ContinuousMap.sub_apply] using (F n - f).enorm_eq_iSup_enorm.symm

theorem complexSupSpace_empty :
    (∀ f : C((∅ : Set ℝ), ℂ), f = 0) ∧
    (∀ f : C((∅ : Set ℝ), ℂ), ‖f‖ = 0) := by
  have hz : ∀ f : C((∅ : Set ℝ), ℂ), f = 0 := by
    intro f
    ext x
    exact x.property.elim
  exact ⟨hz, fun f => by rw [hz f, norm_zero]⟩

end SingleVariableAnalysis
