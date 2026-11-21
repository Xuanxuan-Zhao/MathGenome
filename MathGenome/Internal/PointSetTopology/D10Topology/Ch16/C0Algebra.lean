import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch16.C0Algebra
import MathGenome.Internal.PointSetTopology.D10Topology.Ch11.OnePointConstruction

/-! Compact-level-set and one-point-extension descriptions of C₀.
All results are simultaneous real/complex results via `RCLike`. -/
noncomputable section
open Set Filter
open scoped Topology
universe u v w
namespace D10Topology.Ch16

abbrev IsC0 := @Specs.D10Topology.Ch16.C0Algebra.IsC0
abbrev C0 := Specs.D10Topology.Ch16.C0Algebra.C0
abbrev RealC0 := Specs.D10Topology.Ch16.C0Algebra.RealC0
abbrev ComplexC0 := Specs.D10Topology.Ch16.C0Algebra.ComplexC0
abbrev zeroExtension := @Specs.D10Topology.Ch16.C0Algebra.zeroExtension

variable {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜]

theorem c0_iff_cocompact (f : X → 𝕜) :
    IsC0 f ↔ Continuous f ∧ Tendsto f (cocompact X) (𝓝 0) := by
  constructor
  · rintro ⟨hc, hl⟩
    refine ⟨hc, Metric.tendsto_nhds.mpr fun ε hε => ?_⟩
    have he := (hl ε hε).compl_mem_cocompact
    filter_upwards [he] with x hx
    simpa only [mem_compl_iff, mem_ofPred_eq, not_le, dist_zero_right] using hx
  · rintro ⟨hc, ht⟩
    refine ⟨hc, fun ε hε => ?_⟩
    obtain ⟨K, hK, hsub⟩ := mem_cocompact.mp (Metric.tendsto_nhds.mp ht ε hε)
    apply hK.of_isClosed_subset (isClosed_le continuous_const hc.norm)
    intro x hx
    by_contra h
    have hlt := hsub h
    simp only [mem_ofPred_eq, dist_zero_right] at hlt
    exact (not_lt_of_ge hx) hlt

theorem c0_real_iff : Specs.D10Topology.Ch16.C0Algebra.c0_real_iff := by
  intro X _ f
  simp only [Specs.D10Topology.Ch16.C0Algebra.IsC0, Real.norm_eq_abs]

theorem c0_bundled_iff (f : X → 𝕜) :
    IsC0 f ↔ ∃ g : C0 X 𝕜, (g : X → 𝕜) = f := by
  rw [c0_iff_cocompact]
  constructor
  · rintro ⟨hc, ht⟩
    exact ⟨⟨⟨f, hc⟩, ht⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g.continuous, zero_at_infty g⟩

theorem zeroExtension_values : Specs.D10Topology.Ch16.C0Algebra.zeroExtension_values := by
  intro X 𝕜 _ f
  exact ⟨rfl, fun _ => rfl⟩

theorem c0_iff_continuous_extension (hX : Ch11.LCH X) (f : X → 𝕜) :
    IsC0 f ↔ Continuous (zeroExtension f) := by
  let : T2Space X := hX.2
  rw [OnePoint.continuous_iff, coclosedCompact_eq_cocompact, c0_iff_cocompact]
  exact and_comm

theorem c0_bounded (f : X → 𝕜) (hf : IsC0 f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M := by
  obtain ⟨g, rfl⟩ := (c0_bundled_iff f).mp hf
  exact ⟨‖g.toBCF‖, norm_nonneg _, g.toBCF.norm_coe_le_norm⟩

theorem c0_zero : IsC0 (0 : X → 𝕜) :=
  (c0_bundled_iff _).mpr ⟨0, rfl⟩

theorem c0_add (f g : X → 𝕜) (hf : IsC0 f) (hg : IsC0 g) : IsC0 (f + g) := by
  obtain ⟨f, rfl⟩ := (c0_bundled_iff f).mp hf
  obtain ⟨g, rfl⟩ := (c0_bundled_iff g).mp hg
  exact (c0_bundled_iff _).mpr ⟨f + g, rfl⟩

theorem c0_mul (f g : X → 𝕜) (hf : IsC0 f) (hg : IsC0 g) : IsC0 (f * g) := by
  obtain ⟨f, rfl⟩ := (c0_bundled_iff f).mp hf
  obtain ⟨g, rfl⟩ := (c0_bundled_iff g).mp hg
  exact (c0_bundled_iff _).mpr ⟨f * g, rfl⟩

theorem c0_smul (c : 𝕜) (f : X → 𝕜) (hf : IsC0 f) : IsC0 (c • f) := by
  obtain ⟨f, rfl⟩ := (c0_bundled_iff f).mp hf
  exact (c0_bundled_iff _).mpr ⟨c • f, rfl⟩

theorem c0_conjugate : Specs.D10Topology.Ch16.C0Algebra.c0_conjugate := by
  intro X _ f hf
  obtain ⟨f, rfl⟩ := (c0_bundled_iff f).mp hf
  exact (c0_bundled_iff _).mpr ⟨star f, rfl⟩

theorem c0_compact_iff [CompactSpace X] (f : X → 𝕜) : IsC0 f ↔ Continuous f := by
  rw [c0_iff_cocompact]
  simp

theorem c0_empty [IsEmpty X] (f : X → 𝕜) : IsC0 f :=
  (c0_compact_iff f).mpr continuous_of_discreteTopology

theorem c0_algebra : Specs.D10Topology.Ch16.C0Algebra.c0_algebra := by
  intro X 𝕜 _ _
  refine ⟨{
    carrier := {f | IsC0 (f : X → 𝕜)}
    zero_mem' := c0_zero
    add_mem' := fun hf hg => c0_add _ _ hf hg
    mul_mem' := fun hf hg => c0_mul _ _ hf hg
    smul_mem' := fun c _ hf => c0_smul c _ hf }, fun _ => Iff.rfl⟩

/-- A positive level set of the limit lies in a half-sized level set of one
uniform approximant, and is closed by continuity of the limit. -/
theorem c0_uniform_limit {I : Type w} (l : Filter I) [l.NeBot]
    (F : I → X → 𝕜) (f : X → 𝕜) (hF : ∀ i, IsC0 (F i))
    (hu : TendstoUniformly F f l) : IsC0 f := by
  have hc : Continuous f := hu.continuous (Eventually.of_forall fun i => (hF i).1).frequently
  refine ⟨hc, fun ε hε => ?_⟩
  obtain ⟨i, hi⟩ := (Metric.tendstoUniformly_iff.mp hu (ε / 2) (half_pos hε)).exists
  apply ((hF i).2 (ε / 2) (half_pos hε)).of_isClosed_subset
    (isClosed_le continuous_const hc.norm)
  intro x hx
  have he := hi x
  rw [dist_eq_norm] at he
  have ht := norm_sub_norm_le (f x) (F i x)
  change ε ≤ ‖f x‖ at hx
  change ε / 2 ≤ ‖F i x‖
  linarith

omit [TopologicalSpace X] in
theorem zeroExtension_uniform_iff {I : Type w} (l : Filter I)
    (F : I → X → 𝕜) (f : X → 𝕜) :
    TendstoUniformly (fun i => zeroExtension (F i)) (zeroExtension f) l ↔
      TendstoUniformly F f l := by
  simp only [Metric.tendstoUniformly_iff]
  constructor
  · intro h ε hε
    filter_upwards [h ε hε] with i hi using fun x => hi (OnePoint.some x)
  · intro h ε hε
    filter_upwards [h ε hε] with i hi
    intro z
    induction z using OnePoint.rec with
    | infty => simpa [Specs.D10Topology.Ch16.C0Algebra.zeroExtension] using hε
    | coe x => exact hi x

/-- The algebra map used by real and complex C₀ approximation. -/
abbrev c0ExtensionHom := @Specs.D10Topology.Ch16.C0Algebra.c0ExtensionHom

theorem zeroExtension_conjugate : Specs.D10Topology.Ch16.C0Algebra.zeroExtension_conjugate := by
  intro X f
  funext z
  induction z using OnePoint.rec with
  | infty => exact (star_zero ℂ).symm
  | coe x => rfl

theorem c0_extension_algebra_bridge : Specs.D10Topology.Ch16.C0Algebra.c0_extension_algebra_bridge := by
  intro X 𝕜 _ _ hX
  let E := c0ExtensionHom (𝕜 := 𝕜) hX
  refine ⟨E, fun _ => rfl, ?_, ?_, ?_⟩
  · intro f g h
    apply ZeroAtInftyContinuousMap.ext
    intro x
    exact congrArg (fun k : C(OnePoint X, 𝕜) => k (OnePoint.some x)) h
  · intro g
    constructor
    · rintro ⟨f, rfl⟩
      rfl
    · intro hg
      let f : X → 𝕜 := fun x => g (OnePoint.some x)
      have he : zeroExtension f = (g : OnePoint X → 𝕜) := by
        funext z
        induction z using OnePoint.rec with
        | infty => exact hg.symm
        | coe x => rfl
      have hf : IsC0 f := (c0_iff_continuous_extension hX f).mpr (he ▸ g.continuous)
      obtain ⟨f₀, hf₀⟩ := (c0_bundled_iff f).mp hf
      refine ⟨f₀, ContinuousMap.ext fun z => ?_⟩
      change zeroExtension (f₀ : X → 𝕜) z = g z
      rw [hf₀, he]
  · intro f
    apply le_antisymm
    · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro z
      induction z using OnePoint.rec with
      | infty => exact (norm_zero : ‖(0 : 𝕜)‖ = 0) ▸ norm_nonneg f
      | coe x => exact f.toBCF.norm_coe_le_norm x
    · change ‖f.toBCF‖ ≤ ‖E f‖
      apply (BoundedContinuousFunction.norm_le (norm_nonneg (E f))).mpr
      intro x
      exact (E f).norm_coe_le_norm (OnePoint.some x)

end D10Topology.Ch16
