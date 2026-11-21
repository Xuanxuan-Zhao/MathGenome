import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SpectralProductAndSumDomains
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.MeasurableSpectralCalculus

noncomputable section
open MeasureTheory Set Filter
namespace ExpandedFA.Unbounded.SpectralProductAndSumDomains
open MeasurableSpectralCalculus
universe u v

section Localized
variable {H : Type v} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- A common family of bounded cutoffs may replace the function's own cutoffs
when describing its graph. -/
theorem graph_iff_common_cutoffs (T Q P A : ℕ → H →L[ℂ] H)
    (hQ : ∀ y, Tendsto (fun n => Q n y) atTop (nhds y))
    (hP : ∀ y, Tendsto (fun n => P n y) atTop (nhds y))
    (hQT : ∀ n, ∀ᶠ m in atTop, Q n * T m = T n)
    (hPT : ∀ n, ∀ᶠ m in atTop, P n * T m = A n)
    (hcross : ∀ m n, T m * P n = Q m * A n) (x y : H) :
    (x, y) ∈ (limitOperator T).graph ↔ ∀ n, A n x = P n y := by
  constructor
  · intro h n
    have ht := (mem_limitOperator_graph_iff T x y).mp h
    have hp := ((P n).continuous.tendsto y).comp ht
    have heq : (fun m => P n (T m x)) =ᶠ[atTop] (fun _ => A n x) := by
      filter_upwards [hPT n] with m hm
      exact congrArg (fun B : H →L[ℂ] H => B x) hm
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' heq.symm) hp
  · intro h
    apply (mem_limitOperator_graph_iff_localized Q T hQ hQT x y).mpr
    intro m
    have ht := ((T m).continuous.tendsto x).comp (hP x)
    have hq := ((Q m).continuous.tendsto y).comp (hP y)
    have heq : (fun n => T m (P n x)) = (fun n => Q m (P n y)) := by
      funext n
      calc
        T m (P n x) = Q m (A n x) := congrArg (fun B : H →L[ℂ] H => B x) (hcross m n)
        _ = Q m (P n y) := by rw [h n]
    change Tendsto (fun n => T m (P n x)) atTop (nhds (T m x)) at ht
    rw [heq] at ht
    exact tendsto_nhds_unique ht hq

end Localized

section Spectral
variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : SpectralMeasure.ProjectionValuedMeasure S H} (C : BoundedRealization E)

/-- The symbol a restricted to the n-th spectral cutoff for k. -/
def piece (k a : S → ℂ) (n : ℕ) : S → ℂ :=
  {s | ‖k s‖ ≤ (n : ℝ)}.indicator a

theorem bounded_piece {k a : S → ℂ} (hk : Measurable k) (ha : Measurable a)
    (hbound : ∀ s, ‖a s‖ ≤ ‖k s‖) (n : ℕ) :
    SpectralMeasure.Spec.IsBoundedMeasurable (piece k a n) := by
  refine ⟨ha.indicator (measurableSet_le hk.norm measurable_const), n, ?_⟩
  intro s
  classical
  by_cases hs : ‖k s‖ ≤ (n : ℝ)
  · simpa [piece, hs] using (hbound s).trans hs
  · simp [piece, hs]

theorem mem_graph_iff_piece {k a : S → ℂ} (hk : Measurable k) (ha : Measurable a)
    (hbound : ∀ s, ‖a s‖ ≤ ‖k s‖) (x y : H) :
    (x, y) ∈ (measurableIntegral C a).graph ↔
      ∀ n, C.integral (piece k a n) x = C.integral (cutoffIndicator k n) y := by
  apply graph_iff_common_cutoffs
    (fun n => C.integral (truncation a n))
    (fun n => C.integral (cutoffIndicator a n))
    (fun n => C.integral (cutoffIndicator k n))
    (fun n => C.integral (piece k a n))
    (C.cutoff_tendsto ha) (C.cutoff_tendsto hk) (C.cutoff_left ha)
  · intro n
    filter_upwards [eventually_ge_atTop n] with m hm
    rw [← C.mul _ _ (boundedMeasurable_cutoffIndicator hk n) (boundedMeasurable_truncation ha m)]
    congr 1
    classical
    funext s
    have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    by_cases hs : ‖k s‖ ≤ (n : ℝ)
    · have has : ‖a s‖ ≤ (m : ℝ) := (hbound s).trans (hs.trans hnm)
      simp [piece, cutoffIndicator, truncation, hs, has]
    · simp [piece, cutoffIndicator, hs]
  · intro m n
    rw [← C.mul _ _ (boundedMeasurable_truncation ha m) (boundedMeasurable_cutoffIndicator hk n),
      ← C.mul _ _ (boundedMeasurable_cutoffIndicator ha m) (bounded_piece hk ha hbound n)]
    congr 1
    classical
    funext s
    by_cases hk' : ‖k s‖ ≤ (n : ℝ) <;>
      by_cases ha' : ‖a s‖ ≤ (m : ℝ) <;>
      simp [piece, cutoffIndicator, truncation, hk', ha']

/-- Bounded spectral vectors belong to the domain, with the expected value. -/
theorem piece_graph {k a : S → ℂ} (hk : Measurable k) (ha : Measurable a)
    (hbound : ∀ s, ‖a s‖ ≤ ‖k s‖) (n : ℕ) (x : H) :
    (C.integral (cutoffIndicator k n) x, C.integral (piece k a n) x) ∈
      (measurableIntegral C a).graph := by
  apply (mem_limitOperator_graph_iff _ _ _).mpr
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with m hm
  have heq : C.integral (truncation a m) * C.integral (cutoffIndicator k n) =
      C.integral (piece k a n) := by
    rw [← C.mul _ _ (boundedMeasurable_truncation ha m) (boundedMeasurable_cutoffIndicator hk n)]
    congr 1
    classical
    funext s
    have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    by_cases hs : ‖k s‖ ≤ (n : ℝ)
    · have has : ‖a s‖ ≤ (m : ℝ) := (hbound s).trans (hs.trans hnm)
      simp [piece, cutoffIndicator, truncation, hs, has]
    · simp [piece, cutoffIndicator, hs]
  exact (congrArg (fun B : H →L[ℂ] H => B x) heq).symm


/-- A single measurable size controls both factors and both resulting symbols. -/
def commonSize (f g : S → ℂ) (s : S) : ℂ :=
  (‖f s‖ + ‖g s‖ + ‖(f * g) s‖ + ‖(f + g) s‖ : ℝ)

theorem measurable_commonSize {f g : S → ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (commonSize f g) :=
  (hf.norm.add hg.norm |>.add (hf.mul hg).norm |>.add (hf.add hg).norm).complex_ofReal

omit [MeasurableSpace S] in
theorem commonSize_bounds (f g : S → ℂ) (s : S) :
    ‖f s‖ ≤ ‖commonSize f g s‖ ∧ ‖g s‖ ≤ ‖commonSize f g s‖ ∧
    ‖(f * g) s‖ ≤ ‖commonSize f g s‖ ∧ ‖(f + g) s‖ ≤ ‖commonSize f g s‖ := by
  rw [commonSize, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := norm_nonneg (f s)
  have := norm_nonneg (g s)
  have := norm_nonneg ((f * g) s)
  have := norm_nonneg ((f + g) s)
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Multiplication on two nested common cutoffs. -/
theorem integral_piece_mul {k a b : S → ℂ} (hk : Measurable k)
    (ha : Measurable a) (hb : Measurable b)
    (hba : ∀ s, ‖a s‖ ≤ ‖k s‖) (hbb : ∀ s, ‖b s‖ ≤ ‖k s‖)
    {n m : ℕ} (hnm : n ≤ m) :
    C.integral (piece k a n) * C.integral (piece k b m) =
      C.integral (piece k (a * b) n) := by
  rw [← C.mul _ _ (bounded_piece hk ha hba n) (bounded_piece hk hb hbb m)]
  congr 1
  classical
  funext s
  by_cases hn : ‖k s‖ ≤ (n : ℝ)
  · have hm : ‖k s‖ ≤ (m : ℝ) := hn.trans (by exact_mod_cast hnm)
    simp [piece, hn, hm]
  · simp [piece, hn]

theorem integral_piece_cutoff {k a : S → ℂ} (hk : Measurable k) (ha : Measurable a)
    (hba : ∀ s, ‖a s‖ ≤ ‖k s‖) (n : ℕ) :
    C.integral (piece k a n) * C.integral (cutoffIndicator k n) =
      C.integral (piece k a n) := by
  rw [← C.mul _ _ (bounded_piece hk ha hba n) (boundedMeasurable_cutoffIndicator hk n)]
  congr 1
  classical
  funext s
  by_cases hn : ‖k s‖ ≤ (n : ℝ) <;> simp [piece, cutoffIndicator, hn]

theorem product_graph {f g : S → ℂ} (hf : Measurable f) (hg : Measurable g) (x z : H) :
    (x, z) ∈ (OperatorDomainsSpec.productValue (measurableIntegral C f)
      (measurableIntegral C g)).graph ↔
    x ∈ (measurableIntegral C g).domain ∧ (x, z) ∈ (measurableIntegral C (f * g)).graph := by
  let k := commonSize f g
  have hk := measurable_commonSize hf hg
  have hbf : ∀ s, ‖f s‖ ≤ ‖k s‖ := fun s => (commonSize_bounds f g s).1
  have hbg : ∀ s, ‖g s‖ ≤ ‖k s‖ := fun s => (commonSize_bounds f g s).2.1
  have hbfg : ∀ s, ‖(f * g) s‖ ≤ ‖k s‖ := fun s => (commonSize_bounds f g s).2.2.1
  have hgf := mem_graph_iff_piece C hk hf hbf
  have hgg := mem_graph_iff_piece C hk hg hbg
  have hgfg := mem_graph_iff_piece C hk (hf.mul hg) hbfg
  rw [mem_product_graph_iff]
  constructor
  · rintro ⟨y, hxy, hyz⟩
    refine ⟨((ExpandedFA.Unbounded.mem_graph_iff _ _).mp hxy).choose, ?_⟩
    apply (hgfg x z).mpr
    intro n
    calc
      C.integral (piece k (f * g) n) x =
          C.integral (piece k f n) (C.integral (piece k g n) x) := by
        exact congrArg (fun B : H →L[ℂ] H => B x)
          (integral_piece_mul C hk hf hg hbf hbg (le_refl n)).symm
      _ = C.integral (piece k f n) (C.integral (cutoffIndicator k n) y) := by
        rw [(hgg x y).mp hxy n]
      _ = C.integral (piece k f n) y :=
        congrArg (fun B : H →L[ℂ] H => B y) (integral_piece_cutoff C hk hf hbf n)
      _ = C.integral (cutoffIndicator k n) z := (hgf y z).mp hyz n
  · rintro ⟨hx, hxz⟩
    let y := measurableIntegral C g ⟨x, hx⟩
    have hxy : (x, y) ∈ (measurableIntegral C g).graph :=
      (measurableIntegral C g).mem_graph_iff.mpr ⟨⟨x, hx⟩, rfl, rfl⟩
    refine ⟨y, hxy, (hgf y z).mpr ?_⟩
    intro n
    have ht := ((C.integral (piece k f n)).continuous.tendsto y).comp (C.cutoff_tendsto hk y)
    have heq : (fun m => C.integral (piece k f n) (C.integral (cutoffIndicator k m) y))
        =ᶠ[atTop] (fun _ => C.integral (cutoffIndicator k n) z) := by
      filter_upwards [eventually_ge_atTop n] with m hm
      rw [← (hgg x y).mp hxy m]
      change (C.integral (piece k f n) * C.integral (piece k g m)) x = _
      rw [integral_piece_mul C hk hf hg hbf hbg hm]
      exact (hgfg x z).mp hxz n
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' heq.symm)

end Spectral

theorem product_rule : Spec.ProductRule.{u, v} := by
  intro S H _ _ _ _ E C f g hf hg
  have hle : OperatorDomainsSpec.productValue (measurableIntegral C f) (measurableIntegral C g) ≤
      measurableIntegral C (f * g) := by
    apply LinearPMap.le_of_le_graph
    rintro ⟨x, z⟩ h
    exact ((product_graph C hf hg x z).mp h).2
  refine ⟨?_, hle⟩
  ext x
  constructor
  · intro hx
    have h := (product_graph C hf hg x
      (OperatorDomainsSpec.productValue (measurableIntegral C f) (measurableIntegral C g) ⟨x, hx⟩)).mp
      ((OperatorDomainsSpec.productValue (measurableIntegral C f) (measurableIntegral C g)).mem_graph_iff.mpr
        ⟨⟨x, hx⟩, rfl, rfl⟩)
    exact ⟨h.1, ((ExpandedFA.Unbounded.mem_graph_iff _ _).mp h.2).choose⟩
  · rintro ⟨hxg, hxfg⟩
    have h := (product_graph C hf hg x (measurableIntegral C (f * g) ⟨x, hxfg⟩)).mpr
      ⟨hxg, (measurableIntegral C (f * g)).mem_graph_iff.mpr ⟨⟨x, hxfg⟩, rfl, rfl⟩⟩
    exact ((ExpandedFA.Unbounded.mem_graph_iff _ _).mp h).choose


section Closure
variable {H : Type v} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Graph approximation by vectors in an operator identifies its closure. -/
theorem closure_eq_of_graph_approximation (A B : Operator ℂ H H) (hB : B.IsClosed)
    (hAB : A ≤ B)
    (happrox : ∀ z ∈ B.graph, ∃ z' : ℕ → H × H,
      (∀ n, z' n ∈ A.graph) ∧ Tendsto z' atTop (nhds z)) :
    A.IsClosable ∧ A.closure = B := by
  have hA := hB.isClosable.leIsClosable hAB
  refine ⟨hA, LinearPMap.eq_of_eq_graph ?_⟩
  rw [← hA.graph_closure_eq_closure_graph]
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le hAB) hB
  · intro z hz
    obtain ⟨z', hz', ht⟩ := happrox z hz
    exact mem_closure_of_tendsto ht (Eventually.of_forall hz')

end Closure

theorem product_closure : Spec.ProductClosure.{u, v} := by
  intro S H _ _ _ _ E C f g hf hg
  apply closure_eq_of_graph_approximation _ _ (measurableIntegral_isClosed C (hf.mul hg))
    (product_rule C f g hf hg).2
  rintro ⟨x, z⟩ hxz
  let k := commonSize f g
  have hk := measurable_commonSize hf hg
  have hbg : ∀ s, ‖g s‖ ≤ ‖k s‖ := fun s => (commonSize_bounds f g s).2.1
  have hbfg : ∀ s, ‖(f * g) s‖ ≤ ‖k s‖ := fun s => (commonSize_bounds f g s).2.2.1
  refine ⟨fun n => (C.integral (cutoffIndicator k n) x, C.integral (cutoffIndicator k n) z),
    ?_, (C.cutoff_tendsto hk x).prodMk_nhds (C.cutoff_tendsto hk z)⟩
  intro n
  apply (product_graph C hf hg _ _).mpr
  refine ⟨((ExpandedFA.Unbounded.mem_graph_iff _ _).mp (piece_graph C hk hg hbg n x)).choose, ?_⟩
  have h := piece_graph C hk (hf.mul hg) hbfg n x
  rw [(mem_graph_iff_piece C hk (hf.mul hg) hbfg x z).mp hxz n] at h
  exact h

section Sum
variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : SpectralMeasure.ProjectionValuedMeasure S H} (C : BoundedRealization E)

theorem integral_piece_add {k a b : S → ℂ} (hk : Measurable k)
    (ha : Measurable a) (hb : Measurable b)
    (hba : ∀ s, ‖a s‖ ≤ ‖k s‖) (hbb : ∀ s, ‖b s‖ ≤ ‖k s‖) (n : ℕ) :
    C.integral (piece k (a + b) n) =
      C.integral (piece k a n) + C.integral (piece k b n) := by
  have heq : piece k (a + b) n = piece k a n + piece k b n := by
    classical
    funext s
    by_cases hn : ‖k s‖ ≤ (n : ℝ) <;> simp [piece, hn]
  rw [heq, C.add _ _ (bounded_piece hk ha hba n) (bounded_piece hk hb hbb n)]

theorem sum_le {f g : S → ℂ} (hf : Measurable f) (hg : Measurable g) :
    measurableIntegral C f + measurableIntegral C g ≤ measurableIntegral C (f + g) := by
  let k := commonSize f g
  have hk := measurable_commonSize hf hg
  have hbf : ∀ s, ‖f s‖ ≤ ‖k s‖ := fun s => (commonSize_bounds f g s).1
  have hbg : ∀ s, ‖g s‖ ≤ ‖k s‖ := fun s => (commonSize_bounds f g s).2.1
  have hbadd : ∀ s, ‖(f + g) s‖ ≤ ‖k s‖ := fun s => (commonSize_bounds f g s).2.2.2
  apply LinearPMap.le_of_le_graph
  rintro ⟨x, z⟩ h
  obtain ⟨hx, hz⟩ := (ExpandedFA.Unbounded.mem_graph_iff _ _).mp h
  change measurableIntegral C f ⟨x, hx.1⟩ + measurableIntegral C g ⟨x, hx.2⟩ = z at hz
  rw [← hz]
  apply (mem_graph_iff_piece C hk (hf.add hg) hbadd _ _).mpr
  intro n
  rw [integral_piece_add C hk hf hg hbf hbg, _root_.add_apply, map_add]
  congr 1
  · exact (mem_graph_iff_piece C hk hf hbf _ _).mp
      ((measurableIntegral C f).mem_graph_iff.mpr ⟨⟨x, hx.1⟩, rfl, rfl⟩) n
  · exact (mem_graph_iff_piece C hk hg hbg _ _).mp
      ((measurableIntegral C g).mem_graph_iff.mpr ⟨⟨x, hx.2⟩, rfl, rfl⟩) n

end Sum

theorem sum_closure : Spec.SumClosure.{u, v} := by
  intro S H _ _ _ _ E C f g hf hg
  apply closure_eq_of_graph_approximation _ _ (measurableIntegral_isClosed C (hf.add hg))
    (sum_le C hf hg)
  rintro ⟨x, z⟩ hxz
  let k := commonSize f g
  have hk := measurable_commonSize hf hg
  have hbf : ∀ s, ‖f s‖ ≤ ‖k s‖ := fun s => (commonSize_bounds f g s).1
  have hbg : ∀ s, ‖g s‖ ≤ ‖k s‖ := fun s => (commonSize_bounds f g s).2.1
  have hbadd : ∀ s, ‖(f + g) s‖ ≤ ‖k s‖ := fun s => (commonSize_bounds f g s).2.2.2
  refine ⟨fun n => (C.integral (cutoffIndicator k n) x, C.integral (cutoffIndicator k n) z),
    ?_, (C.cutoff_tendsto hk x).prodMk_nhds (C.cutoff_tendsto hk z)⟩
  intro n
  obtain ⟨hxf, hF⟩ := (ExpandedFA.Unbounded.mem_graph_iff _ _).mp (piece_graph C hk hf hbf n x)
  obtain ⟨hxg, hG⟩ := (ExpandedFA.Unbounded.mem_graph_iff _ _).mp (piece_graph C hk hg hbg n x)
  apply (ExpandedFA.Unbounded.mem_graph_iff _ _).mpr
  refine ⟨⟨hxf, hxg⟩, ?_⟩
  change measurableIntegral C f ⟨_, hxf⟩ + measurableIntegral C g ⟨_, hxg⟩ = _
  rw [hF, hG]
  rw [← _root_.add_apply, ← integral_piece_add C hk hf hg hbf hbg]
  exact (mem_graph_iff_piece C hk (hf.add hg) hbadd _ _).mp hxz n


namespace DiagonalExample
open scoped Classical
set_option maxHeartbeats 400000
abbrev Space := lp (fun _ : ℕ => ℂ) 2

/-- Coordinate projection on an arbitrary subset of the counting space. -/
def mask (B : Set ℕ) (x : Space) : Space :=
  ⟨B.indicator x, (lp.memℓp x).norm.mono (fun i => by
    classical
    by_cases hi : i ∈ B <;> simp [hi])⟩

@[simp] theorem mask_apply (B : Set ℕ) (x : Space) (i : ℕ) :
    mask B x i = B.indicator x i := rfl

def projection (B : Set ℕ) : Space →L[ℂ] Space :=
  LinearMap.mkContinuous
    { toFun := mask B
      map_add' := by
        intro x y
        apply lp.ext
        funext i
        change B.indicator (fun j => x j + y j) i = B.indicator x i + B.indicator y i
        classical
        by_cases hi : i ∈ B <;> simp [Set.indicator, hi]
      map_smul' := by
        intro c x
        apply lp.ext
        funext i
        classical
        by_cases hi : i ∈ B <;> simp [mask, lp.coeFn_smul, hi] }
    1 (fun x => by
      simpa only [one_mul] using
        (lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun i => by
          classical
          by_cases hi : i ∈ B <;> simp [mask, hi])))

@[simp] theorem projection_apply (B : Set ℕ) (x : Space) (i : ℕ) :
    projection B x i = B.indicator x i := rfl

theorem projection_selfAdjoint (B : Set ℕ) : IsSelfAdjoint (projection B) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℂ (projection B x) y = inner ℂ x (projection B y)
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  classical
  by_cases hi : i ∈ B <;> simp [projection_apply, hi]

theorem projection_inter (B D : Set ℕ) : projection B * projection D = projection (B ∩ D) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  classical
  by_cases hB : i ∈ B <;> by_cases hD : i ∈ D <;>
    simp [projection_apply, hB, hD]

theorem projection_single (B : Set ℕ) (i : ℕ) (a : ℂ) :
    projection B (lp.single (E := fun _ : ℕ => ℂ) 2 i a) = if i ∈ B then lp.single (E := fun _ : ℕ => ℂ) 2 i a else 0 := by
  apply lp.ext
  funext j
  classical
  by_cases hj : j = i
  · subst j
    by_cases hi : i ∈ B <;> simp [projection_apply, hi]
  · by_cases hi : i ∈ B <;> by_cases hB : j ∈ B <;>
      simp [projection_apply, hi, hB, lp.coeFn_single, hj]

/-- The sum of the coordinate expansion on B is its coordinate projection. -/
theorem hasSum_single_on (B : Set ℕ) (x : Space) :
    HasSum (fun i : B => lp.single (E := fun _ : ℕ => ℂ) 2 (i : ℕ) (x i)) (projection B x) := by
  have hs : Summable (fun i : B => lp.single (E := fun _ : ℕ => ℂ) 2 (i : ℕ) (x i)) :=
    (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x).summable.subtype B
  suffices heq : (∑' i : B, lp.single (E := fun _ : ℕ => ℂ) 2 (i : ℕ) (x i)) = projection B x by
    rw [← heq]
    exact hs.hasSum
  symm
  apply lp.ext
  funext j
  have heval := (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 j).map_tsum hs
  change (projection B x) j = (∑' i : B, lp.single (E := fun _ : ℕ => ℂ) 2 (i : ℕ) (x i)) j
  rw [show (∑' i : B, lp.single (E := fun _ : ℕ => ℂ) 2 (i : ℕ) (x i)) j =
    ∑' i : B, (lp.single (E := fun _ : ℕ => ℂ) 2 (i : ℕ) (x i)) j from heval]
  classical
  by_cases hj : j ∈ B
  · rw [tsum_eq_single (⟨j, hj⟩ : B)]
    · simp [projection_apply, hj]
    · intro i hi
      have hij : j ≠ (i : ℕ) := by
        intro h
        apply hi
        exact Subtype.ext h.symm
      simp [Pi.single_eq_of_ne hij]
  · have hz : ∀ i : B, (lp.single (E := fun _ : ℕ => ℂ) 2 (i : ℕ) (x i)) j = 0 := by
      intro i
      have hij : j ≠ (i : ℕ) := fun h => hj (h ▸ i.2)
      simp [Pi.single_eq_of_ne hij]
    rw [tsum_congr hz]
    simp [projection_apply, hj]

/-- Countable additivity follows by regrouping the unconditional coordinate
expansion along the disjoint sets. -/
theorem projection_iUnion (B : ℕ → Set ℕ) (hB : Pairwise (fun n m => Disjoint (B n) (B m)))
    (x : Space) : HasSum (fun n => projection (B n) x) (projection (⋃ n, B n) x) := by
  let index : (Σ n, B n) → ℕ := fun p => p.2
  have hinj : Function.Injective index := by
    rintro ⟨n, i, hi⟩ ⟨m, j, hj⟩ hij
    dsimp [index] at hij
    subst j
    have hnm : n = m := by
      by_contra hne
      exact Set.disjoint_left.mp (hB hne) hi hj
    subst m
    rfl
  have hs : Summable (fun p : Σ n, B n => lp.single (E := fun _ : ℕ => ℂ) 2 (index p) (x (index p))) :=
    (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x).summable.comp_injective hinj
  have hsum := hs.hasSum.sigma (fun n => hasSum_single_on (B n) x)
  suffices heq : (∑' p : Σ n, B n, lp.single (E := fun _ : ℕ => ℂ) 2 (index p) (x (index p))) =
      projection (⋃ n, B n) x by
    rw [← heq]
    exact hsum
  symm
  apply lp.ext
  funext j
  have heval := (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 j).map_tsum hs
  change (projection (⋃ n, B n) x) j = (∑' p : Σ n, B n, lp.single (E := fun _ : ℕ => ℂ) 2 (index p) (x (index p))) j
  rw [show (∑' p : Σ n, B n, lp.single (E := fun _ : ℕ => ℂ) 2 (index p) (x (index p))) j =
    ∑' p : Σ n, B n, (lp.single (E := fun _ : ℕ => ℂ) 2 (index p) (x (index p))) j from heval]
  classical
  by_cases hj : j ∈ ⋃ n, B n
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hj
    let p : Σ n, B n := ⟨n, ⟨j, hn⟩⟩
    rw [tsum_eq_single p]
    · simp [projection_apply, hj, p, index]
    · intro q hq
      have hij : j ≠ index q := fun h => hq (hinj h.symm)
      simp [Pi.single_eq_of_ne hij]
  · have hz : ∀ p : Σ n, B n,
        (lp.single (E := fun _ : ℕ => ℂ) 2 (index p) (x (index p))) j = 0 := by
      intro p
      have hij : j ≠ index p := by
        intro h
        exact hj (Set.mem_iUnion.mpr ⟨p.1, h ▸ p.2.2⟩)
      simp [Pi.single_eq_of_ne hij]
    rw [tsum_congr hz]
    simp [projection_apply, hj]

def pvm : SpectralMeasure.ProjectionValuedMeasure ℕ Space where
  toFun := projection
  univ := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    simp [projection_apply]
  selfAdjoint := fun B _ => projection_selfAdjoint B
  inter := fun B D _ _ => projection_inter B D
  iUnion := fun B _ hB x => projection_iUnion B hB x


variable (C : BoundedRealization pvm)

theorem measure_basis (i : ℕ) :
    C.measure (lp.single (E := fun _ : ℕ => ℂ) 2 i 1) = Measure.dirac i := by
  apply Measure.ext
  intro B hB
  rw [C.measure_apply _ B hB]
  change ENNReal.ofReal (‖projection B (lp.single (E := fun _ : ℕ => ℂ) 2 i 1)‖ ^ 2) = _
  rw [projection_single]
  by_cases hi : i ∈ B
  · simp [hi, lp.norm_single (by norm_num : (0 : ENNReal) < 2), Measure.dirac_apply' i hB]
  · simp [hi, Measure.dirac_apply' i hB]

theorem integral_const (c : ℂ) : C.integral (fun _ : ℕ => c) = c • (1 : Space →L[ℂ] Space) := by
  have h1 : SpectralMeasure.Spec.IsBoundedMeasurable (fun _ : ℕ => (1 : ℂ)) :=
    ⟨measurable_const, 1, by simp⟩
  have heq : (fun _ : ℕ => c) = c • (fun _ : ℕ => (1 : ℂ)) := by ext; simp
  rw [heq, C.smul _ _ h1, C.one]

theorem integral_basis {f : ℕ → ℂ} (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) (i : ℕ) :
    C.integral f (lp.single (E := fun _ : ℕ => ℂ) 2 i 1) =
      f i • lp.single (E := fun _ : ℕ => ℂ) 2 i 1 := by
  let c : ℕ → ℂ := fun _ => f i
  have hc : SpectralMeasure.Spec.IsBoundedMeasurable c := ⟨measurable_const, ‖f i‖, by simp [c]⟩
  have hd : SpectralMeasure.Spec.IsBoundedMeasurable (f - c) := by
    simpa only [sub_eq_add_neg] using hf.add (by simpa using hc.smul (-1))
  have hsq := C.norm_sq (f - c) hd (lp.single (E := fun _ : ℕ => ℂ) 2 i 1)
  rw [measure_basis C i] at hsq
  have hzero : C.integral (f - c) (lp.single (E := fun _ : ℕ => ℂ) 2 i 1) = 0 := by
    apply norm_eq_zero.mp
    have hsq' : ‖C.integral (f - c) (lp.single (E := fun _ : ℕ => ℂ) 2 i 1)‖ ^ 2 = 0 := by
      simpa [c] using hsq
    nlinarith [norm_nonneg (C.integral (f - c) (lp.single (E := fun _ : ℕ => ℂ) 2 i 1))]
  rw [C.sub f c hf hc] at hzero
  have h := sub_eq_zero.mp hzero
  simpa [c, integral_const C] using h

/-- The bounded spectral integral for the coordinate PVM is diagonal. -/
theorem integral_coordinate {f : ℕ → ℂ} (hf : SpectralMeasure.Spec.IsBoundedMeasurable f)
    (x : Space) (i : ℕ) : (C.integral f x) i = f i * x i := by
  have h := (C.integral f).adjoint_inner_left x
    (lp.single (E := fun _ : ℕ => ℂ) 2 i 1)
  rw [← ContinuousLinearMap.star_eq_adjoint, ← C.map_star f hf, integral_basis C hf.star i] at h
  simpa [inner_smul_left, lp.inner_single_left, RCLike.inner_apply] using h.symm

/-- The vector (2⁻ⁿ) belongs to ℓ², whereas its image under (2ⁿ) does not. -/
def testVector : Space :=
  ⟨fun n => (1 / 2 : ℂ) ^ n, by
    apply memℓp_gen
    have hs := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)
    convert hs using 1
    funext n
    simp only [ENNReal.toReal_ofNat, norm_pow, Real.rpow_two]
    rw [← pow_mul, mul_comm n 2, pow_mul]
    norm_num⟩

theorem testVector_not_mem :
    testVector ∉ (measurableIntegral C (fun n : ℕ => (2 : ℂ) ^ n)).domain := by
  intro hx
  let y := measurableIntegral C (fun n : ℕ => (2 : ℂ) ^ n) ⟨testVector, hx⟩
  have hy : ∀ i, y i = 1 := by
    intro i
    have ht := ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 i).continuous.tendsto y).comp
      (measurableIntegral_tendsto C _ ⟨testVector, hx⟩)
    have heq : (fun n => (C.integral (truncation (fun i : ℕ => (2 : ℂ) ^ i) n) testVector) i)
        =ᶠ[atTop] (fun _ => (1 : ℂ)) := by
      filter_upwards [truncation_eventually_eq (fun i : ℕ => (2 : ℂ) ^ i) i] with n hn
      rw [integral_coordinate C (boundedMeasurable_truncation (measurable_of_countable _) n), hn]
      change (2 : ℂ) ^ i * (1 / 2 : ℂ) ^ i = 1
      rw [← mul_pow]
      norm_num
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' heq.symm)
  have hs := (lp.memℓp y).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  simp only [hy, norm_one, Real.one_rpow] at hs
  have ht := hs.tendsto_atTop_zero
  have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at this

end DiagonalExample

section Zero
variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : SpectralMeasure.ProjectionValuedMeasure S H} (C : BoundedRealization E)

theorem zero_domain : (measurableIntegral C (0 : S → ℂ)).domain = ⊤ := by
  apply top_unique
  intro x _
  apply (measurableIntegral_domain C (measurable_const : Measurable (0 : S → ℂ)) x).mpr
  change (∫⁻ _ : S, ENNReal.ofReal (‖(0 : ℂ)‖ ^ 2) ∂C.measure x) < ⊤
  simp

end Zero

/-- An explicit counterexample: g(n)=2ⁿ on the counting PVM of ℓ².
The vector x(n)=2⁻ⁿ is outside D(g(E)), so the zero first factor does
not turn the actual product into an everywhere-defined operator. -/
theorem strict_domain_example : Spec.StrictDomainExample := by
  obtain ⟨C⟩ := exists_boundedRealization DiagonalExample.pvm
  refine ⟨DiagonalExample.pvm, C, ?_⟩
  let g : ℕ → ℂ := fun n => (2 : ℂ) ^ n
  change Measurable g ∧ _
  have hg : Measurable g := measurable_of_countable g
  have hzero := zero_domain C
  have hproper : (measurableIntegral C g).domain ≠ ⊤ := by
    intro htop
    apply DiagonalExample.testVector_not_mem C
    rw [htop]
    trivial
  have hprod : (OperatorDomainsSpec.productValue (measurableIntegral C (0 : ℕ → ℂ))
      (measurableIntegral C g)).domain = (measurableIntegral C g).domain := by
    have h := (product_rule C 0 g measurable_const hg).1
    simpa only [zero_mul, hzero, inf_top_eq] using h
  refine ⟨hg, ?_, hproper, hprod, ?_, ?_⟩
  · intro M
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, by simpa [g, norm_pow] using hn⟩
  · simpa only [zero_mul] using hzero
  · rw [hprod, zero_mul, hzero]
    exact lt_top_iff_ne_top.mpr hproper

end ExpandedFA.Unbounded.SpectralProductAndSumDomains
