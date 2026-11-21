import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.RealSpectralProductAndSumDomains
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.RealMeasurableSpectralCalculus
import Mathlib.Analysis.Normed.Operator.Banach

set_option autoImplicit false

noncomputable section
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace ENNReal
namespace ExpandedFA.Unbounded.RealSpectralProductAndSumDomains
open ExpandedFA.SpectralMeasure RealMeasurableSpectralCalculus
universe u v
variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {E : RealProjectionValuedMeasure S H}

private theorem bounded_ext {a b : RealBoundedFunction S}
    (h : ∀ s, a s = b s) : a = b := by
  cases a; cases b; congr; exact funext h

theorem integral_commute (C : RealBoundedRealization E) (a b : RealBoundedFunction S) :
    C.integral a * C.integral b = C.integral b * C.integral a := by
  rw [← C.integral_mul, ← C.integral_mul]
  congr 1
  exact bounded_ext fun s => mul_comm _ _

/-- Bounded multipliers whose product with f is bounded yield actual graph
vectors, even when the symbol f is unbounded. -/
theorem bounded_multiplier_graph (C : RealBoundedRealization E)
    (f : S → ℝ) (hf : Measurable f) (a b : RealBoundedFunction S)
    (hab : ∀ s, f s * a s = b s) (x : H) :
    (C.integral a x, C.integral b x) ∈ (measurableIntegral C f hf).graph := by
  apply (graph_iff_cutoffs C f hf _ _).mpr
  intro n
  change (truncatedOperator C f hf n * C.integral a) x =
    (E (truncationSet f n) * C.integral b) x
  congr 1
  rw [truncatedOperator, ← C.integral_indicator _ (measurableSet_truncationSet hf n),
    ← C.integral_mul, ← C.integral_mul]
  congr 1
  apply bounded_ext
  intro s
  by_cases hs : s ∈ truncationSet f n <;>
    simp [RealBoundedFunction.mul, RealBoundedFunction.indicator, truncation, hs, hab s]

/-- The corresponding localized equation holds on every maximal graph vector. -/
theorem graph_multiplier_equation (C : RealBoundedRealization E)
    (f : S → ℝ) (hf : Measurable f) (a b : RealBoundedFunction S)
    (hab : ∀ s, f s * a s = b s) {x y : H}
    (hxy : (x, y) ∈ (measurableIntegral C f hf).graph) :
    C.integral a y = C.integral b x := by
  have heq (n : ℕ) : C.integral a * truncatedOperator C f hf n =
      E (truncationSet f n) * C.integral b := by
    rw [truncatedOperator, integral_commute]
    rw [ ← C.integral_indicator _ (measurableSet_truncationSet hf n),
      ← C.integral_mul, ← C.integral_mul]
    congr 1
    apply bounded_ext
    intro s
    by_cases hs : s ∈ truncationSet f n <;>
      simp [RealBoundedFunction.mul, RealBoundedFunction.indicator, truncation, hs, hab s]
  obtain ⟨z, hz, hzy⟩ := (measurableIntegral C f hf).mem_graph_iff.mp hxy
  change (z : H) = x at hz
  change measurableIntegral C f hf z = y at hzy
  have ht : Tendsto (fun n => truncatedOperator C f hf n x) atTop (𝓝 y) := by
    rw [← hz, ← hzy]
    exact truncations_converge C f hf z
  apply tendsto_nhds_unique (((C.integral a).continuous.tendsto y).comp ht)
  simpa only [Function.comp_def, ← mul_apply_eq_comp, heq] using
    (cutoff_tendsto C f hf (C.integral b x))

/-- Local graph equations for any strongly exhaustive family of bounded
multipliers characterize the maximal operator. -/
theorem graph_iff_localized (C : RealBoundedRealization E)
    (f : S → ℝ) (hf : Measurable f) (a b : ℕ → RealBoundedFunction S)
    (hab : ∀ n s, f s * a n s = b n s)
    (ha : ∀ x : H, Tendsto (fun n => C.integral (a n) x) atTop (𝓝 x))
    (x y : H) :
    (x, y) ∈ (measurableIntegral C f hf).graph ↔
      ∀ n, C.integral (a n) y = C.integral (b n) x := by
  constructor
  · intro h n
    exact graph_multiplier_equation C f hf (a n) (b n) (hab n) h
  · intro h
    apply (isClosed C f hf).mem_of_tendsto ((ha x).prodMk_nhds (ha y))
    exact Eventually.of_forall fun n => by
      rw [h n]
      exact bounded_multiplier_graph C f hf (a n) (b n) (hab n) x

/-- The common cutoff is bounded simultaneously for both symbols. -/
def jointCutoff (f g : S → ℝ) (hf : Measurable f) (hg : Measurable g)
    (n : ℕ) : RealBoundedFunction S :=
  .mul (.indicator (truncationSet f n) (measurableSet_truncationSet hf n))
    (.indicator (truncationSet g n) (measurableSet_truncationSet hg n))

def jointFirst (f g : S → ℝ) (hf : Measurable f) (hg : Measurable g)
    (n : ℕ) : RealBoundedFunction S :=
  .mul (truncation f hf n)
    (.indicator (truncationSet g n) (measurableSet_truncationSet hg n))

def jointSecond (f g : S → ℝ) (hf : Measurable f) (hg : Measurable g)
    (n : ℕ) : RealBoundedFunction S :=
  .mul (.indicator (truncationSet f n) (measurableSet_truncationSet hf n))
    (truncation g hg n)

def jointProduct (f g : S → ℝ) (hf : Measurable f) (hg : Measurable g)
    (n : ℕ) : RealBoundedFunction S :=
  .mul (truncation f hf n) (truncation g hg n)

private theorem joint_identities (f g : S → ℝ) (hf : Measurable f)
    (hg : Measurable g) (n : ℕ) (s : S) :
    f s * jointCutoff f g hf hg n s = jointFirst f g hf hg n s ∧
    g s * jointCutoff f g hf hg n s = jointSecond f g hf hg n s ∧
    (f s * g s) * jointCutoff f g hf hg n s = jointProduct f g hf hg n s ∧
    g s * jointFirst f g hf hg n s = jointProduct f g hf hg n s ∧
    f s * jointSecond f g hf hg n s = jointProduct f g hf hg n s := by
  by_cases hfs : s ∈ truncationSet f n <;>
    by_cases hgs : s ∈ truncationSet g n <;>
    simp [jointCutoff, jointFirst, jointSecond, jointProduct,
      RealBoundedFunction.mul, RealBoundedFunction.indicator, truncation, hfs, hgs,
      mul_comm]

theorem jointCutoff_tendsto (C : RealBoundedRealization E)
    (f g : S → ℝ) (hf : Measurable f) (hg : Measurable g) (x : H) :
    Tendsto (fun n => C.integral (jointCutoff f g hf hg n) x) atTop (𝓝 x) := by
  let a := jointCutoff f g hf hg
  let d : ℕ → RealBoundedFunction S := fun n => .add (a n) (.const (-1))
  have hb : ∀ n s, |d n s| ≤ 1 := by
    intro n s
    by_cases hfs : s ∈ truncationSet f n <;>
      by_cases hgs : s ∈ truncationSet g n <;>
      simp [d, a, jointCutoff, RealBoundedFunction.add, RealBoundedFunction.mul,
        RealBoundedFunction.indicator, RealBoundedFunction.const, hfs, hgs]
  have hl : ∀ s, Tendsto (fun n => d n s) atTop (𝓝 0) := by
    intro s
    obtain ⟨N, hN⟩ := exists_nat_gt (max |f s| |g s|)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hbound : max |f s| |g s| ≤ (n : ℝ) := hN.le.trans (by exact_mod_cast hn)
    have hfs : s ∈ truncationSet f n := (le_max_left _ _).trans hbound
    have hgs : s ∈ truncationSet g n := (le_max_right _ _).trans hbound
    simp [d, a, jointCutoff, RealBoundedFunction.add, RealBoundedFunction.mul,
      RealBoundedFunction.indicator, RealBoundedFunction.const, hfs, hgs]
  have h := bounded_integrals_tendsto_zero C d 1 zero_le_one hb hl x
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply tendsto_zero_iff_norm_tendsto_zero.mp
  simpa only [d, C.integral_add, C.integral_const, _root_.add_apply,
    smul_apply, one_apply_eq_self,
    neg_one_smul, ← sub_eq_add_neg, sub_apply] using h

theorem product_graph_iff (A B : Operator ℝ H H) (x z : H) :
    (x, z) ∈ (OperatorDomainsSpec.productValue A B).graph ↔
    ∃ y, (x, y) ∈ B.graph ∧ (y, z) ∈ A.graph := by
  constructor
  · rintro h
    obtain ⟨w, hw, hwz⟩ := (OperatorDomainsSpec.productValue A B).mem_graph_iff.mp h
    change (w : H) = x at hw
    let v : B.domain := ⟨w, w.property.choose⟩
    refine ⟨B v, ?_, ?_⟩
    · exact B.mem_graph_iff.mpr ⟨v, hw, rfl⟩
    · exact A.mem_graph_iff.mpr ⟨⟨B v, w.property.choose_spec⟩, rfl, hwz⟩
  · rintro ⟨y, hy, hz⟩
    obtain ⟨v, hv, hvy⟩ := B.mem_graph_iff.mp hy
    obtain ⟨w, hw, hwz⟩ := A.mem_graph_iff.mp hz
    change (v : H) = x at hv
    change (w : H) = y at hw
    change B v = y at hvy
    change A w = z at hwz
    have hBy : B v ∈ A.domain := by rw [hvy, ← hw]; exact w.property
    let t : (OperatorDomainsSpec.productValue A B).domain := ⟨v, ⟨v.property, hBy⟩⟩
    refine (OperatorDomainsSpec.productValue A B).mem_graph_iff.mpr ⟨t, hv, ?_⟩
    change A _ = z
    rw [← hwz]
    apply congrArg A
    apply Subtype.ext
    exact hvy.trans hw.symm

/-- On D(g(E)), the two possible output graph conditions are equivalent. -/
theorem product_graph_equivalence (C : RealBoundedRealization E)
    (f g : S → ℝ) (hf : Measurable f) (hg : Measurable g) {x y z : H}
    (hxy : (x, y) ∈ (measurableIntegral C g hg).graph) :
    (y, z) ∈ (measurableIntegral C f hf).graph ↔
    (x, z) ∈ (measurableIntegral C (fun s => f s * g s) (hf.mul hg)).graph := by
  let a := jointCutoff f g hf hg
  let b := jointFirst f g hf hg
  let c := jointProduct f g hf hg
  have ha := jointCutoff_tendsto C f g hf hg
  have hab := fun n s => (joint_identities f g hf hg n s).1
  have hac := fun n s => (joint_identities f g hf hg n s).2.2.1
  have hbc := fun n s => (joint_identities f g hf hg n s).2.2.2.1
  rw [graph_iff_localized C f hf a b hab ha,
    graph_iff_localized C (fun s => f s * g s) (hf.mul hg) a c hac ha]
  have he (n : ℕ) : C.integral (b n) y = C.integral (c n) x :=
    graph_multiplier_equation C g hg (b n) (c n) (hbc n) hxy
  simp_rw [he]

theorem product_law (C : RealBoundedRealization E)
    (f g : S → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Spec.ProductLaw C f g hf hg := by
  let A := measurableIntegral C f hf
  let B := measurableIntegral C g hg
  let P := measurableIntegral C (fun s => f s * g s) (hf.mul hg)
  have he (x y z : H) (hxy : (x, y) ∈ B.graph) :
      (y, z) ∈ A.graph ↔ (x, z) ∈ P.graph :=
    product_graph_equivalence C f g hf hg hxy
  have hle : OperatorDomainsSpec.productValue A B ≤ P := by
    apply LinearPMap.le_of_le_graph
    intro p hp
    obtain ⟨y, hxy, hyz⟩ := (product_graph_iff A B p.1 p.2).mp hp
    exact (he _ _ _ hxy).mp hyz
  refine ⟨?_, hle⟩
  apply Submodule.ext
  intro x
  constructor
  · intro h
    exact ⟨h.choose, hle.1 h⟩
  · rintro ⟨hx, hp⟩
    have hBy : B ⟨x, hx⟩ ∈ A.domain := by
      apply LinearPMap.mem_domain_of_mem_graph
      exact (he x (B ⟨x, hx⟩) (P ⟨x, hp⟩) (B.mem_graph ⟨x, hx⟩)).mpr
        (P.mem_graph ⟨x, hp⟩)
    exact ⟨hx, hBy⟩

/-- A closed extension is the graph closure whenever its graph is approximated
by graph vectors of the original partial map. -/
theorem closure_eq_of_graph_approx (A B : Operator ℝ H H)
    (hB : B.IsClosed) (hle : A ≤ B)
    (happrox : ∀ p ∈ B.graph, p ∈ _root_.closure (A.graph : Set (H × H))) :
    A.IsClosable ∧ A.closure = B := by
  have hc := hB.isClosable.leIsClosable hle
  refine ⟨hc, LinearPMap.eq_of_eq_graph ?_⟩
  rw [← hc.graph_closure_eq_closure_graph]
  apply le_antisymm
  · exact A.graph.topologicalClosure_minimal (LinearPMap.le_graph_of_le hle) hB
  · exact happrox

/-- Simultaneous cutoffs are a graph core for the maximal product symbol. -/
theorem product_closure (C : RealBoundedRealization E)
    (f g : S → ℝ) (hf : Measurable f) (hg : Measurable g) :
    (OperatorDomainsSpec.productValue (measurableIntegral C f hf)
      (measurableIntegral C g hg)).IsClosable ∧
    (OperatorDomainsSpec.productValue (measurableIntegral C f hf)
      (measurableIntegral C g hg)).closure =
        measurableIntegral C (fun s => f s * g s) (hf.mul hg) := by
  let A := measurableIntegral C f hf
  let B := measurableIntegral C g hg
  let P := measurableIntegral C (fun s => f s * g s) (hf.mul hg)
  apply closure_eq_of_graph_approx _ P (isClosed C _ _) (product_law C f g hf hg).2
  rintro ⟨x, y⟩ hxy
  have hlim := (jointCutoff_tendsto C f g hf hg x).prodMk_nhds
    (jointCutoff_tendsto C f g hf hg y)
  apply mem_closure_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  let a := jointCutoff f g hf hg n
  let b := jointSecond f g hf hg n
  let c := jointProduct f g hf hg n
  have hab := fun s => (joint_identities f g hf hg n s).2.1
  have hbc := fun s => (joint_identities f g hf hg n s).2.2.2.2
  have hac := fun s => (joint_identities f g hf hg n s).2.2.1
  have heq := graph_multiplier_equation C _ (hf.mul hg) a c hac hxy
  rw [heq]
  exact (product_graph_iff A B _ _).mpr ⟨C.integral b x,
    bounded_multiplier_graph C g hg a b hab x,
    bounded_multiplier_graph C f hf b c hbc x⟩

theorem sum_inclusion (C : RealBoundedRealization E)
    (f g : S → ℝ) (hf : Measurable f) (hg : Measurable g) :
    measurableIntegral C f hf + measurableIntegral C g hg ≤
      measurableIntegral C (fun s => f s + g s) (hf.add hg) := by
  apply LinearPMap.le_of_le_graph
  rintro ⟨x, y⟩ hxy
  obtain ⟨w, hw, hwy⟩ := (measurableIntegral C f hf +
    measurableIntegral C g hg).mem_graph_iff.mp hxy
  change (w : H) = x at hw
  change (measurableIntegral C f hf + measurableIntegral C g hg) w = y at hwy
  rw [← hw, ← hwy]
  let a := jointCutoff f g hf hg
  let b := jointFirst f g hf hg
  let c := jointSecond f g hf hg
  have hab := fun n s => (joint_identities f g hf hg n s).1
  have hac := fun n s => (joint_identities f g hf hg n s).2.1
  have had (n : ℕ) (s : S) : (f s + g s) * a n s =
      (RealBoundedFunction.add (b n) (c n)) s := by
    change _ = b n s + c n s
    rw [add_mul, hab, hac]
  apply (graph_iff_localized C _ (hf.add hg) a
    (fun n => .add (b n) (c n)) had (jointCutoff_tendsto C f g hf hg) _ _).mpr
  intro n
  rw [LinearPMap.add_apply, map_add, C.integral_add, _root_.add_apply]
  congr 1
  · exact graph_multiplier_equation C f hf (a n) (b n) (hab n)
      ((measurableIntegral C f hf).mem_graph ⟨w, w.property.1⟩)
  · exact graph_multiplier_equation C g hg (a n) (c n) (hac n)
      ((measurableIntegral C g hg).mem_graph ⟨w, w.property.2⟩)

/-- The raw sum lives on the intersection domain; its closure has the full
sum-symbol domain. No equality of those two raw domains is asserted. -/
theorem sum_closure (C : RealBoundedRealization E)
    (f g : S → ℝ) (hf : Measurable f) (hg : Measurable g) :
    (measurableIntegral C f hf + measurableIntegral C g hg).IsClosable ∧
    (measurableIntegral C f hf + measurableIntegral C g hg).closure =
      measurableIntegral C (fun s => f s + g s) (hf.add hg) := by
  let A := measurableIntegral C f hf
  let B := measurableIntegral C g hg
  let P := measurableIntegral C (fun s => f s + g s) (hf.add hg)
  apply closure_eq_of_graph_approx _ P (isClosed C _ _) (sum_inclusion C f g hf hg)
  rintro ⟨x, y⟩ hxy
  have hlim := (jointCutoff_tendsto C f g hf hg x).prodMk_nhds
    (jointCutoff_tendsto C f g hf hg y)
  apply mem_closure_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  let a := jointCutoff f g hf hg n
  let b := jointFirst f g hf hg n
  let c := jointSecond f g hf hg n
  have hab := fun s => (joint_identities f g hf hg n s).1
  have hac := fun s => (joint_identities f g hf hg n s).2.1
  have had (s : S) : (f s + g s) * a s = (RealBoundedFunction.add b c) s := by
    change _ = b s + c s
    rw [add_mul, hab, hac]
  have heq := graph_multiplier_equation C _ (hf.add hg) a (.add b c) had hxy
  rw [heq, C.integral_add, _root_.add_apply]
  have hb := bounded_multiplier_graph C f hf a b hab x
  have hc := bounded_multiplier_graph C g hg a c hac x
  have hbd := LinearPMap.mem_domain_of_mem_graph hb
  have hcd := LinearPMap.mem_domain_of_mem_graph hc
  refine (A + B).mem_graph_iff.mpr ⟨⟨C.integral a x, hbd, hcd⟩, rfl, ?_⟩
  rw [LinearPMap.add_apply]
  congr 1
  · exact (LinearPMap.image_iff hbd).mpr hb |>.symm
  · exact (LinearPMap.image_iff hcd).mpr hc |>.symm

theorem product_theorem : Spec.ProductTheorem.{u,v} := by
  intro S H _ _ _ _ E C f g hf hg
  exact product_law C f g hf hg

theorem closure_theorem : Spec.ClosureTheorem.{u,v} := by
  intro S H _ _ _ _ E C f g hf hg
  exact ⟨(product_closure C f g hf hg).1, (product_closure C f g hf hg).2,
    (sum_closure C f g hf hg).1, (sum_closure C f g hf hg).2⟩

namespace Diagonal
abbrev Hilbert := lp (fun _ : ℕ => ℝ) 2

/-- Coordinate projection onto an arbitrary subset of the natural numbers. -/
def mask (B : Set ℕ) (x : Hilbert) : Hilbert := by
  classical
  refine ⟨B.indicator x, (lp.memℓp x).mono' ?_⟩
  intro n
  by_cases hn : n ∈ B <;> simp [hn]

@[simp] theorem mask_apply (B : Set ℕ) (x : Hilbert) (n : ℕ) :
    mask B x n = B.indicator x n := rfl

def projection (B : Set ℕ) : Hilbert →L[ℝ] Hilbert := by
  classical
  refine LinearMap.mkContinuous
    { toFun := mask B
      map_add' := by
        intro x y
        apply Subtype.ext
        change B.indicator ((x : ℕ → ℝ) + (y : ℕ → ℝ)) = B.indicator x + B.indicator y
        exact Set.indicator_add _ _ _
      map_smul' := by
        intro c x
        apply Subtype.ext
        funext n
        change B.indicator (fun k => c * x k) n = c * B.indicator x n
        by_cases hn : n ∈ B <;> simp [hn] }
    1 ?_
  intro x
  simp only [one_mul]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  by_cases hn : n ∈ B <;> simp [mask, hn]

@[simp] theorem projection_apply (B : Set ℕ) (x : Hilbert) (n : ℕ) :
    projection B x n = B.indicator x n := rfl

/-- Regrouping the unconditional coordinate expansion along an injection. -/
theorem hasSum_injective {ι : Type*} (j : ι → ℕ) (hj : Function.Injective j)
    (x : Hilbert) :
    HasSum (fun i => lp.single (E := fun _ : ℕ => ℝ) 2 (j i) (x (j i))) (mask (Set.range j) x) := by
  classical
  have hs := ((lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x).summable).comp_injective hj
  have he : (∑' i, lp.single (E := fun _ : ℕ => ℝ) 2 (j i) (x (j i))) = mask (Set.range j) x := by
    apply Subtype.ext
    funext k
    have hev := (hs.hasSum.map (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 k)
      (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 k).continuous).tsum_eq
    change (∑' i, (lp.single (E := fun _ : ℕ => ℝ) 2 (j i) (x (j i))) k) = (∑' i, lp.single (E := fun _ : ℕ => ℝ) 2 (j i) (x (j i))) k at hev
    rw [← hev]
    by_cases hk : k ∈ Set.range j
    · obtain ⟨i, rfl⟩ := hk
      rw [tsum_eq_single i]
      · simp [mask]
      · intro b hbi
        exact lp.single_apply_ne _ _ _ (fun h => hbi (hj h).symm)
    · have hzero (i : ι) : (lp.single (E := fun _ : ℕ => ℝ) 2 (j i) (x (j i))) k = 0 :=
        lp.single_apply_ne _ _ _ (fun h => hk ⟨i, h.symm⟩)
      simp only [hzero, tsum_zero]
      simp [mask, hk]
  exact he ▸ hs.hasSum

/-- The diagonal PVM on the actual real sequence Hilbert space. -/
def pvm : RealProjectionValuedMeasure ℕ Hilbert where
  toFun := projection
  univ := by ext x n; simp
  selfAdjoint B _ x y := by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    congr 1
    funext n
    classical
    by_cases hn : n ∈ B <;> simp [hn]
  inter B D _ _ := by
    ext x n
    classical
    by_cases hb : n ∈ B <;> by_cases hd : n ∈ D <;>
      simp [mul_apply_eq_comp, hb, hd]
  countablyAdditive B _ hB x := by
    classical
    let j : (Σ i, B i) → ℕ := fun p => p.2
    have hj : Function.Injective j := by
      rintro ⟨i, n⟩ ⟨k, m⟩ hnm
      change (n : ℕ) = (m : ℕ) at hnm
      have hik : i = k := by
        by_contra h
        exact Set.disjoint_left.mp (hB h) n.property (by rw [hnm]; exact m.property)
      subst k
      exact congrArg (Sigma.mk i) (Subtype.ext hnm)
    have hr : Set.range j = ⋃ i, B i := by
      ext n
      simp [j]
    have htotal := hasSum_injective j hj x
    rw [hr] at htotal
    have hblock (i : ℕ) : HasSum
        (fun n : B i => lp.single 2 (n : ℕ) (x n)) (mask (B i) x) := by
      have h := hasSum_injective (fun n : B i => (n : ℕ)) Subtype.val_injective x
      simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using h
    exact htotal.sigma hblock

/-- Every bounded realization of the diagonal PVM acts diagonally on the
coordinate vectors. This identifies the realization actually used below. -/
theorem integral_single (C : RealBoundedRealization pvm) (a : RealBoundedFunction ℕ)
    (n : ℕ) (c : ℝ) :
    C.integral a (lp.single 2 n c) = a n • (lp.single 2 n c : Hilbert) := by
  classical
  let b : RealBoundedFunction ℕ := .indicator {n} (measurableSet_singleton n)
  have hb : C.integral b (lp.single 2 n c) = (lp.single 2 n c : Hilbert) := by
    rw [show b = .indicator {n} (measurableSet_singleton n) from rfl, C.integral_indicator]
    apply Subtype.ext
    funext k
    change ({n} : Set ℕ).indicator (lp.single 2 n c : Hilbert) k = (lp.single 2 n c : Hilbert) k
    by_cases hk : k = n
    · simp [hk]
    · simp [hk]
  have hab : RealBoundedFunction.mul a b = RealBoundedFunction.smul (a n) b := by
    apply bounded_ext
    intro k
    by_cases hk : k = n <;>
      simp [RealBoundedFunction.mul, RealBoundedFunction.smul, b,
        RealBoundedFunction.indicator, hk]
  calc
    _ = (C.integral a * C.integral b) (lp.single 2 n c) := by rw [mul_apply_eq_comp, hb]
    _ = C.integral (.mul a b) (lp.single 2 n c) := by rw [C.integral_mul]
    _ = _ := by rw [hab, C.integral_smul, smul_apply, hb]

/-- Coordinate vectors are in the maximal domain for every finite symbol. -/
theorem single_graph (C : RealBoundedRealization pvm) (g : ℕ → ℝ)
    (hg : Measurable g) (n : ℕ) (c : ℝ) :
    ((lp.single 2 n c : Hilbert), g n • (lp.single 2 n c : Hilbert)) ∈
      (measurableIntegral C g hg).graph := by
  have ht : Tendsto (fun m => truncatedOperator C g hg m (lp.single 2 n c)) atTop
      (𝓝 (g n • (lp.single 2 n c : Hilbert))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [truncation_eventually_at g hg n] with m hm
    rw [truncatedOperator, integral_single, hm]
  have hx : (lp.single 2 n c : Hilbert) ∈ (measurableIntegral C g hg).domain :=
    ⟨_, ht⟩
  exact (measurableIntegral C g hg).mem_graph_iff.mpr
    ⟨⟨_, hx⟩, rfl, tendsto_nhds_unique (truncations_converge C g hg ⟨_, hx⟩) ht⟩

/-- A full domain would make the closed diagonal operator bounded, contradicting
its unbounded sequence of eigenvalues. No assumed proper-domain certificate is
used to construct the example. -/
theorem natural_domain_proper (C : RealBoundedRealization pvm) :
    (measurableIntegral C (fun n : ℕ => (n : ℝ)) (measurable_of_countable _)).domain ≠ ⊤ := by
  let g : ℕ → ℝ := fun n => n
  let hg : Measurable g := measurable_of_countable _
  let A := measurableIntegral C g hg
  intro hfull
  have hall (x : Hilbert) : x ∈ A.domain := by rw [hfull]; trivial
  let inc : Hilbert →ₗ[ℝ] A.domain :=
    { toFun := fun x => ⟨x, hall x⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  let T : Hilbert →ₗ[ℝ] Hilbert := A.toFun.comp inc
  have hgraph : T.graph = A.graph := by
    ext p
    rw [LinearMap.mem_graph_iff]
    constructor
    · intro h
      exact A.mem_graph_iff.mpr ⟨inc p.1, rfl, h.symm⟩
    · intro h
      obtain ⟨w, hw, hwy⟩ := A.mem_graph_iff.mp h
      change (w : Hilbert) = p.1 at hw
      change A w = p.2 at hwy
      have he : w = inc p.1 := Subtype.ext hw
      simpa only [T, LinearMap.comp_apply, ← he, LinearPMap.toFun_eq_coe] using hwy.symm
  have hT : _root_.IsClosed (T.graph : Set (Hilbert × Hilbert)) := by
    rw [hgraph]
    exact isClosed C g hg
  let L : Hilbert →L[ℝ] Hilbert := ContinuousLinearMap.ofIsClosedGraph hT
  obtain ⟨n, hn⟩ := exists_nat_gt ‖L‖
  have heigen : L (lp.single 2 n 1) = (n : ℝ) • (lp.single 2 n 1 : Hilbert) := by
    have hs := single_graph C g hg n 1
    have hm := A.mem_graph (inc (lp.single 2 n 1))
    exact A.mem_graph_snd_inj hm hs rfl
  have hb := L.le_opNorm (lp.single 2 n 1)
  rw [heigen, norm_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] at hb
  simp only [Real.norm_natCast, norm_one, mul_one] at hb
  exact (not_le_of_gt hn) hb
end Diagonal

/-- The zero symbol has full domain and the actual zero bounded value. -/
theorem zero_integral (C : RealBoundedRealization E) :
    measurableIntegral C (fun _ : S => (0 : ℝ)) measurable_const =
      (0 : H →L[ℝ] H).toLinearMap.toPMap ⊤ := by
  have h := bounded_agreement C (RealBoundedFunction.const (S := S) 0)
  rw [C.integral_const, zero_smul] at h
  exact h

/-- An actual real ℓ² PVM with a dense proper domain and strict product-domain
inclusion, using the everywhere finite symbol g(n)=n and the bounded symbol 0. -/
theorem strictness : Spec.Strictness := by
  let E := Diagonal.pvm
  let C := E.boundedRealization
  let g : ℕ → ℝ := fun n => n
  let hg : Measurable g := measurable_of_countable _
  let Z := measurableIntegral C (fun _ : ℕ => (0 : ℝ)) measurable_const
  let B := measurableIntegral C g hg
  let P := measurableIntegral C (fun n => (0 : ℝ) * g n) (measurable_const.mul hg)
  have hZ : Z = (0 : Diagonal.Hilbert →L[ℝ] Diagonal.Hilbert).toLinearMap.toPMap ⊤ :=
    zero_integral C
  have hP : P = (0 : Diagonal.Hilbert →L[ℝ] Diagonal.Hilbert).toLinearMap.toPMap ⊤ := by
    have he : (fun n => (0 : ℝ) * g n) = (fun _ : ℕ => (0 : ℝ)) := by simp
    change measurableIntegral C _ _ = _
    simpa only [zero_mul] using (zero_integral C)
  have hBd : B.domain ≠ ⊤ := Diagonal.natural_domain_proper C
  have hPd : P.domain = ⊤ := congrArg LinearPMap.domain hP
  have hZd : Z.domain = ⊤ := congrArg LinearPMap.domain hZ
  have hdom : (OperatorDomainsSpec.productValue Z B).domain = B.domain := by
    have h := (product_law C (fun _ : ℕ => (0 : ℝ)) g measurable_const hg).1
    change (OperatorDomainsSpec.productValue Z B).domain = B.domain ⊓ P.domain at h
    exact h.trans (by rw [hPd, inf_top_eq])
  refine ⟨E, C, g, hg, densely_defined C g hg, hBd, hZd, hdom, hP, ?_⟩
  change (OperatorDomainsSpec.productValue Z B).domain < P.domain
  rw [hdom, hPd]
  exact lt_top_iff_ne_top.mpr hBd

/-- The full real unbounded calculus theorem, retaining arbitrary measurable
bases, arbitrary given bounded realizations, and zero/empty cases. -/
theorem complete_theorem : Spec.CompleteTheorem.{u,v} :=
  ⟨calculus_for_every_realization, product_theorem, closure_theorem, strictness⟩

end ExpandedFA.Unbounded.RealSpectralProductAndSumDomains
