import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HausdorffGraphArea
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Convert

noncomputable section
open MeasureTheory Set Metric Module Filter
open scoped Topology
open scoped ENNReal NNReal InnerProductSpace

namespace ExpandedFA.HausdorffGraphArea

@[simp] theorem graphMap_castSucc {n : ℕ} (g : E n → ℝ) (x : E n) (i : Fin n) :
    graphMap g x i.castSucc = x i := by simp [graphMap]

@[simp] theorem graphMap_last {n : ℕ} (g : E n → ℝ) (x : E n) :
    graphMap g x (Fin.last n) = g x := by simp [graphMap]

theorem graphMap_injective {n : ℕ} (g : E n → ℝ) : Function.Injective (graphMap g) := by
  intro x y h
  ext i
  have := congrArg (fun z : E (n + 1) => z i.castSucc) h
  simpa using this

theorem continuousOn_graphMap {n : ℕ} {U : Set (E n)} {g : E n → ℝ}
    (hg : ContinuousOn g U) : ContinuousOn (graphMap g) U := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp_continuousOn
  apply continuousOn_pi.2
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hg
  · simpa using (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).continuousOn

theorem measurable_graph_image : Specs.MeasurableGraphImage := by
  intro n U g _ hg s hs hsU
  exact hs.image_of_continuousOn_injOn
    ((continuousOn_graphMap hg.continuousOn).mono hsU) (graphMap_injective g).injOn

section GeneralArea
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace W] [BorelSpace W]

omit [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W] in
/-- Continuity of the rectangular volume factor. -/
theorem continuous_normDet : Continuous (fun A : V →L[ℝ] W => A.normDet) := by
  have heq : (fun A : V →L[ℝ] W => A.normDet) =
      fun A => Real.sqrt ((A.adjoint.comp A).det) := by
    funext A
    simpa only [RCLike.ofReal_real_eq_id, id_eq, Real.sqrt_sq A.toLinearMap.normDet_nonneg] using
      congrArg Real.sqrt A.normDet_sq.symm |>.symm
  rw [heq]
  exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
    ((ContinuousLinearMap.adjoint : (V →L[ℝ] W) ≃ₗᵢ⋆[ℝ] (W →L[ℝ] V)).continuous.clm_comp continuous_id))

omit [FiniteDimensional ℝ W] in
/-- Comparison with a tangent graph. Both graphs have the same contractive left inverse. -/
theorem hausdorffMeasure_image_comparison {f : V → W} {A : V →L[ℝ] W}
    {P : W →L[ℝ] V} {s : Set V} {ε : ℝ≥0}
    (hP : ∀ z, ‖P z‖ ≤ ‖z‖) (hPf : ∀ x ∈ s, P (f x) = x)
    (hPA : ∀ x, P (A x) = x) (happrox : ApproximatesLinearOn f A s ε) :
    Measure.hausdorffMeasure (finrank ℝ V : ℝ) (f '' s) ≤
        (↑(1 + ε) : ℝ≥0∞) ^ (finrank ℝ V) *
          (ENNReal.ofReal A.normDet * Measure.hausdorffMeasure (finrank ℝ V : ℝ) s) ∧
    ENNReal.ofReal A.normDet * Measure.hausdorffMeasure (finrank ℝ V : ℝ) s ≤
        (↑(1 + ε) : ℝ≥0∞) ^ (finrank ℝ V) *
          Measure.hausdorffMeasure (finrank ℝ V : ℝ) (f '' s) := by
  have hn : ∀ x y, ‖x - y‖ ≤ ‖A x - A y‖ := by
    intro x y
    simpa only [map_sub, hPA] using hP (A x - A y)
  have hn' : ∀ x ∈ s, ∀ y ∈ s, ‖x - y‖ ≤ ‖f x - f y‖ := by
    intro x hx y hy
    simpa only [map_sub, hPf x hx, hPf y hy] using hP (f x - f y)
  have h₁ : LipschitzOnWith (1 + ε) (f ∘ P) (A '' s) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, hPA, NNReal.coe_add, NNReal.coe_one]
    calc
      ‖f x - f y‖ ≤ ‖A (x - y)‖ + ‖f x - f y - A (x - y)‖ := by
        simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub (A (x - y)) (f x - f y)
      _ ≤ ‖A x - A y‖ + ε * ‖x - y‖ := by
        exact add_le_add (by simp [map_sub]) (by simpa only [map_sub] using happrox x hx y hy)
      _ ≤ (1 + ↑ε) * ‖A x - A y‖ := by nlinarith [hn x y, ε.coe_nonneg]
  have h₂ : LipschitzOnWith (1 + ε) (A ∘ P) (f '' s) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, hPf x hx, hPf y hy, NNReal.coe_add, NNReal.coe_one]
    calc
      ‖A x - A y‖ ≤ ‖f x - f y‖ + ‖f x - f y - A (x - y)‖ := by
        rw [← map_sub]
        simpa [norm_sub_rev] using norm_le_norm_add_norm_sub (f x - f y) (A (x - y))
      _ ≤ ‖f x - f y‖ + ε * ‖x - y‖ := by gcongr; exact happrox x hx y hy
      _ ≤ (1 + ↑ε) * ‖f x - f y‖ := by nlinarith [hn' x hx y hy, ε.coe_nonneg]
  have himg₁ : (f ∘ P) '' (A '' s) = f '' s := by
    ext z
    simp only [Set.mem_image, Function.comp_apply]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, by rw [hPA]⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨A x, ⟨x, hx, rfl⟩, by rw [hPA]⟩
  have himg₂ : (A ∘ P) '' (f '' s) = A '' s := by
    ext z
    simp only [Set.mem_image, Function.comp_apply]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, by rw [hPf x hx]⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨f x, ⟨x, hx, rfl⟩, by rw [hPf x hx]⟩
  have hlin : Measure.hausdorffMeasure (finrank ℝ V : ℝ) (A '' s) =
      ENNReal.ofReal A.normDet * Measure.hausdorffMeasure (finrank ℝ V : ℝ) s :=
    A.toLinearMap.hausdorffMeasure_image s
  constructor
  · have h := h₁.hausdorffMeasure_image_le (d := (finrank ℝ V : ℝ)) (by positivity)
    rw [himg₁, ENNReal.rpow_natCast, hlin] at h
    exact h
  · have h := h₂.hausdorffMeasure_image_le (d := (finrank ℝ V : ℝ)) (by positivity)
    rw [himg₂, ENNReal.rpow_natCast, hlin] at h
    exact h

omit [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] in
/-- Assemble local comparisons using a countable disjoint Borel partition. -/
theorem area_bounds_of_local_bounds {f : V → W} {U s : Set V} {J : V → ℝ≥0∞}
    {c : ℝ≥0∞} (hf : ContinuousOn f U) (hi : InjOn f U)
    (hs : MeasurableSet s) (hsU : s ⊆ U)
    (hloc : ∀ x ∈ U, ∃ t : Set V, IsOpen t ∧ x ∈ t ∧
      ∀ a : Set V, MeasurableSet a → a ⊆ U ∩ t →
        Measure.hausdorffMeasure (finrank ℝ V : ℝ) (f '' a) ≤
            c * ∫⁻ x in a, J x ∂(Measure.hausdorffMeasure (finrank ℝ V : ℝ)) ∧
        (∫⁻ x in a, J x ∂(Measure.hausdorffMeasure (finrank ℝ V : ℝ))) ≤
            c * Measure.hausdorffMeasure (finrank ℝ V : ℝ) (f '' a)) :
    Measure.hausdorffMeasure (finrank ℝ V : ℝ) (f '' s) ≤
        c * ∫⁻ x in s, J x ∂(Measure.hausdorffMeasure (finrank ℝ V : ℝ)) ∧
    (∫⁻ x in s, J x ∂(Measure.hausdorffMeasure (finrank ℝ V : ℝ))) ≤
        c * Measure.hausdorffMeasure (finrank ℝ V : ℝ) (f '' s) := by
  classical
  by_cases hU : U.Nonempty
  · have : Nonempty U := hU.to_subtype
    choose t hto hxt ht using fun x : U => hloc x x.2
    obtain ⟨k, hk⟩ := (IsLindelof.of_coe (s := U)).indexed_countable_subcover t hto (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxt ⟨x, hx⟩⟩)
    let b : ℕ → Set V := fun n => s ∩ disjointed (fun n => t (k n)) n
    have hb : ∀ n, MeasurableSet (b n) := fun n =>
      hs.inter (MeasurableSet.disjointed (fun n => (hto (k n)).measurableSet) n)
    have hbU : ∀ n, b n ⊆ U := fun _ _ hx => hsU hx.1
    have hbt : ∀ n, b n ⊆ U ∩ t (k n) := fun n _ hx =>
      ⟨hsU hx.1, disjointed_subset (fun n => t (k n)) n hx.2⟩
    have hbdisj : Pairwise (fun i j => Disjoint (b i) (b j)) := by
      intro i j hij
      exact (disjoint_disjointed (fun n => t (k n)) hij).mono inter_subset_right inter_subset_right
    have hsb : s = ⋃ n, b n := by
      simp only [b, ← inter_iUnion, iUnion_disjointed]
      exact (inter_eq_left.mpr (hsU.trans hk)).symm
    have hfmb : ∀ n, MeasurableSet (f '' b n) := fun n =>
      (hb n).image_of_continuousOn_injOn (hf.mono (hbU n)) (hi.mono (hbU n))
    have hfdisj : Pairwise (fun i j => Disjoint (f '' b i) (f '' b j)) := by
      intro i j hij
      rw [Set.disjoint_left]
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
      have he : y = x := hi (hbU j hy) (hbU i hx) heq
      subst y
      exact Set.disjoint_left.mp (hbdisj hij) hx hy
    have harea : Measure.hausdorffMeasure (finrank ℝ V : ℝ) (f '' s) =
        ∑' n, Measure.hausdorffMeasure (finrank ℝ V : ℝ) (f '' b n) := by
      rw [hsb, image_iUnion, measure_iUnion hfdisj hfmb]
    have hint : (∫⁻ x in s, J x ∂(Measure.hausdorffMeasure (finrank ℝ V : ℝ))) =
        ∑' n, ∫⁻ x in b n, J x ∂(Measure.hausdorffMeasure (finrank ℝ V : ℝ)) := by
      rw [hsb, lintegral_iUnion hb hbdisj]
    rw [harea, hint, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    exact ⟨ENNReal.tsum_le_tsum (fun n => (ht (k n) (b n) (hb n) (hbt n)).1),
      ENNReal.tsum_le_tsum (fun n => (ht (k n) (b n) (hb n) (hbt n)).2)⟩
  · have : s = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx => hU ⟨x, hsU hx⟩
    simp [this]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
  [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W] in
/-- Differentiating the common projection identity preserves the left inverse. -/
theorem projection_fderiv {f : V → W} {U : Set V} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {P : W →L[ℝ] V}
    (hPf : ∀ x ∈ U, P (f x) = x) {x : V} (hx : x ∈ U) :
    ∀ v, P (fderiv ℝ f x v) = v := by
  have hd := (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hh := (P.hasFDerivAt.comp x hd.hasFDerivAt).congr_of_eventuallyEq
    (Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => (hPf y hy).symm))
  have he := hh.unique (hasFDerivAt_id x)
  exact fun v => congrArg (fun A : V →L[ℝ] V => A v) he

/-- Quantitative area comparison, with an arbitrarily small multiplicative error. -/
theorem graph_area_bounds {f : V → W} {U s : Set V} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {P : W →L[ℝ] V}
    (hP : ∀ z, ‖P z‖ ≤ ‖z‖) (hPf : ∀ x ∈ U, P (f x) = x)
    (hs : MeasurableSet s) (hsU : s ⊆ U) (ε : ℝ≥0) (hε : 0 < ε) :
    Measure.hausdorffMeasure (finrank ℝ V : ℝ) (f '' s) ≤
        (↑(1 + ε) : ℝ≥0∞) ^ (finrank ℝ V + 1) *
          ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).normDet
            ∂(Measure.hausdorffMeasure (finrank ℝ V : ℝ)) ∧
    (∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).normDet
        ∂(Measure.hausdorffMeasure (finrank ℝ V : ℝ))) ≤
        (↑(1 + ε) : ℝ≥0∞) ^ (finrank ℝ V + 1) *
          Measure.hausdorffMeasure (finrank ℝ V : ℝ) (f '' s) := by
  apply area_bounds_of_local_bounds hf.continuousOn
    (fun x hx y hy hxy => by simpa only [hPf x hx, hPf y hy] using congrArg P hxy) hs hsU
  intro x hx
  let A := fderiv ℝ f x
  let J : V → ℝ := fun y => (fderiv ℝ f y).normDet
  have hPA : ∀ v, P (A v) = v := projection_fderiv hU hf hPf hx
  have hAi : Function.Injective A := by
    intro v w hvw
    simpa only [hPA] using congrArg P hvw
  have hJne : A.normDet ≠ 0 := (A.toLinearMap.normDet_ne_zero_tfae.out 5 1).mp hAi
  have hJpos : 0 < J x := lt_of_le_of_ne A.toLinearMap.normDet_nonneg hJne.symm
  have hJcont : ContinuousAt J x := continuous_normDet.continuousAt.comp
    ((hf.continuousOn_fderiv_of_isOpen hU le_rfl x hx).continuousAt (hU.mem_nhds hx))
  have hmul : J x < (1 + (ε : ℝ)) * J x := by
    have : (0 : ℝ) < ε := hε
    nlinarith
  have hev₁ : ∀ᶠ y in nhds x, J x < (1 + (ε : ℝ)) * J y :=
    (continuousAt_const.mul hJcont).eventually (lt_mem_nhds hmul)
  have hev₂ : ∀ᶠ y in nhds x, J y < (1 + (ε : ℝ)) * J x :=
    hJcont.eventually (gt_mem_nhds hmul)
  obtain ⟨q, hqx, hq⟩ := (hf.contDiffAt (hU.mem_nhds hx)).hasStrictFDerivAt (by norm_num)
    |>.approximates_deriv_on_nhds (Or.inr hε)
  obtain ⟨t, htq, hto, hxt⟩ := _root_.mem_nhds_iff.mp
    (Filter.inter_mem hqx (Filter.inter_mem hev₁ hev₂))
  refine ⟨t, hto, hxt, ?_⟩
  intro a ha haU
  have hat : a ⊆ q := fun y hy => (htq (haU hy).2).1
  obtain ⟨hup, hdown⟩ := hausdorffMeasure_image_comparison hP
    (fun y hy => hPf y (haU hy).1) hPA (hq.mono_set hat)
  let K : ℝ≥0∞ := ↑(1 + ε)
  let D : ℝ≥0∞ := ENNReal.ofReal A.normDet
  let μ : Measure V := Measure.hausdorffMeasure (finrank ℝ V : ℝ)
  have hlowJ : D * μ a ≤ K * ∫⁻ y in a, ENNReal.ofReal (J y) ∂μ := by
    rw [← setLIntegral_const, ← lintegral_const_mul' K _ (by simp [K])]
    apply setLIntegral_mono' ha
    intro y hy
    have h := ENNReal.ofReal_le_ofReal (htq (haU hy).2).2.1.le
    simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ 1 + (ε : ℝ)),
      ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) ε.coe_nonneg,
      ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal, ENNReal.coe_add, ENNReal.coe_one,
      J, D, K, A] using h
  have huppJ : (∫⁻ y in a, ENNReal.ofReal (J y) ∂μ) ≤ K * (D * μ a) := by
    rw [← mul_assoc, ← setLIntegral_const]
    apply setLIntegral_mono' ha
    intro y hy
    have h := ENNReal.ofReal_le_ofReal (htq (haU hy).2).2.2.le
    simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ 1 + (ε : ℝ)),
      ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) ε.coe_nonneg,
      ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal, ENNReal.coe_add, ENNReal.coe_one,
      J, D, K, A] using h
  constructor
  · calc
      _ ≤ K ^ finrank ℝ V * (D * μ a) := hup
      _ ≤ K ^ finrank ℝ V * (K * ∫⁻ y in a, ENNReal.ofReal (J y) ∂μ) :=
        by gcongr
      _ = _ := by rw [pow_succ, mul_assoc]
  · calc
      _ ≤ K * (D * μ a) := huppJ
      _ ≤ K * (K ^ finrank ℝ V * Measure.hausdorffMeasure (finrank ℝ V : ℝ) (f '' a)) :=
        by gcongr
      _ = _ := by rw [pow_succ, mul_left_comm, mul_assoc]

/-- The nonlinear set-area formula on an open graph domain, for raw Hausdorff measure. -/
theorem hausdorffMeasure_image_eq_lintegral_of_contDiffOn_graph
    {f : V → W} {U s : Set V} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {P : W →L[ℝ] V} (hP : ∀ z, ‖P z‖ ≤ ‖z‖)
    (hPf : ∀ x ∈ U, P (f x) = x) (hs : MeasurableSet s) (hsU : s ⊆ U) :
    Measure.hausdorffMeasure (finrank ℝ V : ℝ) (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).normDet
        ∂(Measure.hausdorffMeasure (finrank ℝ V : ℝ)) := by
  have hlim : Tendsto (fun ε : ℝ≥0 => (↑(1 + ε) : ℝ≥0∞) ^ (finrank ℝ V + 1))
      (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous (fun ε : ℝ≥0 => (↑(1 + ε) : ℝ≥0∞)) :=
      ENNReal.continuous_coe.comp (continuous_const.add continuous_id)
    have hct : Tendsto (fun ε : ℝ≥0 => (↑(1 + ε) : ℝ≥0∞)) (𝓝 0) (𝓝 1) := by
      simpa using hc.tendsto (0 : ℝ≥0)
    simpa only [one_pow] using (ENNReal.Tendsto.pow (n := finrank ℝ V + 1) hct).mono_left
      (show (𝓝[>] (0 : ℝ≥0)) ≤ 𝓝 0 from inf_le_left)
  have hlimmul (c : ℝ≥0∞) : Tendsto
      (fun ε : ℝ≥0 => (↑(1 + ε) : ℝ≥0∞) ^ (finrank ℝ V + 1) * c)
      (𝓝[>] 0) (𝓝 c) := by
    simpa using ENNReal.Tendsto.mul_const hlim (Or.inl one_ne_zero)
  have hbound : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      Measure.hausdorffMeasure (finrank ℝ V : ℝ) (f '' s) ≤
          (↑(1 + ε) : ℝ≥0∞) ^ (finrank ℝ V + 1) *
            ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).normDet
              ∂(Measure.hausdorffMeasure (finrank ℝ V : ℝ)) ∧
      (∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).normDet
          ∂(Measure.hausdorffMeasure (finrank ℝ V : ℝ))) ≤
          (↑(1 + ε) : ℝ≥0∞) ^ (finrank ℝ V + 1) *
            Measure.hausdorffMeasure (finrank ℝ V : ℝ) (f '' s) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact graph_area_bounds hU hf hP hPf hs hsU ε hε
  exact le_antisymm (ge_of_tendsto (hlimmul _) (hbound.mono fun _ h => h.1))
    (ge_of_tendsto (hlimmul _) (hbound.mono fun _ h => h.2))

/-- The restricted graph measure is the pushforward of the tangent density. -/
theorem map_restrict_withDensity_normDet_eq_restrict_hausdorffMeasure
    {f : V → W} {U s : Set V} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {P : W →L[ℝ] V} (hP : ∀ z, ‖P z‖ ≤ ‖z‖)
    (hPf : ∀ x ∈ U, P (f x) = x) (hs : MeasurableSet s) (hsU : s ⊆ U) :
    Measure.map f ((Measure.hausdorffMeasure (finrank ℝ V : ℝ)).restrict s |>.withDensity
        (fun x => ENNReal.ofReal (fderiv ℝ f x).normDet)) =
      (Measure.hausdorffMeasure (finrank ℝ V : ℝ)).restrict (f '' s) := by
  let μ : Measure V := Measure.hausdorffMeasure (finrank ℝ V : ℝ)
  let J : V → ℝ≥0∞ := fun x => ENNReal.ofReal (fderiv ℝ f x).normDet
  have hfc : ContinuousOn f s := hf.continuousOn.mono hsU
  have hfm : AEMeasurable f ((μ.restrict s).withDensity J) :=
    (hfc.aemeasurable hs).mono_ac (withDensity_absolutelyContinuous _ _)
  ext b hb
  rw [Measure.map_apply_of_aemeasurable hfm hb, Measure.restrict_apply hb,
    ← restrict_withDensity hs J, Measure.restrict_apply' hs]
  have hpre : MeasurableSet (f ⁻¹' b ∩ s) := by
    have hsub := (continuousOn_iff_continuous_domRestrict.mp hfc).measurable hb
    have hmeas := (MeasurableEmbedding.subtype_coe hs).measurableSet_image.mpr hsub
    convert hmeas using 1
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_image, Set.domRestrict_apply]
    aesop
  rw [withDensity_apply J hpre]
  have hset : f '' (f ⁻¹' b ∩ s) = b ∩ f '' s := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_image]
    aesop
  rw [← hset]
  exact (hausdorffMeasure_image_eq_lintegral_of_contDiffOn_graph hU hf hP hPf
    hpre (inter_subset_right.trans hsU)).symm

/-- Full nonnegative weighted area formula on any measurable part of a local graph. -/
theorem lintegral_graph_image_subset
    {f : V → W} {U s : Set V} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {P : W →L[ℝ] V} (hP : ∀ z, ‖P z‖ ≤ ‖z‖)
    (hPf : ∀ x ∈ U, P (f x) = x) (hs : MeasurableSet s) (hsU : s ⊆ U)
    {h : W → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ y in f '' s, h y ∂(Measure.hausdorffMeasure (finrank ℝ V : ℝ))) =
      ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).normDet * h (f x)
        ∂(Measure.hausdorffMeasure (finrank ℝ V : ℝ)) := by
  let μ : Measure V := Measure.hausdorffMeasure (finrank ℝ V : ℝ)
  let J : V → ℝ≥0∞ := fun x => ENNReal.ofReal (fderiv ℝ f x).normDet
  have hfc : ContinuousOn f s := hf.continuousOn.mono hsU
  have hfm : AEMeasurable f (μ.restrict s) := hfc.aemeasurable hs
  have hfm' := hfm.mono_ac (withDensity_absolutelyContinuous (μ.restrict s) J)
  have hJ : AEMeasurable J (μ.restrict s) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (continuous_normDet.comp_continuousOn
        ((hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hsU))).aemeasurable hs
  rw [← map_restrict_withDensity_normDet_eq_restrict_hausdorffMeasure hU hf hP hPf hs hsU]
  rw [lintegral_map' hh.aemeasurable hfm']
  exact lintegral_withDensity_eq_lintegral_mul₀ hJ (hh.comp_aemeasurable hfm)

end GeneralArea
/-- Horizontal Euclidean coordinate projection. -/
def graphProjection (n : ℕ) : E (n + 1) →L[ℝ] E n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun i => z i.castSucc)
      map_add' := by intro x y; ext i; rfl
      map_smul' := by intro c x; ext i; rfl }

@[simp] theorem graphProjection_apply {n : ℕ} (z : E (n + 1)) (i : Fin n) :
    graphProjection n z i = z i.castSucc := rfl

@[simp] theorem graphProjection_graphMap {n : ℕ} (g : E n → ℝ) (x : E n) :
    graphProjection n (graphMap g x) = x := by ext i; simp

theorem norm_graphProjection_le {n : ℕ} (z : E (n + 1)) :
    ‖graphProjection n z‖ ≤ ‖z‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp only [graphProjection_apply]
  nlinarith [sq_nonneg (z (Fin.last n))]

/-- Linear tangent graph of a continuous linear functional. -/
def graphTangent {n : ℕ} (a : E n →L[ℝ] ℝ) : E n →L[ℝ] E (n + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := graphMap a
      map_add' := by
        intro x y; ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      map_smul' := by
        intro c x; ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp }

@[simp] theorem graphTangent_apply {n : ℕ} (a : E n →L[ℝ] ℝ) (v : E n) :
    graphTangent a v = graphMap a v := rfl

theorem contDiffOn_graphMap {n : ℕ} {U : Set (E n)} {g : E n → ℝ}
    (hg : ContDiffOn ℝ 1 g U) : ContDiffOn ℝ 1 (graphMap g) U := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hg
  · simpa using (contDiffOn_piLp_apply (𝕜 := ℝ) (i := j) 2 :
      ContDiffOn ℝ 1 (fun x : E n => x j) U)

set_option backward.isDefEq.respectTransparency false in
theorem hasStrictFDerivAt_graphMap {n : ℕ} {g : E n → ℝ} {a : E n →L[ℝ] ℝ}
    {x : E n} (hg : HasStrictFDerivAt g a x) :
    HasStrictFDerivAt (graphMap g) (graphTangent a) x := by
  apply (hasStrictFDerivAt_piLp 2).mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hd : (PiLp.proj 2 (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).comp
        (graphTangent a) = a := by ext v; simp [PiLp.proj_apply]
    rw [hd]
    simpa only [graphMap_last] using hg
  · have hd : (PiLp.proj 2 (fun _ : Fin (n + 1) => ℝ) j.castSucc).comp
        (graphTangent a) = PiLp.proj 2 (fun _ : Fin n => ℝ) j := by
      ext v; simp [PiLp.proj_apply]
    rw [hd]
    have hid := (hasStrictFDerivAt_piLp 2).mp (hasStrictFDerivAt_id (𝕜 := ℝ) x) j
    simpa only [id_eq, graphMap_castSucc, ContinuousLinearMap.comp_id] using hid

set_option backward.isDefEq.respectTransparency false in
/-- The tangent Gram matrix is a rank-one perturbation of the identity. -/
theorem normDet_graphTangent {n : ℕ} (a : E n →L[ℝ] ℝ) :
    (graphTangent a).normDet = Real.sqrt (1 + ∑ i : Fin n, (a (coordinateVector i)) ^ 2) := by
  classical
  let w : Fin n → ℝ := fun i => a (coordinateVector i)
  have hgram : Matrix.gram ℝ (fun i => graphTangent a (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      1 + Matrix.replicateCol Unit w * Matrix.replicateRow Unit w := by
    ext i j
    simp only [Matrix.gram_apply, EuclideanSpace.basisFun_apply, graphTangent_apply,
      PiLp.inner_apply, Fin.sum_univ_castSucc, graphMap_castSucc, graphMap_last,
      RCLike.inner_apply, conj_trivial, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply, Fintype.sum_unique]
    change (∑ k : Fin n, (EuclideanSpace.single j (1 : ℝ) k) *
      (EuclideanSpace.single i (1 : ℝ) k)) + w j * w i =
        (if i = j then 1 else 0) + w i * w j
    simp only [PiLp.single_apply]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij, Ne.symm hij, mul_comm]
  have hsq : (graphTangent a).normDet ^ 2 = 1 + ∑ i : Fin n, (a (coordinateVector i)) ^ 2 := by
    have h := (graphTangent a).toLinearMap.normDet_sq_eq_det_gram
      (EuclideanSpace.basisFun (Fin n) ℝ)
    rw [show (fun i => (graphTangent a).toLinearMap (EuclideanSpace.basisFun (Fin n) ℝ i)) =
        (fun i => graphTangent a (EuclideanSpace.basisFun (Fin n) ℝ i)) from rfl,
      hgram, Matrix.det_one_add_replicateCol_mul_replicateRow] at h
    simpa only [RCLike.ofReal_real_eq_id, id_eq, dotProduct, w, pow_two] using h
  rw [← hsq, Real.sqrt_sq (graphTangent a).toLinearMap.normDet_nonneg]

theorem normDet_fderiv_graphMap {n : ℕ} {U : Set (E n)} {g : E n → ℝ}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U) {x : E n} (hx : x ∈ U) :
    (fderiv ℝ (graphMap g) x).normDet = graphJacobian g x := by
  have hd := hasStrictFDerivAt_graphMap ((hg.contDiffAt (hU.mem_nhds hx)).hasStrictFDerivAt
    (by norm_num))
  rw [hd.hasFDerivAt.fderiv]
  exact normDet_graphTangent _

theorem weighted_graph_area : Specs.WeightedGraphArea := by
  intro n U g hU hg s hs hsU h hh
  have heq := lintegral_graph_image_subset hU (contDiffOn_graphMap hg)
    (P := graphProjection n) norm_graphProjection_le
    (fun x _ => graphProjection_graphMap g x) hs hsU hh
  simp only [finrank_euclideanSpace_fin] at heq
  rw [heq]
  apply setLIntegral_congr_fun hs
  intro x hx
  change ENNReal.ofReal (fderiv ℝ (graphMap g) x).normDet * h (graphMap g x) = _
  rw [normDet_fderiv_graphMap hU hg (hsU hx)]

end ExpandedFA.HausdorffGraphArea
