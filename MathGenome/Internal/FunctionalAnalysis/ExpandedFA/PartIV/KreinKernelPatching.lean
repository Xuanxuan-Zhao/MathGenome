import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinKernelPatching
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.KreinLocalFiberKernels
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace ExpandedFA.PartIV.KreinKernelPatching
open KreinSpectralKernel KreinLocalFiberKernels

local instance interval_finite (R : ℝ) : IsFiniteMeasure (intervalMeasure R) := by
  dsimp [intervalMeasure]
  infer_instance

lemma intervalMeasure_mono {R T : ℝ} (hRT : R ≤ T) :
    intervalMeasure R ≤ intervalMeasure T :=
  Measure.restrict_mono (Icc_subset_Icc (neg_le_neg hRT) hRT) le_rfl

lemma intervalMeasure_restrict {R T : ℝ} (hRT : R ≤ T) :
    (intervalMeasure T).restrict (Icc (-R) R) = intervalMeasure R := by
  exact Measure.restrict_restrict_of_subset (Icc_subset_Icc (neg_le_neg hRT) hRT)

/-- Zero extension of a scalar L² input from the smaller interval. -/
def extendInput {R T : ℝ} (hRT : R ≤ T) (f : Lp ℂ 2 (intervalMeasure R)) :
    Lp ℂ 2 (intervalMeasure T) :=
  let hm : MemLp ((Icc (-R) R).indicator (fun t => f t)) 2 (intervalMeasure T) :=
    (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).mpr
      (by rw [intervalMeasure_restrict hRT]; exact Lp.memLp f)
  hm.toLp _

lemma extendInput_ae {R T : ℝ} (hRT : R ≤ T) (f : Lp ℂ 2 (intervalMeasure R)) :
    extendInput hRT f =ᵐ[intervalMeasure T] (Icc (-R) R).indicator (fun t => f t) :=
  (show MemLp ((Icc (-R) R).indicator (fun t => f t)) 2 (intervalMeasure T) from
    (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).mpr
      (by rw [intervalMeasure_restrict hRT]; exact Lp.memLp f)).coeFn_toLp

lemma integral_extendInput {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℂ E]
    {R T : ℝ} (hRT : R ≤ T) (f : Lp ℂ 2 (intervalMeasure R)) (v : ℝ → E) :
    (∫ t, extendInput hRT f t • v t ∂intervalMeasure T) =
      ∫ t, f t • v t ∂intervalMeasure R := by
  calc
    _ = ∫ t, (Icc (-R) R).indicator (fun t => f t • v t) t ∂intervalMeasure T := by
      apply integral_congr_ae
      filter_upwards [extendInput_ae hRT f] with t ht
      rw [ht, Set.indicator_smul_left]
    _ = _ := by rw [integral_indicator measurableSet_Icc, intervalMeasure_restrict hRT]

/-- Restricting a representation retains every scalar L² input, by zero
extension. This statement also applies to unrelated choices of local kernels. -/
lemma represents_restrict {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (μ : Measure ℝ) (v : ℝ → H)
    (U : H →ₗᵢ[ℂ] Lp FiberSpace 2 μ) {R T : ℝ} (hRT : R ≤ T)
    (h : ℝ → ℝ → FiberSpace)
    (hr : ∀ f : Lp ℂ 2 (intervalMeasure T),
      (U (∫ t, f t • v t ∂intervalMeasure T) : ℝ → FiberSpace) =ᵐ[μ]
        fun ξ => ∫ t, f t • h ξ t ∂intervalMeasure T) :
    ∀ f : Lp ℂ 2 (intervalMeasure R),
      (U (∫ t, f t • v t ∂intervalMeasure R) : ℝ → FiberSpace) =ᵐ[μ]
        fun ξ => ∫ t, f t • h ξ t ∂intervalMeasure R := by
  intro f
  have he := hr (extendInput hRT f)
  rw [integral_extendInput] at he
  exact he.trans (ae_of_all _ fun ξ => integral_extendInput hRT f (h ξ))

/-- Local uniqueness gives consistency on every ordered pair of intervals. -/
lemma localKernel_overlap {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (m : ℝ → ℕ∞) (v : ℝ → H) (U : H →ₗᵢ[ℂ] Lp FiberSpace 2 μ)
    {R T : ℝ} (hRT : R ≤ T) (K : LocalKernel μ m v U R) (L : LocalKernel μ m v U T) :
    Function.uncurry K.h =ᵐ[μ.prod (intervalMeasure R)] Function.uncurry L.h := by
  let : IsFiniteMeasure (intervalMeasure R) := by dsimp [intervalMeasure]; infer_instance
  apply kernel_unique μ (intervalMeasure R) K.h L.h K.square
    (L.square.mono_measure (Measure.prod_mono le_rfl (intervalMeasure_mono hRT)))
  intro f
  exact (K.represents f).symm.trans (represents_restrict μ v U hRT L.h L.represents f)

/-- Express a local product measure as a restriction of the global one. -/
lemma prod_intervalMeasure (μ : Measure ℝ) [SFinite μ] (R : ℝ) :
    μ.prod (intervalMeasure R) =
      (μ.prod volume).restrict (univ ×ˢ Icc (-R) R) := by
  simpa only [Measure.restrict_univ, intervalMeasure] using
    (Measure.prod_restrict (μ := μ) (ν := (volume : Measure ℝ)) univ (Icc (-R) R))

lemma ae_prod_interval_iff (μ : Measure ℝ) [SFinite μ] (R : ℝ) (P : ℝ × ℝ → Prop) :
    (∀ᵐ q ∂μ.prod (intervalMeasure R), P q) ↔
      ∀ᵐ q ∂μ.prod volume, q.2 ∈ Icc (-R) R → P q := by
  rw [prod_intervalMeasure, ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Icc)]
  simp only [mem_prod, mem_univ, true_and]

lemma integer_intervals_cover :
    (⋃ n : ℕ, Icc (-(n + 1 : ℝ)) (n + 1)) = univ := by
  apply eq_univ_of_forall
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt |t|
  apply mem_iUnion.mpr
  refine ⟨n, ?_⟩
  have habs := abs_le.mp (le_of_lt hn)
  constructor <;> linarith

lemma product_integer_intervals_cover :
    (⋃ n : ℕ, (univ : Set ℝ) ×ˢ Icc (-(n + 1 : ℝ)) (n + 1)) = univ := by
  rw [← prod_iUnion, integer_intervals_cover, univ_prod_univ]

/-- Select a local kernel on a large enough interval. The selection need not
preserve a chosen representative pointwise; countable overlap identities give
its local a.e. equalities and hence global measurability. -/
def paste (k : ℕ → ℝ → ℝ → FiberSpace) (ξ t : ℝ) : FiberSpace :=
  k ⌈|t|⌉₊ ξ t

lemma paste_index_mem (t : ℝ) :
    t ∈ Icc (-(⌈|t|⌉₊ + 1 : ℝ)) (⌈|t|⌉₊ + 1) := by
  have h := Nat.le_ceil |t|
  have habs := abs_le.mp h
  constructor <;> linarith

/-- A compatible countable family pastes to a representative agreeing with
each local kernel. No nonzero-measure assumption is used. -/
lemma paste_ae (μ : Measure ℝ) [SFinite μ] (k : ℕ → ℝ → ℝ → FiberSpace)
    (hc : ∀ n m : ℕ, n ≤ m →
      Function.uncurry (k n) =ᵐ[μ.prod (intervalMeasure (n + 1))]
        Function.uncurry (k m)) :
    ∀ n : ℕ, Function.uncurry (paste k) =ᵐ[μ.prod (intervalMeasure (n + 1))]
      Function.uncurry (k n) := by
  have hpair (n m : ℕ) : ∀ᵐ q ∂μ.prod volume,
      q.2 ∈ Icc (-(n + 1 : ℝ)) (n + 1) →
      q.2 ∈ Icc (-(m + 1 : ℝ)) (m + 1) → k n q.1 q.2 = k m q.1 q.2 := by
    have hn := (ae_prod_interval_iff μ (n + 1) _).mp (hc n (max n m) (le_max_left _ _))
    have hm := (ae_prod_interval_iff μ (m + 1) _).mp (hc m (max n m) (le_max_right _ _))
    filter_upwards [hn, hm] with q hn hm hqn hqm
    exact (hn hqn).trans (hm hqm).symm
  have hall : ∀ᵐ q ∂μ.prod volume, ∀ n m : ℕ,
      q.2 ∈ Icc (-(n + 1 : ℝ)) (n + 1) →
      q.2 ∈ Icc (-(m + 1 : ℝ)) (m + 1) → k n q.1 q.2 = k m q.1 q.2 :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr (hpair n)
  intro n
  apply (ae_prod_interval_iff μ (n + 1) _).mpr
  filter_upwards [hall] with q hq hqn
  exact hq ⌈|q.2|⌉₊ n (paste_index_mem q.2) hqn

lemma measurable_of_local (μ : Measure ℝ) [SFinite μ] (h : ℝ → ℝ → FiberSpace)
    (hh : ∀ n : ℕ, AEStronglyMeasurable (Function.uncurry h)
      (μ.prod (intervalMeasure (n + 1)))) :
    AEStronglyMeasurable (Function.uncurry h) (μ.prod volume) := by
  have hm : ∀ n : ℕ, AEStronglyMeasurable (Function.uncurry h)
      ((μ.prod volume).restrict (univ ×ˢ Icc (-(n + 1 : ℝ)) (n + 1))) := by
    intro n
    rw [← prod_intervalMeasure]
    exact hh n
  have hi := AEStronglyMeasurable.iUnion hm
  rwa [product_integer_intervals_cover, Measure.restrict_univ] at hi

lemma ae_of_integer_intervals (P : ℝ → Prop)
    (hP : ∀ n : ℕ, ∀ᵐ t ∂intervalMeasure (n + 1), P t) : ∀ᵐ t ∂volume, P t := by
  have hi := (ae_restrict_iUnion_iff
    (μ := (volume : Measure ℝ)) (fun n : ℕ => Icc (-(n + 1 : ℝ)) (n + 1)) P).mpr hP
  rwa [integer_intervals_cover, Measure.restrict_univ] at hi

/-- Reflection preserves exactly the restricted interval measure. -/
lemma interval_neg_preserving (R : ℝ) :
    MeasurePreserving (fun t : ℝ => -t) (intervalMeasure R) (intervalMeasure R) := by
  have he : (fun t : ℝ => -t) ⁻¹' Icc (-R) R = Icc (-R) R := by
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]
  simpa only [he, intervalMeasure] using
    (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage (s := Icc (-R) R) measurableSet_Icc

lemma integral_reflect {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℂ E]
    (R : ℝ) (f : ℝ → ℂ) (v : ℝ → E) :
    (∫ t, f (-t) • v t ∂intervalMeasure R) =
      ∫ t, f t • v (-t) ∂intervalMeasure R := by
  have he := (interval_neg_preserving R).integral_comp
    (MeasurableEquiv.neg ℝ).measurableEmbedding (fun t => f t • v (-t))
  simpa only [neg_neg] using he

/-- Reflection of the input has the expected representative in scalar L². -/
def reflectInput (R : ℝ) (f : Lp ℂ 2 (intervalMeasure R)) :
    Lp ℂ 2 (intervalMeasure R) :=
  Lp.compMeasurePreserving (fun t : ℝ => -t) (interval_neg_preserving R) f

lemma reflectInput_ae (R : ℝ) (f : Lp ℂ 2 (intervalMeasure R)) :
    reflectInput R f =ᵐ[intervalMeasure R] fun t => f (-t) :=
  Lp.coeFn_compMeasurePreserving f (interval_neg_preserving R)

lemma integral_reflectInput {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℂ E]
    (R : ℝ) (f : Lp ℂ 2 (intervalMeasure R)) (v : ℝ → E) :
    (∫ t, reflectInput R f t • v t ∂intervalMeasure R) =
      ∫ t, f t • v (-t) ∂intervalMeasure R := by
  rw [← integral_reflect]
  apply integral_congr_ae
  filter_upwards [reflectInput_ae R f] with t ht
  rw [ht]

/-- Parity follows from uniqueness for the reflected kernel, without imposing
parity or a simultaneous exceptional set on the chosen local representative. -/
lemma kernel_parity {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (μ : Measure ℝ) [IsFiniteMeasure μ] (p : Bool)
    (v : ℝ → H) (hv : ∀ t, v (-t) = KreinSymmetricOperator.Spec.paritySign p • v t)
    (U : H →ₗᵢ[ℂ] Lp FiberSpace 2 μ) (R : ℝ) (h : ℝ → ℝ → FiberSpace)
    (hh : MemLp (Function.uncurry h) 2 (μ.prod (intervalMeasure R)))
    (hr : ∀ f : Lp ℂ 2 (intervalMeasure R),
      (U (∫ t, f t • v t ∂intervalMeasure R) : ℝ → FiberSpace) =ᵐ[μ]
        fun ξ => ∫ t, f t • h ξ t ∂intervalMeasure R) :
    ∀ᵐ ξ ∂μ, ∀ᵐ t ∂intervalMeasure R,
      h ξ (-t) = KreinSymmetricOperator.Spec.paritySign p • h ξ t := by
  let c := KreinSymmetricOperator.Spec.paritySign p
  have href : MemLp (fun q : ℝ × ℝ => h q.1 (-q.2)) 2 (μ.prod (intervalMeasure R)) :=
    hh.comp_measurePreserving ((MeasurePreserving.id μ).prod (interval_neg_preserving R))
  have hsm : MemLp (fun q : ℝ × ℝ => c • h q.1 q.2) 2 (μ.prod (intervalMeasure R)) :=
    hh.const_smul c
  have heq : (fun q : ℝ × ℝ => h q.1 (-q.2)) =ᵐ[μ.prod (intervalMeasure R)]
      (fun q : ℝ × ℝ => c • h q.1 q.2) := by
    apply kernel_unique μ (intervalMeasure R) (fun ξ t => h ξ (-t))
      (fun ξ t => c • h ξ t) href hsm
    intro f
    have hsource : U (∫ t, reflectInput R f t • v t ∂intervalMeasure R) =
        c • U (∫ t, f t • v t ∂intervalMeasure R) := by
      rw [integral_reflectInput]
      calc
        _ = U (∫ t, c • (f t • v t) ∂intervalMeasure R) := by
          congr 1
          apply integral_congr_ae
          exact ae_of_all _ fun t => by
            dsimp only
            rw [hv]
            exact smul_comm _ _ _
        _ = _ := by rw [integral_smul, map_smul]
    filter_upwards [hr (reflectInput R f), hr f,
      Lp.coeFn_smul c (U (∫ t, f t • v t ∂intervalMeasure R))] with ξ hre hf hc
    rw [hsource, integral_reflectInput] at hre
    rw [hc, Pi.smul_apply, hf] at hre
    calc
      _ = c • ∫ t, f t • h ξ t ∂intervalMeasure R := hre.symm
      _ = _ := by
        rw [← integral_smul]
        exact integral_congr_ae (ae_of_all _ fun t => smul_comm _ _ _)
  exact Measure.ae_ae_of_ae_prod heq

/-- The global measurable kernel, with the full every-real-radius integral
representation and energy, before any use of the operator's action. -/
theorem exists_kernel : Spec.KernelPatching := by
  intro H _ _ _ _ p F G S M
  classical
  let : IsFiniteMeasure M.μ := M.finite
  have hU (x : H) : ∀ᵐ ξ ∂M.μ, M.U x ξ ∈ coordinateFiber (M.multiplicity ξ) := by
    have hx : M.U x ∈ Set.range M.U := ⟨x, rfl⟩
    rw [M.range_eq] at hx
    exact hx
  have hex (R : ℝ) (hR : 0 < R) :
      Nonempty (LocalKernel M.μ M.multiplicity G.vectors M.U R) :=
    local_kernel_exists H G.vectors G.continuous_vectors M.μ M.multiplicity
      M.measurable_multiplicity M.U hU R hR
  let K (n : ℕ) : LocalKernel M.μ M.multiplicity G.vectors M.U (n + 1) :=
    Classical.choice (hex (n + 1) (by positivity))
  let h := paste (fun n => (K n).h)
  have hsame (n : ℕ) : Function.uncurry h =ᵐ[M.μ.prod (intervalMeasure (n + 1))]
      Function.uncurry (K n).h := by
    apply paste_ae M.μ (fun n => (K n).h)
    intro n m hnm
    exact localKernel_overlap M.μ M.multiplicity G.vectors M.U
      (by exact_mod_cast Nat.add_le_add_right hnm 1) (K n) (K m)
  have hagree (R : ℝ) (L : LocalKernel M.μ M.multiplicity G.vectors M.U R) :
      Function.uncurry h =ᵐ[M.μ.prod (intervalMeasure R)] Function.uncurry L.h := by
    obtain ⟨n, hn⟩ := exists_nat_gt R
    have hRn : R ≤ (n + 1 : ℝ) := by linarith
    exact ((hsame n).filter_mono
      (ae_mono (Measure.prod_mono le_rfl (intervalMeasure_mono hRn)))).trans
      (localKernel_overlap M.μ M.multiplicity G.vectors M.U hRn L (K n)).symm
  have hlocal (R : ℝ) (hR : 0 < R) :
      MemLp (Function.uncurry h) 2 (M.μ.prod (intervalMeasure R)) := by
    let L := Classical.choice (hex R hR)
    exact (memLp_congr_ae (hagree R L)).mpr L.square
  have hmeas : AEStronglyMeasurable (Function.uncurry h) (M.μ.prod volume) := by
    apply measurable_of_local
    intro n
    exact (K n).measurable.congr (hsame n).symm
  have hrep (R : ℝ) (hR : 0 < R) (f : Lp ℂ 2 (intervalMeasure R)) :
      (M.U (∫ t, f t • G.vectors t ∂intervalMeasure R) : ℝ → FiberSpace) =ᵐ[M.μ]
        fun ξ => ∫ t, f t • h ξ t ∂intervalMeasure R := by
    let L := Classical.choice (hex R hR)
    filter_upwards [L.represents f, Measure.ae_ae_of_ae_prod (hagree R L)] with ξ hr he
    apply hr.trans
    apply integral_congr_ae
    filter_upwards [he] with t ht
    change h ξ t = L.h ξ t at ht
    rw [ht]
  have henergy (R : ℝ) (hR : 0 < R) :
      (∫⁻ ξ, ∫⁻ t, ‖h ξ t‖ₑ ^ 2 ∂intervalMeasure R ∂M.μ) =
        ENNReal.ofReal (∫ t, ‖G.vectors t‖ ^ 2 ∂intervalMeasure R) := by
    let L := Classical.choice (hex R hR)
    refine Eq.trans ?_ L.energy
    apply lintegral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod (hagree R L)] with ξ he
    apply lintegral_congr_ae
    filter_upwards [he] with t ht
    change h ξ t = L.h ξ t at ht
    rw [ht]
  have hrows (n : ℕ) : ∀ᵐ ξ ∂M.μ, MemLp (h ξ) 2 (intervalMeasure (n + 1)) :=
    vector_sections M.μ (intervalMeasure (n + 1)) h (hlocal (n + 1) (by positivity))
  have hfib (n : ℕ) : ∀ᵐ ξ ∂M.μ, ∀ᵐ t ∂intervalMeasure (n + 1),
      h ξ t ∈ coordinateFiber (M.multiplicity ξ) := by
    filter_upwards [(K n).fibers, Measure.ae_ae_of_ae_prod (hsame n)] with ξ hf he
    filter_upwards [hf, he] with t hf he
    change h ξ t = (K n).h ξ t at he
    rw [he]
    exact hf
  have hpar (n : ℕ) : ∀ᵐ ξ ∂M.μ, ∀ᵐ t ∂intervalMeasure (n + 1),
      h ξ (-t) = KreinSymmetricOperator.Spec.paritySign p • h ξ t :=
    kernel_parity M.μ p G.vectors G.parity M.U (n + 1) h
      (hlocal (n + 1) (by positivity)) (hrep (n + 1) (by positivity))
  refine ⟨{
    h := h
    measurable := hmeas
    local_square := hlocal
    fiber_properties := ?_
    represents := hrep
    energy := henergy }⟩
  filter_upwards [ae_all_iff.mpr hrows, ae_all_iff.mpr hfib, ae_all_iff.mpr hpar]
    with ξ hrow hf hp
  exact ⟨hrow, ae_of_integer_intervals _ hf, ae_of_integer_intervals _ hp⟩

end ExpandedFA.PartIV.KreinKernelPatching
