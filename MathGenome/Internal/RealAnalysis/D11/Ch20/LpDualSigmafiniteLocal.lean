import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.LpDualSigmafiniteLocal
import MathGenome.Internal.RealAnalysis.D11.Ch20.LpDualFiniteMeasure
import MathGenome.Internal.RealAnalysis.D11.Ch01.ExhaustionRestriction
import MathGenome.Internal.RealAnalysis.D11.Ch10.DominatedLp

open Set MeasureTheory Filter
open scoped ENNReal Topology
universe u
noncomputable section
namespace D11.Ch20.LpDualSigmafiniteLocal
variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]

section Restriction
variable (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (A : Set X) (hA : MeasurableSet A)

/-- Restrict an ordinary Lp class to the ambient restricted measure. -/
def restrictLp : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p (μ.restrict A) :=
  LinearMap.mkContinuous
    { toFun := fun f => ((Lp.memLp f).restrict A).toLp f
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).restrict A),
          Lp.coeFn_add (((Lp.memLp f).restrict A).toLp f)
            (((Lp.memLp g).restrict A).toLp g),
          MemLp.coeFn_toLp ((Lp.memLp f).restrict A),
          MemLp.coeFn_toLp ((Lp.memLp g).restrict A),
          ae_restrict_of_ae (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
        simp_all
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).restrict A),
          Lp.coeFn_smul c (((Lp.memLp f).restrict A).toLp f),
          MemLp.coeFn_toLp ((Lp.memLp f).restrict A),
          ae_restrict_of_ae (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
        simp_all }
    1 (by
      intro f
      change ‖((Lp.memLp f).restrict A).toLp (f : X → 𝕜)‖ ≤ 1 * ‖f‖
      rw [one_mul, Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_restrict_le f p μ A))

lemma restrictLp_coe (f : Lp 𝕜 p μ) :
    restrictLp μ p A f =ᵐ[μ.restrict A] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).restrict A)

lemma norm_restrictLp_le (f : Lp 𝕜 p μ) : ‖restrictLp μ p A f‖ ≤ ‖f‖ := by
  change ‖((Lp.memLp f).restrict A).toLp f‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_restrict_le f p μ A)

omit [Fact (1 ≤ p)] in
include hA in
private lemma memLp_extend (f : Lp 𝕜 p (μ.restrict A)) :
    MemLp (A.indicator (f : X → 𝕜)) p μ :=
  (memLp_indicator_iff_restrict hA.nullMeasurableSet).mpr (Lp.memLp f)

/-- Extension by zero is isometric, also at the exponent infinity. -/
def extendLp : Lp 𝕜 p (μ.restrict A) →L[𝕜] Lp 𝕜 p μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_extend μ p A hA f).toLp (A.indicator (f : X → 𝕜))
      map_add' := by
        intro f g
        apply Lp.ext
        refine (MemLp.coeFn_toLp _).trans ?_
        refine ((ae_eq_restrict_iff_indicator_ae_eq hA).mp (Lp.coeFn_add f g)).trans ?_
        filter_upwards [Lp.coeFn_add
          ((memLp_extend μ p A hA f).toLp _) ((memLp_extend μ p A hA g).toLp _),
          MemLp.coeFn_toLp (memLp_extend μ p A hA f),
          MemLp.coeFn_toLp (memLp_extend μ p A hA g)] with x h1 h2 h3
        simp only [Pi.add_apply] at h1 ⊢
        rw [h1, h2, h3]
        exact congrFun (Set.indicator_add A _ _) x
      map_smul' := by
        intro c f
        apply Lp.ext
        refine (MemLp.coeFn_toLp _).trans ?_
        refine ((ae_eq_restrict_iff_indicator_ae_eq hA).mp (Lp.coeFn_smul c f)).trans ?_
        filter_upwards [Lp.coeFn_smul c ((memLp_extend μ p A hA f).toLp _),
          MemLp.coeFn_toLp (memLp_extend μ p A hA f)] with x h1 h2
        change A.indicator (c • (f : X → 𝕜)) x = (c • (memLp_extend μ p A hA f).toLp _) x
        simp only [Pi.smul_apply] at h1 ⊢
        rw [h1, h2]
        exact congrFun (Set.indicator_smul A (fun _ => c) (f : X → 𝕜)) x }
    1 (by
      intro f
      change ‖(memLp_extend μ p A hA f).toLp _‖ ≤ 1 * ‖f‖
      rw [one_mul, Lp.norm_toLp, Lp.norm_def,
        eLpNorm_indicator_eq_eLpNorm_restrict hA.nullMeasurableSet])

lemma extendLp_coe (f : Lp 𝕜 p (μ.restrict A)) :
    extendLp μ p A hA f =ᵐ[μ] A.indicator (f : X → 𝕜) :=
  MemLp.coeFn_toLp (memLp_extend μ p A hA f)

lemma norm_extendLp (f : Lp 𝕜 p (μ.restrict A)) :
    ‖extendLp μ p A hA f‖ = ‖f‖ := by
  change ‖(memLp_extend μ p A hA f).toLp _‖ = _
  rw [Lp.norm_toLp, Lp.norm_def,
    eLpNorm_indicator_eq_eLpNorm_restrict hA.nullMeasurableSet]

def cutoffLp : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ :=
  (extendLp μ p A hA).comp (restrictLp μ p A)

lemma cutoffLp_coe (f : Lp 𝕜 p μ) :
    cutoffLp μ p A hA f =ᵐ[μ] A.indicator (f : X → 𝕜) :=
  (extendLp_coe μ p A hA _).trans
    ((ae_eq_restrict_iff_indicator_ae_eq hA).mp (restrictLp_coe μ p A f))

lemma norm_cutoffLp_le (f : Lp 𝕜 p μ) :
    ‖cutoffLp μ p A hA f‖ ≤ ‖f‖ := by
  rw [cutoffLp, ContinuousLinearMap.comp_apply, norm_extendLp]
  exact norm_restrictLp_le μ p A f

end Restriction

section Pairing
variable (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [ENNReal.HolderConjugate p q]

lemma pairing_norm [SigmaFinite μ] (g : Lp 𝕜 q μ) :
    ‖IntegralPairing.pairing μ p q g‖ = ‖g‖ := by
  by_cases hq : q = ∞
  · subst q
    have hp : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ p).mp rfl
    subst p
    exact PairingNormEndpoint.pairing_norm_endpoint μ
      (PairingNormEndpoint.sigmaFinite_semifinite μ inferInstance) g
  · exact PairingNormFiniteQ.norm_pairing μ p q hq g

lemma pairing_injective [SigmaFinite μ] :
    Function.Injective (IntegralPairing.pairing (𝕜 := 𝕜) μ p q) :=
  (AddMonoidHomClass.isometry_of_norm _ (pairing_norm μ p q)).injective

lemma pairing_extend (A : Set X) (hA : MeasurableSet A)
    (g : Lp 𝕜 q (μ.restrict A)) (f : Lp 𝕜 p μ) :
    IntegralPairing.pairing μ p q (extendLp μ q A hA g) f =
      IntegralPairing.pairing (μ.restrict A) p q g (restrictLp μ p A f) := by
  change Specs.D11.Ch20.IntegralPairing.pairing_value μ p q _ _ =
    Specs.D11.Ch20.IntegralPairing.pairing_value (μ.restrict A) p q _ _
  rw [(IntegralPairing.pairing_eq_integral μ p q _ _).2,
    (IntegralPairing.pairing_eq_integral (μ.restrict A) p q _ _).2]
  calc
    _ = ∫ x, A.indicator (fun x => f x * g x) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [extendLp_coe μ q A hA g] with x hx
      rw [hx]
      by_cases h : x ∈ A <;> simp [h]
    _ = ∫ x in A, f x * g x ∂μ := integral_indicator hA
    _ = _ := integral_congr_ae ((restrictLp_coe μ p A f).symm.mul EventuallyEq.rfl)

lemma pairing_cutoff (A : Set X) (hA : MeasurableSet A)
    (g : Lp 𝕜 q μ) (f : Lp 𝕜 p μ) :
    IntegralPairing.pairing μ p q (cutoffLp μ q A hA g) f =
      IntegralPairing.pairing μ p q g (cutoffLp μ p A hA f) := by
  change Specs.D11.Ch20.IntegralPairing.pairing_value μ p q _ _ =
    Specs.D11.Ch20.IntegralPairing.pairing_value μ p q _ _
  rw [(IntegralPairing.pairing_eq_integral μ p q _ _).2,
    (IntegralPairing.pairing_eq_integral μ p q _ _).2]
  apply integral_congr_ae
  filter_upwards [cutoffLp_coe μ q A hA g, cutoffLp_coe μ p A hA f] with x hg hf
  rw [hg, hf]
  by_cases hx : x ∈ A <;> simp [hx]

end Pairing

lemma cutoffLp_comp (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
    (f : Lp 𝕜 p μ) :
    cutoffLp μ p B hB (cutoffLp μ p A hA f) = cutoffLp μ p A hA f := by
  apply Lp.ext
  filter_upwards [cutoffLp_coe μ p B hB (cutoffLp μ p A hA f),
    cutoffLp_coe μ p A hA f] with x h1 h2
  rw [h1, h2]
  by_cases hx : x ∈ B
  · simpa only [Set.indicator_of_mem hx] using h2
  · have hxA : x ∉ A := fun h => hx (hAB h)
    simp [hx, hxA]

/-- Exhaustion cutoffs converge in each finite-exponent ordinary Lp space. -/
lemma cutoffLp_tendsto (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (E : ℕ → Set X) (hE : ∀ n, MeasurableSet (E n))
    (hmono : Monotone E) (hcover : ⋃ n, E n = univ) (f : Lp 𝕜 p μ) :
    Tendsto (fun n => cutoffLp μ p (E n) (hE n) f) atTop (𝓝 f) := by
  borelize 𝕜
  have hpR : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp (show 1 ≤ p from Fact.out)
  let F (n : ℕ) : X → 𝕜 := (E n).indicator (f : X → 𝕜)
  have hFm n : Measurable (F n) := (Lp.stronglyMeasurable f).measurable.indicator (hE n)
  have hfM : Measurable (f : X → 𝕜) := (Lp.stronglyMeasurable f).measurable
  have hraw : (fun x => ‖f x‖) ∈ Ch10.LpDefinition.rawLp μ p.toReal := by
    apply (Ch10.LpDefinition.rawLp_iff_memLp μ p.toReal _ hpR).mpr
    refine ⟨hfM.norm, ?_⟩
    simpa only [ENNReal.ofReal_toReal hp] using (Lp.memLp f).norm
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
    apply ae_of_all
    intro x
    obtain ⟨N, hxN⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (Set.indicator_of_mem (hmono hn hxN) _).symm
  have hd := Ch10.DominatedLp.dominated_ae μ p.toReal F (f : X → 𝕜)
    (fun x => ‖f x‖) hpR hFm hfM hraw (fun x => norm_nonneg _)
    (fun n => (Ch04.AeCommonException.almostEverywhere_iff_native μ _).mpr
      (ae_of_all μ (fun x => norm_indicator_le_norm_self (s := E n) (f := (f : X → 𝕜)) (a := x))))
    ((Ch04.AeCommonException.almostEverywhere_iff_native μ _).mpr hlim)
  have ht := hd.2.2.2
  change Tendsto (fun n => Ch10.LpDefinition.powerNorm μ p.toReal
    (fun x => F n x - f x)) atTop (𝓝 0) at ht
  have he n : Ch10.LpDefinition.powerNorm μ p.toReal (fun x => F n x - f x) =
      eLpNorm (fun x => F n x - f x) p μ := by
    calc
      _ = eLpNorm (fun x => F n x - f x) (ENNReal.ofReal p.toReal) μ :=
        Ch10.LpDefinition.powerNorm_eq_eLpNorm μ p.toReal _ hpR ((hFm n).sub hfM)
      _ = _ := by rw [ENNReal.ofReal_toReal hp]
  simp_rw [he] at ht
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ f).mpr
  convert ht using 1
  ext n
  apply eLpNorm_congr_ae
  exact (cutoffLp_coe μ p (E n) (hE n) f).sub EventuallyEq.rfl


/-- Apply finite-measure duality to the functional restricted by extension by
zero. The resulting ambient density represents exactly the cutoff functional. -/
lemma finite_piece_density (μ : Measure X) [SigmaFinite μ]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ∞) (ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜)
    (A : Set X) (hA : MeasurableSet A) (hfin : μ A < ∞) :
    ∃ H : Lp 𝕜 q μ,
      (∀ f, IntegralPairing.pairing μ p q H f = ℓ (cutoffLp μ p A hA f)) ∧
      ‖H‖ ≤ ‖ℓ‖ := by
  let : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hfin.ne
  obtain ⟨k, hk, _⟩ := LpDualFiniteMeasure.finite_measure_duality
    (μ.restrict A) p q hp (ℓ.comp (extendLp μ p A hA))
  let H := extendLp μ q A hA k
  have hr f : IntegralPairing.pairing μ p q H f = ℓ (cutoffLp μ p A hA f) := by
    rw [show H = extendLp μ q A hA k from rfl, pairing_extend]
    exact (IntegralPairing.pairing_eq_integral (μ.restrict A) p q k _).2.trans
      ((hk.1 _).2.symm)
  refine ⟨H, hr, ?_⟩
  rw [← pairing_norm μ p q H]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  rw [hr]
  exact (ℓ.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_cutoffLp_le μ p A hA f) (norm_nonneg _))

/-- Compatible ordinary a.e. densities on an increasing measurable exhaustion
have a measurable global representative. All exceptional sets are countable. -/
lemma glue_exhaustion [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (E : ℕ → Set X) (hE : ∀ n, MeasurableSet (E n))
    (hmono : Monotone E) (hcover : ⋃ n, E n = univ)
    (H : ℕ → Lp 𝕜 q μ)
    (hcomp : ∀ n m, n ≤ m → cutoffLp μ q (E n) (hE n) (H m) = H n) :
    ∃ h : X → 𝕜, Measurable h ∧
      (∀ n, (H n : X → 𝕜) =ᵐ[μ] (E n).indicator h) ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => H n x) atTop (𝓝 (h x))) := by
  classical
  have hpair n m : ∀ᵐ x ∂μ, x ∈ E n → x ∈ E m → H n x = H m x := by
    rcases le_total n m with hnm | hmn
    · have he := cutoffLp_coe μ q (E n) (hE n) (H m)
      rw [hcomp n m hnm] at he
      filter_upwards [he] with x hx hn hm
      exact hx.trans (Set.indicator_of_mem hn _)
    · have he := cutoffLp_coe μ q (E m) (hE m) (H n)
      rw [hcomp m n hmn] at he
      filter_upwards [he] with x hx hn hm
      exact (hx.trans (Set.indicator_of_mem hm _)).symm
  obtain ⟨h, hm, hpiece⟩ := exists_measurable_piecewise (disjointed E)
    (MeasurableSet.disjointed hE) (fun n => (H n : X → 𝕜))
    (fun n => (Lp.stronglyMeasurable (H n)).measurable) (by
      intro n m hnm x hx
      exact False.elim ((disjoint_disjointed E hnm).le_bot hx))
  have hpatch n : (H n : X → 𝕜) =ᵐ[μ] (E n).indicator h := by
    have hs := cutoffLp_coe μ q (E n) (hE n) (H n)
    rw [hcomp n n le_rfl] at hs
    filter_upwards [ae_all_iff.mpr (hpair n), hs] with x hx hxs
    by_cases hxE : x ∈ E n
    · rw [Set.indicator_of_mem hxE]
      have hxU : x ∈ ⋃ m, disjointed E m := by
        rw [iUnion_disjointed, hcover]
        exact mem_univ x
      obtain ⟨m, hxm⟩ := mem_iUnion.mp hxU
      exact (hx m hxE (disjointed_subset E m hxm)).trans (hpiece m hxm).symm
    · simpa only [Set.indicator_of_notMem hxE] using hxs
  refine ⟨h, hm, hpatch, ?_⟩
  filter_upwards [ae_all_iff.mpr hpatch] with x hx
  obtain ⟨N, hxN⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  exact ((hx n).trans (Set.indicator_of_mem (hmono hn hxN) _)).symm

/-- Scalar duality on sigma-finite measure spaces, with ordinary a.e.
uniqueness, product integrability, and the exact norm, including p=1. -/
theorem sigmaFinite_duality : Specs.D11.Ch20.LpDualSigmafiniteLocal.sigmaFinite_duality := by
  intro X 𝕜 _ _ μ _ p q _ _ _ hp ℓ
  borelize 𝕜
  obtain ⟨E, hEfin, hmono, hcover⟩ :=
    Ch01.ExhaustionRestriction.sigmaFinite_iff_increasing_exhaustion μ |>.mp inferInstance
  have hE n := (hEfin n).1
  choose H hH hbound using
    (fun n => finite_piece_density μ p q hp ℓ (E n) (hE n) (hEfin n).2)
  have hcomp n m (hnm : n ≤ m) : cutoffLp μ q (E n) (hE n) (H m) = H n := by
    apply pairing_injective μ p q
    ext f
    rw [pairing_cutoff, hH m, cutoffLp_comp μ p (E n) (E m) (hE n) (hE m)
      (hmono hnm), hH n]
  obtain ⟨h, hm, hpatch, hlim⟩ := glue_exhaustion μ q E hE hmono hcover H hcomp
  have hnorm n : eLpNorm (H n : X → 𝕜) q μ ≤ ENNReal.ofReal ‖ℓ‖ := by
    rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (H n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hnormlim : eLpNorm h q μ ≤ ENNReal.ofReal ‖ℓ‖ :=
    Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hnorm)
      (fun n => Lp.aestronglyMeasurable (H n)) hm.aestronglyMeasurable hlim
  have hmem : MemLp h q μ := hnormlim.trans_lt ENNReal.ofReal_lt_top
  let g : Lp 𝕜 q μ := hmem.toLp h
  have hgpatch n : cutoffLp μ q (E n) (hE n) g = H n := by
    apply Lp.ext
    exact (cutoffLp_coe μ q (E n) (hE n) g).trans
      (((ae_eq_restrict_iff_indicator_ae_eq (hE n)).mp
        (ae_restrict_of_ae (MemLp.coeFn_toLp hmem))).trans (hpatch n).symm)
  have heq : IntegralPairing.pairing μ p q g = ℓ := by
    ext f
    have heqcut n : IntegralPairing.pairing μ p q g
        (cutoffLp μ p (E n) (hE n) f) = ℓ (cutoffLp μ p (E n) (hE n) f) := by
      rw [← pairing_cutoff, hgpatch, hH n]
    have ht := cutoffLp_tendsto μ p hp E hE hmono hcover f
    exact tendsto_nhds_unique
      (((IntegralPairing.pairing μ p q g).continuous.tendsto f).comp ht)
      (((ℓ.continuous.tendsto f).comp ht).congr (fun n => (heqcut n).symm))
  have hgnorm : ‖g‖ = ‖ℓ‖ := (pairing_norm μ p q g).symm.trans (congrArg norm heq)
  refine ⟨g, ⟨fun f => ⟨(IntegralPairing.pairing_eq_integral μ p q g f).1, ?_⟩,
    hgnorm⟩, ?_⟩
  · exact (congrArg (fun L : Lp 𝕜 p μ →L[𝕜] 𝕜 => L f) heq).symm.trans
      (IntegralPairing.pairing_eq_integral μ p q g f).2
  · intro k hk
    apply pairing_injective μ p q
    calc
      IntegralPairing.pairing μ p q k = ℓ := by
        ext f
        exact (IntegralPairing.pairing_eq_integral μ p q k f).2.trans ((hk.1 f).2.symm)
      _ = IntegralPairing.pairing μ p q g := heq.symm

end D11.Ch20.LpDualSigmafiniteLocal
