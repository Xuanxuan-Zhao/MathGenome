import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Weyl.RegularWeylRepresentation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.LpTranslationContinuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

/-! Regular Weyl representations and their angular-frequency Schrödinger model.
The concrete identities are proved on representatives and then descend through
a.e. equality. Continuity uses dominated convergence for the multiplier and
the accepted norm continuity of translations. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
universe u

namespace ExpandedFA.Weyl
open RegularWeylRepresentationSpec

abbrev RegularWeylRepresentation : RegularRepresentationType.{u} := RegularRepresentationValue

def symplecticForm : SymplecticFormType := SymplecticFormValue

def weylPhase : WeylPhaseType := WeylPhaseValue

def schrodingerAction : SchrodingerActionType := SchrodingerActionValue

theorem schrodinger_representative : SchrodingerRepresentative := by
  intro d z f
  let g := Lp.compMeasurePreserving (p := (2 : ℝ≥0∞)) (fun t => t - z.1)
    (measurePreserving_sub_right volume z.1) f
  have h := MemLp.coeFn_toLp ((Lp.memLp g).congr_norm
    ((multiplier_continuous z).aestronglyMeasurable.mul (Lp.aestronglyMeasurable g))
    (.of_forall fun t => by simp only [Pi.mul_apply, norm_mul, multiplier_norm, one_mul]))
  filter_upwards [h, Lp.coeFn_compMeasurePreserving f
    (measurePreserving_sub_right volume z.1)] with t ht hg
  exact ht.trans (congrArg (multiplier z t * ·) hg)

theorem schrodinger_zero : SchrodingerZero := by
  intro d f
  apply Lp.ext
  filter_upwards [schrodinger_representative (0 : PhaseSpace d) f] with t ht
  simpa [multiplier] using ht

/-- The symmetric ordering gives exactly the phase in the manuscript. -/
theorem multiplier_weyl {d : ℕ} (z w : PhaseSpace d) (t : Configuration d) :
    multiplier z t * multiplier w (t - z.1) =
      WeylPhaseValue z w * multiplier (z + w) t := by
  unfold multiplier WeylPhaseValue SymplecticFormValue
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [← add_mul, ← add_mul, ← Complex.ofReal_add, ← Complex.ofReal_add]
  congr 2
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.sub_apply]
  rw [Finset.sum_div]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem schrodinger_weyl : SchrodingerWeylLaw := by
  intro d z w f
  apply Lp.ext
  have hw := (measurePreserving_sub_right (volume : Measure (Configuration d)) z.1).quasiMeasurePreserving.ae (schrodinger_representative w f)
  filter_upwards [schrodinger_representative z (SchrodingerActionValue w f), hw,
    Lp.coeFn_smul (WeylPhaseValue z w) (SchrodingerActionValue (z + w) f),
    schrodinger_representative (z + w) f] with t hz hw hs hzw
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hz, hw, hs, hzw, ← mul_assoc, multiplier_weyl, mul_assoc]
  congr 2
  congr 1
  simp only [Prod.fst_add]
  abel

theorem schrodinger_add {d : ℕ} (z : PhaseSpace d) (f g : SchrodingerSpace d) :
    SchrodingerActionValue z (f + g) = SchrodingerActionValue z f + SchrodingerActionValue z g := by
  apply Lp.ext
  have ha := (measurePreserving_sub_right (volume : Measure (Configuration d)) z.1).quasiMeasurePreserving.ae
    (Lp.coeFn_add f g)
  filter_upwards [schrodinger_representative z (f + g), ha,
    Lp.coeFn_add (SchrodingerActionValue z f) (SchrodingerActionValue z g),
    schrodinger_representative z f, schrodinger_representative z g] with t h ha hs hf hg
  simp only [Pi.add_apply] at ha hs
  rw [h, ha, mul_add, hs, hf, hg]

theorem schrodinger_smul {d : ℕ} (z : PhaseSpace d) (c : ℂ) (f : SchrodingerSpace d) :
    SchrodingerActionValue z (c • f) = c • SchrodingerActionValue z f := by
  apply Lp.ext
  have ha := (measurePreserving_sub_right (volume : Measure (Configuration d)) z.1).quasiMeasurePreserving.ae
    (Lp.coeFn_smul c f)
  filter_upwards [schrodinger_representative z (c • f), ha,
    Lp.coeFn_smul c (SchrodingerActionValue z f), schrodinger_representative z f] with t h ha hs hf
  simp only [Pi.smul_apply, smul_eq_mul] at ha hs
  rw [h, ha, hs, hf]
  ring

theorem schrodinger_norm {d : ℕ} (z : PhaseSpace d) (f : SchrodingerSpace d) :
    ‖SchrodingerActionValue z f‖ = ‖f‖ := by
  let g := Distributions.lpTranslation (E := ℂ) 2 z.1 f
  have hn : ‖SchrodingerActionValue z f‖ = ‖g‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    filter_upwards [schrodinger_representative z f,
      Distributions.lpTranslation_representative 2 z.1 f] with t ht hg
    change g t = f (t - z.1) at hg
    rw [ht, hg, norm_mul, multiplier_norm, one_mul]
  exact hn.trans (Lp.norm_compMeasurePreserving f (measurePreserving_sub_right volume z.1))

theorem weylPhase_neg_left {d : ℕ} (z : PhaseSpace d) : WeylPhaseValue (-z) z = 1 := by
  simp [WeylPhaseValue, SymplecticFormValue, neg_mul, mul_neg]

theorem weylPhase_neg_right {d : ℕ} (z : PhaseSpace d) : WeylPhaseValue z (-z) = 1 := by
  simp [WeylPhaseValue, SymplecticFormValue, neg_mul, mul_neg]

/-- The inverse is the operator at the negative phase-space vector. -/
def schrodingerLinearIsometryEquiv {d : ℕ} (z : PhaseSpace d) :
    SchrodingerSpace d ≃ₗᵢ[ℂ] SchrodingerSpace d where
  toFun := SchrodingerActionValue z
  invFun := SchrodingerActionValue (-z)
  left_inv f := by rw [schrodinger_weyl, weylPhase_neg_left, neg_add_cancel,
    schrodinger_zero, one_smul]
  right_inv f := by rw [schrodinger_weyl, weylPhase_neg_right, add_neg_cancel,
    schrodinger_zero, one_smul]
  map_add' := schrodinger_add z
  map_smul' := schrodinger_smul z
  norm_map' := schrodinger_norm z

theorem schrodinger_unitary : SchrodingerUnitary := by
  intro d z
  exact ⟨schrodingerLinearIsometryEquiv z, fun _ => rfl⟩

/-- Multiplication by the Weyl phase, without the spatial translation. -/
theorem multiplier_memLp {d : ℕ} (z : PhaseSpace d) (f : SchrodingerSpace d) :
    MemLp (fun t => multiplier z t * f t) 2 volume :=
  (Lp.memLp f).congr_norm
    ((multiplier_continuous z).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (.of_forall fun t => by simp only [norm_mul, multiplier_norm, one_mul])

def multiplyL2 {d : ℕ} (z : PhaseSpace d) (f : SchrodingerSpace d) : SchrodingerSpace d :=
  (multiplier_memLp z f).toLp (fun t => multiplier z t * f t)

theorem multiplyL2_coe {d : ℕ} (z : PhaseSpace d) (f : SchrodingerSpace d) :
    multiplyL2 z f =ᵐ[volume] fun t => multiplier z t * f t :=
  (multiplier_memLp z f).coeFn_toLp

theorem multiplyL2_isometry {d : ℕ} (z : PhaseSpace d) : Isometry (multiplyL2 z) := by
  apply Isometry.of_dist_eq
  intro f g
  rw [Lp.dist_def, Lp.dist_def]
  congr 1
  apply eLpNorm_congr_norm_ae
    ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))
    ((Lp.aestronglyMeasurable f).sub (Lp.aestronglyMeasurable g))
  filter_upwards [multiplyL2_coe z f, multiplyL2_coe z g] with t hf hg
  simp only [Pi.sub_apply, hf, hg, ← mul_sub, norm_mul, multiplier_norm, one_mul]

/-- Dominated convergence applies to a fixed L² vector: the squared error
is dominated by the square of `2 * f`, independently of the parameters. -/
theorem multiplyL2_continuous {d : ℕ} (f : SchrodingerSpace d) :
    Continuous (fun z => multiplyL2 z f) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun z => fun t => multiplier z t * f t) (fun z => multiplier_memLp z f)
    (fun t => multiplier z₀ t * f t) (multiplier_memLp z₀ f)).mpr
  have hm (z : PhaseSpace d) :=
    (multiplier_memLp z f).aestronglyMeasurable.sub (multiplier_memLp z₀ f).aestronglyMeasurable
  have hfin : (∫⁻ t, ‖(2 : ℂ) * f t‖ₑ ^ (2 : ℝ) ∂volume) < ∞ := by
    simpa using lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by simp) ((Lp.memLp f).const_mul (2 : ℂ)).eLpNorm_lt_top
  have hb (z : PhaseSpace d) (t : Configuration d) :
      ‖multiplier z t * f t - multiplier z₀ t * f t‖ₑ ^ (2 : ℝ) ≤
        ‖(2 : ℂ) * f t‖ₑ ^ (2 : ℝ) := by
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    apply enorm_le_iff_norm_le.mpr
    calc
      ‖multiplier z t * f t - multiplier z₀ t * f t‖ ≤
        ‖multiplier z t * f t‖ + ‖multiplier z₀ t * f t‖ := norm_sub_le _ _
      _ = ‖(2 : ℂ) * f t‖ := by
        simp only [norm_mul, multiplier_norm, one_mul]
        norm_num
        ring
  have hl := tendsto_lintegral_filter_of_dominated_convergence'
    (μ := (volume : Measure (Configuration d))) (l := 𝓝 z₀)
    (F := fun z t => ‖multiplier z t * f t - multiplier z₀ t * f t‖ₑ ^ (2 : ℝ))
    (f := fun _ => 0) (fun t => ‖(2 : ℂ) * f t‖ₑ ^ (2 : ℝ))
    (.of_forall fun z => (hm z).enorm.pow_const _)
    (.of_forall fun z => .of_forall (hb z)) hfin.ne
    (.of_forall fun t => by
      have hc : Continuous (fun z : PhaseSpace d => multiplier z t) := by
        unfold multiplier
        fun_prop
      have hc' : Continuous (fun z : PhaseSpace d =>
          multiplier z t * f t - multiplier z₀ t * f t) :=
        (hc.mul continuous_const).sub continuous_const
      have h := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).comp hc'.enorm
      simpa only [Function.comp_def, sub_self, enorm_zero,
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] using h.tendsto z₀)
  have hr := hl.ennrpow_const (1 / 2 : ℝ)
  simp only [lintegral_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hr
  convert hr using 1
  funext z
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) (hm z)]
  simp

/-- Joint continuity follows from the isometric bound in the vector variable. -/
theorem multiplyL2_joint_continuous {d : ℕ} :
    Continuous (fun zf : PhaseSpace d × SchrodingerSpace d => multiplyL2 zf.1 zf.2) :=
  continuous_prod_of_continuous_lipschitzWith' _ 1
    (fun z => (multiplyL2_isometry z).lipschitzWith) multiplyL2_continuous

theorem schrodinger_eq_multiply_translation {d : ℕ} (z : PhaseSpace d) (f : SchrodingerSpace d) :
    SchrodingerActionValue z f = multiplyL2 z (Distributions.lpTranslation 2 z.1 f) := by
  apply Lp.ext
  filter_upwards [schrodinger_representative z f,
    multiplyL2_coe z (Distributions.lpTranslation 2 z.1 f),
    Distributions.lpTranslation_representative 2 z.1 f] with t hs hm ht
  change Distributions.lpTranslation 2 z.1 f t = f (t - z.1) at ht
  rw [hs, hm, ht]

theorem schrodinger_strongContinuous : SchrodingerStrongContinuous := by
  intro d f
  have ht : Continuous (fun z : PhaseSpace d => Distributions.lpTranslation 2 z.1 f) :=
    (Distributions.lpTranslation_continuous (E := ℂ) (d := d) 2 (by simp) f).comp continuous_fst
  have hp : Continuous (fun z : PhaseSpace d => (z, Distributions.lpTranslation 2 z.1 f)) :=
    continuous_id.prodMk ht
  have h := (multiplyL2_joint_continuous (d := d)).comp
    (f := fun z : PhaseSpace d => (z, Distributions.lpTranslation 2 z.1 f)) hp
  exact h.congr (fun z => (schrodinger_eq_multiply_translation z f).symm)

theorem schrodingerSpace_nontrivial (d : ℕ) : Nontrivial (SchrodingerSpace d) := by
  let s := Set.Icc (0 : Configuration d) 1
  have hs : volume s = 1 := by simp [s, Real.volume_Icc_pi]
  let f : SchrodingerSpace d := indicatorConstLp 2 measurableSet_Icc (by rw [hs]; simp) (1 : ℂ)
  apply nontrivial_of_ne f 0
  intro hf
  have hn : ‖f‖ = 1 := by
    rw [norm_indicatorConstLp (by norm_num) (by simp)]
    simp [measureReal_def]
  rw [hf, norm_zero] at hn
  exact zero_ne_one hn

theorem schrodinger_regular : SchrodingerRegular := by
  intro d hd
  refine ⟨{
    dimension_pos := hd
    nontrivial_space := schrodingerSpace_nontrivial d
    W := schrodingerLinearIsometryEquiv
    zero := schrodinger_zero
    mul := schrodinger_weyl
    strong_continuous := schrodinger_strongContinuous }, fun _ _ => rfl⟩

end ExpandedFA.Weyl
