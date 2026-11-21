import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.WeylGroupsAndUncertainty
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.PositionAndMomentum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.StoneTheorem

set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform ComplexConjugate Topology

namespace ExpandedFA.Models.WeylGroupsAndUncertainty
open PositionMomentum ExpandedFA.Fourier ExpandedFA.Unbounded

lemma selfAdjoint_formal {A : Operator ℂ H H} (hA : _root_.IsSelfAdjoint A) :
    A.IsFormalAdjoint A := by
  have h := A.adjoint_isFormalAdjoint hA.dense_domain
  rwa [LinearPMap.isSelfAdjoint_def.mp hA] at h

lemma schwartz_commutator (φ : S) :
    schwartzPosition (schwartzMomentum φ) - schwartzMomentum (schwartzPosition φ) =
      Complex.I • φ := by
  ext x
  simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul,
    schwartzPosition_apply, schwartzMomentum_apply]
  have heq : (schwartzPosition φ : Euclidean 1 → ℂ) = fun y => (y 0 : ℂ) * φ y :=
    funext (schwartzPosition_apply φ)
  rw [heq]
  have hf := fderiv_mul (𝕜 := ℝ) (c := fun y : Euclidean 1 => (y 0 : ℂ))
    (d := (φ : Euclidean 1 → ℂ)) (x := x) (by fun_prop) φ.differentiableAt
  change fderiv ℝ (fun y : Euclidean 1 => (y 0 : ℂ) * φ y) x = _ at hf
  rw [hf]
  have hcoord : fderiv ℝ (fun y : Euclidean 1 => (y 0 : ℂ)) x
      (basisVector (d := 1) 0) = 1 := by
    have he : (fun y : Euclidean 1 => (y 0 : ℂ)) =
        Complex.ofRealCLM ∘ realLineCoordinates.toContinuousLinearEquiv.toContinuousLinearMap := rfl
    rw [he, fderiv_comp x (by fun_prop) (by fun_prop)]
    rw [ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
    change ((basisVector (d := 1) 0) 0 : ℂ) = 1
    simp [basisVector]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hcoord]
  ring

lemma schwartz_weak_commutator (φ : S) :
    inner ℂ ((schwartzPosition φ).toLp 2 volume) ((schwartzMomentum φ).toLp 2 volume) -
      inner ℂ ((schwartzMomentum φ).toLp 2 volume) ((schwartzPosition φ).toLp 2 volume) =
        Complex.I * (‖φ.toLp 2 volume‖ ^ 2 : ℝ) := by
  have hi (ψ : S) := invariance ψ
  let f : position.domain := ⟨φ.toLp 2 volume, schwartz_le_position ⟨φ, rfl⟩⟩
  let g : position.domain := ⟨(schwartzMomentum φ).toLp 2 volume,
    schwartz_le_position ⟨schwartzMomentum φ, rfl⟩⟩
  let u : momentum.domain := ⟨φ.toLp 2 volume, schwartz_le_momentum ⟨φ, rfl⟩⟩
  let v : momentum.domain := ⟨(schwartzPosition φ).toLp 2 volume,
    schwartz_le_momentum ⟨schwartzPosition φ, rfl⟩⟩
  have hq : ∀ ψ : S, ∀ h : ψ.toLp 2 volume ∈ position.domain,
      position ⟨ψ.toLp 2 volume, h⟩ = (schwartzPosition ψ).toLp 2 volume := by
    intro ψ h
    exact position.mem_graph_snd_inj (position.mem_graph _) (hi ψ).1 rfl
  have hp : ∀ ψ : S, ∀ h : ψ.toLp 2 volume ∈ momentum.domain,
      momentum ⟨ψ.toLp 2 volume, h⟩ = (schwartzMomentum ψ).toLp 2 volume := by
    intro ψ h
    exact momentum.mem_graph_snd_inj (momentum.mem_graph _) (hi ψ).2 rfl
  have h₁ := selfAdjoint_formal position_selfAdjoint f g
  have h₂ := selfAdjoint_formal momentum_selfAdjoint u v
  change inner ℂ (position f) ((schwartzMomentum φ).toLp 2 volume) =
    inner ℂ (φ.toLp 2 volume) (position g) at h₁
  change inner ℂ (momentum u) ((schwartzPosition φ).toLp 2 volume) =
    inner ℂ (φ.toLp 2 volume) (momentum v) at h₂
  simp only [f, g, u, v, hq, hp] at h₁ h₂
  rw [h₁, h₂, ← inner_sub_right]
  have he : (schwartzPosition (schwartzMomentum φ)).toLp 2 volume -
      (schwartzMomentum (schwartzPosition φ)).toLp 2 volume =
        Complex.I • φ.toLp 2 volume := by
    change (SchwartzMap.toLpCLM ℂ ℂ (E := Euclidean 1) 2 volume) _ -
      (SchwartzMap.toLpCLM ℂ ℂ (E := Euclidean 1) 2 volume) _ =
      Complex.I • (SchwartzMap.toLpCLM ℂ ℂ (E := Euclidean 1) 2 volume) φ
    rw [← map_sub, schwartz_commutator, map_smul]
  rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
  norm_cast

 theorem weak_commutator : Spec.WeakCommutator := by
  intro f hq hp
  let F : H × H × H → ℂ := fun z => inner ℂ z.2.1 z.2.2 - inner ℂ z.2.2 z.2.1
  let G : H × H × H → ℂ := fun z => Complex.I * (‖z.1‖ ^ 2 : ℝ)
  have hc : IsClosed {z | F z = G z} := isClosed_eq (by unfold F; fun_prop) (by unfold G; fun_prop)
  have hs : closure (Set.range jointSchwartzGraph) ⊆ {z | F z = G z} := by
    apply closure_minimal _ hc
    rintro _ ⟨φ, rfl⟩
    exact schwartz_weak_commutator φ
  exact hs (jointGraph_mem_closure f hq hp)

lemma selfAdjoint_mean_im {A : Operator ℂ H H} (hA : _root_.IsSelfAdjoint A)
    (f : A.domain) : (inner ℂ (f : H) (A f)).im = 0 := by
  have he := congrArg Complex.im (selfAdjoint_formal hA f f)
  rw [← inner_conj_symm (A f) (f : H), Complex.conj_im] at he
  linarith

theorem real_means : Spec.RealMeans := fun f hq hp =>
  ⟨selfAdjoint_mean_im position_selfAdjoint ⟨f, hq⟩,
    selfAdjoint_mean_im momentum_selfAdjoint ⟨f, hp⟩⟩

lemma centered_im (f Q P : H) (q p : ℝ)
    (hQ : (inner ℂ f Q).im = 0) (hP : (inner ℂ f P).im = 0) :
    (inner ℂ (Q - (q : ℂ) • f) (P - (p : ℂ) • f)).im = (inner ℂ Q P).im := by
  have hQ' : (inner ℂ Q f).im = 0 := by rw [← inner_conj_symm Q f, Complex.conj_im, hQ, neg_zero]
  have hself : (inner ℂ f f).im = 0 := inner_self_im (𝕜 := ℂ) f
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, hQ', hP, hself, mul_zero, zero_mul, add_zero, zero_add, sub_zero]

theorem uncertainty : Spec.Uncertainty := by
  intro f hq hp hf
  dsimp
  have hm := real_means f hq hp
  have hc := congrArg Complex.im (weak_commutator f hq hp)
  rw [Complex.sub_im, ← inner_conj_symm (momentum ⟨f, hp⟩) (position ⟨f, hq⟩),
    Complex.conj_im] at hc
  simp only [hf, one_pow, Complex.ofReal_one, mul_one, Complex.I_im] at hc
  have hi : (inner ℂ (position ⟨f, hq⟩) (momentum ⟨f, hp⟩)).im = 1 / 2 := by linarith
  calc
    (1 / 2 : ℝ) = (inner ℂ
        (position ⟨f, hq⟩ - ((inner ℂ f (position ⟨f, hq⟩)).re : ℂ) • f)
        (momentum ⟨f, hp⟩ - ((inner ℂ f (momentum ⟨f, hp⟩)).re : ℂ) • f)).im := by
      rw [centered_im _ _ _ _ _ hm.1 hm.2, hi]
    _ ≤ ‖inner ℂ _ _‖ := Complex.im_le_norm _
    _ ≤ _ := norm_inner_le_norm _ _


open ExpandedFA.Semigroups.Stone ExpandedFA.Sobolev.FourierScale

/-- Phase multiplication, with a real scaling parameter for the Fourier model. -/
def phase (c a : ℝ) (x : Euclidean 1) : ℂ :=
  Complex.exp ((c * a * x 0 : ℝ) * Complex.I)

lemma phase_growth (c a : ℝ) : (phase c a).HasTemperateGrowth := by
  change ((fun r : ℝ => Complex.exp (r * Complex.I)) ∘
    (fun x : Euclidean 1 => c * a * x 0)).HasTemperateGrowth
  apply Function.HasTemperateGrowth.comp Complex.hasTemperateGrowth_exp_mul_I
  exact (Function.HasTemperateGrowth.const _).mul
    realLineCoordinates.toContinuousLinearEquiv.toContinuousLinearMap.hasTemperateGrowth

lemma phase_norm (c a : ℝ) (x : Euclidean 1) : ‖phase c a x‖ = 1 := by
  simp [phase, Complex.norm_exp]

def phaseMap (c a : ℝ) : H →L[ℂ] H :=
  multiplierL2CLM (phase c a) (phase_growth c a) (fun x => (phase_norm c a x).le)

lemma phaseMap_coe (c a : ℝ) (f : H) :
    phaseMap c a f =ᵐ[volume] fun x => phase c a x * f x :=
  multiplierL2_coe (phase c a) (phase_growth c a) (fun x => (phase_norm c a x).le) f

lemma phaseMap_zero (c : ℝ) (f : H) : phaseMap c 0 f = f := by
  apply Lp.ext
  filter_upwards [phaseMap_coe c 0 f] with x hx
  simpa [phase] using hx

lemma phaseMap_add (c a b : ℝ) (f : H) :
    phaseMap c (a + b) f = phaseMap c a (phaseMap c b f) := by
  apply Lp.ext
  filter_upwards [phaseMap_coe c (a + b) f, phaseMap_coe c a (phaseMap c b f),
    phaseMap_coe c b f] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, ← mul_assoc]
  congr 1
  simp only [phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma phaseMap_norm (c a : ℝ) (f : H) : ‖phaseMap c a f‖ = ‖f‖ := by
  apply le_antisymm
  · change ‖multiplierL2 (phase c a) (phase_growth c a) (fun x => (phase_norm c a x).le) f‖ ≤ ‖f‖
    simpa using multiplierL2_norm_le (phase c a) (phase_growth c a)
      (fun x => (phase_norm c a x).le) f
  · have hn : ‖f‖ ≤ 1 * ‖phaseMap c a f‖ := Lp.norm_le_mul_norm_of_ae_le_mul (c := 1) (by
      filter_upwards [phaseMap_coe c a f] with x hx
      simp [hx, norm_mul, phase_norm])
    simpa using hn

def phaseUnitary (c a : ℝ) : H ≃ₗᵢ[ℂ] H where
  toFun := phaseMap c a
  invFun := phaseMap c (-a)
  map_add' := (phaseMap c a).map_add
  map_smul' := (phaseMap c a).map_smul
  left_inv f := by rw [← phaseMap_add, neg_add_cancel, phaseMap_zero]
  right_inv f := by rw [← phaseMap_add, add_neg_cancel, phaseMap_zero]
  norm_map' := phaseMap_norm c a

/-- A dominated convergence criterion phrased entirely on L² classes. -/
lemma l2_dominated_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (v : ι → H) (w : H) (g : ι → Euclidean 1 → ℂ) (B : Euclidean 1 → ℝ)
    (hcoe : ∀ i, (v i - w : H) =ᵐ[volume] g i)
    (hm : ∀ᶠ i in l, AEStronglyMeasurable (g i) volume)
    (hB : Integrable (fun x => B x ^ 2) volume)
    (hb : ∀ᶠ i in l, ∀ᵐ x ∂volume, ‖g i x‖ ≤ B x)
    (ht : ∀ᵐ x ∂volume, Tendsto (fun i => g i x) l (𝓝 0)) :
    Tendsto v l (𝓝 w) := by
  have hi : Tendsto (fun i => ∫ x, ‖g i x‖ ^ 2) l (𝓝 0) := by
    have hi := tendsto_integral_filter_of_dominated_convergence
      (F := fun i x => ‖g i x‖ ^ 2) (f := fun _ => (0 : ℝ)) (fun x => B x ^ 2)
      (hm.mono fun i hi => hi.norm.pow 2)
      (hb.mono fun i hi => hi.mono fun x hx => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) hx 2)
      hB (ht.mono fun x hx => by simpa using hx.norm.pow 2)
    simpa using hi
  have hn : Tendsto (fun i => ‖v i - w‖ ^ 2) l (𝓝 0) := by
    convert hi using 1
    ext i
    rw [PositionMomentum.l2_norm_sq]
    exact integral_congr_ae ((hcoe i).fun_comp (fun z : ℂ => ‖z‖ ^ 2))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  change Tendsto (fun i => Real.sqrt (‖v i - w‖ ^ 2)) l (𝓝 (Real.sqrt 0)) at hs
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs

lemma phaseMap_continuous (c : ℝ) (f : H) : Continuous (fun a => phaseMap c a f) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply l2_dominated_tendsto (fun t => phaseMap c t f) (phaseMap c a f)
    (fun t x => (phase c t x - phase c a x) * f x) (fun x => 2 * ‖f x‖)
  · intro t
    filter_upwards [Lp.coeFn_sub (phaseMap c t f) (phaseMap c a f),
      phaseMap_coe c t f, phaseMap_coe c a f] with x hx hy hz
    simp only [hx, Pi.sub_apply, hy, hz, sub_mul]
  · exact Eventually.of_forall fun t =>
      (((phase_growth c t).1.continuous.aestronglyMeasurable.sub
        (phase_growth c a).1.continuous.aestronglyMeasurable).mul (Lp.aestronglyMeasurable f))
  · simpa only [mul_pow] using
      ((Lp.memLp f).integrable_norm_pow (by norm_num)).const_mul ((2 : ℝ)^2)
  · exact Eventually.of_forall fun t => Eventually.of_forall fun x => by
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa only [phase_norm, one_add_one_eq_two] using norm_sub_le (phase c t x) (phase c a x)
  · exact Eventually.of_forall fun x => by
      have hp : Continuous (fun t : ℝ => phase c t x) := by unfold phase; fun_prop
      simpa using ((hp.tendsto a).sub_const (phase c a x)).mul_const (f x)

def multiplicationGroup (c : ℝ) : UnitaryGroup H where
  operators := phaseUnitary c
  at_zero := phaseMap_zero c
  add_time := phaseMap_add c
  continuous_orbit := phaseMap_continuous c


def scaledPosition (c : ℝ) : Operator ℂ H H :=
  Multiplication.maximalMultiplier volume 2 (fun x : Euclidean 1 => (c * x 0 : ℝ))

lemma phase_exponential (c a : ℝ) (x : Euclidean 1) :
    phase c a x = exponentialSymbol a (c * x 0) := by
  unfold phase exponentialSymbol
  congr 1
  push_cast
  ring

lemma multiplicationGroup_derivative (c : ℝ) (f : (scaledPosition c).domain) :
    HasDerivative (multiplicationGroup c) f (Complex.I • scaledPosition c f) := by
  let A := scaledPosition c
  let w : H := Complex.I • A f
  let v : ℝ → H := fun h => if h = 0 then w else differenceQuotient (multiplicationGroup c) h f
  have hw : w =ᵐ[volume] fun x => Complex.I * (c * x 0 : ℝ) * (f : H) x := by
    filter_upwards [Lp.coeFn_smul Complex.I (A f),
      Multiplication.maximalLpMultiplier_apply volume 2 _ f] with x hs ha
    change (A f : H) x = (c * x 0 : ℝ) * (f : H) x at ha
    simp only [w, hs, Pi.smul_apply, smul_eq_mul, ha, mul_assoc]
  have hcoe (h : ℝ) : (v h - w : H) =ᵐ[volume]
      fun x => (derivativeMultiplier h (c * x 0) - 1) * w x := by
    by_cases hh : h = 0
    · subst h
      filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure (Euclidean 1))] with x hx
      simpa only [v, if_pos rfl, sub_self, derivativeMultiplier_zero, sub_self,
        zero_mul, Pi.zero_apply] using hx
    · filter_upwards [Lp.coeFn_sub (v h) w,
        Lp.coeFn_smul ((h : ℂ)⁻¹) (phaseMap c h (f : H) - (f : H)),
        Lp.coeFn_sub (phaseMap c h (f : H)) (f : H), phaseMap_coe c h (f : H), hw] with x hs hd hsub hphase hval
      rw [hs]
      simp only [Pi.sub_apply, v, if_neg hh]
      change differenceQuotient (multiplicationGroup c) h f x - w x = _
      change (((h : ℂ)⁻¹) • (phaseMap c h (f : H) - (f : H)) : H) x - w x = _
      rw [hd, Pi.smul_apply, smul_eq_mul, hsub, Pi.sub_apply, hphase, phase_exponential]
      have hmul : exponentialSymbol h (c * x 0) * (f : H) x - (f : H) x =
          (exponentialSymbol h (c * x 0) - 1) * (f : H) x := by ring
      rw [hmul, ← derivativeMultiplier_identity, hval]
      have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
      field_simp
      <;> ring
  have ht : Tendsto v (𝓝 (0 : ℝ)) (𝓝 w) := by
    apply l2_dominated_tendsto v w
      (fun h x => (derivativeMultiplier h (c * x 0) - 1) * w x)
      (fun x => 2 * ‖w x‖) hcoe
    · exact Eventually.of_forall fun h =>
        ((((continuous_derivativeMultiplier h).comp (by fun_prop)).aestronglyMeasurable.sub
          aestronglyMeasurable_const).mul (Lp.aestronglyMeasurable w))
    · simpa only [mul_pow] using
        ((Lp.memLp w).integrable_norm_pow (by norm_num)).const_mul ((2 : ℝ)^2)
    · exact Eventually.of_forall fun h => Eventually.of_forall fun x => by
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (norm_sub_le _ _).trans (by
          have hb := derivativeMultiplier_bound h (c * x 0)
          rw [norm_one]
          linarith)
    · exact Eventually.of_forall fun x => by
        simpa using ((derivativeMultiplier_tendsto (c * x 0)).sub_const 1).mul_const (w x)
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hh
  simp only [v, if_neg hh]

lemma scaledPosition_selfAdjoint (c : ℝ) : _root_.IsSelfAdjoint (scaledPosition c) := by
  apply Multiplication.multiplier_real_selfAdjoint volume
  · fun_prop
  · exact Eventually.of_forall fun _ => rfl

/-- Identifies the spectral exponential from derivatives on the full domain;
maximality supplies the converse domain inclusion. -/
lemma spectral_of_domain_derivatives (U : UnitaryGroup H) (A : Operator ℂ H H)
    (hA : _root_.IsSelfAdjoint A)
    (hd : ∀ f : A.domain, HasDerivative U f (Complex.I • A f)) :
    SpectralExponential A U ∧ DerivativeGraph U A := by
  have hAs : ExpandedFA.Unbounded.IsSelfAdjoint A :=
    ⟨hA.dense_domain, (LinearPMap.isSelfAdjoint_def.mp hA).symm⟩
  have he := selfAdjoint_eq_of_le_symmetric A U.stoneOperator hAs U.stoneOperator_symmetric
    (le_stoneOperator_of_hasDerivative A U hd)
  obtain ⟨B, hB, hBU, hdB, _⟩ := stone_forward H U
  have hBeq := operator_eq_of_derivativeGraph U B U.stoneOperator hdB U.derivativeGraph_stoneOperator
  rw [hBeq, ← he] at hBU hdB
  exact ⟨hBU, hdB⟩

lemma multiplicationGroup_spectral (c : ℝ) :
    SpectralExponential (scaledPosition c) (multiplicationGroup c) ∧
      DerivativeGraph (multiplicationGroup c) (scaledPosition c) :=
  spectral_of_domain_derivatives _ _ (scaledPosition_selfAdjoint c) (multiplicationGroup_derivative c)

lemma scaledPosition_one : scaledPosition 1 = position := by
  unfold scaledPosition position canonicalPosition
  congr 1
  funext x
  simp

/-- Conjugation by the negative-2πi Fourier transform. -/
def translationGroup : UnitaryGroup H where
  operators b := (l2Fourier 1).trans ((multiplicationGroup (2 * Real.pi)).operators b) |>.trans (l2Fourier 1).symm
  at_zero x := by simp [multiplicationGroup, phaseUnitary, phaseMap_zero]
  add_time b a x := by
    change (l2Fourier 1).symm (phaseMap (2 * Real.pi) (b+a) (l2Fourier 1 x)) =
      (l2Fourier 1).symm (phaseMap (2 * Real.pi) b (l2Fourier 1
        ((l2Fourier 1).symm (phaseMap (2 * Real.pi) a (l2Fourier 1 x)))))
    rw [LinearIsometryEquiv.apply_symm_apply, phaseMap_add]
  continuous_orbit x := (l2Fourier 1).symm.continuous.comp (phaseMap_continuous (2 * Real.pi) (l2Fourier 1 x))

lemma translationGroup_derivative (f : momentum.domain) :
    HasDerivative translationGroup f (Complex.I • momentum f) := by
  have ht := multiplicationGroup_derivative (2 * Real.pi)
    ⟨l2Fourier 1 f, f.2⟩
  change Tendsto (fun h => differenceQuotient (multiplicationGroup (2 * Real.pi)) h
    (l2Fourier 1 f)) (𝓝[≠] (0 : ℝ)) _ at ht
  have hl := (l2Fourier 1).symm.continuous.continuousAt.tendsto.comp ht
  have heq (h : ℝ) : differenceQuotient translationGroup h f =
      (l2Fourier 1).symm (differenceQuotient (multiplicationGroup (2 * Real.pi)) h
        (l2Fourier 1 f)) := by
    simp only [differenceQuotient, map_smul, map_sub]
    change (h : ℂ)⁻¹ • ((l2Fourier 1).symm _ - (f : H)) =
      (h : ℂ)⁻¹ • ((l2Fourier 1).symm _ - (l2Fourier 1).symm (l2Fourier 1 f))
    rw [LinearIsometryEquiv.symm_apply_apply]
    rfl
  change Tendsto (fun h => differenceQuotient translationGroup h f) (𝓝[≠] (0 : ℝ)) _
  have hval : (l2Fourier 1).symm (Complex.I • (scaledPosition (2 * Real.pi))
      ⟨l2Fourier 1 f, f.2⟩) = Complex.I • momentum f := by
    rw [map_smul]
    rfl
  rw [hval] at hl
  exact hl.congr' (Eventually.of_forall fun h => (heq h).symm)

lemma translationGroup_spectral : SpectralExponential momentum translationGroup ∧
    DerivativeGraph translationGroup momentum :=
  spectral_of_domain_derivatives _ _ momentum_selfAdjoint translationGroup_derivative

/-- Pullback under x ↦ x+b, on the a.e. quotient. -/
def translateMap (b : ℝ) : H →ₗᵢ[ℂ] H :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : Euclidean 1 => x + b • basisVector (d := 1) 0)
    (measurePreserving_add_right volume _)

lemma translateMap_coe (b : ℝ) (f : H) :
    translateMap b f =ᵐ[volume] fun x => f (x + b • basisVector (d := 1) 0) :=
  Lp.coeFn_compMeasurePreserving _ _

lemma fourier_translate_schwartz (b : ℝ) (φ : S) :
    l2Fourier 1 (translateMap b (φ.toLp 2 volume)) =
      phaseMap (2 * Real.pi) b (l2Fourier 1 (φ.toLp 2 volume)) := by
  let t : Euclidean 1 := b • basisVector (d := 1) 0
  let ψ : Euclidean 1 → ℂ := fun x => φ (x + t)
  have hψ : MemLp ψ 2 volume := (φ.memLp 2 volume).comp_measurePreserving
    (measurePreserving_add_right volume t)
  have he : translateMap b (φ.toLp 2 volume) = hψ.toLp ψ := by
    apply Lp.ext
    filter_upwards [translateMap_coe b (φ.toLp 2 volume), hψ.coeFn_toLp,
      (measurePreserving_add_right volume t).quasiMeasurePreserving.ae_eq_comp (φ.coeFn_toLp 2 volume)]
      with x hx hy hz
    exact hx.trans (hz.trans hy.symm)
  rw [he]
  apply Lp.ext
  filter_upwards [Plancherel.integral_agreement_native ψ (φ.integrable.comp_add_right t) hψ,
    phaseMap_coe (2 * Real.pi) b (l2Fourier 1 (φ.toLp 2 volume)),
    Plancherel.integral_agreement_native φ φ.integrable (φ.memLp 2 volume)]
    with ξ h₁ h₂ h₃
  change (l2Fourier 1 (φ.toLp 2 volume) : Euclidean 1 → ℂ) ξ = (𝓕 (φ : Euclidean 1 → ℂ)) ξ at h₃
  rw [h₁, h₂, h₃]
  have ht := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ (Euclidean 1)) (φ : Euclidean 1 → ℂ) t) ξ
  change (𝓕 ψ) ξ = _ at ht
  rw [ht]
  congr 1
  simp only [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  congr 1
  simp [phase, t, realLine_inner, basisVector]
  <;> push_cast <;> ring

lemma fourier_translate (b : ℝ) (f : H) :
    l2Fourier 1 (translateMap b f) = phaseMap (2 * Real.pi) b (l2Fourier 1 f) := by
  have heq := (SchwartzMap.denseRange_toLpCLM (E := Euclidean 1)
    (F := ℂ) (p := 2) ENNReal.ofNat_ne_top).equalizer
      ((l2Fourier 1).continuous.comp (translateMap b).continuous)
      ((phaseMap (2 * Real.pi) b).continuous.comp (l2Fourier 1).continuous)
      (funext (fourier_translate_schwartz b))
  exact congrFun heq f

lemma translationGroup_formula (b : ℝ) (f : H) :
    translationGroup.operators b f =ᵐ[volume]
      fun x => f (x + b • basisVector (d := 1) 0) := by
  have he : translationGroup.operators b f = translateMap b f := by
    apply (l2Fourier 1).injective
    change l2Fourier 1 ((l2Fourier 1).symm _) = _
    rw [LinearIsometryEquiv.apply_symm_apply, fourier_translate]
    rfl
  rw [he]
  exact translateMap_coe b f

lemma weyl_relation (a b : ℝ) (f : H) :
    (multiplicationGroup 1).operators a (translationGroup.operators b f) =
      Complex.exp (-Complex.I * (a : ℂ) * (b : ℂ)) •
        translationGroup.operators b ((multiplicationGroup 1).operators a f) := by
  let t : Euclidean 1 := b • basisVector (d := 1) 0
  have hshift := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae_eq_comp
    (phaseMap_coe 1 a f)
  apply Lp.ext
  filter_upwards [phaseMap_coe 1 a (translationGroup.operators b f),
    translationGroup_formula b f,
    Lp.coeFn_smul (Complex.exp (-Complex.I * (a : ℂ) * (b : ℂ)))
      (translationGroup.operators b ((multiplicationGroup 1).operators a f)),
    translationGroup_formula b ((multiplicationGroup 1).operators a f), hshift]
    with x h₁ h₂ h₃ h₄ h₅
  change phaseMap 1 a (translationGroup.operators b f) x = _
  rw [h₁, h₂, h₃, Pi.smul_apply, smul_eq_mul, h₄]
  change phaseMap 1 a f (x + b • basisVector (d := 1) 0) =
    phase 1 a (x + b • basisVector (d := 1) 0) * f (x + b • basisVector (d := 1) 0) at h₅
  change phase 1 a x * f (x + b • basisVector (d := 1) 0) =
    _ * phaseMap 1 a f (x + b • basisVector (d := 1) 0)
  rw [h₅, ← mul_assoc]
  congr 1
  simp only [phase, ← Complex.exp_add]
  congr 1
  simp [t, basisVector]
  <;> push_cast <;> ring

theorem groups : Spec.Groups := by
  refine ⟨multiplicationGroup 1, translationGroup, ?_, ?_,
    translationGroup_spectral.1, translationGroup_spectral.2, ?_,
    translationGroup_formula, weyl_relation⟩
  · simpa only [scaledPosition_one] using (multiplicationGroup_spectral 1).1
  · simpa only [scaledPosition_one] using (multiplicationGroup_spectral 1).2
  · intro a f
    filter_upwards [phaseMap_coe 1 a f] with x hx
    change phaseMap 1 a f x = _
    rw [hx]
    congr 2
    unfold phase
    congr 1
    push_cast
    ring

end ExpandedFA.Models.WeylGroupsAndUncertainty
