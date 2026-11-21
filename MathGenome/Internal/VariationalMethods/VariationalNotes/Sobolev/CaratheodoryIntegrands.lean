import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Data.EReal.Operations

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace VariationalNotes.Sobolev

variable {S E : Type*} [MeasurableSpace S] [TopologicalSpace E]

/-- Measurable sections and continuity outside one common null set. -/
def Caratheodory (μ : Measure S) (F : S → E → ℝ) : Prop :=
  (∀ y, Measurable (fun x => F x y)) ∧ ∀ᵐ x ∂μ, Continuous (F x)

/-- The ordinary integrability condition on the negative part. -/
def NegativePartIntegrable (μ : Measure S) (f : S → ℝ) : Prop :=
  Integrable (fun x => max (-f x) 0) μ

/-- Extended Lebesgue integral, used when the negative part is integrable.
Unlike the totalized real Bochner integral this retains a possible value `⊤`. -/
def extendedIntegral (μ : Measure S) (f : S → ℝ) : EReal :=
  (∫⁻ x, ENNReal.ofReal (f x) ∂μ : ℝ≥0∞) -
    (∫⁻ x, ENNReal.ofReal (-f x) ∂μ : ℝ≥0∞)

/-- Integral energy on representatives; the theorems establish descent modulo a.e. equality. -/
def integralEnergy (μ : Measure S) (F : S → E → ℝ) (y : S → E) : EReal :=
  extendedIntegral μ (fun x => F x (y x))

/-- State and variable finite product of independent fiber arguments. In particular,
`A = EuclideanSpace ℝ (Fin m)` and `B i = EuclideanSpace ℝ (Fin (d i))`
recover the state and mixed-exponent fibers in the source. -/
def MixedCaratheodory {A ι : Type*} {B : ι → Type*}
    [TopologicalSpace A] [∀ i, TopologicalSpace (B i)]
    (μ : Measure S) (F : S → A → (∀ i, B i) → ℝ) : Prop :=
  Caratheodory μ (fun x (v : A × (∀ i, B i)) => F x v.1 v.2)

/-- Energy on an `Lp` class, evaluated on its a.e. representative. -/
def lpIntegralEnergy {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (μ : Measure S) (F : S → E → ℝ) (y : Lp E p μ) : EReal :=
  integralEnergy μ F y


variable {S E : Type*} [MeasurableSpace S]

/-- Sections can be substituted with a simple measurable field. -/
theorem measurable_simple_substitution [Nonempty E] {F : S → E → ℝ}
    (hF : ∀ y, Measurable (fun x => F x y)) (y : SimpleFunc S E) :
    Measurable (fun x => F x (y x)) := by
  classical
  induction y using SimpleFunc.induction' with
  | const c => exact hF c
  | @pcw f g s hs hf hg =>
    have hh : (fun x => F x ((f.piecewise s hs g) x)) =
        s.piecewise (fun x => F x (f x)) (fun x => F x (g x)) := by
      ext x
      by_cases hx : x ∈ s <;> simp [SimpleFunc.coe_piecewise, Set.piecewise, hx]
    rw [hh]
    exact hf.piecewise hs hg

section Metric

variable [MeasurableSpace E] [PseudoMetricSpace E] [SecondCountableTopology E]
    [BorelSpace E] [Nonempty E]

/-- The countable-grid argument, for an everywhere continuous integrand. -/
theorem measurable_substitution {F : S → E → ℝ}
    (hF : ∀ y, Measurable (fun x => F x y)) (hC : ∀ x, Continuous (F x))
    {y : S → E} (hy : Measurable y) : Measurable (fun x => F x (y x)) := by
  let a : E := Classical.ofNonempty
  let yₙ := SimpleFunc.approxOn y hy Set.univ a (Set.mem_univ a)
  apply measurable_of_tendsto_metrizable
    (fun n => measurable_simple_substitution hF (yₙ n))
  apply tendsto_pi_nhds.mpr
  intro x
  exact (hC x).continuousAt.tendsto.comp
    (SimpleFunc.tendsto_approxOn hy (Set.mem_univ a) (by simp))

omit [MeasurableSpace E] [SecondCountableTopology E] [BorelSpace E] [Nonempty E] in
/-- One measurable null set suffices for all field values, and zero redefinition
there has measurable sections and continuous fibers everywhere. -/
theorem Caratheodory.exists_regularization {μ : Measure S} {F : S → E → ℝ}
    (hF : Caratheodory μ F) :
    ∃ (N : Set S) (G : S → E → ℝ), MeasurableSet N ∧ μ N = 0 ∧
      (∀ x ∉ N, ∀ y, G x y = F x y) ∧
      (∀ x ∈ N, ∀ y, G x y = 0) ∧
      (∀ y, Measurable (fun x => G x y)) ∧ (∀ x, Continuous (G x)) := by
  classical
  let N := toMeasurable μ {x | ¬ Continuous (F x)}
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN : μ N = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.mp hF.2
  let G : S → E → ℝ := fun x y => if x ∈ N then 0 else F x y
  refine ⟨N, G, hNm, hN, ?_, ?_, ?_, ?_⟩
  · intro x hx y
    exact ite_eq_right hx
  · intro x hx y
    exact ite_eq_left hx
  · intro y
    exact measurable_const.piecewise hNm (hF.1 y)
  · intro x
    by_cases hx : x ∈ N
    · simpa only [G, ite_eq_left hx] using (continuous_const : Continuous (fun _ : E => (0 : ℝ)))
    · have hC : Continuous (F x) := by
        by_contra h
        exact hx (subset_toMeasurable μ _ h)
      simpa only [G, ite_eq_right hx] using hC

/-- Composition is a.e. measurable on an arbitrary, possibly incomplete, measure space. -/
theorem Caratheodory.aemeasurable_substitution {μ : Measure S} {F : S → E → ℝ}
    (hF : Caratheodory μ F) {y : S → E} (hy : AEMeasurable y μ) :
    AEMeasurable (fun x => F x (y x)) μ := by
  obtain ⟨N, G, hNm, hN, hGF, _, hG, hC⟩ := hF.exists_regularization
  have hm := (measurable_substitution hG hC hy.measurable_mk).aemeasurable (μ := μ)
  apply hm.congr
  have hNc : ∀ᵐ x ∂μ, x ∉ N := measure_eq_zero_iff_ae_notMem.mp hN
  filter_upwards [hy.ae_eq_mk, hNc] with x hxy hx
  rw [← hxy]
  exact hGF x hx (y x)

/-- On a complete measure space the original composition itself is measurable. -/
theorem Caratheodory.measurable_substitution {μ : Measure S} [μ.IsComplete]
    {F : S → E → ℝ} (hF : Caratheodory μ F) {y : S → E} (hy : Measurable y) :
    Measurable (fun x => F x (y x)) :=
  aemeasurable_iff_measurable.mp (hF.aemeasurable_substitution hy.aemeasurable)

end Metric

section Energy

variable {μ : Measure S} {f g : S → ℝ}

/-- Finiteness of the negative-part integral, in the nonnegative integral convention. -/
theorem negativePartIntegrable_iff (hf : AEMeasurable f μ) :
    NegativePartIntegrable μ f ↔ (∫⁻ x, ENNReal.ofReal (-f x) ∂μ) ≠ ∞ := by
  have hm : AEStronglyMeasurable (fun x => max (-f x) 0) μ :=
    (hf.neg.max aemeasurable_const).aestronglyMeasurable
  simpa only [NegativePartIntegrable, ENNReal.ofReal_max, ENNReal.ofReal_zero,
    max_eq_left (zero_le : (0 : ℝ≥0∞) ≤ _)] using
    (lintegral_ofReal_ne_top_iff_integrable hm
      (Eventually.of_forall (fun x => le_max_right (-f x) 0))).symm

/-- Integrable lower bounds guarantee that the extended integral is well defined. -/
theorem negativePartIntegrable_of_lower_bound (hf : AEMeasurable f μ)
    {a : S → ℝ} (ha : Integrable a μ) (h : ∀ᵐ x ∂μ, -a x ≤ f x) :
    NegativePartIntegrable μ f := by
  apply ha.pos_part.mono_nonneg (hf.neg.max aemeasurable_const).aestronglyMeasurable
    (Eventually.of_forall (fun x => le_max_right (-f x) 0))
  filter_upwards [h] with x hx
  apply max_le_max _ le_rfl
  simpa only [Pi.neg_apply, neg_neg] using neg_le_neg hx

/-- A.e. changes preserve the domain of the extended integral. -/
theorem negativePartIntegrable_congr_ae (h : f =ᵐ[μ] g) :
    NegativePartIntegrable μ f ↔ NegativePartIntegrable μ g := by
  apply integrable_congr
  filter_upwards [h] with x hx
  rw [hx]

/-- The extended integral is insensitive to null-set changes. -/
theorem extendedIntegral_congr_ae (h : f =ᵐ[μ] g) :
    extendedIntegral μ f = extendedIntegral μ g := by
  unfold extendedIntegral
  congr 1
  · exact congrArg (fun z : ℝ≥0∞ => (z : EReal))
      (lintegral_congr_ae (h.fun_comp ENNReal.ofReal))
  · exact congrArg (fun z : ℝ≥0∞ => (z : EReal))
      (lintegral_congr_ae (h.fun_comp (fun t => ENNReal.ofReal (-t))))

/-- An integrable negative part rules out minus infinity. -/
theorem extendedIntegral_ne_bot (hf : AEMeasurable f μ)
    (hn : NegativePartIntegrable μ f) : extendedIntegral μ f ≠ ⊥ := by
  have hn' := (negativePartIntegrable_iff hf).mp hn
  simp only [extendedIntegral, sub_eq_add_neg, EReal.add_ne_bot_iff,
    EReal.coe_ennreal_ne_bot, ne_eq, EReal.neg_eq_bot_iff,
    EReal.coe_ennreal_eq_top_iff]
  exact ⟨not_false, hn'⟩

/-- Positive infinity is retained precisely when the positive-part integral is infinite. -/
theorem extendedIntegral_eq_top_iff (hf : AEMeasurable f μ)
    (hn : NegativePartIntegrable μ f) :
    extendedIntegral μ f = ⊤ ↔ (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = ∞ := by
  have hn' := (negativePartIntegrable_iff hf).mp hn
  simp [extendedIntegral, sub_eq_add_neg, EReal.add_eq_top_iff,
    EReal.neg_eq_bot_iff, EReal.neg_eq_top_iff, hn']

/-- On integrable functions this agrees with the usual Lebesgue integral. -/
theorem extendedIntegral_eq_integral (hf : Integrable f μ) :
    extendedIntegral μ f = (∫ x, f x ∂μ : ℝ) := by
  have hn := (negativePartIntegrable_iff hf.aestronglyMeasurable.aemeasurable).mp
    hf.neg_part
  have hp : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ∞ := by
    have hh := (negativePartIntegrable_iff hf.neg.aestronglyMeasurable.aemeasurable).mp
      hf.neg.neg_part
    simpa only [Pi.neg_apply, neg_neg] using hh
  rw [extendedIntegral, ← EReal.coe_ennreal_toReal hp, ← EReal.coe_ennreal_toReal hn,
    ← EReal.coe_sub, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]

/-- For nonnegative functions there is no negative contribution, including at infinite energy. -/
theorem extendedIntegral_of_nonneg (hf : ∀ᵐ x ∂μ, 0 ≤ f x) :
    extendedIntegral μ f = (∫⁻ x, ENNReal.ofReal (f x) ∂μ : ℝ≥0∞) := by
  have hn : (∫⁻ x, ENNReal.ofReal (-f x) ∂μ) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hf] with x hx
    exact ENNReal.ofReal_of_nonpos (neg_nonpos.mpr hx)
  simp [extendedIntegral, hn]

/-- The energy and its negative-part domain depend only on the field's a.e. class. -/
theorem integralEnergy_congr_ae {F : S → E → ℝ} {y y' : S → E}
    (h : y =ᵐ[μ] y') :
    integralEnergy μ F y = integralEnergy μ F y' ∧
      (NegativePartIntegrable μ (fun x => F x (y x)) ↔
       NegativePartIntegrable μ (fun x => F x (y' x))) := by
  have hh : (fun x => F x (y x)) =ᵐ[μ] (fun x => F x (y' x)) := by
    filter_upwards [h] with x hx
    rw [hx]
  exact ⟨extendedIntegral_congr_ae hh, negativePartIntegrable_congr_ae hh⟩

/-- Redefining an integrand on a common null set preserves every energy and its domain. -/
theorem integralEnergy_congr_integrand_ae {F G : S → E → ℝ}
    (h : ∀ᵐ x ∂μ, ∀ y, F x y = G x y) (y : S → E) :
    integralEnergy μ F y = integralEnergy μ G y ∧
      (NegativePartIntegrable μ (fun x => F x (y x)) ↔
       NegativePartIntegrable μ (fun x => G x (y x))) := by
  have hh := h.mono (fun x hx => hx (y x))
  exact ⟨extendedIntegral_congr_ae hh, negativePartIntegrable_congr_ae hh⟩

end Energy

section Mixed

variable {A ι : Type*} {B : ι → Type*} [Fintype ι]
    [MeasurableSpace A] [PseudoMetricSpace A] [SecondCountableTopology A]
    [BorelSpace A] [Nonempty A]
    [∀ i, MeasurableSpace (B i)] [∀ i, PseudoMetricSpace (B i)]
    [∀ i, SecondCountableTopology (B i)] [∀ i, BorelSpace (B i)]
    [∀ i, Nonempty (B i)]
    {μ : Measure S} {F : S → A → (∀ i, B i) → ℝ}

/-- Independent fibers may have different finite dimensions (and later different exponents). -/
theorem MixedCaratheodory.aemeasurable_substitution (hF : MixedCaratheodory μ F)
    {s : S → A} {z : ∀ i, S → B i} (hs : AEMeasurable s μ)
    (hz : ∀ i, AEMeasurable (z i) μ) :
    AEMeasurable (fun x => F x (s x) (fun i => z i x)) μ :=
  Caratheodory.aemeasurable_substitution
    (show Caratheodory μ (fun x (v : A × (∀ i, B i)) => F x v.1 v.2) from hF) (hs.prodMk (aemeasurable_pi_iff.mpr hz))

/-- The completed-space formulation for measurable state and component fields. -/
theorem MixedCaratheodory.measurable_substitution [μ.IsComplete]
    (hF : MixedCaratheodory μ F) {s : S → A} {z : ∀ i, S → B i}
    (hs : Measurable s) (hz : ∀ i, Measurable (z i)) :
    Measurable (fun x => F x (s x) (fun i => z i x)) :=
  aemeasurable_iff_measurable.mp
    (hF.aemeasurable_substitution hs.aemeasurable (fun i => (hz i).aemeasurable))

omit [Fintype ι] [MeasurableSpace A] [SecondCountableTopology A] [BorelSpace A]
    [Nonempty A] [∀ i, SecondCountableTopology (B i)] [∀ i, BorelSpace (B i)]
    [∀ i, Nonempty (B i)] [∀ i, MeasurableSpace (B i)] in
/-- Substituting the state preserves continuity in the full independent fiber, on
one common set of full measure. No regularity of the state is needed for this part. -/
theorem MixedCaratheodory.ae_continuous_fiber (hF : MixedCaratheodory μ F)
    (s : S → A) : ∀ᵐ x ∂μ, Continuous (F x (s x)) := by
  filter_upwards [hF.2] with x hx
  exact hx.comp (continuous_const.prodMk continuous_id)

/-- Measurable state substitution at a fixed fiber, on incomplete spaces as well. -/
theorem MixedCaratheodory.aemeasurable_state_section (hF : MixedCaratheodory μ F)
    {s : S → A} (hs : AEMeasurable s μ) (z : ∀ i, B i) :
    AEMeasurable (fun x => F x (s x) z) μ :=
  hF.aemeasurable_substitution hs (fun _ => aemeasurable_const)

end Mixed

section Lp

variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {μ : Measure S} {p : ℝ≥0∞} {F : S → E → ℝ}


theorem Caratheodory.aemeasurable_lp_substitution (hF : Caratheodory μ F)
    (y : Lp E p μ) : AEMeasurable (fun x => F x (y x)) μ :=
  hF.aemeasurable_substitution (Lp.aestronglyMeasurable y).aemeasurable

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Every `MemLp` representative gives exactly the class energy and the same domain. -/
theorem lpIntegralEnergy_toLp {y : S → E} (hy : MemLp y p μ) :
    lpIntegralEnergy μ F (hy.toLp y) = integralEnergy μ F y ∧
      (NegativePartIntegrable μ (fun x => F x ((hy.toLp y) x)) ↔
       NegativePartIntegrable μ (fun x => F x (y x))) :=
  integralEnergy_congr_ae hy.coeFn_toLp

/-- If the negative part is integrable, an `Lp` energy is finite or positive infinite. -/
theorem Caratheodory.lpIntegralEnergy_ne_bot (hF : Caratheodory μ F)
    (y : Lp E p μ) (hn : NegativePartIntegrable μ (fun x => F x (y x))) :
    lpIntegralEnergy μ F y ≠ ⊥ :=
  extendedIntegral_ne_bot (hF.aemeasurable_lp_substitution y) hn

end Lp

section MixedLp

variable {A ι : Type*} {B : ι → Type*} [Fintype ι]
    [NormedAddCommGroup A] [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
    [∀ i, NormedAddCommGroup (B i)] [∀ i, MeasurableSpace (B i)]
    [∀ i, BorelSpace (B i)] [∀ i, SecondCountableTopology (B i)]
    {μ : Measure S} {q : ℝ≥0∞} {r : ι → ℝ≥0∞}
    {F : S → A → (∀ i, B i) → ℝ}

/-- Mixed-exponent representatives need not belong to one common `Lp` space. -/
theorem MixedCaratheodory.aemeasurable_lp_substitution (hF : MixedCaratheodory μ F)
    (s : Lp A q μ) (z : ∀ i, Lp (B i) (r i) μ) :
    AEMeasurable (fun x => F x (s x) (fun i => z i x)) μ :=
  hF.aemeasurable_substitution (Lp.aestronglyMeasurable s).aemeasurable
    (fun i => (Lp.aestronglyMeasurable (z i)).aemeasurable)

omit [NormedAddCommGroup A] [MeasurableSpace A] [BorelSpace A]
    [SecondCountableTopology A] [∀ i, BorelSpace (B i)]
    [∀ i, SecondCountableTopology (B i)] [∀ i, NormedAddCommGroup (B i)]
    [∀ i, MeasurableSpace (B i)] in
/-- State and every fiber can independently be replaced by any a.e. representative. -/
theorem mixed_integralEnergy_congr_ae {s s' : S → A} {z z' : ∀ i, S → B i}
    (hs : s =ᵐ[μ] s') (hz : ∀ i, z i =ᵐ[μ] z' i) :
    integralEnergy μ (fun x (v : A × (∀ i, B i)) => F x v.1 v.2)
      (fun x => (s x, fun i => z i x)) =
    integralEnergy μ (fun x (v : A × (∀ i, B i)) => F x v.1 v.2)
      (fun x => (s' x, fun i => z' i x)) ∧
    (NegativePartIntegrable μ (fun x => F x (s x) (fun i => z i x)) ↔
     NegativePartIntegrable μ (fun x => F x (s' x) (fun i => z' i x))) := by
  apply integralEnergy_congr_ae
  filter_upwards [hs, ae_all_iff.mpr hz] with x hx hz
  simp only [hx, funext hz]

end MixedLp

/-- Specialization to the ordinary coordinate space `ℝⁿ`, with its Borel sigma algebra. -/
theorem finiteDimensional_substitution {μ : Measure S} {n : ℕ}
    {F : S → (Fin n → ℝ) → ℝ} (hF : Caratheodory μ F)
    {y : S → (Fin n → ℝ)} (hy : AEMeasurable y μ) :
    AEMeasurable (fun x => F x (y x)) μ :=
  hF.aemeasurable_substitution hy

/-- The source's `ℝᵐ` state and `ℝ^(dᵢ)` independent mixed-exponent fibers.
All dimensions and the number of fibers vary; no common exponent is required. -/
theorem mixed_finiteDimensional_lp_substitution {μ : Measure S} {m k : ℕ}
    {d : Fin k → ℕ} {q : ℝ≥0∞} {r : Fin k → ℝ≥0∞}
    {F : S → (Fin m → ℝ) → (∀ i, Fin (d i) → ℝ) → ℝ}
    (hF : MixedCaratheodory μ F) (s : Lp (Fin m → ℝ) q μ)
    (z : ∀ i, Lp (Fin (d i) → ℝ) (r i) μ) :
    AEMeasurable (fun x => F x (s x) (fun i => z i x)) μ :=
  hF.aemeasurable_lp_substitution s z

end VariationalNotes.Sobolev
