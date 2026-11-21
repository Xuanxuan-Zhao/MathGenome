import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.DelayModel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.OdeIntegral
import Mathlib.Topology.Piecewise
import Mathlib.Tactic.Linarith

noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace ExpandedFA.PartV
open OdeIntegralSpec DelayModelSpec

section Regularity
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
local instance delayModelRegularityRealNormedSpace : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ 𝕜 E
variable [CompleteSpace E] {τ T : ℝ} (hτ : 0 < τ) (hT : 0 ≤ T)

@[simp] theorem delay_extend_at (u : C(SolutionInterval τ T, E))
    (t : SolutionInterval τ T) : solutionExtension hτ hT u (t : ℝ) = u t :=
  ode_extend_at _ u t

theorem continuous_delay_field (A B : C(VolterraInterval 0 T, E →L[𝕜] E))
    (u : C(SolutionInterval τ T, E)) : Continuous (field hτ hT A B u) := by
  have hc : Continuous (solutionExtension hτ hT u) := continuous_ode_extend _ u
  exact ((continuous_ode_extend hT A).clm_apply hc).add
    ((continuous_ode_extend hT B).clm_apply (hc.comp (continuous_id.sub continuous_const)))

theorem delay_solution_derivative (η : C(HistoryInterval τ, E))
    (A B : C(VolterraInterval 0 T, E →L[𝕜] E))
    (u : C(SolutionInterval τ T, E)) (hu : IsSolution hτ hT η A B u)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (solutionExtension hτ hT u) (field hτ hT A B u t)
      (Icc 0 T) t := by
  have hc := continuous_delay_field hτ hT A B u
  have hp := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 t) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hd := (hp.const_add (η ⟨0, neg_nonpos.mpr hτ.le, le_rfl⟩)).hasDerivWithinAt
    (s := Icc 0 T)
  apply hd.congr
  · intro r hr
    simpa only [delay_extend_at hτ hT u
      ⟨r, (neg_nonpos.mpr hτ.le).trans hr.1, hr.2⟩] using hu.2 ⟨r, hr⟩
  · simpa only [delay_extend_at hτ hT u
      ⟨t, (neg_nonpos.mpr hτ.le).trans ht.1, ht.2⟩] using hu.2 ⟨t, ht⟩

theorem delay_rhs_at_zero (η : C(HistoryInterval τ, E))
    (A B : C(VolterraInterval 0 T, E →L[𝕜] E))
    (u : C(SolutionInterval τ T, E)) (hu : IsSolution hτ hT η A B u) :
    field hτ hT A B u 0 =
      A ⟨0, le_rfl, hT⟩ (η ⟨0, neg_nonpos.mpr hτ.le, le_rfl⟩) +
      B ⟨0, le_rfl, hT⟩ (η ⟨-τ, le_rfl, neg_nonpos.mpr hτ.le⟩) := by
  have hz := hu.1 ⟨0, neg_nonpos.mpr hτ.le, le_rfl⟩
  have hn := hu.1 ⟨-τ, le_rfl, neg_nonpos.mpr hτ.le⟩
  simp only [field, zero_sub, ode_extend_at hT A ⟨0, le_rfl, hT⟩,
    ode_extend_at hT B ⟨0, le_rfl, hT⟩,
    delay_extend_at hτ hT u ⟨0, neg_nonpos.mpr hτ.le, hT⟩,
    delay_extend_at hτ hT u ⟨-τ, le_rfl, (neg_nonpos.mpr hτ.le).trans hT⟩,
    hz, hn]

end Regularity

theorem delay_regularity : DelayModelSpec.Regularity := by
  intro 𝕜 E _ _ _ _ τ T hτ hT η A B u hu
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hd := delay_solution_derivative hτ hT η A B u hu
  have hc := continuous_delay_field hτ hT A B u
  have hi (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt (solutionExtension hτ hT u) (field hτ hT A B u t) t :=
    (hd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  refine ⟨hc, hd, hi, ?_⟩
  apply (contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn).mpr
  refine ⟨fun t ht => (hi t ht).differentiableAt.differentiableWithinAt, ?_⟩
  apply hc.continuousOn.congr
  intro t ht
  exact ((hi t ht).hasDerivWithinAt.derivWithin (isOpen_Ioo.uniqueDiffOn t ht))

theorem delay_initial_compatibility : DelayModelSpec.InitialCompatibility := by
  intro 𝕜 E _ _ _ _ τ T hτ hT η A B u hu
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro d hη
  have hd := delay_solution_derivative hτ hT.le η A B u hu 0 ⟨le_rfl, hT.le⟩
  have hz := delay_rhs_at_zero hτ hT.le η A B u hu
  rw [← hz]
  constructor
  · intro h
    exact (uniqueDiffOn_Icc hT 0 ⟨le_rfl, hT.le⟩).eq_deriv _ h.hasDerivWithinAt hd
  · intro he
    rw [he]
    have hl : HasDerivWithinAt (solutionExtension hτ hT.le u) d (Icc (-τ) 0) 0 := by
      apply hη.congr
      · intro r hr
        rw [delay_extend_at hτ hT.le u ⟨r, hr.1, hr.2.trans hT.le⟩,
          ode_extend_at (neg_nonpos.mpr hτ.le) η ⟨r, hr⟩]
        exact hu.1 ⟨r, hr⟩
      · rw [delay_extend_at hτ hT.le u ⟨0, neg_nonpos.mpr hτ.le, hT.le⟩,
          ode_extend_at (neg_nonpos.mpr hτ.le) η ⟨0, neg_nonpos.mpr hτ.le, le_rfl⟩]
        exact hu.1 ⟨0, neg_nonpos.mpr hτ.le, le_rfl⟩
    rw [he] at hl
    have hder := hl.union hd
    apply hder.hasDerivAt
    have heq : Icc (-τ) 0 ∪ Icc 0 T = Icc (-τ) T :=
      Icc_union_Icc_eq_Icc (neg_nonpos.mpr hτ.le) hT.le
    rw [heq]
    exact Icc_mem_nhds (neg_neg_of_pos hτ) hT

section Jets
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma productJet_congr (n : ℕ) (A : ℕ → E →L[𝕜] E) (U V : ℕ → E)
    (h : ∀ k ≤ n, U k = V k) : productJet n A U = productJet n A V := by
  induction n generalizing A U V with
  | zero => simp only [productJet, h 0 (by omega)]
  | succ n ih =>
    rw [productJet, productJet,
      ih _ U V (fun k hk => h k (by omega)),
      ih A (fun k => U (k + 1)) (fun k => V (k + 1)) (fun k hk => h (k + 1) (by omega))]

@[simp] lemma productJet_zero (n : ℕ) (A : ℕ → E →L[𝕜] E) :
    productJet n A (fun _ => 0) = 0 := by
  induction n generalizing A with
  | zero => simp [productJet]
  | succ n ih => simp only [productJet, ih, add_zero]

lemma productJet_sub (n : ℕ) (A : ℕ → E →L[𝕜] E) (U V : ℕ → E) :
    productJet n A (fun k => U k - V k) = productJet n A U - productJet n A V := by
  induction n generalizing A U V with
  | zero => simp [productJet]
  | succ n ih =>
    simp only [productJet, ih]
    abel

lemma productJet_first_nonzero (n : ℕ) (A : ℕ → E →L[𝕜] E) (U : ℕ → E)
    (h : ∀ k < n, U k = 0) : productJet n A U = A 0 (U n) := by
  induction n generalizing A U with
  | zero => rfl
  | succ n ih =>
    have hz : productJet n (fun k => A (k + 1)) U = 0 := by
      rw [productJet_congr n _ U (fun _ => 0) (fun k hk => h k (by omega))]
      exact productJet_zero _ _
    rw [productJet, hz, zero_add, ih A (fun k => U (k + 1))]
    intro k hk
    exact h (k + 1) (by omega)

lemma productJet_restrictScalars (n : ℕ) (A : ℕ → E →L[𝕜] E) (U : ℕ → E) :
    letI := NormedSpace.restrictScalars ℝ 𝕜 E
    productJet n (fun k => (A k).restrictScalars ℝ) U = productJet n A U := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  induction n generalizing A U with
  | zero => rfl
  | succ n ih => simp only [productJet, ih]

end Jets

section RealJets
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma productJet_hasDerivWithinAt (n : ℕ)
    (A : ℕ → ℝ → E →L[ℝ] E) (U : ℕ → ℝ → E) (s : Set ℝ) (t : ℝ)
    (hA : ∀ k ≤ n, HasDerivWithinAt (A k) (A (k + 1) t) s t)
    (hU : ∀ k ≤ n, HasDerivWithinAt (U k) (U (k + 1) t) s t) :
    HasDerivWithinAt (fun r => productJet n (fun k => A k r) (fun k => U k r))
      (productJet (n + 1) (fun k => A k t) (fun k => U k t)) s t := by
  induction n generalizing A U with
  | zero =>
    simpa only [productJet] using (hA 0 (by omega)).clm_apply (hU 0 (by omega))
  | succ n ih =>
    have h1 := ih (fun k => A (k + 1)) U
      (fun k hk => hA (k + 1) (by omega)) (fun k hk => hU k (by omega))
    have h2 := ih A (fun k => U (k + 1))
      (fun k hk => hA k (by omega)) (fun k hk => hU (k + 1) (by omega))
    exact h1.add h2

end RealJets

theorem delay_jet_differentiation : DelayModelSpec.JetDifferentiation := by
  intro 𝕜 E _ _ _ n A B U V s
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro hA hB hU hV t ht
  have h1 := productJet_hasDerivWithinAt n (fun k r => (A k r).restrictScalars ℝ)
    U s t (fun k hk => hA k (by omega) t ht) (fun k hk => hU k (by omega) t ht)
  have h2 := productJet_hasDerivWithinAt n (fun k r => (B k r).restrictScalars ℝ)
    V s t (fun k hk => hB k (by omega) t ht) (fun k hk => hV k (by omega) t ht)
  convert h1.add h2 using 1 <;>
    simp only [equationJet, productJet_restrictScalars] <;> rfl

theorem delay_jump_propagation : DelayModelSpec.JumpPropagation := by
  intro 𝕜 E _ _ _ n A B UL UR VL VR hU hV
  rw [equationJet, equationJet, productJet_congr n A UR UL hU]
  have h := productJet_first_nonzero n B (fun k => VR k - VL k)
    (fun k hk => sub_eq_zero.mpr (hV k hk))
  rw [productJet_sub] at h
  rw [← h]
  abel

namespace DelayConstruction
section
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
local instance delayModelConstructionRealNormedSpace : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ 𝕜 E
variable [CompleteSpace E]

def globalField (τ : ℝ) (A B : C(ℝ, E →L[𝕜] E)) (u : C(ℝ, E)) : C(ℝ, E) :=
  ⟨fun t => A t (u t) + B t (u (t - τ)),
    (A.continuous.clm_apply u.continuous).add
      (B.continuous.clm_apply (u.continuous.comp (continuous_id.sub continuous_const)))⟩

def Solves (τ b : ℝ) (η : C(ℝ, E)) (A B : C(ℝ, E →L[𝕜] E))
    (u : C(ℝ, E)) : Prop :=
  (∀ t ∈ Icc (-τ) 0, u t = η t) ∧
  ∀ t ∈ Icc 0 b, u t = η 0 + ∫ s in 0..t, globalField τ A B u s

lemma restriction_eq (a b : ℝ) (hab : a ≤ b) (u : C(ℝ, E)) (t : ℝ)
    (ht : t ∈ Icc a b) :
    extendCurve hab (u.comp ⟨Subtype.val, continuous_subtype_val⟩) t = u t := by
  simp [extendCurve, projIcc_of_mem hab ht]

lemma ode_step (a b : ℝ) (hab : a ≤ b) (A : C(ℝ, E →L[𝕜] E))
    (f : C(ℝ, E)) (ξ : E) :
    ∃ z : C(ℝ, E), z a = ξ ∧
      ∀ t ∈ Icc a b, z t = ξ + ∫ s in a..t, A s (z s) + f s := by
  let Ar : C(VolterraInterval a b, E →L[𝕜] E) :=
    A.comp ⟨Subtype.val, continuous_subtype_val⟩
  let fr : C(VolterraInterval a b, E) := f.comp ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨v, hv, hc, _, _⟩ := ode_unique_solvability 𝕜 E a b hab Ar fr ξ
  let z : C(ℝ, E) := ⟨extendCurve hab v, continuous_ode_extend hab v⟩
  refine ⟨z, ?_, ?_⟩
  · simpa only [z, ContinuousMap.coe_mk, ode_extend_at hab v ⟨a, le_rfl, hab⟩] using hc.2.1
  · intro t ht
    have hi : (∫ s in a..t, extendCurve hab (rhs Ar fr v) s) =
        ∫ s in a..t, A s (z s) + f s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      have hs' : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
      rw [ode_extend_at hab (rhs Ar fr v) ⟨s, hs'⟩]
      change A s (v ⟨s, hs'⟩) + f s = A s (extendCurve hab v s) + f s
      rw [ode_extend_at hab v ⟨s, hs'⟩]
    have hh := hv ⟨t, ht⟩
    rw [hi] at hh
    simpa only [z, ContinuousMap.coe_mk, ode_extend_at hab v ⟨t, ht⟩] using hh

lemma integral_congr_prefix (τ b : ℝ) (hτ : 0 < τ)
    (A B : C(ℝ, E →L[𝕜] E)) (u w : C(ℝ, E))
    (h : ∀ s ≤ b, w s = u s) (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ b) :
    (∫ s in 0..t, globalField τ A B w s) =
      ∫ s in 0..t, globalField τ A B u s := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht0] at hs
  change A s (w s) + B s (w (s - τ)) = A s (u s) + B s (u (s - τ))
  rw [h s (hs.2.trans ht), h (s - τ) (by linarith [hs.2])]

lemma extend_step {τ b : ℝ} (hτ : 0 < τ) (hb : 0 ≤ b)
    (η : C(ℝ, E)) (A B : C(ℝ, E →L[𝕜] E)) (u : C(ℝ, E))
    (hu : Solves τ b η A B u) : ∃ w : C(ℝ, E), Solves τ (b + τ) η A B w := by
  classical
  let f : C(ℝ, E) := ⟨fun s => B s (u (s - τ)),
    B.continuous.clm_apply (u.continuous.comp (continuous_id.sub continuous_const))⟩
  obtain ⟨z, hz0, hz⟩ := ode_step b (b + τ) (by linarith) A f (u b)
  let w : C(ℝ, E) := ⟨fun t => if t ≤ b then u t else z t, by
    apply u.continuous.if _ z.continuous
    intro t ht
    have ht' : t = b := frontier_Iic_subset b ht
    subst t
    exact hz0.symm⟩
  have hw (s : ℝ) (hs : s ≤ b) : w s = u s := if_pos hs
  have hwz (s : ℝ) (hs : b ≤ s) : w s = z s := by
    by_cases hs' : s ≤ b
    · have he : s = b := le_antisymm hs' hs
      subst s
      exact (hw b le_rfl).trans hz0.symm
    · exact if_neg hs'
  have hc := (globalField τ A B w).continuous
  refine ⟨w, ?_, ?_⟩
  · intro t ht
    rw [hw t (ht.2.trans hb)]
    exact hu.1 t ht
  · intro t ht
    by_cases htb : t ≤ b
    · rw [hw t htb, integral_congr_prefix τ b hτ A B u w hw t ht.1 htb]
      exact hu.2 t ⟨ht.1, htb⟩
    · have hbt : b ≤ t := (lt_of_not_ge htb).le
      have hi0 := integral_congr_prefix τ b hτ A B u w hw b hb le_rfl
      have hi1 : (∫ s in b..t, globalField τ A B w s) =
          ∫ s in b..t, A s (z s) + f s := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hbt] at hs
        change A s (w s) + B s (w (s - τ)) = A s (z s) + B s (u (s - τ))
        rw [hwz s hs.1, hw (s - τ) (by linarith [hs.2, ht.2])]
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable (μ := volume) 0 b) (hc.intervalIntegrable (μ := volume) b t)
      rw [← hsplit, hi0, hi1, hwz t hbt, hz t ⟨hbt, ht.2⟩, hu.2 b ⟨hb, le_rfl⟩]
      abel

lemma exists_steps {τ : ℝ} (hτ : 0 < τ) (η : C(ℝ, E))
    (A B : C(ℝ, E →L[𝕜] E)) (n : ℕ) :
    ∃ u : C(ℝ, E), Solves τ ((n : ℝ) * τ) η A B u := by
  induction n with
  | zero =>
    refine ⟨η, (fun _ _ => rfl), ?_⟩
    intro t ht
    have ht' : t = 0 := le_antisymm (by simpa using ht.2) ht.1
    subst t
    simp
  | succ n ih =>
    obtain ⟨u, hu⟩ := ih
    obtain ⟨w, hw⟩ := extend_step hτ (mul_nonneg (Nat.cast_nonneg n) hτ.le) η A B u hu
    refine ⟨w, ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hw

lemma ode_unique_global (a b : ℝ) (hab : a ≤ b) (A : C(ℝ, E →L[𝕜] E))
    (f : C(ℝ, E)) (ξ : E) (v w : C(ℝ, E))
    (hv : ∀ t ∈ Icc a b, v t = ξ + ∫ s in a..t, A s (v s) + f s)
    (hw : ∀ t ∈ Icc a b, w t = ξ + ∫ s in a..t, A s (w s) + f s) :
    ∀ t ∈ Icc a b, v t = w t := by
  let Ar : C(VolterraInterval a b, E →L[𝕜] E) :=
    A.comp ⟨Subtype.val, continuous_subtype_val⟩
  let fr : C(VolterraInterval a b, E) := f.comp ⟨Subtype.val, continuous_subtype_val⟩
  have hsol (z : C(ℝ, E))
      (hz : ∀ t ∈ Icc a b, z t = ξ + ∫ s in a..t, A s (z s) + f s) :
      IsIntegralSolution hab Ar fr ξ (z.comp ⟨Subtype.val, continuous_subtype_val⟩) := by
    intro t
    change z t = _
    rw [hz t t.property]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.property.1] at hs
    have hs' : s ∈ Icc a b := ⟨hs.1, hs.2.trans t.property.2⟩
    rw [ode_extend_at hab (rhs Ar fr _) ⟨s, hs'⟩]
    rfl
  obtain ⟨z, _, _, huniq, _⟩ := ode_unique_solvability 𝕜 E a b hab Ar fr ξ
  have heq : v.comp ⟨Subtype.val, continuous_subtype_val⟩ =
      w.comp ⟨Subtype.val, continuous_subtype_val⟩ :=
    (huniq _ (hsol v hv)).trans (huniq _ (hsol w hw)).symm
  intro t ht
  exact congrArg (fun q : C(VolterraInterval a b, E) => q ⟨t, ht⟩) heq

lemma subinterval_formula {τ b : ℝ} (η : C(ℝ, E))
    (A B : C(ℝ, E →L[𝕜] E)) (u : C(ℝ, E)) (hu : Solves τ b η A B u)
    (c t : ℝ) (hc : c ∈ Icc 0 b) (ht : t ∈ Icc 0 b) :
    u t = u c + ∫ s in c..t, globalField τ A B u s := by
  have hs := intervalIntegral.integral_add_adjacent_intervals
    ((globalField τ A B u).continuous.intervalIntegrable (μ := volume) 0 c)
    ((globalField τ A B u).continuous.intervalIntegrable (μ := volume) c t)
  rw [hu.2 t ht, hu.2 c hc, ← hs]
  abel

lemma unique_prefix {τ b : ℝ} (hτ : 0 < τ) (hb : 0 ≤ b)
    (η : C(ℝ, E)) (A B : C(ℝ, E →L[𝕜] E)) (v w : C(ℝ, E))
    (hv : Solves τ b η A B v) (hw : Solves τ b η A B w) (n : ℕ) :
    ∀ t ∈ Icc (-τ) (min b ((n : ℝ) * τ)), v t = w t := by
  induction n with
  | zero =>
    intro t ht
    have ht0 : t ≤ 0 := by simpa only [Nat.cast_zero, zero_mul, min_eq_right hb] using ht.2
    exact (hv.1 t ⟨ht.1, ht0⟩).trans (hw.1 t ⟨ht.1, ht0⟩).symm
  | succ n ih =>
    let c := min b ((n : ℝ) * τ)
    let d := min b (((n + 1 : ℕ) : ℝ) * τ)
    have hc0 : 0 ≤ c := le_min hb (mul_nonneg (Nat.cast_nonneg n) hτ.le)
    have hd0 : 0 ≤ d := le_min hb (mul_nonneg (Nat.cast_nonneg _) hτ.le)
    have hcb : c ≤ b := min_le_left _ _
    have hdb : d ≤ b := min_le_left _ _
    have hcd : c ≤ d := min_le_min_left b (by simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]; linarith)
    have hec : v c = w c := ih c ⟨(neg_nonpos.mpr hτ.le).trans hc0, le_rfl⟩
    have hdelay (s : ℝ) (hs : s ∈ Icc c d) : v (s - τ) = w (s - τ) := by
      apply ih (s - τ)
      refine ⟨by linarith [hs.1], le_min ?_ ?_⟩
      · linarith [hs.2.trans hdb]
      · have hn : s ≤ ((n + 1 : ℕ) : ℝ) * τ := hs.2.trans (min_le_right _ _)
        simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] at hn
        linarith
    let f : C(ℝ, E) := ⟨fun s => B s (v (s - τ)),
      B.continuous.clm_apply (v.continuous.comp (continuous_id.sub continuous_const))⟩
    have hvs (t : ℝ) (ht : t ∈ Icc c d) :
        v t = v c + ∫ s in c..t, A s (v s) + f s :=
      subinterval_formula η A B v hv c t ⟨hc0, hcb⟩ ⟨hc0.trans ht.1, ht.2.trans hdb⟩
    have hws (t : ℝ) (ht : t ∈ Icc c d) :
        w t = v c + ∫ s in c..t, A s (w s) + f s := by
      rw [hec, subinterval_formula η A B w hw c t ⟨hc0, hcb⟩
        ⟨hc0.trans ht.1, ht.2.trans hdb⟩]
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      change A s (w s) + B s (w (s - τ)) = A s (w s) + B s (v (s - τ))
      rw [hdelay s ⟨hs.1, hs.2.trans ht.2⟩]
    intro t ht
    by_cases htc : t ≤ c
    · exact ih t ⟨ht.1, htc⟩
    · exact ode_unique_global c d hcd A f (v c) v w hvs hws t
        ⟨(lt_of_not_ge htc).le, ht.2⟩

lemma unique_global {τ b : ℝ} (hτ : 0 < τ) (hb : 0 ≤ b)
    (η : C(ℝ, E)) (A B : C(ℝ, E →L[𝕜] E)) (v w : C(ℝ, E))
    (hv : Solves τ b η A B v) (hw : Solves τ b η A B w) :
    ∀ t ∈ Icc (-τ) b, v t = w t := by
  obtain ⟨n, hn⟩ := exists_nat_gt (b / τ)
  have hn' : b ≤ (n : ℝ) * τ := by
    exact ((div_lt_iff₀ hτ).mp hn).le
  simpa only [min_eq_left hn'] using unique_prefix hτ hb η A B v w hv hw n

lemma exists_global {τ T : ℝ} (hτ : 0 < τ) (hT : 0 ≤ T)
    (η : C(ℝ, E)) (A B : C(ℝ, E →L[𝕜] E)) :
    ∃ u : C(ℝ, E), Solves τ T η A B u := by
  obtain ⟨n, hn⟩ := exists_nat_gt (T / τ)
  have hn' : T ≤ (n : ℝ) * τ := ((div_lt_iff₀ hτ).mp hn).le
  obtain ⟨u, hu⟩ := exists_steps hτ η A B n
  exact ⟨u, hu.1, fun t ht => hu.2 t ⟨ht.1, ht.2.trans hn'⟩⟩

end
end DelayConstruction

section FiniteBridge
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
local instance delayModelFiniteBridgeRealNormedSpace : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ 𝕜 E
variable [CompleteSpace E] {τ T : ℝ} (hτ : 0 < τ) (hT : 0 ≤ T)

lemma delay_finite_global_bridge (η : C(HistoryInterval τ, E))
    (A B : C(VolterraInterval 0 T, E →L[𝕜] E)) (v : C(SolutionInterval τ T, E)) :
    IsSolution hτ hT η A B v ↔
      DelayConstruction.Solves τ T
        ⟨extendCurve (neg_nonpos.mpr hτ.le) η, continuous_ode_extend _ η⟩
        ⟨extendCurve hT A, continuous_ode_extend _ A⟩
        ⟨extendCurve hT B, continuous_ode_extend _ B⟩
        ⟨solutionExtension hτ hT v, continuous_ode_extend _ v⟩ := by
  have hh (s : ℝ) (hs : s ∈ Icc (-τ) 0) :
      solutionExtension hτ hT v s = v ⟨s, hs.1, hs.2.trans hT⟩ :=
    delay_extend_at hτ hT v ⟨s, hs.1, hs.2.trans hT⟩
  constructor
  · intro hv
    refine ⟨?_, ?_⟩
    · intro s hs
      change solutionExtension hτ hT v s = extendCurve (neg_nonpos.mpr hτ.le) η s
      rw [hh s hs, ode_extend_at _ η ⟨s, hs⟩]
      exact hv.1 ⟨s, hs⟩
    · intro s hs
      change solutionExtension hτ hT v s = extendCurve (neg_nonpos.mpr hτ.le) η 0 + _
      rw [delay_extend_at hτ hT v ⟨s, (neg_nonpos.mpr hτ.le).trans hs.1, hs.2⟩,
        ode_extend_at _ η ⟨0, neg_nonpos.mpr hτ.le, le_rfl⟩]
      exact hv.2 ⟨s, hs⟩
  · intro hv
    refine ⟨?_, ?_⟩
    · intro s
      have h := hv.1 s s.property
      change solutionExtension hτ hT v s = extendCurve (neg_nonpos.mpr hτ.le) η s at h
      simpa only [hh s s.property, ode_extend_at _ η s] using h
    · intro s
      have h := hv.2 s s.property
      change solutionExtension hτ hT v s = extendCurve (neg_nonpos.mpr hτ.le) η 0 + _ at h
      rw [delay_extend_at hτ hT v
        ⟨s, (neg_nonpos.mpr hτ.le).trans s.property.1, s.property.2⟩,
        ode_extend_at _ η ⟨0, neg_nonpos.mpr hτ.le, le_rfl⟩] at h
      exact h

lemma delay_restrict_global_solution (η : C(HistoryInterval τ, E))
    (A B : C(VolterraInterval 0 T, E →L[𝕜] E)) (v : C(ℝ, E))
    (hv : DelayConstruction.Solves τ T
      ⟨extendCurve (neg_nonpos.mpr hτ.le) η, continuous_ode_extend _ η⟩
      ⟨extendCurve hT A, continuous_ode_extend _ A⟩
      ⟨extendCurve hT B, continuous_ode_extend _ B⟩ v) :
    IsSolution hτ hT η A B (v.comp ⟨Subtype.val, continuous_subtype_val⟩) := by
  let u : C(SolutionInterval τ T, E) := v.comp ⟨Subtype.val, continuous_subtype_val⟩
  have hu (s : ℝ) (hs : s ∈ SolutionInterval τ T) : solutionExtension hτ hT u s = v s :=
    DelayConstruction.restriction_eq (-τ) T _ v s hs
  refine ⟨?_, ?_⟩
  · intro t
    have h := hv.1 t t.property
    simpa only [ContinuousMap.coe_mk, ode_extend_at _ η t,
      ContinuousMap.comp_apply] using h
  · intro t
    have h := hv.2 t t.property
    change v t = extendCurve (neg_nonpos.mpr hτ.le) η 0 + _ at h
    rw [ode_extend_at _ η ⟨0, neg_nonpos.mpr hτ.le, le_rfl⟩] at h
    change v t = _
    rw [h]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.property.1] at hs
    change extendCurve hT A s (v s) + extendCurve hT B s (v (s - τ)) =
      extendCurve hT A s (solutionExtension hτ hT u s) +
        extendCurve hT B s (solutionExtension hτ hT u (s - τ))
    rw [hu s ⟨by linarith [hs.1], hs.2.trans t.property.2⟩,
      hu (s - τ) ⟨by linarith [hs.1], by linarith [hs.2, t.property.2]⟩]

end FiniteBridge

theorem delay_unique_solvability : DelayModelSpec.UniqueSolvability := by
  intro 𝕜 E _ _ _ _ τ T hτ hT η A B
  let ηg : C(ℝ, E) := ⟨extendCurve (neg_nonpos.mpr hτ.le) η, continuous_ode_extend _ η⟩
  let Ag : C(ℝ, E →L[𝕜] E) := ⟨extendCurve hT A, continuous_ode_extend _ A⟩
  let Bg : C(ℝ, E →L[𝕜] E) := ⟨extendCurve hT B, continuous_ode_extend _ B⟩
  obtain ⟨v, hv⟩ := DelayConstruction.exists_global hτ hT ηg Ag Bg
  let u : C(SolutionInterval τ T, E) := v.comp ⟨Subtype.val, continuous_subtype_val⟩
  have hu : IsSolution hτ hT η A B u := delay_restrict_global_solution hτ hT η A B v hv
  refine ⟨u, hu, ?_⟩
  intro w hw
  have hwu := DelayConstruction.unique_global hτ hT ηg Ag Bg
    ⟨solutionExtension hτ hT w, continuous_ode_extend _ w⟩
    ⟨solutionExtension hτ hT u, continuous_ode_extend _ u⟩
    ((delay_finite_global_bridge hτ hT η A B w).mp hw)
    ((delay_finite_global_bridge hτ hT η A B u).mp hu)
  ext t
  have h := hwu t t.property
  change solutionExtension hτ hT w t = solutionExtension hτ hT u t at h
  simpa only [delay_extend_at] using h

lemma derivativeTower_mono {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m n : ℕ} {U : ℕ → ℝ → F} {s : Set ℝ}
    (h : IsDerivativeTower n U s) (hmn : m ≤ n) : IsDerivativeTower m U s :=
  fun k hk t ht => h k (lt_of_lt_of_le hk hmn) t ht

section JetRecurrence
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma equationJet_recurrence :
    letI := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ (n : ℕ) (s : Set ℝ), UniqueDiffOn ℝ s →
    ∀ (A B : ℕ → ℝ → E →L[𝕜] E) (U V : ℕ → ℝ → E),
    IsDerivativeTower n (fun k t => (A k t).restrictScalars ℝ) s →
    IsDerivativeTower n (fun k t => (B k t).restrictScalars ℝ) s →
    IsDerivativeTower (n + 1) U s → IsDerivativeTower n V s →
    (∀ t ∈ s, U 1 t = equationJet 0
      (fun k => A k t) (fun k => B k t) (fun k => U k t) (fun k => V k t)) →
    ∀ k ≤ n, ∀ t ∈ s, U (k + 1) t = equationJet k
      (fun j => A j t) (fun j => B j t) (fun j => U j t) (fun j => V j t) := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro n s hs A B U V hA hB hU hV hbase k hk
  induction k with
  | zero => exact hbase
  | succ k ih =>
    have ih' := ih (by omega)
    intro t ht
    have hd := delay_jet_differentiation 𝕜 E k A B U V s
      (derivativeTower_mono hA (by omega)) (derivativeTower_mono hB (by omega))
      (derivativeTower_mono hU (by omega)) (derivativeTower_mono hV (by omega)) t ht
    have hu := hU (k + 1) (by omega) t ht
    have hu' : HasDerivWithinAt
        (fun r => equationJet k (fun j => A j r) (fun j => B j r)
          (fun j => U j r) (fun j => V j r)) (U (k + 1 + 1) t) s t := by
      apply hu.congr
      · intro r hr
        exact (ih' r hr).symm
      · exact (ih' t ht).symm
    exact (hs t ht).eq_deriv _ hu' hd

end JetRecurrence

theorem delay_solution_jets : DelayModelSpec.SolutionJets := by
  intro 𝕜 E _ _ _ _ τ T hτ hT η A B u hu
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro n s hsub huniq AJ BJ U V hA0 hB0 hU0 hV0 hA hB hU hV
  apply equationJet_recurrence n s huniq AJ BJ U V hA hB hU hV
  intro t ht
  have hd := (delay_solution_derivative hτ hT η A B u hu t (hsub ht)).mono hsub
  have htower := hU 0 (by omega) t ht
  have hx : HasDerivWithinAt (solutionExtension hτ hT u) (U 1 t) s t := by
    apply htower.congr
    · intro r hr
      exact (hU0 r hr).symm
    · exact (hU0 t ht).symm
  have he := (huniq t ht).eq_deriv _ hx hd
  rw [he]
  simp only [equationJet, productJet, hA0 t ht, hB0 t ht, hU0 t ht, hV0 t ht]
  rfl

theorem delay_scalar_unique_solvability : DelayModelSpec.ScalarUniqueSolvability := by
  intro 𝕜 E _ _ _ _ τ T hτ hT η a b
  exact delay_unique_solvability 𝕜 E τ T hτ hT η (scalarCoefficient a) (scalarCoefficient b)

theorem delay_failure_example : DelayModelSpec.FailureExample := by
  let η : C(HistoryInterval 1, ℝ) := ContinuousMap.const _ 1
  let A : C(VolterraInterval 0 2, ℝ →L[ℝ] ℝ) := ContinuousMap.const _ 0
  let B : C(VolterraInterval 0 2, ℝ →L[ℝ] ℝ) :=
    ContinuousMap.const _ (ContinuousLinearMap.id ℝ ℝ)
  obtain ⟨u, hu, _⟩ := delay_unique_solvability ℝ ℝ 1 2 zero_lt_one zero_le_two η A B
  refine ⟨u, hu, ?_⟩
  let x := solutionExtension zero_lt_one zero_le_two u
  change (∀ t ∈ Icc 0 1, x t = 1 + t) ∧
    HasDerivWithinAt (deriv x) 0 (Icc (1 / 2) 1) 1 ∧
    HasDerivWithinAt (deriv x) 1 (Icc 1 (3 / 2)) 1 ∧
    ¬DifferentiableAt ℝ (deriv x) 1
  have hhist (t : ℝ) (ht : t ∈ Icc (-1) 0) : x t = 1 := by
    change solutionExtension zero_lt_one zero_le_two u t = 1
    rw [delay_extend_at zero_lt_one zero_le_two u ⟨t, ht.1, ht.2.trans zero_le_two⟩]
    exact hu.1 ⟨t, ht⟩
  have hfield (t : ℝ) : field zero_lt_one zero_le_two A B u t = x (t - 1) := by
    simp [field, A, B, extendCurve, x]
  have hfield1 (t : ℝ) (ht : t ∈ Icc 0 1) :
      field zero_lt_one zero_le_two A B u t = 1 := by
    rw [hfield]
    exact hhist (t - 1) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hfirst (t : ℝ) (ht : t ∈ Icc 0 1) : x t = 1 + t := by
    have ht2 : t ∈ Icc 0 2 := ⟨ht.1, by linarith [ht.2]⟩
    have h := hu.2 ⟨t, ht2⟩
    have hi : (∫ s in 0..t, field zero_lt_one zero_le_two A B u s) = t := by
      calc
        _ = ∫ _s in 0..t, (1 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [uIcc_of_le ht.1] at hs
          exact hfield1 s ⟨hs.1, hs.2.trans ht.2⟩
        _ = t := by simp
    change u ⟨t, by linarith [ht.1], ht2.2⟩ = 1 + _ at h
    rw [hi] at h
    change solutionExtension zero_lt_one zero_le_two u t = _
    rw [delay_extend_at zero_lt_one zero_le_two u ⟨t, by linarith [ht.1], ht2.2⟩]
    exact h
  have hd (t : ℝ) (ht : t ∈ Ioo 0 2) : deriv x t = x (t - 1) := by
    have h := (delay_regularity ℝ ℝ 1 2 zero_lt_one zero_le_two η A B u hu).2.2.1 t ht
    exact h.deriv.trans (hfield t)
  have hleft (t : ℝ) (ht : t ∈ Icc (1 / 2) 1) : deriv x t = 1 := by
    rw [hd t ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    exact hhist (t - 1) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hright (t : ℝ) (ht : t ∈ Icc 1 (3 / 2)) : deriv x t = t := by
    rw [hd t ⟨by linarith [ht.1], by linarith [ht.2]⟩,
      hfirst (t - 1) ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    ring
  have hl : HasDerivWithinAt (deriv x) 0 (Icc (1 / 2) 1) 1 := by
    apply (hasDerivWithinAt_const 1 (Icc (1 / 2) 1) (1 : ℝ)).congr
    · exact hleft
    · exact hleft 1 ⟨by norm_num, le_rfl⟩
  have hr : HasDerivWithinAt (deriv x) 1 (Icc 1 (3 / 2)) 1 := by
    apply (hasDerivWithinAt_id 1 (Icc 1 (3 / 2))).congr
    · exact hright
    · exact hright 1 ⟨le_rfl, by norm_num⟩
  refine ⟨hfirst, hl, hr, ?_⟩
  intro h
  have hl' := (uniqueDiffOn_Icc (show (1 / 2 : ℝ) < 1 by norm_num) 1
    ⟨by norm_num, le_rfl⟩).eq_deriv _ h.hasDerivAt.hasDerivWithinAt hl
  have hr' := (uniqueDiffOn_Icc (show (1 : ℝ) < 3 / 2 by norm_num) 1
    ⟨le_rfl, by norm_num⟩).eq_deriv _ h.hasDerivAt.hasDerivWithinAt hr
  linarith

theorem delay_smooth_step : DelayModelSpec.SmoothStep := by
  intro 𝕜 E _ _ _ _ τ T hτ hT η A B u hu
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro n s hsub huniq
  have hd (t : ℝ) (ht : t ∈ s) :=
    (delay_solution_derivative hτ hT η A B u hu t (hsub ht)).mono hsub
  have hdiff : DifferentiableOn ℝ (solutionExtension hτ hT u) s :=
    fun t ht => (hd t ht).differentiableWithinAt
  have heq (t : ℝ) (ht : t ∈ s) :
      derivWithin (solutionExtension hτ hT u) s t = field hτ hT A B u t :=
    (hd t ht).derivWithin (huniq t ht)
  induction n with
  | zero =>
    intro _ _ _
    apply (contDiffOn_one_iff_derivWithin huniq).mpr
    refine ⟨hdiff, ?_⟩
    exact (continuous_delay_field hτ hT A B u).continuousOn.congr heq
  | succ n ih =>
    intro hA hB hV
    have hle : (n : ℕ∞ω) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
    have hx := ih (hA.of_le hle) (hB.of_le hle) (hV.of_le hle)
    have hrhs := (hA.clm_apply hx).add (hB.clm_apply hV)
    apply (contDiffOn_succ_iff_derivWithin huniq).mpr
    refine ⟨hdiff, by simp, ?_⟩
    apply hrhs.congr
    intro t ht
    exact heq t ht

end ExpandedFA.PartV
