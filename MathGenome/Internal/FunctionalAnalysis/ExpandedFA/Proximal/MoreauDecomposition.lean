import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.MoreauDecomposition
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Proximal.VariationalFirmness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.SubgradientBasicCalculus

/-! Moreau's primal–dual identity (paper.tex:8523–8572).
The input is any proper convex norm-lower-semicontinuous function on a real
Hilbert space. The conjugate is the actual supremum, transported faithfully
from EReal to WithTop ℝ. All arithmetic in the energy calculation is performed
at proved finite real values. -/
noncomputable section
open scoped InnerProductSpace
namespace ExpandedFA.Proximal
open P1.ExtendedConvexFunctions
open P1.C06Conjugates
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def conjugateFunction : MoreauSpec.ConjugateFunctionType.{u} :=
  MoreauSpec.ConjugateFunctionValue

theorem conjugateFunction_identification : MoreauSpec.ConjugateIdentification.{u} := by
  intro H _ _ _ φ hp w
  have hn := hilbertConjugate_ne_bot H φ hp w
  change WithBot.some ((hilbertConjugate H φ w).unbotD ⊤) = hilbertConjugate H φ w
  change (hilbertConjugate H φ w : WithBot (WithTop ℝ)) ≠ ⊥ at hn
  obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp hn
  rw [← hx]
  rfl

lemma conjugateFunction_coe [CompleteSpace H] (φ : ExtendedFunction H)
    (hp : Proper H φ) (w : H) :
    extendedRealValue (conjugateFunction H φ w) =
      convexConjugate H φ (InnerProductSpace.toDual ℝ H w) :=
  (conjugateFunction_identification H φ hp w).trans
    (hilbertConjugate_eq_banachConjugate H φ w)

lemma conjugateFunction_le_real_iff [CompleteSpace H] (φ : ExtendedFunction H)
    (hp : Proper H φ) (w : H) (r : ℝ) :
    conjugateFunction H φ w ≤ (r : WithTop ℝ) ↔
      ∀ (v : H) (s : ℝ), φ v = (s : WithTop ℝ) → ⟪w, v⟫_ℝ - s ≤ r := by
  have hh := P1.C06FenchelMoreau.convexConjugate_le_real_iff φ
    (InnerProductSpace.toDual ℝ H w) r
  rw [← conjugateFunction_coe φ hp w] at hh
  exact (WithBot.coe_le_coe (α := WithTop ℝ)).symm.trans hh

theorem conjugateFunction_regular : MoreauSpec.ConjugateRegularity.{u} := by
  intro H _ _ _ φ hp hc hl
  change Proper H (conjugateFunction H φ) ∧ ExtendedConvex H (conjugateFunction H φ) ∧
    LowerSemicontinuous H (conjugateFunction H φ)
  have hi := conjugateFunction_coe φ hp
  have hproper := P1.C06FenchelMoreau.convexConjugate_proper H φ hp hc hl
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨f, r, hr⟩ := hproper.2
    obtain ⟨w, hw⟩ := (InnerProductSpace.toDual ℝ H).surjective f
    have he : conjugateFunction H φ w = (r : WithTop ℝ) := by
      apply WithBot.coe_injective
      change extendedRealValue (conjugateFunction H φ w) = (r : EReal)
      rw [hi w, hw]
      exact hr
    exact ⟨w, by change conjugateFunction H φ w ≠ ⊤; rw [he]; exact WithTop.coe_ne_top⟩
  · intro w z r s a b hw hz ha hb hab
    apply (conjugateFunction_le_real_iff φ hp _ _).mpr
    intro v t ht
    have hwr := (conjugateFunction_le_real_iff φ hp w r).mp hw.le v t ht
    have hzs := (conjugateFunction_le_real_iff φ hp z s).mp hz.le v t ht
    simp only [inner_add_left, real_inner_smul_left]
    nlinarith [mul_le_mul_of_nonneg_left hwr ha, mul_le_mul_of_nonneg_left hzs hb,
      congrArg (fun x : ℝ => x * t) hab]
  · intro r
    have he : {w : H | conjugateFunction H φ w ≤ (r : WithTop ℝ)} =
        ⋂ (v : H) (s : ℝ) (_ : φ v = (s : WithTop ℝ)),
          {w | ⟪w, v⟫_ℝ - s ≤ r} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, conjugateFunction_le_real_iff φ hp]
    rw [he]
    exact isClosed_iInter fun v => isClosed_iInter fun s => isClosed_iInter fun _ =>
      isClosed_le ((continuous_id.inner continuous_const).sub continuous_const) continuous_const

/-- A supporting vector attains the actual conjugate, and the same equality
supplies the reverse supporting inequality on the conjugate. -/
lemma conjugate_subgradient [CompleteSpace H] (φ : ExtendedFunction H)
    (hp : Proper H φ) (u w : H) (hw : w ∈ hilbertSubdifferential H φ u) :
    ∃ r s : ℝ, φ u = (r : WithTop ℝ) ∧
      hilbertConjugate H φ w = (s : EReal) ∧
      conjugateFunction H φ w = (s : WithTop ℝ) ∧
      r + s = ⟪u, w⟫_ℝ ∧
      u ∈ hilbertSubdifferential H (conjugateFunction H φ) w := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hw.1
  have hb : (InnerProductSpace.toDual ℝ H w) ∈ BanachConvex.subdifferential H φ u := hw
  have he := (BanachConvex.mem_subdifferential_iff_conjugate φ u r hr.symm
    (InnerProductSpace.toDual ℝ H w)).mp hb
  let s : ℝ := ⟪w, u⟫_ℝ - r
  have hs : hilbertConjugate H φ w = (s : EReal) := he
  have hs' : conjugateFunction H φ w = (s : WithTop ℝ) := by
    apply WithBot.coe_injective
    change extendedRealValue (conjugateFunction H φ w) = (s : EReal)
    rw [conjugateFunction_coe φ hp w]
    exact he
  refine ⟨r, s, hr.symm, hs, hs', ?_, ?_⟩
  · dsimp [s]
    rw [real_inner_comm w u]
    ring
  · change conjugateFunction H φ w ≠ ⊤ ∧
      ∀ z, conjugateFunction H φ w + (⟪u, z - w⟫_ℝ : WithTop ℝ) ≤ conjugateFunction H φ z
    refine ⟨by rw [hs']; exact WithTop.coe_ne_top, ?_⟩
    intro z
    by_cases hz : conjugateFunction H φ z = ⊤
    · rw [hz]; exact le_top
    · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hz
      have ht' : hilbertConjugate H φ z = (t : EReal) := by
        have hi := conjugateFunction_identification H φ hp z
        change extendedRealValue (conjugateFunction H φ z) = hilbertConjugate H φ z at hi
        rw [← ht] at hi
        exact hi.symm
      have hbound := (hilbertConjugate_isLUB H φ z).1 ⟨u, rfl⟩
      change (⟪z, u⟫_ℝ : EReal) - extendedRealValue (φ u) ≤ hilbertConjugate H φ z at hbound
      rw [← hr, ht'] at hbound
      change (⟪z, u⟫_ℝ : EReal) - (r : EReal) ≤ (t : EReal) at hbound
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at hbound
      rw [hs', ← ht, ← WithTop.coe_add]
      apply WithTop.coe_le_coe.mpr
      dsimp [s]
      rw [inner_sub_right]
      nlinarith [real_inner_comm u z, real_inner_comm u w]

private lemma envelope_at_finite_minimizer (φ : ExtendedFunction H) (μ : ℝ)
    (f u : H) (r : ℝ) (hr : φ u = (r : WithTop ℝ))
    (hu : IsProximalMinimizer H φ μ f u) :
    moreauEnvelope H φ μ f = ((r + ‖f - u‖ ^ 2 / (2 * μ) : ℝ) : EReal) := by
  have he := moreauEnvelope_eq_objective H φ μ f u hu
  change moreauEnvelope H φ μ f = extendedRealValue (proximalObjective H φ μ f u) at he
  rw [he]
  change extendedRealValue (φ u + ((‖f - u‖ ^ 2 / (2 * μ) : ℝ) : WithTop ℝ)) = _
  rw [hr, ← WithTop.coe_add]
  rfl

private lemma energy_algebra (μ : ℝ) (hμ : 0 < μ) (f u w : H) (r s : ℝ)
    (hf : u + μ • w = f) (hrs : r + s = ⟪u, w⟫_ℝ) :
    (r + ‖f - u‖ ^ 2 / (2 * μ)) +
      (s + ‖μ⁻¹ • f - w‖ ^ 2 / (2 * μ⁻¹)) = ‖f‖ ^ 2 / (2 * μ) := by
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  have hfu : f - u = μ • w := by rw [← hf]; abel
  have hfw : μ⁻¹ • f - w = μ⁻¹ • u := by
    rw [← hf, smul_add, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    abel
  have hnorm : ‖f‖ ^ 2 = ‖u‖ ^ 2 + 2 * μ * ⟪u, w⟫_ℝ + μ ^ 2 * ‖w‖ ^ 2 := by
    rw [← hf, norm_add_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [hfu, hfw, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, mul_pow, sq_abs, sq_abs]
  rw [hnorm]
  have hsum : s = ⟪u, w⟫_ℝ - r := by linarith
  rw [hsum]
  field_simp
  ring

theorem moreau_decomposition : MoreauSpec.Decomposition.{u} := by
  intro H _ _ _ φ hp hc hl μ hμ f
  let u := proximalMap H φ μ f
  let w := μ⁻¹ • (f - u)
  have hu : IsProximalMinimizer H φ μ f u := proximalMap_minimizes H φ hp hc hl μ hμ f
  have hw : w ∈ hilbertSubdifferential H φ u :=
    (proximalMap_characterization H φ hp hc hl μ hμ f u).2.mp rfl
  obtain ⟨r, s, hr, hs, hs', hrs, hrev⟩ := conjugate_subgradient φ hp u w hw
  obtain ⟨hp', hc', hl'⟩ := conjugateFunction_regular H φ hp hc hl
  have hf : u + μ • w = f := by
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hμ), one_smul]
    abel
  have hscale : (μ⁻¹)⁻¹ • (μ⁻¹ • f - w) = u := by
    dsimp [w]
    rw [← smul_sub, sub_sub_cancel, smul_smul, inv_inv,
      mul_inv_cancel₀ (ne_of_gt hμ), one_smul]
  have hdual : proximalMap H (conjugateFunction H φ) μ⁻¹ (μ⁻¹ • f) = w := by
    symm
    apply (proximalMap_characterization H (conjugateFunction H φ) hp' hc' hl'
      μ⁻¹ (inv_pos.mpr hμ) (μ⁻¹ • f) w).2.mpr
    rw [hscale]
    exact hrev
  have hwmin : IsProximalMinimizer H (conjugateFunction H φ) μ⁻¹ (μ⁻¹ • f) w := by
    rw [← hdual]
    exact proximalMap_minimizes H (conjugateFunction H φ) hp' hc' hl'
      μ⁻¹ (inv_pos.mpr hμ) (μ⁻¹ • f)
  have hea := envelope_at_finite_minimizer φ μ f u r hr hu
  have heb := envelope_at_finite_minimizer (conjugateFunction H φ) μ⁻¹ (μ⁻¹ • f) w s hs' hwmin
  change u + μ • proximalMap H (conjugateFunction H φ) μ⁻¹ (μ⁻¹ • f) = f ∧
    ∃ r s a b : ℝ, φ u = (r : WithTop ℝ) ∧
      hilbertConjugate H φ (proximalMap H (conjugateFunction H φ) μ⁻¹ (μ⁻¹ • f)) = (s : EReal) ∧
      conjugateFunction H φ (proximalMap H (conjugateFunction H φ) μ⁻¹ (μ⁻¹ • f)) = (s : WithTop ℝ) ∧
      r + s = ⟪u, proximalMap H (conjugateFunction H φ) μ⁻¹ (μ⁻¹ • f)⟫_ℝ ∧
      moreauEnvelope H φ μ f = (a : EReal) ∧
      moreauEnvelope H (conjugateFunction H φ) μ⁻¹ (μ⁻¹ • f) = (b : EReal) ∧
      a + b = ‖f‖ ^ 2 / (2 * μ)
  rw [hdual]
  exact ⟨hf, r, s, _, _, hr, hs, hs', hrs, hea, heb, energy_algebra μ hμ f u w r s hf hrs⟩

theorem moreau_unit_parameter : MoreauSpec.UnitParameter.{u} := by
  intro H _ _ _ φ hp hc hl f
  have h := moreau_decomposition H φ hp hc hl 1 zero_lt_one f
  dsimp only at h
  simp only [inv_one, one_smul, mul_one] at h
  obtain ⟨hd, r, s, a, b, _, _, _, _, ha, hb, he⟩ := h
  refine ⟨hd, ?_⟩
  change moreauEnvelope H φ 1 f + moreauEnvelope H (conjugateFunction H φ) 1 f = _
  change moreauEnvelope H φ 1 f = (a : EReal) at ha
  change moreauEnvelope H (conjugateFunction H φ) 1 f = (b : EReal) at hb
  rw [ha, hb, ← EReal.coe_add, he]

end ExpandedFA.Proximal
