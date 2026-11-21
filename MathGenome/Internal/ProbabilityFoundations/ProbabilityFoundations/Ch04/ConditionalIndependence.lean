import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.ConditionalIndependence
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch03.ConditionalDominatedConvergence

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityFoundations.Ch04
universe u v w

/-- Conditional independence by the source's event identities. Each measurable
rectangle has its own almost sure identity; no common exceptional set is asserted. -/
noncomputable def IsConditionallyIndependent :
    ∀ {Ω : Type u} {S : Type v} {T : Type w} (G : MeasurableSpace Ω)
      [F : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T],
      Measure[F] Ω → (Ω → S) → (Ω → T) → Prop :=
  fun {_Ω} {_S} {_T} G _F _mS _mT P Y Z => ∀ (B : Set _) (C : Set _), MeasurableSet B → MeasurableSet C →
    Ch03.realConditionalExpectation G P
      ((Y ⁻¹' B ∩ Z ⁻¹' C).indicator (fun _ => (1 : ℝ))) =ᵐ[P]
      (fun ω => Ch03.realConditionalExpectation G P
          ((Y ⁻¹' B).indicator (fun _ => (1 : ℝ))) ω *
        Ch03.realConditionalExpectation G P
          ((Z ⁻¹' C).indicator (fun _ => (1 : ℝ))) ω)

private lemma bounded_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f)
    {M : ℝ} (hb : ∀ ω, ‖f ω‖ ≤ M) : Integrable f P :=
  (integrable_const M).mono' hf.aestronglyMeasurable (Eventually.of_forall hb)

private lemma simple_bounded {S : Type*} [MeasurableSpace S] (s : SimpleFunc S ℝ) :
    ∃ M : ℝ, ∀ x, ‖s x‖ ≤ M := by
  obtain ⟨M, hM⟩ := (s.finite_range.image (fun x : ℝ => ‖x‖)).bddAbove
  exact ⟨M, fun x => hM ⟨s x, Set.mem_range_self x, rfl⟩⟩

/-- Extend a conditional product identity from indicators in one target to
bounded measurable functions, keeping the other bounded factor fixed. -/
private lemma extend_indicators {Ω S : Type*} (G : MeasurableSpace Ω)
    [F : MeasurableSpace Ω] [MeasurableSpace S] (P : Measure[F] Ω)
    [IsProbabilityMeasure P] (hGF : G ≤ F) (Y : Ω → S) (hY : Measurable Y)
    (V : Ω → ℝ) (hVm : Measurable V) (hVb : ∃ N : ℝ, ∀ ω, ‖V ω‖ ≤ N)
    (h : ∀ B, MeasurableSet B →
      condExp G P (fun ω => (Y ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω * V ω) =ᵐ[P]
        (fun ω => condExp G P ((Y ⁻¹' B).indicator (fun _ => (1 : ℝ))) ω *
          condExp G P V ω))
    (u : S → ℝ) (hu : Measurable u) (hub : ∃ M : ℝ, ∀ y, ‖u y‖ ≤ M) :
    condExp G P (fun ω => u (Y ω) * V ω) =ᵐ[P]
      (fun ω => condExp G P (u ∘ Y) ω * condExp G P V ω) := by
  obtain ⟨N, hN⟩ := hVb
  have hVi : Integrable V P := bounded_integrable P hVm hN
  have hsimp (s : SimpleFunc S ℝ) :
      condExp G P (fun ω => s (Y ω) * V ω) =ᵐ[P]
        (fun ω => condExp G P (fun ω => s (Y ω)) ω * condExp G P V ω) := by
    induction s using SimpleFunc.induction with
    | @const c B hB =>
      have heq : (fun ω => (SimpleFunc.piecewise B hB (SimpleFunc.const S c)
          (SimpleFunc.const S 0)) (Y ω)) =
          (fun ω => c * (Y ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω) := by
        ext ω
        simp only [SimpleFunc.coe_piecewise, SimpleFunc.coe_const]
        by_cases hω : Y ω ∈ B <;> simp [hω]
      simp_rw [show ∀ ω, (SimpleFunc.piecewise B hB (SimpleFunc.const S c)
        (SimpleFunc.const S 0)) (Y ω) = c * (Y ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω
        from fun ω => congrFun heq ω]
      have heq' : (fun ω => c * (Y ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω * V ω) =
          c • (fun ω => (Y ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω * V ω) := by
        ext ω; simp [mul_assoc]
      rw [heq']
      filter_upwards [condExp_smul c (fun ω => (Y ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω * V ω) G (μ := P),
        condExp_smul c ((Y ⁻¹' B).indicator (fun _ => (1 : ℝ))) G (μ := P), h B hB]
        with ω hc hc' hi
      change _ = c * _ at hc hc'
      change condExp G P (fun ω => c * (Y ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω) ω =
        c * condExp G P ((Y ⁻¹' B).indicator (fun _ => (1 : ℝ))) ω at hc'
      rw [hc, hi, hc']
      ring
    | @add s t _ ihs iht =>
      obtain ⟨A, hA⟩ := simple_bounded s
      obtain ⟨B, hB⟩ := simple_bounded t
      have hsi := bounded_integrable P (s.measurable.comp hY) (fun ω => hA (Y ω))
      have hti := bounded_integrable P (t.measurable.comp hY) (fun ω => hB (Y ω))
      have hsVi := bounded_integrable P ((s.measurable.comp hY).mul hVm)
        (fun ω => (norm_mul _ _).trans_le (mul_le_mul (hA (Y ω)) (hN ω)
          (norm_nonneg _) ((norm_nonneg _).trans (hA (Y ω)))))
      have htVi := bounded_integrable P ((t.measurable.comp hY).mul hVm)
        (fun ω => (norm_mul _ _).trans_le (mul_le_mul (hB (Y ω)) (hN ω)
          (norm_nonneg _) ((norm_nonneg _).trans (hB (Y ω)))))
      have heq : (fun ω => (s + t) (Y ω) * V ω) =
          (fun ω => s (Y ω) * V ω) + (fun ω => t (Y ω) * V ω) := by
        ext ω; simp [add_mul]
      rw [heq]
      filter_upwards [condExp_add hsVi htVi G, condExp_add hsi hti G, ihs, iht]
        with ω ha hb hs ht
      change condExp G P (fun ω => s (Y ω) * V ω + t (Y ω) * V ω) ω =
        condExp G P (fun ω => s (Y ω) * V ω) ω +
          condExp G P (fun ω => t (Y ω) * V ω) ω at ha
      change condExp G P (fun ω => s (Y ω) + t (Y ω)) ω =
        condExp G P (fun ω => s (Y ω)) ω + condExp G P (fun ω => t (Y ω)) ω at hb
      change condExp G P (fun ω => s (Y ω) * V ω + t (Y ω) * V ω) ω =
        condExp G P (fun ω => s (Y ω) + t (Y ω)) ω * condExp G P V ω
      rw [ha, hs, ht, hb]
      ring
  obtain ⟨M, hM⟩ := hub
  let A := max M 0
  have hA : 0 ≤ A := le_max_right _ _
  let s := hu.stronglyMeasurable.approxBounded A
  have hsb : ∀ n x, ‖s n x‖ ≤ A := fun n x =>
    hu.stronglyMeasurable.norm_approxBounded_le hA n x
  have hsl : ∀ x, Tendsto (fun n => s n x) atTop (𝓝 (u x)) := fun x =>
    hu.stronglyMeasurable.tendsto_approxBounded_of_norm_le ((hM x).trans (le_max_left _ _))
  have hleft := Ch03.realConditionalExpectation_dominated_convergence G P hGF
    (fun n ω => s n (Y ω)) (u ∘ Y) (fun _ => A)
    (fun n => (s n).measurable.comp hY) (hu.comp hY) measurable_const
    (Eventually.of_forall fun _ => hA) (integrable_const A)
    (fun n => Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hsb n (Y ω))
    (Eventually.of_forall fun ω => hsl (Y ω))
  have hprod := Ch03.realConditionalExpectation_dominated_convergence G P hGF
    (fun n ω => s n (Y ω) * V ω) (fun ω => u (Y ω) * V ω)
    (fun _ => A * max N 0)
    (fun n => ((s n).measurable.comp hY).mul hVm) ((hu.comp hY).mul hVm)
    measurable_const (Eventually.of_forall fun _ => mul_nonneg hA (le_max_right _ _))
    (integrable_const _)
    (fun n => Eventually.of_forall fun ω => by
      rw [← Real.norm_eq_abs, norm_mul]
      exact mul_le_mul (hsb n (Y ω)) ((hN ω).trans (le_max_left _ _)) (norm_nonneg _) hA)
    (Eventually.of_forall fun ω => (hsl (Y ω)).mul_const (V ω))
  filter_upwards [hleft.2.2.1, hprod.2.2.1, ae_all_iff.mpr (fun n => hsimp (s n))] with ω hl hp he
  exact tendsto_nhds_unique hp ((hl.mul_const (condExp G P V ω)).congr (fun n => (he n).symm))

/-- Factorization for all bounded measurable real test functions, on arbitrary
measurable target spaces. -/
theorem conditional_independence_bounded_factorization :
    Specs.ProbabilityFoundations.Ch04.ConditionalIndependence.boundedFactorizationType := by
  intro Ω S T G F mS mT P _ hGF Y Z hY hZ hind u v hu hv hub hvb
  change IsConditionallyIndependent G P Y Z at hind
  change condExp G P (fun ω => u (Y ω) * v (Z ω)) =ᵐ[P]
    (fun ω => condExp G P (u ∘ Y) ω * condExp G P (v ∘ Z) ω)
  have hB (B : Set S) (hB : MeasurableSet B) :
      condExp G P (fun ω => (Y ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω * v (Z ω)) =ᵐ[P]
        (fun ω => condExp G P ((Y ⁻¹' B).indicator (fun _ => (1 : ℝ))) ω *
          condExp G P (v ∘ Z) ω) := by
    have hbound : ∃ N : ℝ, ∀ ω, ‖(Y ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω‖ ≤ N := by
      refine ⟨1, fun ω => ?_⟩
      by_cases hb : Y ω ∈ B <;> simp [hb]
    have ht := extend_indicators G P hGF Z hZ
      ((Y ⁻¹' B).indicator (fun _ => (1 : ℝ)))
      (measurable_const.indicator (hY hB)) hbound (fun C hC => ?_) v hv hvb
    · simpa only [mul_comm] using ht
    · have hi := hind B C hB hC
      change condExp G P ((Y ⁻¹' B ∩ Z ⁻¹' C).indicator (fun _ => (1 : ℝ))) =ᵐ[P]
        (fun ω => condExp G P ((Y ⁻¹' B).indicator (fun _ => (1 : ℝ))) ω *
          condExp G P ((Z ⁻¹' C).indicator (fun _ => (1 : ℝ))) ω) at hi
      have heq : (Y ⁻¹' B ∩ Z ⁻¹' C).indicator (fun _ => (1 : ℝ)) =
          (fun ω => (Z ⁻¹' C).indicator (fun _ => (1 : ℝ)) ω *
            (Y ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω) := by
        ext ω
        by_cases hb : Y ω ∈ B <;> by_cases hc : Z ω ∈ C <;> simp [hb, hc]
      rw [heq] at hi
      simpa only [mul_comm] using hi
  obtain ⟨N, hN⟩ := hvb
  exact extend_indicators G P hGF Y hY (v ∘ Z) (hv.comp hZ)
    ⟨N, fun ω => hN (Z ω)⟩ hB u hu hub

/-- Event factorization is unchanged by choosing any measurable conditional
expectation versions of the three indicators. -/
theorem conditional_independence_indicator_versions :
    Specs.ProbabilityFoundations.Ch04.ConditionalIndependence.indicatorVersionsType := by
  intro Ω S T G F mS mT P _ hGF Y Z hY hZ hind B C hB hC U V W hU hV hW
  have hBi := (integrable_const (1 : ℝ)).indicator (hY hB) (μ := P)
  have hCi := (integrable_const (1 : ℝ)).indicator (hZ hC) (μ := P)
  have hBCi := (integrable_const (1 : ℝ)).indicator ((hY hB).inter (hZ hC)) (μ := P)
  have heU := ((Ch03.isRealConditionalExpectationVersion_iff G P hGF _ U hBi).mp hU).2
  have heV := ((Ch03.isRealConditionalExpectationVersion_iff G P hGF _ V hCi).mp hV).2
  have heW := ((Ch03.isRealConditionalExpectationVersion_iff G P hGF _ W hBCi).mp hW).2
  filter_upwards [heU, heV, heW, hind B C hB hC] with ω hu hv hw hi
  exact hw.trans (hi.trans (congrArg₂ (· * ·) hu.symm hv.symm))

/-- The bounded-function factorization also holds for arbitrary versions. -/
theorem conditional_independence_bounded_versions :
    Specs.ProbabilityFoundations.Ch04.ConditionalIndependence.boundedVersionsType := by
  intro Ω S T G F mS mT P _ hGF Y Z hY hZ hind u v hu hv hub hvb U V W hU hV hW
  obtain ⟨M, hM⟩ := hub
  obtain ⟨N, hN⟩ := hvb
  have hui := bounded_integrable P (hu.comp hY) (fun ω => hM (Y ω))
  have hvi := bounded_integrable P (hv.comp hZ) (fun ω => hN (Z ω))
  have huvi := bounded_integrable P ((hu.comp hY).mul (hv.comp hZ))
    (fun ω => (norm_mul _ _).trans_le (mul_le_mul (hM (Y ω)) (hN (Z ω))
      (norm_nonneg _) ((norm_nonneg _).trans (hM (Y ω)))))
  have heU := ((Ch03.isRealConditionalExpectationVersion_iff G P hGF _ U hui).mp hU).2
  have heV := ((Ch03.isRealConditionalExpectationVersion_iff G P hGF _ V hvi).mp hV).2
  have heW := ((Ch03.isRealConditionalExpectationVersion_iff G P hGF _ W huvi).mp hW).2
  have he := conditional_independence_bounded_factorization G P hGF Y Z hY hZ hind
    u v hu hv ⟨M, hM⟩ ⟨N, hN⟩
  filter_upwards [heU, heV, heW, he] with ω hu hv hw hi
  exact hw.trans (hi.trans (congrArg₂ (· * ·) hu.symm hv.symm))

end ProbabilityFoundations.Ch04
