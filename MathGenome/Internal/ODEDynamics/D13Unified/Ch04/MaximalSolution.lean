import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.LocalExistenceUniqueness
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.MaximalSolution

noncomputable section
open Set Filter
open scoped Topology

namespace D13Unified.Ch04.MaximalSolution
universe u v
open Specs.D13Unified.Ch04.MaximalSolution

/-- Every nonempty open real interval has extended-real endpoints, including
the two rays and the whole real line. -/
lemma open_interval_endpoints (I : OpenTimeInterval) (s : ℝ) (hs : s ∈ I.carrier) :
    ∃ a b : EReal, a < (s : EReal) ∧ (s : EReal) < b ∧
      I.carrier = {t : ℝ | a < (t : EReal) ∧ (t : EReal) < b} := by
  let S : Set EReal := (fun t : ℝ => (t : EReal)) '' I.carrier
  have hiff (t : ℝ) : t ∈ I.carrier ↔ sInf S < (t : EReal) ∧ (t : EReal) < sSup S := by
    constructor
    · intro ht
      obtain ⟨l, r, hlt, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (I.isOpen.mem_nhds ht)
      obtain ⟨l', hll', hl't⟩ := exists_between hlt.1
      obtain ⟨r', htr', hr'r⟩ := exists_between hlt.2
      exact ⟨lt_of_le_of_lt (sInf_le (show (l' : EReal) ∈ S from
        ⟨l', hsub ⟨hll', hl't.trans hlt.2⟩, rfl⟩)) (EReal.coe_lt_coe_iff.mpr hl't),
        lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr htr') (le_sSup
          (show (r' : EReal) ∈ S from ⟨r', hsub ⟨hlt.1.trans htr', hr'r⟩, rfl⟩))⟩
    · rintro ⟨hl, hr⟩
      obtain ⟨a, ha, hat⟩ := sInf_lt_iff.mp hl
      obtain ⟨b, hb, htb⟩ := lt_sSup_iff.mp hr
      obtain ⟨a, ha, rfl⟩ := ha
      obtain ⟨b, hb, rfl⟩ := hb
      exact I.ordConnected.out ha hb
        ⟨(EReal.coe_lt_coe_iff.mp hat).le, (EReal.coe_lt_coe_iff.mp htb).le⟩
  exact ⟨sInf S, sSup S, (hiff s).mp hs |>.1, (hiff s).mp hs |>.2, Set.ext hiff⟩

/-- Glue all classical solutions through one datum. Only local choices of
representatives enter this proof; no canonical solution map is postulated. -/
theorem maximal_solution : maximalSolutionExpected.{u} := by
  intro E _ _ _ F hF s ξ hs
  classical
  let A := {x : Solution F // s ∈ x.interval.carrier ∧ x.representative s = ξ}
  obtain ⟨I₀, x₀, hx₀, _⟩ :=
    Ch03.LocalExistenceUniqueness.local_existence_uniqueness F hF s ξ hs
  let a₀ : A := ⟨⟨I₀, x₀, hx₀.1⟩, hx₀.2⟩
  let D : Set ℝ := ⋃ a : A, a.val.interval.carrier
  have hDs : s ∈ D := mem_iUnion.mpr ⟨a₀, a₀.property.1⟩
  have hDo : IsOpen D := isOpen_iUnion (fun a : A => a.val.interval.isOpen)
  have hDc : OrdConnected D := by
    constructor
    intro a ha b hb t ht
    obtain ⟨x, hx⟩ := mem_iUnion.mp ha
    obtain ⟨y, hy⟩ := mem_iUnion.mp hb
    by_cases hts : t ≤ s
    · exact mem_iUnion.mpr ⟨x, x.val.interval.ordConnected.out hx x.property.1 ⟨ht.1, hts⟩⟩
    · exact mem_iUnion.mpr ⟨y, y.val.interval.ordConnected.out y.property.1 hy
        ⟨(le_of_not_ge hts), ht.2⟩⟩
  let I : OpenTimeInterval := ⟨⟨D, ⟨s, hDs⟩, hDc⟩, hDo⟩
  let z : ℝ → E := fun t =>
    if h : ∃ a : A, t ∈ a.val.interval.carrier then
      (Classical.choose h).val.representative t else 0
  have hz (a : A) : EqOn z a.val.representative a.val.interval.carrier := by
    intro t ht
    have hex : ∃ b : A, t ∈ b.val.interval.carrier := ⟨a, ht⟩
    dsimp only [z]
    rw [dite_eq_left hex]
    exact Ch03.LocalExistenceUniqueness.overlap_uniqueness F hF
      (Classical.choose hex).val.interval a.val.interval
      (Classical.choose hex).val.representative a.val.representative s ξ
      ⟨(Classical.choose hex).val.isSolution, (Classical.choose hex).property⟩
      ⟨a.val.isSolution, a.property⟩ ⟨Classical.choose_spec hex, ht⟩
  have hlocal (t : ℝ) (ht : t ∈ D) :
      ContDiffAt ℝ 1 z t ∧ (t, z t) ∈ F.domain ∧ HasDerivAt z (F.eval t (z t)) t := by
    obtain ⟨a, ha⟩ := mem_iUnion.mp ht
    have heq : z =ᶠ[𝓝 t] a.val.representative :=
      Filter.mem_of_superset (a.val.interval.isOpen.mem_nhds ha) (fun r hr => hz a hr)
    refine ⟨(a.val.isSolution.1.contDiffAt
      (a.val.interval.isOpen.mem_nhds ha)).congr_of_eventuallyEq heq, ?_, ?_⟩
    · rw [hz a ha]
      exact a.val.isSolution.2.1 t ha
    · rw [hz a ha]
      exact (a.val.isSolution.2.2 t ha).congr_of_eventuallyEq heq
  have hsol : IsClassicalSolutionOn F I z :=
    ⟨fun t ht => (hlocal t ht).1.contDiffWithinAt,
      fun t ht => (hlocal t ht).2.1, fun t ht => (hlocal t ht).2.2⟩
  let X : Solution F := ⟨I, z, hsol⟩
  have hzs : z s = ξ := (hz a₀ a₀.property.1).trans a₀.property.2
  have hcover (y : Solution F) (hsy : s ∈ y.interval.carrier)
      (hyξ : y.representative s = ξ) :
      y.interval.carrier ⊆ X.interval.carrier ∧
        EqOn X.representative y.representative y.interval.carrier := by
    let a : A := ⟨y, hsy, hyξ⟩
    exact ⟨fun t ht => mem_iUnion.mpr ⟨a, ht⟩, hz a⟩
  have hmax : IsMaximal X := by
    rintro ⟨y, hxy, hstrict⟩
    have hsy := hxy.1 hDs
    have hyξ : y.representative s = ξ := (hxy.2 hDs).trans hzs
    exact hstrict.not_subset (hcover y hsy hyξ).1
  refine ⟨X, hDs, hzs, hmax, open_interval_endpoints I s hDs, ?_, ?_⟩
  · intro J y hy
    exact hcover ⟨J, y, hy.1⟩ hy.2.1 hy.2.2
  · intro y hsy hyξ hmy
    obtain ⟨hsub, heq⟩ := hcover y hsy hyξ
    have hdom : y.interval.carrier = X.interval.carrier := by
      by_contra hne
      exact hmy ⟨X, ⟨hsub, heq⟩, ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩⟩
    exact ⟨hdom, heq.symm⟩

/-- The same theorem on each actual constant-parameter slice. -/
theorem parameter_maximal_solution : parameterMaximalSolutionExpected.{u, v} := by
  intro E _ _ _ P _ _ _ F hF p s ξ hs
  exact maximal_solution (F.atParameter p)
    (ParameterODE.LocallyLipschitzInState.atParameter F hF p) s ξ hs

end D13Unified.Ch04.MaximalSolution
