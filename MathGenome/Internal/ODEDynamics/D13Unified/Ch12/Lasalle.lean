import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch12.Lasalle
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Omega
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence

noncomputable section
open Set Filter Metric
open scoped Topology

namespace D13Unified.Ch12.Lasalle
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch11.Invariant
open Specs.D13Unified.Ch11.Flow
open Specs.D13Unified.Ch11.OmegaTopology
open Specs.D13Unified.Ch12.Lasalle
open Ch06.StateDerivative
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Relative invariance passes to a closure contained in the original state
domain. Only times in the limiting point's actual lifespan are used. -/
lemma invariant_closure (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {S : Set E}
    (hS : invariantValue F S) (hcl : closure S ⊆ F.domain) :
    invariantValue F (closure S) := by
  refine ⟨hcl, ?_⟩
  intro x hx t ht
  obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.mp hx
  have hxt : x ∈ timeDomainValue F t := ⟨hcl hx, ht⟩
  have hevent : ∀ᶠ n in atTop, s n ∈ timeDomainValue F t :=
    hlim ((Ch11.Flow.isOpen_timeDomain F hF t).mem_nhds hxt)
  have hc := (Ch11.Flow.contDiffOn_timeMap 1 le_rfl F hF t).continuousOn.continuousAt
    ((Ch11.Flow.isOpen_timeDomain F hF t).mem_nhds hxt)
  apply isClosed_closure.mem_of_tendsto (hc.tendsto.comp hlim)
  filter_upwards [hevent] with n hn
  exact subset_closure (hS.2 (s n) (hs n) t hn.2)

/-- The points of complete orbits in Z form an invariant subset of Z. -/
lemma core_invariant (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {Z : Set E} (hZΩ : Z ⊆ F.domain) :
    invariantValue F (completeCore F Z) := by
  refine ⟨fun x hx => hZΩ hx.1, ?_⟩
  intro x hx s hs
  have htrans := Ch11.Flow.flow_translation F hF x (hZΩ hx.1) s hs
  refine ⟨hx.2.2 s, ?_, ?_⟩
  · rw [htrans.1, hx.2.1]
    rfl
  · intro t
    rw [htrans.2 t (hx.2.1.symm ▸ mem_univ (t+s))]
    exact hx.2.2 (t+s)

/-- Compactness of Z supplies completeness even for an invariant subset
that is not closed: first take its invariant compact closure. -/
lemma compact_core (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {Z : Set E}
    (hZ : IsCompact Z) (hZΩ : Z ⊆ F.domain) :
    IsCompact (completeCore F Z) ∧ invariantValue F (completeCore F Z) ∧
      (∀ S : Set E, S ⊆ Z → invariantValue F S → S ⊆ completeCore F Z) := by
  have hclosed := hZ.isClosed
  have hlargest : ∀ S : Set E, S ⊆ Z → invariantValue F S → S ⊆ completeCore F Z := by
    intro S hSZ hS
    have hclZ : closure S ⊆ Z := closure_minimal hSZ hclosed
    have hclS := invariant_closure F hF hS (hclZ.trans hZΩ)
    have hcS := hZ.of_isClosed_subset isClosed_closure hclZ
    intro x hx
    have hcomp := Ch11.Invariant.compact_complete F hF (closure S) hcS hclS x
      (subset_closure hx)
    exact ⟨hSZ hx, hcomp.1, fun t => hclZ (hcomp.2 t)⟩
  have hinv := core_invariant F hF hZΩ
  have hcoreZ : completeCore F Z ⊆ Z := fun _ hx => hx.1
  have hclZ : closure (completeCore F Z) ⊆ Z := closure_minimal hcoreZ hclosed
  have hclInv := invariant_closure F hF hinv (hclZ.trans hZΩ)
  have hclCore := hlargest _ hclZ hclInv
  have hcoreClosed : IsClosed (completeCore F Z) := isClosed_of_closure_subset hclCore
  exact ⟨hZ.of_isClosed_subset hcoreClosed hcoreZ, hinv, hlargest⟩

omit [FiniteDimensional ℝ E] in
/-- Continuity of the Lie derivative uses C¹ regularity of V only near K. -/
lemma lieDerivative_continuousOn (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {K U : Set E} {V : E → ℝ}
    (hKΩ : K ⊆ F.domain) (hU : IsOpen U) (hKU : K ⊆ U)
    (hV : ContDiffOn ℝ 1 V U) : ContinuousOn (lieDerivative F V) K := by
  exact ((hV.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU).clm_apply
    (hF.continuousOn.mono hKΩ)

lemma zeroSet_compact (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {K U : Set E} {V : E → ℝ}
    (hK : IsCompact K) (hKΩ : K ⊆ F.domain) (hU : IsOpen U) (hKU : K ⊆ U)
    (hV : ContDiffOn ℝ 1 V U) : IsCompact (zeroSet F K V) := by
  have hc := (lieDerivative_continuousOn F hF hKΩ hU hKU hV).preimage_isClosed_of_isClosed
    hK.isClosed (isClosed_singleton (x := (0 : ℝ)))
  have he : K ∩ lieDerivative F V ⁻¹' {0} = zeroSet F K V := by
    ext x
    simp [zeroSet]
  rw [he] at hc
  exact hK.of_isClosed_subset hc (fun _ hx => hx.1)

/-- Chain rule along the canonical solution at any allowed time. -/
lemma lyapunov_hasDerivAt (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {V : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hV : ContDiffOn ℝ 1 V U) {x : E} (hx : x ∈ F.domain)
    {t : ℝ} (ht : t ∈ (flowInterval F x).carrier) (hVU : flow F t x ∈ U) :
    HasDerivAt (fun r => V (flow F r x)) (lieDerivative F V (flow F t x)) t := by
  have hv := ((hV.differentiableOn one_ne_zero _ hVU).differentiableAt
    (hU.mem_nhds hVU)).hasFDerivAt
  have hd := (flow_ivp F hF hx).1.2.2 t ht
  simpa only [lieDerivative, AutonomousODE.toODE_eval, Function.comp_def, flow,
    AutonomousODE.eval] using hv.comp_hasDerivAt t hd

/-- V is nonincreasing along every forward orbit in K. -/
lemma lyapunov_antitone (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {K U : Set E} {V : E → ℝ}
    (hInv : positiveInvariantValue F K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hV : ContDiffOn ℝ 1 V U) (hdec : ∀ z ∈ K, lieDerivative F V z ≤ 0)
    {x : E} (hx : x ∈ K)
    (hcomplete : Ici 0 ⊆ (flowInterval F x).carrier) :
    AntitoneOn (fun t => V (flow F t x)) (Ici 0) := by
  have hstay (t : ℝ) (ht : 0 ≤ t) := hInv.2 x hx t (hcomplete ht) ht
  have hd (t : ℝ) (ht : 0 ≤ t) := lyapunov_hasDerivAt F hF hU hV (hInv.1 hx)
    (hcomplete ht) (hKU (hstay t ht))
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ))
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  · intro t ht
    exact (hd t (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    exact hdec _ (hstay t (interior_subset ht))

/-- Compactness bounds V below, so its monotone values have a finite limit. -/
lemma lyapunov_limit (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {K U : Set E} {V : E → ℝ}
    (hK : IsCompact K) (hInv : positiveInvariantValue F K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hV : ContDiffOn ℝ 1 V U)
    (hdec : ∀ z ∈ K, lieDerivative F V z ≤ 0) {x : E} (hx : x ∈ K)
    (hcomplete : Ici 0 ⊆ (flowInterval F x).carrier) :
    ∃ l : ℝ, Tendsto (fun t : ℝ => V (flow F t x)) atTop (𝓝 l) := by
  have hanti := lyapunov_antitone F hF hInv hU hKU hV hdec hx hcomplete
  let w : ℝ → ℝ := fun t => V (flow F (max t 0) x)
  have hw : Antitone w := fun a b hab => hanti (le_max_right a 0)
    (le_max_right b 0) (max_le_max_right 0 hab)
  obtain ⟨b, hb⟩ := hK.bddBelow_image (hV.continuousOn.mono hKU)
  have hbd : BddBelow (range w) := by
    refine ⟨b, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hb ⟨_, hInv.2 x hx _ (hcomplete (le_max_right t 0)) (le_max_right t 0), rfl⟩
  refine ⟨⨅ t, w t, (tendsto_atTop_ciInf hw hbd).congr' ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  dsimp [w]
  rw [max_eq_left ht]

omit [FiniteDimensional ℝ E] in
/-- A compact positively invariant set confines the positive orbit and its
ambient closure. -/
lemma positiveOrbit_closure_subset (F : AutonomousODE E)
    {K : Set E} (hK : IsCompact K) (hInv : positiveInvariantValue F K)
    {x : E} (hx : x ∈ K) : closure (positiveOrbit F x) ⊆ K := by
  apply closure_minimal _ hK.isClosed
  rintro _ ⟨t, ht, rfl⟩
  exact hInv.2 x hx t ht.1 ht.2

omit [FiniteDimensional ℝ E] in
/-- Every omega-limit point has the same limiting Lyapunov value. -/
lemma lyapunov_constant_on_omega (F : AutonomousODE E)
    (_hF : ContDiffOn ℝ 1 F.eval F.domain) {K U : Set E} {V : E → ℝ}
    (hK : IsCompact K) (hInv : positiveInvariantValue F K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hV : ContDiffOn ℝ 1 V U) {x : E} (hx : x ∈ K)
    {l : ℝ} (hl : Tendsto (fun t : ℝ => V (flow F t x)) atTop (𝓝 l)) :
    ∀ y ∈ omegaValue F x, V y = l := by
  intro y hy
  have hyK := positiveOrbit_closure_subset F hK hInv hx
    (Ch11.OmegaTopology.omega_subset F x hy)
  obtain ⟨t, _, htTop, hty⟩ := (Ch11.OmegaTopology.sequence_characterization F x y).mp hy
  have hc := hV.continuousOn.continuousAt (hU.mem_nhds (hKU hyK))
  exact tendsto_nhds_unique (hc.tendsto.comp hty) (hl.comp htTop)

/-- Invariance makes V constant along the entire orbit of an omega-limit
point, so the chain rule at time zero gives the zero Lie derivative. -/
lemma omega_subset_zeroSet (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {K U : Set E} {V : E → ℝ}
    (hK : IsCompact K) (hInv : positiveInvariantValue F K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hV : ContDiffOn ℝ 1 V U)
    (hdec : ∀ z ∈ K, lieDerivative F V z ≤ 0) {x : E} (hx : x ∈ K) :
    omegaValue F x ⊆ zeroSet F K V := by
  have hclK := positiveOrbit_closure_subset F hK hInv hx
  have hcl := hK.of_isClosed_subset isClosed_closure hclK
  have ho := Ch11.Omega.compact_omega F hF x (hInv.1 hx) hcl (hclK.trans hInv.1)
  obtain ⟨l, hl⟩ := lyapunov_limit F hF hK hInv hU hKU hV hdec hx ho.1
  have hconst := lyapunov_constant_on_omega F hF hK hInv hU hKU hV hx hl
  intro y hy
  have hyK := hclK (ho.2.2.2.2.1 hy)
  have hcomplete := ho.2.2.2.2.2.2.1 y hy
  refine ⟨hyK, ?_⟩
  have hzero := (Ch11.Flow.flow_zero F hF y (hInv.1 hyK)).2
  have h0 : (0 : ℝ) ∈ (flowInterval F y).carrier := hcomplete.1.symm ▸ mem_univ 0
  have hd : HasDerivAt (fun t => V (flow F t y)) (lieDerivative F V y) 0 := by
    simpa only [hzero] using lyapunov_hasDerivAt F hF hU hV (hInv.1 hyK) h0
      (show flow F 0 y ∈ U by rw [hzero]; exact hKU hyK)
  have heq : (fun t => V (flow F t y)) = fun _ : ℝ => l :=
    funext fun t => hconst _ (hcomplete.2 t)
  rw [heq] at hd
  exact hd.unique (hasDerivAt_const (0 : ℝ) l)

/-- LaSalle's invariance principle on the original partial-flow domain. -/
theorem lasalle : InvariancePrinciple.{u} := by
  intro E _ _ _ F hF K hK hInv V U hU hKU hV hdec
  dsimp only
  have hZ := zeroSet_compact F hF hK hInv.1 hU hKU hV
  have hZΩ : zeroSet F K V ⊆ F.domain := fun _ hx => hInv.1 hx.1
  obtain ⟨hM, hMinv, hmax⟩ := compact_core F hF hZ hZΩ
  have horbit (x : E) (hx : x ∈ K) :
      Ici 0 ⊆ (flowInterval F x).carrier ∧
      (∀ t : ℝ, 0 ≤ t → flow F t x ∈ K) ∧
      (omegaValue F x).Nonempty ∧ omegaValue F x ⊆ completeCore F (zeroSet F K V) ∧
      Tendsto (fun t : ℝ => infDist (flow F t x) (completeCore F (zeroSet F K V)))
        atTop (𝓝 0) := by
    have hforward := Ch11.Invariant.compact_forward_complete F hF K hK hInv x hx
    have hclK := positiveOrbit_closure_subset F hK hInv hx
    have hcl := hK.of_isClosed_subset isClosed_closure hclK
    have ho := Ch11.Omega.compact_omega F hF x (hInv.1 hx) hcl (hclK.trans hInv.1)
    have hωM := hmax _ (omega_subset_zeroSet F hF hK hInv hU hKU hV hdec hx)
      ho.2.2.2.2.2.1
    refine ⟨hforward.1, hforward.2, ho.2.1, hωM, ?_⟩
    exact squeeze_zero (fun _ => infDist_nonneg)
      (fun _ => infDist_le_infDist_of_subset hωM ho.2.1) ho.2.2.2.2.2.2.2.2.2
  refine ⟨fun _ hx => hx.1, hM, hMinv, hmax, ?_, horbit⟩
  rintro ⟨x, hx⟩
  exact (horbit x hx).2.2.1.mono (horbit x hx).2.2.2.1

/-- A singleton invariant core attracts every starting point in K. -/
theorem singleton_convergence : SingletonConvergence.{u} := by
  intro E _ _ _ F hF K hK hInv V U hU hKU hV hdec p hp heq hM x hx
  have h := (lasalle F hF K hK hInv V U hU hKU hV hdec).2.2.2.2.2 x hx
  refine ⟨h.1, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [hM, infDist_singleton] using h.2.2.2.2

end D13Unified.Ch12.Lasalle
