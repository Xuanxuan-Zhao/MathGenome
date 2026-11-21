import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.RealAnalyticPropagation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.RealAnalyticLocal
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.Rebase

/-! Propagation along the real canonical trajectory. The proof uses the
open-and-closed principle on its actual interval and the nonautonomous
rebasing identity, with starting time, initial state and parameters variable. -/
noncomputable section
namespace D13Unified.Ch06.RealAnalyticPropagation
open Set Metric Filter
open scoped Topology
open D13Unified.Ch06.RealAnalytic
open D13Unified.Ch06.HolomorphicLimits D13Unified.Ch06.HolomorphicDependence
open Specs.D13Unified.Ch03.LocalLipschitz
open Specs.D13Unified.Ch04.MaximalSolutionMap

variable {n m : ℕ}

/-- Freeze only terminal time; all initial data remain variable. -/
def freezeTime (r : ℝ) (q : Fin (n+m+2) → ℝ) : Fin (n+m+2) → ℝ :=
  Fin.cons r (Fin.tail q)

lemma continuous_freezeTime (r : ℝ) : Continuous (@freezeTime n m r) := by
  apply continuous_pi
  intro i
  exact Fin.cases continuous_const (fun j => continuous_apply j.succ) i

lemma analytic_freezeTime (r : ℝ) {V : Set (Fin (n+m+2) → ℝ)} (hV : IsOpen V) :
    CoordinateRealAnalyticOn V (@freezeTime n m r) := by
  let G : (Fin (n+m+2) → ℂ) → Fin (n+m+2) → ℂ :=
    fun q => Fin.cons (r : ℂ) (Fin.tail q)
  have hG : CoordinateHolomorphicOn univ G :=
    coordinateHolomorphicOn_of_analyticOnNhd isOpen_univ (by
      intro q _
      apply AnalyticAt.pi
      intro i
      exact Fin.cases analyticAt_const
        (fun j => (ContinuousLinearMap.proj (R := ℂ) j.succ).analyticAt q) i)
  have h := coordinateRealAnalyticOn_real_restriction hG hV (fun _ _ => mem_univ _)
  convert h using 1
  ext q i
  exact Fin.cases (by simp [G, freezeTime])
    (fun j => by simp [G, freezeTime, Fin.tail, complexifyPoint]) i

/-- Data for a second step starting at the fixed intermediate absolute time. -/
def rebaseMap (r : ℝ) (g : (Fin (n+m+2) → ℝ) → Fin n → ℝ)
    (q : Fin (n+m+2) → ℝ) : Fin (n+m+2) → ℝ :=
  Fin.cons (q 0) (realFieldPoint r (g q) (fieldData (Fin.tail q)).2)

lemma analytic_rebaseMap (r : ℝ) {V : Set (Fin (n+m+2) → ℝ)}
    {g : (Fin (n+m+2) → ℝ) → Fin n → ℝ}
    (hg : CoordinateRealAnalyticOn V g) :
    CoordinateRealAnalyticOn V (rebaseMap r g) := by
  apply coordinateRealAnalyticOn_of_local_extension
  intro a ha
  obtain ⟨s, hs, hsV, G, hG, he, _⟩ := local_complexification hg a ha
  let H : (Fin (n+m+2) → ℂ) → Fin (n+m+2) → ℂ := fun q =>
    Fin.cons (q 0) (Fin.cons (r : ℂ) (Fin.append (G q)
      (fun i : Fin m => Fin.tail (Fin.tail q) (Fin.natAdd n i))))
  refine ⟨s, hs, hsV, H, ?_, ?_⟩
  · apply coordinateHolomorphicOn_of_continuous_lineAnalytic isOpen_ball
    · apply continuousOn_pi.mpr
      intro i
      refine Fin.cases (continuous_apply 0).continuousOn (fun j => ?_) i
      refine Fin.cases continuousOn_const (fun k => ?_) j
      exact Fin.addCases (fun l => by
        simpa [H, Function.comp_def] using (continuous_apply l).comp_continuousOn hG.continuousOn)
        (fun l => by
          simpa [H, Fin.tail] using
            (show ContinuousOn (fun q : Fin (n+m+2) → ℂ => q ((Fin.natAdd n l).succ.succ))
              (ball (complexifyPoint a) s) from (continuous_apply _).continuousOn)) k
    · intro b v z hz
      apply AnalyticAt.pi
      intro i
      have hline := analyticAt_affineLine b v z
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [H, Function.comp_def] using
          ((ContinuousLinearMap.proj (R := ℂ) 0).analyticAt _).comp hline
      · refine Fin.cases ?_ (fun k => ?_) j
        · simpa [H] using (analyticAt_const (𝕜 := ℂ) (v := (r : ℂ)) (x := z))
        · refine Fin.addCases (fun l => ?_) (fun l => ?_) k
          · simpa [H, Function.comp_def] using
              ((ContinuousLinearMap.proj (R := ℂ) l).analyticAt _).comp
                (analyticAt_comp_coordinateHolomorphic hG hline hz)
          · simpa [H, Fin.tail, Function.comp_def] using
              ((ContinuousLinearMap.proj (R := ℂ) ((Fin.natAdd n l).succ.succ)).analyticAt _).comp hline
  · intro x hx
    ext i
    refine Fin.cases (by simp [H, rebaseMap]) (fun j => ?_) i
    refine Fin.cases (by simp [H, rebaseMap, realFieldPoint]) (fun k => ?_) j
    exact Fin.addCases (fun l => by simp [H, rebaseMap, realFieldPoint, he x hx])
      (fun l => by simp [H, rebaseMap, realFieldPoint, fieldData, Fin.tail]) k

/-- The actual coordinate domain is open under the original uniqueness
hypothesis, independently of analyticity of the field. -/
lemma solutionDomain_isOpen (F : ParameterODE (Fin n → ℝ) (Fin m → ℝ))
    (hF : parameterLocallyLipschitzInStateValue F) :
    IsOpen (solutionDomainInCoordinates F) :=
  (D13Unified.Ch05.OpenDomain.open_domain F hF).preimage
    ((continuous_apply 0).prodMk ((continuous_fieldData n m).comp
      (continuous_pi fun i => continuous_apply i.succ)))

/-- Continuity here is only on the actual maximal domain; the ambient
zero totalization is never presumed continuous outside it. -/
lemma solutionInCoordinates_continuousOn (F : ParameterODE (Fin n → ℝ) (Fin m → ℝ))
    (hF : parameterLocallyLipschitzInStateValue F) :
    ContinuousOn (solutionInCoordinates F) (solutionDomainInCoordinates F) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hc : Continuous (fun q : solutionDomainInCoordinates F =>
      (q.val 0, fieldData (Fin.tail q.val))) :=
    ((continuous_apply 0).prodMk ((continuous_fieldData n m).comp
      (continuous_pi fun i => continuous_apply i.succ))).comp continuous_subtype_val
  exact (D13Unified.Ch05.OpenDomain.continuous_solutionMap F hF).comp
    (hc.subtype_mk fun q => q.property)

/-- Points having an actual open analytic neighborhood inside the domain. -/
def analyticLocus (F : ParameterODE (Fin n → ℝ) (Fin m → ℝ)) :
    Set (Fin (n+m+2) → ℝ) :=
  {q | ∃ V, IsOpen V ∧ q ∈ V ∧ V ⊆ solutionDomainInCoordinates F ∧
    CoordinateRealAnalyticOn V (solutionInCoordinates F)}

lemma isOpen_analyticLocus (F : ParameterODE (Fin n → ℝ) (Fin m → ℝ)) :
    IsOpen (analyticLocus F) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro q ⟨V, hV, hq, hVD, hf⟩
  exact Filter.mem_of_superset (hV.mem_nhds hq) fun x hx => ⟨V, hV, hx, hVD, hf⟩

lemma analyticLocus_subset (F : ParameterODE (Fin n → ℝ) (Fin m → ℝ)) :
    analyticLocus F ⊆ solutionDomainInCoordinates F := by
  rintro q ⟨_, _, hq, hVD, _⟩
  exact hVD hq

lemma analyticOn_analyticLocus (F : ParameterODE (Fin n → ℝ) (Fin m → ℝ)) :
    CoordinateRealAnalyticOn (analyticLocus F) (solutionInCoordinates F) := by
  rintro q ⟨V, hV, hq, hVD, hf⟩
  obtain ⟨r, hr, hrV, hseries⟩ := hf q hq
  exact ⟨r, hr, fun x hx => ⟨V, hV, hrV hx, hVD, hf⟩, hseries⟩

/-- The true nonautonomous composition law, used only when the original
terminal and intermediate times belong to the same original interval. -/
lemma solution_rebase (F : ParameterODE (Fin n → ℝ) (Fin m → ℝ))
    (hF : parameterLocallyLipschitzInStateValue F) {q : Fin (n+m+2) → ℝ} {r : ℝ}
    (hq : q ∈ solutionDomainInCoordinates F)
    (hr : freezeTime r q ∈ solutionDomainInCoordinates F) :
    solutionInCoordinates F
        (rebaseMap r (solutionInCoordinates F ∘ freezeTime r) q) =
      solutionInCoordinates F q := by
  simpa [solutionInCoordinates, rebaseMap, freezeTime, Function.comp_def] using
    (ParameterODE.rebase F hF
    (fieldData (Fin.tail q)).1.1 (fieldData (Fin.tail q)).1.2
    (fieldData (Fin.tail q)).2 hq.1 r hr.2 _ rfl).2 (q 0) hq.2

/-- Compose two actual analytic neighborhoods, shrinking to a common open
existence neighborhood before applying the rebasing identity. -/
lemma analyticLocus_rebase (F : ParameterODE (Fin n → ℝ) (Fin m → ℝ))
    (hF : parameterLocallyLipschitzInStateValue F) {q : Fin (n+m+2) → ℝ} {r : ℝ}
    (hq : q ∈ solutionDomainInCoordinates F)
    (hi : freezeTime r q ∈ analyticLocus F)
    (ho : rebaseMap r (solutionInCoordinates F ∘ freezeTime r) q ∈ analyticLocus F) :
    q ∈ analyticLocus F := by
  obtain ⟨U, hU, hiU, hUD, hUf⟩ := hi
  obtain ⟨W, hW, hoW, _, hWf⟩ := ho
  let V := solutionDomainInCoordinates F ∩ freezeTime r ⁻¹' U
  have hV : IsOpen V := (solutionDomain_isOpen F hF).inter
    (hU.preimage (continuous_freezeTime r))
  have hqV : q ∈ V := ⟨hq, hiU⟩
  have hg : CoordinateRealAnalyticOn V (solutionInCoordinates F ∘ freezeTime r) :=
    hUf.comp (analytic_freezeTime r hV) hV (fun _ hx => hx.2)
  let Q := rebaseMap r (solutionInCoordinates F ∘ freezeTime r)
  have hQ : CoordinateRealAnalyticOn V Q := analytic_rebaseMap r hg
  let N := V ∩ Q ⁻¹' W
  have hN : IsOpen N := hQ.continuousOn.isOpen_inter_preimage hV hW
  have hcomp : CoordinateRealAnalyticOn N (solutionInCoordinates F ∘ Q) :=
    hWf.comp (hQ.mono hN inter_subset_left) hN (fun _ hx => hx.2)
  refine ⟨N, hN, ⟨hqV, hoW⟩, fun _ hx => hx.1.1, hcomp.congr ?_⟩
  intro x hx
  exact (solution_rebase F hF hx.1.1 (hUD hx.1.2)).symm

/-- Connectedness argument on a reference maximal interval. The moving-data
analyticity in `analyticLocus` retains all four groups of variables. -/
lemma analyticLocus_entire_interval (F : ParameterODE (Fin n → ℝ) (Fin m → ℝ))
    (hF : parameterLocallyLipschitzInStateValue F)
    (hlocal : ∀ (s : ℝ) (ξ : Fin n → ℝ) (p : Fin m → ℝ), ((s, ξ), p) ∈ F.domain →
      ∃ δ : ℝ, 0 < δ ∧
        ball (Fin.cons s (realFieldPoint s ξ p)) δ ⊆ solutionDomainInCoordinates F ∧
        CoordinateRealAnalyticOn (ball (Fin.cons s (realFieldPoint s ξ p)) δ)
          (solutionInCoordinates F))
    (s : ℝ) (ξ : Fin n → ℝ) (p : Fin m → ℝ) (hs : ((s, ξ), p) ∈ F.domain) :
    ∀ t ∈ (parameterMaximalIntervalValue F s ξ p).carrier,
      Fin.cons t (realFieldPoint s ξ p) ∈ analyticLocus F := by
  let I := parameterMaximalIntervalValue F s ξ p
  let x : ℝ → Fin n → ℝ := fun t => parameterSolutionValueValue F t s ξ p
  let θ : ℝ → Fin (n+m+2) → ℝ := fun t => Fin.cons t (realFieldPoint s ξ p)
  let Good : Set ℝ := θ ⁻¹' analyticLocus F
  have hθ : Continuous θ := by
    apply continuous_pi
    intro i
    exact Fin.cases continuous_id (fun _ => continuous_const) i
  have hGood : IsOpen Good := (isOpen_analyticLocus F).preimage hθ
  obtain ⟨hx, hsI, hxξ⟩ := ParameterODE.solutionValue_ivp F hF s ξ p hs
  have hxcont : ContinuousOn x I.carrier := hx.1.continuousOn
  obtain ⟨δ₀, hδ₀, hδ₀D, hδ₀a⟩ := hlocal s ξ p hs
  have hstart : s ∈ Good :=
    ⟨ball (θ s) δ₀, isOpen_ball, mem_ball_self hδ₀, hδ₀D, hδ₀a⟩
  have hcover : I.carrier ⊆ Good := by
    apply I.ordConnected.isPreconnected.subset_of_closure_inter_subset hGood
      ⟨s, hsI, hstart⟩
    rintro r ⟨hrclose, hrI⟩
    have hrD : θ r ∈ solutionDomainInCoordinates F := by
      simpa [θ, solutionDomainInCoordinates, parameterSolutionDomainValue, I] using And.intro hs hrI
    have hrU : ((r, x r), p) ∈ F.domain :=
      (ParameterODE.solutionValue_on_domain F hF r s ξ p ⟨hs, hrI⟩).2
    obtain ⟨δ, hδ, hδD, hδa⟩ := hlocal r (x r) p hrU
    let k : ℝ → Fin (n+m+2) → ℝ := fun u =>
      Fin.cons r (realFieldPoint u (x u) p)
    have hk : ContinuousOn k I.carrier := by
      apply continuousOn_pi.mpr
      intro i
      refine Fin.cases continuousOn_const (fun j => ?_) i
      refine Fin.cases continuousOn_id (fun l => ?_) j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) l
      · simpa [k, realFieldPoint, Function.comp_def] using
          (continuous_apply j).comp_continuousOn hxcont
      · simpa [k, realFieldPoint] using
          (show ContinuousOn (fun _ : ℝ => p j) I.carrier from continuousOn_const)
    let N := I.carrier ∩ k ⁻¹' ball (k r) δ
    have hN : IsOpen N := hk.isOpen_inter_preimage I.isOpen isOpen_ball
    have hrN : r ∈ N := ⟨hrI, mem_ball_self hδ⟩
    obtain ⟨u, huN, huGood⟩ := mem_closure_iff.mp hrclose N hN hrN
    have hi : freezeTime u (θ r) ∈ analyticLocus F := by
      simpa only [Good, mem_preimage, freezeTime, θ, Fin.tail_cons] using huGood
    have ho : rebaseMap u (solutionInCoordinates F ∘ freezeTime u) (θ r) ∈
        analyticLocus F := by
      have hku : k u ∈ analyticLocus F :=
        ⟨ball (k r) δ, isOpen_ball, huN.2, hδD, hδa⟩
      simpa [rebaseMap, freezeTime, solutionInCoordinates, θ, k, x] using hku
    exact analyticLocus_rebase F hF hrD hi ho
  exact hcover

/-- Joint real analyticity propagates from local diagonal charts to every
allowed finite elapsed time in the original canonical maximal domain. -/
theorem real_analytic_propagation :
    Specs.D13Unified.Ch06.RealAnalyticPropagation.realAnalyticPropagation_type := by
  intro n m F hF hlocal
  apply (analyticOn_analyticLocus F).mono (solutionDomain_isOpen F hF)
  intro q hq
  have h := analyticLocus_entire_interval F hF hlocal
    (fieldData (Fin.tail q)).1.1 (fieldData (Fin.tail q)).1.2
    (fieldData (Fin.tail q)).2 hq.1 (q 0) hq.2
  simpa only [realFieldPoint_fieldData, Fin.cons_self_tail] using h

end D13Unified.Ch06.RealAnalyticPropagation
