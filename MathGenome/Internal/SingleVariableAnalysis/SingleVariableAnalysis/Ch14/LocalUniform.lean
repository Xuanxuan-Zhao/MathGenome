import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.LocalUniform
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.ImproperContinuity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.ImproperDerivative
import Mathlib.Topology.Order.DenselyOrdered

/-! Local uniform improper limits, K03.14.local_uniform.
The compact-interval theorems apply locally. Uniqueness of the same improper
integral identifies the resulting functions on overlaps. A spanning interval
transfers the single base point to any requested compact subinterval.
-/
namespace SingleVariableAnalysis.Riemann.Improper
open Set Filter
open scoped Topology
open Specs.SingleVariableAnalysis.Ch10.OneEndpoint
open Specs.SingleVariableAnalysis.Ch14.UniformImproper
open Specs.SingleVariableAnalysis.Ch14.LocalUniform

/-- Patch compact uniform integral limits by uniqueness. Singletons supply the
pointwise limits, so this construction also works for an empty parameter set. -/
theorem exists_local_integral_limit
    (k : ScalarKind) (a : ℝ) (J : Set ℝ)
    (f : ℝ → ℝ → S.scalarValue k)
    (hlocal : ∀ c d : ℝ, c ≤ d → Icc c d ⊆ J →
      rightUniformConvergesValue k (Icc c d) (fun x t => f x t.val) a ⊤) :
    ∃ F : ℝ → S.scalarValue k, LocalIntegralLimit k a J f F ∧
      ∀ t ∈ J, rightHasIntegralValue k (fun x => f x t) a ⊤ (F t) := by
  classical
  have hp (t : J) : ∃ L, rightHasIntegralValue k (fun x => f x t.val) a ⊤ L := by
    obtain ⟨F, hF⟩ := hlocal t t le_rfl (by simpa only [Icc_self, singleton_subset_iff] using t.property)
    exact ⟨F ⟨t.val, by simp⟩,
      right_uniform_pointwise k _ _ _ _ _ hF ⟨t.val, by simp⟩⟩
  choose F hF using hp
  obtain ⟨Fext, hext⟩ := exists_ambientExtension J F
  have hpoint (t : ℝ) (ht : t ∈ J) :
      rightHasIntegralValue k (fun x => f x t) a ⊤ (Fext t) := by
    rw [hext ⟨t, ht⟩]
    exact hF ⟨t, ht⟩
  refine ⟨Fext, ?_, hpoint⟩
  intro c d hcd hsub
  obtain ⟨Fc, hFc⟩ := hlocal c d hcd hsub
  have heq : Fc = fun t : Icc c d => Fext t.val := by
    funext t
    exact right_unique k (fun x => f x t.val) a ⊤ _ _
      (right_uniform_pointwise k _ _ _ _ _ hFc t) (hpoint t (hsub t.property))
  rw [← heq]
  exact hFc

/-- Continuity is local, so a separate compact cutoff at every point suffices. -/
theorem continuousOn_of_local_integral_limit
    (k : ScalarKind) (a : ℝ) (J : Set ℝ) (hJ : IsOpen J)
    (f : ℝ → ℝ → S.scalarValue k)
    (FR : rightIndexValue a ⊤ → ℝ → S.scalarValue k)
    (hproper : ProperFamily k a J f FR)
    (F : ℝ → S.scalarValue k) (hF : LocalIntegralLimit k a J f F) :
    ContinuousOn F J := by
  intro t ht
  obtain ⟨c, d, htc, hnhds, hsub⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (hJ.mem_nhds ht)
  have hc : c ≤ d := htc.1.trans htc.2
  obtain ⟨h, hlim⟩ := hF c d hc hsub
  have hcont : ContinuousAt F t := by
    apply ParameterIntegral.continuousAt_of_uniform_approximation_on_nhds
      (Icc c d) ⟨t, htc⟩ hnhds F (fun R u => FR R u.val)
    · intro R
      exact (continuousOn_iff_continuous_domRestrict.mp ((hproper.continuous R).mono hsub)).continuousAt
    · intro ε hε
      obtain ⟨r, hr⟩ := hlim ε hε
      obtain ⟨R, hrR, _⟩ := right_later r r
      refine ⟨R, fun u => ?_⟩
      rw [hproper.equation R ⟨u.val, hsub u.property⟩]
      exact hr R hrR u
  exact hcont.continuousWithinAt

theorem local_improper_continuity :
    Specs.SingleVariableAnalysis.Ch14.LocalUniform.localContinuity := by
  intro k a J hJ f FR hproper hlocal
  obtain ⟨F, hF, hp⟩ := exists_local_integral_limit k a J f hlocal
  exact ⟨F, hF, hp, continuousOn_of_local_integral_limit k a J hJ f FR hproper F hF⟩

/-- Restrict the proper data and derivative tails to one compact interval and
apply the already established base-point differentiation theorem. -/
theorem compact_improper_derivative_limit
    (k : ScalarKind) (a : ℝ) (J : Set ℝ)
    (f ft : ℝ → ℝ → S.scalarValue k)
    (FR D : rightIndexValue a ⊤ → ℝ → S.scalarValue k)
    (G : ℝ → S.scalarValue k)
    (hp : ProperDerivativeFamily k a J f ft FR D)
    (hg : LocalDerivativeLimit k a J D G)
    (c d : ℝ) (hcd : c ≤ d) (hsub : Icc c d ⊆ J)
    (hbase : ∃ (t₀ : Icc c d) (L : S.scalarValue k),
      rightHasIntegralValue k (fun x => f x t₀.val) a ⊤ L) :
    ∃ F : ℝ → S.scalarValue k,
      rightUniformHasIntegralValue k (Icc c d) (fun x t => f x t.val) a ⊤
        (fun t => F t.val) ∧
      (∀ t : Icc c d, rightHasIntegralValue k (fun x => f x t.val) a ⊤ (F t.val)) ∧
      ContinuousOn F (Icc c d) ∧
      ∀ t ∈ Ioo c d, HasDerivAt F (G t) t := by
  let hf : rightFamilyRegularValue k (Icc c d) (fun x t => f x t.val) a ⊤ :=
    ⟨hp.regular.1, fun t => hp.regular.2 ⟨t.val, hsub t.property⟩⟩
  let hft : rightFamilyRegularValue k (Ioo c d) (fun x t => ft x t.val) a ⊤ :=
    ⟨hp.derivativeRegular.1,
      fun t => hp.derivativeRegular.2 ⟨t.val, hsub (Ioo_subset_Icc_self t.property)⟩⟩
  apply improper_derivative k a c d hcd _ _ hf hft FR D G
  · intro R t
    exact hp.equation R ⟨t.val, hsub t.property⟩
  · intro R
    exact (hp.continuous R).mono hsub
  · intro R t ht
    rw [← hp.derivativeEquation R ⟨t, hsub (Ioo_subset_Icc_self ht)⟩]
    exact hp.derivative R t (hsub (Ioo_subset_Icc_self ht))
  · intro R t
    exact hp.derivativeEquation R ⟨t.val, hsub (Ioo_subset_Icc_self t.property)⟩
  · exact hg c d hcd hsub
  · exact hbase

/-- The local derivative-tail limit is itself the improper integral of ft. -/
theorem derivative_integral_of_local_limit
    (k : ScalarKind) (a : ℝ) (J : Set ℝ)
    (f ft : ℝ → ℝ → S.scalarValue k)
    (FR D : rightIndexValue a ⊤ → ℝ → S.scalarValue k)
    (G : ℝ → S.scalarValue k)
    (hp : ProperDerivativeFamily k a J f ft FR D)
    (hg : LocalDerivativeLimit k a J D G) :
    ∀ t ∈ J, rightHasIntegralValue k (fun x => ft x t) a ⊤ (G t) := by
  intro t ht
  refine ⟨hp.derivativeRegular.2 ⟨t, ht⟩, fun ε hε => ?_⟩
  obtain ⟨r, hr⟩ := hg t t le_rfl
    (by simpa only [Icc_self, singleton_subset_iff] using ht) ε hε
  refine ⟨r, fun R hR => ?_⟩
  rw [← hp.derivativeEquation R ⟨t, ht⟩]
  exact hr R hR t (by simp)

theorem local_improper_differentiation :
    Specs.SingleVariableAnalysis.Ch14.LocalUniform.localDifferentiationWithLimit := by
  intro k a J hJ f ft FR D G hp hg hbase
  -- Only nondegenerate intervals have a base-point hypothesis. For a singleton
  -- we first use the derivative theorem on a genuine compact neighborhood.
  have hbase' (c d : ℝ) (hcd : c ≤ d) (hsub : Icc c d ⊆ J) :
      ∃ (t₀ : Icc c d) (L : S.scalarValue k),
        rightHasIntegralValue k (fun x => f x t₀.val) a ⊤ L := by
    rcases hcd.eq_or_lt with heq | hlt
    · subst d
      have hcJ : c ∈ J := hsub (by simp)
      obtain ⟨u, v, hcu, hnhds, huv⟩ :=
        exists_Icc_mem_subset_of_mem_nhds (hJ.mem_nhds hcJ)
      have hlt : u < v := (Icc_mem_nhds_iff.mp hnhds).1.trans
        (Icc_mem_nhds_iff.mp hnhds).2
      obtain ⟨H, _, hH, _⟩ := compact_improper_derivative_limit
        k a J f ft FR D G hp hg u v hlt.le huv (hbase u v hlt huv)
      exact ⟨⟨c, by simp⟩, H c, hH ⟨c, hcu⟩⟩
    · exact hbase c d hlt hsub
  have hlocal (c d : ℝ) (hcd : c ≤ d) (hsub : Icc c d ⊆ J) :
      rightUniformConvergesValue k (Icc c d) (fun x t => f x t.val) a ⊤ := by
    obtain ⟨F, hF, _⟩ := compact_improper_derivative_limit k a J f ft FR D G hp hg
      c d hcd hsub (hbase' c d hcd hsub)
    exact ⟨fun t => F t.val, hF⟩
  obtain ⟨F, hF, hpoint, hcont⟩ := local_improper_continuity k a J hJ f FR
    hp.toProperFamily hlocal
  refine ⟨F, hF, hpoint, hcont, ?_,
    derivative_integral_of_local_limit k a J f ft FR D G hp hg⟩
  intro t ht
  obtain ⟨c, d, htc, hnhds, hsub⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (hJ.mem_nhds ht)
  have hcd := htc.1.trans htc.2
  obtain ⟨Fc, hFc, hpointc, _, hder⟩ := compact_improper_derivative_limit
    k a J f ft FR D G hp hg c d hcd hsub (hbase' c d hcd hsub)
  apply (hder t (Icc_mem_nhds_iff.mp hnhds)).congr_of_eventuallyEq
  filter_upwards [hnhds] with u hu
  exact right_unique k (fun x => f x u) a ⊤ _ _ (hpoint u (hsub hu))
    (hpointc ⟨u, hu⟩)

/-- Convergence at one point supplies the base point for every compact
subinterval. The spanning compact interval remains inside the original J. -/
theorem compact_base_point_of_single_point
    (k : ScalarKind) (a : ℝ) (J : Set ℝ) (hinterval : OrdConnected J)
    (f ft : ℝ → ℝ → S.scalarValue k)
    (FR D : rightIndexValue a ⊤ → ℝ → S.scalarValue k)
    (G : ℝ → S.scalarValue k)
    (hp : ProperDerivativeFamily k a J f ft FR D)
    (hg : LocalDerivativeLimit k a J D G)
    (hbase : ∃ (t₀ : J) (L : S.scalarValue k),
      rightHasIntegralValue k (fun x => f x t₀.val) a ⊤ L) :
    ∀ c d : ℝ, c < d → Icc c d ⊆ J →
      ∃ (t₁ : Icc c d) (L : S.scalarValue k),
        rightHasIntegralValue k (fun x => f x t₁.val) a ⊤ L := by
  obtain ⟨t₀, L, hL⟩ := hbase
  intro c d hcd hsub
  have hcJ : c ∈ J := hsub ⟨le_rfl, hcd.le⟩
  have hspan : Icc (min c t₀.val) (max c t₀.val) ⊆ J :=
    hinterval.uIcc_subset hcJ t₀.property
  have hcspan : c ∈ Icc (min c t₀.val) (max c t₀.val) :=
    ⟨min_le_left _ _, le_max_left _ _⟩
  have htspan : t₀.val ∈ Icc (min c t₀.val) (max c t₀.val) :=
    ⟨min_le_right _ _, le_max_right _ _⟩
  obtain ⟨F, _, hpoint, _⟩ := compact_improper_derivative_limit
    k a J f ft FR D G hp hg (min c t₀.val) (max c t₀.val)
      (hcspan.1.trans hcspan.2) hspan ⟨⟨t₀.val, htspan⟩, L, hL⟩
  exact ⟨⟨c, le_rfl, hcd.le⟩, F c, hpoint ⟨c, hcspan⟩⟩

theorem single_base_point_improper_differentiation :
    Specs.SingleVariableAnalysis.Ch14.LocalUniform.singleBasePointDifferentiationWithLimit := by
  intro k a J hJ hinterval f ft FR D G hp hg hbase
  exact local_improper_differentiation k a J hJ f ft FR D G hp hg
    (compact_base_point_of_single_point k a J hinterval f ft FR D G hp hg hbase)

/-- Patch the locally convergent derivative integrals, rather than presupposing
that the compact limits were chosen compatibly. -/
theorem exists_local_derivative_limit
    (k : ScalarKind) (a : ℝ) (J : Set ℝ)
    (f ft : ℝ → ℝ → S.scalarValue k)
    (FR D : rightIndexValue a ⊤ → ℝ → S.scalarValue k)
    (hp : ProperDerivativeFamily k a J f ft FR D)
    (hg : LocalDerivativeConvergence k a J D) :
    ∃ G : ℝ → S.scalarValue k, LocalDerivativeLimit k a J D G := by
  have hlocal (c d : ℝ) (hcd : c ≤ d) (hsub : Icc c d ⊆ J) :
      rightUniformConvergesValue k (Icc c d) (fun x t => ft x t.val) a ⊤ := by
    obtain ⟨G, hG⟩ := hg c d hcd hsub
    refine ⟨fun t => G t.val, ⟨?_, ?_⟩⟩
    · exact ⟨hp.derivativeRegular.1,
        fun t => hp.derivativeRegular.2 ⟨t.val, hsub t.property⟩⟩
    · intro ε hε
      obtain ⟨r, hr⟩ := hG ε hε
      refine ⟨r, fun R hR t => ?_⟩
      rw [← hp.derivativeEquation R ⟨t.val, hsub t.property⟩]
      exact hr R hR t.val t.property
  obtain ⟨G, hG, _⟩ := exists_local_integral_limit k a J ft hlocal
  refine ⟨G, fun c d hcd hsub ε hε => ?_⟩
  obtain ⟨h, hlim⟩ := hG c d hcd hsub
  obtain ⟨r, hr⟩ := hlim ε hε
  refine ⟨r, fun R hR t ht => ?_⟩
  rw [hp.derivativeEquation R ⟨t, hsub ht⟩]
  exact hr R hR ⟨t, ht⟩

theorem local_improper_differentiation_of_convergence :
    Specs.SingleVariableAnalysis.Ch14.LocalUniform.localDifferentiation := by
  intro k a J hJ f ft FR D hp hg hbase
  obtain ⟨G, hG⟩ := exists_local_derivative_limit k a J f ft FR D hp hg
  exact ⟨G, local_improper_differentiation k a J hJ f ft FR D G hp hG hbase⟩

theorem single_base_point_improper_differentiation_of_convergence :
    Specs.SingleVariableAnalysis.Ch14.LocalUniform.singleBasePointDifferentiation := by
  intro k a J hJ hinterval f ft FR D hp hg hbase
  obtain ⟨G, hG⟩ := exists_local_derivative_limit k a J f ft FR D hp hg
  exact ⟨G, single_base_point_improper_differentiation
    k a J hJ hinterval f ft FR D G hp hG hbase⟩

end SingleVariableAnalysis.Riemann.Improper
