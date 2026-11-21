import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.CommutingFieldsConverse
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.CommutingFields

namespace SmoothManifolds.CommutingFields

open ModelData AtlasData MapData TangentData TangentBundleData VectorFieldData LieBracketData
  IntegralCurveData MaximalFlowData BracketFlowData CommutingFieldsData Set Filter
open scoped Topology

universe u

private theorem pullbackGerm_of_eq {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (f : M → M) (q p : M) (hbase : f q = p)
    (hf : ManifoldSmoothAt S.smoothStructure.val S.smoothStructure.val f q)
    (h : SmoothGerm S p) (r : M → ℝ) (hr : Germ.ofFun r = h.val) :
    ∃ k : SmoothGerm S q, Germ.ofFun (r ∘ f) = k.val := by
  subst p
  exact ⟨BracketFromFlow.localGermPullback S S f q hf h,
    (BracketFromFlow.localGermPullback_rep S S f q hf h r hr).symm⟩

private theorem integralCurve_scalar_at_zero {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (Y : SmoothField B) {I : Set ℝ} (hI : IsOpen I) (γ : ℝ → M)
    (hγ : IsIntegralCurveOn Y I γ) (h0 : 0 ∈ I) (q : M) (hq : γ 0 = q)
    (g : SmoothGerm S q) (r : M → ℝ) (hr : Germ.ofFun r = g.val) :
    HasDerivAt (r ∘ γ) ((Y.val q).val g) 0 := by
  subst q
  exact integralCurve_scalar_hasDerivAt S B Y hI γ hγ 0 h0 g r hr

/-- Commuting local flows preserve the other field under inverse-time pullback. -/
private theorem pullback_eventually_eq_of_commute_near {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X Y : SmoothField B) (F G : CurveFamily M)
    (hF : IsMaximalFamily X F) (hG : IsMaximalFamily Y G)
    (p : M) (hcomm : CommuteNear F G p) :
    ∀ᶠ s in 𝓝 (0 : ℝ), pullback F Y.val s p = Y.val p := by
  obtain ⟨ε, hε, U, hU, hpU, hbox⟩ := hcomm
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have hc : ContinuousAt (F.curve p) (0 : ℝ) :=
    (hF p).2.2.1.1.continuousAt ((F.interval p).isOpen.mem_nhds (hF p).1)
  have hUevent : ∀ᶠ s in 𝓝 (0 : ℝ), F.curve p s ∈ U :=
    hc.preimage_mem_nhds (by rw [(hF p).2.1]; exact hU.mem_nhds hpU)
  filter_upwards [hUevent, isOpen_Ioo.mem_nhds h0] with s hqU hs
  let q := F.curve p s
  have hsF : s ∈ (F.interval p).carrier := (hbox p hpU s hs 0 h0).1.1
  have hinv := (BracketFromFlow.pullback_boundaryless S B X F hF).1 p s hsF
  let f : M → M := fun z => F.curve z (-s)
  have hbase : f q = p := hinv.2.1
  have hf := timeMap_smoothAt S F (-s) q
    ((MaximalFlow.domain_open_smooth S B X F hF).2 (-s, q) hinv.1)
  have hneg : -s ∈ Ioo (-ε) ε := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  apply Subtype.ext
  apply LinearMap.ext
  intro h
  obtain ⟨r, _, hr⟩ := (mem_smoothGermAlgebra_iff S p h.val).mp h.property
  obtain ⟨k, hk⟩ := pullbackGerm_of_eq S f q p hbase hf h r hr.symm
  have hspec := hinv.2.2.1 (Y.val q) h k r hr.symm hk
  have hdq := integralCurve_scalar_at_zero S B Y (G.interval q).isOpen (G.curve q)
    (hG q).2.2.1 (hG q).1 q (hG q).2.1 k (r ∘ f) hk
  have hdp := integralCurve_scalar_at_zero S B Y (G.interval p).isOpen (G.curve p)
    (hG p).2.2.1 (hG p).1 p (hG p).2.1 h r hr.symm
  have heq : (r ∘ G.curve p) =ᶠ[𝓝 (0 : ℝ)] ((r ∘ f) ∘ G.curve q) := by
    filter_upwards [isOpen_Ioo.mem_nhds h0] with t ht
    have he : G.curve (f q) t = f (G.curve q t) := (hbox q hqU (-s) hneg t ht).2
    rw [hbase] at he
    exact congrArg r he
  exact hspec.trans ((hdq.congr_of_eventuallyEq heq).unique hdp)

/-- The converse of local commutation in M06.07, at any point with a common
time and state neighborhood on which the two maximal flows commute. -/
theorem bracket_zero_of_commute_near :
    Specs.SmoothManifolds.Ch06.CommutingFieldsConverse.bracket_zero_of_commute_nearType.{u} := by
  intro n M _ S B b hb X Y F G hF hG p hcomm
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  have hpb := pullback_eventually_eq_of_commute_near S B X Y F G hF hG p hcomm
  have heq : (fun s => pullbackCoefficients B F Y.val e he (s, p)) =ᶠ[𝓝 (0 : ℝ)]
      (fun _ => coefficients B Y.val e he p) := hpb.mono fun s hs => by
    simp only [pullbackCoefficients, coefficients, dite_eq_left hp, hs]
  have hd := BracketFromFlow.derivative_zero S B b hb X Y F hF p e he hp
  have hz := (hasDerivAt_const (0 : ℝ) (coefficients B Y.val e he p)).congr_of_eventuallyEq heq
  apply (B.fiberCoordinates.equiv e he p hp).injective
  simpa only [coefficients, dite_eq_left hp, map_zero] using hd.unique hz

end SmoothManifolds.CommutingFields
