import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.BracketFromFlow
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.BoundaryTangentFlow
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.LieBracket
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.MaximalFlow
import Batteries.Tactic.OpenPrivate

/-! The derivative clauses of M06.07. The inverse differential is evaluated
at the moving point on the actual flow domain. Joint smoothness and the flow
law come from the upstream boundaryless and boundary-tangent flow theorems.
The variational equation is derived below from the integral-curve equation;
no tangency is imposed on the field being pulled back.
-/
namespace SmoothManifolds.BracketFromFlow
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  VectorFieldData LieBracketData MaximalFlowData BracketFlowData Set Filter
open scoped Topology
universe u

open private scalar_comp_at germPullbackRaw from MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential

/-- Smoothness at one point suffices to pull back the algebra of smooth germs.
This local interface applies to time maps without requiring their arbitrary
off-domain representatives to be globally smooth. -/
noncomputable def localGermPullback {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N) (p : M)
    (hf : ManifoldSmoothAt S.smoothStructure.val T.smoothStructure.val f p) :
    SmoothGerm T (f p) →ₐ[ℝ] SmoothGerm S p :=
  ((germPullbackRaw f p hf.1).comp (smoothGermAlgebra T (f p)).val).codRestrict
    (smoothGermAlgebra S p) (by
      intro h
      obtain ⟨r, hr, he⟩ := (mem_smoothGermAlgebra_iff T (f p) h.val).mp h.property
      change germPullbackRaw f p hf.1 h.val ∈ smoothGermAlgebra S p
      rw [he]
      exact Algebra.subset_adjoin ⟨r ∘ f, scalar_comp_at hf hr, rfl⟩)

theorem localGermPullback_rep {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N) (p : M)
    (hf : ManifoldSmoothAt S.smoothStructure.val T.smoothStructure.val f p)
    (h : SmoothGerm T (f p)) (r : N → ℝ) (hr : Germ.ofFun r = h.val) :
    (localGermPullback S T f p hf h).val = Germ.ofFun (r ∘ f) := by
  change germPullbackRaw f p hf.1 h.val = _
  rw [← hr]
  rfl

/-- An augmentation-preserving algebra map acts contravariantly on point
derivations. This algebraic construction does not assume any map is smooth. -/
def tangentMapOfGermHom {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (p : M) (q : N)
    (R : SmoothGerm T q →ₐ[ℝ] SmoothGerm S p)
    (hR : ∀ h, germEvaluation S p (R h) = germEvaluation T q h) :
    TangentSpace S p →ₗ[ℝ] TangentSpace T q where
  toFun v := ⟨v.val.comp R.toLinearMap, by
    intro h k
    change v.val (R (h * k)) = _
    rw [map_mul, v.property]
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, hR]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Local existence and uniqueness of the intrinsic differential. -/
theorem differentialAt_exists {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N) (p : M)
    (hf : ManifoldSmoothAt S.smoothStructure.val T.smoothStructure.val f p) :
    ∃! L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p), IsDifferential S T f p L := by
  let R := localGermPullback S T f p hf
  have hR (h : SmoothGerm T (f p)) :
      germEvaluation S p (R h) = germEvaluation T (f p) h := by
    change (germPullbackRaw f p hf.1 h.val).value = h.val.value
    induction h.val using Germ.inductionOn with | _ r => rfl
  let L := tangentMapOfGermHom S T p (f p) R hR
  have hL : IsDifferential S T f p L := by
    intro v h k r hr hk
    change v.val (R h) = v.val k
    congr 1
    exact Subtype.ext ((localGermPullback_rep S T f p hf h r hr).trans hk)
  refine ⟨L, hL, ?_⟩
  intro K hK
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  apply LinearMap.ext
  intro h
  obtain ⟨r, _, hr⟩ := (mem_smoothGermAlgebra_iff T (f p) h.val).mp h.property
  have hk : Germ.ofFun (r ∘ f) = (R h).val :=
    (localGermPullback_rep S T f p hf h r hr.symm).symm
  exact (hK v h (R h) r hr.symm hk).trans (hL v h (R h) r hr.symm hk).symm

/-- The local differential with an explicitly equal target base point. -/
theorem rebased_differentialAt_exists {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N) (p : M)
    (hf : ManifoldSmoothAt S.smoothStructure.val T.smoothStructure.val f p)
    (q : N) (hq : f p = q) :
    ∃! L : TangentSpace S p →ₗ[ℝ] TangentSpace T q,
      ∀ (v : TangentSpace S p) (h : SmoothGerm T q) (k : SmoothGerm S p)
        (r : N → ℝ), Germ.ofFun r = h.val → Germ.ofFun (r ∘ f) = k.val →
          (L v).val h = v.val k := by
  subst q
  exact differentialAt_exists S T f p hf

/-- Differentiating an actual local inverse gives inverse maps on the full
intrinsic tangent fibers. Smoothness is only needed near the relevant points. -/
theorem tangent_left_inverse_of_local_inverse
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (f g : M → M) (p : M)
    (hg : ManifoldSmoothAt S.smoothStructure.val S.smoothStructure.val g (f p))
    (hgp : g (f p) = p) (hgf : (g ∘ f) =ᶠ[𝓝 p] id)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace S (f p))
    (hL : IsDifferential S S f p L)
    (K : TangentSpace S (f p) →ₗ[ℝ] TangentSpace S p)
    (hK : ∀ (v : TangentSpace S (f p)) (h : SmoothGerm S p)
      (k : SmoothGerm S (f p)) (r : M → ℝ),
      Germ.ofFun r = h.val → Germ.ofFun (r ∘ g) = k.val →
        (K v).val h = v.val k) :
    ∀ v, K (L v) = v := by
  intro v
  apply LieBrackets.tangent_ext_global p
  intro u
  have hu : ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val u.val (g (f p)) := by
    rw [hgp]
    exact (mem_globalSmoothAlgebra_iff S _).mp u.property p
  let k : SmoothGerm S (f p) := ⟨Germ.ofFun (u.val ∘ g),
    Algebra.subset_adjoin ⟨u.val ∘ g, scalar_comp_at hg hu, rfl⟩⟩
  have hcomp : Germ.ofFun ((u.val ∘ g) ∘ f) = (globalToGerm S p u).val :=
    Germ.coe_eq.mpr (hgf.fun_comp u.val)
  exact (hK (L v) (globalToGerm S p u) k u.val rfl rfl).trans
    (hL v k (globalToGerm S p u) (u.val ∘ g) rfl hcomp)

/-- Fixing a time in a joint smooth flow gives local smoothness of the actual
time-map representative, also in ordinary boundary charts. -/
theorem timeMap_smoothAt {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (F : CurveFamily M)
    (t : ℝ) (p : M) (h : BoundaryFlowData.FlowSmoothAt S F (t, p)) :
    ManifoldSmoothAt S.smoothStructure.val S.smoothStructure.val
      (fun q => F.curve q t) p := by
  have hi : ContinuousAt (fun q : M => (t, q)) p :=
    continuousAt_const.prodMk continuousAt_id
  refine ⟨h.1.comp hi, ?_⟩
  intro e he d hd hp hfp
  obtain ⟨U, hU, hpU, G, hG, heG⟩ := h.2 e he d hd hp hfp
  refine ⟨(fun x : Euclidean n => (t, x)) ⁻¹' U,
    hU.preimage (continuous_const.prodMk continuous_id), hpU,
    (fun x => G (t, x)), ?_, ?_⟩
  · exact hG.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)
  · exact heG.comp_tendsto hi

theorem inverseTimeDifferential_spec {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (F : CurveFamily M)
    (t : ℝ) (p : M)
    (h : ∃ L, IsInverseTimeDifferential S F t p L) :
    IsInverseTimeDifferential S F t p (inverseTimeDifferential S F t p) := by
  classical
  simpa only [inverseTimeDifferential, dif_pos h] using Classical.choose_spec h

/-- The flow law places the moving point in the domain of the inverse time
map. The inverse is evaluated there, and returns the original initial point. -/
theorem reverse_time {M : Type u} (F : CurveFamily M)
    (hzero : ∀ p, 0 ∈ (F.interval p).carrier)
    (hinit : ∀ p, F.curve p 0 = p)
    (hlaw : ∀ p s, s ∈ (F.interval p).carrier →
      (F.interval (F.curve p s)).carrier = {t | s + t ∈ (F.interval p).carrier} ∧
      ∀ t, s + t ∈ (F.interval p).carrier →
        F.curve (F.curve p s) t = F.curve p (s + t))
    (p : M) (t : ℝ) (ht : t ∈ (F.interval p).carrier) :
    -t ∈ (F.interval (F.curve p t)).carrier ∧ F.curve (F.curve p t) (-t) = p := by
  have h0 : t + -t ∈ (F.interval p).carrier := by simpa using hzero p
  constructor
  · rw [(hlaw p t ht).1]
    exact h0
  · calc
      F.curve (F.curve p t) (-t) = F.curve p 0 := by
        simpa only [add_neg_cancel] using (hlaw p t ht).2 (-t) h0
      _ = p := hinit p

/-- Correctness of the chosen inverse differential from joint regularity and
the exact flow law. No derivative identity is assumed here. -/
theorem pullbackCorrect_of_flow {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (F : CurveFamily M)
    (hzero : ∀ p, 0 ∈ (F.interval p).carrier)
    (hinit : ∀ p, F.curve p 0 = p)
    (hsm : ∀ z ∈ flowDomain F, BoundaryFlowData.FlowSmoothAt S F z)
    (hlaw : ∀ p s, s ∈ (F.interval p).carrier →
      (F.interval (F.curve p s)).carrier = {t | s + t ∈ (F.interval p).carrier} ∧
      ∀ t, s + t ∈ (F.interval p).carrier →
        F.curve (F.curve p s) t = F.curve p (s + t)) : PullbackCorrect S F := by
  intro p t ht
  obtain ⟨hrev, hback⟩ := reverse_time F hzero hinit hlaw p t ht
  have hloc := timeMap_smoothAt S F (-t) (F.curve p t) (hsm (-t, F.curve p t) hrev)
  obtain ⟨L, hL, huniq⟩ := rebased_differentialAt_exists S S
    (fun q => F.curve q (-t)) (F.curve p t) hloc p hback
  have hsel := inverseTimeDifferential_spec S F t p ⟨L, hL⟩
  refine ⟨hrev, hback, hsel, ?_⟩
  intro K hK
  exact (huniq K hK).trans (huniq _ hsel).symm

/-- At zero the chosen differential acts as the identity on all smooth germs.
Testing global functions avoids any implicit identification of distinct fibers. -/
theorem pullback_zero_of_correct {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (F : CurveFamily M)
    (hzero : ∀ p, 0 ∈ (F.interval p).carrier) (hinit : ∀ p, F.curve p 0 = p)
    (hcorrect : PullbackCorrect S F) (Y : Section S) (p : M) :
    pullback F Y 0 p = Y p := by
  apply LieBrackets.tangent_ext_global p
  intro f
  have hcomp : (f.val ∘ fun q => F.curve q (-0)) = f.val := by
    funext q
    simp only [neg_zero, Function.comp_apply, hinit]
  have h := (hcorrect p 0 (hzero p)).2.2.1 (Y (F.curve p 0))
    (globalToGerm S p f) (globalToGerm S (F.curve p 0) f) f.val rfl
    (by rw [hcomp]; rfl)
  exact h.trans (by rw [hinit p])

/-- Every smooth ambient representative computes the rebased local differential,
including all normal directions at an ordinary boundary face. -/
theorem rebased_jacobian {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (f : M → M) (q p : M)
    (L : TangentSpace S q →ₗ[ℝ] TangentSpace S p)
    (hL : ∀ (v : TangentSpace S q) (h : SmoothGerm S p)
      (k : SmoothGerm S q) (r : M → ℝ),
      Germ.ofFun r = h.val → Germ.ofFun (r ∘ f) = k.val → (L v).val h = v.val k)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (d : ModelChart n a M) (hd : d ∈ S.smoothStructure.val)
    (hq : q ∈ d.source)
    (U : Set (Euclidean n)) (H : Euclidean n → Euclidean n)
    (hU : IsOpen U) (hqU : (d q).val ∈ U)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H U)
    (heH : (fun r => H (d r).val) =ᶠ[𝓝 q]
      (fun r => (e (f r)).val))
    (v : TangentSpace S q) :
    B.fiberCoordinates.equiv e he p hp (L v) =
      fderiv ℝ H (d q).val (B.fiberCoordinates.equiv d hd _ hq v) := by
  have hHd : DifferentiableAt ℝ H (d q).val :=
    (hH.contDiffAt (hU.mem_nhds hqU)).differentiableAt (by simp)
  let w := B.fiberCoordinates.equiv d hd _ hq v
  have hw : w = ∑ i, w i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  ext j
  let k := germOfChart S q d hd hq (fun x => H x j)
    ⟨U, hU, hqU, (contDiffOn_pi.mp hH) j⟩
  have hk : Germ.ofFun ((fun r => (e r).val j) ∘ f) = k.val :=
    Germ.coe_eq.mpr ((heH.fun_comp (fun x => x j)).symm)
  rw [LieBrackets.coordinates_eval e he p hp,
    hL v (coordinateGerm S p e he hp j) k _ rfl hk,
    derivation_coordinate_formula S q d hd hq v k (fun x => H x j)
      ⟨⟨U, hU, hqU, (contDiffOn_pi.mp hH) j⟩, rfl⟩]
  calc
    _ = fderiv ℝ (fun x => H x j) (d q).val
        (∑ i, w i • Pi.single i (1 : ℝ)) := by
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [← LieBrackets.coordinates_eval d hd _ hq]
    _ = _ := by rw [← hw, fderiv_apply hHd j]; rfl

/-- Every smooth ambient representative of the inverse time map computes its
intrinsic differential. The input coordinates are at the moving point, and the
output coordinates are at the original point, including at a boundary face. -/
theorem inverseTime_jacobian {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (F : CurveFamily M) (t : ℝ) (p : M)
    (L : TangentSpace S (F.curve p t) →ₗ[ℝ] TangentSpace S p)
    (hL : IsInverseTimeDifferential S F t p L)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (d : ModelChart n a M) (hd : d ∈ S.smoothStructure.val)
    (hq : F.curve p t ∈ d.source)
    (U : Set (Euclidean n)) (H : Euclidean n → Euclidean n)
    (hU : IsOpen U) (hqU : (d (F.curve p t)).val ∈ U)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H U)
    (heH : (fun r => H (d r).val) =ᶠ[𝓝 (F.curve p t)]
      (fun r => (e (F.curve r (-t))).val))
    (v : TangentSpace S (F.curve p t)) :
    B.fiberCoordinates.equiv e he p hp (L v) =
      fderiv ℝ H (d (F.curve p t)).val (B.fiberCoordinates.equiv d hd _ hq v) := by
  exact rebased_jacobian B (fun r => F.curve r (-t)) (F.curve p t) p L hL
    e he hp d hd hq U H hU hqU hH heH v

/-- A local formula for the actual pullback on a whole joint neighborhood.
The backward representative is evaluated at `(-s, forward(s,x))`. -/
theorem pullback_local_representation {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (F : CurveFamily M) (Y : Section S) (hcorrect : PullbackCorrect S F)
    (hD : IsOpen (flowDomain F)) (t : ℝ) (p : M)
    (ht : t ∈ (F.interval p).carrier) (hsm : BoundaryFlowData.FlowSmoothAt S F (t, p))
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (d : ModelChart n a M) (hd : d ∈ S.smoothStructure.val)
    (hq : F.curve p t ∈ d.source)
    (G : ℝ × Euclidean n → Euclidean n)
    (heG : (fun w : ℝ × M => G (w.1, (e w.2).val)) =ᶠ[𝓝 (t, p)]
      (fun w => (d (flow F w)).val))
    (V : Set (ℝ × Euclidean n)) (H : ℝ × Euclidean n → Euclidean n)
    (hV : IsOpen V) (hqV : (-t, (d (F.curve p t)).val) ∈ V)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H V)
    (heH : (fun w : ℝ × M => H (w.1, (d w.2).val)) =ᶠ[𝓝 (-t, F.curve p t)]
      (fun w => (e (flow F w)).val))
    (W : Euclidean n → Euclidean n)
    (heW : (fun q => W (d q).val) =ᶠ[𝓝 (F.curve p t)] (coefficients B Y d hd)) :
    pullbackCoefficients B F Y e he =ᶠ[𝓝 (t, p)]
      (fun z => fderiv ℝ H (-z.1, G (z.1, (e z.2).val))
        (0, W (G (z.1, (e z.2).val)))) := by
  have hi : ContinuousAt (fun z : ℝ × M => (-z.1, flow F z)) (t, p) :=
    continuousAt_fst.neg.prodMk hsm.1
  have hc : ContinuousAt (fun z : ℝ × M => (-z.1, (d (flow F z)).val)) (t, p) :=
    continuousAt_fst.neg.prodMk
      (continuous_subtype_val.continuousAt.comp ((d.continuousAt hq).comp (f := flow F) hsm.1))
  have hEqNear := hi.eventually (eventually_eventually_nhds.mpr heH)
  filter_upwards [hD.mem_nhds ht, heG, hEqNear,
    hc.preimage_mem_nhds (hV.mem_nhds hqV), heW.comp_tendsto hsm.1,
    continuousAt_snd.preimage_mem_nhds (e.open_source.mem_nhds hp),
    hsm.1.preimage_mem_nhds (d.open_source.mem_nhds hq)] with z hz hzG hzH hzV hzW hze hzd
  have hzHEq : (fun w : ℝ × M => H (w.1, (d w.2).val)) =ᶠ[𝓝 (-z.1, flow F z)]
      (fun w => (e (flow F w)).val) := hzH
  have hslice : (fun r => H (-z.1, (d r).val)) =ᶠ[𝓝 (flow F z)]
      (fun r => (e (F.curve r (-z.1))).val) :=
    hzHEq.comp_tendsto
      (continuousAt_const.prodMk continuousAt_id :
        ContinuousAt (fun r : M => (-z.1, r)) (flow F z))
  have hHslice : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => H (-z.1, x))
      ((fun x => (-z.1, x)) ⁻¹' V) :=
    hH.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)
  have hJac := inverseTime_jacobian B F z.1 z.2 _ (hcorrect z.2 z.1 hz).2.2.1
    e he hze d hd hzd _ (fun x => H (-z.1, x))
    (hV.preimage (continuous_const.prodMk continuous_id)) hzV hHslice hslice (Y (flow F z))
  have hDiff :=
    ((hH.contDiffAt (hV.mem_nhds hzV)).differentiableAt (by simp)).hasFDerivAt.comp
      (d (flow F z)).val
      ((hasFDerivAt_const (-z.1) (d (flow F z)).val).prodMk
        (hasFDerivAt_id (d (flow F z)).val))
  simp only [Function.comp_def, flow] at hDiff hJac
  rw [hDiff.fderiv] at hJac
  change coefficients B (pullback F Y z.1) e he z.2 = _
  rw [LieBrackets.coefficients_eq _ e he z.2 hze]
  change B.fiberCoordinates.equiv e he z.2 hze
    (inverseTimeDifferential S F z.1 z.2 (Y (F.curve z.2 z.1))) = _
  rw [hJac]
  change fderiv ℝ H (-z.1, (d (flow F z)).val)
    (0, B.fiberCoordinates.equiv d hd (flow F z) hzd (Y (flow F z))) = _
  simp only [Function.comp_def] at hzW hzG
  rw [← LieBrackets.coefficients_eq Y d hd (flow F z) hzd, ← hzW, ← hzG]

/-- The joint local formula has a smooth ambient extension. This proves
regularity up to the boundary for arbitrary Y, without assuming Y is tangent. -/
theorem pullbackSmoothAt_of_flow {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (F : CurveFamily M) (hcorrect : PullbackCorrect S F)
    (hD : IsOpen (flowDomain F))
    (hsm : ∀ z ∈ flowDomain F, BoundaryFlowData.FlowSmoothAt S F z)
    (Y : SmoothField B) (t : ℝ) (p : M) (ht : t ∈ (F.interval p).carrier) :
    PullbackSmoothAt B F Y.val (t, p) := by
  intro e he hp
  obtain ⟨d, hd, hq⟩ := S.smoothStructure.property.1.1 (F.curve p t)
  obtain ⟨U, hU, hpU, G, hG, heG⟩ := (hsm (t, p) ht).2 e he d hd hp hq
  have hrev := hcorrect p t ht
  have hback : flow F (-t, F.curve p t) ∈ e.source := by
    simpa only [flow, hrev.2.1] using hp
  obtain ⟨V, hV, hqV, H, hH, heH⟩ :=
    (hsm (-t, F.curve p t) hrev.1).2 d hd e he hq hback
  obtain ⟨W, hW, hqW, K, hK, heK⟩ :=
    LieBrackets.smooth_field_regular Y d hd (F.curve p t) hq
  have hrepr := pullback_local_representation B F Y.val hcorrect hD t p ht
    (hsm (t, p) ht) e he hp d hd hq G heG V H hV hqV hH heH K heK
  have hGc : G (t, (e p).val) = (d (F.curve p t)).val := heG.self_of_nhds
  have hGcAt : ContinuousAt G (t, (e p).val) :=
    (hG.contDiffAt (hU.mem_nhds hpU)).continuousAt
  have hinner : ContinuousAt (fun z : ℝ × Euclidean n => (-z.1, G z)) (t, (e p).val) :=
    continuousAt_fst.neg.prodMk hGcAt
  have hcenterV : (-t, G (t, (e p).val)) ∈ V := by simpa only [hGc] using hqV
  have hcenterW : G (t, (e p).val) ∈ W := by simpa only [hGc] using hqW
  have hnear : ∀ᶠ z in 𝓝 (t, (e p).val), z ∈ U ∧ (-z.1, G z) ∈ V ∧ G z ∈ W := by
    filter_upwards [hU.mem_nhds hpU,
      hinner.preimage_mem_nhds (hV.mem_nhds hcenterV),
      hGcAt.preimage_mem_nhds (hW.mem_nhds hcenterW)] with z hzU hzV hzW
    exact ⟨hzU, hzV, hzW⟩
  obtain ⟨R, hRsub, hR, hpR⟩ := mem_nhds_iff.mp hnear
  have hGR : ContDiffOn ℝ (⊤ : ℕ∞) G R := hG.mono (fun z hz => (hRsub hz).1)
  have hIR : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × Euclidean n => (-z.1, G z)) R :=
    contDiffOn_fst.neg.prodMk hGR
  have hHR : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × Euclidean n =>
      fderiv ℝ H (-z.1, G z)) R :=
    (hH.fderiv_of_isOpen hV (by simp)).comp hIR (fun z hz => (hRsub hz).2.1)
  have hKR : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => K (G z)) R :=
    hK.comp hGR (fun z hz => (hRsub hz).2.2)
  refine ⟨R, hR, hpR, (fun z => fderiv ℝ H (-z.1, G z) (0, K (G z))), ?_, hrepr.symm⟩
  exact hHR.clm_apply (contDiffOn_const.prodMk hKR)

/-- A local inverse identity determines inverse ambient Jacobians, also when
the chart is a relatively open half-space chart. -/
theorem jacobian_left_inverse {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (e : ModelChart n a M) (p : M) (hp : p ∈ e.source)
    (G H : Euclidean n → Euclidean n) (A K : Euclidean n →L[ℝ] Euclidean n)
    (hG : HasFDerivAt G A (e p).val) (hH : HasFDerivAt H K (G (e p).val))
    (hcomp : (fun r => H (G (e r).val)) =ᶠ[𝓝 p] (fun r => (e r).val)) :
    K.comp A = ContinuousLinearMap.id ℝ (Euclidean n) :=
  FiniteRegularity.extension_independence e (fun r => (e r).val) p hp _ _
    ⟨H ∘ G, hH.comp (e p).val hG, hcomp⟩
    ⟨id, hasFDerivAt_id (e p).val, Eventually.of_forall (fun _ => rfl)⟩

/-- Jacobians of forward and reverse flow representatives are inverse. The
proof differentiates the actual domain-restricted flow law, not a presumed
matrix inverse identity. -/
theorem flow_jacobians_inverse {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (F : CurveFamily M)
    (hzero : ∀ p, 0 ∈ (F.interval p).carrier) (hinit : ∀ p, F.curve p 0 = p)
    (hlaw : ∀ p s, s ∈ (F.interval p).carrier →
      (F.interval (F.curve p s)).carrier = {t | s + t ∈ (F.interval p).carrier} ∧
      ∀ t, s + t ∈ (F.interval p).carrier →
        F.curve (F.curve p s) t = F.curve p (s + t))
    (hD : IsOpen (flowDomain F)) (t : ℝ) (p : M)
    (ht : t ∈ (F.interval p).carrier) (hsm : BoundaryFlowData.FlowSmoothAt S F (t, p))
    (e : ModelChart n a M) (hp : p ∈ e.source)
    (d : ModelChart n a M) (hq : F.curve p t ∈ d.source)
    (G H : ℝ × Euclidean n → Euclidean n)
    (hG : DifferentiableAt ℝ G (t, (e p).val))
    (hH : DifferentiableAt ℝ H (-t, (d (F.curve p t)).val))
    (heG : (fun w : ℝ × M => G (w.1, (e w.2).val)) =ᶠ[𝓝 (t, p)]
      (fun w => (d (flow F w)).val))
    (heH : (fun w : ℝ × M => H (w.1, (d w.2).val)) =ᶠ[𝓝 (-t, F.curve p t)]
      (fun w => (e (flow F w)).val)) :
    ((fderiv ℝ H (-t, G (t, (e p).val))).comp (ContinuousLinearMap.inr ℝ ℝ (Euclidean n))).comp
      ((fderiv ℝ G (t, (e p).val)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclidean n))) =
        ContinuousLinearMap.id ℝ (Euclidean n) := by
  have hi : ContinuousAt (fun q : M => (t, q)) p :=
    continuousAt_const.prodMk continuousAt_id
  have hf : ContinuousAt (fun q => F.curve q t) p := hsm.1.comp hi
  have hforward := heG.comp_tendsto hi
  have hback : (fun r => H (-t, (d r).val)) =ᶠ[𝓝 (F.curve p t)]
      (fun r => (e (F.curve r (-t))).val) :=
    heH.comp_tendsto
      (continuousAt_const.prodMk continuousAt_id : ContinuousAt (fun r : M => (-t, r)) _)
  have hcomp : (fun r => H (-t, G (t, (e r).val))) =ᶠ[𝓝 p] (fun r => (e r).val) := by
    filter_upwards [hforward, hback.comp_tendsto hf,
      hi.preimage_mem_nhds (hD.mem_nhds ht)] with r hrG hrH hrD
    simp only [Function.comp_def, flow] at hrG hrH
    rw [hrG, hrH, (reverse_time F hzero hinit hlaw r t hrD).2]
  have hGc : G (t, (e p).val) = (d (F.curve p t)).val := heG.self_of_nhds
  have hGs := hG.hasFDerivAt.comp (e p).val
    ((hasFDerivAt_const t (e p).val).prodMk (hasFDerivAt_id (e p).val))
  have hHs := hH.hasFDerivAt.comp (d (F.curve p t)).val
    ((hasFDerivAt_const (-t) (d (F.curve p t)).val).prodMk
      (hasFDerivAt_id (d (F.curve p t)).val))
  have hHslice : HasFDerivAt (fun y => H (-t, y))
      ((fderiv ℝ H (-t, G (t, (e p).val))).comp
        (ContinuousLinearMap.inr ℝ ℝ (Euclidean n))) (G (t, (e p).val)) := by
    rw [hGc]
    convert hHs using 1 <;> first | rfl | (ext v; rfl)
  apply jacobian_left_inverse e p hp (fun x => G (t, x)) (fun x => H (-t, x)) _ _ _ hHslice hcomp
  convert hGs using 1 <;> first | rfl | (ext v; rfl)

/-- Tangency is vacuous for the Euclidean ordinary model, without restricting
the dimension or requiring the manifold to be nonempty. -/
theorem euclidean_tangent {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    (X : SmoothField B) : BoundaryFlowData.IsTangentToBoundary X := by
  intro p hp
  obtain ⟨e, he, hpe, hface⟩ := hp
  exact False.elim hface

/-- Differentiating a pair of inverse operator paths and applying the product
rule. The inverse relation is required on a neighborhood of the time in
question; an isolated inverse at that time would not determine its derivative.
This is the analytic calculation behind the bracket-from-flow identity. -/
theorem inverse_path_apply_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A K : ℝ → E →L[ℝ] E) (V : ℝ → E) (t : ℝ)
    (A' K' : E →L[ℝ] E) (V' : E)
    (hA : HasDerivAt A A' t) (hK : HasDerivAt K K' t)
    (hV : HasDerivAt V V' t)
    (hKA : (fun s => (K s).comp (A s)) =ᶠ[𝓝 t]
      (fun _ => ContinuousLinearMap.id ℝ E))
    (hAK : (A t).comp (K t) = ContinuousLinearMap.id ℝ E) :
    HasDerivAt (fun s => K s (V s))
      (K t (V' - A' (K t (V t)))) t := by
  have hzero : K'.comp (A t) + (K t).comp A' = 0 :=
    ((hK.clm_comp hA).congr_of_eventuallyEq hKA.symm).unique (hasDerivAt_const t _)
  have hz := congrArg (fun L : E →L[ℝ] E => L (K t (V t))) hzero
  have hAKv : A t (K t (V t)) = V t :=
    congrArg (fun L : E →L[ℝ] E => L (V t)) hAK
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, hAKv] at hz
  convert hK.clm_apply hV using 1
  rw [map_sub]
  exact (sub_eq_add_neg _ _).trans (by
    rw [← eq_neg_of_add_eq_zero_left hz]
    exact add_comm _ _)

/-- With the variational equation A'=DX∘A and V'=DY·X, the preceding rule is
exactly K(DY·X-DX·Y). These are explicit hypotheses of this local analytic
lemma; the manifold theorem must still derive them from its actual flow. -/
theorem pullback_path_bracket_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A K : ℝ → E →L[ℝ] E) (V : ℝ → E) (t : ℝ)
    (DX DY : E →L[ℝ] E) (x : E) (K' : E →L[ℝ] E)
    (hA : HasDerivAt A (DX.comp (A t)) t)
    (hK : HasDerivAt K K' t) (hV : HasDerivAt V (DY x) t)
    (hKA : (fun s => (K s).comp (A s)) =ᶠ[𝓝 t]
      (fun _ => ContinuousLinearMap.id ℝ E))
    (hAK : (A t).comp (K t) = ContinuousLinearMap.id ℝ E) :
    HasDerivAt (fun s => K s (V s)) (K t (DY x - DX (V t))) t := by
  have h := inverse_path_apply_derivative A K V t _ K' (DY x) hA hK hV hKA hAK
  have hAKv : A t (K t (V t)) = V t :=
    congrArg (fun L : E →L[ℝ] E => L (V t)) hAK
  simpa only [ContinuousLinearMap.comp_apply, hAKv] using h

/-- Equality of the time derivative of the state Jacobian and the state
derivative of the time velocity. This is Schwarz symmetry for a smooth local
flow representative, without an ODE or a global flow assumption. -/
theorem time_derivative_state_jacobian
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : ℝ × E → F) (t : ℝ) (x : E)
    (hΦ : ContDiffAt ℝ 2 Φ (t, x)) :
    HasDerivAt
      (fun s => (fderiv ℝ Φ (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E))
      (fderiv ℝ (fun y => fderiv ℝ Φ (t, y) (1, 0)) x) t := by
  have hD : DifferentiableAt ℝ (fderiv ℝ Φ) (t, x) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have ht := hD.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hpath := ht.clm_comp
    (hasDerivAt_const t (ContinuousLinearMap.inr ℝ ℝ E))
  have hs := hD.hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  have hv := hs.clm_apply (hasFDerivAt_const (1, (0 : E)) x)
  simp only [Function.comp_def] at hv hpath
  have hsym := hΦ.isSymmSndFDerivAt (by norm_num)
  convert hpath using 1
  · rfl
  · rw [hv.fderiv]
    ext v
    simpa using hsym.eq (0, v) (1, 0)

/-- The time velocity of every joint ambient flow representative agrees near
the initial state with the actual field at the moving state. The comparison
uses the ODE on each state's two-sided maximal interval, also at the boundary. -/
theorem flow_velocity_in_coordinates {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (X : SmoothField B) (F : CurveFamily M)
    (hF : BoundaryFlowData.IsMaximalFamily X F)
    (hD : IsOpen (flowDomain F))
    (hsm : ∀ z ∈ flowDomain F, BoundaryFlowData.FlowSmoothAt S F z)
    (t : ℝ) (p : M) (ht : t ∈ (F.interval p).carrier)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (d : ModelChart n a M) (hd : d ∈ S.smoothStructure.val)
    (hq : F.curve p t ∈ d.source)
    (U : Set (ℝ × Euclidean n)) (G : ℝ × Euclidean n → Euclidean n)
    (hU : IsOpen U) (hpU : (t, (e p).val) ∈ U)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (heG : (fun w : ℝ × M => G (w.1, (e w.2).val)) =ᶠ[𝓝 (t, p)]
      (fun w => (d (flow F w)).val)) :
    (fun q => fderiv ℝ G (t, (e q).val) (1, 0)) =ᶠ[𝓝 p]
      (fun q => coefficients B X.val d hd (F.curve q t)) := by
  have hi : ContinuousAt (fun q : M => (t, q)) p :=
    continuousAt_const.prodMk continuousAt_id
  have hf : ContinuousAt (fun q => F.curve q t) p :=
    (timeMap_smoothAt S F t p (hsm (t, p) ht)).1
  have hcoord : ContinuousAt (fun q => (t, (e q).val)) p :=
    continuousAt_const.prodMk
      (continuous_subtype_val.continuousAt.comp (e.continuousAt hp))
  have heGnear : ∀ᶠ q in 𝓝 p,
      (fun w : ℝ × M => G (w.1, (e w.2).val)) =ᶠ[𝓝 (t, q)]
        (fun w => (d (flow F w)).val) :=
    hi.eventually (eventually_eventually_nhds.mpr heG)
  filter_upwards [heGnear, hi.preimage_mem_nhds (hD.mem_nhds ht),
    hf.preimage_mem_nhds (d.open_source.mem_nhds hq),
    hcoord.preimage_mem_nhds (hU.mem_nhds hpU)] with q hEq hqt hqd hqU
  have hs : ContinuousAt (fun s : ℝ => (s, q)) t :=
    continuousAt_id.prodMk continuousAt_const
  have hEqSlice := hEq.comp_tendsto hs
  have hvel :=
    ((hG.contDiffAt (hU.mem_nhds hqU)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t (e q).val))
  have hode := ((hF q).2.2.1).2 t hqt d hd hqd
  rw [LieBrackets.coefficients_eq X.val d hd (F.curve q t) hqd]
  exact (hvel.congr_of_eventuallyEq hEqSlice.symm).unique hode.2

/-- A coordinate velocity identity on the manifold determines the full ambient
state derivative. In particular it determines normal columns at the boundary:
the upstream extension-independence theorem applies to the entire half-space,
rather than to boundary-tangent directions alone. -/
theorem state_jacobian_variation_of_velocity
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n a M) (p : M) (hp : p ∈ e.source)
    (G : ℝ × Euclidean n → Euclidean n) (H : Euclidean n → Euclidean n)
    (t : ℝ) (hG : ContDiffAt ℝ 2 G (t, (e p).val))
    (hH : DifferentiableAt ℝ H (G (t, (e p).val)))
    (hvel : (fun q => fderiv ℝ G (t, (e q).val) (1, 0)) =ᶠ[𝓝 p]
      (fun q => H (G (t, (e q).val)))) :
    HasDerivAt
      (fun s => (fderiv ℝ G (s, (e p).val)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclidean n)))
      ((fderiv ℝ H (G (t, (e p).val))).comp
        ((fderiv ℝ G (t, (e p).val)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclidean n)))) t := by
  have hD : DifferentiableAt ℝ (fderiv ℝ G) (t, (e p).val) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hs := hD.hasFDerivAt.comp (e p).val
    ((hasFDerivAt_const t (e p).val).prodMk (hasFDerivAt_id (e p).val))
  have hv := hs.clm_apply (hasFDerivAt_const (1, (0 : Euclidean n)) (e p).val)
  have hGs := (hG.differentiableAt (by norm_num)).hasFDerivAt.comp (e p).val
    ((hasFDerivAt_const t (e p).val).prodMk (hasFDerivAt_id (e p).val))
  have hHs := hH.hasFDerivAt.comp (e p).val hGs
  simp only [Function.comp_def] at hv hHs
  have hsame := FiniteRegularity.extension_independence e
    (fun q => H (G (t, (e q).val))) p hp _ _
    ⟨_, hv, hvel⟩ ⟨_, hHs, Eventually.of_forall (fun _ => rfl)⟩
  have hderiv : fderiv ℝ (fun y => fderiv ℝ G (t, y) (1, 0)) (e p).val =
      (fderiv ℝ H (G (t, (e p).val))).comp
        ((fderiv ℝ G (t, (e p).val)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclidean n))) := by
    rw [hv.fderiv]
    convert hsame using 1 <;> ext v <;> rfl
  exact (time_derivative_state_jacobian G t (e p).val hG).congr_deriv hderiv

/-- The actual forward flow satisfies the full variational equation in every
ambient chart representative. H is any smooth extension of X's coefficients
near the moving point; no variational equation is assumed. -/
theorem flow_state_jacobian_variation {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (X : SmoothField B) (F : CurveFamily M)
    (hF : BoundaryFlowData.IsMaximalFamily X F)
    (hD : IsOpen (flowDomain F))
    (hsm : ∀ z ∈ flowDomain F, BoundaryFlowData.FlowSmoothAt S F z)
    (t : ℝ) (p : M) (ht : t ∈ (F.interval p).carrier)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (d : ModelChart n a M) (hd : d ∈ S.smoothStructure.val)
    (hq : F.curve p t ∈ d.source)
    (U : Set (ℝ × Euclidean n)) (G : ℝ × Euclidean n → Euclidean n)
    (hU : IsOpen U) (hpU : (t, (e p).val) ∈ U)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (heG : (fun w : ℝ × M => G (w.1, (e w.2).val)) =ᶠ[𝓝 (t, p)]
      (fun w => (d (flow F w)).val))
    (V : Set (Euclidean n)) (H : Euclidean n → Euclidean n)
    (hV : IsOpen V) (hqV : (d (F.curve p t)).val ∈ V)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H V)
    (heH : (fun q => H (d q).val) =ᶠ[𝓝 (F.curve p t)] (coefficients B X.val d hd)) :
    HasDerivAt
      (fun s => (fderiv ℝ G (s, (e p).val)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclidean n)))
      ((fderiv ℝ H (d (F.curve p t)).val).comp
        ((fderiv ℝ G (t, (e p).val)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclidean n)))) t := by
  have hGc : G (t, (e p).val) = (d (F.curve p t)).val := heG.self_of_nhds
  have hf := (timeMap_smoothAt S F t p (hsm (t, p) ht)).1
  have hi : ContinuousAt (fun q : M => (t, q)) p :=
    continuousAt_const.prodMk continuousAt_id
  have hEq := heG.comp_tendsto hi
  have hvel := flow_velocity_in_coordinates B X F hF hD hsm t p ht e he hp d hd hq
    U G hU hpU hG heG
  have hvelocity : (fun q => fderiv ℝ G (t, (e q).val) (1, 0)) =ᶠ[𝓝 p]
      (fun q => H (G (t, (e q).val))) := by
    filter_upwards [hvel, hEq, heH.comp_tendsto hf] with q hqv hqG hqH
    exact hqv.trans (hqH.symm.trans (congrArg H hqG.symm))
  have hHdiff : DifferentiableAt ℝ H (G (t, (e p).val)) := by
    rw [hGc]
    exact (hH.contDiffAt (hV.mem_nhds hqV)).differentiableAt (by simp)
  have h := state_jacobian_variation_of_velocity e p hp G H t
    ((hG.contDiffAt (hU.mem_nhds hpU)).of_le (by simp)) hHdiff hvelocity
  simpa only [hGc] using h

/-- The derivative identity for an actual smooth two-sided flow on either
ordinary model. All extra premises here are flow properties proved upstream;
there is no tangency premise on Y and no assumed variational equation. -/
theorem derivative_at_time_of_flow {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B) (hb : BracketOperation b)
    (X Y : SmoothField B) (F : CurveFamily M)
    (hF : BoundaryFlowData.IsMaximalFamily X F)
    (hD : IsOpen (flowDomain F))
    (hsm : ∀ z ∈ flowDomain F, BoundaryFlowData.FlowSmoothAt S F z)
    (hlaw : ∀ p s, s ∈ (F.interval p).carrier →
      (F.interval (F.curve p s)).carrier = {t | s + t ∈ (F.interval p).carrier} ∧
      ∀ t, s + t ∈ (F.interval p).carrier →
        F.curve (F.curve p s) t = F.curve p (s + t))
    (hcorrect : PullbackCorrect S F)
    (p : M) (t : ℝ) (ht : t ∈ (F.interval p).carrier) :
    HasPullbackTimeDerivative B F Y.val (pullback F (b X Y).val t) p t := by
  intro e he hp
  obtain ⟨d, hd, hq⟩ := S.smoothStructure.property.1.1 (F.curve p t)
  obtain ⟨U, hU, hpU, G, hG, heG⟩ := (hsm (t, p) ht).2 e he d hd hp hq
  have hrev := hcorrect p t ht
  have hback : flow F (-t, F.curve p t) ∈ e.source := by
    simpa only [flow, hrev.2.1] using hp
  obtain ⟨V, hV, hqV, H, hH, heH⟩ :=
    (hsm (-t, F.curve p t) hrev.1).2 d hd e he hq hback
  obtain ⟨UX, hUX, hqX, CX, hCX, heCX⟩ :=
    LieBrackets.smooth_field_regular X d hd (F.curve p t) hq
  obtain ⟨UY, hUY, hqY, CY, hCY, heCY⟩ :=
    LieBrackets.smooth_field_regular Y d hd (F.curve p t) hq
  let I : Euclidean n →L[ℝ] ℝ × Euclidean n := ContinuousLinearMap.inr ℝ ℝ (Euclidean n)
  let A (s : ℝ) := (fderiv ℝ G (s, (e p).val)).comp I
  let K (s : ℝ) := (fderiv ℝ H (-s, G (s, (e p).val))).comp I
  let v (s : ℝ) := CY (G (s, (e p).val))
  have hGc : G (t, (e p).val) = (d (F.curve p t)).val := heG.self_of_nhds
  have hXdiff := (hCX.contDiffAt (hUX.mem_nhds hqX)).differentiableAt (by simp)
  have hYdiff := (hCY.contDiffAt (hUY.mem_nhds hqY)).differentiableAt (by simp)
  have hAd : HasDerivAt A ((fderiv ℝ CX (d (F.curve p t)).val).comp (A t)) t :=
    flow_state_jacobian_variation B X F hF hD hsm t p ht e he hp d hd hq U G hU hpU hG heG
      UX CX hUX hqX hCX heCX
  have hvel := (flow_velocity_in_coordinates B X F hF hD hsm t p ht e he hp d hd hq
    U G hU hpU hG heG).self_of_nhds
  have hGp : HasDerivAt (fun s => G (s, (e p).val))
      (coefficients B X.val d hd (F.curve p t)) t := by
    have h := ((hG.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t (e p).val))
    exact h.congr_deriv hvel
  have hYat : DifferentiableAt ℝ CY (G (t, (e p).val)) := hGc.symm ▸ hYdiff
  have hv : HasDerivAt v
      (fderiv ℝ CY (d (F.curve p t)).val (coefficients B X.val d hd (F.curve p t))) t := by
    simpa only [v, hGc, Function.comp_def] using hYat.hasFDerivAt.comp_hasDerivAt t hGp
  have hHD : DifferentiableAt ℝ (fderiv ℝ H) (-t, G (t, (e p).val)) := by
    rw [hGc]
    exact ((hH.contDiffAt (hV.mem_nhds hqV)).fderiv_right (m := 1) (by simp)).differentiableAt one_ne_zero
  have hKd : DifferentiableAt ℝ K t := by
    exact (hHD.comp t ((differentiableAt_id.neg).prodMk hGp.differentiableAt)).clm_comp
      (differentiableAt_const I)
  have hi : ContinuousAt (fun s : ℝ => (s, p)) t := continuousAt_id.prodMk continuousAt_const
  have hcurve : ContinuousAt (F.curve p) t :=
    (hsm (t, p) ht).1.comp (f := fun s : ℝ => (s, p)) hi
  have hmove : ContinuousAt (fun s => (-s, F.curve p s)) t :=
    continuousAt_id.neg.prodMk hcurve
  have hcoords : ContinuousAt (fun s => (-s, (d (F.curve p s)).val)) t :=
    continuousAt_id.neg.prodMk
      (continuous_subtype_val.continuousAt.comp ((d.continuousAt hq).comp hcurve))
  have heGnear := hi.eventually (eventually_eventually_nhds.mpr heG)
  have heHnear := hmove.eventually (eventually_eventually_nhds.mpr heH)
  have hKA : (fun s => (K s).comp (A s)) =ᶠ[𝓝 t]
      (fun _ => ContinuousLinearMap.id ℝ (Euclidean n)) := by
    filter_upwards [heGnear, heHnear,
      hi.preimage_mem_nhds (hD.mem_nhds ht),
      (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (hU.mem_nhds hpU),
      hcoords.preimage_mem_nhds (hV.mem_nhds hqV),
      hcurve.preimage_mem_nhds (d.open_source.mem_nhds hq)] with s hsG hsH hsD hsU hsV hsd
    exact flow_jacobians_inverse F (fun q => (hF q).1) (fun q => (hF q).2.1)
      hlaw hD s p hsD (hsm (s, p) hsD) e hp d hsd G H
      ((hG.contDiffAt (hU.mem_nhds hsU)).differentiableAt (by simp))
      ((hH.contDiffAt (hV.mem_nhds hsV)).differentiableAt (by simp)) hsG hsH
  have hAK : (A t).comp (K t) = ContinuousLinearMap.id ℝ (Euclidean n) := by
    have hlin : (K t).toLinearMap.comp (A t).toLinearMap = LinearMap.id :=
      congrArg ContinuousLinearMap.toLinearMap hKA.self_of_nhds
    have hcomm := (LinearMap.comp_eq_id_comm ℝ (Euclidean n)).mp hlin
    apply ContinuousLinearMap.ext
    intro w
    exact LinearMap.congr_fun hcomm w
  have hcalc := pullback_path_bracket_derivative A K v t
    (fderiv ℝ CX (d (F.curve p t)).val) (fderiv ℝ CY (d (F.curve p t)).val)
    (coefficients B X.val d hd (F.curve p t)) (deriv K t) hAd hKd.hasDerivAt hv hKA hAK
  have hrepr := pullback_local_representation B F Y.val hcorrect hD t p ht
    (hsm (t, p) ht) e he hp d hd hq G heG V H hV hqV hH heH CY heCY
  have htime : (fun s => pullbackCoefficients B F Y.val e he (s, p)) =ᶠ[𝓝 t]
      (fun s => K s (v s)) := by
    simpa only [Function.comp_def, K, v, I, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply] using hrepr.comp_tendsto hi
  have hbc := (LieBrackets.bracket_coordinates S B b hb X Y).2 d hd (F.curve p t) hq
    (fderiv ℝ CX (d (F.curve p t)).val) (fderiv ℝ CY (d (F.curve p t)).val)
    ⟨CX, hXdiff.hasFDerivAt, heCX⟩ ⟨CY, hYdiff.hasFDerivAt, heCY⟩
  have hbracket : coefficients B (b X Y).val d hd (F.curve p t) =
      fderiv ℝ CY (d (F.curve p t)).val (coefficients B X.val d hd (F.curve p t)) -
        fderiv ℝ CX (d (F.curve p t)).val (v t) := by
    have hvval : v t = coefficients B Y.val d hd (F.curve p t) := by
      simpa only [v, hGc] using heCY.self_of_nhds
    rw [hvval]
    ext j
    exact (hbc j).trans (LieBrackets.coordinate_commutator_sum _ _ _ _ j).symm
  have hHslice : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => H (-t, x))
      ((fun x => (-t, x)) ⁻¹' V) :=
    hH.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)
  have hHsEq : (fun r => H (-t, (d r).val)) =ᶠ[𝓝 (F.curve p t)]
      (fun r => (e (F.curve r (-t))).val) :=
    heH.comp_tendsto
      (continuousAt_const.prodMk continuousAt_id : ContinuousAt (fun r : M => (-t, r)) _)
  have hZ := inverseTime_jacobian B F t p _ hrev.2.2.1 e he hp d hd hq _ (fun x => H (-t, x))
    (hV.preimage (continuous_const.prodMk continuous_id)) hqV hHslice hHsEq ((b X Y).val (F.curve p t))
  have hHs := ((hH.contDiffAt (hV.mem_nhds hqV)).differentiableAt (by simp)).hasFDerivAt.comp
    (d (F.curve p t)).val
    ((hasFDerivAt_const (-t) (d (F.curve p t)).val).prodMk (hasFDerivAt_id (d (F.curve p t)).val))
  simp only [Function.comp_def] at hHs
  rw [hHs.fderiv] at hZ
  have hZvalue : coefficients B (pullback F (b X Y).val t) e he p =
      K t (coefficients B (b X Y).val d hd (F.curve p t)) := by
    rw [LieBrackets.coefficients_eq _ e he p hp,
      LieBrackets.coefficients_eq _ d hd (F.curve p t) hq]
    simpa [pullback, K, I, hGc] using hZ
  rw [hZvalue, hbracket]
  exact hcalc.congr_of_eventuallyEq htime


/-- The inverse differential and zero-time pullback for a boundary-tangent flow. -/
theorem pullback_boundary :
    Specs.SmoothManifolds.Ch06.BracketFromFlow.pullback_boundaryType.{u} := by
  intro n a M _ S B X hX F hF
  have hz := fun p => (hF p).1
  have hi := fun p => (hF p).2.1
  have hc := pullbackCorrect_of_flow S F hz hi
    (BoundaryTangentFlow.domain_open_smooth S B X hX F hF).2 (BoundaryTangentFlow.lifespan_flow_law S B X hX F hF)
  exact ⟨hc, fun Y p => pullback_zero_of_correct S F hz hi hc Y.val p⟩

/-- The inverse differential and zero-time pullback for a boundaryless flow. -/
theorem pullback_boundaryless :
    Specs.SmoothManifolds.Ch06.BracketFromFlow.pullback_boundarylessType.{u} := by
  intro n M _ S B X F hF
  have hz := fun p => (hF p).1
  have hi := fun p => (hF p).2.1
  have hc := pullbackCorrect_of_flow S F hz hi
    (MaximalFlow.domain_open_smooth S B X F hF).2
    (MaximalFlow.lifespan_flow_law S B X F hF)
  exact ⟨hc, fun Y p => pullback_zero_of_correct S F hz hi hc Y.val p⟩

theorem pullback_smooth :
    Specs.SmoothManifolds.Ch06.BracketFromFlow.pullback_smoothType.{u} := by
  intro n M _ S B X F hF Y z hz
  obtain ⟨hD, hsm⟩ := MaximalFlow.domain_open_smooth S B X F hF
  have hc := (pullback_boundaryless S B X F hF).1
  exact pullbackSmoothAt_of_flow B F hc hD hsm Y z.1 z.2 hz


theorem boundary_pullback_smooth :
    Specs.SmoothManifolds.Ch06.BracketFromFlow.boundary_pullback_smoothType.{u} := by
  intro n a M _ S B X hX F hF Y z hz
  obtain ⟨hD, hsm⟩ := BoundaryTangentFlow.domain_open_smooth S B X hX F hF
  have hc := (pullback_boundary S B X hX F hF).1
  exact pullbackSmoothAt_of_flow B F hc hD hsm Y z.1 z.2 hz


theorem derivative_at_time :
    Specs.SmoothManifolds.Ch06.BracketFromFlow.derivative_at_timeType.{u} := by
  intro n M _ S B b hb X Y F hF p t ht
  obtain ⟨hD, hsm⟩ := MaximalFlow.domain_open_smooth S B X F hF
  have hc := (pullback_boundaryless S B X F hF).1
  exact derivative_at_time_of_flow B b hb X Y F hF hD hsm
    (MaximalFlow.lifespan_flow_law S B X F hF) hc p t ht


theorem boundary_derivative_at_time :
    Specs.SmoothManifolds.Ch06.BracketFromFlow.boundary_derivative_at_timeType.{u} := by
  intro n a M _ S B b hb X Y hX F hF p t ht
  obtain ⟨hD, hsm⟩ := BoundaryTangentFlow.domain_open_smooth S B X hX F hF
  have hc := (pullback_boundary S B X hX F hF).1
  exact derivative_at_time_of_flow B b hb X Y F hF hD hsm
    (BoundaryTangentFlow.lifespan_flow_law S B X hX F hF) hc p t ht


theorem derivative_zero :
    Specs.SmoothManifolds.Ch06.BracketFromFlow.derivative_zeroType.{u} := by
  intro n M _ S B b hb X Y F hF p
  have h := derivative_at_time S B b hb X Y F hF p 0 (hF p).1
  have hpb : pullback F (b X Y).val 0 = (b X Y).val :=
    funext (fun q => (pullback_boundaryless S B X F hF).2 (b X Y) q)
  rwa [hpb] at h


theorem boundary_derivative_zero :
    Specs.SmoothManifolds.Ch06.BracketFromFlow.boundary_derivative_zeroType.{u} := by
  intro n a M _ S B b hb X Y hX F hF p
  have h := boundary_derivative_at_time S B b hb X Y hX F hF p 0 (hF p).1
  have hpb : pullback F (b X Y).val 0 = (b X Y).val :=
    funext (fun q => (pullback_boundary S B X hX F hF).2 (b X Y) q)
  rwa [hpb] at h

end SmoothManifolds.BracketFromFlow
