import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch15.PoleMovement
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Connected.Clopen
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.RationalInfinity
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereTopology
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
open Set TopologicalSpace
open scoped Topology

namespace D12Complex.PoleMovement

/- Candidate-owned exports of the shared canonical definitions. -/
namespace Definitions
abbrev sphericalComplement := D12Complex.PoleMovement.sphericalComplement
abbrev rationalRestrictions := D12Complex.PoleMovement.rationalRestrictions
abbrev uniformClosure := D12Complex.PoleMovement.uniformClosure
abbrev resolvent := D12Complex.PoleMovement.resolvent
abbrev coordinate := D12Complex.PoleMovement.coordinate
end Definitions

open Filter
open D12Complex.RationalInfinity
open D12Complex.LocalQuotientsArithmetic hiding add mul sub neg inv div
open private rational_meromorphic reciprocal_meromorphic from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.RationalInfinity

private theorem normal_form_of_finite {f : ℂ → ℂ} {a c : ℂ}
    (hf : MeromorphicAt f a) (hc : fill f a = sphereFinite c) :
    AnalyticAt ℂ (toMeromorphicNFAt f a) a ∧ toMeromorphicNFAt f a a = c := by
  have hn : ¬ meromorphicOrderAt f a < 0 := by
    intro hn
    have he : fill f a = sphereInfty := (fill_eq_infty_iff f a).mpr hn
    rw [hc] at he
    exact OnePoint.coe_ne_infty c he
  refine ⟨hf.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp
    (not_lt.mp hn), ?_⟩
  apply sphereFinite_injective
  simpa only [fill, ite_eq_right hn] using hc

private theorem fill_add_finite {f g : ℂ → ℂ} {a c d : ℂ}
    (hf : MeromorphicAt f a) (hg : MeromorphicAt g a)
    (hc : fill f a = sphereFinite c) (hd : fill g a = sphereFinite d) :
    fill (f + g) a = sphereFinite (c + d) := by
  obtain ⟨hfn, hfc⟩ := normal_form_of_finite hf hc
  obtain ⟨hgn, hgd⟩ := normal_form_of_finite hg hd
  exact (fill_congr (f + g) (toMeromorphicNFAt f a + toMeromorphicNFAt g a) a
    (hf.eq_nhdsNE_toMeromorphicNFAt.add hg.eq_nhdsNE_toMeromorphicNFAt)).trans
    ((fill_of_analyticAt (hfn.add hgn)).trans (by simp only [Pi.add_apply, hfc, hgd]))

private theorem fill_mul_finite {f g : ℂ → ℂ} {a c d : ℂ}
    (hf : MeromorphicAt f a) (hg : MeromorphicAt g a)
    (hc : fill f a = sphereFinite c) (hd : fill g a = sphereFinite d) :
    fill (f * g) a = sphereFinite (c * d) := by
  obtain ⟨hfn, hfc⟩ := normal_form_of_finite hf hc
  obtain ⟨hgn, hgd⟩ := normal_form_of_finite hg hd
  exact (fill_congr (f * g) (toMeromorphicNFAt f a * toMeromorphicNFAt g a) a
    (hf.eq_nhdsNE_toMeromorphicNFAt.mul hg.eq_nhdsNE_toMeromorphicNFAt)).trans
    ((fill_of_analyticAt (hfn.mul hgn)).trans (by simp only [Pi.mul_apply, hfc, hgd]))

private theorem rational_add_cofinite (P Q U V : Polynomial ℂ) (hQ : Q ≠ 0) (hV : V ≠ 0) :
    rational (P * V + U * Q) (Q * V) =ᶠ[cofinite] rational P Q + rational U V := by
  filter_upwards [Polynomial.eventually_eval_ne_zero_cofinite hQ,
    Polynomial.eventually_eval_ne_zero_cofinite hV] with z hq hv
  simp only [rational, Polynomial.eval_add, Polynomial.eval_mul, Pi.add_apply]
  field_simp

private theorem rational_mul_eq (P Q U V : Polynomial ℂ) :
    rational (P * U) (Q * V) = rational P Q * rational U V := by
  funext z
  simp only [rational, Polynomial.eval_mul, Pi.mul_apply]
  exact div_mul_div_comm _ _ _ _ |>.symm

/-- Addition cannot introduce a pole at any spherical point where both
summands are finite. The reciprocal chart is checked as well. -/
theorem extension_add_finite (P Q U V : Polynomial ℂ) (hQ : Q ≠ 0) (hV : V ≠ 0)
    (p : RiemannSphere) (c d : ℂ)
    (hc : extension P Q p = sphereFinite c) (hd : extension U V p = sphereFinite d) :
    extension (P * V + U * Q) (Q * V) p = sphereFinite (c + d) := by
  have he := rational_add_cofinite P Q U V hQ hV
  induction p using OnePoint.rec with
  | coe a =>
    change fill _ a = _ at hc hd ⊢
    exact (fill_congr _ _ a (he.filter_mono (nhdsNE_le_cofinite a))).trans
      (fill_add_finite (rational_meromorphic P Q a) (rational_meromorphic U V a) hc hd)
  | infty =>
    change fill _ 0 = _ at hc hd ⊢
    have hi : Tendsto (fun w : ℂ => w⁻¹) (𝓝[≠] 0) cofinite :=
      inv_injective.tendsto_cofinite.mono_left (nhdsNE_le_cofinite 0)
    exact (fill_congr _ _ 0 (he.comp_tendsto hi)).trans
      (fill_add_finite (reciprocal_meromorphic P Q) (reciprocal_meromorphic U V) hc hd)

theorem extension_mul_finite (P Q U V : Polynomial ℂ) (p : RiemannSphere) (c d : ℂ)
    (hc : extension P Q p = sphereFinite c) (hd : extension U V p = sphereFinite d) :
    extension (P * U) (Q * V) p = sphereFinite (c * d) := by
  induction p using OnePoint.rec with
  | coe a =>
    change fill _ a = _ at hc hd ⊢
    rw [rational_mul_eq]
    exact fill_mul_finite (rational_meromorphic P Q a) (rational_meromorphic U V a) hc hd
  | infty =>
    change fill _ 0 = _ at hc hd ⊢
    have he : reciprocalPullback (rational (P * U) (Q * V)) =
        reciprocalPullback (rational P Q) * reciprocalPullback (rational U V) := by
      funext w
      exact congrFun (rational_mul_eq P Q U V) w⁻¹
    rw [he]
    exact fill_mul_finite (reciprocal_meromorphic P Q) (reciprocal_meromorphic U V) hc hd

theorem extension_constant (c : ℂ) (p : RiemannSphere) :
    extension (Polynomial.C c) 1 p = sphereFinite c := by
  have he : rational (Polynomial.C c) 1 = fun _ => c := by
    funext z; simp [rational]
  induction p using OnePoint.rec with
  | coe a => change fill _ a = _; rw [he]; exact fill_const c a
  | infty =>
    change fill _ 0 = _
    have hi : reciprocalPullback (rational (Polynomial.C c) 1) = fun _ => c := by
      funext w; simp [reciprocalPullback, he]
    rw [hi]; exact fill_const c 0

theorem rationalRestrictions_const (K : Compacts ℂ) (A : Set RiemannSphere) (c : ℂ) :
    ContinuousMap.const K c ∈ rationalRestrictions K A := by
  refine ⟨Polynomial.C c, 1, one_ne_zero, ?_, ?_⟩
  · intro p hp
    exact (OnePoint.coe_ne_infty c ((extension_constant c p).symm.trans hp)).elim
  · intro z
    exact extension_constant c (sphereFinite z)

theorem rationalRestrictions_add {K : Compacts ℂ} {A : Set RiemannSphere}
    {f g : C(K, ℂ)} (hf : f ∈ rationalRestrictions K A) (hg : g ∈ rationalRestrictions K A) :
    f + g ∈ rationalRestrictions K A := by
  obtain ⟨P, Q, hQ, hp, hf⟩ := hf
  obtain ⟨U, V, hV, hu, hg⟩ := hg
  refine ⟨P * V + U * Q, Q * V, mul_ne_zero hQ hV, ?_, ?_⟩
  · intro p hnew
    by_contra hpA
    obtain ⟨c, hc⟩ := (sphere_eq_infty_or_finite (extension P Q p)).resolve_left
      (fun h => hpA (hp p h))
    obtain ⟨d, hd⟩ := (sphere_eq_infty_or_finite (extension U V p)).resolve_left
      (fun h => hpA (hu p h))
    have hh := extension_add_finite P Q U V hQ hV p c d hc hd
    exact OnePoint.infty_ne_coe (c + d) (hnew.symm.trans hh)
  · intro z
    exact extension_add_finite P Q U V hQ hV (sphereFinite z) (f z) (g z) (hf z) (hg z)

theorem rationalRestrictions_mul {K : Compacts ℂ} {A : Set RiemannSphere}
    {f g : C(K, ℂ)} (hf : f ∈ rationalRestrictions K A) (hg : g ∈ rationalRestrictions K A) :
    f * g ∈ rationalRestrictions K A := by
  obtain ⟨P, Q, hQ, hp, hf⟩ := hf
  obtain ⟨U, V, hV, hu, hg⟩ := hg
  refine ⟨P * U, Q * V, mul_ne_zero hQ hV, ?_, ?_⟩
  · intro p hnew
    by_contra hpA
    obtain ⟨c, hc⟩ := (sphere_eq_infty_or_finite (extension P Q p)).resolve_left
      (fun h => hpA (hp p h))
    obtain ⟨d, hd⟩ := (sphere_eq_infty_or_finite (extension U V p)).resolve_left
      (fun h => hpA (hu p h))
    have hh := extension_mul_finite P Q U V p c d hc hd
    exact OnePoint.infty_ne_coe (c * d) (hnew.symm.trans hh)
  · intro z
    exact extension_mul_finite P Q U V (sphereFinite z) (f z) (g z) (hf z) (hg z)

/-- The permitted rational restrictions themselves form a complex algebra. -/
def rationalAlgebra (K : Compacts ℂ) (A : Set RiemannSphere) : Subalgebra ℂ C(K, ℂ) where
  carrier := rationalRestrictions K A
  mul_mem' := rationalRestrictions_mul
  add_mem' := rationalRestrictions_add
  algebraMap_mem' := rationalRestrictions_const K A

theorem uniformClosure_algebra (K : Compacts ℂ) (A : Set RiemannSphere)
    (_hA : A ⊆ sphericalComplement K) :
    ∃ S : Subalgebra ℂ C(K, ℂ), (S : Set C(K, ℂ)) = uniformClosure K A :=
  ⟨(rationalAlgebra K A).topologicalClosure, rfl⟩

theorem constants_mem (K : Compacts ℂ) (A : Set RiemannSphere) (c : ℂ) :
    ContinuousMap.const K c ∈ uniformClosure K A :=
  subset_closure (rationalRestrictions_const K A c)

theorem rationalRestrictions_coordinate (K : Compacts ℂ) (A : Set RiemannSphere)
    (hA : sphereInfty ∈ A) : coordinate K ∈ rationalRestrictions K A := by
  refine ⟨Polynomial.X, 1, one_ne_zero, ?_, ?_⟩
  · intro p hp
    induction p using OnePoint.rec with
    | infty => exact hA
    | coe z =>
      have he := (meromorphic_extension Polynomial.X 1 one_ne_zero).2 z (by simp)
      simp only [Polynomial.eval_one, Polynomial.eval_X, div_one] at he
      exact (OnePoint.coe_ne_infty z (he.symm.trans hp)).elim
  · intro z
    change extension Polynomial.X 1 (sphereFinite z) = sphereFinite (z : ℂ)
    simpa using (meromorphic_extension Polynomial.X 1 one_ne_zero).2 z (by simp)

theorem rationalRestrictions_resolvent (K : Compacts ℂ) (A : Set RiemannSphere)
    (a : ℂ) (ha : a ∉ (K : Set ℂ)) (hA : sphereFinite a ∈ A) :
    resolvent K a ha ∈ rationalRestrictions K A := by
  let Q : Polynomial ℂ := Polynomial.X - Polynomial.C a
  have hQ : Q ≠ 0 := Polynomial.X_sub_C_ne_zero a
  have hfinite (z : ℂ) (hz : z ≠ a) :
      extension 1 Q (sphereFinite z) = sphereFinite (z - a)⁻¹ := by
    simpa [Q] using (meromorphic_extension 1 Q hQ).2 z (by simpa [Q] using sub_ne_zero.mpr hz)
  have hinfty : extension 1 Q sphereInfty = sphereFinite 0 := by
    apply (infinity_values 1 Q one_ne_zero hQ (isRelPrime_one_left)).2
    simp [Q]
  refine ⟨1, Q, hQ, ?_, ?_⟩
  · intro p hp
    induction p using OnePoint.rec with
    | infty => exact (OnePoint.coe_ne_infty 0 (hinfty.symm.trans hp)).elim
    | coe z =>
      by_cases hz : z = a
      · change sphereFinite z ∈ A
        rw [hz]
        exact hA
      · exact (OnePoint.coe_ne_infty ((z - a)⁻¹) ((hfinite z hz).symm.trans hp)).elim
  · intro z
    exact hfinite z (fun hz => ha (by
      have hzK : (z : ℂ) ∈ (K : Set ℂ) := z.2
      exact hz ▸ hzK))

/-- Complements of large disks are connected. Using the exponential image
of a half-plane avoids any plane separation assumption. -/
theorem isConnected_exterior {R : ℝ} (hR : 0 < R) :
    IsConnected {z : ℂ | R < ‖z‖} := by
  let H : Set ℂ := {z | Real.log R < z.re}
  have hH : Convex ℝ H := (convex_Ioi (Real.log R)).linear_preimage Complex.reLm
  have hne : H.Nonempty := ⟨((Real.log R + 1 : ℝ) : ℂ), by
    change Real.log R < Real.log R + 1
    linarith⟩
  have he : Complex.exp '' H = {z : ℂ | R < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change R < ‖Complex.exp w‖
      rw [Complex.norm_exp]
      exact (Real.log_lt_iff_lt_exp hR).mp hw
    · intro hz
      have hz0 : z ≠ 0 := norm_pos_iff.mp (hR.trans hz)
      refine ⟨Complex.log z, ?_, Complex.exp_log hz0⟩
      change Real.log R < (Complex.log z).re
      rw [Complex.log_re]
      exact Real.log_lt_log hR hz
  rw [← he]
  exact (hH.isConnected hne).image Complex.exp Complex.continuous_exp.continuousOn

theorem isOpen_compl_component {U : Set ℂ} (hU : IsOpen U) (a : ℂ) :
    IsOpen (U \ connectedComponentIn U a) := by
  have he : U \ connectedComponentIn U a =
      ⋃ b ∈ U \ connectedComponentIn U a, connectedComponentIn U b := by
    ext z
    constructor
    · intro hz
      exact mem_iUnion₂.mpr ⟨z, hz, mem_connectedComponentIn hz.1⟩
    · intro hz
      obtain ⟨b, hb, hzb⟩ := mem_iUnion₂.mp hz
      refine ⟨connectedComponentIn_subset U b hzb, ?_⟩
      intro hza
      have he := (connectedComponentIn_eq hza).trans (connectedComponentIn_eq hzb).symm
      apply hb.2
      rw [he]
      exact mem_connectedComponentIn hb.1
  rw [he]
  exact isOpen_biUnion (fun b _ => hU.connectedComponentIn)

/-- An unbounded connected set meets every exterior. -/
theorem exists_norm_gt_of_unbounded {C : Set ℂ} (hC : ¬ Bornology.IsBounded C) (R : ℝ) :
    ∃ z ∈ C, R < ‖z‖ := by
  by_contra h
  apply hC
  refine isBounded_iff_forall_norm_le.mpr ⟨R, ?_⟩
  intro z hz
  exact not_lt.mp (fun hh => h ⟨z, hz, hh⟩)

/-- The plane component containing an exterior contains every sufficiently
distant point, and its one-point extension is the spherical infinity component. -/
theorem infinity_component_of_exterior (K : Compacts ℂ) (R : ℝ) (hR : 0 < R)
    (hKR : ∀ z ∈ (K : Set ℂ), ‖z‖ ≤ R) (b : ℂ) (hb : R < ‖b‖) :
    connectedComponentIn (sphericalComplement K) sphereInfty =
      insert sphereInfty (sphereFinite '' connectedComponentIn (K : Set ℂ)ᶜ b) := by
  let C := connectedComponentIn (K : Set ℂ)ᶜ b
  let D := (K : Set ℂ)ᶜ \ C
  let L := insert sphereInfty (sphereFinite '' C)
  have hU : IsOpen (K : Set ℂ)ᶜ := K.isCompact.isClosed.isOpen_compl
  have hE : {z : ℂ | R < ‖z‖} ⊆ (K : Set ℂ)ᶜ := by
    intro z hz hzk
    exact (not_lt.mpr (hKR z hzk)) hz
  have hEC : {z : ℂ | R < ‖z‖} ⊆ C :=
    (isConnected_exterior hR).isPreconnected.subset_connectedComponentIn hb hE
  have hC : IsOpen C := hU.connectedComponentIn
  have hD : IsOpen D := isOpen_compl_component hU b
  have hCc : IsCompact Cᶜ :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hC.isClosed_compl (by
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right]
      exact not_lt.mp (fun hh => hz (hEC hh)))
  have hpre : sphereFinite ⁻¹' L = C := by
    ext z
    simp only [L, mem_preimage, mem_insert_iff, mem_image]
    constructor
    · rintro (hi | ⟨w, hw, he⟩)
      · exact (OnePoint.coe_ne_infty z hi).elim
      · exact (sphereFinite_injective he) ▸ hw
    · intro hz
      exact Or.inr ⟨z, hz, rfl⟩
  have hL : IsOpen L := by
    apply (OnePoint.isOpen_iff_of_mem (show sphereInfty ∈ L from mem_insert _ _)).mpr
    change IsClosed (sphereFinite ⁻¹' L)ᶜ ∧ IsCompact (sphereFinite ⁻¹' L)ᶜ
    rw [hpre]
    exact ⟨hC.isClosed_compl, hCc⟩
  have hDimage : IsOpen (sphereFinite '' D) := OnePoint.isOpenMap_coe _ hD
  have hLsub : L ⊆ sphericalComplement K := by
    intro p hp
    rcases hp with rfl | ⟨z, hz, rfl⟩
    · rintro ⟨z, _, he⟩
      exact OnePoint.coe_ne_infty z he
    · rintro ⟨w, hw, he⟩
      have hwz := sphereFinite_injective he
      exact connectedComponentIn_subset (K : Set ℂ)ᶜ b hz (hwz ▸ hw)
  have hdis : Disjoint L (sphereFinite '' D) := by
    apply disjoint_left.mpr
    intro p hp hpd
    obtain ⟨z, hz, rfl⟩ := hpd
    exact hz.2 (hpre ▸ hp)
  have hcover : sphericalComplement K ⊆ L ∪ sphereFinite '' D := by
    intro p hp
    induction p using OnePoint.rec with
    | infty => exact Or.inl (mem_insert _ _)
    | coe z =>
      by_cases hz : z ∈ C
      · exact Or.inl (mem_insert_of_mem _ ⟨z, hz, rfl⟩)
      · exact Or.inr ⟨z, ⟨(fun hzk => hp ⟨z, hzk, rfl⟩), hz⟩, rfl⟩
  have hclosure : sphereInfty ∈ closure (sphereFinite '' C) := by
    rw [mem_closure_iff_nhds]
    intro N hN
    obtain ⟨T, hT, hTN⟩ := (mem_nhds_sphereInfty_iff N).mp hN
    let z : ℂ := ((max R T + 1 : ℝ) : ℂ)
    have hnz : ‖z‖ = max R T + 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
      linarith [le_max_left R T]
    have hzR : R < ‖z‖ := by rw [hnz]; linarith [le_max_left R T]
    have hzT : T < ‖z‖ := by rw [hnz]; linarith [le_max_right R T]
    exact ⟨sphereFinite z, hTN (Or.inr ⟨z, hzT, rfl⟩), ⟨z, hEC hzR, rfl⟩⟩
  have hLconn : IsPreconnected L :=
    (isPreconnected_connectedComponentIn.image sphereFinite continuous_sphereFinite.continuousOn)
      |>.subset_closure (subset_insert _ _) (by
        intro p hp
        rcases hp with rfl | hp
        · exact hclosure
        · exact subset_closure hp)
  apply subset_antisymm
  · exact isPreconnected_connectedComponentIn.subset_left_of_subset_union
      hL hDimage hdis ((connectedComponentIn_subset _ _).trans hcover)
      ⟨sphereInfty, mem_connectedComponentIn (hLsub (mem_insert _ _)), mem_insert _ _⟩
  · exact hLconn.subset_connectedComponentIn (mem_insert _ _) hLsub

theorem exterior_unbounded (R : ℝ) : ¬ Bornology.IsBounded {z : ℂ | R < ‖z‖} := by
  intro h
  obtain ⟨T, hT⟩ := h.exists_norm_le
  let z : ℂ := ((max (max R T) 0 + 1 : ℝ) : ℂ)
  have hn : ‖z‖ = max (max R T) 0 + 1 := by
    change ‖((max (max R T) 0 + 1 : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    linarith [le_max_right (max R T) 0]
  have hz : R < ‖z‖ := by
    rw [hn]
    linarith [le_max_left R T, le_max_left (max R T) 0]
  have hh := hT z hz
  rw [hn] at hh
  linarith [le_max_right R T, le_max_left (max R T) 0]

theorem unbounded_component (K : Compacts ℂ) :
    IsConnected (sphereFinite ⁻¹'
      connectedComponentIn (sphericalComplement K) sphereInfty) ∧
    ¬ Bornology.IsBounded (sphereFinite ⁻¹'
      connectedComponentIn (sphericalComplement K) sphereInfty) ∧
    ∀ a : ℂ, a ∉ (K : Set ℂ) →
      (¬ Bornology.IsBounded (connectedComponentIn (K : Set ℂ)ᶜ a) ↔
        sphereFinite a ∈ connectedComponentIn (sphericalComplement K) sphereInfty) := by
  obtain ⟨R, hR, hKR⟩ := K.isCompact.isBounded.exists_pos_norm_le
  let b : ℂ := ((R + 1 : ℝ) : ℂ)
  have hb : R < ‖b‖ := by
    change R < ‖((R + 1 : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hE : {z : ℂ | R < ‖z‖} ⊆ (K : Set ℂ)ᶜ := by
    intro z hz hzk
    exact (not_lt.mpr (hKR z hzk)) hz
  have hEC := (isConnected_exterior hR).isPreconnected.subset_connectedComponentIn hb hE
  have he := infinity_component_of_exterior K R hR hKR b hb
  have hpre : sphereFinite ⁻¹' connectedComponentIn (sphericalComplement K) sphereInfty =
      connectedComponentIn (K : Set ℂ)ᶜ b := by
    rw [he]
    ext z
    simp [sphereFinite, sphereInfty]
  have hCb : ¬ Bornology.IsBounded (connectedComponentIn (K : Set ℂ)ᶜ b) :=
    fun h => exterior_unbounded R (h.subset hEC)
  refine ⟨?_, ?_, ?_⟩
  · rw [hpre]
    exact isConnected_connectedComponentIn_iff.mpr (hE hb)
  · rwa [hpre]
  · intro a ha
    change ¬ Bornology.IsBounded (connectedComponentIn (K : Set ℂ)ᶜ a) ↔
      a ∈ sphereFinite ⁻¹' connectedComponentIn (sphericalComplement K) sphereInfty
    rw [hpre]
    constructor
    · intro hun
      obtain ⟨z, hza, hzR⟩ := exists_norm_gt_of_unbounded hun R
      have heq := (connectedComponentIn_eq hza).trans (connectedComponentIn_eq (hEC hzR)).symm
      rw [← heq]
      exact mem_connectedComponentIn ha
    · intro hab
      rw [← connectedComponentIn_eq hab]
      exact hCb

theorem finite_mem_sphericalComplement_iff (K : Compacts ℂ) (a : ℂ) :
    sphereFinite a ∈ sphericalComplement K ↔ a ∉ (K : Set ℂ) := by
  simp [sphericalComplement, sphereFinite]

theorem finite_part_subset_complement (K : Compacts ℂ) (p : RiemannSphere) :
    sphereFinite ⁻¹' connectedComponentIn (sphericalComplement K) p ⊆ (K : Set ℂ)ᶜ := by
  intro a ha
  exact (finite_mem_sphericalComplement_iff K a).mp (connectedComponentIn_subset _ _ ha)

/-- Adding infinity does not join distinct finite complementary components.
The case of its own component uses the connectedness proved above. -/
theorem finite_component_of_spherical (K : Compacts ℂ) (a b : ℂ)
    (ha : a ∉ (K : Set ℂ))
    (hab : sphereFinite b ∈ connectedComponentIn (sphericalComplement K) (sphereFinite a)) :
    b ∈ connectedComponentIn (K : Set ℂ)ᶜ a := by
  let C := connectedComponentIn (sphericalComplement K) (sphereFinite a)
  have hconn : IsPreconnected (sphereFinite ⁻¹' C) := by
    by_cases hi : sphereInfty ∈ C
    · have he := connectedComponentIn_eq hi
      change IsPreconnected (sphereFinite ⁻¹' connectedComponentIn
        (sphericalComplement K) (sphereFinite a))
      rw [he]
      exact (unbounded_component K).1.isPreconnected
    · apply isPreconnected_connectedComponentIn.preimage_of_isOpenMap
        sphereFinite_injective OnePoint.isOpenMap_coe
      intro p hp
      rcases sphere_eq_infty_or_finite p with he | ⟨z, hz⟩
      · exact (hi (he ▸ hp)).elim
      · exact ⟨z, hz.symm⟩
  exact hconn.subset_connectedComponentIn
    (mem_connectedComponentIn ((finite_mem_sphericalComplement_iff K a).mpr ha))
    (finite_part_subset_complement K (sphereFinite a)) hab

theorem uniformClosure_isClosed (K : Compacts ℂ) (A : Set RiemannSphere) :
    IsClosed (uniformClosure K A) := isClosed_closure

theorem uniformClosure_iff_approximation (K : Compacts ℂ) (A : Set RiemannSphere)
    (f : C(K, ℂ)) : f ∈ uniformClosure K A ↔
      ∀ ε : ℝ, 0 < ε → ∃ g ∈ rationalRestrictions K A,
        ∀ z : K, ‖f z - g z‖ < ε := by
  simp only [uniformClosure, Metric.mem_closure_iff, dist_eq_norm]
  constructor
  · intro h ε hε
    obtain ⟨g, hg, hh⟩ := h ε hε
    refine ⟨g, hg, ?_⟩
    exact (ContinuousMap.norm_lt_iff (f - g) hε).mp hh
  · intro h ε hε
    obtain ⟨g, hg, hh⟩ := h ε hε
    exact ⟨g, hg, (ContinuousMap.norm_lt_iff (f - g) hε).mpr hh⟩

theorem permitted_rational_restriction (K : Compacts ℂ) (A : Set RiemannSphere)
    (hA : A ⊆ sphericalComplement K) (P Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (hp : ∀ p : RiemannSphere,
      Specs.D12Complex.Ch07.RationalInfinity.Objects.extension P Q p = sphereInfty → p ∈ A) :
    ∃ f ∈ rationalRestrictions K A, ∀ z : K,
      Specs.D12Complex.Ch07.RationalInfinity.Objects.extension P Q (sphereFinite z) =
        sphereFinite (f z) := by
  have hfinite (z : K) : extension P Q (sphereFinite z) ≠ sphereInfty := by
    intro hz
    exact (finite_mem_sphericalComplement_iff K z).mp (hA (hp (sphereFinite z) hz)) z.2
  have hmero : ScalarMeromorphicOn univ (extension P Q ∘ sphereFinite) := by
    exact (meromorphic_extension P Q hQ).1.2.1
  have hc : Continuous (fun z : K => finiteCoordinate (extension P Q (sphereFinite z))) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (scalarMeromorphicOn_finite_analytic univ (extension P Q ∘ sphereFinite)
      hmero z (mem_univ _) (hfinite z)).continuousAt.comp continuous_subtype_val.continuousAt
  let f : C(K, ℂ) := ⟨fun z => finiteCoordinate (extension P Q (sphereFinite z)), hc⟩
  have hf (z : K) : extension P Q (sphereFinite z) = sphereFinite (f z) := by
    rcases sphere_eq_infty_or_finite (extension P Q (sphereFinite z)) with hi | ⟨c, he⟩
    · exact (hfinite z hi).elim
    · change extension P Q (sphereFinite z) =
        sphereFinite (finiteCoordinate (extension P Q (sphereFinite z)))
      rw [he, finiteCoordinate_sphereFinite]
  exact ⟨f, ⟨P, Q, hQ, hp, hf⟩, hf⟩

/-- The geometric inverse belongs to every closed subalgebra containing x. -/
theorem geometric_sum_mem {K : Compacts ℂ} (S : Subalgebra ℂ C(K, ℂ))
    (hS : IsClosed (S : Set C(K, ℂ))) {x : C(K, ℂ)} (hx : x ∈ S) :
    (∑' n : ℕ, x ^ n) ∈ S :=
  tsum_mem hS (fun n => S.pow_mem hx n)

theorem resolvent_geometric_series (K : Compacts ℂ) (a b : ℂ)
    (ha : a ∉ (K : Set ℂ)) (hb : b ∉ (K : Set ℂ))
    (h : ‖(b - a) • resolvent K a ha‖ < 1) :
    HasSum (fun n : ℕ => (b - a) ^ n • resolvent K a ha ^ (n + 1))
      (resolvent K b hb) := by
  let x : C(K, ℂ) := (b - a) • resolvent K a ha
  have hs := (summable_geometric_of_norm_lt_one h).hasSum.mul_right
    (resolvent K a ha)
  have he : (∑' n : ℕ, x ^ n) * resolvent K a ha = resolvent K b hb := by
    have hi := geom_series_mul_neg x h
    ext z
    have haz : (z : ℂ) - a ≠ 0 := fun hz => ha (by
      have hzK : (z : ℂ) ∈ (K : Set ℂ) := z.2
      exact (sub_eq_zero.mp hz) ▸ hzK)
    have hbz : (z : ℂ) - b ≠ 0 := fun hz => hb (by
      have hzK : (z : ℂ) ∈ (K : Set ℂ) := z.2
      exact (sub_eq_zero.mp hz) ▸ hzK)
    have hv := congrArg (fun f : C(K, ℂ) => f z) hi
    change (∑' n : ℕ, x ^ n) z * (1 - (b - a) * ((z : ℂ) - a)⁻¹) = 1 at hv
    change (∑' n : ℕ, x ^ n) z * ((z : ℂ) - a)⁻¹ = ((z : ℂ) - b)⁻¹
    field_simp at hv ⊢
    linear_combination hv
  rw [← he]
  convert hs using 1
  ext n z
  simp [pow_succ, mul_pow, smul_eq_mul, mul_assoc]

theorem closedAlgebra_resolvent_near (K : Compacts ℂ) (S : Subalgebra ℂ C(K, ℂ))
    (hS : IsClosed (S : Set C(K, ℂ))) (a b : ℂ)
    (ha : a ∉ (K : Set ℂ)) (hb : b ∉ (K : Set ℂ))
    (hra : resolvent K a ha ∈ S) (h : ‖(b - a) • resolvent K a ha‖ < 1) :
    resolvent K b hb ∈ S := by
  exact hS.mem_of_tendsto (resolvent_geometric_series K a b ha hb h)
    (Filter.Eventually.of_forall (fun s => S.sum_mem (fun n _ =>
      S.smul_mem (S.pow_mem hra (n + 1)) ((b - a) ^ n))))

theorem resolvent_polynomial_series (K : Compacts ℂ) (b : ℂ)
    (hb : b ∉ (K : Set ℂ)) (h : ‖coordinate K‖ < ‖b‖) :
    HasSum (fun n : ℕ => -(b ^ (n + 1))⁻¹ • coordinate K ^ n)
      (resolvent K b hb) := by
  have hb0 : b ≠ 0 := by
    intro hb0
    simpa [hb0] using (lt_of_le_of_lt (norm_nonneg _) h)
  let x : C(K, ℂ) := b⁻¹ • coordinate K
  have hx : ‖x‖ < 1 := by
    rw [norm_smul, norm_inv]
    exact (inv_mul_lt_one₀ (norm_pos_iff.mpr hb0)).mpr h
  have hs := (summable_geometric_of_norm_lt_one hx).hasSum.const_smul (-b⁻¹)
  have he : -b⁻¹ • (∑' n : ℕ, x ^ n) = resolvent K b hb := by
    have hi := geom_series_mul_neg x hx
    ext z
    have hbz : (z : ℂ) - b ≠ 0 := fun hz => hb (by
      have hzK : (z : ℂ) ∈ (K : Set ℂ) := z.2
      exact (sub_eq_zero.mp hz) ▸ hzK)
    have hv := congrArg (fun f : C(K, ℂ) => f z) hi
    change (∑' n : ℕ, x ^ n) z * (1 - b⁻¹ * (z : ℂ)) = 1 at hv
    change -b⁻¹ * (∑' n : ℕ, x ^ n) z = ((z : ℂ) - b)⁻¹
    field_simp at hv ⊢
    linear_combination hv
  rw [← he]
  convert hs using 1
  ext n z
  simp [x, pow_succ, mul_pow, smul_eq_mul, mul_assoc]

theorem closedAlgebra_resolvent_far (K : Compacts ℂ) (S : Subalgebra ℂ C(K, ℂ))
    (hS : IsClosed (S : Set C(K, ℂ))) (hcoord : coordinate K ∈ S)
    (b : ℂ) (hb : b ∉ (K : Set ℂ)) (h : ‖coordinate K‖ < ‖b‖) :
    resolvent K b hb ∈ S := by
  exact hS.mem_of_tendsto (resolvent_polynomial_series K b hb h)
    (Filter.Eventually.of_forall (fun s => S.sum_mem (fun n _ =>
      S.smul_mem (S.pow_mem hcoord n) (-(b ^ (n + 1))⁻¹))))

/-- Resolvents vary continuously in the uniform norm, as long as the pole
stays in the complement of K. Compactness is built into C(K,ℂ). -/
theorem continuous_resolvent (K : Compacts ℂ) :
    Continuous (fun a : ↥((K : Set ℂ)ᶜ) => resolvent K a a.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ↥((K : Set ℂ)ᶜ) × K => ((p.2 : ℂ) - (p.1 : ℂ))⁻¹)
  apply ((continuous_subtype_val.comp continuous_snd).sub
    (continuous_subtype_val.comp continuous_fst)).inv₀
  intro p hp
  apply p.1.2
  have hzK : (p.2 : ℂ) ∈ (K : Set ℂ) := p.2.2
  have he : (p.2 : ℂ) = (p.1 : ℂ) := sub_eq_zero.mp hp
  exact he ▸ hzK

/-- The admissible finite pole locations form a clopen subset of the
plane complement. This does not assume that every component is seeded. -/
theorem isClopen_resolvent_mem (K : Compacts ℂ) (S : Subalgebra ℂ C(K, ℂ))
    (hS : IsClosed (S : Set C(K, ℂ))) :
    IsClopen {a : ↥((K : Set ℂ)ᶜ) | resolvent K a a.2 ∈ S} := by
  refine ⟨hS.preimage (continuous_resolvent K), ?_⟩
  rw [isOpen_iff_mem_nhds]
  intro a ha
  have hc : Continuous (fun b : ↥((K : Set ℂ)ᶜ) =>
      ‖((b : ℂ) - (a : ℂ)) • resolvent K a a.2‖) := by fun_prop
  have hzero : ‖((a : ℂ) - (a : ℂ)) • resolvent K a a.2‖ < 1 := by simp
  have hn := hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds hzero)
  exact Filter.mem_of_superset hn (fun b hb =>
    closedAlgebra_resolvent_near K S hS a b a.2 b.2 ha hb)

theorem closedAlgebra_resolvent_component (K : Compacts ℂ) (S : Subalgebra ℂ C(K, ℂ))
    (hS : IsClosed (S : Set C(K, ℂ))) (a b : ℂ)
    (ha : a ∉ (K : Set ℂ)) (hb : b ∉ (K : Set ℂ))
    (hab : b ∈ connectedComponentIn (K : Set ℂ)ᶜ a)
    (hra : resolvent K a ha ∈ S) : resolvent K b hb ∈ S := by
  have hh := isPreconnected_connectedComponent.subset_isClopen
    (isClopen_resolvent_mem K S hS)
    (show (connectedComponent (⟨a, ha⟩ : ↥((K : Set ℂ)ᶜ)) ∩
      {c : ↥((K : Set ℂ)ᶜ) | resolvent K c c.2 ∈ S}).Nonempty from
      ⟨⟨a, ha⟩, mem_connectedComponent, hra⟩)
  rw [connectedComponentIn_eq_image ha] at hab
  obtain ⟨c, hc, hcb⟩ := hab
  have hm := hh hc
  have he : c = (⟨b, hb⟩ : ↥((K : Set ℂ)ᶜ)) := Subtype.ext hcb
  simpa only [he, Set.mem_ofPred_eq] using hm

theorem resolvent_mem_uniformClosure (K : Compacts ℂ) (A : Set RiemannSphere)
    (hA : A ⊆ sphericalComplement K) (a : ℂ) (ha : a ∉ (K : Set ℂ))
    (hmeet : (connectedComponentIn (sphericalComplement K) (sphereFinite a) ∩ A).Nonempty) :
    resolvent K a ha ∈ uniformClosure K A := by
  obtain ⟨S, hS⟩ := uniformClosure_algebra K A hA
  have hclosed : IsClosed (S : Set C(K, ℂ)) := by
    rw [hS]
    exact uniformClosure_isClosed K A
  have hseed (b : ℂ) (hb : b ∉ (K : Set ℂ)) (hbA : sphereFinite b ∈ A) :
      resolvent K b hb ∈ S := by
    change resolvent K b hb ∈ (S : Set C(K, ℂ))
    rw [hS]
    exact subset_closure (rationalRestrictions_resolvent K A b hb hbA)
  obtain ⟨p, hpcomp, hpA⟩ := hmeet
  rw [← hS]
  induction p using OnePoint.rec with
  | coe b =>
    have hb : b ∉ (K : Set ℂ) := (finite_mem_sphericalComplement_iff K b).mp (hA hpA)
    have hab := finite_component_of_spherical K a b ha hpcomp
    have hba : a ∈ connectedComponentIn (K : Set ℂ)ᶜ b := by
      rw [← connectedComponentIn_eq hab]
      exact mem_connectedComponentIn ha
    exact closedAlgebra_resolvent_component K S hclosed b a hb ha hba (hseed b hb hpA)
  | infty =>
    have hcoord : coordinate K ∈ S := by
      change coordinate K ∈ (S : Set C(K, ℂ))
      rw [hS]
      exact subset_closure (rationalRestrictions_coordinate K A hpA)
    have haInf : sphereFinite a ∈ connectedComponentIn (sphericalComplement K) sphereInfty := by
      change sphereInfty ∈ connectedComponentIn (sphericalComplement K) (sphereFinite a) at hpcomp
      rw [← connectedComponentIn_eq hpcomp]
      exact mem_connectedComponentIn ((finite_mem_sphericalComplement_iff K a).mpr ha)
    obtain ⟨b, hbcomp, hbR⟩ := exists_norm_gt_of_unbounded
      (unbounded_component K).2.1 ‖coordinate K‖
    have hb : b ∉ (K : Set ℂ) := finite_part_subset_complement K sphereInfty hbcomp
    have hba : a ∈ connectedComponentIn (K : Set ℂ)ᶜ b :=
      (unbounded_component K).1.isPreconnected.subset_connectedComponentIn
        hbcomp (finite_part_subset_complement K sphereInfty) haInf
    exact closedAlgebra_resolvent_component K S hclosed b a hb ha hba
      (closedAlgebra_resolvent_far K S hclosed hcoord b hb hbR)

theorem resolvent_polynomial_approximation (K : Compacts ℂ) (a : ℂ)
    (ha : a ∉ (K : Set ℂ))
    (hun : ¬ Bornology.IsBounded (connectedComponentIn (K : Set ℂ)ᶜ a))
    (ε : ℝ) (hε : 0 < ε) : ∃ P : Polynomial ℂ,
      ∀ z ∈ (K : Set ℂ), ‖(z - a)⁻¹ - P.eval z‖ < ε := by
  let T : Subalgebra ℂ C(K, ℂ) := (Polynomial.aeval (coordinate K)).range
  let S := T.topologicalClosure
  have hclosed : IsClosed (S : Set C(K, ℂ)) := T.isClosed_topologicalClosure
  have hcoord : coordinate K ∈ S := T.le_topologicalClosure (by
    exact ⟨Polynomial.X, Polynomial.aeval_X (coordinate K)⟩)
  obtain ⟨b, hbcomp, hbR⟩ := exists_norm_gt_of_unbounded hun ‖coordinate K‖
  have hb : b ∉ (K : Set ℂ) := connectedComponentIn_subset _ _ hbcomp
  have hba : a ∈ connectedComponentIn (K : Set ℂ)ᶜ b := by
    rw [← connectedComponentIn_eq hbcomp]
    exact mem_connectedComponentIn ha
  have hm : resolvent K a ha ∈ S :=
    closedAlgebra_resolvent_component K S hclosed b a hb ha hba
      (closedAlgebra_resolvent_far K S hclosed hcoord b hb hbR)
  change resolvent K a ha ∈ closure (T : Set C(K, ℂ)) at hm
  obtain ⟨f, hf, hdist⟩ := Metric.mem_closure_iff.mp hm ε hε
  obtain ⟨P, rfl⟩ := hf
  refine ⟨P, ?_⟩
  intro z hz
  rw [dist_eq_norm] at hdist
  change ‖resolvent K a ha - Polynomial.aeval (coordinate K) P‖ < ε at hdist
  have hh := (ContinuousMap.norm_lt_iff (resolvent K a ha - Polynomial.aeval (coordinate K) P) hε).mp
    (by exact hdist) ⟨z, hz⟩
  have he : (Polynomial.aeval (coordinate K) P) ⟨z, hz⟩ = P.eval z := by
    have h := Polynomial.aeval_algHom_apply (ContinuousMap.evalAlgHom ℂ ℂ ⟨z, hz⟩)
      (coordinate K) P
    simpa only [ContinuousMap.evalAlgHom_apply, coordinate, ContinuousMap.coe_mk,
      Polynomial.coe_aeval_eq_eval] using h.symm
  simpa only [ContinuousMap.sub_apply, resolvent, ContinuousMap.coe_mk, he] using hh

end D12Complex.PoleMovement
