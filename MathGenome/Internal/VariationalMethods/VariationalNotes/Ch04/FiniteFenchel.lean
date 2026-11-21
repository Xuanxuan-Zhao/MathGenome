import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.FiniteFenchel
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch04.PerturbationAlgebra
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch04.LocalValueSupport
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.RelativeInteriorAffine
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology
universe u v
namespace VariationalNotes.Ch04
open VariationalNotes.ConvexAnalysis
open VariationalNotes.ConvexGeometry

/-- The finite-candidate perturbation domain. -/
def candidateDomain {X : Type u} {Y : Type v} (Φ : X × Y → WithTop ℝ) : Set Y :=
  {u | ∃ x, Φ (x,u) < ⊤}

lemma convex_candidateDomain {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    (Φ : X × Y → WithTop ℝ) (hc : IsConvex Φ) : Convex ℝ (candidateDomain Φ) := by
  have heq : candidateDomain Φ = (LinearMap.snd ℝ X Y) '' effectiveDomain Φ := by
    ext u
    constructor
    · rintro ⟨x,hx⟩
      exact ⟨(x,u),hx,rfl⟩
    · rintro ⟨⟨x,v⟩,hx,rfl⟩
      exact ⟨x,hx⟩
  rw [heq]
  exact (convex_effectiveDomain hc).linear_image _

/-- Relative interior excludes minus-infinite fibers, including in dimension zero. -/
lemma marginal_ne_bot_of_relativeInterior
    {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (Φ : X × Y → WithTop ℝ) (hc : IsConvex Φ) (p : ℝ)
    (hp : marginal Φ 0 = (p : EReal))
    (hi : (0 : Y) ∈ relativeInterior (candidateDomain Φ)) :
    ∀ u, marginal Φ u ≠ ⊥ := by
  intro u hu
  obtain ⟨x,r,hx,_⟩ := exists_candidate_lt Φ u 0 (by rw [hu]; exact EReal.bot_lt_coe _)
  have huS : u ∈ candidateDomain Φ := ⟨x, hx ▸ WithTop.coe_lt_top r⟩
  have h0S := intrinsicInterior_subset hi
  obtain ⟨ε,hε,hv⟩ :=
    (mem_relativeInterior_iff_extendible _ (convex_candidateDomain Φ hc) 0 h0S).mp hi u huS
  obtain ⟨z,hz⟩ := hv
  obtain ⟨s,hs⟩ := (mem_domain_iff Φ (z,0 + ε • (0-u))).mp hz
  have hd : 0 < 1+ε := by linarith
  have hab : ε/(1+ε) + 1/(1+ε) = 1 := by field_simp; ring
  have heq : (ε/(1+ε)) • u + (1/(1+ε)) • (0 + ε • (0-u)) = 0 := by
    simp only [zero_add, zero_sub, smul_neg, smul_smul]
    rw [← sub_eq_add_neg, ← sub_smul]
    have hz : ε/(1+ε) - 1/(1+ε)*ε = 0 := by ring
    rw [hz, zero_smul]
  have hh := marginal_eq_bot_of_left Φ hc u _ hu z s hs
    (ε/(1+ε)) (1/(1+ε)) (div_pos hε hd) (by positivity) hab
  rw [heq, hp] at hh
  exact EReal.coe_ne_bot p hh

/-- A convex marginal admits ambient support at a relative-interior point.
The functional is first constructed on the effective span and then extended. -/
lemma marginal_support_of_relativeInterior
    {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (Φ : X × Y → WithTop ℝ) (hc : IsConvex Φ) (p : ℝ)
    (hp : marginal Φ 0 = (p : EReal))
    (hi : (0 : Y) ∈ relativeInterior (candidateDomain Φ)) :
    ∃ y : Y →L[ℝ] ℝ, ∀ u, ((p + y u : ℝ) : EReal) ≤ marginal Φ u := by
  have hnb := marginal_ne_bot_of_relativeInterior Φ hc p hp hi
  let f := marginalFunction Φ
  have hrep (u : Y) : toEReal (f u) = Specs.marginal Φ u :=
    marginalFunction_representation Φ hnb u
  have hf0 : f 0 = (p : WithTop ℝ) := WithBot.coe_injective ((hrep 0).trans hp)
  have hfc : IsConvex f := by
    apply (convex_iff_twoPoint f).mpr
    intro u v r s hu hv a b ha hb hab
    have hmu : Specs.marginal Φ u = (r : EReal) :=
      (hrep u).symm.trans (congrArg toEReal hu)
    have hmv : Specs.marginal Φ v = (s : EReal) :=
      (hrep v).symm.trans (congrArg toEReal hv)
    have hh := marginal_convex_finite Φ hc u v r s hmu hmv a b ha hb hab
    rw [← hrep (a • u + b • v)] at hh
    exact WithBot.coe_le_coe.mp hh
  have hdom : effectiveDomain f = candidateDomain Φ := by
    ext u
    constructor
    · intro hu
      have hh : Specs.marginal Φ u < ⊤ := by rw [← hrep u]; exact WithBot.coe_lt_coe.mpr hu
      obtain ⟨r,hr⟩ := EReal.exists_between_coe_real hh
      obtain ⟨x,s,hs,_⟩ := exists_candidate_lt Φ u r hr.1
      exact ⟨x, hs ▸ WithTop.coe_lt_top s⟩
    · rintro ⟨x,hx⟩
      have hh := marginal_le_candidate Φ x u
      rw [← hrep u] at hh
      exact lt_of_le_of_lt (WithBot.coe_le_coe.mp hh) hx
  let S := candidateDomain Φ
  let H := Submodule.span ℝ S
  have h0S : (0 : Y) ∈ S := intrinsicInterior_subset hi
  have hspan : affineSpan ℝ S = H.toAffineSubspace :=
    affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ S h0S)
  have hiH : (0 : H) ∈ interior ((Subtype.val : H → Y) ⁻¹' S) := by
    have hset : (affineSpan ℝ S : Set Y) = (H : Set Y) := by rw [hspan]; rfl
    change (0 : Y) ∈ (Subtype.val '' interior ((Subtype.val : affineSpan ℝ S → Y) ⁻¹' S)) at hi
    change (0 : Y) ∈ (Subtype.val '' interior ((Subtype.val : ↥(affineSpan ℝ S : Set Y) → Y) ⁻¹' S)) at hi
    rw [hset] at hi
    obtain ⟨a,ha,hval⟩ := hi
    have heq : a = (0 : H) := Subtype.ext hval
    rw [heq] at ha
    convert ha using 1
  let fH : H → WithTop ℝ := fun u => f u
  have hcH : IsConvex fH := by
    apply (convex_iff_twoPoint fH).mpr
    intro u v r s hu hv a b ha hb hab
    exact (convex_iff_twoPoint f).mp hfc u v r s hu hv a b ha hb hab
  have hD : effectiveDomain fH = (Subtype.val : H → Y) ⁻¹' S := by
    change (Subtype.val : H → Y) ⁻¹' effectiveDomain f = _
    rw [hdom]
  have hiD : (0 : H) ∈ interior (effectiveDomain fH) := by rwa [hD]
  have hcv := convexOn_untopD_comp hcH (AffineMap.id ℝ H)
    (convex_effectiveDomain hcH) (fun _ hx => hx)
  have hcont : ContinuousAt (fun u : H => (fH u).untopD 0) 0 :=
    (hcv.continuousOn_interior 0 hiD).continuousAt (isOpen_interior.mem_nhds hiD)
  have hevent : ∀ᶠ u : H in 𝓝 0, fH u ≤ ((p+1 : ℝ) : WithTop ℝ) := by
    have hsmall : ∀ᶠ u : H in 𝓝 0, (fH u).untopD 0 < p+1 :=
      hcont.eventually (gt_mem_nhds (by simp [fH, hf0]))
    filter_upwards [hsmall, isOpen_interior.mem_nhds hiD] with u hu hd
    have hfin : u ∈ effectiveDomain fH := interior_subset hd
    obtain ⟨r,hr⟩ := (mem_domain_iff fH u).mp hfin
    rw [hr, WithTop.untopD_coe] at hu
    rw [hr]
    exact WithTop.coe_le_coe.mpr hu.le
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  obtain ⟨l,hl⟩ := exists_subgradient_of_local_upper_bound fH hcH p r (p+1)
    hf0 hr (fun u hu => hball (by simpa using hu))
  let y : Y →L[ℝ] ℝ := (Subspace.dualLift H l.toLinearMap).toContinuousLinearMap
  refine ⟨y, fun u => ?_⟩
  change ((p + y u : ℝ) : EReal) ≤ Specs.marginal Φ u
  by_cases hu : u ∈ H
  · let uH : H := ⟨u,hu⟩
    have hh := (mem_subdifferential_iff (show fH 0 = (p : WithTop ℝ) from hf0) l).mp hl uH
    simp only [sub_zero] at hh
    have hy : y u = l uH := Subspace.dualLift_of_mem hu
    rw [hy, ← hrep u]
    exact WithBot.coe_le_coe.mpr hh
  · have htop : f u = ⊤ := by
      by_contra hn
      have hs : u ∈ S := by
        change u ∈ candidateDomain Φ
        rw [← hdom]
        exact lt_top_iff_ne_top.mpr hn
      exact hu (Submodule.subset_span hs)
    rw [← hrep u, htop]
    exact le_top

section Fenchel
variable {X : Type u} {Y : Type v}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- The composition perturbation with the manuscript's sign convention. -/
def fenchelPerturbation (A : X →ₗ[ℝ] Y) (f : X → WithTop ℝ) (g : Y → WithTop ℝ)
    (z : X × Y) : WithTop ℝ := f z.1 + g (A z.1 + z.2)

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
lemma convex_fenchelPerturbation (A : X →ₗ[ℝ] Y)
    (f : X → WithTop ℝ) (g : Y → WithTop ℝ)
    (hf : IsConvex f) (hg : IsConvex g) : IsConvex (fenchelPerturbation A f g) := by
  apply (convex_iff_twoPoint _).mpr
  intro x z r s hx hz a b ha hb hab
  obtain ⟨r₁,r₂,hr₁,hr₂,hr⟩ := WithTop.add_eq_coe.mp hx
  obtain ⟨s₁,s₂,hs₁,hs₂,hs⟩ := WithTop.add_eq_coe.mp hz
  have h₁ := convex_upper_bound hf hr₁.symm.le hs₁.symm.le ha hb hab
  have h₂ := convex_upper_bound hg hr₂.symm.le hs₂.symm.le ha hb hab
  have hmap : A (a • x.1 + b • z.1) + (a • x.2 + b • z.2) =
      a • (A x.1 + x.2) + b • (A z.1 + z.2) := by simp only [map_add,map_smul,smul_add]; module
  change f (a • x.1 + b • z.1) + g (A (a • x.1 + b • z.1) + (a • x.2 + b • z.2)) ≤ _
  rw [hmap]
  have hh := add_le_add h₁ h₂
  rw [← WithTop.coe_add] at hh
  convert hh using 1
  congr 1
  rw [← hr, ← hs]
  ring

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
lemma candidateDomain_fenchelPerturbation (A : X →ₗ[ℝ] Y)
    (f : X → WithTop ℝ) (g : Y → WithTop ℝ) :
    candidateDomain (fenchelPerturbation A f g) =
      (LinearMap.snd ℝ X Y - A.comp (LinearMap.fst ℝ X Y)) ''
        (effectiveDomain f ×ˢ effectiveDomain g) := by
  ext u
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨hf,hg⟩ := WithTop.add_lt_top.mp hx
    exact ⟨(x,A x+u), ⟨hf,hg⟩, by simp⟩
  · rintro ⟨⟨x,z⟩,⟨hx,hz⟩,heq⟩
    refine ⟨x, ?_⟩
    change f x + g (A x + u) < ⊤
    have he : z - A x = u := heq
    have he' : A x + u = z := by rw [← he]; abel
    rw [he']
    exact WithTop.add_lt_top.mpr ⟨hx,hz⟩

lemma relativeInterior_candidateDomain_fenchel (A : X →ₗ[ℝ] Y)
    (f : X → WithTop ℝ) (g : Y → WithTop ℝ)
    (hfp : Proper f) (hf : IsConvex f) (hgp : Proper g) (hg : IsConvex g)
    (hq : (A '' relativeInterior (effectiveDomain f) ∩
      relativeInterior (effectiveDomain g)).Nonempty) :
    (0 : Y) ∈ relativeInterior (candidateDomain (fenchelPerturbation A f g)) := by
  have hfn : (effectiveDomain f).Nonempty := hfp
  have hgn : (effectiveDomain g).Nonempty := hgp
  let B := LinearMap.snd ℝ X Y - A.comp (LinearMap.fst ℝ X Y)
  rw [candidateDomain_fenchelPerturbation]
  change (0 : Y) ∈ relativeInterior (B.toAffineMap '' (effectiveDomain f ×ˢ effectiveDomain g))
  rw [relativeInterior_affine_image B.toAffineMap _
      ((convex_effectiveDomain hf).prod (convex_effectiveDomain hg)) (hfn.prod hgn),
    relativeInterior_product _ _ (convex_effectiveDomain hf) hfn (convex_effectiveDomain hg) hgn]
  obtain ⟨_,⟨x,hx,rfl⟩,hgx⟩ := hq
  exact ⟨(x,A x), ⟨hx,hgx⟩, by simp [B]⟩

omit [FiniteDimensional ℝ Y] in
/-- Weak Fenchel duality in the extended reals, before any qualification. -/
lemma fenchel_dual_le_primal (A : X →ₗ[ℝ] Y)
    (f : X → WithTop ℝ) (g : Y → WithTop ℝ) (y : Y →L[ℝ] ℝ) :
    -conjugate f (-(y.comp A.toContinuousLinearMap)) - conjugate g y ≤
      ⨅ x, toEReal (f x + g (A x)) := by
  apply le_iInf
  intro x
  by_cases hx : f x = ⊤
  · simp [hx, toEReal, ConvexAnalysis.Specs.toEReal]
  by_cases hz : g (A x) = ⊤
  · simp [hz, toEReal, ConvexAnalysis.Specs.toEReal]
  obtain ⟨r,hr⟩ := WithTop.ne_top_iff_exists.mp hx
  obtain ⟨s,hs⟩ := WithTop.ne_top_iff_exists.mp hz
  have h₁ := conjugate_finite_lower_bound f x r hr.symm (-(y.comp A.toContinuousLinearMap))
  have h₂ := conjugate_finite_lower_bound g (A x) s hs.symm y
  have hh := add_le_add (EReal.neg_le_neg_iff.mpr h₁) (EReal.neg_le_neg_iff.mpr h₂)
  change -conjugate f (-(y.comp A.toContinuousLinearMap)) + -conjugate g y ≤ _
  apply hh.trans
  rw [← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add, ← hr, ← hs, ← WithTop.coe_add]
  change ((-(-y (A x) - r) + -(y (A x) - s) : ℝ) : EReal) ≤ ((r+s : ℝ) : EReal)
  apply EReal.coe_le_coe_iff.mpr
  linarith

omit [FiniteDimensional ℝ Y] in
/-- Supporting the perturbation bounds both separated conjugates by finite
numbers, so their sum and the dual value have ordinary real arithmetic. -/
lemma fenchel_dual_ge_of_support (A : X →ₗ[ℝ] Y)
    (f : X → WithTop ℝ) (g : Y → WithTop ℝ) (hfp : Proper f) (hgp : Proper g)
    (p : ℝ) (y : Y →L[ℝ] ℝ)
    (hsupp : ∀ u, ((p + y u : ℝ) : EReal) ≤ marginal (fenchelPerturbation A f g) u) :
    (p : EReal) ≤ -conjugate f (-(y.comp A.toContinuousLinearMap)) - conjugate g y := by
  let a : X →L[ℝ] ℝ := -(y.comp A.toContinuousLinearMap)
  have hpair (x : X) (z : Y) (r s : ℝ)
      (hx : f x = (r : WithTop ℝ)) (hz : g z = (s : WithTop ℝ)) :
      -y (A x) - r + (y z - s) ≤ -p := by
    have hh := (hsupp (z-A x)).trans
      (marginal_le_candidate (fenchelPerturbation A f g) x (z-A x))
    have he : A x + (z-A x) = z := by abel
    change ((p+y (z-A x) : ℝ) : EReal) ≤ toEReal (f x + g (A x + (z-A x))) at hh
    rw [he,hx,hz,← WithTop.coe_add] at hh
    have hh' := EReal.coe_le_coe_iff.mp hh
    rw [map_sub] at hh'
    linarith
  have hcf (z : Y) (s : ℝ) (hz : g z = (s : WithTop ℝ)) :
      conjugate f a ≤ ((-p - (y z-s) : ℝ) : EReal) := by
    apply iSup₂_le
    intro x hx
    obtain ⟨r,hr⟩ := (mem_domain_iff f x).mp hx
    have hh := hpair x z r s hr hz
    change ((-y (A x) - (f x).untopD 0 : ℝ) : EReal) ≤ _
    rw [hr, WithTop.untopD_coe]
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  obtain ⟨z₀,s₀,hs₀⟩ := (proper_iff_exists_real g).mp hgp
  have hcfnt : conjugate f a ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (hcf z₀ s₀ hs₀)
  let c := (conjugate f a).toReal
  have hc : conjugate f a = (c : EReal) :=
    (EReal.coe_toReal hcfnt (conjugate_ne_bot f hfp a)).symm
  have hcg : conjugate g y ≤ ((-p-c : ℝ) : EReal) := by
    apply iSup₂_le
    intro z hz
    obtain ⟨s,hs⟩ := (mem_domain_iff g z).mp hz
    have hh := hcf z s hs
    rw [hc] at hh
    have hh' := EReal.coe_le_coe_iff.mp hh
    change ((y z - (g z).untopD 0 : ℝ) : EReal) ≤ _
    rw [hs, WithTop.untopD_coe]
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  have hh := add_le_add (le_refl (-(c : EReal))) (EReal.neg_le_neg_iff.mpr hcg)
  change (p : EReal) ≤ -conjugate f a + -conjugate g y
  rw [hc]
  apply le_trans ?_ hh
  rw [← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  linarith

/-- Finite-dimensional Fenchel--Rockafellar duality under the relative-interior
qualification, with a dual maximizer and no primal attainment assumption. -/
lemma finite_fenchel_normed (A : X →ₗ[ℝ] Y) (f : X → WithTop ℝ) (g : Y → WithTop ℝ)
    (hfp : Proper f) (hf : IsConvex f) (hgp : Proper g) (hg : IsConvex g)
    (hq : (A '' relativeInterior (effectiveDomain f) ∩
      relativeInterior (effectiveDomain g)).Nonempty)
    (p : ℝ) (hp : (⨅ x, toEReal (f x + g (A x))) = (p : EReal)) :
    ∃ y : Y →L[ℝ] ℝ,
      (p : EReal) = -conjugate f (-(y.comp A.toContinuousLinearMap)) - conjugate g y ∧
      (⨆ z : Y →L[ℝ] ℝ,
        -conjugate f (-(z.comp A.toContinuousLinearMap)) - conjugate g z) = (p : EReal) := by
  let Φ := fenchelPerturbation A f g
  have hc : IsConvex Φ := convex_fenchelPerturbation A f g hf hg
  have h0 : marginal Φ 0 = (p : EReal) := by
    change (⨅ x, toEReal (f x + g (A x + 0))) = _
    simpa only [add_zero] using hp
  have hi := relativeInterior_candidateDomain_fenchel A f g hfp hf hgp hg hq
  obtain ⟨y,hy⟩ := marginal_support_of_relativeInterior Φ hc p h0 hi
  have hweak (z : Y →L[ℝ] ℝ) :
      -conjugate f (-(z.comp A.toContinuousLinearMap)) - conjugate g z ≤ (p : EReal) := by
    exact (fenchel_dual_le_primal A f g z).trans_eq hp
  have heq := le_antisymm (hweak y) (fenchel_dual_ge_of_support A f g hfp hgp p y hy)
  refine ⟨y, heq.symm, ?_⟩
  change (⨆ z : Y →L[ℝ] ℝ,
    -conjugate f (-(z.comp A.toContinuousLinearMap)) - conjugate g z) = (p : EReal)
  apply le_antisymm (iSup_le hweak)
  rw [← heq]
  exact le_iSup (fun z : Y →L[ℝ] ℝ =>
    -conjugate f (-(z.comp A.toContinuousLinearMap)) - conjugate g z) y

end Fenchel

/-- The manuscript's theorem for the given finite-dimensional Hausdorff
vector topologies. Compatible norms are introduced only inside the proof. -/
theorem finite_fenchel : Specs.finite_fenchel.{u,v} := by
  intro X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ A f g hfp hf hgp hg hq p hp
  let : IsNormableSpace ℝ X := isNormableSpace_of_finiteDimensional
  let : SeminormedAddCommGroup X := IsNormableSpace.toSeminormedAddCommGroup ℝ X
  let : NormedSpace ℝ X := IsNormableSpace.toNormedSpace ℝ X
  let : NormedAddCommGroup X := { MetricSpace.ofT0PseudoMetricSpace X with
    dist_eq := dist_eq_norm_neg_add }
  let : IsNormableSpace ℝ Y := isNormableSpace_of_finiteDimensional
  let : SeminormedAddCommGroup Y := IsNormableSpace.toSeminormedAddCommGroup ℝ Y
  let : NormedSpace ℝ Y := IsNormableSpace.toNormedSpace ℝ Y
  let : NormedAddCommGroup Y := { MetricSpace.ofT0PseudoMetricSpace Y with
    dist_eq := dist_eq_norm_neg_add }
  exact finite_fenchel_normed A f g hfp hf hgp hg hq p hp

end VariationalNotes.Ch04
