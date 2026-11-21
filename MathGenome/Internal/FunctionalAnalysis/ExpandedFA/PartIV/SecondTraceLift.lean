import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SecondTraceLift
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SecondTraceTransport
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevTraceAndKernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SecondTraceGeometry
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal

namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.SecondTraceFlat
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem IsC2Domain.isC1Domain (hΩ : IsC2Domain Ω) : C1Extension.IsC1Domain Ω := by
  intro x hx
  obtain ⟨i, Φ, hxΦ, hzero, hΦ, hInv, hside⟩ := hΩ x hx
  exact ⟨i, Φ, hxΦ, hzero, hΦ.of_le (by norm_num), hInv.of_le (by norm_num), hside⟩

/-- The existential graph witnesses in the specification are uniquely
determined by u, so the jet predicate uses exactly its actual derivatives. -/
theorem hasDomainJets_iff
    (ν : Domain d → Domain d)
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
    (u : SpaceValue 𝕜 d Ω 2 p) (g h : BoundaryLp 𝕜 Ω p) :
    HasDomainJets ν T u g h ↔
      T (orderOnePart u) = g ∧
      h =ᵐ[surfaceMeasure Ω] fun x =>
        ∑ j : Fin d, (ν x j : 𝕜) * T (derivativePart j u) x := by
  constructor
  · rintro ⟨v, w, hv, hw, hg, hh⟩
    have hv' : v = orderOnePart u := by
      apply sobolev_underlying_injective 𝕜 d Ω 1 p
      simpa only [orderOnePart_apply, orderOneToTwo_zero] using hv
    have hw' : w = fun j => derivativePart j u := by
      funext j
      apply sobolev_underlying_injective 𝕜 d Ω 1 p
      simpa only [derivativePart_apply, derivativePartIndex_zero] using hw j
    rw [hw'] at hh
    exact ⟨hv' ▸ hg, hh⟩
  · rintro ⟨hg, hh⟩
    exact ⟨orderOnePart u, fun j => derivativePart j u,
      by simp only [orderOnePart_apply, orderOneToTwo_zero],
      fun j => by simp only [derivativePart_apply, derivativePartIndex_zero], hg, hh⟩

/-- In particular, no choice of first-order graph witnesses can change
either prescribed boundary class. -/
theorem hasDomainJets_unique
    {ν : Domain d → Domain d}
    {T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p}
    {u : SpaceValue 𝕜 d Ω 2 p} {g h g' h' : BoundaryLp 𝕜 Ω p}
    (h₁ : HasDomainJets ν T u g h) (h₂ : HasDomainJets ν T u g' h') :
    g = g' ∧ h = h' := by
  rw [hasDomainJets_iff] at h₁ h₂
  exact ⟨h₁.1.symm.trans h₂.1, Lp.ext (h₁.2.trans h₂.2.symm)⟩

theorem hasDomainJets_zero (ν : Domain d → Domain d)
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) :
    HasDomainJets ν T 0 0 0 := by
  rw [hasDomainJets_iff]
  have hv : orderOnePart (0 : SpaceValue 𝕜 d Ω 2 p) = 0 :=
    (orderOnePartCLM 𝕜 d Ω p).map_zero
  have hw (j : Fin d) : derivativePart j (0 : SpaceValue 𝕜 d Ω 2 p) = 0 :=
    (derivativePartCLM 𝕜 d Ω p j).map_zero
  refine ⟨by rw [hv, map_zero], ?_⟩
  simp_rw [hw, map_zero]
  change (0 : BoundaryLp 𝕜 Ω p) =ᵐ[surfaceMeasure Ω] fun x =>
    ∑ j : Fin d, (ν x j : 𝕜) * (0 : BoundaryLp 𝕜 Ω p) x
  filter_upwards [Lp.coeFn_zero 𝕜 p (surfaceMeasure Ω)] with x hx
  change (0 : BoundaryLp 𝕜 Ω p) x = 0 at hx
  simp only [hx, mul_zero, Finset.sum_const_zero]

/-- Addition is the finite-patch assembly rule; no regularity or
compatibility of the independent data is needed for this algebraic step. -/
theorem hasDomainJets_add
    {ν : Domain d → Domain d}
    {T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p}
    {u v : SpaceValue 𝕜 d Ω 2 p} {g h g' h' : BoundaryLp 𝕜 Ω p}
    (hu : HasDomainJets ν T u g h) (hv : HasDomainJets ν T v g' h') :
    HasDomainJets ν T (u + v) (g + g') (h + h') := by
  rw [hasDomainJets_iff] at hu hv ⊢
  have hvalue : orderOnePart (u + v) = orderOnePart u + orderOnePart v :=
    (orderOnePartCLM 𝕜 d Ω p).map_add u v
  have hder (j : Fin d) : T (derivativePart j (u + v)) =
      T (derivativePart j u) + T (derivativePart j v) := by
    rw [show derivativePart j (u + v) = derivativePart j u + derivativePart j v from
      (derivativePartCLM 𝕜 d Ω p j).map_add u v, map_add]
  refine ⟨by rw [hvalue, map_add, hu.1, hv.1], ?_⟩
  simp_rw [hder]
  filter_upwards [hu.2, hv.2, Lp.coeFn_add h h',
    ae_all_iff.mpr (fun j => Lp.coeFn_add
      (T (derivativePart j u)) (T (derivativePart j v)))] with x hux hvx hs hd
  simp only [Pi.add_apply] at hs hd
  rw [hs, hux, hvx, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => by rw [hd j, mul_add])

theorem hasDomainJets_smul
    {ν : Domain d → Domain d}
    {T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p}
    {u : SpaceValue 𝕜 d Ω 2 p} {g h : BoundaryLp 𝕜 Ω p}
    (c : 𝕜) (hu : HasDomainJets ν T u g h) :
    HasDomainJets ν T (c • u) (c • g) (c • h) := by
  rw [hasDomainJets_iff] at hu ⊢
  have hvalue : orderOnePart (c • u) = c • orderOnePart u :=
    (orderOnePartCLM 𝕜 d Ω p).map_smul c u
  have hder (j : Fin d) : T (derivativePart j (c • u)) =
      c • T (derivativePart j u) := by
    rw [show derivativePart j (c • u) = c • derivativePart j u from
      (derivativePartCLM 𝕜 d Ω p j).map_smul c u, map_smul]
  refine ⟨by rw [hvalue, map_smul, hu.1], ?_⟩
  simp_rw [hder]
  filter_upwards [hu.2, Lp.coeFn_smul c h,
    ae_all_iff.mpr (fun j => Lp.coeFn_smul c (T (derivativePart j u)))] with x hux hs hd
  simp only [Pi.smul_apply, smul_eq_mul] at hs hd
  rw [hs, hux, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [hd j]; ring)

theorem hasDomainJets_finsetSum {ι : Type*} (s : Finset ι)
    {ν : Domain d → Domain d}
    {T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p}
    (u : ι → SpaceValue 𝕜 d Ω 2 p) (g h : ι → BoundaryLp 𝕜 Ω p)
    (hjets : ∀ j ∈ s, HasDomainJets ν T (u j) (g j) (h j)) :
    HasDomainJets ν T (∑ j ∈ s, u j) (∑ j ∈ s, g j) (∑ j ∈ s, h j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasDomainJets_zero ν T
  | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact hasDomainJets_add (hjets j (Finset.mem_insert_self _ _))
        (ih (fun k hk => hjets k (Finset.mem_insert_of_mem hk)))

/-- All prescribed surface classes vanish when the boundary measure is
zero. The zero W²,p graph then realizes both jets. -/
theorem domain_jets_onto_of_surfaceMeasure_zero
    (hμ : surfaceMeasure Ω = 0) (ν : Domain d → Domain d)
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
    (g h : BoundaryLp 𝕜 Ω p) :
    ∃ u : SpaceValue 𝕜 d Ω 2 p, HasDomainJets ν T u g h := by
  have hz (f : BoundaryLp 𝕜 Ω p) : f = 0 := by
    apply Lp.ext
    simp [Filter.EventuallyEq, hμ]
  rw [hz g, hz h]
  exact ⟨0, hasDomainJets_zero ν T⟩

theorem domain_jets_onto_zero_dimension
    (Ω : Opens (Domain 0)) (ν : Domain 0 → Domain 0)
    (T : SpaceValue 𝕜 0 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
    (g h : BoundaryLp 𝕜 Ω p) :
    ∃ u : SpaceValue 𝕜 0 Ω 2 p, HasDomainJets ν T u g h :=
  domain_jets_onto_of_surfaceMeasure_zero (surfaceMeasure_zero_dim Ω) ν T g h

theorem domain_jets_onto_empty_frontier
    (hΩ : frontier (Ω : Set (Domain d)) = ∅) (ν : Domain d → Domain d)
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
    (g h : BoundaryLp 𝕜 Ω p) :
    ∃ u : SpaceValue 𝕜 d Ω 2 p, HasDomainJets ν T u g h := by
  apply domain_jets_onto_of_surfaceMeasure_zero _ ν T g h
  simp [surfaceMeasure, hΩ]

/-- The normal trace is an actual bounded operator on the original surface
Lp quotient. Only the geometric component measurability and unit bounds
are used to construct this order-zero contraction. -/
def normalTrace (ν : Domain d → Domain d) (hν : IsOutwardNormal Ω ν)
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) :
    SpaceValue 𝕜 d Ω 2 p →L[𝕜] BoundaryLp 𝕜 Ω p :=
  ∑ j : Fin d, (C1Extension.Transport.aeSmulLpCLM (fun x => ν x j)
    (hν.1 j).aestronglyMeasurable 1
    (by simpa only [Real.norm_eq_abs] using hν.2.1 j)).comp
      (T.comp (derivativePartCLM 𝕜 d Ω p j))

theorem normalTrace_representative (ν : Domain d → Domain d)
    (hν : IsOutwardNormal Ω ν)
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
    (u : SpaceValue 𝕜 d Ω 2 p) :
    normalTrace ν hν T u =ᵐ[surfaceMeasure Ω] fun x =>
      ∑ j : Fin d, (ν x j : 𝕜) * T (derivativePart j u) x := by
  classical
  unfold normalTrace
  rw [ContinuousLinearMap.sum_apply]
  apply (Lp.coeFn_fun_finsetSum Finset.univ _).trans
  have hj (j : Fin d) := C1Extension.Transport.aeSmulLp_coe
    (fun x => ν x j) (hν.1 j).aestronglyMeasurable 1
    (by simpa only [Real.norm_eq_abs] using hν.2.1 j) (T (derivativePart j u))
  filter_upwards [ae_all_iff.mpr hj] with x hx
  apply Finset.sum_congr rfl
  intro j _
  exact (hx j).trans (RCLike.real_smul_eq_coe_mul _ _)

theorem hasDomainJets_iff_normalTrace (ν : Domain d → Domain d)
    (hν : IsOutwardNormal Ω ν)
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
    (u : SpaceValue 𝕜 d Ω 2 p) (g h : BoundaryLp 𝕜 Ω p) :
    HasDomainJets ν T u g h ↔
      T (orderOnePart u) = g ∧ normalTrace ν hν T u = h := by
  rw [hasDomainJets_iff]
  exact and_congr_right (fun _ => ⟨
    fun hh => Lp.ext ((normalTrace_representative ν hν T u).trans hh.symm),
    fun hh => hh ▸ normalTrace_representative ν hν T u⟩)

/-- Inward flat jets from the supplied simultaneous lift realize arbitrary
outward flat data after negating the second input. The same full norm
bound holds, since negation is an isometry of the fractional data space. -/
theorem flat_outward_jet_lift (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (i : Fin (n + 1))
      (T : SpaceValue 𝕜 (n + 1) (HalfSpace.upper i) 1 p →L[𝕜]
        Lp 𝕜 p (volume : Measure (Lines.Transverse i))),
      SharpTraceBound.CoordinateTraceCondition i T →
      ∀ (g : FractionalSobolev.HigherFractionalSpace 𝕜 n (2 - 1 / p.toReal) p)
        (h : FractionalSobolev.FractionalSpace 𝕜 n (1 - 1 / p.toReal) p),
      ∃ u : SpaceValue 𝕜 (n + 1) (HalfSpace.upper i) 2 p,
        SharpTraceBound.reindexedTrace i T (orderOnePart u) =
          FractionalSobolev.wholeLp (g.val.val (zeroIndex n 1)) ∧
        -SharpTraceBound.reindexedTrace i T (derivativePart i u) = h.val ∧
        ‖u‖ ≤ C * (FractionalSobolev.higherFractionalNorm (2 - 1 / p.toReal) p g +
          FractionalSobolev.fractionalNorm (1 - 1 / p.toReal) p h) := by
  obtain ⟨C, hC, hE⟩ := bounded_jet_extension n p hp1 hp
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ i T hT g h
  letI : Fact (p ≠ ∞) := ⟨hp⟩
  obtain ⟨_, E, _, _, hbound, _, hjets⟩ := hE 𝕜 i
  have hj := (hasBoundaryJets_iff i T _ _ _).mp (hjets T hT g (-h))
  refine ⟨E g (-h), hj.1, ?_, ?_⟩
  · rw [hj.2]
    exact neg_neg h.val
  · have hnorm : FractionalSobolev.fractionalNorm (1 - 1 / p.toReal) p (-h) =
        FractionalSobolev.fractionalNorm (1 - 1 / p.toReal) p h := norm_neg h
    simpa only [hnorm] using hbound g (-h)

end ExpandedFA.PartIV.SecondTrace

namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.PartIV.FractionalSobolev

def chartNormalCoefficient {d : ℕ}
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (ν : Domain d → Domain d) (i : Fin d) (x : Domain d) : ℝ :=
  fderiv ℝ Φ x (ν x) i

def chartTangentialCoefficient {n : ℕ}
    (Φ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1)))
    (ν : Domain (n+1) → Domain (n+1)) (i : Fin (n+1)) (k : Fin n)
    (x : Domain (n+1)) : ℝ :=
  fderiv ℝ Φ x (ν x) (i.succAbove k)

lemma normal_chain_rule {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (Φ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1)))
    (ν : Domain (n+1) → Domain (n+1)) (i : Fin (n+1))
    (F : Domain (n+1) → 𝕜) (x : Domain (n+1))
    (hΦ : DifferentiableAt ℝ Φ x) (hF : DifferentiableAt ℝ F (Φ x)) :
    fderiv ℝ (F ∘ Φ) x (ν x) =
      chartNormalCoefficient Φ ν i x • fderiv ℝ F (Φ x) (coordinateVector i) +
      ∑ k : Fin n, chartTangentialCoefficient Φ ν i k x •
        fderiv ℝ F (Φ x) (coordinateVector (i.succAbove k)) := by
  rw [fderiv_comp x hF hΦ]
  change fderiv ℝ F (Φ x) (fderiv ℝ Φ x (ν x)) = _
  calc
    _ = fderiv ℝ F (Φ x) (∑ k, (fderiv ℝ Φ x (ν x)) k • coordinateVector k) :=
      congrArg _ (pi_eq_sum_univ' (fderiv ℝ Φ x (ν x)))
    _ = ∑ k, (fderiv ℝ Φ x (ν x)) k • fderiv ℝ F (Φ x) (coordinateVector k) := by
      simp only [map_sum, map_smul]
    _ = _ := Fin.sum_univ_succAbove _ i

lemma chart_normal_coefficient_continuousOn {d : ℕ}
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (ν : Domain d → Domain d)
    (hν : ContinuousOn ν Φ.source) (i : Fin d) :
    ContinuousOn (chartNormalCoefficient Φ ν i) Φ.source := by
  exact (continuous_apply i).comp_continuousOn
    ((hΦ.continuousOn_fderiv_of_isOpen Φ.open_source (by norm_num)).clm_apply hν)

lemma chart_normal_coefficient_away_from_zero {d : ℕ}
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (ν : Domain d → Domain d)
    (hν : ContinuousOn ν Φ.source) (i : Fin d)
    (K : Set (Domain d)) (hK : IsCompact K) (hKs : K ⊆ Φ.source)
    (ha : ∀ x ∈ K, chartNormalCoefficient Φ ν i x ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ |chartNormalCoefficient Φ ν i x| := by
  exact hK.exists_forall_le'
    ((chart_normal_coefficient_continuousOn Φ hΦ ν hν i).abs.mono hKs)
    (fun x hx => abs_pos.mpr (ha x hx))

def inwardChartGradient {d : ℕ}
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (x : Domain d) : Domain d :=
  fun j => fderiv ℝ Φ x (coordinateVector j) i

def chartOutwardNormal {d : ℕ}
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (x : Domain d) : Domain d :=
  fun j => -inwardChartGradient Φ i x j /
    Real.sqrt (∑ k, (inwardChartGradient Φ i x k)^2)

lemma derivative_coordinate_expansion {d : ℕ}
    (A : Domain d →L[ℝ] Domain d) (v : Domain d) (i : Fin d) :
    A v i = ∑ j : Fin d, v j * A (coordinateVector j) i := by
  calc
    _ = A (∑ j, v j • coordinateVector j) i := congrArg (fun w => A w i) (pi_eq_sum_univ' v)
    _ = _ := by simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

lemma inwardChartGradient_sq_sum_pos {d : ℕ}
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (x : Domain d) (hx : x ∈ Φ.source)
    (hΦ : DifferentiableAt ℝ Φ x) (hInv : DifferentiableAt ℝ Φ.symm (Φ x)) :
    0 < ∑ k : Fin d, (inwardChartGradient Φ i x k)^2 := by
  have hcomp : (Φ ∘ Φ.symm) =ᶠ[nhds (Φ x)] id := by
    filter_upwards [Φ.open_target.mem_nhds (Φ.map_source hx)] with y hy
    exact Φ.right_inv hy
  have hder := hcomp.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp (Φ x) (by simpa only [Φ.left_inv hx] using hΦ) hInv,
    Φ.left_inv hx, fderiv_id] at hder
  have hnonzero : (∑ k : Fin d, (inwardChartGradient Φ i x k)^2) ≠ 0 := by
    intro hz
    have hrow : ∀ k, inwardChartGradient Φ i x k = 0 := by
      simpa only [Finset.sum_sq_eq_zero_iff, Finset.mem_univ, forall_const] using hz
    have hval := congrArg (fun A : Domain d →L[ℝ] Domain d => A (coordinateVector i) i) hder
    change fderiv ℝ Φ x (fderiv ℝ Φ.symm (Φ x) (coordinateVector i)) i =
      coordinateVector i i at hval
    rw [derivative_coordinate_expansion] at hval
    change ∀ k, fderiv ℝ Φ x (coordinateVector k) i = 0 at hrow
    simp only [hrow, mul_zero, Finset.sum_const_zero] at hval
    exact zero_ne_one (by simpa only [coordinateVector, Pi.single_eq_same] using hval)
  exact lt_of_le_of_ne (Finset.sum_nonneg (fun k _ => sq_nonneg _)) (Ne.symm hnonzero)

lemma chartNormalCoefficient_outward {d : ℕ}
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (x : Domain d)
    (hpos : 0 < ∑ k : Fin d, (inwardChartGradient Φ i x k)^2) :
    chartNormalCoefficient Φ (chartOutwardNormal Φ i) i x =
      -Real.sqrt (∑ k : Fin d, (inwardChartGradient Φ i x k)^2) := by
  rw [chartNormalCoefficient, derivative_coordinate_expansion]
  change (∑ j : Fin d, -inwardChartGradient Φ i x j /
    Real.sqrt (∑ k, (inwardChartGradient Φ i x k)^2) * inwardChartGradient Φ i x j) = _
  have hs := Real.sq_sqrt hpos.le
  have hsn : Real.sqrt (∑ k, (inwardChartGradient Φ i x k)^2) ≠ 0 :=
    (Real.sqrt_pos.mpr hpos).ne'
  calc
    _ = ∑ j : Fin d, -(inwardChartGradient Φ i x j)^2 /
        Real.sqrt (∑ k : Fin d, (inwardChartGradient Φ i x k)^2) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = -(∑ k : Fin d, (inwardChartGradient Φ i x k)^2) /
        Real.sqrt (∑ k : Fin d, (inwardChartGradient Φ i x k)^2) := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    _ = _ := by
      apply (div_eq_iff hsn).mpr
      nlinarith [hs]


lemma chartOutwardNormal_c1 {d : ℕ}
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target) :
    ContDiffOn ℝ 1 (chartOutwardNormal Φ i) Φ.source := by
  have hpos (x) (hx : x ∈ Φ.source) := inwardChartGradient_sq_sum_pos Φ i x hx
    ((hΦ.contDiffAt (Φ.open_source.mem_nhds hx)).differentiableAt (by norm_num))
    ((hInv.contDiffAt (Φ.open_target.mem_nhds (Φ.map_source hx))).differentiableAt (by norm_num))
  have hq (j : Fin d) : ContDiffOn ℝ 1 (fun x => inwardChartGradient Φ i x j) Φ.source :=
    SecondTraceTransport.chartCoefficient_c1 Φ hΦ j i
  have hQ : ContDiffOn ℝ 1 (fun x => ∑ j : Fin d, (inwardChartGradient Φ i x j)^2)
      Φ.source := ContDiffOn.sum (fun j _ => (hq j).pow 2)
  apply contDiffOn_pi.mpr
  intro j
  exact (hq j).neg.div (hQ.sqrt (fun x hx => (hpos x hx).ne'))
    (fun x hx => (Real.sqrt_pos.mpr (hpos x hx)).ne')

lemma chart_normal_coefficient_c1 {d : ℕ}
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (ν : Domain d → Domain d)
    (hν : ContDiffOn ℝ 1 ν Φ.source) (i : Fin d) :
    ContDiffOn ℝ 1 (chartNormalCoefficient Φ ν i) Φ.source := by
  exact (contDiff_apply ℝ (fun _ : Fin d => ℝ) i).comp_contDiffOn
    ((hΦ.fderiv_of_isOpen Φ.open_source (by norm_num)).clm_apply hν)

lemma chart_normal_coefficient_outward_negative {d : ℕ}
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (x : Domain d) (hx : x ∈ Φ.source) :
    chartNormalCoefficient Φ (chartOutwardNormal Φ i) i x < 0 := by
  have hpos := inwardChartGradient_sq_sum_pos Φ i x hx
    ((hΦ.contDiffAt (Φ.open_source.mem_nhds hx)).differentiableAt (by norm_num))
    ((hInv.contDiffAt (Φ.open_target.mem_nhds (Φ.map_source hx))).differentiableAt (by norm_num))
  rw [chartNormalCoefficient_outward Φ i x hpos]
  exact neg_neg_of_pos (Real.sqrt_pos.mpr hpos)

lemma exists_chart_normal_lower_bound {d : ℕ}
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (K : Set (Domain d)) (hK : IsCompact K) (hKs : K ⊆ Φ.source) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K,
      δ ≤ |chartNormalCoefficient Φ (chartOutwardNormal Φ i) i x| := by
  apply chart_normal_coefficient_away_from_zero Φ hΦ (chartOutwardNormal Φ i)
    (chartOutwardNormal_c1 Φ i hΦ hInv).continuousOn i K hK hKs
  exact fun x hx => (chart_normal_coefficient_outward_negative Φ i hΦ hInv x (hKs hx)).ne

lemma chartOutwardNormal_defining_function {d : ℕ}
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (x : Domain d) (hΦ : DifferentiableAt ℝ Φ x) :
    ∀ j : Fin d, chartOutwardNormal Φ i x j =
      fderiv ℝ (fun y => -Φ y i) x (coordinateVector j) /
        Real.sqrt (∑ k : Fin d, (fderiv ℝ (fun y => -Φ y i) x (coordinateVector k))^2) := by
  have hd : fderiv ℝ (fun y => -Φ y i) x =
      -((ContinuousLinearMap.proj i).comp (fderiv ℝ Φ x)) :=
    ((ContinuousLinearMap.proj i).hasFDerivAt.comp x hΦ.hasFDerivAt).neg.fderiv
  intro j
  simp only [hd, neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, neg_sq]
  rfl

end ExpandedFA.PartIV.SecondTrace

namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.PartIV.FractionalSobolev

lemma c1_lipschitzOn_compact {n : ℕ} (f : Domain n → ℝ)
    (U K : Set (Domain n)) (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (hf : ContDiffOn ℝ 1 f U) :
    ∃ L : ℝ≥0, LipschitzOnWith L f K := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  intro x hx
  obtain ⟨L, V, hV, hLip⟩ := (hf.contDiffAt (hU.mem_nhds (hKU hx))).exists_lipschitzOnWith
  exact ⟨L, V, mem_nhdsWithin_of_mem_nhds hV, hLip⟩

lemma c1_bounded_lipschitz_extension {n : ℕ} (f : Domain n → ℝ)
    (U K : Set (Domain n)) (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (hf : ContDiffOn ℝ 1 f U) :
    ∃ (F : Domain n → ℝ) (M L : ℝ≥0),
      EqOn F f K ∧ (∀ x, ‖F x‖ ≤ M) ∧
      (∀ x y, ‖F x - F y‖ ≤ L * euclideanLength (x-y)) := by
  obtain ⟨L, hL⟩ := c1_lipschitzOn_compact f U K hU hK hKU hf
  obtain ⟨G, hG, hGF⟩ := hL.extend_real
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hf.continuousOn.mono hKU)
  let M : ℝ≥0 := ⟨max 0 B, le_max_left _ _⟩
  let F := fun x => max (-(M : ℝ)) (min (M : ℝ) (G x))
  have hF : LipschitzWith L F := (hG.const_min (M : ℝ)).const_max (-(M : ℝ))
  refine ⟨F, M, L, ?_, ?_, ?_⟩
  · intro x hx
    have hb : |f x| ≤ M := (hB x hx).trans (le_max_right _ _)
    change max (-(M : ℝ)) (min (M : ℝ) (G x)) = f x
    rw [← hGF hx, min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]
  · intro x
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    exact ⟨le_max_left _ _, max_le (by linarith [M.coe_nonneg]) (min_le_left _ _)⟩
  · intro x y
    exact (hF.norm_sub_le x y).trans
      (mul_le_mul_of_nonneg_left (norm_le_euclideanLength (x-y)) L.coe_nonneg)

lemma c1_negative_lipschitz_extension {n : ℕ} (f : Domain n → ℝ)
    (U K : Set (Domain n)) (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (hf : ContDiffOn ℝ 1 f U) (hfneg : ∀ x ∈ K, f x < 0) :
    ∃ (F : Domain n → ℝ) (δ : ℝ) (L : ℝ≥0),
      0 < δ ∧ EqOn F f K ∧ (∀ x, F x ≤ -δ) ∧
      (∀ x y, ‖F x - F y‖ ≤ L * euclideanLength (x-y)) := by
  obtain ⟨δ, hδ, hδf⟩ := hK.exists_forall_le'
    (hf.continuousOn.neg.mono hKU) (fun x hx => neg_pos.mpr (hfneg x hx))
  obtain ⟨L, hL⟩ := c1_lipschitzOn_compact f U K hU hK hKU hf
  obtain ⟨G, hG, hGF⟩ := hL.extend_real
  let F := fun x => min (-δ) (G x)
  have hF : LipschitzWith L F := hG.const_min (-δ)
  refine ⟨F, δ, L, hδ, ?_, fun x => min_le_left _ _, ?_⟩
  · intro x hx
    change min (-δ) (G x) = f x
    have hfx : δ ≤ -f x := hδf x hx
    rw [← hGF hx, min_eq_right (by linarith)]
  · intro x y
    exact (hF.norm_sub_le x y).trans
      (mul_le_mul_of_nonneg_left (norm_le_euclideanLength (x-y)) L.coe_nonneg)

end ExpandedFA.PartIV.SecondTrace

namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.PartIV.FractionalSobolev

lemma inverse_coefficient_bounds {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (a : Domain n → 𝕜) (δ : ℝ) (L : ℝ≥0) (hδ : 0 < δ)
    (ha : ∀ x, δ ≤ ‖a x‖)
    (hL : ∀ x y, ‖a x - a y‖ ≤ L * euclideanLength (x-y)) :
    (∀ x, ‖(a x)⁻¹‖ ≤ δ⁻¹) ∧
    (∀ x y, ‖(a x)⁻¹ - (a y)⁻¹‖ ≤
      ((L : ℝ) / (δ*δ)) * euclideanLength (x-y)) := by
  have ha0 (x) : 0 < ‖a x‖ := hδ.trans_le (ha x)
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · rw [norm_inv]
    exact inv_anti₀ hδ (ha x)
  · rw [inv_sub_inv (norm_pos_iff.mp (ha0 x)) (norm_pos_iff.mp (ha0 y)),
      norm_div, norm_mul, norm_sub_rev]
    calc
      ‖a x - a y‖ / (‖a x‖ * ‖a y‖) ≤
          ((L : ℝ) * euclideanLength (x-y)) / (δ*δ) :=
        div_le_div₀ (mul_nonneg L.coe_nonneg (norm_nonneg _)) (hL x y) (mul_pos hδ hδ)
          (mul_le_mul (ha x) (ha y) hδ.le (ha0 x).le)
      _ = _ := by ring

lemma corrected_datum_algebra {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (a h : 𝕜) (b q : Fin n → 𝕜) (ha : a ≠ 0) :
    a * ((h - ∑ j, b j * q j) / a) + ∑ j, b j * q j = h := by
  field_simp
  ring


/-- The correction has the required genuine fractional membership whenever
its coefficients have the stated global bounds. Applying this to a domain
patch still requires deriving such coefficients from its C² geometry. -/
theorem corrected_fractional_datum {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (g : HigherFractionalSpace 𝕜 n (s+1) p) (h : FractionalSpace 𝕜 n s p)
    (a : Domain n → 𝕜) (b : Fin n → Domain n → 𝕜)
    (δ : ℝ) (hδ : 0 < δ) (La : ℝ≥0)
    (ha : ∀ x, δ ≤ ‖a x‖)
    (haL : ∀ x y, ‖a x - a y‖ ≤ La * euclideanLength (x-y))
    (M L : Fin n → ℝ≥0)
    (hbM : ∀ j x, ‖b j x‖ ≤ M j)
    (hbL : ∀ j x y, ‖b j x - b j y‖ ≤ L j * euclideanLength (x-y)) :
    ∃ k : FractionalSpace 𝕜 n s p,
      k.val =ᵐ[volume] fun x =>
        (h.val x - ∑ j : Fin n, b j x * wholeLp (g.val.val (firstIndex j)) x) / a x := by
  letI : Fact (p ≠ ∞) := ⟨hp⟩
  let q (j : Fin n) : FractionalSpace 𝕜 n s p :=
    ⟨wholeLp (g.val.val (firstIndex j)), by simpa only [add_sub_cancel_right] using g.property j⟩
  let v (j : Fin n) : FractionalSpace 𝕜 n s p :=
    fractionalMultiply s p hs0 hs1 hp (b j) (M j) (L j) (hbM j) (hbL j) (q j)
  let l : FractionalSpace 𝕜 n s p := h - ∑ j : Fin n, v j
  have hv (j : Fin n) : (v j).val =ᵐ[volume] fun x => b j x * (q j).val x :=
    fractionalMultiply_representative s p hs0 hs1 hp (b j) (M j) (L j) (hbM j) (hbL j) (q j)
  have hsum : (∑ j : Fin n, v j).val = ∑ j : Fin n, (v j).val := by
    exact map_sum (finiteEnergySubmodule (𝕜 := 𝕜) (d := n) s p hp).subtype _ _
  have hl : l.val =ᵐ[volume] fun x => h.val x - ∑ j : Fin n, b j x * (q j).val x := by
    change (h.val - (∑ j : Fin n, v j).val) =ᵐ[volume] _
    rw [hsum]
    filter_upwards [Lp.coeFn_sub h.val (∑ j : Fin n, (v j).val),
      Lp.coeFn_fun_finsetSum Finset.univ (fun j : Fin n => (v j).val),
      ae_all_iff.mpr hv] with x hx hs hvx
    simp only [Pi.sub_apply] at hx
    rw [hx, hs]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => hvx j)
  obtain ⟨haM, haLi⟩ := inverse_coefficient_bounds a δ La hδ ha haL
  let Mi : ℝ≥0 := ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩
  let Li : ℝ≥0 := ⟨(La : ℝ)/(δ*δ), div_nonneg La.coe_nonneg (mul_self_nonneg δ)⟩
  let k := fractionalMultiply s p hs0 hs1 hp (fun x => (a x)⁻¹) Mi Li haM haLi l
  refine ⟨k, ?_⟩
  have hk := fractionalMultiply_representative s p hs0 hs1 hp (fun x => (a x)⁻¹)
    Mi Li haM haLi l
  filter_upwards [hk, hl] with x hkx hlx
  rw [hkx, hlx]
  rw [div_eq_mul_inv]
  exact mul_comm _ _

end ExpandedFA.PartIV.SecondTrace

namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.PartIV.FractionalSobolev

def boundaryEmbedding {n : ℕ} (i : Fin (n+1)) (z : Domain n) : Domain (n+1) :=
  i.insertNth 0 z

lemma boundaryEmbedding_contDiff {n : ℕ} (i : Fin (n+1)) :
    ContDiff ℝ (⊤ : ℕ∞) (boundaryEmbedding i) := by
  apply contDiff_pi.mpr
  intro k
  refine Fin.succAboveCases i ?_ (fun j => ?_) k
  · simpa only [boundaryEmbedding, Fin.insertNth_apply_same] using
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Domain n => (0 : ℝ)))
  · simpa only [boundaryEmbedding, Fin.insertNth_apply_succAbove] using
      (contDiff_apply ℝ (fun _ : Fin n => ℝ) j :
        ContDiff ℝ (⊤ : ℕ∞) (fun z : Domain n => z j))

def boundaryChartDomain {n : ℕ}
    (Φ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1))) (i : Fin (n+1)) :
    Set (Domain n) := boundaryEmbedding i ⁻¹' Φ.target

lemma boundaryChartDomain_isOpen {n : ℕ}
    (Φ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1))) (i : Fin (n+1)) :
    IsOpen (boundaryChartDomain Φ i) :=
  Φ.open_target.preimage (boundaryEmbedding_contDiff i).continuous

lemma chart_normal_coefficient_on_boundary_c1 {n : ℕ}
    (Φ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1))) (i : Fin (n+1))
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (k : Fin (n+1)) :
    ContDiffOn ℝ 1
      (fun z => chartNormalCoefficient Φ (chartOutwardNormal Φ i) k
        (Φ.symm (boundaryEmbedding i z))) (boundaryChartDomain Φ i) := by
  have hψ : ContDiffOn ℝ 1 (fun z => Φ.symm (boundaryEmbedding i z))
      (boundaryChartDomain Φ i) :=
    (hInv.of_le (by norm_num)).comp ((boundaryEmbedding_contDiff i).of_le (by simp)).contDiffOn
      (fun _ hz => hz)
  exact (chart_normal_coefficient_c1 Φ hΦ (chartOutwardNormal Φ i)
    (chartOutwardNormal_c1 Φ i hΦ hInv) k).comp hψ (fun _ hz => Φ.map_target hz)

end ExpandedFA.PartIV.SecondTrace

namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.PartIV.FractionalSobolev

lemma exists_boundary_chart_coefficients {n : ℕ}
    (Φ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1))) (i : Fin (n+1))
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (K : Set (Domain n)) (hK : IsCompact K) (hKV : K ⊆ boundaryChartDomain Φ i) :
    ∃ (a : Domain n → ℝ) (b : Fin n → Domain n → ℝ)
      (δ : ℝ) (La : ℝ≥0) (M L : Fin n → ℝ≥0),
      0 < δ ∧ (∀ z, a z ≤ -δ) ∧
      (∀ x y, ‖a x-a y‖ ≤ La * euclideanLength (x-y)) ∧
      EqOn a (fun z => chartNormalCoefficient Φ (chartOutwardNormal Φ i) i
        (Φ.symm (boundaryEmbedding i z))) K ∧
      (∀ j, EqOn (b j) (fun z => chartTangentialCoefficient Φ (chartOutwardNormal Φ i) i j
        (Φ.symm (boundaryEmbedding i z))) K) ∧
      (∀ j x, ‖b j x‖ ≤ M j) ∧
      (∀ j x y, ‖b j x-b j y‖ ≤ L j * euclideanLength (x-y)) := by
  obtain ⟨a, δ, La, hδ, haeq, haneg, haL⟩ := c1_negative_lipschitz_extension
    (fun z => chartNormalCoefficient Φ (chartOutwardNormal Φ i) i (Φ.symm (boundaryEmbedding i z)))
    (boundaryChartDomain Φ i) K (boundaryChartDomain_isOpen Φ i) hK hKV
    (chart_normal_coefficient_on_boundary_c1 Φ i hΦ hInv i)
    (fun z hz => chart_normal_coefficient_outward_negative Φ i hΦ hInv _ (Φ.map_target (hKV hz)))
  have hb (j : Fin n) := c1_bounded_lipschitz_extension
    (fun z => chartNormalCoefficient Φ (chartOutwardNormal Φ i) (i.succAbove j)
      (Φ.symm (boundaryEmbedding i z)))
    (boundaryChartDomain Φ i) K (boundaryChartDomain_isOpen Φ i) hK hKV
    (chart_normal_coefficient_on_boundary_c1 Φ i hΦ hInv (i.succAbove j))
  choose b M L hbeq hbM hbL using hb
  exact ⟨a, b, δ, La, M, L, hδ, haneg, haL, haeq, hbeq, hbM, hbL⟩

/-- The coefficient correction on a compact chart piece is a member of the
original fractional space. The coefficients are derived from the actual
C² chart, including its outward sign; no multiplier certificate is assumed. -/
theorem local_chart_corrected_datum {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (Φ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1))) (i : Fin (n+1))
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (K : Set (Domain n)) (hK : IsCompact K) (hKV : K ⊆ boundaryChartDomain Φ i)
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (g : HigherFractionalSpace 𝕜 n (s+1) p) (h : FractionalSpace 𝕜 n s p) :
    ∃ k : FractionalSpace 𝕜 n s p, ∀ᵐ z ∂volume, z ∈ K →
      (chartNormalCoefficient Φ (chartOutwardNormal Φ i) i
        (Φ.symm (boundaryEmbedding i z)) : 𝕜) * k.val z +
      ∑ j : Fin n, (chartTangentialCoefficient Φ (chartOutwardNormal Φ i) i j
        (Φ.symm (boundaryEmbedding i z)) : 𝕜) * wholeLp (g.val.val (firstIndex j)) z = h.val z := by
  obtain ⟨a, b, δ, La, M, L, hδ, haneg, haL, haeq, hbeq, hbM, hbL⟩ :=
    exists_boundary_chart_coefficients Φ i hΦ hInv K hK hKV
  have haM (z) : δ ≤ ‖(a z : 𝕜)‖ := by
    rw [RCLike.norm_ofReal, abs_of_neg (lt_of_le_of_lt (haneg z) (neg_neg_of_pos hδ))]
    linarith [haneg z]
  have haLip (x y) : ‖(a x : 𝕜) - (a y : 𝕜)‖ ≤ La * euclideanLength (x-y) := by
    rw [← RCLike.ofReal_sub, RCLike.norm_ofReal]
    exact haL x y
  have hbBound (j x) : ‖(b j x : 𝕜)‖ ≤ M j := by
    rw [RCLike.norm_ofReal]
    exact hbM j x
  have hbLip (j x y) : ‖(b j x : 𝕜) - (b j y : 𝕜)‖ ≤ L j * euclideanLength (x-y) := by
    rw [← RCLike.ofReal_sub, RCLike.norm_ofReal]
    exact hbL j x y
  obtain ⟨k, hk⟩ := corrected_fractional_datum s p hs0 hs1 hp g h
    (fun z => (a z : 𝕜)) (fun j z => (b j z : 𝕜)) δ hδ La haM haLip M L hbBound hbLip
  refine ⟨k, ?_⟩
  filter_upwards [hk] with z hkz
  intro hz
  have haz : (a z : 𝕜) = (chartNormalCoefficient Φ (chartOutwardNormal Φ i) i
      (Φ.symm (boundaryEmbedding i z)) : 𝕜) := congrArg (fun r : ℝ => (r : 𝕜)) (haeq hz)
  have hbz (j : Fin n) : (b j z : 𝕜) = (chartTangentialCoefficient Φ (chartOutwardNormal Φ i) i j
      (Φ.symm (boundaryEmbedding i z)) : 𝕜) := congrArg (fun r : ℝ => (r : 𝕜)) (hbeq j hz)
  simp only [← haz, ← hbz]
  rw [hkz]
  exact corrected_datum_algebra _ _ _ _ (norm_pos_iff.mp (hδ.trans_le (haM z)))

end ExpandedFA.PartIV.SecondTrace

namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.SecondTraceFlat ExpandedFA.PartIV.SecondTraceTransport
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma orderOnePart_assembleTwo {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (V : X →L[𝕜] SpaceValue 𝕜 d Ω 1 p) (W : Fin d → X →L[𝕜] SpaceValue 𝕜 d Ω 1 p)
    (hW : ∀ x i, (W i x).val (zeroIndex d 1) = (V x).val (HalfSpace.coordinateIndex i)) (x : X) :
    orderOnePart (assembleTwo V W hW x) = V x := by
  apply sobolev_underlying_injective 𝕜 d Ω 1 p
  simp only [orderOnePart_apply, orderOneToTwo_zero, assembleTwo_zero]

lemma derivativePart_assembleTwo {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (V : X →L[𝕜] SpaceValue 𝕜 d Ω 1 p) (W : Fin d → X →L[𝕜] SpaceValue 𝕜 d Ω 1 p)
    (hW : ∀ x i, (W i x).val (zeroIndex d 1) = (V x).val (HalfSpace.coordinateIndex i))
    (x : X) (j : Fin d) : derivativePart j (assembleTwo V W hW x) = W j x := by
  apply sobolev_underlying_injective 𝕜 d Ω 1 p
  simp only [derivativePart_apply, derivativePartIndex_zero]
  have hn : natIndex (normalIndex j) = Pi.single j 1 := by
    funext k
    simp [natIndex, normalIndex, Pi.single_apply, apply_ite]
  change twoJet (V x) (fun i => W i x) (normalIndex j) = _
  simp only [twoJet, PiLp.toLp_apply, hn, Lines.multiIndexWord_single]
  exact (hW x j).symm

/-- Actual boundary product rule, with the normal derivative of the cutoff
retained. Its graph and trace statements use the original spaces. -/
theorem hasDomainJets_smooth_multiplication
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (hc : IsC2Domain Ω) (hp : p ≠ ∞)
    (ν : Domain d → Domain d) (hν : IsOutwardNormal Ω ν)
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖a x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C)
    (hDD : ∀ j k x, ‖partialFunction [k] (partialFunction [j] a) x‖ ≤ C)
    (u : SpaceValue 𝕜 d Ω 2 p) (g h : BoundaryLp 𝕜 Ω p)
    (hu : HasDomainJets ν T u g h) :
    ∃ g' h' : BoundaryLp 𝕜 Ω p,
      HasDomainJets ν T (multiplyTwo a ha C hC0 hC hD hDD u) g' h' ∧
      g' =ᵐ[surfaceMeasure Ω] (fun x => a x * g x) ∧
      h' =ᵐ[surfaceMeasure Ω] (fun x => a x * h x +
        (∑ j : Fin d, (ν x j : 𝕜) * partialFunction [j] a x) * g x) := by
  let U := multiplyTwo (Ω := Ω) (p := p) a ha C hC0 hC hD hDD u
  let G := T (orderOnePart U)
  let H := normalTrace ν hν T U
  have hG : orderOnePart U = multiplyValue a ha C hC0 hC hD u :=
    orderOnePart_assembleTwo _ _ _ u
  have hW (j : Fin d) : derivativePart j U = multiplyDerivative a ha C hC0 hC hD hDD j u :=
    derivativePart_assembleTwo _ _ _ u j
  have hdense := C1Extension.smooth_density 𝕜 d Ω hc.isC1Domain
    (hΩ.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure) p hp
  have hprod := trace_ambientMultiply Ω hdense T hT a ha C hC0 hC hD
  have hdprod (j : Fin d) := trace_ambientMultiply Ω hdense T hT (partialFunction [j] a)
    (Smoothing.partialFunction_contDiff _ a ha) C hC0 (hD j) (fun k => hDD j k)
  rw [hasDomainJets_iff] at hu
  have htrace : G =ᵐ[surfaceMeasure Ω] fun x => a x * g x := by
    change T (orderOnePart U) =ᵐ[surfaceMeasure Ω] _
    rw [hG]
    exact (hprod (orderOnePart u)).trans (Filter.Eventually.of_forall (fun x => by rw [hu.1]))
  refine ⟨G, H, (hasDomainJets_iff_normalTrace ν hν T U G H).mpr ⟨rfl, rfl⟩, htrace, ?_⟩
  have hdertrace (j : Fin d) : T (derivativePart j U) =ᵐ[surfaceMeasure Ω] fun x =>
      a x * T (derivativePart j u) x + partialFunction [j] a x * g x := by
    rw [hW]
    change T ((C1Extension.ambientMultiply a ha C hC0 hC hD) (derivativePart j u) +
      (C1Extension.ambientMultiply (partialFunction [j] a) (Smoothing.partialFunction_contDiff _ a ha)
        C hC0 (hD j) (fun k => hDD j k)) (orderOnePart u)) =ᵐ[surfaceMeasure Ω] _
    rw [map_add]
    filter_upwards [Lp.coeFn_add
      (T (C1Extension.ambientMultiply a ha C hC0 hC hD (derivativePart j u)))
      (T (C1Extension.ambientMultiply (partialFunction [j] a) (Smoothing.partialFunction_contDiff _ a ha)
        C hC0 (hD j) (fun k => hDD j k) (orderOnePart u))),
      hprod (derivativePart j u), hdprod j (orderOnePart u)] with x hx ha hb
    simp only [Pi.add_apply] at hx
    rw [hx, ha, hb, hu.1]
  filter_upwards [normalTrace_representative ν hν T U, hu.2,
    ae_all_iff.mpr hdertrace] with x hx hux hdx
  rw [hx, hux, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [hdx j]
  ring

end ExpandedFA.PartIV.SecondTrace

namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- Distributional derivatives vanish on the open complement of a closed
support. Thus localizing the value does not leave untracked derivative tails. -/
lemma sobolev_components_supported_of_value_supported {𝕜 : Type} [RCLike 𝕜] {d m : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : SpaceValue 𝕜 d Ω m p) (K : Set (Domain d)) (hK : IsClosed K)
    (hu : ∀ᵐ x ∂volume.restrict (Ω : Set (Domain d)), x ∉ K → u.val (zeroIndex d m) x = 0) :
    ∀ α, ∀ᵐ x ∂volume.restrict (Ω : Set (Domain d)), x ∉ K → u.val α x = 0 := by
  let V : Opens (Domain d) := Ω ⊓ ⟨Kᶜ, hK.isOpen_compl⟩
  let R := C1Extension.restrictSobolev (𝕜 := 𝕜) (m := m) (p := p) (show V ≤ Ω from inf_le_left)
  have hV : V ≤ Ω := inf_le_left
  have huV := hu.filter_mono (ae_mono (Measure.restrict_mono hV le_rfl))
  have hzero : (R u).val (zeroIndex d m) = 0 := by
    apply Lp.ext
    filter_upwards [C1Extension.restrictSobolev_coe hV u (zeroIndex d m),
      huV, ae_restrict_mem V.isOpen.measurableSet,
      Lp.coeFn_zero 𝕜 p (volume.restrict (V : Set (Domain d)))] with x hx hux hxV hz
    change (R u).val (zeroIndex d m) x = (0 : DomainLp 𝕜 V p) x
    rw [hx, hz]
    exact hux hxV.2
  have hR : R u = 0 := sobolev_underlying_injective 𝕜 d V m p hzero
  intro α
  have hα : u.val α =ᵐ[volume.restrict (V : Set (Domain d))] 0 := by
    filter_upwards [C1Extension.restrictSobolev_coe hV u α,
      Lp.coeFn_zero 𝕜 p (volume.restrict (V : Set (Domain d)))] with x hx hz
    change (R u).val α x = u.val α x at hx
    rw [hR] at hx
    exact hx.symm.trans hz
  have hμ : volume.restrict (V : Set (Domain d)) =
      (volume.restrict (Ω : Set (Domain d))).restrict Kᶜ := by
    rw [Measure.restrict_restrict hK.isOpen_compl.measurableSet]
    congr 1
    exact Set.inter_comm _ _
  rw [hμ] at hα
  exact (ae_restrict_iff' hK.isOpen_compl.measurableSet).mp hα

end ExpandedFA.PartIV.SecondTrace

namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.PartIV.FractionalSobolev

/-- The fractional correction has no tail outside the common closed support
of the data. Derivative support is proved from the weak graph, not assumed. -/
theorem corrected_fractional_datum_supported {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (g : HigherFractionalSpace 𝕜 n (s+1) p) (h : FractionalSpace 𝕜 n s p)
    (a : Domain n → 𝕜) (b : Fin n → Domain n → 𝕜)
    (δ : ℝ) (hδ : 0 < δ) (La : ℝ≥0)
    (ha : ∀ x, δ ≤ ‖a x‖)
    (haL : ∀ x y, ‖a x - a y‖ ≤ La * euclideanLength (x-y))
    (M L : Fin n → ℝ≥0)
    (hbM : ∀ j x, ‖b j x‖ ≤ M j)
    (hbL : ∀ j x y, ‖b j x - b j y‖ ≤ L j * euclideanLength (x-y))
    (K : Set (Domain n)) (hK : IsClosed K)
    (hg : ∀ᵐ x ∂volume, x ∉ K → wholeLp (g.val.val (zeroIndex n 1)) x = 0)
    (hh : ∀ᵐ x ∂volume, x ∉ K → h.val x = 0) :
    ∃ k : FractionalSpace 𝕜 n s p,
      (k.val =ᵐ[volume] fun x =>
        (h.val x - ∑ j : Fin n, b j x * wholeLp (g.val.val (firstIndex j)) x) / a x) ∧
      (∀ᵐ x ∂volume, x ∉ K → k.val x = 0) := by
  have hgu : ∀ᵐ x ∂volume.restrict ((⊤ : Opens (Domain n)) : Set (Domain n)),
      x ∉ K → g.val.val (zeroIndex n 1) x = 0 := by
    simp only [Opens.coe_top, Measure.restrict_univ]
    filter_upwards [hg, wholeLp_representative (g.val.val (zeroIndex n 1))] with x hx hrep
    exact fun hxK => hrep.symm.trans (hx hxK)
  have hsupp := sobolev_components_supported_of_value_supported g.val K hK hgu
  have hq (j : Fin n) : ∀ᵐ x ∂volume, x ∉ K →
      wholeLp (g.val.val (firstIndex j)) x = 0 := by
    have hj := hsupp (firstIndex j)
    simp only [Opens.coe_top, Measure.restrict_univ] at hj
    filter_upwards [hj, wholeLp_representative (g.val.val (firstIndex j))] with x hx hrep
    exact fun hxK => hrep.trans (hx hxK)
  obtain ⟨k, hk⟩ := corrected_fractional_datum s p hs0 hs1 hp g h a b δ hδ La ha haL M L hbM hbL
  refine ⟨k, hk, ?_⟩
  filter_upwards [hk, hh, ae_all_iff.mpr hq] with x hkx hhx hqx
  intro hxK
  have hqx' (j : Fin n) : wholeLp (g.val.val (firstIndex j)) x = 0 := hqx j hxK
  rw [hkx, hhx hxK]
  simp only [hqx', mul_zero, Finset.sum_const_zero, sub_zero, zero_div]

end ExpandedFA.PartIV.SecondTrace


open Set Filter Topology TopologicalSpace
noncomputable section
namespace ExpandedFA.PartIV.SecondTrace
lemma flat_gradient_normal {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (y : Fin d → ℝ) (i : Fin d) (hyi : y i = 0)
    (hf : DifferentiableAt ℝ f y) (hfy : f y = 0)
    (hsign : ∀ᶠ z in 𝓝 y, z i ≤ 0 → 0 ≤ f z) :
    ∃ a : ℝ, a ≤ 0 ∧ ∀ v, fderiv ℝ f y v = a * v i := by
  have hmin : IsLocalMinOn f {z | z i ≤ 0} y := by
    filter_upwards [hsign.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzS
    simpa [hfy] using hz hzS
  have htangent (v : Fin d → ℝ) (hv : v i ≤ 0) :
      v ∈ posTangentConeAt {z : Fin d → ℝ | z i ≤ 0} y := by
    apply mem_posTangentConeAt_of_frequently_mem
    apply Filter.Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with t ht
    change y i + t * v i ≤ 0
    rw [hyi, zero_add]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht) hv
  have hdir (v : Fin d → ℝ) (hv : v i ≤ 0) : 0 ≤ fderiv ℝ f y v :=
    hmin.hasFDerivWithinAt_nonneg hf.hasFDerivAt.hasFDerivWithinAt (htangent v hv)
  refine ⟨fderiv ℝ f y (Pi.single i 1), ?_, ?_⟩
  · have := hdir (-(Pi.single i 1)) (by simp)
    simpa using this
  · intro v
    have hz : fderiv ℝ f y (v - v i • Pi.single i 1) = 0 := by
      apply le_antisymm
      · have := hdir (-(v - v i • Pi.single i 1)) (by simp)
        simpa using this
      · exact hdir _ (by simp)
    rw [map_sub, map_smul, smul_eq_mul] at hz
    linarith


lemma defining_gradient_chart_proportional {d : ℕ} (Ω : Set (Fin d → ℝ))
    (Φ : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ)) (i : Fin d)
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    (x : Fin d → ℝ) (hx : x ∈ Φ.source) (hxi : Φ x i = 0)
    (hΦ : DifferentiableAt ℝ Φ x) (hInv : DifferentiableAt ℝ Φ.symm (Φ x))
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) (hxU : x ∈ U)
    (r : (Fin d → ℝ) → ℝ) (hr : DifferentiableAt ℝ r x) (hrx : r x = 0)
    (hrside : ∀ y ∈ U, y ∈ Ω ↔ r y < 0)
    (hrnonzero : (∑ j : Fin d, (fderiv ℝ r x (Pi.single j 1))^2) ≠ 0) :
    ∃ a : ℝ, a < 0 ∧ ∀ v, fderiv ℝ r x v = a * fderiv ℝ Φ x v i := by
  let R := r ∘ Φ.symm
  have hR : DifferentiableAt ℝ R (Φ x) := by
    have hr' : DifferentiableAt ℝ r (Φ.symm (Φ x)) := by
      simpa only [Φ.left_inv hx] using hr
    exact hr'.comp (Φ x) hInv
  have hRzero : R (Φ x) = 0 := by simpa [R, Φ.left_inv hx] using hrx
  have hsign : ∀ᶠ z in 𝓝 (Φ x), z i ≤ 0 → 0 ≤ R z := by
    have hU' : ∀ᶠ z in 𝓝 (Φ x), Φ.symm z ∈ U := by
      apply (Φ.continuousAt_symm (Φ.map_source hx)).eventually
      change U ∈ 𝓝 (Φ.symm (Φ x))
      simpa only [Φ.left_inv hx] using hU.mem_nhds hxU
    filter_upwards [hU', Φ.open_target.mem_nhds (Φ.map_source hx)] with z hzU hzT hzi
    apply le_of_not_gt
    intro hrz
    have hzΩ := (hrside _ hzU).mpr hrz
    have hzpos := (hside _ (Φ.map_target hzT)).mp hzΩ
    rw [Φ.right_inv hzT] at hzpos
    exact (not_lt_of_ge hzi) hzpos
  obtain ⟨a, ha, hDa⟩ := flat_gradient_normal R (Φ x) i hxi hR hRzero hsign
  have heq : R ∘ Φ =ᶠ[𝓝 x] r := by
    filter_upwards [Φ.open_source.mem_nhds hx] with z hz
    simp [R, Φ.left_inv hz]
  have hcomp := heq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp x hR hΦ] at hcomp
  have hDr (v) : fderiv ℝ r x v = a * fderiv ℝ Φ x v i := by
    rw [← hcomp]
    exact hDa _
  refine ⟨a, lt_of_le_of_ne ha ?_, hDr⟩
  intro hazero
  apply hrnonzero
  simp [hDr, hazero]

lemma normalized_negative_scalar {d : ℕ} (v : Fin d → ℝ) {a : ℝ} (ha : a < 0)
    (j : Fin d) :
    (a * v j) / Real.sqrt (∑ k : Fin d, (a * v k)^2) =
      - v j / Real.sqrt (∑ k : Fin d, (v k)^2) := by
  have hsum : (∑ k : Fin d, (a * v k)^2) = a^2 * (∑ k : Fin d, (v k)^2) := by
    simp only [mul_pow, Finset.mul_sum]
  rw [hsum, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_neg ha]
  have ha0 : a ≠ 0 := ne_of_lt ha
  field_simp

open ExpandedFA.Distributions ExpandedFA.Sobolev

lemma outward_normal_chart_formula {d : ℕ} {Ω : Opens (Domain d)}
    (ν : Domain d → Domain d) (hν : IsOutwardNormal Ω ν)
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (x : Domain d) (hxb : x ∈ frontier (Ω : Set (Domain d))) (hx : x ∈ Φ.source)
    (j : Fin d) :
    ν x j = -fderiv ℝ Φ x (coordinateVector j) i /
      Real.sqrt (∑ k : Fin d, (fderiv ℝ Φ x (coordinateVector k) i)^2) := by
  obtain ⟨U, r, hU, hxU, hr, hrx, hrside, hrnonzero, hνr⟩ := hν.2.2 x hxb
  have hΦd := (hΦ.contDiffAt (Φ.open_source.mem_nhds hx)).differentiableAt (by norm_num)
  have hId := (hInv.contDiffAt (Φ.open_target.mem_nhds (Φ.map_source hx))).differentiableAt
    (by norm_num)
  have hrd := (hr.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by norm_num)
  obtain ⟨a, ha, hDr⟩ := defining_gradient_chart_proportional (Ω : Set (Domain d)) Φ i hside
    x hx ((ExpandedFA.Sobolev.Trace.chart_boundary_iff Ω Φ i hside x hx).mp hxb)
    hΦd hId U hU hxU r hrd hrx hrside hrnonzero
  rw [hνr j]
  simp_rw [hDr]
  exact normalized_negative_scalar (fun k => fderiv ℝ Φ x (coordinateVector k) i) ha j

lemma outward_normal_eq_chart {d : ℕ} {Ω : Opens (Domain d)}
    (ν : Domain d → Domain d) (hν : IsOutwardNormal Ω ν)
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (x : Domain d) (hxb : x ∈ frontier (Ω : Set (Domain d))) (hx : x ∈ Φ.source) :
    ν x = chartOutwardNormal Φ i x := by
  funext j
  exact outward_normal_chart_formula ν hν Φ i hside hΦ hInv x hxb hx j

lemma chartNormalCoefficient_eq_outward {d : ℕ} {Ω : Opens (Domain d)}
    (ν : Domain d → Domain d) (hν : IsOutwardNormal Ω ν)
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i k : Fin d)
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (x : Domain d) (hxb : x ∈ frontier (Ω : Set (Domain d))) (hx : x ∈ Φ.source) :
    chartNormalCoefficient Φ ν k x = chartNormalCoefficient Φ (chartOutwardNormal Φ i) k x := by
  unfold chartNormalCoefficient
  rw [outward_normal_eq_chart ν hν Φ i hside hΦ hInv x hxb hx]

lemma chartTangentialCoefficient_eq_outward {n : ℕ} {Ω : Opens (Domain (n+1))}
    (ν : Domain (n+1) → Domain (n+1)) (hν : IsOutwardNormal Ω ν)
    (Φ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1))) (i : Fin (n+1)) (k : Fin n)
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (x : Domain (n+1)) (hxb : x ∈ frontier (Ω : Set (Domain (n+1)))) (hx : x ∈ Φ.source) :
    chartTangentialCoefficient Φ ν i k x =
      chartTangentialCoefficient Φ (chartOutwardNormal Φ i) i k x := by
  unfold chartTangentialCoefficient
  rw [outward_normal_eq_chart ν hν Φ i hside hΦ hInv x hxb hx]

lemma chartNormalCoefficient_negative {d : ℕ} {Ω : Opens (Domain d)}
    (ν : Domain d → Domain d) (hν : IsOutwardNormal Ω ν)
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (x : Domain d) (hxb : x ∈ frontier (Ω : Set (Domain d))) (hx : x ∈ Φ.source) :
    chartNormalCoefficient Φ ν i x < 0 := by
  rw [chartNormalCoefficient_eq_outward ν hν Φ i i hside hΦ hInv x hxb hx]
  exact chart_normal_coefficient_outward_negative Φ i hΦ hInv x hx

end ExpandedFA.PartIV.SecondTrace


noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators
namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound
open ExpandedFA.PartIV.SharpTraceExtension ExpandedFA.PartIV.SecondTraceFlat
open ExpandedFA.PartIV.SharpTraceBound.AnalyticEstimates
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

lemma jetFunction_tangential_boundary {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (j : Fin n) (f h : Domain n → 𝕜)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h) (x : Domain n) :
    fderiv ℝ (jetFunction i f h) (i.insertNth 0 x) (coordinateVector (i.succAbove j)) =
      fderiv ℝ f x (coordinateVector j) := by
  have hdir : insertZeroCLM i (coordinateVector j) = coordinateVector (i.succAbove j) := by
    ext k
    induction k using i.succAboveCases <;> simp [insertZeroCLM, LinearMap.mkContinuous_apply,
      coordinateVector, Pi.single_apply]
  have hfun : (fun z => jetFunction i f h (insertZeroCLM i z)) = f := by
    funext z
    exact jetFunction_boundary i f h z
  have hd := fderiv_linear_comp (insertZeroCLM i) (jetFunction i f h)
    (jetFunction_contDiff i f h hf hh) x (coordinateVector j)
  rw [hfun, hdir] at hd
  exact hd.symm

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (σ : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (p ≠ ∞)]

def higherDerivativeCLM (j : Fin n) : HigherFractionalSpace 𝕜 n σ p →L[𝕜]
    Lp 𝕜 p (volume : Measure (Domain n)) :=
  (show HigherFractionalSpace 𝕜 n σ p →ₗ[𝕜] Lp 𝕜 p volume from
    { toFun := fun g => wholeLp (g.val.val (firstIndex j))
      map_add' := fun g h => by
        change wholeLp (g.val.val (firstIndex j) + h.val.val (firstIndex j)) = _
        exact wholeLp_add _ _
      map_smul' := fun c g => by
        change wholeLp (c • g.val.val (firstIndex j)) = _
        exact wholeLp_smul _ _ }).mkContinuous 1 (fun g => by
      change ‖wholeLp (g.val.val (firstIndex j))‖ ≤ 1 * higherFractionalNorm σ p g
      rw [one_mul]
      have hpart := norm_le_fractionalNorm (σ-1) p
        (⟨wholeLp (g.val.val (firstIndex j)), g.property j⟩ : FractionalSpace 𝕜 n (σ-1) p)
      refine hpart.trans ?_
      exact (Finset.single_le_sum (fun k _ => fractionalNorm_nonneg (σ-1) p
        (⟨wholeLp (g.val.val (firstIndex k)), g.property k⟩ : FractionalSpace 𝕜 n (σ-1) p))
        (Finset.mem_univ j)).trans (le_add_of_nonneg_left (norm_nonneg _)))

lemma smooth_jet_tangential_trace
    (i : Fin (n+1)) (j : Fin n) (f h : Domain n → 𝕜)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h)
    (u : SpaceValue 𝕜 (n+1) (upper i) 2 p)
    (hcoe : ∀ α, u.val α =ᵐ[volume.restrict (upper i : Set (Domain (n+1)))]
      Smoothing.classicalDerivative α (jetFunction i f h))
    (T : SpaceValue 𝕜 (n+1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))) (hT : CoordinateTraceCondition i T) :
    reindexedTrace i T (derivativePart (i.succAbove j) u) =ᵐ[volume]
      fun x => fderiv ℝ f x (coordinateVector j) := by
  let F := jetFunction i f h
  have hF := jetFunction_contDiff i f h hf hh
  let D : Domain (n+1) → 𝕜 := fun x => fderiv ℝ F x (coordinateVector (i.succAbove j))
  have hD : ContDiff ℝ (↑(⊤ : ℕ∞)) D :=
    (hF.fderiv_right (by simp)).clm_apply contDiff_const
  have hw : (derivativePart (i.succAbove j) u).val (zeroIndex (n+1) 1) =ᵐ[
      volume.restrict (upper i : Set (Domain (n+1)))] D := by
    simpa only [derivativePart_apply, derivativePartIndex_zero, classicalDerivative_normal]
      using hcoe (normalIndex (i.succAbove j))
  have ht := reindexedTrace_smooth i T hT (derivativePart (i.succAbove j) u) D
    (hD.of_le (by simp)) hw
  filter_upwards [ht] with x hx
  exact hx.trans (jetFunction_tangential_boundary i j f h hf hh x)

/-- Smooth representative data and bounded linearity imply the complete tangential jets. -/
theorem jet_extension_tangential_trace
    (hp1 : 1 < p) (i : Fin (n+1))
    (E : (HigherFractionalSpace 𝕜 n (2 - 1 / p.toReal) p ×
        FractionalSpace 𝕜 n (1 - 1 / p.toReal) p) →L[𝕜]
      SpaceValue 𝕜 (n+1) (upper i) 2 p)
    (hSmooth : ∀ g k (f h : Domain n → 𝕜)
      (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h),
      wholeLp (g.val.val (zeroIndex n 1)) =ᵐ[volume] f →
      (∀ j, wholeLp (g.val.val (firstIndex j)) =ᵐ[volume]
        fun x => fderiv ℝ f x (coordinateVector j)) →
      k.val =ᵐ[volume] h →
      ∀ α, (E (g,k)).val α =ᵐ[volume.restrict (upper i : Set (Domain (n+1)))]
        Smoothing.classicalDerivative α (jetFunction i f h))
    (T : SpaceValue 𝕜 (n+1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))) (hT : CoordinateTraceCondition i T)
    (g : HigherFractionalSpace 𝕜 n (2 - 1 / p.toReal) p)
    (k : FractionalSpace 𝕜 n (1 - 1 / p.toReal) p) (j : Fin n) :
    reindexedTrace i T (derivativePart (i.succAbove j) (E (g,k))) =
      wholeLp (g.val.val (firstIndex j)) := by
  let s := 1 - 1 / p.toReal
  let σ := 2 - 1 / p.toReal
  let X := HigherFractionalSpace 𝕜 n σ p × FractionalSpace 𝕜 n s p
  let S := HigherDensity.smoothJetDataSubmodule (𝕜 := 𝕜) (n := n) s σ p
  have hS : DenseRange S.subtype := HigherDensity.smoothJetData_denseRange s σ p
    (endpoint_exponent hp1 Fact.out).1 (endpoint_exponent hp1 Fact.out).2
  let G : X →L[𝕜] Lp 𝕜 p (volume : Measure (Domain n)) :=
    (higherDerivativeCLM σ p j).comp (ContinuousLinearMap.fst 𝕜 _ _)
  have heq : (fun u : X => reindexedTrace i T (derivativePart (i.succAbove j) (E u))) = G := by
    apply hS.equalizer
      ((reindexedTrace i T).continuous.comp
        ((derivativePartCLM 𝕜 (n+1) (upper i) p (i.succAbove j)).continuous.comp E.continuous))
      G.continuous
    funext u
    obtain ⟨f, hf, hgf, hgrad⟩ := u.property.1
    obtain ⟨h, hh, hkh⟩ := u.property.2
    apply Lp.ext
    exact (smooth_jet_tangential_trace p i j f h hf hh (E u.val)
      (hSmooth u.val.1 u.val.2 f h hf hh hgf hgrad hkh) T hT).trans (hgrad j).symm
  exact congrFun heq (g,k)

end ExpandedFA.PartIV.SecondTrace


noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal
namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.Sobolev.C1Extension ExpandedFA.Sobolev.HalfSpace
open ExpandedFA.Sobolev.C1Extension.Transport
open ExpandedFA.PartIV.SecondTraceFlat ExpandedFA.PartIV.SecondTraceTransport
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- An actual order-two patch on the physical domain, obtained by C²
transport and zero extension across only the artificial chart edge. The
formula holds for every representative of the input graph. -/
theorem exists_domain_chart_pullback_two {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞)
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    (θ : Tests 𝕜 (⊤ : Opens (Domain d))) (hθ : tsupport θ ⊆ Φ.source) :
    ∃ P : SpaceValue 𝕜 d (upper i) 2 p →L[𝕜] SpaceValue 𝕜 d Ω 2 p,
      ∀ (u : SpaceValue 𝕜 d (upper i) 2 p) (f : Domain d → 𝕜),
        f =ᵐ[volume.restrict (upper i : Set (Domain d))] u.val (zeroIndex d 2) →
        (P u).val (zeroIndex d 2) =ᵐ[volume.restrict (Ω : Set (Domain d))]
          fun x => θ x * f (Φ x) := by
  let A := chartPreimage Φ (upper i)
  have hAΩ : A ≤ Ω := fun x hx => (hside x hx.1).mpr hx.2
  obtain ⟨Q, hQ⟩ := localized_transport 𝕜 d (upper i) p hp1 hp Φ hΦ hInv
    θ θ.contDiff θ.hasCompactSupport hθ
  obtain ⟨η, hη, hηone⟩ := exists_compact_ambient_cutoff (𝕜 := 𝕜)
    (tsupport θ) θ.hasCompactSupport ⟨Φ.source, Φ.open_source⟩ hθ
  let K : Set (Domain d) := (Ω : Set (Domain d)) ∩ tsupport η
  have hK : IsClosed (K ∪ (Ω : Set (Domain d))ᶜ) := by
    convert (isClosed_tsupport η).union Ω.isOpen.isClosed_compl using 1
    ext x
    simp only [K, mem_union, mem_inter_iff, mem_compl_iff]
    tauto
  have hKA : K ⊆ A := by
    intro x hx
    exact ⟨hη hx.2, (hside x (hη hx.2)).mp hx.1⟩
  obtain ⟨E, hE⟩ := localized_zero_extension 𝕜 d A Ω hAΩ K hK hKA
    η η.contDiff η.hasCompactSupport (fun x hx => ⟨hAΩ hx.1, hx.2⟩) p
  refine ⟨E.comp Q, ?_⟩
  intro u f hf
  have hQu := hQ u f hf
  apply (hE (Q u) (fun x => θ x * f (Φ x)) hQu.symm).trans
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hxΩ
  change (A : Set (Domain d)).indicator (fun x => η x * (θ x * f (Φ x))) x = _
  by_cases hxθ : x ∈ tsupport θ
  · have hxA : x ∈ A := ⟨hθ hxθ, (hside x (hθ hxθ)).mp hxΩ⟩
    rw [Set.indicator_of_mem hxA, hηone x hxθ, one_mul]
  · have hz : θ x = 0 := image_eq_zero_of_notMem_tsupport hxθ
    by_cases hxA : x ∈ A <;> simp [hxA, hz]

/-- Physical patch construction controls every weak derivative's support,
not just the representative of the function. -/
theorem domain_chart_pullback_two_supported {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (θ : Tests 𝕜 (⊤ : Opens (Domain d)))
    (P : SpaceValue 𝕜 d (upper i) 2 p →L[𝕜] SpaceValue 𝕜 d Ω 2 p)
    (hP : ∀ u, (P u).val (zeroIndex d 2) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun x => θ x * u.val (zeroIndex d 2) (Φ x))
    (u : SpaceValue 𝕜 d (upper i) 2 p) :
    ∀ α, ∀ᵐ x ∂volume.restrict (Ω : Set (Domain d)),
      x ∉ tsupport θ → (P u).val α x = 0 := by
  apply sobolev_components_supported_of_value_supported (P u) (tsupport θ) (isClosed_tsupport θ)
  filter_upwards [hP u] with x hx hxs
  rw [hx, image_eq_zero_of_notMem_tsupport hxs, zero_mul]

end ExpandedFA.PartIV.SecondTrace


noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal

namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.FractionalSobolev
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

namespace C2BoundaryModel
variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {Ω : Opens (Domain (n+1))}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : C2BoundaryModel 𝕜 Ω p)

/-- A fixed compact tangential support shared by all data localized in a chart. -/
def coordinateSupport (j : Fin B.chartCount) : Set (Domain n) :=
  (B.atlas.chart j) '' tsupport (B.atlas.cutoff j)

lemma coordinateSupport_compact (hb : Bornology.IsBounded (Ω : Set (Domain (n+1))))
    (j : Fin B.chartCount) : IsCompact (B.coordinateSupport j) := by
  have hc : IsCompact (frontier (Ω : Set (Domain (n+1)))) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  let : CompactSpace (frontier (Ω : Set (Domain (n+1)))) :=
    isCompact_iff_compactSpace.mp hc
  exact B.atlas.cutoffImage_isCompact j

lemma coordinateSupport_subset_boundaryChartDomain (j : Fin B.chartCount) :
    B.coordinateSupport j ⊆ boundaryChartDomain (B.ambient j) (B.normal j) := by
  intro z hz
  exact B.insert_chart_mem j z (B.atlas.cutoffImage_subset_target j hz)

lemma localizedLp_supported (j : Fin B.chartCount) (f : BoundaryLp 𝕜 Ω p) :
    ∀ᵐ z ∂volume, z ∉ B.coordinateSupport j →
      B.atlas.localizedLp p j (B.identify f) z = 0 := by
  filter_upwards [B.atlas.localizedLp_representative p j (B.identify f)] with z hz
  intro hzK
  rw [hz]
  exact Function.notMem_support.mp (fun hs => hzK
    (B.atlas.localizedRepresentative_support_subset j (B.identify f) hs))

lemma higherPiece_supported (σ : ℝ) (g : B.HigherData σ) (j : Fin B.chartCount) :
    ∀ᵐ z ∂volume, z ∉ B.coordinateSupport j →
      wholeLp ((B.higherPiece σ g j).val.val (zeroIndex n 1)) z = 0 := by
  have hs := B.higherPiece_spec σ g j
  change wholeLp ((B.higherPiece σ g j).val.val (zeroIndex n 1)) =
    B.atlas.localizedLp p j (B.identify g.val) at hs
  simpa only [hs] using B.localizedLp_supported j g.val

/-- The localized lower datum is an independent member of the exact flat space. -/
def fractionalPiece (s : ℝ) (h : B.toBoundaryModel.Data s) (j : Fin B.chartCount) :
    FractionalSpace 𝕜 n s p :=
  ⟨B.atlas.localizedLp p j (B.identify h.val), h.property j⟩

lemma fractionalPiece_supported (s : ℝ) (h : B.toBoundaryModel.Data s)
    (j : Fin B.chartCount) : ∀ᵐ z ∂volume, z ∉ B.coordinateSupport j →
      (B.fractionalPiece s h j).val z = 0 :=
  B.localizedLp_supported j h.val

end C2BoundaryModel
end ExpandedFA.PartIV.SecondTrace


noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Trace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound
open ExpandedFA.PartIV.SharpTrace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
lemma localized_chart_pullback_trace_supported_c1
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (Λ : Opens (Domain d))
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (θ : Domain d → 𝕜) (hθcompact : HasCompactSupport θ) (hθ : tsupport θ ⊆ Φ.source)
    (F : SpaceValue 𝕜 d Λ 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p)
    (hF : ∀ (u : SpaceValue 𝕜 d Λ 1 p) (f : Domain d → 𝕜),
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (Λ : Set (Domain d))] f →
      (F u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
        fun x => θ x * f (Φ x))
    (u : SpaceValue 𝕜 d Λ 1 p) :
    ∀ᵐ x ∂(surfaceMeasure Ω), x ∉ Φ.source → T (F u) x = 0 := by
  obtain ⟨η, hη, hηone⟩ := exists_compact_ambient_cutoff (𝕜 := 𝕜)
    (tsupport θ) hθcompact ⟨Φ.source, Φ.open_source⟩ hθ
  have hfix := trace_fixed_by_cutoff hdense T hT η (F u) (by
    filter_upwards [hF u (u.val (zeroIndex d 1)) Filter.EventuallyEq.rfl] with x hx
    rw [hx]
    by_cases hxθ : x ∈ tsupport θ
    · rw [hηone x hxθ, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hxθ, zero_mul, mul_zero])
  filter_upwards [hfix] with x hx hxs
  have hxη : x ∉ tsupport η := fun hh => hxs (hη hh)
  simpa only [image_eq_zero_of_notMem_tsupport hxη, zero_mul] using hx


lemma coordinate_trace_flattening_pushback_c1 (i : Fin d) (hp : p ≠ ∞)
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (θ χ : Tests 𝕜 (⊤ : Opens (Domain d)))
    (η : Domain d → 𝕜) (hηC1 : ContDiff ℝ 1 η)
    (Cη : ℝ) (hCη0 : 0 ≤ Cη) (hCη : ∀ x, ‖η x‖ ≤ Cη) (hχ : tsupport χ ⊆ Φ.target)
    (E : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d (upper i) 1 p)
    (hE : ∀ (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜),
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f →
      (E u).val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))]
        fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y)))
    (F : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p)
    (hF : ∀ (u : SpaceValue 𝕜 d (upper i) 1 p) (f : Domain d → 𝕜),
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))] f →
      (F u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
        fun x => η x * f (Φ x))
    (S : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))) (hS : IsCoordinateTrace i S)
    (u : SpaceValue 𝕜 d (upper i) 1 p) :
    S (E (F u)) =ᵐ[volume] fun y =>
      (χ (coordinateLine i y 0) *
        (θ (Φ.symm (coordinateLine i y 0)) * η (Φ.symm (coordinateLine i y 0)))) * S u y := by
  let a : Domain d → 𝕜 := fun y => χ y * (θ (Φ.symm y) * η (Φ.symm y))
  have ha : ContDiff ℝ 1 a :=
    contDiff_chart_cutoff_comp Φ hInv χ hχ (fun x => θ x * η x)
      ((θ.contDiff.of_le (by simp)).mul hηC1)
  obtain ⟨Cχ, hCχ0, hCχ, _⟩ := ambient_test_bounds χ
  obtain ⟨Cθ, hCθ0, hCθ, _⟩ := ambient_test_bounds θ
  have hbound : ∀ y, ‖a y‖ ≤ Cχ * (Cθ * Cη) := by
    intro y
    dsimp [a]
    rw [norm_mul, norm_mul]
    exact mul_le_mul (hCχ _) (mul_le_mul (hCθ _) (hCη _) (norm_nonneg _) hCθ0)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCχ0
  have hEF : ∀ v, (E (F v)).val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))]
      fun y => a y * v.val (zeroIndex d 1) y := by
    intro v
    have hFv := hF v (v.val (zeroIndex d 1)) Filter.EventuallyEq.rfl
    filter_upwards [hE (F v) (fun x => η x * v.val (zeroIndex d 1) (Φ x)) hFv] with y hy
    rw [hy]
    by_cases hyt : y ∈ Φ.target
    · rw [Φ.right_inv hyt]
      simp only [a]
      ring
    · have hyχ : y ∉ tsupport χ := fun hh => hyt (hχ hh)
      simp only [a, image_eq_zero_of_notMem_tsupport hyχ, zero_mul]
  exact coordinate_trace_of_continuous_multiplier i hp S hS a ha _ hbound (E.comp F) hEF u


lemma localized_chart_pullback_trace_formula_c1
    {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (Ω : Opens (Domain (n + 1)))
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
    (hBinv : ∀ x ∈ Φ.target, ‖fderiv ℝ Φ.symm x‖ ≤ B)
    (hSource : Bornology.IsBounded Φ.source)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    {K : ℝ≥0} (hLip : LipschitzOnWith K Φ Φ.source)
    (η : Domain (n+1) → 𝕜) (hηC1 : ContDiff ℝ 1 η) (hηcompact : HasCompactSupport η)
    (Cη : ℝ) (hCη0 : 0 ≤ Cη) (hCη : ∀ x, ‖η x‖ ≤ Cη) (hη : tsupport η ⊆ Φ.source)
    (F : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜] SpaceValue 𝕜 (n + 1) Ω 1 p)
    (hF : ∀ (u : SpaceValue 𝕜 (n + 1) (upper i) 1 p) (f : Domain (n + 1) → 𝕜),
      u.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))] f →
      (F u).val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (n + 1)))]
        fun x => η x * f (Φ x))
    (T : SpaceValue 𝕜 (n + 1) Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (S : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))) (hS : IsCoordinateTrace i S)
    (u : SpaceValue 𝕜 (n + 1) (upper i) 1 p) :
    (fun z => T (F u) (boundaryParam Φ i z)) =ᵐ[volume.restrict (boundaryParameters Φ i)]
      fun z => η (boundaryParam Φ i z) * reindexedTrace i S u z := by
  obtain ⟨θ, hθ, hθone⟩ := exists_compact_ambient_cutoff (𝕜 := 𝕜)
    (tsupport η) hηcompact ⟨Φ.source, Φ.open_source⟩ hη
  obtain ⟨χ, hχ, hχone⟩ := exists_chart_cutoff Φ θ hθ
  obtain ⟨E, hE⟩ := exists_flattened_localization_all_representatives (Ω := Ω) (p := p) i Φ hΦ hInv B hB0
    hB hBinv hSource hside θ χ hχ
  have hEsmooth : ∀ (v : SpaceValue 𝕜 (n + 1) Ω 1 p) (f : Domain (n + 1) → 𝕜),
      ContDiff ℝ (⊤ : ℕ∞) f →
      v.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (n + 1)))] f →
      ContDiff ℝ 1 (fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y))) ∧
      (E v).val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))]
        fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y)) := by
    intro v f hf hv
    exact ⟨contDiff_chart_cutoff_comp Φ hInv χ hχ (fun x => θ x * f x)
      ((θ.contDiff.mul hf).of_le (by simp)), hE v f hv⟩
  have hraw := flattened_trace_raw_boundary_formula Ω hdense Φ i hside hLip θ χ E hEsmooth T hT S hS (F u)
  have hcomp := reindexed_trace_multiplier_of_ae i S
    (fun y => χ y * (θ (Φ.symm y) * η (Φ.symm y))) u (E (F u))
    (coordinate_trace_flattening_pushback_c1 i hp Φ hInv θ χ η hηC1 Cη hCη0 hCη hχ E hE F hF S hS u)
  have hcomp' := hcomp.filter_mono
    (ae_mono (show volume.restrict (boundaryParameters Φ i) ≤ volume from Measure.restrict_le_self))
  have hfix := trace_fixed_by_cutoff hdense T hT θ (F u) (by
    filter_upwards [hF u (u.val (zeroIndex (n + 1) 1)) Filter.EventuallyEq.rfl] with x hx
    rw [hx]
    by_cases hxη : x ∈ tsupport η
    · rw [hθone x hxη, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hxη, zero_mul, mul_zero])
  obtain ⟨D, hD, hmap⟩ := boundaryParam_map_le_surfaceMeasure Ω Φ i hside hLip
  have hac : (volume.restrict (boundaryParameters Φ i)).map (boundaryParam Φ i) ≪ surfaceMeasure Ω :=
    Measure.absolutelyContinuous_of_le_smul
      (hmap.trans (smul_le_smul_left D Measure.restrict_le_self))
  have hfixparam := ae_of_ae_map (boundaryParam_aemeasurable Φ i) (hac.ae_eq hfix)
  filter_upwards [hraw, hcomp', hfixparam,
    ae_restrict_mem (boundaryParameters_isOpen Φ i).measurableSet] with z hzraw hzcomp hzfix hz
  have hχθ : χ (i.insertNth 0 z) * θ (boundaryParam Φ i z) * T (F u) (boundaryParam Φ i z) =
      T (F u) (boundaryParam Φ i z) := by
    by_cases hzθ : θ (boundaryParam Φ i z) = 0
    · simpa only [hzθ, zero_mul, mul_zero] using hzfix.symm
    · have hχz := hχone _ (subset_tsupport θ hzθ)
      change χ (Φ (Φ.symm (i.insertNth 0 z))) = 1 at hχz
      rw [Φ.right_inv hz] at hχz
      rw [mul_assoc, ← hzfix, hχz, one_mul]
  have hχη : χ (i.insertNth 0 z) * (θ (boundaryParam Φ i z) * η (boundaryParam Φ i z)) =
      η (boundaryParam Φ i z) := by
    by_cases hzη : η (boundaryParam Φ i z) = 0
    · simp only [hzη, mul_zero]
    · have hθz := hθone _ (subset_tsupport η hzη)
      have hχz := hχone (boundaryParam Φ i z) (subset_tsupport θ
        (show θ (boundaryParam Φ i z) ≠ 0 by rw [hθz]; exact one_ne_zero))
      change χ (Φ (Φ.symm (i.insertNth 0 z))) = 1 at hχz
      rw [Φ.right_inv hz] at hχz
      rw [hθz, hχz, one_mul, one_mul]
  rw [hχθ] at hzraw
  change reindexedTrace i S (E (F u)) z =
    (χ (i.insertNth 0 z) * (θ (boundaryParam Φ i z) * η (boundaryParam Φ i z))) *
      reindexedTrace i S u z at hzcomp
  rw [hχη] at hzcomp
  exact hzraw.symm.trans hzcomp


lemma localized_chart_pullback_trace_eq_c1
    {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (Ω : Opens (Domain (n + 1)))
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
    (hBinv : ∀ x ∈ Φ.target, ‖fderiv ℝ Φ.symm x‖ ≤ B)
    (hSource : Bornology.IsBounded Φ.source)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    {K L : ℝ≥0} (hLip : LipschitzOnWith K Φ Φ.source)
    (hInvLip : LipschitzOnWith L Φ.symm Φ.target)
    (η : Domain (n+1) → 𝕜) (hηC1 : ContDiff ℝ 1 η) (hηcompact : HasCompactSupport η)
    (Cη : ℝ) (hCη0 : 0 ≤ Cη) (hCη : ∀ x, ‖η x‖ ≤ Cη) (hη : tsupport η ⊆ Φ.source)
    (F : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜] SpaceValue 𝕜 (n + 1) Ω 1 p)
    (hF : ∀ (u : SpaceValue 𝕜 (n + 1) (upper i) 1 p) (f : Domain (n + 1) → 𝕜),
      u.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))] f →
      (F u).val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (n + 1)))]
        fun x => η x * f (Φ x))
    (T : SpaceValue 𝕜 (n + 1) Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (S : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))) (hS : IsCoordinateTrace i S)
    (u : SpaceValue 𝕜 (n + 1) (upper i) 1 p) (g : BoundaryLp 𝕜 Ω p)
    (hfix : ∀ᵐ x ∂surfaceMeasure Ω, η x * g x = g x)
    (houtside : ∀ᵐ x ∂surfaceMeasure Ω, x ∉ Φ.source → g x = 0)
    (hflat : reindexedTrace i S u =ᵐ[volume.restrict (boundaryParameters Φ i)]
      fun z => g (boundaryParam Φ i z)) :
    T (F u) = g := by
  have hraw := localized_chart_pullback_trace_formula_c1 Ω hp hdense Φ i hΦ hInv B hB0 hB hBinv
    hSource hside hLip η hηC1 hηcompact Cη hCη0 hCη hη F hF T hT S hS u
  obtain ⟨D, hD, hmap⟩ := boundaryParam_map_le_surfaceMeasure Ω Φ i hside hLip
  have hac : (volume.restrict (boundaryParameters Φ i)).map (boundaryParam Φ i) ≪ surfaceMeasure Ω :=
    Measure.absolutelyContinuous_of_le_smul
      (hmap.trans (smul_le_smul_left D Measure.restrict_le_self))
  have hfixparam := ae_of_ae_map (boundaryParam_aemeasurable Φ i) (hac.ae_eq hfix)
  apply boundary_eq_of_chart_pullback_eq Ω Φ i hside hLip hInvLip (T (F u)) g
  · filter_upwards [hraw, hflat, hfixparam] with z hz₁ hz₂ hz₃
    exact hz₁.trans ((congrArg (η (boundaryParam Φ i z) * ·) hz₂).trans hz₃)
  · have hsupport := localized_chart_pullback_trace_supported_c1 hdense T hT (upper i) Φ η hηcompact hη F hF u
    filter_upwards [hsupport, houtside] with x hx₁ hx₂ hxout
    exact (hx₁ hxout).trans (hx₂ hxout).symm


end ExpandedFA.PartIV.SecondTrace


noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal Topology
namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.Sobolev.C1Extension
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- A smooth ambient cutoff is identically one on a neighborhood of the
compact data support, so all its first partial derivatives vanish there. -/
lemma exists_compact_cutoff_with_zero_gradient {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (K U : Set (Domain d)) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ η : Tests 𝕜 (⊤ : Opens (Domain d)), tsupport η ⊆ U ∧
      (∃ V : Set (Domain d), IsOpen V ∧ K ⊆ V ∧ EqOn η (fun _ => 1) V) ∧
      (∀ x ∈ K, η x = 1) ∧
      ∀ j : Fin d, ∀ x ∈ K, partialFunction [j] η x = 0 := by
  obtain ⟨V, hV, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨η, hηU, hηone⟩ := exists_compact_ambient_cutoff (𝕜 := 𝕜)
    (closure V) hVc ⟨U, hU⟩ hVU
  refine ⟨η, hηU, ⟨V, hV, hKV, fun x hx => hηone x (subset_closure hx)⟩,
    (fun x hx => hηone x (subset_closure (hKV hx))), ?_⟩
  intro j x hx
  have heq : η =ᶠ[𝓝 x] fun _ => (1 : 𝕜) := by
    filter_upwards [hV.mem_nhds (hKV hx)] with y hy
    exact hηone y (subset_closure hy)
  change fderiv ℝ η x (coordinateVector j) = 0
  rw [heq.fderiv_eq]
  simp

lemma cutoff_jet_identity {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (K : Set (Domain d)) (η : Domain d → 𝕜)
    (hη : ∀ x ∈ K, η x = 1)
    (hDη : ∀ j : Fin d, ∀ x ∈ K, partialFunction [j] η x = 0)
    (ν : Domain d → Domain d) (g h : Domain d → 𝕜)
    (hg : Function.support g ⊆ K) (hh : Function.support h ⊆ K) :
    (∀ x, η x * g x = g x) ∧
      ∀ x, η x * h x +
        (∑ j : Fin d, (ν x j : 𝕜) * partialFunction [j] η x) * g x = h x := by
  constructor
  · intro x
    by_cases hx : x ∈ K
    · rw [hη x hx, one_mul]
    · have hgx : g x = 0 := by
        by_contra hgx
        exact hx (hg hgx)
      simp [hgx]
  · intro x
    by_cases hx : x ∈ K
    · simp [hη x hx, fun j => hDη j x hx]
    · have hgx : g x = 0 := by
        by_contra hgx
        exact hx (hg hgx)
      have hhx : h x = 0 := by
        by_contra hhx
        exact hx (hh hhx)
      simp [hgx, hhx]

lemma cutoff_jet_identity_ae {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (K : Set (Domain d)) (η : Domain d → 𝕜)
    (hη : ∀ x ∈ K, η x = 1)
    (hDη : ∀ j : Fin d, ∀ x ∈ K, partialFunction [j] η x = 0)
    (ν : Domain d → Domain d) (g h : BoundaryLp 𝕜 Ω p)
    (hg : ∀ᵐ x ∂surfaceMeasure Ω, x ∉ K → g x = 0)
    (hh : ∀ᵐ x ∂surfaceMeasure Ω, x ∉ K → h x = 0) :
    (fun x => η x * g x) =ᵐ[surfaceMeasure Ω] g ∧
      (fun x => η x * h x +
        (∑ j : Fin d, (ν x j : 𝕜) * partialFunction [j] η x) * g x)
      =ᵐ[surfaceMeasure Ω] h := by
  constructor
  · filter_upwards [hg] with x hgx
    by_cases hx : x ∈ K
    · rw [hη x hx, one_mul]
    · simp [hgx hx]
  · filter_upwards [hg, hh] with x hgx hhx
    by_cases hx : x ∈ K
    · simp [hη x hx, fun j => hDη j x hx]
    · simp [hgx hx, hhx hx]

/-- The product rule becomes exact preservation of both prescribed jets
when the cutoff is one near their common compact support. -/
lemma hasDomainJets_cutoff_preserves {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (hc : IsC2Domain Ω) (hp : p ≠ ∞)
    (ν : Domain d → Domain d) (hν : IsOutwardNormal Ω ν)
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (η : Domain d → 𝕜) (hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖η x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] η x‖ ≤ C)
    (hDD : ∀ j k x, ‖partialFunction [k] (partialFunction [j] η) x‖ ≤ C)
    (K : Set (Domain d)) (hη : ∀ x ∈ K, η x = 1)
    (hDη : ∀ j : Fin d, ∀ x ∈ K, partialFunction [j] η x = 0)
    (u : SpaceValue 𝕜 d Ω 2 p) (g h : BoundaryLp 𝕜 Ω p)
    (hg : ∀ᵐ x ∂surfaceMeasure Ω, x ∉ K → g x = 0)
    (hh : ∀ᵐ x ∂surfaceMeasure Ω, x ∉ K → h x = 0)
    (hu : HasDomainJets ν T u g h) :
    HasDomainJets ν T
      (SecondTraceTransport.multiplyTwo η hηsmooth C hC0 hC hD hDD u) g h := by
  obtain ⟨g', h', hjet, hg', hh'⟩ := hasDomainJets_smooth_multiplication hΩ hc hp ν hν
    T hT η hηsmooth C hC0 hC hD hDD u g h hu
  obtain ⟨hgη, hhη⟩ := cutoff_jet_identity_ae K η hη hDη ν g h hg hh
  have hgg : g' = g := Lp.ext (hg'.trans hgη)
  have hhh : h' = h := Lp.ext (hh'.trans hhη)
  simpa only [hgg, hhh] using hjet

end ExpandedFA.PartIV.SecondTrace


noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal
namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SecondTraceFlat
open ExpandedFA.PartIV.SharpTraceBound
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

lemma higher_derivatives_supported {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (g : HigherFractionalSpace 𝕜 n s p) (K : Set (Domain n)) (hK : IsClosed K)
    (hg : ∀ᵐ x ∂volume, x ∉ K → wholeLp (g.val.val (zeroIndex n 1)) x = 0) :
    ∀ j, ∀ᵐ x ∂volume, x ∉ K → wholeLp (g.val.val (firstIndex j)) x = 0 := by
  have hgu : ∀ᵐ x ∂volume.restrict ((⊤ : Opens (Domain n)) : Set (Domain n)),
      x ∉ K → g.val.val (zeroIndex n 1) x = 0 := by
    simp only [Opens.coe_top, Measure.restrict_univ]
    filter_upwards [hg, wholeLp_representative (g.val.val (zeroIndex n 1))] with x hx hrep
    exact fun hxK => hrep.symm.trans (hx hxK)
  have hsupp := sobolev_components_supported_of_value_supported g.val K hK hgu
  intro j
  have hj := hsupp (firstIndex j)
  simp only [Opens.coe_top, Measure.restrict_univ] at hj
  filter_upwards [hj, wholeLp_representative (g.val.val (firstIndex j))] with x hx hrep
  exact fun hxK => hrep.trans (hx hxK)

/-- The correction solves the actual chart-normal equation everywhere and
has the same compact support as the independent data. Coefficients away
from that support are irrelevant because all actual weak derivatives vanish. -/
theorem compact_chart_corrected_datum {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (Φ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1))) (i : Fin (n+1))
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (K : Set (Domain n)) (hK : IsCompact K) (hKV : K ⊆ boundaryChartDomain Φ i)
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (g : HigherFractionalSpace 𝕜 n (s+1) p) (h : FractionalSpace 𝕜 n s p)
    (hg : ∀ᵐ z ∂volume, z ∉ K → wholeLp (g.val.val (zeroIndex n 1)) z = 0)
    (hh : ∀ᵐ z ∂volume, z ∉ K → h.val z = 0) :
    ∃ k : FractionalSpace 𝕜 n s p,
      (∀ᵐ z ∂volume,
        (chartNormalCoefficient Φ (chartOutwardNormal Φ i) i
          (Φ.symm (boundaryEmbedding i z)) : 𝕜) * k.val z +
        ∑ j : Fin n, (chartTangentialCoefficient Φ (chartOutwardNormal Φ i) i j
          (Φ.symm (boundaryEmbedding i z)) : 𝕜) *
            wholeLp (g.val.val (firstIndex j)) z = h.val z) ∧
      (∀ᵐ z ∂volume, z ∉ K → k.val z = 0) := by
  obtain ⟨a, b, δ, La, M, L, hδ, haneg, haL, haeq, hbeq, hbM, hbL⟩ :=
    exists_boundary_chart_coefficients Φ i hΦ hInv K hK hKV
  have haM (z) : δ ≤ ‖(a z : 𝕜)‖ := by
    rw [RCLike.norm_ofReal, abs_of_neg (lt_of_le_of_lt (haneg z) (neg_neg_of_pos hδ))]
    linarith [haneg z]
  have haLip (x y) : ‖(a x : 𝕜) - (a y : 𝕜)‖ ≤ La * euclideanLength (x-y) := by
    rw [← RCLike.ofReal_sub, RCLike.norm_ofReal]
    exact haL x y
  have hbBound (j x) : ‖(b j x : 𝕜)‖ ≤ M j := by
    rw [RCLike.norm_ofReal]
    exact hbM j x
  have hbLip (j x y) : ‖(b j x : 𝕜) - (b j y : 𝕜)‖ ≤ L j * euclideanLength (x-y) := by
    rw [← RCLike.ofReal_sub, RCLike.norm_ofReal]
    exact hbL j x y
  obtain ⟨k, hk, hks⟩ := corrected_fractional_datum_supported s p hs0 hs1 hp g h
    (fun z => (a z : 𝕜)) (fun j z => (b j z : 𝕜)) δ hδ La haM haLip M L hbBound hbLip
    K hK.isClosed hg hh
  have hqs := higher_derivatives_supported g K hK.isClosed hg
  refine ⟨k, ?_, hks⟩
  filter_upwards [hk, hks, hh, ae_all_iff.mpr hqs] with z hkz hksz hhz hqz
  by_cases hz : z ∈ K
  · have haz : (a z : 𝕜) = (chartNormalCoefficient Φ (chartOutwardNormal Φ i) i
        (Φ.symm (boundaryEmbedding i z)) : 𝕜) := congrArg (fun r : ℝ => (r : 𝕜)) (haeq hz)
    have hbz (j : Fin n) : (b j z : 𝕜) = (chartTangentialCoefficient Φ (chartOutwardNormal Φ i) i j
        (Φ.symm (boundaryEmbedding i z)) : 𝕜) := congrArg (fun r : ℝ => (r : 𝕜)) (hbeq j hz)
    simp only [← haz, ← hbz]
    rw [hkz]
    exact corrected_datum_algebra _ _ _ _ (norm_pos_iff.mp (hδ.trans_le (haM z)))
  · simp only [hksz hz, (fun j => hqz j hz), mul_zero, Finset.sum_const_zero, zero_add, hhz hz]

/-- A simultaneous flat lift with the corrected *curved-chart* normal jet.
The construction preserves independence of the two data and gives every
tangential derivative trace as its genuine weak boundary derivative. -/
theorem compact_chart_flat_jet_lift {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (Φ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1))) (i : Fin (n+1))
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (K : Set (Domain n)) (hK : IsCompact K) (hKV : K ⊆ boundaryChartDomain Φ i)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    (S : SpaceValue 𝕜 (n+1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))) (hS : CoordinateTraceCondition i S)
    (g : HigherFractionalSpace 𝕜 n (2 - 1 / p.toReal) p)
    (h : FractionalSpace 𝕜 n (1 - 1 / p.toReal) p)
    (hg : ∀ᵐ z ∂volume, z ∉ K → wholeLp (g.val.val (zeroIndex n 1)) z = 0)
    (hh : ∀ᵐ z ∂volume, z ∉ K → h.val z = 0) :
    ∃ u : SpaceValue 𝕜 (n+1) (upper i) 2 p,
      reindexedTrace i S (orderOnePart u) = wholeLp (g.val.val (zeroIndex n 1)) ∧
      (∀ j : Fin n, reindexedTrace i S (derivativePart (i.succAbove j) u) =
        wholeLp (g.val.val (firstIndex j))) ∧
      (∀ᵐ z ∂volume,
        (chartNormalCoefficient Φ (chartOutwardNormal Φ i) i
          (Φ.symm (boundaryEmbedding i z)) : 𝕜) *
            reindexedTrace i S (derivativePart i u) z +
        ∑ j : Fin n, (chartTangentialCoefficient Φ (chartOutwardNormal Φ i) i j
          (Φ.symm (boundaryEmbedding i z)) : 𝕜) *
            reindexedTrace i S (derivativePart (i.succAbove j) u) z = h.val z) ∧
      (∀ j : Fin (n+1), ∀ᵐ z ∂volume, z ∉ K →
        reindexedTrace i S (derivativePart j u) z = 0) := by
  letI : Fact (p ≠ ∞) := ⟨hp⟩
  have hc := compact_chart_corrected_datum (𝕜 := 𝕜) Φ i hΦ hInv K hK hKV
    (1 - 1 / p.toReal) p (endpoint_exponent hp1 hp).1 (endpoint_exponent hp1 hp).2 hp
  rw [show (1 - 1 / p.toReal) + 1 = 2 - 1 / p.toReal by ring] at hc
  obtain ⟨k, hk, hks⟩ := hc g h hg hh
  obtain ⟨_, _, hE⟩ := bounded_jet_extension_clm n p hp1 hp
  obtain ⟨E, _, hSmooth, hjets⟩ := hE 𝕜 i
  have hj := (hasBoundaryJets_iff i S _ _ _).mp (hjets S hS g k)
  have ht (j : Fin n) := jet_extension_tangential_trace p hp1 i E hSmooth S hS g k j
  refine ⟨E (g,k), hj.1, ht, ?_, ?_⟩
  · simpa only [hj.2, ht] using hk
  · intro j
    refine Fin.succAboveCases i ?_ (fun l => ?_) j
    · simpa only [hj.2] using hks
    · simpa only [ht] using higher_derivatives_supported g K hK.isClosed hg l

end ExpandedFA.PartIV.SecondTrace


noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal

namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.Sobolev.C1Extension ExpandedFA.PartIV.FractionalSobolev
open ExpandedFA.PartIV.SharpTrace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

namespace C2BoundaryModel
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : C2BoundaryModel 𝕜 Ω p)

def boundaryPieceBound (j : Fin B.chartCount) : ℝ :=
  Classical.choose (ambient_test_bounds (B.test j))

lemma boundaryPieceBound_bound (j : Fin B.chartCount) (x : Domain d) :
    ‖(B.test j x : 𝕜)‖ ≤ B.boundaryPieceBound j := by
  simpa only [boundaryPieceBound, RCLike.norm_ofReal, Real.norm_eq_abs] using
    (Classical.choose_spec (ambient_test_bounds (B.test j))).2.1 x

def boundaryPiece (j : Fin B.chartCount) : BoundaryLp 𝕜 Ω p →L[𝕜] BoundaryLp 𝕜 Ω p :=
  boundedLpMultiplyCLM (surfaceMeasure Ω) (fun x => (B.test j x : 𝕜))
    (RCLike.continuous_ofReal.comp (B.test j).continuous).aestronglyMeasurable
    (B.boundaryPieceBound j) (B.boundaryPieceBound_bound j)

lemma boundaryPiece_coe (j : Fin B.chartCount) (g : BoundaryLp 𝕜 Ω p) :
    B.boundaryPiece j g =ᵐ[surfaceMeasure Ω] fun x => (B.test j x : 𝕜) * g x :=
  boundedLpMultiplyCLM_coe (surfaceMeasure Ω) (fun x => (B.test j x : 𝕜))
    (RCLike.continuous_ofReal.comp (B.test j).continuous).aestronglyMeasurable
    (B.boundaryPieceBound j) (B.boundaryPieceBound_bound j) g

lemma test_sum (x : Domain d) (hx : x ∈ frontier (Ω : Set (Domain d))) :
    ∑ j, B.test j x = 1 := by
  simpa only [B.cutoff_eq] using B.atlas.cutoff_sum ⟨x,hx⟩

lemma sum_boundaryPiece (g : BoundaryLp 𝕜 Ω p) : ∑ j, B.boundaryPiece j g = g :=
  boundary_model_partition_reconstruction_real (fun j => B.test j) B.test_sum g
    (fun j => B.boundaryPiece j g) (fun j => B.boundaryPiece_coe j g)

lemma boundaryPiece_supported (j : Fin B.chartCount) (g : BoundaryLp 𝕜 Ω p) :
    ∀ᵐ x ∂surfaceMeasure Ω, x ∉ tsupport (B.test j) → B.boundaryPiece j g x = 0 := by
  filter_upwards [B.boundaryPiece_coe j g] with x hx hxs
  rw [hx, image_eq_zero_of_notMem_tsupport hxs, RCLike.ofReal_zero, zero_mul]

lemma boundaryPiece_mul_eq (j : Fin B.chartCount) (g : BoundaryLp 𝕜 Ω p)
    (η : Domain d → 𝕜) (hη : ∀ x ∈ tsupport (B.test j), η x = 1) :
    (fun x => η x * B.boundaryPiece j g x) =ᵐ[surfaceMeasure Ω] B.boundaryPiece j g := by
  filter_upwards [B.boundaryPiece_coe j g] with x hx
  by_cases hxs : x ∈ tsupport (B.test j)
  · rw [hη x hxs, one_mul]
  · rw [hx, image_eq_zero_of_notMem_tsupport hxs, RCLike.ofReal_zero, zero_mul, mul_zero]

/-- A faithful model transfers agreement of actual surface representatives
through its chart measure, without a global ambient Lipschitz assumption. -/
lemma surface_representative_pullback (j : Fin B.chartCount)
    (g : BoundaryLp 𝕜 Ω p) (f : Domain d → 𝕜)
    (hgf : g =ᵐ[surfaceMeasure Ω] f) :
    (fun z => g (((B.atlas.chart j).symm z).val)) =ᵐ[
      volume.restrict (B.atlas.chart j).target]
      fun z => f (((B.atlas.chart j).symm z).val) := by
  have hrep := (B.representative g g EventuallyEq.rfl).symm.trans
    (B.representative g f hgf)
  have hlocal := (ae_mono (B.atlas.chartMeasure_le j)) hrep
  exact ae_of_ae_map ((B.atlas.chart j).continuousOn_symm.aemeasurable
    (B.atlas.chart j).open_target.measurableSet) hlocal

end C2BoundaryModel

namespace C2BoundaryModel
variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {Ω : Opens (Domain (n+1))}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : C2BoundaryModel 𝕜 Ω p)

lemma chart_target (j : Fin B.chartCount) :
    (B.atlas.chart j).target = boundaryParameters (B.ambient j) (B.normal j) := by
  ext z
  constructor
  · exact B.insert_chart_mem j z
  · intro hz
    let x : Domain (n+1) := (B.ambient j).symm ((B.normal j).insertNth 0 z)
    have hxs : x ∈ (B.ambient j).source := (B.ambient j).map_target hz
    have hxf : x ∈ frontier (Ω : Set (Domain (n+1))) := by
      apply (chart_boundary_iff Ω (B.ambient j) (B.normal j) (B.side j) x hxs).mpr
      dsimp only [x]
      rw [(B.ambient j).right_inv hz]
      exact Fin.insertNth_apply_same _ _ _
    let x' : frontier (Ω : Set (Domain (n+1))) := ⟨x,hxf⟩
    have hxc : x' ∈ (B.atlas.chart j).source := by
      rw [B.chart_source]
      exact hxs
    have heq : B.atlas.chart j x' = z := by
      rw [B.chart_apply j x' hxc]
      change (B.normal j).removeNth (B.ambient j x) = z
      dsimp only [x]
      rw [(B.ambient j).right_inv hz]
      exact Fin.removeNth_insertNth _ _ _
    rw [← heq]
    exact (B.atlas.chart j).map_source hxc

lemma localizedLp_representative_global (j : Fin B.chartCount) (g : BoundaryLp 𝕜 Ω p) :
    B.atlas.localizedLp p j (B.identify g) =ᵐ[volume]
      (boundaryParameters (B.ambient j) (B.normal j)).indicator
        (fun z => (B.test j (boundaryParam (B.ambient j) (B.normal j) z) : 𝕜) *
          g (boundaryParam (B.ambient j) (B.normal j) z)) := by
  have hr := B.toBoundaryModel.localizedLp_representative j g
  filter_upwards [hr] with z hz
  rw [hz]
  unfold Boundary.FiniteAtlas.localizedRepresentative
  rw [B.chart_target j]
  by_cases hzV : z ∈ boundaryParameters (B.ambient j) (B.normal j)
  · rw [indicator_of_mem hzV, indicator_of_mem hzV]
    have ht : z ∈ (B.atlas.chart j).target := by rw [B.chart_target j]; exact hzV
    rw [B.cutoff_eq]
    dsimp only
    rw [B.chart_symm_val j z ht]
    rfl
  · rw [indicator_of_notMem hzV, indicator_of_notMem hzV]

lemma localizedLp_eq_boundaryPiece (j : Fin B.chartCount) (g : BoundaryLp 𝕜 Ω p) :
    B.atlas.localizedLp p j (B.identify g) =ᵐ[
      volume.restrict (boundaryParameters (B.ambient j) (B.normal j))]
      fun z => B.boundaryPiece j g (boundaryParam (B.ambient j) (B.normal j) z) := by
  have hl := (B.localizedLp_representative_global j g).restrict
    (s := boundaryParameters (B.ambient j) (B.normal j))
  have hpull := B.surface_representative_pullback j (B.boundaryPiece j g)
    (fun x => (B.test j x : 𝕜) * g x) (B.boundaryPiece_coe j g)
  rw [B.chart_target j] at hpull
  filter_upwards [hl, hpull,
    ae_restrict_mem (boundaryParameters_isOpen (B.ambient j) (B.normal j)).measurableSet]
    with z hz hp hzV
  rw [indicator_of_mem hzV] at hz
  have ht : z ∈ (B.atlas.chart j).target := by rw [B.chart_target j]; exact hzV
  change B.boundaryPiece j g (((B.atlas.chart j).symm z).val) =
    (B.test j (((B.atlas.chart j).symm z).val) : 𝕜) *
      g (((B.atlas.chart j).symm z).val) at hp
  rw [B.chart_symm_val j z ht] at hp
  exact hz.trans hp.symm

lemma localizedLp_eq_boundaryPiece_global (j : Fin B.chartCount) (g : BoundaryLp 𝕜 Ω p) :
    B.atlas.localizedLp p j (B.identify g) =ᵐ[volume]
      (boundaryParameters (B.ambient j) (B.normal j)).indicator
        (fun z => B.boundaryPiece j g (boundaryParam (B.ambient j) (B.normal j) z)) := by
  have hm := (boundaryParameters_isOpen (B.ambient j) (B.normal j)).measurableSet
  have hlocal := (ae_restrict_iff' hm).mp (B.localizedLp_eq_boundaryPiece j g)
  filter_upwards [B.localizedLp_representative_global j g, hlocal] with z hz hl
  by_cases hzV : z ∈ boundaryParameters (B.ambient j) (B.normal j)
  · rw [indicator_of_mem hzV]
    exact hl hzV
  · simp only [indicator_of_notMem hzV] at hz ⊢
    exact hz

lemma higherPiece_eq_boundaryPiece (σ : ℝ) (g : B.HigherData σ) (j : Fin B.chartCount) :
    wholeLp ((B.higherPiece σ g j).val.val (zeroIndex n 1)) =ᵐ[
      volume.restrict (boundaryParameters (B.ambient j) (B.normal j))]
      fun z => B.boundaryPiece j g.val (boundaryParam (B.ambient j) (B.normal j) z) := by
  have heq := B.higherPiece_spec σ g j
  change wholeLp ((B.higherPiece σ g j).val.val (zeroIndex n 1)) =
    B.atlas.localizedLp p j (B.identify g.val) at heq
  simpa only [heq] using B.localizedLp_eq_boundaryPiece j g.val

end C2BoundaryModel

lemma hasDomainJets_sum_of_boundaryPieces
    {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : C2BoundaryModel 𝕜 Ω p)
    (ν : Domain d → Domain d)
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
    (g h : BoundaryLp 𝕜 Ω p) (u : Fin B.chartCount → SpaceValue 𝕜 d Ω 2 p)
    (hlocal : ∀ j, HasDomainJets ν T (u j) (B.boundaryPiece j g) (B.boundaryPiece j h)) :
    HasDomainJets ν T (∑ j, u j) g h := by
  have hj := hasDomainJets_finsetSum Finset.univ u
    (fun j => B.boundaryPiece j g) (fun j => B.boundaryPiece j h) (fun j _ => hlocal j)
  simpa only [B.sum_boundaryPiece] using hj

end ExpandedFA.PartIV.SecondTrace


noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal
namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev

lemma normal_chain_contraction {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (A : Domain d →L[ℝ] Domain d) (ν : Domain d) (q : Fin d → 𝕜) :
    (∑ j : Fin d, (ν j : 𝕜) * ∑ k : Fin d, (A (coordinateVector j) k : 𝕜) * q k) =
      ∑ k : Fin d, (A ν k : 𝕜) * q k := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [derivative_coordinate_expansion A ν k, RCLike.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [RCLike.ofReal_mul, mul_assoc]

/-- Contraction of the actual weak coordinate-chain and product rule gives
the chart normal coefficient and retains precisely the cutoff derivative. -/
lemma normal_chart_jet_algebra {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (Φ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1)))
    (ν : Domain (n+1) → Domain (n+1)) (i : Fin (n+1)) (x : Domain (n+1))
    (η g : 𝕜) (Dη q : Fin (n+1) → 𝕜) :
    (∑ j : Fin (n+1), (ν x j : 𝕜) *
      (η * ∑ k : Fin (n+1), (fderiv ℝ Φ x (coordinateVector j) k : 𝕜) * q k + Dη j * g)) =
      η * ((chartNormalCoefficient Φ ν i x : 𝕜) * q i +
        ∑ k : Fin n, (chartTangentialCoefficient Φ ν i k x : 𝕜) * q (i.succAbove k)) +
      (∑ j : Fin (n+1), (ν x j : 𝕜) * Dη j) * g := by
  calc
    _ = η * (∑ j : Fin (n+1), (ν x j : 𝕜) *
        ∑ k : Fin (n+1), (fderiv ℝ Φ x (coordinateVector j) k : 𝕜) * q k) +
        (∑ j : Fin (n+1), (ν x j : 𝕜) * Dη j) * g := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      · rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = η * (∑ k : Fin (n+1), (fderiv ℝ Φ x (ν x) k : 𝕜) * q k) +
        (∑ j : Fin (n+1), (ν x j : 𝕜) * Dη j) * g := by
      rw [normal_chain_contraction]
    _ = _ := by
      rw [Fin.sum_univ_succAbove (fun k => (fderiv ℝ Φ x (ν x) k : 𝕜) * q k) i]
      rfl

end ExpandedFA.PartIV.SecondTrace


noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal Topology
namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.C1Extension.Transport
open ExpandedFA.Sobolev.HalfSpace
open ExpandedFA.Sobolev.C1Extension
open ExpandedFA.PartIV.SecondTraceTransport

/-- A compact subset of a genuine C² chart fits into a relatively compact
restriction with all first chart and inverse bounds, second coordinate bounds,
and Lipschitz constants in both directions. The ambient functions are unchanged. -/
lemma exists_c2_subchart_full_bounds {d : ℕ}
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (K : Set (Domain d)) (hK : IsCompact K) (hKs : K ⊆ Φ.source) :
    ∃ (Ψ : OpenPartialHomeomorph (Domain d) (Domain d)) (B J : ℝ) (L M : ℝ≥0),
      (Ψ : Domain d → Domain d) = Φ ∧
      (Ψ.symm : Domain d → Domain d) = Φ.symm ∧
      K ⊆ Ψ.source ∧ Ψ.source ⊆ Φ.source ∧ Ψ.target ⊆ Φ.target ∧
      ContDiffOn ℝ 2 Ψ Ψ.source ∧ ContDiffOn ℝ 2 Ψ.symm Ψ.target ∧
      0 ≤ B ∧ (∀ x ∈ Ψ.source, ‖fderiv ℝ Ψ x‖ ≤ B) ∧
      (∀ y ∈ Ψ.target, ‖fderiv ℝ Ψ.symm y‖ ≤ B) ∧
      (∀ j k l x, x ∈ Ψ.source →
        ‖fderiv ℝ (chartCoefficient Ψ j k) x (coordinateVector l)‖ ≤ B) ∧
      1 ≤ J ∧ (∀ y ∈ Ψ.target, |(fderiv ℝ Ψ.symm y).det| ≤ J) ∧
      Bornology.IsBounded Ψ.source ∧ Bornology.IsBounded Ψ.target ∧
      LipschitzOnWith L Ψ Ψ.source ∧ LipschitzOnWith M Ψ.symm Ψ.target ∧
      ∃ (U : Set (Domain d)) (hU : IsOpen U), Ψ = Φ.restrOpen U hU := by
  classical
  obtain ⟨U, hUo, hKU, hUs, hUc⟩ :=
    exists_open_between_and_isCompact_closure hK Φ.open_source hKs
  let Ψ := Φ.restrOpen U hUo
  have hsrc : Ψ.source ⊆ Φ.source := inter_subset_left
  have htgt : Ψ.target ⊆ Φ.target := inter_subset_left
  have himg : IsCompact (Φ '' closure U) :=
    hUc.image_of_continuousOn (hΦ.continuousOn.mono hUs)
  have himgtgt : Φ '' closure U ⊆ Φ.target := by
    rintro y ⟨x, hx, rfl⟩
    exact Φ.map_source (hUs hx)
  have htimg : Ψ.target ⊆ Φ '' closure U := by
    intro y hy
    exact ⟨Ψ.symm y, subset_closure (Ψ.map_target hy).2, Ψ.right_inv hy⟩
  obtain ⟨A, hA⟩ := hUc.exists_bound_of_continuousOn
    ((hΦ.continuousOn_fderiv_of_isOpen Φ.open_source (by norm_num)).mono hUs)
  obtain ⟨A', hA'⟩ := himg.exists_bound_of_continuousOn
    ((hInv.continuousOn_fderiv_of_isOpen Φ.open_target (by norm_num)).mono himgtgt)
  have hd (q : Fin d × Fin d × Fin d) : ∃ D : ℝ, ∀ x ∈ closure U,
      ‖fderiv ℝ (chartCoefficient Φ q.1 q.2.1) x (coordinateVector q.2.2)‖ ≤ D :=
    hUc.exists_bound_of_continuousOn
      ((Classical.c1_partial_continuousOn (Ω := ⟨Φ.source, Φ.open_source⟩)
        _ (chartCoefficient_c1 Φ hΦ q.1 q.2.1) q.2.2).mono hUs)
  choose D hD using hd
  let S : ℝ := ∑ q : Fin d × Fin d × Fin d, max 0 (D q)
  let B := max 0 A + max 0 A' + S
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hB0 : 0 ≤ B := add_nonneg
    (add_nonneg (le_max_left _ _) (le_max_left _ _)) hS
  have hAB : A ≤ B := by dsimp [B]; linarith [le_max_right 0 A, le_max_left 0 A']
  have hA'B : A' ≤ B := by dsimp [B]; linarith [le_max_left 0 A, le_max_right 0 A']
  have hSB : S ≤ B := by dsimp [B]; linarith [le_max_left 0 A, le_max_left 0 A']
  have hdet : ContinuousOn (fun y => (fderiv ℝ Φ.symm y).det) Φ.target :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (hInv.continuousOn_fderiv_of_isOpen Φ.open_target (by norm_num))
  obtain ⟨J, hJ⟩ := himg.exists_bound_of_continuousOn (hdet.mono himgtgt)
  have hLf : ∃ L : ℝ≥0, LipschitzOnWith L Φ (closure U) := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hUc
    intro x hx
    obtain ⟨L, V, hV, hLip⟩ :=
      ((hΦ.of_le (by norm_num)).contDiffAt (Φ.open_source.mem_nhds (hUs hx))).exists_lipschitzOnWith
    exact ⟨L, V, mem_nhdsWithin_of_mem_nhds hV, hLip⟩
  obtain ⟨L, hL⟩ := hLf
  have hMi : ∃ M : ℝ≥0, LipschitzOnWith M Φ.symm (Φ '' closure U) := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact himg
    intro y hy
    obtain ⟨M, V, hV, hLip⟩ :=
      ((hInv.of_le (by norm_num)).contDiffAt (Φ.open_target.mem_nhds (himgtgt hy))).exists_lipschitzOnWith
    exact ⟨M, V, mem_nhdsWithin_of_mem_nhds hV, hLip⟩
  obtain ⟨M, hM⟩ := hMi
  refine ⟨Ψ, B, max 1 J, L, M, rfl, rfl, (fun x hx => ⟨hKs hx, hKU hx⟩),
    hsrc, htgt, hΦ.mono hsrc, hInv.mono htgt, hB0, ?_, ?_, ?_,
    le_max_left _ _, ?_, hUc.isBounded.subset (fun x hx => subset_closure hx.2),
    himg.isBounded.subset htimg,
    hL.mono (fun x hx => subset_closure hx.2), hM.mono htimg, ⟨U, hUo, rfl⟩⟩
  · intro x hx
    exact (hA x (subset_closure hx.2)).trans hAB
  · intro y hy
    exact (hA' y (htimg hy)).trans hA'B
  · intro j k l x hx
    have hsingle : max 0 (D (j,k,l)) ≤ S :=
      Finset.single_le_sum (fun q _ => le_max_left _ _) (Finset.mem_univ _)
    exact (hD (j,k,l) x (subset_closure hx.2)).trans
      ((le_max_right _ _).trans (hsingle.trans hSB))
  · intro y hy
    exact (hJ y (htimg hy)).trans (le_max_right _ _)

end ExpandedFA.PartIV.SecondTrace


noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal
namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.SecondTraceFlat ExpandedFA.PartIV.SharpTrace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- Raw parameter equalities determine both actual surface quotient jets
when the two representatives also agree outside the physical chart. -/
lemma hasDomainJets_of_chart_pullback_equalities
    {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {Ω : Opens (Domain (n+1))}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (ν : Domain (n+1) → Domain (n+1)) (hν : IsOutwardNormal Ω ν)
    (T : SpaceValue 𝕜 (n+1) Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
    (V : SpaceValue 𝕜 (n+1) Ω 2 p) (G H : BoundaryLp 𝕜 Ω p)
    (Φ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1))) (i : Fin (n+1))
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    {K L : ℝ≥0} (hLip : LipschitzOnWith K Φ Φ.source)
    (hInvLip : LipschitzOnWith L Φ.symm Φ.target)
    (hvalue : (fun z => T (orderOnePart V) (boundaryParam Φ i z)) =ᵐ[
      volume.restrict (boundaryParameters Φ i)] fun z => G (boundaryParam Φ i z))
    (hnormal : (fun z => ∑ j : Fin (n+1), (ν (boundaryParam Φ i z) j : 𝕜) *
        T (derivativePart j V) (boundaryParam Φ i z)) =ᵐ[
      volume.restrict (boundaryParameters Φ i)] fun z => H (boundaryParam Φ i z))
    (hvalueOutside : ∀ᵐ x ∂surfaceMeasure Ω,
      x ∉ Φ.source → T (orderOnePart V) x = G x)
    (hnormalOutside : ∀ᵐ x ∂surfaceMeasure Ω,
      x ∉ Φ.source → ∑ j : Fin (n+1), (ν x j : 𝕜) * T (derivativePart j V) x = H x) :
    HasDomainJets ν T V G H := by
  rw [hasDomainJets_iff_normalTrace ν hν]
  refine ⟨boundary_eq_of_chart_pullback_eq Ω Φ i hside hLip hInvLip
    (T (orderOnePart V)) G hvalue hvalueOutside, ?_⟩
  have hrep := normalTrace_representative ν hν T V
  obtain ⟨C, hC, hmap⟩ := boundaryParam_map_le_surfaceMeasure Ω Φ i hside hLip
  have hac : (volume.restrict (boundaryParameters Φ i)).map (boundaryParam Φ i) ≪
      surfaceMeasure Ω :=
    (Measure.absolutelyContinuous_of_le_smul hmap).trans
      Measure.restrict_le_self.absolutelyContinuous
  have hpull := ae_of_ae_map (boundaryParam_aemeasurable Φ i) (hac.ae_eq hrep)
  have hpull' : (fun z => normalTrace ν hν T V (boundaryParam Φ i z)) =ᵐ[
      volume.restrict (boundaryParameters Φ i)]
      (fun z => ∑ j : Fin (n+1), (ν (boundaryParam Φ i z) j : 𝕜) *
        T (derivativePart j V) (boundaryParam Φ i z)) := hpull
  apply boundary_eq_of_chart_pullback_eq Ω Φ i hside hLip hInvLip
    (normalTrace ν hν T V) H (hpull'.trans hnormal)
  filter_upwards [hrep, hnormalOutside] with x hx hxo hxs
  exact hx.trans (hxo hxs)

/-- A convenient supported version: zero first derivative traces and zero
prescribed data outside the chart supply the exterior equality automatically. -/
lemma hasDomainJets_of_supported_chart_pullback_equalities
    {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {Ω : Opens (Domain (n+1))}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (ν : Domain (n+1) → Domain (n+1)) (hν : IsOutwardNormal Ω ν)
    (T : SpaceValue 𝕜 (n+1) Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
    (V : SpaceValue 𝕜 (n+1) Ω 2 p) (G H : BoundaryLp 𝕜 Ω p)
    (Φ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1))) (i : Fin (n+1))
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    {K L : ℝ≥0} (hLip : LipschitzOnWith K Φ Φ.source)
    (hInvLip : LipschitzOnWith L Φ.symm Φ.target)
    (hvalue : (fun z => T (orderOnePart V) (boundaryParam Φ i z)) =ᵐ[
      volume.restrict (boundaryParameters Φ i)] fun z => G (boundaryParam Φ i z))
    (hnormal : (fun z => ∑ j : Fin (n+1), (ν (boundaryParam Φ i z) j : 𝕜) *
        T (derivativePart j V) (boundaryParam Φ i z)) =ᵐ[
      volume.restrict (boundaryParameters Φ i)] fun z => H (boundaryParam Φ i z))
    (hvalueOutside : ∀ᵐ x ∂surfaceMeasure Ω, x ∉ Φ.source → T (orderOnePart V) x = 0)
    (hderivativeOutside : ∀ j : Fin (n+1), ∀ᵐ x ∂surfaceMeasure Ω,
      x ∉ Φ.source → T (derivativePart j V) x = 0)
    (hGOutside : ∀ᵐ x ∂surfaceMeasure Ω, x ∉ Φ.source → G x = 0)
    (hHOutside : ∀ᵐ x ∂surfaceMeasure Ω, x ∉ Φ.source → H x = 0) :
    HasDomainJets ν T V G H := by
  apply hasDomainJets_of_chart_pullback_equalities ν hν T V G H Φ i hside
    hLip hInvLip hvalue hnormal
  · filter_upwards [hvalueOutside, hGOutside] with x hx hG hxs
    rw [hx hxs, hG hxs]
  · filter_upwards [ae_all_iff.mpr hderivativeOutside, hHOutside] with x hx hH hxs
    simp only [fun j => hx j hxs, mul_zero, Finset.sum_const_zero, hH hxs]

end ExpandedFA.PartIV.SecondTrace


noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.FractionalSobolev
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

lemma subchart_target_subset {d : ℕ}
    (Φ Ψ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hfun : (Ψ : Domain d → Domain d) = Φ)
    (hsource : Ψ.source ⊆ Φ.source) : Ψ.target ⊆ Φ.target := by
  intro y hy
  have hx := hsource (Ψ.map_target hy)
  have heq : Φ (Ψ.symm y) = y := by rw [← hfun]; exact Ψ.right_inv hy
  rw [← heq]
  exact Φ.map_source hx

lemma subchart_boundaryParameters_subset {n : ℕ}
    (Φ Ψ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1)))
    (i : Fin (n+1))
    (hfun : (Ψ : Domain (n+1) → Domain (n+1)) = Φ)
    (hsource : Ψ.source ⊆ Φ.source) :
    boundaryParameters Ψ i ⊆ boundaryParameters Φ i :=
  fun _ hz => subchart_target_subset Φ Ψ hfun hsource hz

namespace C2BoundaryModel
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : C2BoundaryModel 𝕜 Ω p)

lemma cutoff_support_ambient (j : Fin B.chartCount) :
    tsupport (B.atlas.cutoff j) ⊆ Subtype.val ⁻¹' tsupport (B.test j) := by
  have heq : B.atlas.cutoff j = (B.test j) ∘ Subtype.val := funext (B.cutoff_eq j)
  rw [heq]
  exact tsupport_comp_subset_preimage (B.test j) continuous_subtype_val

lemma boundaryPiece_supported_subchart (j : Fin B.chartCount)
    (Ψ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hcut : tsupport (B.test j) ⊆ Ψ.source) (g : BoundaryLp 𝕜 Ω p) :
    ∀ᵐ x ∂surfaceMeasure Ω, x ∉ Ψ.source → B.boundaryPiece j g x = 0 := by
  filter_upwards [B.boundaryPiece_supported j g] with x hx hxout
  exact hx (fun hxs => hxout (hcut hxs))

end C2BoundaryModel

namespace C2BoundaryModel
variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {Ω : Opens (Domain (n+1))}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : C2BoundaryModel 𝕜 Ω p)

lemma coordinateSupport_subset_subchart (j : Fin B.chartCount)
    (Ψ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1)))
    (hfun : (Ψ : Domain (n+1) → Domain (n+1)) = B.ambient j)
    (hcut : tsupport (B.test j) ⊆ Ψ.source) :
    B.coordinateSupport j ⊆ boundaryParameters Ψ (B.normal j) := by
  rintro z ⟨x,hxs,rfl⟩
  have hxΨ : x.val ∈ Ψ.source := hcut (B.cutoff_support_ambient j hxs)
  have hxc := B.atlas.cutoff_subordinate j hxs
  change (B.normal j).insertNth 0 (B.atlas.chart j x) ∈ Ψ.target
  rw [B.insert_chart j x hxc, ← hfun]
  exact Ψ.map_source hxΨ

lemma coordinateSupport_param_in_test_support (j : Fin B.chartCount)
    (Ψ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1)))
    (hinv : (Ψ.symm : Domain (n+1) → Domain (n+1)) = (B.ambient j).symm)
    {z : Domain n} (hz : z ∈ B.coordinateSupport j) :
    boundaryParam Ψ (B.normal j) z ∈ tsupport (B.test j) := by
  rcases hz with ⟨x,hxs,rfl⟩
  have hxc := B.atlas.cutoff_subordinate j hxs
  have hxa : x.val ∈ (B.ambient j).source := by
    simpa only [B.chart_source j, mem_preimage] using hxc
  unfold boundaryParam
  rw [hinv, B.insert_chart j x hxc, (B.ambient j).left_inv hxa]
  exact B.cutoff_support_ambient j hxs

lemma cutoff_one_on_coordinateSupport (j : Fin B.chartCount)
    (Ψ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1)))
    (hinv : (Ψ.symm : Domain (n+1) → Domain (n+1)) = (B.ambient j).symm)
    (η : Domain (n+1) → 𝕜) (hη : ∀ x ∈ tsupport (B.test j), η x = 1) :
    ∀ z ∈ B.coordinateSupport j, η (boundaryParam Ψ (B.normal j) z) = 1 := by
  intro z hz
  exact hη _ (B.coordinateSupport_param_in_test_support j Ψ hinv hz)

lemma cutoff_derivative_zero_on_coordinateSupport (j : Fin B.chartCount)
    (Ψ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1)))
    (hinv : (Ψ.symm : Domain (n+1) → Domain (n+1)) = (B.ambient j).symm)
    (η : Domain (n+1) → 𝕜)
    (hη : ∀ x ∈ tsupport (B.test j), fderiv ℝ η x = 0) :
    ∀ z ∈ B.coordinateSupport j,
      fderiv ℝ η (boundaryParam Ψ (B.normal j) z) = 0 := by
  intro z hz
  exact hη _ (B.coordinateSupport_param_in_test_support j Ψ hinv hz)

lemma localizedLp_eq_boundaryPiece_subchart (j : Fin B.chartCount)
    (Ψ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1)))
    (hfun : (Ψ : Domain (n+1) → Domain (n+1)) = B.ambient j)
    (hinv : (Ψ.symm : Domain (n+1) → Domain (n+1)) = (B.ambient j).symm)
    (hsource : Ψ.source ⊆ (B.ambient j).source) (g : BoundaryLp 𝕜 Ω p) :
    B.atlas.localizedLp p j (B.identify g) =ᵐ[
      volume.restrict (boundaryParameters Ψ (B.normal j))]
      fun z => B.boundaryPiece j g (boundaryParam Ψ (B.normal j) z) := by
  have hparam := subchart_boundaryParameters_subset (B.ambient j) Ψ (B.normal j) hfun hsource
  have hr := (B.localizedLp_eq_boundaryPiece j g).filter_mono
    (ae_mono (Measure.restrict_mono hparam le_rfl))
  simpa only [boundaryParam, hinv] using hr

lemma higherPiece_eq_boundaryPiece_subchart (σ : ℝ) (g : B.HigherData σ)
    (j : Fin B.chartCount)
    (Ψ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1)))
    (hfun : (Ψ : Domain (n+1) → Domain (n+1)) = B.ambient j)
    (hinv : (Ψ.symm : Domain (n+1) → Domain (n+1)) = (B.ambient j).symm)
    (hsource : Ψ.source ⊆ (B.ambient j).source) :
    wholeLp ((B.higherPiece σ g j).val.val (zeroIndex n 1)) =ᵐ[
      volume.restrict (boundaryParameters Ψ (B.normal j))]
      fun z => B.boundaryPiece j g.val (boundaryParam Ψ (B.normal j) z) := by
  have heq := B.higherPiece_spec σ g j
  change wholeLp ((B.higherPiece σ g j).val.val (zeroIndex n 1)) =
    B.atlas.localizedLp p j (B.identify g.val) at heq
  simpa only [heq] using B.localizedLp_eq_boundaryPiece_subchart j Ψ hfun hinv hsource g.val

lemma fractionalPiece_eq_boundaryPiece_subchart (s : ℝ) (h : B.toBoundaryModel.Data s)
    (j : Fin B.chartCount)
    (Ψ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1)))
    (hfun : (Ψ : Domain (n+1) → Domain (n+1)) = B.ambient j)
    (hinv : (Ψ.symm : Domain (n+1) → Domain (n+1)) = (B.ambient j).symm)
    (hsource : Ψ.source ⊆ (B.ambient j).source) :
    (B.fractionalPiece s h j).val =ᵐ[
      volume.restrict (boundaryParameters Ψ (B.normal j))]
      fun z => B.boundaryPiece j h.val (boundaryParam Ψ (B.normal j) z) :=
  B.localizedLp_eq_boundaryPiece_subchart j Ψ hfun hinv hsource h.val

lemma localizedLp_eq_boundaryPiece_subchart_global (j : Fin B.chartCount)
    (Ψ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1)))
    (hfun : (Ψ : Domain (n+1) → Domain (n+1)) = B.ambient j)
    (hinv : (Ψ.symm : Domain (n+1) → Domain (n+1)) = (B.ambient j).symm)
    (hsource : Ψ.source ⊆ (B.ambient j).source)
    (hcut : tsupport (B.test j) ⊆ Ψ.source) (g : BoundaryLp 𝕜 Ω p) :
    B.atlas.localizedLp p j (B.identify g) =ᵐ[volume]
      (boundaryParameters Ψ (B.normal j)).indicator
        (fun z => B.boundaryPiece j g (boundaryParam Ψ (B.normal j) z)) := by
  have hm := (boundaryParameters_isOpen Ψ (B.normal j)).measurableSet
  have hlocal := (ae_restrict_iff' hm).mp
    (B.localizedLp_eq_boundaryPiece_subchart j Ψ hfun hinv hsource g)
  filter_upwards [hlocal, B.localizedLp_supported j g] with z hl hz
  by_cases hzV : z ∈ boundaryParameters Ψ (B.normal j)
  · rw [indicator_of_mem hzV]
    exact hl hzV
  · rw [indicator_of_notMem hzV]
    exact hz (fun hzK => hzV (B.coordinateSupport_subset_subchart j Ψ hfun hcut hzK))

end C2BoundaryModel
end ExpandedFA.PartIV.SecondTrace


noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Trace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.Sobolev.C1Extension.Transport
open ExpandedFA.PartIV.SharpTrace ExpandedFA.PartIV.SecondTraceFlat
open ExpandedFA.PartIV.SecondTraceTransport
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

section
variable (a : Domain d → 𝕜) (ha : ContDiff ℝ 1 a)
  (C : ℝ) (hC : ∀ x, ‖a x‖ ≤ C)
  (hD : ∀ j x, ‖fderiv ℝ a x (coordinateVector j)‖ ≤ C)

def c1LpMultiplier : DomainLp 𝕜 Ω p →L[𝕜] DomainLp 𝕜 Ω p :=
  boundedLpMultiplyCLM (volume.restrict (Ω : Set (Domain d))) a ha.continuous.aestronglyMeasurable C hC

def c1DerivativeLpMultiplier (j : Fin d) : DomainLp 𝕜 Ω p →L[𝕜] DomainLp 𝕜 Ω p :=
  boundedLpMultiplyCLM (volume.restrict (Ω : Set (Domain d)))
    (fun x => fderiv ℝ a x (coordinateVector j))
    ((ha.continuous_fderiv (by norm_num)).clm_apply continuous_const).aestronglyMeasurable C (hD j)

def c1MultiplyJet : SpaceValue 𝕜 d Ω 1 p →L[𝕜] DerivativeTuple 𝕜 Ω 1 p :=
  firstTuple ((c1LpMultiplier a ha C hC).comp (evalOne (zeroIndex d 1)))
    (fun j => (c1LpMultiplier a ha C hC).comp (evalOne (coordinateIndex j)) +
      (c1DerivativeLpMultiplier a ha C hD j).comp (evalOne (zeroIndex d 1)))

lemma c1MultiplyJet_zero_coe (u : SpaceValue 𝕜 d Ω 1 p) :
    c1MultiplyJet a ha C hC hD u (zeroIndex d 1) =ᵐ[
      volume.restrict (Ω : Set (Domain d))] fun x => a x * u.val (zeroIndex d 1) x := by
  simp only [c1MultiplyJet, firstTuple_zero, ContinuousLinearMap.comp_apply]
  exact boundedLpMultiplyCLM_coe _ _ _ _ _ _

lemma c1MultiplyJet_coordinate_coe (u : SpaceValue 𝕜 d Ω 1 p) (j : Fin d) :
    c1MultiplyJet a ha C hC hD u (coordinateIndex j) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun x => a x * u.val (coordinateIndex j) x +
        fderiv ℝ a x (coordinateVector j) * u.val (zeroIndex d 1) x := by
  simp only [c1MultiplyJet, firstTuple_coordinate, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply]
  exact (Lp.coeFn_add _ _).trans ((boundedLpMultiplyCLM_coe _ _ _ _ _ _).add
    (boundedLpMultiplyCLM_coe _ _ _ _ _ _))

lemma c1MultiplyJet_mem_smooth (u : SpaceValue 𝕜 d Ω 1 p)
    (f : Domain d → 𝕜) (hf : ContDiffOn ℝ 1 f Ω)
    (hu : u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f) :
    c1MultiplyJet a ha C hC hD u ∈ derivativeGraph 𝕜 Ω 1 p := by
  apply Classical.c1_firstJet_mem (fun x => a x * f x) (ha.contDiffOn.mul hf)
  · exact (c1MultiplyJet_zero_coe a ha C hC hD u).trans (hu.mono (fun x hx => congrArg (a x * ·) hx))
  · intro j
    apply (c1MultiplyJet_coordinate_coe a ha C hC hD u j).trans
    filter_upwards [hu, Classical.c1_representative_derivative u f hf hu j,
      ae_restrict_mem Ω.isOpen.measurableSet] with x hx hdx hxΩ
    have hda := ha.differentiable (by norm_num) x
    have hdf := (hf.contDiffAt (Ω.isOpen.mem_nhds hxΩ)).differentiableAt (by simp)
    rw [hx, hdx]
    change _ = fderiv ℝ (a * f) x (coordinateVector j)
    rw [fderiv_mul hda hdf]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

lemma c1MultiplyJet_mem (hp : p ≠ ∞) (u : SpaceValue 𝕜 d Ω 1 p) :
    c1MultiplyJet a ha C hC hD u ∈ derivativeGraph 𝕜 Ω 1 p := by
  have hc : IsClosed {u : SpaceValue 𝕜 d Ω 1 p |
      c1MultiplyJet a ha C hC hD u ∈ derivativeGraph 𝕜 Ω 1 p} :=
    Smoothing.derivativeGraph_isClosed.preimage (c1MultiplyJet a ha C hC hD).continuous
  have hsub : Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity.SmoothMembers
      𝕜 d Ω 1 p ⊆ {u : SpaceValue 𝕜 d Ω 1 p |
        c1MultiplyJet a ha C hC hD u ∈ derivativeGraph 𝕜 Ω 1 p} := by
    rintro v ⟨f, hf, hv⟩
    exact c1MultiplyJet_mem_smooth a ha C hC hD v f (hf.of_le (by simp)) hv
  exact (hc.closure_subset_iff.mpr hsub) (Smoothing.smooth_density 𝕜 d Ω 1 p hp u)

def c1Multiply (hp : p ≠ ∞) : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p :=
  (c1MultiplyJet a ha C hC hD).codRestrict (derivativeGraph 𝕜 Ω 1 p)
    (c1MultiplyJet_mem a ha C hC hD hp)

lemma c1Multiply_coe (hp : p ≠ ∞) (u : SpaceValue 𝕜 d Ω 1 p) :
    (c1Multiply a ha C hC hD hp u).val (zeroIndex d 1) =ᵐ[
      volume.restrict (Ω : Set (Domain d))] fun x => a x * u.val (zeroIndex d 1) x :=
  c1MultiplyJet_zero_coe a ha C hC hD u
end

end ExpandedFA.PartIV.SecondTrace


noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Trace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.Sobolev.C1Extension.Transport
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound
open ExpandedFA.PartIV.SharpTrace ExpandedFA.PartIV.SecondTraceFlat
open ExpandedFA.PartIV.SecondTraceTransport
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω Λ : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma localizedZeroExtension_coordinate_coe (h : Ω ≤ Λ) (K : Set (Domain d))
    (hK : IsClosed (K ∪ (Λ : Set (Domain d))ᶜ)) (hKΩ : K ⊆ Ω)
    (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖a x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C)
    (hcoeff : (Ω : Set (Domain d)) ∩ tsupport a ⊆ K)
    (u : SpaceValue 𝕜 d Ω 1 p) (j : Fin d) :
    (localizedZeroExtension h K hK hKΩ a ha C hC0 hC hD hcoeff u).val (coordinateIndex j)
      =ᵐ[volume.restrict (Λ : Set (Domain d))]
        (Ω : Set (Domain d)).indicator (fun x => a x * u.val (coordinateIndex j) x +
          partialFunction [j] a x * u.val (zeroIndex d 1) x) := by
  have hm : (ambientMultiply a ha C hC0 hC hD u).val (coordinateIndex j) =ᵐ[
      volume.restrict (Ω : Set (Domain d))] fun x => a x * u.val (coordinateIndex j) x +
        partialFunction [j] a x * u.val (zeroIndex d 1) x := by
    change ambientMultiplyJet a ha C hC hD u.val (coordinateIndex j) =ᵐ[_] _
    rw [ambientMultiplyJet_coordinate]
    filter_upwards [Lp.coeFn_add
      (boundedMulLp a ha.continuous C hC (u.val (coordinateIndex j)))
      (boundedMulLp (partialFunction [j] a) (Smoothing.partialFunction_contDiff _ a ha).continuous C
        (hD j) (u.val (zeroIndex d 1))),
      boundedMulLp_coe a ha.continuous C hC (u.val (coordinateIndex j)),
      boundedMulLp_coe (partialFunction [j] a)
        (Smoothing.partialFunction_contDiff _ a ha).continuous C (hD j) (u.val (zeroIndex d 1))]
      with x hx h₁ h₂
    rw [hx]
    simp only [Pi.add_apply, h₁, h₂]
  have hm' := ((ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).mp hm).filter_mono
    (ae_mono (Measure.restrict_le_self (s := (Λ : Set (Domain d)))))
  exact (zeroLp_coe ((ambientMultiply a ha C hC0 hC hD u).val (coordinateIndex j))).trans hm'

/-- A localized chart pullback with its actual first weak chain and product rule. -/
theorem exists_localized_chart_pullback_with_derivatives
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
    (J : ℝ) (hJ1 : 1 ≤ J) (hJ : ∀ x ∈ Φ.target, |(fderiv ℝ Φ.symm x).det| ≤ J)
    (hTarget : Bornology.IsBounded Φ.target)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ Φ x ∈ Λ)
    (θ : Tests 𝕜 (⊤ : Opens (Domain d))) (hθ : tsupport θ ⊆ Φ.source) :
    ∃ F : SpaceValue 𝕜 d Λ 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p,
      (∀ (u : SpaceValue 𝕜 d Λ 1 p) (f : Domain d → 𝕜),
        u.val (zeroIndex d 1) =ᵐ[volume.restrict (Λ : Set (Domain d))] f →
        (F u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
          fun x => θ x * f (Φ x)) ∧
      (∀ (u : SpaceValue 𝕜 d Λ 1 p) j,
        (F u).val (coordinateIndex j) =ᵐ[volume.restrict (Ω : Set (Domain d))]
          fun x => θ x * ∑ k, (chartCoefficient Φ j k x : 𝕜) * u.val (coordinateIndex k) (Φ x) +
            partialFunction [j] θ x * u.val (zeroIndex d 1) (Φ x)) := by
  let V := chartPreimage Φ Λ
  let W := chartTarget Φ Λ
  have hVΩ : V ≤ Ω := fun x hx => (hside x hx.1).mpr hx.2
  let K : Set (Domain d) := tsupport θ ∩ (Ω : Set (Domain d))
  have hKclosed : IsClosed (K ∪ (Ω : Set (Domain d))ᶜ) := by
    have heq : K ∪ (Ω : Set (Domain d))ᶜ = tsupport θ ∪ (Ω : Set (Domain d))ᶜ := by
      ext x
      simp only [K, mem_union, mem_inter_iff, mem_compl_iff]
      tauto
    rw [heq]
    exact (isClosed_tsupport θ).union Ω.isOpen.isClosed_compl
  have hKV : K ⊆ V := fun x hx => ⟨hθ hx.1, (hside x (hθ hx.1)).mp hx.2⟩
  have hθK : (V : Set (Domain d)) ∩ tsupport θ ⊆ K := fun x hx => ⟨hx.2, hVΩ hx.1⟩
  obtain ⟨C, hC0, hC, hD⟩ := ambient_test_bounds θ
  let M : SpaceValue 𝕜 d V 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p :=
    localizedZeroExtension hVΩ K hKclosed hKV θ θ.contDiff C hC0 hC hD hθK
  let Q : SpaceValue 𝕜 d W 1 p →L[𝕜] SpaceValue 𝕜 d V 1 p :=
    chartSobolevPull Φ hΦ hInv B hB hB0 J hJ hJ1 Λ hTarget
  let R : SpaceValue 𝕜 d Λ 1 p →L[𝕜] SpaceValue 𝕜 d W 1 p :=
    restrictSobolev (show W ≤ Λ from inter_subset_left)
  have hf (u : SpaceValue 𝕜 d Λ 1 p) : (Q (R u)).val (zeroIndex d 1) =ᵐ[
      volume.restrict (V : Set (Domain d))] fun x => u.val (zeroIndex d 1) (Φ x) := by
    apply chartSobolevPull_coe Φ hΦ hInv B hB hB0 J hJ hJ1 Λ hTarget
    exact (restrictSobolev_coe inter_subset_left u (zeroIndex d 1)).symm
  have hd (u : SpaceValue 𝕜 d Λ 1 p) (j : Fin d) :
      (Q (R u)).val (coordinateIndex j) =ᵐ[volume.restrict (V : Set (Domain d))]
        fun x => ∑ k, (chartCoefficient Φ j k x : 𝕜) * u.val (coordinateIndex k) (Φ x) := by
    have hac : (volume.restrict (V : Set (Domain d))).map Φ ≪ volume.restrict (W : Set (Domain d)) :=
      Measure.absolutelyContinuous_of_le_smul (chart_map_measure_le Φ hInv J hJ Λ)
    have hr (k : Fin d) := ae_of_ae_map (chart_aemeasurable Φ Λ)
      (hac.ae_eq (restrictSobolev_coe inter_subset_left u (coordinateIndex k)))
    filter_upwards [chartSobolevPull_coordinate_coe Φ hΦ hInv B hB hB0 J hJ hJ1 Λ hTarget
      (R u) j, ae_all_iff.mpr hr] with x hx hrest
    rw [hx]
    apply Finset.sum_congr rfl
    intro k _
    rw [hrest k, RCLike.real_smul_eq_coe_mul]
  refine ⟨M.comp (Q.comp R), ?_, ?_⟩
  · intro u f hu
    have hq := chartSobolevPull_coe Φ hΦ hInv B hB hB0 J hJ hJ1 Λ hTarget (R u) f
      ((hu.filter_mono (ae_mono (Measure.restrict_mono inter_subset_left le_rfl))).symm.trans
        (restrictSobolev_coe inter_subset_left u (zeroIndex d 1)).symm)
    have hm := localizedZeroExtension_representative hVΩ K hKclosed hKV θ θ.contDiff
      C hC0 hC hD hθK (Q (R u)) (f ∘ Φ) hq.symm
    change (M (Q (R u))).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] _
    filter_upwards [hm, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
    rw [hx]
    change (V : Set (Domain d)).indicator (fun y => θ y * f (Φ y)) x = θ x * f (Φ x)
    by_cases hxV : x ∈ V
    · exact indicator_of_mem hxV _
    · rw [indicator_of_notMem hxV]
      have hxθ : x ∉ tsupport θ := fun hh => hxV ⟨hθ hh, (hside x (hθ hh)).mp hxΩ⟩
      rw [image_eq_zero_of_notMem_tsupport hxθ, zero_mul]
  · intro u j
    have hloc : (fun x => θ x * (Q (R u)).val (coordinateIndex j) x +
        partialFunction [j] θ x * (Q (R u)).val (zeroIndex d 1) x) =ᵐ[
        volume.restrict (V : Set (Domain d))] fun x =>
          θ x * ∑ k, (chartCoefficient Φ j k x : 𝕜) * u.val (coordinateIndex k) (Φ x) +
            partialFunction [j] θ x * u.val (zeroIndex d 1) (Φ x) := by
      filter_upwards [hf u, hd u j] with x hx hd
      rw [hx, hd]
    have hloc' := ((ae_eq_restrict_iff_indicator_ae_eq V.isOpen.measurableSet).mp hloc).filter_mono
      (ae_mono (Measure.restrict_le_self (s := (Ω : Set (Domain d)))))
    have hm := localizedZeroExtension_coordinate_coe hVΩ K hKclosed hKV θ θ.contDiff C hC0 hC hD hθK
      (Q (R u)) j
    change (M (Q (R u))).val (coordinateIndex j) =ᵐ[volume.restrict (Ω : Set (Domain d))] _
    filter_upwards [hm.trans hloc', ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
    rw [hx]
    by_cases hxV : x ∈ V
    · exact indicator_of_mem hxV _
    · rw [indicator_of_notMem hxV]
      have hxθ : x ∉ tsupport θ := fun hh => hxV ⟨hθ hh, (hside x (hθ hh)).mp hxΩ⟩
      have hz := image_eq_zero_of_notMem_tsupport hxθ
      have hdz : partialFunction [j] θ x = 0 := by
        change fderiv ℝ θ x (coordinateVector j) = 0
        rw [fderiv_of_notMem_tsupport ℝ hxθ]
        rfl
      simp only [hz, hdz, zero_mul, add_zero]

end ExpandedFA.PartIV.SecondTrace


noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Trace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.Sobolev.C1Extension.Transport
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound
open ExpandedFA.PartIV.SharpTrace ExpandedFA.PartIV.SecondTraceFlat
open ExpandedFA.PartIV.SecondTraceTransport
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω Λ : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_compact_c1_chart_pullback (hp : p ≠ ∞)
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
    (J : ℝ) (hJ1 : 1 ≤ J) (hJ : ∀ x ∈ Φ.target, |(fderiv ℝ Φ.symm x).det| ≤ J)
    (hTarget : Bornology.IsBounded Φ.target)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ Φ x ∈ Λ)
    (a : Domain d → 𝕜) (ha : ContDiff ℝ 1 a) (hcompact : HasCompactSupport a)
    (hsource : tsupport a ⊆ Φ.source) :
    ∃ F : SpaceValue 𝕜 d Λ 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p,
      ∀ (u : SpaceValue 𝕜 d Λ 1 p) (f : Domain d → 𝕜),
        u.val (zeroIndex d 1) =ᵐ[volume.restrict (Λ : Set (Domain d))] f →
        (F u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
          fun x => a x * f (Φ x) := by
  obtain ⟨θ, hθ, hθone⟩ := exists_compact_ambient_cutoff (𝕜 := 𝕜)
    (tsupport a) hcompact ⟨Φ.source, Φ.open_source⟩ hsource
  obtain ⟨G, hG⟩ := exists_localized_chart_pullback (Ω := Ω) (p := p)
    Λ Φ hΦ hInv B hB0 hB J hJ1 hJ hTarget hside θ hθ
  obtain ⟨A, hA⟩ := ha.continuous.bounded_above_of_compact_support hcompact
  obtain ⟨D, hD⟩ := (ha.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hcompact.fderiv ℝ)
  let C := max A D
  have hC (x) : ‖a x‖ ≤ C := (hA x).trans (le_max_left _ _)
  have hDC (j x) : ‖fderiv ℝ a x (coordinateVector j)‖ ≤ C := by
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    simpa only [coordinateVector, Pi.norm_single, norm_one, mul_one] using
      (hD x).trans (le_max_right A D)
  let M := c1Multiply (Ω := Ω) (p := p) a ha C hC hDC hp
  refine ⟨M.comp G, ?_⟩
  intro u f hu
  change (c1Multiply a ha C hC hDC hp (G u)).val (zeroIndex d 1) =ᵐ[_] _
  filter_upwards [c1Multiply_coe a ha C hC hDC hp (G u), hG u f hu] with x hx hGx
  rw [hx, hGx]
  by_cases hxa : x ∈ tsupport a
  · rw [hθone x hxa, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hxa, zero_mul, zero_mul]

lemma orderOnePart_coordinate_eq_derivativePart_zero (u : SpaceValue 𝕜 d Ω 2 p) (j : Fin d) :
    (orderOnePart u).val (coordinateIndex j) = (derivativePart j u).val (zeroIndex d 1) := by
  simp only [orderOnePart_apply, derivativePart_apply, derivativePartIndex_zero]
  have hi : orderOneToTwo (coordinateIndex j) = normalIndex j := by
    apply Subtype.ext
    funext k
    apply Fin.ext
    simp [normalIndex, orderOneToTwo, coordinateIndex, boundedIndex, natIndex, Pi.single_apply, apply_ite]
  rw [hi]

set_option maxHeartbeats 1000000 in
/-- Every actual W² patch with the localized pullback representative has the
expected first derivative traces, including derivatives of its cutoff. -/
theorem domain_chart_pullback_two_derivative_trace
    {n : ℕ} {Ω : Opens (Domain (n+1))} (hp : p ≠ ∞)
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (Φ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1))) (i : Fin (n+1))
    (hΦ2 : ContDiffOn ℝ 2 Φ Φ.source) (hInv2 : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
    (hBinv : ∀ x ∈ Φ.target, ‖fderiv ℝ Φ.symm x‖ ≤ B)
    (hSource : Bornology.IsBounded Φ.source) (hTarget : Bornology.IsBounded Φ.target)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    {K : ℝ≥0} (hLip : LipschitzOnWith K Φ Φ.source)
    (θ : Tests 𝕜 (⊤ : Opens (Domain (n+1)))) (hθ : tsupport θ ⊆ Φ.source)
    (P : SpaceValue 𝕜 (n+1) (upper i) 2 p →L[𝕜] SpaceValue 𝕜 (n+1) Ω 2 p)
    (hP : ∀ u, (P u).val (zeroIndex (n+1) 2) =ᵐ[volume.restrict (Ω : Set (Domain (n+1)))]
      fun x => θ x * u.val (zeroIndex (n+1) 2) (Φ x))
    (T : SpaceValue 𝕜 (n+1) Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (S : SpaceValue 𝕜 (n+1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))) (hS : IsCoordinateTrace i S)
    (u : SpaceValue 𝕜 (n+1) (upper i) 2 p) (j : Fin (n+1)) :
    (fun z => T (derivativePart j (P u)) (boundaryParam Φ i z)) =ᵐ[
      volume.restrict (boundaryParameters Φ i)] fun z =>
        partialFunction [j] θ (boundaryParam Φ i z) * reindexedTrace i S (orderOnePart u) z +
        ∑ k, (θ (boundaryParam Φ i z) * (chartCoefficient Φ j k (boundaryParam Φ i z) : 𝕜)) *
          reindexedTrace i S (derivativePart k u) z := by
  classical
  have hΦ : ContDiffOn ℝ 1 Φ Φ.source := hΦ2.of_le (by norm_num)
  have hInv : ContDiffOn ℝ 1 Φ.symm Φ.target := hInv2.of_le (by norm_num)
  obtain ⟨J, hJ1, hJbound⟩ := exists_det_bound_of_norm_bound (E := Domain (n+1)) B
  have hJ : ∀ x ∈ Φ.target, |(fderiv ℝ Φ.symm x).det| ≤ J := fun x hx => hJbound _ (hBinv x hx)
  have hside' : ∀ x ∈ Φ.source, x ∈ Ω ↔ Φ x ∈ upper i := hside
  obtain ⟨F, hF, hFd⟩ := exists_localized_chart_pullback_with_derivatives (p := p) (Ω := Ω) (Λ := upper i)
    Φ hΦ hInv B hB0 hB J hJ1 hJ hTarget hside' θ hθ
  have hfirst : orderOnePart (P u) = F (orderOnePart u) := by
    apply sobolev_underlying_injective 𝕜 (n+1) Ω 1 p
    apply Lp.ext
    exact (hP u).trans (hF (orderOnePart u) (u.val (zeroIndex (n+1) 2)) EventuallyEq.rfl).symm
  let a₀ := partialFunction [j] θ
  let a : Fin (n+1) → Domain (n+1) → 𝕜 := fun k x => θ x * (chartCoefficient Φ j k x : 𝕜)
  have ha₀ := Analytic.compact_cutoff_derivative_coefficient Φ θ hθ j
  have ha (k : Fin (n+1)) := Analytic.compact_chart_derivative_coefficient Φ hΦ2 θ hθ j k
  obtain ⟨F₀, hF₀⟩ := exists_compact_c1_chart_pullback (Ω := Ω) (Λ := upper i) hp
    Φ hΦ hInv B hB0 hB J hJ1 hJ hTarget hside' a₀ ha₀.1 ha₀.2.1 ha₀.2.2
  choose Fₖ hFₖ using fun k : Fin (n+1) => exists_compact_c1_chart_pullback (Ω := Ω) (Λ := upper i) hp
    Φ hΦ hInv B hB0 hB J hJ1 hJ hTarget hside' (a k) (ha k).1 (ha k).2.1 (ha k).2.2
  have hder : derivativePart j (P u) = F₀ (orderOnePart u) + ∑ k, Fₖ k (derivativePart k u) := by
    apply sobolev_underlying_injective 𝕜 (n+1) Ω 1 p
    have hlp : (F₀ (orderOnePart u) + ∑ k, Fₖ k (derivativePart k u)).val (zeroIndex (n+1) 1) =
        (F₀ (orderOnePart u)).val (zeroIndex (n+1) 1) +
          ∑ k, (Fₖ k (derivativePart k u)).val (zeroIndex (n+1) 1) := by
      exact map_add (evalOne (zeroIndex (n+1) 1)) _ _ |>.trans
        (congrArg (_ + ·) (map_sum (evalOne (zeroIndex (n+1) 1)) _ _))
    change (derivativePart j (P u)).val (zeroIndex (n+1) 1) =
      (F₀ (orderOnePart u) + ∑ k, Fₖ k (derivativePart k u)).val (zeroIndex (n+1) 1)
    rw [hlp]
    apply Lp.ext
    have hfd := hFd (orderOnePart u) j
    rw [← hfirst, orderOnePart_coordinate_eq_derivativePart_zero] at hfd
    filter_upwards [hfd, hF₀ (orderOnePart u) ((orderOnePart u).val (zeroIndex (n+1) 1)) EventuallyEq.rfl,
      ae_all_iff.mpr (fun k => hFₖ k (derivativePart k u)
        ((derivativePart k u).val (zeroIndex (n+1) 1)) EventuallyEq.rfl),
      Lp.coeFn_add ((F₀ (orderOnePart u)).val (zeroIndex (n+1) 1))
        (∑ k, (Fₖ k (derivativePart k u)).val (zeroIndex (n+1) 1)),
      Lp.coeFn_fun_finsetSum Finset.univ (fun k => (Fₖ k (derivativePart k u)).val (zeroIndex (n+1) 1))]
      with x hx h₀ hₖ hadd hsum
    rw [hadd]
    simp only [Pi.add_apply]
    rw [hsum, hx, h₀]
    simp only [a₀, a, Finset.mul_sum]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hₖ k, orderOnePart_coordinate_eq_derivativePart_zero]
    ring
  have raw (b : Domain (n+1) → 𝕜) (hb : ContDiff ℝ 1 b) (hbc : HasCompactSupport b)
      (hbs : tsupport b ⊆ Φ.source)
      (G : SpaceValue 𝕜 (n+1) (upper i) 1 p →L[𝕜] SpaceValue 𝕜 (n+1) Ω 1 p)
      (hG : ∀ v f, v.val (zeroIndex (n+1) 1) =ᵐ[volume.restrict (upper i : Set (Domain (n+1)))] f →
        (G v).val (zeroIndex (n+1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (n+1)))]
          fun x => b x * f (Φ x)) (v : SpaceValue 𝕜 (n+1) (upper i) 1 p) :
      (fun z => T (G v) (boundaryParam Φ i z)) =ᵐ[volume.restrict (boundaryParameters Φ i)]
        fun z => b (boundaryParam Φ i z) * reindexedTrace i S v z := by
    obtain ⟨C, hC⟩ := hb.continuous.bounded_above_of_compact_support hbc
    have hC0 := (norm_nonneg (b 0)).trans (hC 0)
    exact localized_chart_pullback_trace_formula_c1 Ω hp hdense Φ i hΦ hInv B hB0 hB hBinv
      hSource hside hLip b hb hbc C hC0 hC hbs G hG T hT S hS v
  have hr₀ := raw a₀ ha₀.1 ha₀.2.1 ha₀.2.2 F₀ hF₀ (orderOnePart u)
  have hrₖ (k) := raw (a k) (ha k).1 (ha k).2.1 (ha k).2.2 (Fₖ k) (hFₖ k) (derivativePart k u)
  rw [hder, map_add, map_sum]
  have hadd := Lp.coeFn_add (T (F₀ (orderOnePart u))) (∑ k, T (Fₖ k (derivativePart k u)))
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ (fun k => T (Fₖ k (derivativePart k u)))
  obtain ⟨D, hD, hmap⟩ := boundaryParam_map_le_surfaceMeasure Ω Φ i hside hLip
  have hac : (volume.restrict (boundaryParameters Φ i)).map (boundaryParam Φ i) ≪ surfaceMeasure Ω :=
    Measure.absolutelyContinuous_of_le_smul
      (hmap.trans (smul_le_smul_left D Measure.restrict_le_self))
  have hadd' := ae_of_ae_map (boundaryParam_aemeasurable Φ i) (hac.ae_eq hadd)
  have hsum' := ae_of_ae_map (boundaryParam_aemeasurable Φ i) (hac.ae_eq hsum)
  filter_upwards [hr₀, ae_all_iff.mpr hrₖ, hadd', hsum'] with z hz₀ hzₖ hzadd hzsum
  rw [hzadd]
  simp only [Pi.add_apply]
  rw [hzsum, hz₀]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => hzₖ k)


lemma trace_supported_in_open_of_value_supported
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (K : Set (Domain d)) (hK : IsCompact K) (U : Opens (Domain d)) (hKU : K ⊆ U)
    (v : SpaceValue 𝕜 d Ω 1 p)
    (hv : ∀ᵐ x ∂volume.restrict (Ω : Set (Domain d)), x ∉ K → v.val (zeroIndex d 1) x = 0) :
    ∀ᵐ x ∂surfaceMeasure Ω, x ∉ U → T v x = 0 := by
  obtain ⟨η, hη, hηone⟩ := exists_compact_ambient_cutoff (𝕜 := 𝕜) K hK U hKU
  have hfix := trace_fixed_by_cutoff hdense T hT η v (by
    filter_upwards [hv] with x hx
    by_cases hxK : x ∈ K
    · rw [hηone x hxK, one_mul]
    · rw [hx hxK, mul_zero])
  filter_upwards [hfix] with x hx hxU
  have hxη : x ∉ tsupport η := fun hh => hxU (hη hh)
  simpa only [image_eq_zero_of_notMem_tsupport hxη, zero_mul] using hx

theorem domain_chart_pullback_two_component_trace_supported
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (U : Opens (Domain d)) (θ : Tests 𝕜 (⊤ : Opens (Domain d))) (hθ : tsupport θ ⊆ U)
    (v : SpaceValue 𝕜 d Ω 2 p)
    (hv : ∀ᵐ x ∂volume.restrict (Ω : Set (Domain d)), x ∉ tsupport θ → v.val (zeroIndex d 2) x = 0) :
    (∀ᵐ x ∂surfaceMeasure Ω, x ∉ U → T (orderOnePart v) x = 0) ∧
    ∀ j, ∀ᵐ x ∂surfaceMeasure Ω, x ∉ U → T (derivativePart j v) x = 0 := by
  have hall := sobolev_components_supported_of_value_supported v (tsupport θ) (isClosed_tsupport θ) hv
  constructor
  · exact trace_supported_in_open_of_value_supported hdense T hT (tsupport θ) θ.hasCompactSupport U hθ
      (orderOnePart v) (hall (zeroIndex d 2))
  · intro j
    exact trace_supported_in_open_of_value_supported hdense T hT (tsupport θ) θ.hasCompactSupport U hθ
      (derivativePart j v) (by
        simpa only [derivativePart_apply, derivativePartIndex_zero] using hall (normalIndex j))

/-- Value trace transport for an arbitrary genuine W² chart patch. -/
theorem domain_chart_pullback_two_value_trace
    {n : ℕ} {Ω : Opens (Domain (n+1))} (hp : p ≠ ∞)
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (Φ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1))) (i : Fin (n+1))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
    (hBinv : ∀ x ∈ Φ.target, ‖fderiv ℝ Φ.symm x‖ ≤ B)
    (hSource : Bornology.IsBounded Φ.source) (hTarget : Bornology.IsBounded Φ.target)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    {K : ℝ≥0} (hLip : LipschitzOnWith K Φ Φ.source)
    (θ : Tests 𝕜 (⊤ : Opens (Domain (n+1)))) (hθ : tsupport θ ⊆ Φ.source)
    (P : SpaceValue 𝕜 (n+1) (upper i) 2 p →L[𝕜] SpaceValue 𝕜 (n+1) Ω 2 p)
    (hP : ∀ u, (P u).val (zeroIndex (n+1) 2) =ᵐ[volume.restrict (Ω : Set (Domain (n+1)))]
      fun x => θ x * u.val (zeroIndex (n+1) 2) (Φ x))
    (T : SpaceValue 𝕜 (n+1) Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (S : SpaceValue 𝕜 (n+1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))) (hS : IsCoordinateTrace i S)
    (u : SpaceValue 𝕜 (n+1) (upper i) 2 p) :
    (fun z => T (orderOnePart (P u)) (boundaryParam Φ i z)) =ᵐ[
      volume.restrict (boundaryParameters Φ i)] fun z =>
        θ (boundaryParam Φ i z) * reindexedTrace i S (orderOnePart u) z := by
  obtain ⟨J, hJ1, hJbound⟩ := exists_det_bound_of_norm_bound (E := Domain (n+1)) B
  have hJ : ∀ x ∈ Φ.target, |(fderiv ℝ Φ.symm x).det| ≤ J := fun x hx => hJbound _ (hBinv x hx)
  have hside' : ∀ x ∈ Φ.source, x ∈ Ω ↔ Φ x ∈ upper i := hside
  obtain ⟨F, hF⟩ := exists_localized_chart_pullback (Ω := Ω) (p := p)
    (upper i) Φ hΦ hInv B hB0 hB J hJ1 hJ hTarget hside' θ hθ
  have hfirst : orderOnePart (P u) = F (orderOnePart u) := by
    apply sobolev_underlying_injective 𝕜 (n+1) Ω 1 p
    apply Lp.ext
    exact (hP u).trans (hF (orderOnePart u) (u.val (zeroIndex (n+1) 2)) EventuallyEq.rfl).symm
  rw [hfirst]
  exact localized_chart_pullback_trace_formula Ω hp hdense Φ i hΦ hInv B hB0 hB hBinv
    hSource hside hLip θ hθ F hF T hT S hS (orderOnePart u)

end ExpandedFA.PartIV.SecondTrace


noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal
namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.Sobolev.C1Extension
open ExpandedFA.PartIV.SecondTraceFlat
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- Coordinate value and derivative trace formulas, with compactly supported
independent corrected data, recover the prescribed physical surface jets. -/
lemma hasDomainJets_of_compact_chart_formulas
    {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {Ω : Opens (Domain (n+1))}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (ν : Domain (n+1) → Domain (n+1)) (hν : IsOutwardNormal Ω ν)
    (T : SpaceValue 𝕜 (n+1) Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
    (V : SpaceValue 𝕜 (n+1) Ω 2 p) (G H : BoundaryLp 𝕜 Ω p)
    (Φ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1))) (i : Fin (n+1))
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    {L M : ℝ≥0} (hLip : LipschitzOnWith L Φ Φ.source)
    (hInvLip : LipschitzOnWith M Φ.symm Φ.target)
    (K : Set (Domain n)) (η : Domain (n+1) → 𝕜)
    (hη : ∀ z ∈ K, η (boundaryParam Φ i z) = 1)
    (hDη : ∀ j : Fin (n+1), ∀ z ∈ K, partialFunction [j] η (boundaryParam Φ i z) = 0)
    (g h : Lp 𝕜 p (volume : Measure (Domain n)))
    (q : Fin (n+1) → Lp 𝕜 p (volume : Measure (Domain n)))
    (hg : ∀ᵐ z ∂volume, z ∉ K → g z = 0)
    (hh : ∀ᵐ z ∂volume, z ∉ K → h z = 0)
    (hq : ∀ j, ∀ᵐ z ∂volume, z ∉ K → q j z = 0)
    (hflat : ∀ᵐ z ∂volume,
      (chartNormalCoefficient Φ (chartOutwardNormal Φ i) i
        (Φ.symm (boundaryEmbedding i z)) : 𝕜) * q i z +
      ∑ j : Fin n, (chartTangentialCoefficient Φ (chartOutwardNormal Φ i) i j
        (Φ.symm (boundaryEmbedding i z)) : 𝕜) * q (i.succAbove j) z = h z)
    (hgG : g =ᵐ[volume.restrict (boundaryParameters Φ i)]
      fun z => G (boundaryParam Φ i z))
    (hhH : h =ᵐ[volume.restrict (boundaryParameters Φ i)]
      fun z => H (boundaryParam Φ i z))
    (hv : (fun z => T (orderOnePart V) (boundaryParam Φ i z)) =ᵐ[
      volume.restrict (boundaryParameters Φ i)] fun z => η (boundaryParam Φ i z) * g z)
    (hd : ∀ j, (fun z => T (derivativePart j V) (boundaryParam Φ i z)) =ᵐ[
      volume.restrict (boundaryParameters Φ i)] fun z =>
      η (boundaryParam Φ i z) * ∑ k : Fin (n+1),
        (fderiv ℝ Φ (boundaryParam Φ i z) (coordinateVector j) k : 𝕜) * q k z +
      partialFunction [j] η (boundaryParam Φ i z) * g z)
    (hvout : ∀ᵐ x ∂surfaceMeasure Ω, x ∉ Φ.source → T (orderOnePart V) x = 0)
    (hdout : ∀ j, ∀ᵐ x ∂surfaceMeasure Ω, x ∉ Φ.source → T (derivativePart j V) x = 0)
    (hGout : ∀ᵐ x ∂surfaceMeasure Ω, x ∉ Φ.source → G x = 0)
    (hHout : ∀ᵐ x ∂surfaceMeasure Ω, x ∉ Φ.source → H x = 0) :
    HasDomainJets ν T V G H := by
  have hμ : volume.restrict (boundaryParameters Φ i) ≤ (volume : Measure (Domain n)) :=
    Measure.restrict_le_self
  apply hasDomainJets_of_supported_chart_pullback_equalities ν hν T V G H Φ i hside
    hLip hInvLip ?_ ?_ hvout hdout hGout hHout
  · filter_upwards [hv, hgG, hg.filter_mono (ae_mono hμ)] with z hz hzg hg0
    rw [hz]
    by_cases hzK : z ∈ K
    · rw [hη z hzK, one_mul, hzg]
    · rw [hg0 hzK, mul_zero]
      exact (hg0 hzK).symm.trans hzg
  · filter_upwards [ae_all_iff.mpr hd, hhH,
      hg.filter_mono (ae_mono hμ), hh.filter_mono (ae_mono hμ),
      (ae_all_iff.mpr hq).filter_mono (ae_mono hμ),
      hflat.filter_mono (ae_mono hμ),
      ae_restrict_mem (boundaryParameters_isOpen Φ i).measurableSet]
      with z hdz hhz hgz hhz0 hqz hfz hz
    simp_rw [hdz]
    rw [normal_chart_jet_algebra]
    by_cases hzK : z ∈ K
    · have hxs : boundaryParam Φ i z ∈ Φ.source := Φ.map_target hz
      have hxb : boundaryParam Φ i z ∈ frontier (Ω : Set (Domain (n+1))) := by
        apply (chart_boundary_iff Ω Φ i hside _ hxs).mpr
        change Φ (Φ.symm (i.insertNth 0 z)) i = 0
        rw [Φ.right_inv hz]
        exact Fin.insertNth_apply_same _ _ _
      rw [chartNormalCoefficient_eq_outward ν hν Φ i i hside hΦ hInv _ hxb hxs]
      simp_rw [chartTangentialCoefficient_eq_outward ν hν Φ i _ hside hΦ hInv _ hxb hxs]
      rw [hη z hzK]
      simp only [fun j => hDη j z hzK, mul_zero, Finset.sum_const_zero, zero_mul,
        add_zero, one_mul]
      exact hfz.trans hhz
    · simp only [fun j => hqz j hzK, hgz hzK, mul_zero, Finset.sum_const_zero, add_zero]
      exact (hhz0 hzK).symm.trans hhz

end ExpandedFA.PartIV.SecondTrace


noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.Sobolev.C1Extension ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.Sobolev.C1Extension.Transport
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound
open ExpandedFA.PartIV.SharpTrace ExpandedFA.PartIV.SecondTraceFlat
open ExpandedFA.PartIV.SecondTraceTransport
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

set_option maxHeartbeats 1000000 in
/-- Independent localized data are lifted in finitely many actual C² charts,
and their original surface classes reconstruct the simultaneous domain jets. -/
theorem onto_trace : Specs.ExpandedFA.PartIV.SecondTraceLift.OntoTrace := by
  intro 𝕜 _ d Ω hb hc p _ hp1 hp B ν hν T hT g h
  classical
  cases d with
  | zero => exact domain_jets_onto_zero_dimension Ω ν T g.val h.val
  | succ n =>
    have hdense := C1Extension.smooth_density 𝕜 (n+1) Ω hc.isC1Domain
      (hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure) p hp
    have hlocal (j : Fin B.chartCount) :
        ∃ V : SpaceValue 𝕜 (n+1) Ω 2 p,
          HasDomainJets ν T V (B.boundaryPiece j g.val) (B.boundaryPiece j h.val) := by
      obtain ⟨η, hηsource, _, hηone, hηD⟩ := exists_compact_cutoff_with_zero_gradient (𝕜 := 𝕜)
        (tsupport (B.test j)) (B.ambient j).source (B.test j).hasCompactSupport
        (B.ambient j).open_source (B.test_subordinate j)
      obtain ⟨Ψ, C, J, L, M, hfun, hinv, hηΨ, hΨΦ, hΨtarget, hΨ, hΨinv,
        hC0, hC, hCinv, hDD, hJ1, hJ, hSource, hTarget, hLip, hInvLip, _⟩ :=
        exists_c2_subchart_full_bounds (B.ambient j) (B.regular j).1 (B.regular j).2
          (tsupport η) η.hasCompactSupport hηsource
      have hcut : tsupport (B.test j) ⊆ Ψ.source := by
        intro x hx
        apply hηΨ
        apply subset_tsupport η
        change η x ≠ 0
        rw [hηone x hx]
        exact one_ne_zero
      have hside : ∀ x ∈ Ψ.source, x ∈ Ω ↔ 0 < Ψ x (B.normal j) := by
        intro x hx
        rw [hfun]
        exact B.side j x (hΨΦ hx)
      let K := B.coordinateSupport j
      have hK : IsCompact K := B.coordinateSupport_compact hb j
      have hKV : K ⊆ boundaryChartDomain Ψ (B.normal j) :=
        B.coordinateSupport_subset_subchart j Ψ hfun hcut
      let g₀ := B.higherPiece (2 - 1 / p.toReal) g j
      let h₀ := B.fractionalPiece (1 - 1 / p.toReal) h j
      have hg₀ : ∀ᵐ z ∂volume, z ∉ K → wholeLp (g₀.val.val (zeroIndex n 1)) z = 0 :=
        B.higherPiece_supported (2 - 1 / p.toReal) g j
      have hh₀ : ∀ᵐ z ∂volume, z ∉ K → h₀.val z = 0 :=
        B.fractionalPiece_supported (1 - 1 / p.toReal) h j
      obtain ⟨S, hS, _⟩ := coordinate_upper_trace_exists (𝕜 := 𝕜) (i := B.normal j) hp
      obtain ⟨u, huvalue, hutangent, hunormal, husupport⟩ := compact_chart_flat_jet_lift Ψ (B.normal j)
        hΨ hΨinv K hK hKV p hp1 hp S hS g₀ h₀ hg₀ hh₀
      obtain ⟨P, hP⟩ := exists_domain_chart_pullback_two Ω p hp1 hp Ψ (B.normal j)
        hΨ hΨinv hside η hηΨ
      have hP' (v : SpaceValue 𝕜 (n+1) (upper (B.normal j)) 2 p) :=
        hP v (v.val (zeroIndex (n+1) 2)) EventuallyEq.rfl
      let V := P u
      have hVs : ∀ᵐ x ∂volume.restrict (Ω : Set (Domain (n+1))), x ∉ tsupport η →
          V.val (zeroIndex (n+1) 2) x = 0 := by
        filter_upwards [hP' u] with x hx hxη
        rw [hx, image_eq_zero_of_notMem_tsupport hxη, zero_mul]
      obtain ⟨hvout, hdout⟩ := domain_chart_pullback_two_component_trace_supported
        hdense T hT ⟨Ψ.source, Ψ.open_source⟩ η hηΨ V hVs
      refine ⟨V, ?_⟩
      apply hasDomainJets_of_compact_chart_formulas ν hν T V
        (B.boundaryPiece j g.val) (B.boundaryPiece j h.val)
        Ψ (B.normal j) hside hΨ hΨinv hLip hInvLip K η
        (B.cutoff_one_on_coordinateSupport j Ψ hinv η hηone)
        (fun k z hz => hηD k _ (B.coordinateSupport_param_in_test_support j Ψ hinv hz))
        (wholeLp (g₀.val.val (zeroIndex n 1))) h₀.val
        (fun k => reindexedTrace (B.normal j) S (derivativePart k u))
        hg₀ hh₀ husupport hunormal
        (B.higherPiece_eq_boundaryPiece_subchart (2 - 1 / p.toReal) g j Ψ hfun hinv hΨΦ)
        (B.fractionalPiece_eq_boundaryPiece_subchart (1 - 1 / p.toReal) h j Ψ hfun hinv hΨΦ)
        ?_ ?_ hvout hdout
        (B.boundaryPiece_supported_subchart j Ψ hcut g.val)
        (B.boundaryPiece_supported_subchart j Ψ hcut h.val)
      · have hv := domain_chart_pullback_two_value_trace hp hdense Ψ (B.normal j)
          (hΨ.of_le (by norm_num)) (hΨinv.of_le (by norm_num)) C hC0 hC hCinv
          hSource hTarget hside hLip η hηΨ P hP' T hT S hS u
        simpa only [huvalue] using hv
      · intro k
        have hd := domain_chart_pullback_two_derivative_trace hp hdense Ψ (B.normal j)
          hΨ hΨinv C hC0 hC hCinv hSource hTarget hside hLip η hηΨ P hP' T hT S hS u k
        filter_upwards [hd] with z hz
        rw [hz, huvalue]
        simp only [Finset.mul_sum, chartCoefficient, mul_assoc]
        exact add_comm _ _
    choose V hV using hlocal
    exact ⟨∑ j, V j, hasDomainJets_sum_of_boundaryPieces B ν T g.val h.val V hV⟩

end ExpandedFA.PartIV.SecondTrace
