import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SecondTraceBound
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SecondTraceFlat
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SharpTrace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SecondTraceGeometry
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SecondTraceTransport
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! Work on boundedness of the two domain jets. These lemmas construct the
actual Lp jets, establish their uniqueness and boundedness, and apply the
sharp first-order theorem to the genuine first weak derivatives. Tangential trace differentiation and geometric normal coefficient estimates
then give the full higher fractional bound on every bounded C² domain. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open ExpandedFA.PartIV.SecondTrace
open Specs.ExpandedFA.PartIV.SecondTraceBound

namespace ExpandedFA.PartIV.SecondTraceBound
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.Sobolev.C1Extension
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTrace
open SecondTraceFlat ExpandedFA.Sobolev.HalfSpace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma isC1Domain_of_isC2Domain (hΩ : IsC2Domain Ω) : IsC1Domain Ω := by
  intro x hx
  obtain ⟨i, Φ, hxΦ, hz, hΦ, hInv, hside⟩ := hΩ x hx
  exact ⟨i, Φ, hxΦ, hz, hΦ.of_le (by norm_num), hInv.of_le (by norm_num), hside⟩

/-- The original graph representatives determine both jets uniquely. -/
lemma hasDomainJets_iff (ν : Domain d → Domain d)
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
    (u : SpaceValue 𝕜 d Ω 2 p) (g h : BoundaryLp 𝕜 Ω p) :
    HasDomainJets ν T u g h ↔
      T (orderOnePart u) = g ∧
      h =ᵐ[surfaceMeasure Ω] fun x => ∑ j : Fin d, ν x j • T (derivativePart j u) x := by
  constructor
  · rintro ⟨v, w, hv, hw, hg, hh⟩
    have hv' : v = orderOnePart u := by
      apply sobolev_underlying_injective 𝕜 d Ω 1 p
      simpa only [orderOnePart_apply, orderOneToTwo_zero] using hv
    have hw' : ∀ j, w j = derivativePart j u := by
      intro j
      apply sobolev_underlying_injective 𝕜 d Ω 1 p
      simpa only [derivativePart_apply, derivativePartIndex_zero] using hw j
    simpa only [hv', hw'] using And.intro hg hh
  · rintro ⟨hg, hh⟩
    exact ⟨orderOnePart u, fun j => derivativePart j u,
      by simp, by intro j; simp, hg, hh⟩

lemma hasDomainJets_unique (ν : Domain d → Domain d)
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
    (u : SpaceValue 𝕜 d Ω 2 p) {g h g' h' : BoundaryLp 𝕜 Ω p}
    (ha : HasDomainJets ν T u g h) (hb : HasDomainJets ν T u g' h') :
    g = g' ∧ h = h' := by
  rw [hasDomainJets_iff] at ha hb
  exact ⟨ha.1.symm.trans hb.1, Lp.ext (ha.2.trans hb.2.symm)⟩

/-- The derivative graph used for the normal jet has exactly the corresponding
coordinate derivative of the value graph as its underlying Lp class. -/
lemma derivativePart_zero_eq_coordinate (j : Fin d) (u : SpaceValue 𝕜 d Ω 2 p) :
    (derivativePart j u).val (zeroIndex d 1) =
      (orderOnePart u).val (coordinateIndex j) := by
  simp only [derivativePart_apply, derivativePartIndex_zero, orderOnePart_apply]
  have hi : normalIndex j = orderOneToTwo (coordinateIndex j) := by
    apply Subtype.ext
    funext k
    apply Fin.ext
    simp [natIndex, normalIndex, coordinateIndex, orderOneToTwo, boundedIndex,
      Pi.single_apply, apply_ite]
  rw [hi]

lemma derivativePart_zero_ae_fderiv (u : SpaceValue 𝕜 d Ω 2 p)
    (f : Domain d → 𝕜) (hf : ContDiff ℝ 1 f)
    (hu : u.val (zeroIndex d 2) =ᵐ[volume.restrict (Ω : Set (Domain d))] f)
    (j : Fin d) :
    (derivativePart j u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun x => fderiv ℝ f x (coordinateVector j) := by
  rw [derivativePart_zero_eq_coordinate]
  exact Classical.c1_representative_derivative (orderOnePart u) f hf.contDiffOn
    (by simpa only [orderOnePart_apply, orderOneToTwo_zero] using hu) j

section NormalLp
variable (ν : Domain d → Domain d) (hν : GeometricNormal Ω ν)

/-- Only the measurable and a.e. unit-bound parts of the geometric normal
are needed to form its product with an arbitrary surface Lp class. -/
def normalComponent (j : Fin d) (g : BoundaryLp 𝕜 Ω p) : BoundaryLp 𝕜 Ω p :=
  ((Lp.memLp g).of_le_mul (f := fun x => ν x j • g x) (c := 1)
    ((hν.1 j).aestronglyMeasurable.smul (Lp.aestronglyMeasurable g)) (by
      filter_upwards [hν.2.1 j] with x hx
      simpa only [norm_smul, Real.norm_eq_abs, one_mul] using
        mul_le_mul_of_nonneg_right hx (norm_nonneg (g x)))).toLp _

lemma normalComponent_coe (j : Fin d) (g : BoundaryLp 𝕜 Ω p) :
    normalComponent ν hν j g =ᵐ[surfaceMeasure Ω] fun x => ν x j • g x :=
  MemLp.coeFn_toLp _

lemma normalComponent_norm_le (j : Fin d) (g : BoundaryLp 𝕜 Ω p) :
    ‖normalComponent ν hν j g‖ ≤ ‖g‖ := by
  have hb : ‖normalComponent ν hν j g‖ ≤ 1 * ‖g‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [normalComponent_coe ν hν j g, hν.2.1 j] with x hx hbound
    rw [hx, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
  simpa using hb

/-- Scalar linearity is over the original real or complex scalar field,
although the geometric coefficients are real. -/
def normalComponentCLM (j : Fin d) : BoundaryLp 𝕜 Ω p →L[𝕜] BoundaryLp 𝕜 Ω p :=
  LinearMap.mkContinuous
    { toFun := normalComponent ν hν j
      map_add' := by
        intro g h
        apply Lp.ext
        filter_upwards [normalComponent_coe ν hν j (g + h),
          normalComponent_coe ν hν j g, normalComponent_coe ν hν j h,
          Lp.coeFn_add g h,
          Lp.coeFn_add (normalComponent ν hν j g) (normalComponent ν hν j h)]
          with x h₁ h₂ h₃ h₄ h₅
        rw [h₁, h₅, h₄]
        simp only [Pi.add_apply, h₂, h₃, smul_add]
      map_smul' := by
        intro c g
        apply Lp.ext
        filter_upwards [normalComponent_coe ν hν j (c • g),
          normalComponent_coe ν hν j g, Lp.coeFn_smul c g,
          Lp.coeFn_smul c (normalComponent ν hν j g)] with x h₁ h₂ h₃ h₄
        change normalComponent ν hν j (c • g) x =
          (c • normalComponent ν hν j g : BoundaryLp 𝕜 Ω p) x
        rw [h₁, h₄, h₃]
        simp only [Pi.smul_apply, h₂]
        exact smul_comm _ _ _ }
    1 (fun g => by simpa using normalComponent_norm_le ν hν j g)

variable (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)

/-- The normal jet on W2p, formed from the genuine coordinate weak
derivatives. No interior extension of ν is chosen or assumed. -/
def normalTraceCLM : SpaceValue 𝕜 d Ω 2 p →L[𝕜] BoundaryLp 𝕜 Ω p :=
  ∑ j : Fin d, (normalComponentCLM ν hν j).comp
    (T.comp (derivativePartCLM 𝕜 d Ω p j))

lemma normalTraceCLM_coe (u : SpaceValue 𝕜 d Ω 2 p) :
    normalTraceCLM ν hν T u =ᵐ[surfaceMeasure Ω]
      fun x => ∑ j : Fin d, ν x j • T (derivativePart j u) x := by
  simp only [normalTraceCLM, _root_.sum_apply, ContinuousLinearMap.comp_apply]
  have hs := Lp.coeFn_fun_finsetSum Finset.univ
    (fun j : Fin d => normalComponent ν hν j (T (derivativePart j u)))
  have hc : ∀ᵐ x ∂surfaceMeasure Ω, ∀ j : Fin d,
      normalComponent ν hν j (T (derivativePart j u)) x =
        ν x j • T (derivativePart j u) x :=
    Filter.eventually_all.mpr (fun j => normalComponent_coe ν hν j _)
  filter_upwards [hs, hc] with x hx hcomp
  change (∑ j : Fin d, normalComponent ν hν j (T (derivativePart j u))) x = _
  rw [hx]
  exact Finset.sum_congr rfl (fun j _ => hcomp j)

lemma canonical_hasDomainJets (u : SpaceValue 𝕜 d Ω 2 p) :
    HasDomainJets ν T u (T (orderOnePart u)) (normalTraceCLM ν hν T u) :=
  (hasDomainJets_iff ν T u _ _).mpr ⟨rfl, normalTraceCLM_coe ν hν T u⟩

lemma hasDomainJets_iff_normalTrace (u : SpaceValue 𝕜 d Ω 2 p)
    (g h : BoundaryLp 𝕜 Ω p) :
    HasDomainJets ν T u g h ↔
      T (orderOnePart u) = g ∧ normalTraceCLM ν hν T u = h := by
  rw [hasDomainJets_iff]
  apply and_congr_right
  intro _
  constructor
  · intro hh
    exact Lp.ext ((normalTraceCLM_coe ν hν T u).trans hh.symm)
  · intro hh
    exact hh ▸ normalTraceCLM_coe ν hν T u

/-- Smooth agreement identifies these Lp jets with the classical boundary
value and outward normal derivative, with the prescribed sign of ν. -/
lemma canonical_jets_smooth (hT : IsTrace T) (u : SpaceValue 𝕜 d Ω 2 p)
    (f : Domain d → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hu : u.val (zeroIndex d 2) =ᵐ[volume.restrict (Ω : Set (Domain d))] f) :
    (T (orderOnePart u) =ᵐ[surfaceMeasure Ω] f) ∧
      normalTraceCLM ν hν T u =ᵐ[surfaceMeasure Ω]
        fun x => ∑ j : Fin d, ν x j • fderiv ℝ f x (coordinateVector j) := by
  refine ⟨hT (orderOnePart u) f hf (by simpa using hu), ?_⟩
  have hj (j : Fin d) : T (derivativePart j u) =ᵐ[surfaceMeasure Ω]
      fun x => fderiv ℝ f x (coordinateVector j) := by
    apply hT
    · exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
    · exact derivativePart_zero_ae_fderiv u f (hf.of_le (by simp)) hu j
  filter_upwards [normalTraceCLM_coe ν hν T u, Filter.eventually_all.mpr hj] with x hx hgrad
  rw [hx]
  exact Finset.sum_congr rfl (fun j _ => congrArg (ν x j • ·) (hgrad j))

include hν in
/-- Both original trace identities pass to Sobolev and boundary Lp limits.
This uses bounded graph projections, without assuming W2p boundary density. -/
lemma hasDomainJets_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (U : ι → SpaceValue 𝕜 d Ω 2 p) (G H : ι → BoundaryLp 𝕜 Ω p)
    (u : SpaceValue 𝕜 d Ω 2 p) (g h : BoundaryLp 𝕜 Ω p)
    (hU : Filter.Tendsto U l (nhds u)) (hG : Filter.Tendsto G l (nhds g))
    (hH : Filter.Tendsto H l (nhds h))
    (hjets : ∀ i, HasDomainJets ν T (U i) (G i) (H i)) :
    HasDomainJets ν T u g h := by
  have hG' : G = fun i => T (orderOnePart (U i)) :=
    funext (fun i => ((hasDomainJets_iff_normalTrace ν hν T _ _ _).mp (hjets i)).1.symm)
  have hH' : H = fun i => normalTraceCLM ν hν T (U i) :=
    funext (fun i => ((hasDomainJets_iff_normalTrace ν hν T _ _ _).mp (hjets i)).2.symm)
  rw [hG'] at hG
  rw [hH'] at hH
  apply (hasDomainJets_iff_normalTrace ν hν T u g h).mpr
  exact ⟨tendsto_nhds_unique
    (((T.comp (orderOnePartCLM 𝕜 d Ω p)).continuous.tendsto u).comp hU) hG,
    tendsto_nhds_unique ((normalTraceCLM ν hν T).continuous.tendsto u |>.comp hU) hH⟩

lemma normalTraceCLM_norm_le (u : SpaceValue 𝕜 d Ω 2 p) :
    ‖normalTraceCLM ν hν T u‖ ≤
      (d : ℝ) * ‖T‖ * (Fintype.card (DerivativeIndex d 1) : ℝ) * ‖u‖ := by
  simp only [normalTraceCLM, _root_.sum_apply, ContinuousLinearMap.comp_apply]
  change ‖∑ j : Fin d, normalComponent ν hν j (T (derivativePart j u))‖ ≤ _
  calc
    _ ≤ ∑ j : Fin d, ‖normalComponent ν hν j (T (derivativePart j u))‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin d, ‖T‖ * ((Fintype.card (DerivativeIndex d 1) : ℝ) * ‖u‖) := by
      apply Finset.sum_le_sum
      intro j _
      exact (normalComponent_norm_le ν hν j _).trans
        ((T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          (derivativePart_norm_le j u) (norm_nonneg T)))
    _ = _ := by simp [mul_assoc]

/-- Full boundedness of the two jets in the original surface Lp quotient.
Fractional regularity is a further obligation, not a hypothesis here. -/
lemma lp_jet_bound (u : SpaceValue 𝕜 d Ω 2 p) :
    ‖T (orderOnePart u)‖ + ‖normalTraceCLM ν hν T u‖ ≤
      ((d : ℝ) + 1) * ‖T‖ * (Fintype.card (DerivativeIndex d 1) : ℝ) * ‖u‖ := by
  have hv := (T.le_opNorm (orderOnePart u)).trans
    (mul_le_mul_of_nonneg_left (orderOnePart_norm_le u) (norm_nonneg T))
  have hn := normalTraceCLM_norm_le ν hν T u
  calc
    _ ≤ ‖T‖ * ((Fintype.card (DerivativeIndex d 1) : ℝ) * ‖u‖) +
        (d : ℝ) * ‖T‖ * (Fintype.card (DerivativeIndex d 1) : ℝ) * ‖u‖ := add_le_add hv hn
    _ = _ := by ring
end NormalLp

/-- Applying the sharp first trace to the actual coordinate derivative
graphs gives fractional membership and full norms uniformly in u and T. -/
lemma first_jet_fractional_bound (hΩb : Bornology.IsBounded (Ω : Set (Domain d)))
    (hΩ : IsC2Domain Ω) (hp1 : 1 < p) (hp : p ≠ ∞)
    (B : C2BoundaryModel 𝕜 Ω p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
      ∀ u : SpaceValue 𝕜 d Ω 2 p,
        ∃ (hg : B.toBoundaryModel.FiniteEnergy (1 - 1 / p.toReal) (T (orderOnePart u)))
          (hw : ∀ j : Fin d, B.toBoundaryModel.FiniteEnergy (1 - 1 / p.toReal)
            (T (derivativePart j u))),
          B.toBoundaryModel.dataNorm (1 - 1 / p.toReal) ⟨T (orderOnePart u), hg⟩ +
            ∑ j : Fin d, B.toBoundaryModel.dataNorm (1 - 1 / p.toReal)
              ⟨T (derivativePart j u), hw j⟩ ≤ C * ‖u‖ := by
  obtain ⟨C, hC, hbound⟩ := domain_sharp_bound 𝕜 d Ω hΩb (isC1Domain_of_isC2Domain hΩ) p hp1 hp
    B.toBoundaryModel
  let q : ℝ := Fintype.card (DerivativeIndex d 1)
  refine ⟨((d : ℝ) + 1) * C * q, by dsimp [q]; positivity, ?_⟩
  intro T hT u
  obtain ⟨hg, hgb⟩ := hbound T hT (orderOnePart u)
  have hw (j : Fin d) := hbound T hT (derivativePart j u)
  choose hw hwb using hw
  refine ⟨hg, hw, ?_⟩
  have hg' := hgb.trans (mul_le_mul_of_nonneg_left (orderOnePart_norm_le u) hC)
  have hw' (j : Fin d) := (hwb j).trans
    (mul_le_mul_of_nonneg_left (derivativePart_norm_le j u) hC)
  calc
    _ ≤ C * (q * ‖u‖) + ∑ _ : Fin d, C * (q * ‖u‖) :=
      add_le_add hg' (Finset.sum_le_sum (fun j _ => hw' j))
    _ = _ := by simp; ring

/-- Empty surface measure forces every localized higher piece to be zero;
this constructs the higher membership witness rather than assuming it. -/
lemma higherEnergy_of_surfaceMeasure_zero (hμ : surfaceMeasure Ω = 0)
    (hp : p ≠ ∞) (B : C2BoundaryModel 𝕜 Ω p) (σ : ℝ)
    (g : BoundaryLp 𝕜 Ω p) : B.HasHigherEnergy σ g := by
  intro j
  refine ⟨⟨0, higher_finite_energy_zero σ p hp⟩, ?_⟩
  rw [boundaryLp_eq_zero_of_surfaceMeasure_zero hμ g, map_zero]
  change wholeLp (0 : DomainLp 𝕜 (⊤ : Opens (Domain (d - 1))) p) =
    (B.atlas.localizer p j) 0
  simp

lemma higherDataNorm_of_surfaceMeasure_zero (hμ : surfaceMeasure Ω = 0)
    (hp : p ≠ ∞) (B : C2BoundaryModel 𝕜 Ω p) (σ : ℝ) (g : B.HigherData σ) :
    B.higherDataNorm σ g = 0 := by
  unfold C2BoundaryModel.higherDataNorm
  apply Finset.sum_eq_zero
  intro j _
  apply (higherFractionalNorm_eq_zero_iff σ p hp _).mpr
  apply sobolev_underlying_injective 𝕜 (d - 1) ⊤ 1 p
  apply wholeLp_injective
  have hpiece := Classical.choose_spec (g.property j)
  change wholeLp ((B.higherPiece σ g j).val.val (zeroIndex (d - 1) 1)) = _ at hpiece
  rw [boundaryLp_eq_zero_of_surfaceMeasure_zero hμ g.val, map_zero] at hpiece
  change wholeLp ((B.higherPiece σ g j).val.val (zeroIndex (d - 1) 1)) =
    (B.atlas.localizer p j) 0 at hpiece
  simpa using hpiece

/-- The complete two-jet bound on every zero-surface-measure boundary.
The constant is zero and no trace or normal regularity is needed. -/
theorem boundedTrace_of_surfaceMeasure_zero (hμ : surfaceMeasure Ω = 0)
    (hp : p ≠ ∞) (B : C2BoundaryModel 𝕜 Ω p) (ν : Domain d → Domain d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p),
      ∀ u : SpaceValue 𝕜 d Ω 2 p,
        ∃ (g : B.HigherData (2 - 1 / p.toReal))
          (h : B.toBoundaryModel.Data (1 - 1 / p.toReal)),
          HasDomainJets ν T u g.val h.val ∧
          B.higherDataNorm (2 - 1 / p.toReal) g +
            B.toBoundaryModel.dataNorm (1 - 1 / p.toReal) h ≤ C * ‖u‖ := by
  refine ⟨0, le_rfl, ?_⟩
  intro T u
  let g : B.HigherData (2 - 1 / p.toReal) :=
    ⟨T (orderOnePart u), higherEnergy_of_surfaceMeasure_zero hμ hp B _ _⟩
  let h : B.toBoundaryModel.Data (1 - 1 / p.toReal) :=
    ⟨0, boundaryModel_finiteEnergy_of_surfaceMeasure_zero hμ hp B.toBoundaryModel _ _⟩
  refine ⟨g, h, ?_, ?_⟩
  · apply (hasDomainJets_iff ν T u g.val h.val).mpr
    exact ⟨rfl, by simp [Filter.EventuallyEq, hμ]⟩
  · rw [higherDataNorm_of_surfaceMeasure_zero hμ hp B,
      boundaryModel_dataNorm_of_surfaceMeasure_zero hμ hp B.toBoundaryModel]
    simp

/-- In dimension zero every open set has empty frontier. -/
lemma surfaceMeasure_zero_dimension (Ω : Opens (Domain 0)) : surfaceMeasure Ω = 0 := by
  have hf : frontier (Ω : Set (Domain 0)) = ∅ :=
    (show IsClopen (Ω : Set (Domain 0)) from ⟨isClosed_discrete _, Ω.isOpen⟩).frontier_eq
  simp only [surfaceMeasure, hf, Measure.restrict_empty, smul_zero]

/-- Explicit empty-boundary specialization of the full bound. -/
theorem boundedTrace_of_empty_frontier (hf : frontier (Ω : Set (Domain d)) = ∅)
    (hp : p ≠ ∞) (B : C2BoundaryModel 𝕜 Ω p) (ν : Domain d → Domain d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p),
      ∀ u : SpaceValue 𝕜 d Ω 2 p,
        ∃ (g : B.HigherData (2 - 1 / p.toReal))
          (h : B.toBoundaryModel.Data (1 - 1 / p.toReal)),
          HasDomainJets ν T u g.val h.val ∧
          B.higherDataNorm (2 - 1 / p.toReal) g +
            B.toBoundaryModel.dataNorm (1 - 1 / p.toReal) h ≤ C * ‖u‖ :=
  boundedTrace_of_surfaceMeasure_zero (by simp [surfaceMeasure, hf]) hp B ν

section DimensionOne
variable {Ω₁ : Opens (Domain 1)}

/-- The unrestricted Lp class on the one-point, zero-dimensional space. -/
def zeroDimensionalLp (g : Lp 𝕜 p (volume : Measure (Domain 0))) :
    DomainLp 𝕜 (⊤ : Opens (Domain 0)) p :=
  (show MemLp g p (volume.restrict (Set.univ : Set (Domain 0))) by
    simp).toLp g

lemma zeroDimensionalLp_coe (g : Lp 𝕜 p (volume : Measure (Domain 0))) :
    zeroDimensionalLp g =ᵐ[volume] g := by
  have h : zeroDimensionalLp g =ᵐ[volume.restrict (Set.univ : Set (Domain 0))] g :=
    MemLp.coeFn_toLp _
  simpa only [Measure.restrict_univ] using h

/-- There are no positive-order derivatives in dimension zero. This is an
actual member of the existing derivative graph, rather than a new space. -/
def zeroDimensionalGraph (g : Lp 𝕜 p (volume : Measure (Domain 0))) :
    SpaceValue 𝕜 0 ⊤ 1 p :=
  ⟨WithLp.toLp 1 (fun _ => zeroDimensionalLp g), by
    intro α
    have hα : α = zeroIndex 0 1 := Subsingleton.elim _ _
    subst α
    change lpDistributionLM (zeroDimensionalLp g) =
      Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue 𝕜 0 ⊤
        (multiIndexWord (natIndex (zeroIndex 0 1))) (lpDistributionLM (zeroDimensionalLp g))
    have hz : multiIndexWord (natIndex (zeroIndex 0 1)) = [] := by
      apply List.eq_nil_iff_length_eq_zero.mpr
      simp
    rw [hz]
    ext φ
    simp [Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue, testPartialCLM]⟩

lemma zeroDimensionalGraph_zero (g : Lp 𝕜 p (volume : Measure (Domain 0))) :
    wholeLp ((zeroDimensionalGraph g).val (zeroIndex 0 1)) = g := by
  apply Lp.ext
  exact (wholeLp_representative _).trans (zeroDimensionalLp_coe g)

lemma higherEnergy_dimension_one (B : C2BoundaryModel 𝕜 Ω₁ p) (σ : ℝ)
    (g : BoundaryLp 𝕜 Ω₁ p) : B.HasHigherEnergy σ g := by
  intro j
  refine ⟨⟨zeroDimensionalGraph (B.atlas.localizedLp p j (B.identify g)), ?_⟩,
    zeroDimensionalGraph_zero _⟩
  exact fun i => Fin.elim0 i

lemma finiteEnergy_dimension_one (B : BoundaryModel 𝕜 Ω₁ p) (s : ℝ)
    (g : BoundaryLp 𝕜 Ω₁ p) : B.FiniteEnergy s g := by
  intro j
  exact (difference_zero_dimension 𝕜 s p _).2

lemma higherDataNorm_dimension_one_le (B : C2BoundaryModel 𝕜 Ω₁ p) (σ : ℝ)
    (g : B.HigherData σ) :
    B.higherDataNorm σ g ≤ (B.chartCount : ℝ) * B.forwardConstant * ‖g.val‖ := by
  unfold C2BoundaryModel.higherDataNorm
  calc
    _ = ∑ j : Fin B.chartCount, ‖B.atlas.localizedLp p j (B.identify g.val)‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [higher_fractionalNorm_zero_dimension 𝕜 σ p]
      rw [← norm_wholeLp]
      exact congrArg norm (Classical.choose_spec (g.property j))
    _ ≤ ∑ _ : Fin B.chartCount, B.forwardConstant * ‖g.val‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact (localizedLp_norm_le B.atlas p j _).trans (B.forward_bound g.val)
    _ = _ := by simp [mul_assoc]

lemma dataNorm_dimension_one_le (hp : p ≠ ∞) (B : BoundaryModel 𝕜 Ω₁ p)
    (s : ℝ) (g : B.Data s) :
    B.dataNorm s g ≤ (B.chartCount : ℝ) * B.forwardConstant * ‖g.val‖ := by
  unfold BoundaryModel.dataNorm Boundary.FiniteAtlas.fractionalNorm
  calc
    _ = ∑ j : Fin B.chartCount, ‖B.atlas.localizedLp p j (B.identify g.val)‖ := by
      apply Finset.sum_congr rfl
      intro j _
      exact fractionalNorm_zero_dimension 𝕜 s p hp _
    _ ≤ ∑ _ : Fin B.chartCount, B.forwardConstant * ‖g.val‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact (localizedLp_norm_le B.atlas p j _).trans (B.forward_bound g.val)
    _ = _ := by simp [mul_assoc]

/-- The full two-jet boundedness conclusion for one-dimensional domains,
including nonempty boundaries. The constant is uniform in the original trace. -/
theorem boundedTrace_dimension_one (hΩb : Bornology.IsBounded (Ω₁ : Set (Domain 1)))
    (hΩ : IsC2Domain Ω₁) (hp : p ≠ ∞) (B : C2BoundaryModel 𝕜 Ω₁ p)
    (ν : Domain 1 → Domain 1) (hν : GeometricNormal Ω₁ ν) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SpaceValue 𝕜 1 Ω₁ 1 p →L[𝕜] BoundaryLp 𝕜 Ω₁ p), IsTrace T →
      ∀ u : SpaceValue 𝕜 1 Ω₁ 2 p,
        ∃ (g : B.HigherData (2 - 1 / p.toReal))
          (h : B.toBoundaryModel.Data (1 - 1 / p.toReal)),
          HasDomainJets ν T u g.val h.val ∧
          B.higherDataNorm (2 - 1 / p.toReal) g +
            B.toBoundaryModel.dataNorm (1 - 1 / p.toReal) h ≤ C * ‖u‖ := by
  obtain ⟨T₀, _, huniq⟩ := trace_exists 𝕜 1 Ω₁ hΩb (isC1Domain_of_isC2Domain hΩ) p hp
  let A : ℝ := (B.chartCount : ℝ) * B.forwardConstant
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) B.forward_nonneg
  let K : ℝ := 2 * ‖T₀‖ * (Fintype.card (DerivativeIndex 1 1) : ℝ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨A * K, mul_nonneg hA hK, ?_⟩
  intro T hT u
  have hTT : T = T₀ := huniq T hT
  subst T
  let g : B.HigherData (2 - 1 / p.toReal) :=
    ⟨T₀ (orderOnePart u), higherEnergy_dimension_one B _ _⟩
  let h : B.toBoundaryModel.Data (1 - 1 / p.toReal) :=
    ⟨normalTraceCLM ν hν T₀ u, finiteEnergy_dimension_one B.toBoundaryModel _ _⟩
  refine ⟨g, h, canonical_hasDomainJets ν hν T₀ u, ?_⟩
  have hjet : ‖g.val‖ + ‖h.val‖ ≤ K * ‖u‖ := by
    have hb := lp_jet_bound ν hν T₀ u
    norm_num at hb
    simpa [g, h, K] using hb
  calc
    _ ≤ A * ‖g.val‖ + A * ‖h.val‖ :=
      add_le_add (higherDataNorm_dimension_one_le B _ g)
        (dataNorm_dimension_one_le hp B.toBoundaryModel _ h)
    _ = A * (‖g.val‖ + ‖h.val‖) := (mul_add _ _ _).symm
    _ ≤ A * (K * ‖u‖) := mul_le_mul_of_nonneg_left hjet hA
    _ = _ := (mul_assoc _ _ _).symm
end DimensionOne


open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTrace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both jet norms can be transported to any faithful C² atlas while keeping
both original surface Lp classes unchanged. -/
lemma transfer_jet_data (hΩb : Bornology.IsBounded (Ω : Set (Domain d)))
    (hp1 : 1 < p) (hp : p ≠ ∞) (B D : C2BoundaryModel 𝕜 Ω p) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g : B.HigherData (2 - 1 / p.toReal))
        (h : B.toBoundaryModel.Data (1 - 1 / p.toReal)),
        ∃ (g' : D.HigherData (2 - 1 / p.toReal))
          (h' : D.toBoundaryModel.Data (1 - 1 / p.toReal)),
          g'.val = g.val ∧ h'.val = h.val ∧
          D.higherDataNorm (2 - 1 / p.toReal) g' +
            D.toBoundaryModel.dataNorm (1 - 1 / p.toReal) h' ≤
              K * (B.higherDataNorm (2 - 1 / p.toReal) g +
                B.toBoundaryModel.dataNorm (1 - 1 / p.toReal) h) := by
  have hc : IsCompact (frontier (Ω : Set (Domain d))) :=
    hΩb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  let : CompactSpace (frontier (Ω : Set (Domain d))) := isCompact_iff_compactSpace.mp hc
  obtain ⟨hmem, C, E, hC, hE, hnorm⟩ := higher_atlas_independence 𝕜 d Ω hΩb p hp1 hp B D
  obtain ⟨hs0, hs1⟩ := SharpTraceBound.endpoint_exponent hp1 hp
  obtain ⟨J, hJ, hnormal⟩ := D.toBoundaryModel.transferData_norm_bound
    B.toBoundaryModel (1 - 1 / p.toReal) hs0 hs1 hp
  refine ⟨max C J, le_trans hC.le (le_max_left _ _), ?_⟩
  intro g h
  let g' : D.HigherData (2 - 1 / p.toReal) := ⟨g.val, (hmem g.val).mp g.property⟩
  let h' := D.toBoundaryModel.transferData B.toBoundaryModel
    (1 - 1 / p.toReal) hs0 hs1 hp h
  refine ⟨g', h', rfl, rfl, ?_⟩
  have hg := (hnorm g g' rfl).1
  have hh := hnormal h
  have hg0 := B.higherDataNorm_nonneg (2 - 1 / p.toReal) g
  have hh0 : 0 ≤ B.toBoundaryModel.dataNorm (1 - 1 / p.toReal) h :=
    B.atlas.fractionalNorm_nonneg (1 - 1 / p.toReal) p ⟨B.identify h.val, h.property⟩
  calc
    _ ≤ C * B.higherDataNorm (2 - 1 / p.toReal) g +
        J * B.toBoundaryModel.dataNorm (1 - 1 / p.toReal) h := add_le_add hg hh
    _ ≤ max C J * B.higherDataNorm (2 - 1 / p.toReal) g +
        max C J * B.toBoundaryModel.dataNorm (1 - 1 / p.toReal) h :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hg0)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hh0)
    _ = _ := (mul_add _ _ _).symm

/-- Establishing the full two-jet bound in one faithful C² model suffices.
Every transferred datum is the identical original surface Lp class. -/
lemma bounded_trace_of_model (hΩb : Bornology.IsBounded (Ω : Set (Domain d)))
    (hp1 : 1 < p) (hp : p ≠ ∞) (B D : C2BoundaryModel 𝕜 Ω p)
    (ν : Domain d → Domain d)
    (hB : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
      ∀ u : SpaceValue 𝕜 d Ω 2 p,
        ∃ (g : B.HigherData (2 - 1 / p.toReal))
          (h : B.toBoundaryModel.Data (1 - 1 / p.toReal)),
          HasDomainJets ν T u g.val h.val ∧
          B.higherDataNorm (2 - 1 / p.toReal) g +
            B.toBoundaryModel.dataNorm (1 - 1 / p.toReal) h ≤ C * ‖u‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
      ∀ u : SpaceValue 𝕜 d Ω 2 p,
        ∃ (g : D.HigherData (2 - 1 / p.toReal))
          (h : D.toBoundaryModel.Data (1 - 1 / p.toReal)),
          HasDomainJets ν T u g.val h.val ∧
          D.higherDataNorm (2 - 1 / p.toReal) g +
            D.toBoundaryModel.dataNorm (1 - 1 / p.toReal) h ≤ C * ‖u‖ := by
  obtain ⟨K, hK, htransfer⟩ := transfer_jet_data hΩb hp1 hp B D
  obtain ⟨C, hC, hbound⟩ := hB
  refine ⟨K * C, mul_nonneg hK hC, ?_⟩
  intro T hT u
  obtain ⟨g, h, hjets, hgh⟩ := hbound T hT u
  obtain ⟨g', h', hg', hh', hn⟩ := htransfer g h
  refine ⟨g', h', ?_, ?_⟩
  · simpa only [hg', hh'] using hjets
  · calc
      _ ≤ K * (B.higherDataNorm (2 - 1 / p.toReal) g +
          B.toBoundaryModel.dataNorm (1 - 1 / p.toReal) h) := hn
      _ ≤ K * (C * ‖u‖) := mul_le_mul_of_nonneg_left hgh hK
      _ = _ := (mul_assoc _ _ _).symm



open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTrace
open SecondTraceFlat
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Finite chart estimates construct the actual higher-data membership
witness and control its full atlas norm. Uniqueness of the original weak
derivative graph identifies each chosen piece with the estimated witness. -/
lemma higher_trace_bound_of_chart_estimates (B : C2BoundaryModel 𝕜 Ω p) (σ : ℝ)
    (hlocal : ∀ j : Fin B.chartCount, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
      ∀ u : SpaceValue 𝕜 d Ω 2 p,
        ∃ g : HigherFractionalSpace 𝕜 (d - 1) σ p,
          wholeLp (g.val.val (zeroIndex (d - 1) 1)) =
            B.atlas.localizedLp p j (B.identify (T (orderOnePart u))) ∧
          higherFractionalNorm σ p g ≤ C * ‖u‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
      ∀ u : SpaceValue 𝕜 d Ω 2 p,
        ∃ g : B.HigherData σ, g.val = T (orderOnePart u) ∧
          B.higherDataNorm σ g ≤ C * ‖u‖ := by
  choose C hC hbound using hlocal
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), ?_⟩
  intro T hT u
  choose g hg hgb using fun j => hbound j T hT u
  let G : B.HigherData σ := ⟨T (orderOnePart u), fun j => ⟨g j, hg j⟩⟩
  refine ⟨G, rfl, ?_⟩
  have hpiece (j : Fin B.chartCount) : B.higherPiece σ G j = g j :=
    B.higherPiece_unique σ G.val j _ _ (B.higherPiece_spec σ G j) (hg j)
  calc
    _ = ∑ j, higherFractionalNorm σ p (g j) := by
      unfold C2BoundaryModel.higherDataNorm
      exact Finset.sum_congr rfl (fun j _ => congrArg (higherFractionalNorm σ p) (hpiece j))
    _ ≤ ∑ j, C j * ‖u‖ := Finset.sum_le_sum (fun j _ => hgb j)
    _ = _ := by rw [Finset.sum_mul]



open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.Sobolev.Lines ExpandedFA.Sobolev.HalfSpace
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound
open ExpandedFA.PartIV.SecondTraceFlat
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- Once the tangential weak derivative identities have constructed a boundary
W1p graph, applying the sharp first trace to each actual derivative gives the
full higher value norm and the normal norm, with a common uniform constant. -/
theorem flat_jet_fractional_bound_of_graph (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (i : Fin (n + 1))
      (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
        Lp 𝕜 p (volume : Measure (Transverse i))), CoordinateTraceCondition i T →
      ∀ (u : SpaceValue 𝕜 (n + 1) (upper i) 2 p)
        (v : SpaceValue 𝕜 n ⊤ 1 p),
        wholeLp (v.val (zeroIndex n 1)) = reindexedTrace i T (orderOnePart u) →
        (∀ j : Fin n, wholeLp (v.val (firstIndex j)) =
          reindexedTrace i T (derivativePart (i.succAbove j) u)) →
        ∃ (g : HigherFractionalSpace 𝕜 n (2 - 1 / p.toReal) p)
          (h : FractionalSpace 𝕜 n (1 - 1 / p.toReal) p),
          g.val = v ∧ h.val = reindexedTrace i T (derivativePart i u) ∧
          higherFractionalNorm (2 - 1 / p.toReal) p g +
            fractionalNorm (1 - 1 / p.toReal) p h ≤ C * ‖u‖ := by
  obtain ⟨C, hC, hbound⟩ := sharp_trace_bound n p hp1 hp
  let q : ℝ := Fintype.card (DerivativeIndex (n + 1) 1)
  refine ⟨(4 + (n + 1 : ℝ) * C) * q, by dsimp [q]; positivity, ?_⟩
  intro 𝕜 _ i T hT u v hv0 hvj
  have hs : (2 - 1 / p.toReal) - 1 = 1 - 1 / p.toReal := by ring
  have hj (j : Fin n) := (hbound 𝕜 i).2 T hT (derivativePart (i.succAbove j) u)
  choose hj hbj using hj
  have hmem (j : Fin n) :
      differenceEnergy ((2 - 1 / p.toReal) - 1) p (wholeLp (v.val (firstIndex j))) < ∞ := by
    rw [hs, hvj j]
    exact hj j
  obtain ⟨hh, hbh⟩ := (hbound 𝕜 i).2 T hT (derivativePart i u)
  let g : HigherFractionalSpace 𝕜 n (2 - 1 / p.toReal) p := ⟨v, hmem⟩
  let h : FractionalSpace 𝕜 n (1 - 1 / p.toReal) p :=
    ⟨reindexedTrace i T (derivativePart i u), hh⟩
  refine ⟨g, h, rfl, rfl, ?_⟩
  have hb0 : ‖wholeLp (v.val (zeroIndex n 1))‖ ≤ 4 * (q * ‖u‖) := by
    rw [hv0]
    exact (reindexedTrace_norm_le i hp T hT (orderOnePart u)).trans
      (mul_le_mul_of_nonneg_left (orderOnePart_norm_le u) (by norm_num))
  have hbj' (j : Fin n) :
      fractionalNorm ((2 - 1 / p.toReal) - 1) p
        ⟨wholeLp (v.val (firstIndex j)), hmem j⟩ ≤ C * (q * ‖u‖) := by
    have h := (hbj j).trans (mul_le_mul_of_nonneg_left
      (derivativePart_norm_le (i.succAbove j) u) hC)
    simpa only [fractionalNorm, hs, hvj j] using h
  have hbh' : fractionalNorm (1 - 1 / p.toReal) p h ≤ C * (q * ‖u‖) :=
    hbh.trans (mul_le_mul_of_nonneg_left (derivativePart_norm_le i u) hC)
  calc
    _ = ‖wholeLp (v.val (zeroIndex n 1))‖ +
        ∑ j : Fin n, fractionalNorm ((2 - 1 / p.toReal) - 1) p
          ⟨wholeLp (v.val (firstIndex j)), hmem j⟩ + fractionalNorm (1 - 1 / p.toReal) p h := rfl
    _ ≤ 4 * (q * ‖u‖) + ∑ _ : Fin n, C * (q * ‖u‖) + C * (q * ‖u‖) :=
      add_le_add (add_le_add hb0 (Finset.sum_le_sum (fun j _ => hbj' j))) hbh'
    _ = _ := by simp; ring



open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace

lemma normalized_gradient_component_contDiffOn {d : ℕ}
    (U : Set (Domain d)) (hU : IsOpen U) (r : Domain d → ℝ)
    (hr : ContDiffOn ℝ 2 r U)
    (hn : ∀ x ∈ U, (∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2) ≠ 0)
    (j : Fin d) :
    ContDiffOn ℝ 1 (fun x => fderiv ℝ r x (coordinateVector j) /
      Real.sqrt (∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2)) U := by
  have hg (k : Fin d) : ContDiffOn ℝ 1
      (fun x => fderiv ℝ r x (coordinateVector k)) U :=
    (hr.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  have hs : ContDiffOn ℝ 1 (fun x => ∑ k : Fin d,
      (fderiv ℝ r x (coordinateVector k)) ^ 2) U :=
    ContDiffOn.sum (fun k _ => (hg k).pow 2)
  apply (hg j).div (hs.sqrt hn)
  intro x hx
  exact (Real.sqrt_pos.mpr (lt_of_le_of_ne
    (Finset.sum_nonneg (fun k _ => sq_nonneg (fderiv ℝ r x (coordinateVector k))))
    (Ne.symm (hn x hx)))).ne'

/-- A pointwise regular defining function is regular on an open neighborhood. -/
lemma exists_normalized_gradient_regular_neighborhood {d : ℕ}
    (U : Set (Domain d)) (hU : IsOpen U) (r : Domain d → ℝ)
    (hr : ContDiffOn ℝ 2 r U) (x : Domain d) (hx : x ∈ U)
    (hn : (∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2) ≠ 0) :
    ∃ V : Set (Domain d), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      (∀ y ∈ V, (∑ k : Fin d, (fderiv ℝ r y (coordinateVector k)) ^ 2) ≠ 0) ∧
      ∀ j : Fin d, ContDiffOn ℝ 1 (fun y => fderiv ℝ r y (coordinateVector j) /
        Real.sqrt (∑ k : Fin d, (fderiv ℝ r y (coordinateVector k)) ^ 2)) V := by
  have hg (k : Fin d) : ContinuousAt
      (fun y => fderiv ℝ r y (coordinateVector k)) x :=
    (((hr.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const :
      ContDiffOn ℝ 1 (fun y => fderiv ℝ r y (coordinateVector k)) U).continuousOn x hx).continuousAt
      (hU.mem_nhds hx)
  have hs : ContinuousAt (fun y => ∑ k : Fin d,
      (fderiv ℝ r y (coordinateVector k)) ^ 2) x :=
    by
      simpa only [ContinuousAt, Pi.pow_apply] using tendsto_finsetSum Finset.univ (fun k _ => (hg k).pow 2)
  have hpos : 0 < ∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2 :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun k _ => sq_nonneg _)) (Ne.symm hn)
  have hUx : ∀ᶠ y in 𝓝 x, y ∈ U := hU.mem_nhds hx
  have hevent : ∀ᶠ y in 𝓝 x, y ∈ U ∧
      0 < ∑ k : Fin d, (fderiv ℝ r y (coordinateVector k)) ^ 2 :=
    hUx.and (hs.eventually (isOpen_Ioi.mem_nhds hpos))
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hevent
  have hVU : V ⊆ U := fun y hy => (hVsub hy).1
  have hVn : ∀ y ∈ V, (∑ k : Fin d, (fderiv ℝ r y (coordinateVector k)) ^ 2) ≠ 0 :=
    fun y hy => (hVsub hy).2.ne'
  exact ⟨V, hV, hxV, hVU, hVn, fun j =>
    normalized_gradient_component_contDiffOn V hV r (hr.mono hVU) hVn j⟩

/-- A normalized defining-function coefficient has a bounded Lipschitz
compact extension around any compact subset of its regular open set. -/
lemma exists_compact_normalized_gradient_component {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (U : Set (Domain d)) (hU : IsOpen U) (r : Domain d → ℝ)
    (hr : ContDiffOn ℝ 2 r U)
    (hn : ∀ x ∈ U, (∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2) ≠ 0)
    (K : Set (Domain d)) (hK : IsCompact K) (hKU : K ⊆ U) (j : Fin d) :
    ∃ a : Domain d → 𝕜, ContDiff ℝ 1 a ∧ HasCompactSupport a ∧
      tsupport a ⊆ U ∧
      EqOn a (fun x => ((fderiv ℝ r x (coordinateVector j) /
        Real.sqrt (∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2) : ℝ) : 𝕜)) K ∧
      ∃ M L : ℝ≥0, (∀ x, ‖a x‖ ≤ M) ∧
        ∀ x y, ‖a x - a y‖ ≤ L *
          ExpandedFA.PartIV.FractionalSobolev.euclideanLength (x - y) := by
  let a0 : Domain d → 𝕜 := fun x => ((fderiv ℝ r x (coordinateVector j) /
    Real.sqrt (∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2) : ℝ) : 𝕜)
  have ha0 : ContDiffOn ℝ 1 a0 U :=
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp_contDiffOn
      (normalized_gradient_component_contDiffOn U hU r hr hn j)
  obtain ⟨a, ha, hac, hasub, V, _, hKV, hVa⟩ :=
    exists_compact_contDiff_extension 1 U hU K hK hKU a0 ha0
  refine ⟨a, ha, hac, hasub, fun x hx => hVa (hKV hx), ?_⟩
  exact compact_c1_coefficient_bounds a ha hac



open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.Sobolev.C1Extension SecondTraceFlat ExpandedFA.Sobolev.HalfSpace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]

private lemma mixed_derivative_coordinate (i j : Fin d) (u : SpaceValue 𝕜 d Ω 2 p) :
    (derivativePart i u).val (coordinateIndex j) =
      (derivativePart j u).val (coordinateIndex i) := by
  have hi : derivativePartIndex i (coordinateIndex j) =
      derivativePartIndex j (coordinateIndex i) := by
    apply Subtype.ext
    funext k
    apply Fin.ext
    simp [derivativePartIndex, coordinateIndex, boundedIndex, natIndex, Pi.single_apply,
      add_comm]
  simp only [derivativePart_apply, hi]

lemma coordinate_trace_tangential_test (i j : Fin d) (hij : i ≠ j) (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜] Lp 𝕜 p (volume : Measure (Lines.Transverse i)))
    (hT : IsCoordinateTrace i T) (u : SpaceValue 𝕜 d (upper i) 2 p)
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    (∫ y : Lines.Transverse i, testPartialCLM [j] φ (Lines.coordinateLine i y 0) *
      T (orderOnePart u) y) =
    -(∫ y : Lines.Transverse i, φ (Lines.coordinateLine i y 0) * T (derivativePart j u) y) := by
  have ht (v : SpaceValue 𝕜 d (upper i) 1 p) (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) :
      lpDistribution (zeroLp ⊤ (v.val (coordinateIndex j))) ψ =
        -lpDistribution (zeroLp ⊤ (v.val (zeroIndex d 1))) (testPartialCLM [j] ψ) := by
    have hh := tangent_weak_zero_extension i j hij (v.val (zeroIndex d 1))
      (fun k => v.val (coordinateIndex k)) (coordinate_weak_derivatives i v)
      (zeroLp ⊤ (v.val (zeroIndex d 1))) (zeroLp ⊤ (v.val (coordinateIndex j)))
      (by simpa using zeroLp_coe (Λ := ⊤) (v.val (zeroIndex d 1)))
      (by simpa using zeroLp_coe (Λ := ⊤) (v.val (coordinateIndex j)))
    exact congrArg (fun D => D ψ) hh
  have hg := coordinate_trace_normal_green i hp T hT (orderOnePart u) (testPartialCLM [j] φ)
  have hgj := coordinate_trace_normal_green i hp T hT (derivativePart j u) φ
  have hm := ht (derivativePart i u) φ
  have hv := ht (orderOnePart u) (testPartialCLM [i] φ)
  rw [derivativePart_zero_eq_coordinate, mixed_derivative_coordinate] at hm
  rw [← derivativePart_zero_eq_coordinate j u] at hv
  rw [Smoothing.testPartial_single_comm i j φ] at hg
  linear_combination hg + hgj - hm - hv

open ExpandedFA.PartIV.SharpTraceExtension ExpandedFA.PartIV.SharpTraceExtension.SmoothLift
open ExpandedFA.PartIV.SharpTraceBound

private def boundaryTestLift {n : ℕ} (i : Fin (n+1))
    (ψ : Tests 𝕜 (⊤ : Opens (Domain n))) : Tests 𝕜 (⊤ : Opens (Domain (n+1))) where
  toFun x := jetCutoff (x i) • ψ (i.removeNth x)
  contDiff' := by
    have hA := flatCoordinates_contDiff i
    exact (jetCutoff_contDiff.comp hA.snd).smul (ψ.contDiff.comp hA.fst)
  hasCompactSupport' := by
    let F : Domain n × ℝ → 𝕜 := fun z => jetCutoff z.2 • ψ z.1
    have hs : tsupport F ⊆ tsupport ψ ×ˢ tsupport jetCutoff := by
      apply closure_minimal
      · intro z hz
        exact ⟨subset_tsupport ψ (fun h => hz (by simp [F, h])),
          subset_tsupport jetCutoff (fun h => hz (by simp [F, h]))⟩
      · exact (isClosed_tsupport ψ).prod (isClosed_tsupport jetCutoff)
    have hF : HasCompactSupport F :=
      (ψ.hasCompactSupport.prod jetCutoff_compactSupport).of_isClosed_subset
        (isClosed_tsupport F) hs
    have hcomp : HasCompactSupport (F ∘ flatCoordinates i) :=
      hF.comp_isClosedEmbedding (flatCoordinates i).isClosedEmbedding
    convert hcomp using 1
    rfl
  tsupport_subset' := subset_univ _

private lemma boundaryTestLift_boundary {n : ℕ} (i : Fin (n+1))
    (ψ : Tests 𝕜 (⊤ : Opens (Domain n))) (z : Domain n) :
    boundaryTestLift i ψ (i.insertNth 0 z) = ψ z := by
  change jetCutoff _ • ψ _ = _
  simp

private lemma boundaryTestLift_tangential {n : ℕ} (i : Fin (n+1))
    (ψ : Tests 𝕜 (⊤ : Opens (Domain n))) (j : Fin n) (z : Domain n) :
    testPartialCLM [i.succAbove j] (boundaryTestLift i ψ) (i.insertNth 0 z) =
      testPartialCLM [j] ψ z := by
  rw [testPartial_single_apply, testPartial_single_apply]
  let F : Domain n × ℝ → 𝕜 := fun z => jetCutoff z.2 • ψ z.1
  have hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z : Domain n × ℝ => ψ z.1) :=
    ψ.contDiff.comp contDiff_fst
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F :=
    (jetCutoff_contDiff.comp contDiff_snd).smul hψ
  change fderiv ℝ (fun x => F (flatCoordinatesCLM i x)) _ _ = _
  rw [fderiv_linear_comp (flatCoordinatesCLM i) F hF,
    flatCoordinatesCLM_tangential]
  have hflat : flatCoordinatesCLM i (i.insertNth 0 z) = (z, 0) := by
    ext k <;> simp [flatCoordinatesCLM]
  rw [hflat]
  rw [cutoff_smul_fderiv jetCutoff (fun z : Domain n × ℝ => ψ z.1)
    jetCutoff_contDiff hψ]
  simp only [jetCutoff_zero, one_smul, zero_smul, add_zero]
  exact fderiv_linear_comp (ContinuousLinearMap.fst ℝ (Domain n) ℝ) ψ ψ.contDiff
    (z, 0) (coordinateVector j, 0)


private lemma boundaryPairing_reindexed {n : ℕ} (i : Fin (n+1))
    (T : SpaceValue 𝕜 (n+1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Lines.Transverse i)))
    (v : SpaceValue 𝕜 (n+1) (upper i) 1 p) (F : Domain (n+1) → 𝕜) :
    (∫ y : Lines.Transverse i, F (Lines.coordinateLine i y 0) * T v y) =
      ∫ z : Domain n, F (i.insertNth 0 z) * reindexedTrace i T v z := by
  have he := (boundaryCoordinates_measurePreserving i).integral_comp'
    (fun y : Lines.Transverse i => F (Lines.coordinateLine i y 0) * T v y)
  rw [← he]
  have hc := Lp.coeFn_compMeasurePreserving (T v) (boundaryCoordinates_measurePreserving i)
  apply integral_congr_ae
  filter_upwards [hc] with z hz
  change reindexedTrace i T v z = T v (transverseFinEquiv i z) at hz
  change F (Lines.coordinateLine i (transverseFinEquiv i z) 0) * T v (transverseFinEquiv i z) = _
  rw [coordinateLine_transverseFinEquiv, hz]

lemma reindexed_trace_tangential_test {n : ℕ} (i : Fin (n+1)) (j : Fin n) (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 (n+1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Lines.Transverse i)))
    (hT : IsCoordinateTrace i T) (u : SpaceValue 𝕜 (n+1) (upper i) 2 p)
    (ψ : Tests 𝕜 (⊤ : Opens (Domain n))) :
    (∫ z : Domain n, testPartialCLM [j] ψ z * reindexedTrace i T (orderOnePart u) z) =
      -(∫ z : Domain n, ψ z * reindexedTrace i T (derivativePart (i.succAbove j) u) z) := by
  have hh := coordinate_trace_tangential_test i (i.succAbove j)
    (Fin.succAbove_ne i j).symm hp T hT u (boundaryTestLift i ψ)
  rw [boundaryPairing_reindexed i T (orderOnePart u),
    boundaryPairing_reindexed i T (derivativePart (i.succAbove j) u)] at hh
  simpa only [boundaryTestLift_boundary, boundaryTestLift_tangential] using hh


open ExpandedFA.PartIV.FractionalSobolev

/-- Regard a whole-space Lp class in the original domain Lp quotient for ⊤. -/
def domainLpOfWhole {n : ℕ} (g : Lp 𝕜 p (volume : Measure (Domain n))) :
    DomainLp 𝕜 (⊤ : Opens (Domain n)) p :=
  (show MemLp g p (volume.restrict (Set.univ : Set (Domain n))) by
    simpa only [Measure.restrict_univ] using Lp.memLp g).toLp g

lemma domainLpOfWhole_coe {n : ℕ} (g : Lp 𝕜 p (volume : Measure (Domain n))) :
    domainLpOfWhole g =ᵐ[volume] g := by
  have h : domainLpOfWhole g =ᵐ[volume.restrict (Set.univ : Set (Domain n))] g :=
    MemLp.coeFn_toLp _
  simpa only [Measure.restrict_univ] using h

@[simp] lemma wholeLp_domainLpOfWhole {n : ℕ}
    (g : Lp 𝕜 p (volume : Measure (Domain n))) : wholeLp (domainLpOfWhole g) = g := by
  apply Lp.ext
  exact (wholeLp_representative _).trans (domainLpOfWhole_coe g)

lemma domainLpOfWhole_distribution_apply {n : ℕ}
    (g : Lp 𝕜 p (volume : Measure (Domain n))) (ψ : Tests 𝕜 (⊤ : Opens (Domain n))) :
    lpDistribution (domainLpOfWhole g) ψ = ∫ z : Domain n, ψ z * g z := by
  simp only [lpDistribution_apply, Opens.coe_top, Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards [domainLpOfWhole_coe g] with z hz
  rw [hz]

/-- The value trace of an actual half-space W²,p graph has a genuine W¹,p
boundary graph. Its first weak derivatives are the first traces of the actual
interior tangential derivatives. This includes tangential dimension zero. -/
lemma coordinate_trace_first_order_graph {n : ℕ} (i : Fin (n+1)) (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 (n+1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Lines.Transverse i)))
    (hT : IsCoordinateTrace i T) (u : SpaceValue 𝕜 (n+1) (upper i) 2 p) :
    ∃ v : SpaceValue 𝕜 n ⊤ 1 p,
      wholeLp (v.val (zeroIndex n 1)) = reindexedTrace i T (orderOnePart u) ∧
      ∀ j : Fin n, wholeLp (v.val (firstIndex j)) =
        reindexedTrace i T (derivativePart (i.succAbove j) u) := by
  let g0 := domainLpOfWhole (reindexedTrace i T (orderOnePart u))
  let g := fun j : Fin n => domainLpOfWhole
    (reindexedTrace i T (derivativePart (i.succAbove j) u))
  have hw : Lines.HasWeakCoordinateDerivatives g0 g := by
    intro j
    ext ψ
    simp only [neg_apply, ContinuousLinearMap.comp_apply]
    change lpDistribution (domainLpOfWhole _) ψ =
      -lpDistribution (domainLpOfWhole _) (testPartialCLM [j] ψ)
    rw [domainLpOfWhole_distribution_apply, domainLpOfWhole_distribution_apply]
    exact neg_eq_iff_eq_neg.mp (reindexed_trace_tangential_test i j hp T hT u ψ).symm
  obtain ⟨v, hv⟩ := (Lines.first_order_membership_iff g0).mpr ⟨g, hw⟩
  refine ⟨v, ?_, ?_⟩
  · rw [hv]
    exact wholeLp_domainLpOfWhole _
  · intro j
    have hj : v.val (firstIndex j) = g j := by
      apply lpDistribution_injective
      rw [first_derivative_formula, hv]
      exact (hw j).symm
    rw [hj]
    exact wholeLp_domainLpOfWhole _



open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.Sobolev.C1Extension ExpandedFA.Sobolev.C1Extension.Transport
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.PartIV.SharpTrace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open SecondTraceFlat SecondTraceTransport

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Genuine order-two flattening into the entire half-space. The artificial
edge of the coordinate chart creates no weak-derivative jump. -/
lemma exists_flattened_two_localization (hp1 : 1 < p) (hp : p ≠ ∞)
    (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    (θ χ : Tests 𝕜 (⊤ : Opens (Domain d))) (hχ : tsupport χ ⊆ Φ.target) :
    ∃ E : SpaceValue 𝕜 d Ω 2 p →L[𝕜] SpaceValue 𝕜 d (upper i) 2 p,
      ∀ (u : SpaceValue 𝕜 d Ω 2 p) (f : Domain d → 𝕜),
      u.val (zeroIndex d 2) =ᵐ[volume.restrict (Ω : Set (Domain d))] f →
      (E u).val (zeroIndex d 2) =ᵐ[volume.restrict (upper i : Set (Domain d))]
        fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y)) := by
  let V := chartPreimage Φ.symm Ω
  have hVupper : V ≤ upper i := by
    rintro y ⟨hyt, hyΩ⟩
    have h := (hside (Φ.symm y) (Φ.map_target hyt)).mp hyΩ
    change 0 < y i
    simpa only [Φ.right_inv hyt] using h
  let K : Set (Domain d) := tsupport χ ∩ (upper i : Set (Domain d))
  have hKclosed : IsClosed (K ∪ (upper i : Set (Domain d))ᶜ) := by
    convert (isClosed_tsupport χ).union (upper i).isOpen.isClosed_compl using 1
    ext x
    simp only [K, mem_union, mem_inter_iff, mem_compl_iff]
    tauto
  have hKV : K ⊆ V := by
    rintro y ⟨hyχ, hyU⟩
    have hyT := hχ hyχ
    refine ⟨hyT, (hside (Φ.symm y) (Φ.map_target hyT)).mpr ?_⟩
    change 0 < y i at hyU
    simpa only [Φ.right_inv hyT] using hyU
  obtain ⟨η, hη, hηone⟩ := exists_compact_ambient_cutoff (𝕜 := 𝕜)
    (tsupport χ) χ.hasCompactSupport ⟨Φ.target, Φ.open_target⟩ hχ
  obtain ⟨M, hM⟩ := smooth_multiplication 𝕜 d Ω p θ θ.contDiff θ.hasCompactSupport
  obtain ⟨P, hP⟩ := localized_transport 𝕜 d Ω p hp1 hp Φ.symm hInv hΦ
    η η.contDiff η.hasCompactSupport hη
  obtain ⟨Z, hZ⟩ := localized_zero_extension 𝕜 d V (upper i) hVupper K
    hKclosed hKV χ χ.contDiff χ.hasCompactSupport
    (fun y hy => ⟨hy.2, hVupper hy.1⟩) p
  refine ⟨Z.comp (P.comp M), ?_⟩
  intro u f hf
  have hM' := hM u f hf.symm
  have hP' := hP (M u) (fun x => θ x * f x) hM'.symm
  apply (hZ (P (M u)) (fun y => η y * (θ (Φ.symm y) * f (Φ.symm y))) hP'.symm).trans
  filter_upwards [ae_restrict_mem (upper i).isOpen.measurableSet] with y hy
  by_cases hyχ : χ y = 0
  · by_cases hyV : y ∈ V <;> simp [hyV, hyχ]
  · have hys : y ∈ tsupport χ := subset_tsupport χ hyχ
    have hyV : y ∈ V := hKV ⟨hys, hy⟩
    simp only [indicator_of_mem hyV, hηone y hys, one_mul]

/-- Localizations of order one and two with the same representative formula
have identical first-order parts, by uniqueness in the actual weak graph. -/
lemma flattened_two_orderOnePart
    (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (θ χ : Tests 𝕜 (⊤ : Opens (Domain d)))
    (E₁ : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d (upper i) 1 p)
    (E₂ : SpaceValue 𝕜 d Ω 2 p →L[𝕜] SpaceValue 𝕜 d (upper i) 2 p)
    (hE₁ : ∀ (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜),
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f →
      (E₁ u).val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))]
        fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y)))
    (hE₂ : ∀ (u : SpaceValue 𝕜 d Ω 2 p) (f : Domain d → 𝕜),
      u.val (zeroIndex d 2) =ᵐ[volume.restrict (Ω : Set (Domain d))] f →
      (E₂ u).val (zeroIndex d 2) =ᵐ[volume.restrict (upper i : Set (Domain d))]
        fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y)))
    (u : SpaceValue 𝕜 d Ω 2 p) :
    orderOnePart (E₂ u) = E₁ (orderOnePart u) := by
  apply sobolev_underlying_injective 𝕜 d (upper i) 1 p
  apply Lp.ext
  simpa only [orderOnePart_apply, orderOneToTwo_zero] using
    (hE₂ u (u.val (zeroIndex d 2)) Filter.EventuallyEq.rfl).trans
      (hE₁ (orderOnePart u) (u.val (zeroIndex d 2))
        (by simpa only [orderOnePart_apply, orderOneToTwo_zero] using
          (Filter.EventuallyEq.rfl : u.val (zeroIndex d 2) =ᵐ[volume.restrict (Ω : Set (Domain d))]
            u.val (zeroIndex d 2)))).symm



open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.Sobolev.C1Extension ExpandedFA.Sobolev.C1Extension.Transport
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.PartIV.SharpTrace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open SecondTraceFlat SecondTraceTransport

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Compactly supported first-order flattening on an arbitrary C² chart.
All bounds are derived on a smaller chart containing the cutoff support. -/
lemma exists_flattened_one_localization
    (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    (θ χ : Tests 𝕜 (⊤ : Opens (Domain d))) (hχ : tsupport χ ⊆ Φ.target) :
    ∃ E : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d (upper i) 1 p,
      ∀ (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜),
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f →
      (E u).val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))]
        fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y)) := by
  obtain ⟨Ψ, B, J, hfun, hinv, hχΨ, hΨΦ, hΨ, hΨinv, hB0, hB, hDD, hJ1, hJ, hTarget⟩ :=
    exists_bounded_c2_subchart Φ.symm hInv hΦ (tsupport χ) χ.hasCompactSupport hχ
  have hsideΨ : ∀ y ∈ Ψ.source, y ∈ upper i ↔ Ψ y ∈ Ω := by
    intro y hy
    have hyT := hΨΦ hy
    rw [show Ψ y = Φ.symm y from congrFun hfun y]
    have h := hside (Φ.symm y) (Φ.map_target hyT)
    change 0 < y i ↔ Φ.symm y ∈ Ω
    simpa only [Φ.right_inv hyT] using h.symm
  obtain ⟨G, hG⟩ := exists_localized_chart_pullback (Ω := upper i) (p := p)
    Ω Ψ (hΨ.of_le (by norm_num)) (hΨinv.of_le (by norm_num))
    B hB0 hB J hJ1 hJ hTarget hsideΨ χ hχΨ
  obtain ⟨Cθ, hCθ0, hCθ, hDθ⟩ := ambient_test_bounds θ
  let M := ambientMultiply (Ω := Ω) (p := p) θ θ.contDiff Cθ hCθ0 hCθ hDθ
  refine ⟨G.comp M, ?_⟩
  intro u f hf
  have hM : (M u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun x => θ x * f x := by
    filter_upwards [ambientMultiply_coe θ θ.contDiff Cθ hCθ0 hCθ hDθ u, hf] with x hx hux
    exact hx.trans (congrArg (θ x * ·) hux)
  simpa only [ContinuousLinearMap.comp_apply, hfun] using hG (M u) (fun x => θ x * f x) hM



open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound
open SecondTraceFlat
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- Full flat two-jet boundedness in every boundary dimension. Tangential
trace differentiation is proved in the actual weak derivative graph. -/
theorem flat_jet_fractional_bound (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (i : Fin (n + 1))
      (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
        Lp 𝕜 p (volume : Measure (Transverse i))), CoordinateTraceCondition i T →
      ∀ u : SpaceValue 𝕜 (n + 1) (upper i) 2 p,
        ∃ (g : HigherFractionalSpace 𝕜 n (2 - 1 / p.toReal) p)
          (h : FractionalSpace 𝕜 n (1 - 1 / p.toReal) p),
          HasBoundaryJets i T u (wholeLp (g.val.val (zeroIndex n 1))) h.val ∧
          (∀ j : Fin n, wholeLp (g.val.val (firstIndex j)) =
            reindexedTrace i T (derivativePart (i.succAbove j) u)) ∧
          higherFractionalNorm (2 - 1 / p.toReal) p g +
            fractionalNorm (1 - 1 / p.toReal) p h ≤ C * ‖u‖ := by
  obtain ⟨C, hC, hbound⟩ := flat_jet_fractional_bound_of_graph n p hp1 hp
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ i T hT u
  obtain ⟨v, hv0, hvj⟩ := coordinate_trace_first_order_graph i hp T hT u
  obtain ⟨g, h, hgv, hh, hb⟩ := hbound 𝕜 i T hT u v hv0 hvj
  have hg0 : wholeLp (g.val.val (zeroIndex n 1)) = reindexedTrace i T (orderOnePart u) := by
    rw [hgv]
    exact hv0
  refine ⟨g, h, ?_, ?_, hb⟩
  · exact ⟨orderOnePart u, derivativePart i u, by simp, by simp, hg0.symm, hh.symm⟩
  · intro j
    rw [hgv]
    exact hvj j



open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace

lemma positive_functional_multiple {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A B : E →ₗ[ℝ] ℝ) (hA : A ≠ 0) (hB : B ≠ 0)
    (h : ∀ v, 0 < A v → 0 ≤ B v) :
    ∃ c : ℝ, 0 < c ∧ B = c • A := by
  have hex : ∃ v, A v ≠ 0 := by
    by_contra! hz
    apply hA
    ext v
    exact hz v
  obtain ⟨v, hv⟩ := hex
  let w : E := (A v)⁻¹ • v
  have hw : A w = 1 := by simp [w, hv]
  have hker : ∀ k, A k = 0 → B k = 0 := by
    intro k hk
    by_contra hBk
    have hpos : 0 < A (w + (-(B w + 1) / B k) • k) := by simp [hk, hw]
    have hn := h _ hpos
    simp only [map_add, map_smul, smul_eq_mul] at hn
    rw [div_mul_cancel₀ _ hBk] at hn
    linarith
  have hrepr : B = (B w) • A := by
    ext z
    have hz := hker (z - (A z) • w) (by simp [hw])
    simp only [map_sub, map_smul, smul_eq_mul] at hz
    change B z = B w * A z
    nlinarith
  have hc : 0 < B w := by
    have hc0 : 0 ≤ B w := h w (by rw [hw]; norm_num)
    apply lt_of_le_of_ne hc0
    intro hz
    apply hB
    simpa [← hz] using hrepr
  exact ⟨B w, hc, hrepr⟩

/-- Local agreement of negative sides forces the corresponding derivative
half-spaces to have the same orientation. -/
lemma derivative_nonneg_of_same_negative_side {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ) (A B : E →L[ℝ] ℝ) (x : E)
    (hf : HasFDerivAt f A x) (hg : HasFDerivAt g B x)
    (hfx : f x = 0) (hgx : g x = 0)
    (hside : ∀ᶠ y in 𝓝 x, f y < 0 ↔ g y < 0)
    (v : E) (hv : 0 < A v) : 0 ≤ B v := by
  have hfs : Tendsto (fun t : ℝ => t⁻¹ * (f (x + t • v) - f x))
      (𝓝[>] 0) (𝓝 (A v)) := by
    simpa only [smul_eq_mul] using
      (hf.hasLineDerivAt v).tendsto_slope_zero.mono_left (nhdsGT_le_nhdsNE 0)
  have hgs : Tendsto (fun t : ℝ => t⁻¹ * (g (x + t • v) - g x))
      (𝓝[>] 0) (𝓝 (B v)) := by
    simpa only [smul_eq_mul] using
      (hg.hasLineDerivAt v).tendsto_slope_zero.mono_left (nhdsGT_le_nhdsNE 0)
  have hcurve : Tendsto (fun t : ℝ => x + t • v) (𝓝[>] 0) (𝓝 x) := by
    have hc : ContinuousAt (fun t : ℝ => x + t • v) 0 := by fun_prop
    simpa only [zero_smul, add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hpositive := hfs.eventually (isOpen_Ioi.mem_nhds hv)
  have hn : ∀ᶠ t : ℝ in 𝓝[>] 0,
      0 ≤ t⁻¹ * (g (x + t • v) - g x) := by
    filter_upwards [hpositive, hcurve.eventually hside, self_mem_nhdsWithin]
      with t ht hs ht0
    have htpos : 0 < t := ht0
    rw [hfx, sub_zero] at ht
    have hfpos : 0 < f (x + t • v) :=
      pos_of_mul_pos_right ht (inv_nonneg.mpr htpos.le)
    have hgpos : 0 ≤ g (x + t • v) := by
      by_contra hh
      have hfneg := hs.mpr (lt_of_not_ge hh)
      linarith
    rw [hgx, sub_zero]
    exact mul_nonneg (inv_nonneg.mpr htpos.le) hgpos
  exact ge_of_tendsto hgs hn

lemma defining_derivatives_positive_multiple {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ) (A B : E →L[ℝ] ℝ) (x : E)
    (hf : HasFDerivAt f A x) (hg : HasFDerivAt g B x)
    (hfx : f x = 0) (hgx : g x = 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hside : ∀ᶠ y in 𝓝 x, f y < 0 ↔ g y < 0) :
    ∃ c : ℝ, 0 < c ∧ B = c • A := by
  have hA' : A.toLinearMap ≠ 0 := by
    intro hz; apply hA; ext v; exact congrArg (fun L : E →ₗ[ℝ] ℝ => L v) hz
  have hB' : B.toLinearMap ≠ 0 := by
    intro hz; apply hB; ext v; exact congrArg (fun L : E →ₗ[ℝ] ℝ => L v) hz
  obtain ⟨c, hc, heq⟩ := positive_functional_multiple A.toLinearMap B.toLinearMap hA' hB'
    (derivative_nonneg_of_same_negative_side f g A B x hf hg hfx hgx hside)
  refine ⟨c, hc, ?_⟩
  ext v
  exact congrArg (fun L : E →ₗ[ℝ] ℝ => L v) heq

lemma normalized_components_eq_of_positive_multiple {d : ℕ}
    (a b : Domain d) (c : ℝ) (hc : 0 < c) (hab : ∀ j, b j = c * a j) (j : Fin d) :
    b j / Real.sqrt (∑ k : Fin d, (b k) ^ 2) =
      a j / Real.sqrt (∑ k : Fin d, (a k) ^ 2) := by
  have hs : (∑ k : Fin d, (b k) ^ 2) = c ^ 2 * ∑ k : Fin d, (a k) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hab k]
    ring
  rw [hs, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_pos hc, hab j]
  exact mul_div_mul_left _ _ hc.ne'

/-- A geometric normal is forced to be the normalized gradient of every
oriented chart defining function. -/
lemma geometricNormal_eq_chart {d : ℕ} (Ω : Opens (Domain d))
    (ν : Domain d → Domain d) (hν : GeometricNormal Ω ν)
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    (x : Domain d) (hx : x ∈ frontier (Ω : Set (Domain d))) (hxΦ : x ∈ Φ.source)
    (j : Fin d) :
    ν x j = fderiv ℝ (fun y => -Φ y i) x (coordinateVector j) /
      Real.sqrt (∑ k : Fin d,
        (fderiv ℝ (fun y => -Φ y i) x (coordinateVector k)) ^ 2) := by
  obtain ⟨U, r, hU, hxU, hr, hrx, hrside, hrn, hνr⟩ := hν.2.2 x hx
  let q : Domain d → ℝ := fun y => -Φ y i
  obtain ⟨hq, hqside, hqn⟩ := chart_defining_function Ω Φ i hΦ hInv hside x hxΦ
  have hqx : q x = 0 := by
    have hz := (ExpandedFA.Sobolev.Trace.chart_boundary_iff Ω Φ i hside x hxΦ).mp hx
    simp [q, hz]
  have hqd : DifferentiableAt ℝ q x :=
    ((hq.of_le (by norm_num)).differentiableOn_one x hxΦ).differentiableAt
      (Φ.open_source.mem_nhds hxΦ)
  have hrd : DifferentiableAt ℝ r x :=
    ((hr.of_le (by norm_num)).differentiableOn_one x hxU).differentiableAt (hU.mem_nhds hxU)
  have hA : fderiv ℝ q x ≠ 0 := by
    intro hz
    apply hqn
    simp only [q] at hz
    simp [hz]
  have hB : fderiv ℝ r x ≠ 0 := by
    intro hz
    apply hrn
    simp [hz]
  have hsides : ∀ᶠ y in 𝓝 x, q y < 0 ↔ r y < 0 := by
    have hΦevent : ∀ᶠ y in 𝓝 x, y ∈ Φ.source := Φ.open_source.mem_nhds hxΦ
    have hUevent : ∀ᶠ y in 𝓝 x, y ∈ U := hU.mem_nhds hxU
    filter_upwards [hΦevent, hUevent] with y hyΦ hyU
    exact (hqside y hyΦ).symm.trans (hrside y hyU)
  obtain ⟨c, hc, hcr⟩ := defining_derivatives_positive_multiple q r _ _ x
    hqd.hasFDerivAt hrd.hasFDerivAt hqx hrx hA hB hsides
  rw [hνr j]
  apply normalized_components_eq_of_positive_multiple
    (fun k => fderiv ℝ q x (coordinateVector k))
    (fun k => fderiv ℝ r x (coordinateVector k)) c hc
  intro k
  have heq := congrArg (fun A : Domain d →L[ℝ] ℝ => A (coordinateVector k)) hcr
  simpa only [smul_apply, smul_eq_mul] using heq

namespace C2BoundaryModel

/-- Every geometric normal component has a compact C¹ coefficient in each
faithful C² chart, agreeing wherever its localized piece can be nonzero. -/
lemma exists_compact_chart_normal_coefficient {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    {Ω : Opens (Domain (n + 1))} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    [CompactSpace (frontier (Ω : Set (Domain (n + 1))))]
    (B : C2BoundaryModel 𝕜 Ω p) (ν : Domain (n + 1) → Domain (n + 1))
    (hν : GeometricNormal Ω ν) (k : Fin B.chartCount) (j : Fin (n + 1)) :
    ∃ a : Domain n → 𝕜, ContDiff ℝ 1 a ∧ HasCompactSupport a ∧
      tsupport a ⊆ (B.atlas.chart k).target ∧
      (∀ x ∈ (B.atlas.chart k).source, B.atlas.cutoff k x ≠ 0 →
        a (B.atlas.chart k x) = (ν x.val j : 𝕜)) ∧
      ∃ M L : ℝ≥0, (∀ x, ‖a x‖ ≤ M) ∧
        ∀ x y, ‖a x - a y‖ ≤ L *
          ExpandedFA.PartIV.FractionalSobolev.euclideanLength (x - y) := by
  let Φ := B.ambient k
  let i := B.normal k
  let r : Domain (n + 1) → ℝ := fun y => -Φ y i
  let f : Domain (n + 1) → ℝ := fun y => fderiv ℝ r y (coordinateVector j) /
    Real.sqrt (∑ l : Fin (n + 1), (fderiv ℝ r y (coordinateVector l)) ^ 2)
  let a0 : Domain n → 𝕜 := fun z => (f ((B.atlas.chart k).symm z).val : 𝕜)
  have hr : ContDiffOn ℝ 2 r Φ.source :=
    ((contDiffOn_pi.mp (B.regular k).1) i).neg
  have hn : ∀ y ∈ Φ.source,
      (∑ l : Fin (n + 1), (fderiv ℝ r y (coordinateVector l)) ^ 2) ≠ 0 := by
    intro y hy
    exact (chart_defining_function Ω Φ i (B.regular k).1 (B.regular k).2
      (B.side k) y hy).2.2
  have hf : ContDiffOn ℝ 1 f Φ.source :=
    normalized_gradient_component_contDiffOn Φ.source Φ.open_source r hr hn j
  have hmaps : MapsTo (fun z => ((B.atlas.chart k).symm z).val)
      (B.atlas.chart k).target Φ.source := by
    intro z hz
    have hx := (B.atlas.chart k).map_target hz
    simpa only [B.chart_source k, mem_preimage] using hx
  have ha0 : ContDiffOn ℝ 1 a0 (B.atlas.chart k).target :=
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp_contDiffOn
      (hf.comp ((B.chart_symm_contDiff k).of_le (by norm_num)) hmaps)
  let K := (B.atlas.chart k) '' tsupport (B.atlas.cutoff k)
  obtain ⟨a, ha, hac, hasub, V, _, hKV, hVa⟩ :=
    exists_compact_contDiff_extension 1 (B.atlas.chart k).target
      (B.atlas.chart k).open_target K (B.atlas.cutoffImage_isCompact k)
      (B.atlas.cutoffImage_subset_target k) a0 ha0
  refine ⟨a, ha, hac, hasub, ?_, compact_c1_coefficient_bounds a ha hac⟩
  intro x hx hcut
  have hxK : B.atlas.chart k x ∈ K := ⟨x, subset_tsupport _ hcut, rfl⟩
  rw [hVa (hKV hxK)]
  change (f ((B.atlas.chart k).symm (B.atlas.chart k x)).val : 𝕜) = _
  rw [(B.atlas.chart k).left_inv hx]
  congr 1
  exact (geometricNormal_eq_chart Ω ν hν Φ i (B.regular k).1 (B.regular k).2
    (B.side k) x.val x.property (by
      simpa only [B.chart_source k, mem_preimage] using hx) j).symm

end C2BoundaryModel



open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTrace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma normalComponent_localizedLp (B : BoundaryModel 𝕜 Ω p)
    (ν : Domain d → Domain d) (hν : GeometricNormal Ω ν)
    (j : Fin d) (k : Fin B.chartCount)
    (a : Domain (d - 1) → 𝕜) (M L : ℝ≥0)
    (hM : ∀ x, ‖a x‖ ≤ M)
    (hL : ∀ x y, ‖a x - a y‖ ≤ L * euclideanLength (x - y))
    (ha : ∀ x ∈ (B.atlas.chart k).source, B.atlas.cutoff k x ≠ 0 →
      a (B.atlas.chart k x) = (ν x.val j : 𝕜)) (g : BoundaryLp 𝕜 Ω p) :
    B.atlas.localizedLp p k (B.identify (normalComponent ν hν j g)) =
      lpMultiply p a M L hM hL (B.atlas.localizedLp p k (B.identify g)) := by
  have hgn := B.representative (normalComponent ν hν j g)
    (fun x => ν x j • g x) (normalComponent_coe ν hν j g)
  have hgg := B.representative g g Filter.EventuallyEq.rfl
  have h₁ := (B.atlas.localizedLp_representative p k (B.identify (normalComponent ν hν j g))).trans
    (B.atlas.localizedRepresentative_congr_ae k hgn)
  have h₂ := (B.atlas.localizedLp_representative p k (B.identify g)).trans
    (B.atlas.localizedRepresentative_congr_ae k hgg)
  apply Lp.ext
  filter_upwards [h₁, h₂, lpMultiply_representative p a M L hM hL
    (B.atlas.localizedLp p k (B.identify g))] with z hz₁ hz₂ hz₃
  rw [hz₁, hz₃, hz₂]
  by_cases hz : z ∈ (B.atlas.chart k).target
  · simp only [Boundary.FiniteAtlas.localizedRepresentative, indicator_of_mem hz]
    by_cases hc : B.atlas.cutoff k ((B.atlas.chart k).symm z) = 0
    · simp [hc]
    · have he := ha ((B.atlas.chart k).symm z) ((B.atlas.chart k).map_target hz) hc
      rw [(B.atlas.chart k).right_inv hz] at he
      rw [he, Algebra.smul_def]
      ring
  · simp only [Boundary.FiniteAtlas.localizedRepresentative, indicator_of_notMem hz, mul_zero]


/-- Local bounded Lipschitz coefficient representatives give a full atlas
fractional bound for one geometric normal component. -/
lemma normalComponent_fractional_bound_of_coefficients (B : BoundaryModel 𝕜 Ω p)
    (ν : Domain d → Domain d) (hν : GeometricNormal Ω ν) (j : Fin d)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (hcoeff : ∀ k : Fin B.chartCount, ∃ (a : Domain (d - 1) → 𝕜) (M L : ℝ≥0),
      (∀ x, ‖a x‖ ≤ M) ∧
      (∀ x y, ‖a x - a y‖ ≤ L * euclideanLength (x - y)) ∧
      ∀ x ∈ (B.atlas.chart k).source, B.atlas.cutoff k x ≠ 0 →
        a (B.atlas.chart k x) = (ν x.val j : 𝕜)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : B.Data s,
      ∃ h : B.Data s, h.val = normalComponent ν hν j g.val ∧
        B.dataNorm s h ≤ C * B.dataNorm s g := by
  choose a M L hM hL ha using hcoeff
  let A : Fin B.chartCount → ℝ := fun k => multiplierBound (d := d - 1) s p (M k) (L k)
  have hA (k : Fin B.chartCount) : 0 ≤ A k := multiplierBound_nonneg s p (M k) (L k)
  refine ⟨∑ k, A k, Finset.sum_nonneg (fun k _ => hA k), ?_⟩
  intro g
  let w (k : Fin B.chartCount) := fractionalMultiply s p hs0 hs1 hp (a k) (M k) (L k)
    (hM k) (hL k) ⟨B.atlas.localizedLp p k (B.identify g.val), g.property k⟩
  have hw (k : Fin B.chartCount) :
      B.atlas.localizedLp p k (B.identify (normalComponent ν hν j g.val)) = (w k).val :=
    normalComponent_localizedLp B ν hν j k (a k) (M k) (L k) (hM k) (hL k) (ha k) g.val
  have hm : B.FiniteEnergy s (normalComponent ν hν j g.val) := by
    intro k
    rw [hw k]
    exact (w k).property
  let h : B.Data s := ⟨normalComponent ν hν j g.val, hm⟩
  refine ⟨h, rfl, ?_⟩
  change (∑ k, fractionalNorm s p
    ⟨B.atlas.localizedLp p k (B.identify (normalComponent ν hν j g.val)), hm k⟩) ≤
      (∑ k, A k) * ∑ k, fractionalNorm s p
        ⟨B.atlas.localizedLp p k (B.identify g.val), g.property k⟩
  calc
    _ = ∑ k, fractionalNorm s p (w k) := by
      apply Finset.sum_congr rfl
      intro k _
      exact congrArg (fractionalNorm s p) (Subtype.ext (hw k))
    _ ≤ ∑ k, A k * fractionalNorm s p
        ⟨B.atlas.localizedLp p k (B.identify g.val), g.property k⟩ := by
      apply Finset.sum_le_sum
      intro k _
      exact fractionalMultiply_norm_le s p hs0 hs1 hp (a k) (M k) (L k) (hM k) (hL k) _
    _ ≤ ∑ k, (∑ l, A l) * fractionalNorm s p
        ⟨B.atlas.localizedLp p k (B.identify g.val), g.property k⟩ := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun l _ => hA l) (Finset.mem_univ k))
        (fractionalNorm_nonneg _ _ _)
    _ = _ := (Finset.mul_sum _ _ _).symm



open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.Sobolev.C1Extension ExpandedFA.Sobolev.C1Extension.Transport
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.PartIV.SharpTrace
open ExpandedFA.PartIV.SharpTraceBound
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open SecondTraceFlat ExpandedFA.PartIV.FractionalSobolev ExpandedFA.Sobolev.Lines

namespace C2BoundaryModel
variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {Ω : Opens (Domain (n+1))}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : C2BoundaryModel 𝕜 Ω p)

lemma insert_mem_target_iff (j : Fin B.chartCount) (z : Domain n) :
    (B.normal j).insertNth 0 z ∈ (B.ambient j).target ↔ z ∈ (B.atlas.chart j).target := by
  constructor
  · intro hz
    let x := (B.ambient j).symm ((B.normal j).insertNth 0 z)
    have hxA : x ∈ (B.ambient j).source := (B.ambient j).map_target hz
    have hxF : x ∈ frontier (Ω : Set (Domain (n+1))) := by
      apply (chart_boundary_iff Ω (B.ambient j) (B.normal j) (B.side j) x hxA).mpr
      dsimp only [x]
      rw [(B.ambient j).right_inv hz]
      simp
    let xb : frontier (Ω : Set (Domain (n+1))) := ⟨x, hxF⟩
    have hxb : xb ∈ (B.atlas.chart j).source := by
      rw [B.chart_source j]
      exact hxA
    have hcoord : (B.atlas.chart j) xb = z := by
      rw [B.chart_apply j xb hxb]
      change (B.normal j).removeNth (B.ambient j x) = z
      dsimp only [x]
      rw [(B.ambient j).right_inv hz, Fin.removeNth_insertNth]
    rw [← hcoord]
    exact (B.atlas.chart j).map_source hxb
  · exact B.insert_chart_mem j z

/-- The actual boundary chart target is exactly the set of flattened
parameters whose normal-coordinate insertion lies in the ambient target. -/
lemma chart_target_eq_boundaryParameters (j : Fin B.chartCount) :
    (B.atlas.chart j).target = boundaryParameters (B.ambient j) (B.normal j) := by
  ext z
  exact (insert_mem_target_iff B j z).symm

lemma localizedRepresentative_eq_flattened (j : Fin B.chartCount)
    (θ χ : Tests 𝕜 (⊤ : Opens (Domain (n+1))))
    (hχ : tsupport χ ⊆ (B.ambient j).target)
    (hχone : ∀ x ∈ tsupport θ, χ (B.ambient j x) = 1)
    (hcutoff : ∀ x : frontier (Ω : Set (Domain (n+1))),
      (B.atlas.cutoff j x : 𝕜) = θ x.val)
    (f : Domain (n+1) → 𝕜) :
    B.atlas.localizedRepresentative j (fun x => f x.val) =
      fun z => χ ((B.normal j).insertNth 0 z) *
        (θ ((B.ambient j).symm ((B.normal j).insertNth 0 z)) *
          f ((B.ambient j).symm ((B.normal j).insertNth 0 z))) := by
  classical
  funext z
  unfold Boundary.FiniteAtlas.localizedRepresentative
  by_cases hz : z ∈ (B.atlas.chart j).target
  · rw [indicator_of_mem hz, hcutoff, B.chart_symm_val j z hz]
    by_cases hθz : θ ((B.ambient j).symm ((B.normal j).insertNth 0 z)) = 0
    · simp only [hθz, zero_mul, mul_zero]
    · have hχz := hχone _ (subset_tsupport θ hθz)
      rw [(B.ambient j).right_inv (B.insert_chart_mem j z hz)] at hχz
      rw [hχz, one_mul]
      change θ _ * f (((B.atlas.chart j).symm z).val) = _
      rw [B.chart_symm_val j z hz]
  · rw [indicator_of_notMem hz]
    have hχz : (B.normal j).insertNth (α := fun _ => ℝ) 0 z ∉ tsupport χ := by
      intro hs
      exact hz ((insert_mem_target_iff B j z).mp (hχ hs))
    rw [image_eq_zero_of_notMem_tsupport hχz, zero_mul]

/-- Smooth boundary agreement for every faithful C² model; only the given
chart restrictions and original surface quotient are used. -/
lemma flattened_trace_smooth_eq_localized (j : Fin B.chartCount)
    (θ χ : Tests 𝕜 (⊤ : Opens (Domain (n+1))))
    (hχ : tsupport χ ⊆ (B.ambient j).target)
    (hχone : ∀ x ∈ tsupport θ, χ (B.ambient j x) = 1)
    (hcutoff : ∀ x : frontier (Ω : Set (Domain (n+1))),
      (B.atlas.cutoff j x : 𝕜) = θ x.val)
    (E : SpaceValue 𝕜 (n+1) Ω 1 p →L[𝕜]
      SpaceValue 𝕜 (n+1) (upper (B.normal j)) 1 p)
    (hE : ∀ (u : SpaceValue 𝕜 (n+1) Ω 1 p) (f : Domain (n+1) → 𝕜),
      u.val (zeroIndex (n+1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (n+1)))] f →
      (E u).val (zeroIndex (n+1) 1) =ᵐ[
        volume.restrict (upper (B.normal j) : Set (Domain (n+1)))]
        fun y => χ y * (θ ((B.ambient j).symm y) * f ((B.ambient j).symm y)))
    (S : SpaceValue 𝕜 (n+1) (upper (B.normal j)) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse (B.normal j))))
    (hS : IsCoordinateTrace (B.normal j) S)
    (u : SpaceValue 𝕜 (n+1) Ω 1 p) (f : Domain (n+1) → 𝕜)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hu : u.val (zeroIndex (n+1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (n+1)))] f) :
    reindexedTrace (B.normal j) S (E u) =ᵐ[volume]
      B.atlas.localizedRepresentative j (fun x => f x.val) := by
  have hg : ContDiff ℝ 1 (fun y => χ y *
      (θ ((B.ambient j).symm y) * f ((B.ambient j).symm y))) :=
    contDiff_chart_cutoff_comp (B.ambient j) ((B.regular j).2.of_le (by norm_num))
      χ hχ (fun x => θ x * f x) ((θ.contDiff.mul hf).of_le (by simp))
  have ht := reindexedTrace_smooth (B.normal j) S hS (E u) _ hg (hE u f hu)
  rw [localizedRepresentative_eq_flattened B j θ χ hχ hχone hcutoff f]
  exact ht

end C2BoundaryModel


open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTrace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- Every component of the geometric unit normal acts boundedly on every
order between zero and one of the original finite-atlas boundary space. -/
lemma normalComponent_fractional_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hb : Bornology.IsBounded (Ω : Set (Domain d)))
    (B : C2BoundaryModel 𝕜 Ω p) (ν : Domain d → Domain d)
    (hν : GeometricNormal Ω ν) (j : Fin d)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : B.toBoundaryModel.Data s,
      ∃ h : B.toBoundaryModel.Data s, h.val = normalComponent ν hν j g.val ∧
        B.toBoundaryModel.dataNorm s h ≤ C * B.toBoundaryModel.dataNorm s g := by
  cases d with
  | zero => exact Fin.elim0 j
  | succ n =>
    have hc : IsCompact (frontier (Ω : Set (Domain (n + 1)))) :=
      hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
    letI : CompactSpace (frontier (Ω : Set (Domain (n + 1)))) := isCompact_iff_compactSpace.mp hc
    apply normalComponent_fractional_bound_of_coefficients B.toBoundaryModel ν hν j s hs0 hs1 hp
    intro k
    obtain ⟨a, _, _, _, ha, M, L, hM, hL⟩ :=
      C2BoundaryModel.exists_compact_chart_normal_coefficient B ν hν k j
    exact ⟨a, M, L, hM, hL, ha⟩


end ExpandedFA.PartIV.SecondTraceBound

namespace ExpandedFA.PartIV.SecondTraceBound.BoundaryModel
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTrace
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Finite sums of surface data remain in the same actual atlas space, and
obey the triangle bound for the full atlas norm. -/
lemma data_sum {ι : Type*} [Fintype ι] (B : BoundaryModel 𝕜 Ω p)
    (s : ℝ) (hp : p ≠ ∞) (g : ι → B.Data s) :
    ∃ h : B.Data s, h.val = ∑ j, (g j).val ∧
      B.dataNorm s h ≤ ∑ j, B.dataNorm s (g j) := by
  classical
  letI : Fact (p ≠ ∞) := ⟨hp⟩
  let f : ι → B.atlas.FractionalSpace 𝕜 s p :=
    fun j => ⟨B.identify (g j).val, (g j).property⟩
  have hmem : B.FiniteEnergy s (∑ j, (g j).val) := by
    change B.identify (∑ j, (g j).val) ∈ B.atlas.finiteEnergySubmodule s p hp
    rw [map_sum]
    exact Submodule.sum_mem _ (fun j _ => (g j).property)
  let h : B.Data s := ⟨∑ j, (g j).val, hmem⟩
  refine ⟨h, rfl, ?_⟩
  have he : (⟨B.identify h.val, h.property⟩ : B.atlas.FractionalSpace 𝕜 s p) =
      ∑ j, f j := by
    apply Subtype.ext
    change B.identify (∑ j, (g j).val) = (∑ j, f j).val
    rw [map_sum]
    exact (map_sum (B.atlas.finiteEnergySubmodule s p hp).subtype f Finset.univ).symm
  change B.atlas.fractionalNorm s p ⟨B.identify h.val, h.property⟩ ≤ _
  rw [he]
  change ‖∑ j, f j‖ ≤ ∑ j, ‖f j‖
  exact norm_sum_le Finset.univ f
end ExpandedFA.PartIV.SecondTraceBound.BoundaryModel

namespace ExpandedFA.PartIV.SecondTraceBound
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.Sobolev.C1Extension ExpandedFA.Sobolev.C1Extension.Transport
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.PartIV.SharpTrace ExpandedFA.PartIV.SharpTraceBound ExpandedFA.PartIV.FractionalSobolev
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open SecondTraceFlat SecondTraceTransport
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
/-- Full higher fractional bound for the value trace in every faithful C²
model, obtained from genuine flattened W²,p graphs. -/
theorem higher_value_trace_bound
    (hΩb : Bornology.IsBounded (Ω : Set (Domain d))) (hΩ : IsC2Domain Ω)
    (hp1 : 1 < p) (hp : p ≠ ∞) (B : C2BoundaryModel 𝕜 Ω p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
      ∀ u : SpaceValue 𝕜 d Ω 2 p,
        ∃ g : B.HigherData (2 - 1 / p.toReal), g.val = T (orderOnePart u) ∧
          B.higherDataNorm (2 - 1 / p.toReal) g ≤ C * ‖u‖ := by
  cases d with
  | zero =>
    have hμ := surfaceMeasure_zero_dimension Ω
    refine ⟨0, le_rfl, ?_⟩
    intro T _ u
    let g : B.HigherData (2 - 1 / p.toReal) :=
      ⟨T (orderOnePart u), higherEnergy_of_surfaceMeasure_zero hμ hp B _ _⟩
    exact ⟨g, rfl, by rw [higherDataNorm_of_surfaceMeasure_zero hμ hp B]; simp⟩
  | succ n =>
    have hc : IsCompact (frontier (Ω : Set (Domain (n+1)))) :=
      hΩb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
    have hdense := C1Extension.smooth_density 𝕜 (n+1) Ω (isC1Domain_of_isC2Domain hΩ) hc p hp
    obtain ⟨C, hC, hflat⟩ := flat_jet_fractional_bound n p hp1 hp
    apply higher_trace_bound_of_chart_estimates B (2 - 1 / p.toReal)
    intro j
    let θ := scalarTest (𝕜 := 𝕜) (B.test j)
    have hθ : tsupport θ ⊆ (B.ambient j).source :=
      (tsupport_scalarTest (B.test j)).trans (B.test_subordinate j)
    obtain ⟨χ, hχ, hχone⟩ := exists_chart_cutoff (B.ambient j) θ hθ
    obtain ⟨E₁, hE₁⟩ := exists_flattened_one_localization (p := p) (B.normal j) (B.ambient j)
      (B.regular j).1 (B.regular j).2 (B.side j) θ χ hχ
    obtain ⟨E₂, hE₂⟩ := exists_flattened_two_localization hp1 hp (B.normal j) (B.ambient j)
      (B.regular j).1 (B.regular j).2 (B.side j) θ χ hχ
    obtain ⟨S, hS, _⟩ := coordinate_upper_trace_exists (𝕜 := 𝕜) (B.normal j) hp
    have hcutoff : ∀ x : frontier (Ω : Set (Domain (n+1))),
        (B.atlas.cutoff j x : 𝕜) = θ x.val := by
      intro x
      change (B.atlas.cutoff j x : 𝕜) = (B.test j x.val : 𝕜)
      exact congrArg (fun r : ℝ => (r : 𝕜)) (B.cutoff_eq j x)
    refine ⟨C * ‖E₂‖, mul_nonneg hC E₂.opNorm_nonneg, ?_⟩
    intro T hT u
    have heq := localized_trace_eq_of_smooth B.toBoundaryModel hdense j (B.normal j) E₁ S T hT
      (fun v f hf hv => C2BoundaryModel.flattened_trace_smooth_eq_localized B j θ χ hχ hχone hcutoff
        E₁ hE₁ S hS v f hf hv) (orderOnePart u)
    have horder := flattened_two_orderOnePart (B.normal j) (B.ambient j) θ χ E₁ E₂ hE₁ hE₂ u
    rw [← horder] at heq
    obtain ⟨g, h, hjets, _, hbound⟩ := hflat 𝕜 (B.normal j) S hS (E₂ u)
    refine ⟨g, ?_, ?_⟩
    · exact ((hasBoundaryJets_iff (B.normal j) S (E₂ u) _ _).mp hjets).1.symm.trans heq.symm
    · have hg0 := fractionalNorm_nonneg (1 - 1 / p.toReal) p h
      have hg := (le_add_of_nonneg_right hg0).trans hbound
      exact hg.trans (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (E₂.le_opNorm u) hC)

end ExpandedFA.PartIV.SecondTraceBound

namespace ExpandedFA.PartIV.SecondTraceBound
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTrace
open ExpandedFA.PartIV.SharpTraceBound SecondTraceFlat
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- Full sharp fractional regularity and a uniform bound for the normal jet,
assembled in the original surface Lp quotient from the actual weak derivatives. -/
lemma normal_trace_fractional_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hΩb : Bornology.IsBounded (Ω : Set (Domain d))) (hΩ : IsC2Domain Ω)
    (hp1 : 1 < p) (hp : p ≠ ∞) (B : C2BoundaryModel 𝕜 Ω p)
    (ν : Domain d → Domain d) (hν : GeometricNormal Ω ν) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
      ∀ u : SpaceValue 𝕜 d Ω 2 p,
        ∃ h : B.toBoundaryModel.Data (1 - 1 / p.toReal),
          h.val = normalTraceCLM ν hν T u ∧
            B.toBoundaryModel.dataNorm (1 - 1 / p.toReal) h ≤ C * ‖u‖ := by
  let s : ℝ := 1 - 1 / p.toReal
  have hs0 : 0 < s := (endpoint_exponent hp1 hp).1
  have hs1 : s < 1 := (endpoint_exponent hp1 hp).2
  obtain ⟨C, hC, hbound⟩ := domain_sharp_bound 𝕜 d Ω hΩb (isC1Domain_of_isC2Domain hΩ) p hp1 hp
    B.toBoundaryModel
  have hn (j : Fin d) := normalComponent_fractional_bound hΩb B ν hν j s hs0 hs1 hp
  choose D hD hnormal using hn
  let q : ℝ := Fintype.card (DerivativeIndex d 1)
  refine ⟨(∑ j, D j) * C * q, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (Finset.sum_nonneg (fun j _ => hD j)) hC)
      (by dsimp [q]; positivity)
  intro T hT u
  have hw (j : Fin d) := hbound T hT (derivativePart j u)
  choose E hE using hw
  let w : Fin d → B.toBoundaryModel.Data s := fun j => ⟨T (derivativePart j u), E j⟩
  have hh (j : Fin d) := hnormal j (w j)
  choose H hH hHb using hh
  obtain ⟨h, hv, hb⟩ := BoundaryModel.data_sum B.toBoundaryModel s hp H
  refine ⟨h, ?_, ?_⟩
  · calc
      h.val = ∑ j, (H j).val := hv
      _ = ∑ j : Fin d, normalComponent ν hν j (T (derivativePart j u)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact hH j
      _ = normalTraceCLM ν hν T u := by
        simp only [normalTraceCLM, _root_.sum_apply, ContinuousLinearMap.comp_apply]
        rfl
  · have hwbound (j : Fin d) : B.toBoundaryModel.dataNorm s (w j) ≤ C * (q * ‖u‖) :=
      (hE j).trans (mul_le_mul_of_nonneg_left (derivativePart_norm_le j u) hC)
    calc
      B.toBoundaryModel.dataNorm s h ≤ ∑ j, B.toBoundaryModel.dataNorm s (H j) := hb
      _ ≤ ∑ j, D j * B.toBoundaryModel.dataNorm s (w j) :=
        Finset.sum_le_sum (fun j _ => hHb j)
      _ ≤ ∑ j, D j * (C * (q * ‖u‖)) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hwbound j) (hD j))
      _ = ((∑ j, D j) * C * q) * ‖u‖ := by
        rw [← Finset.sum_mul]
        ring

/-- The full bounded two-jet trace theorem on every bounded C² domain,
with the original first trace and the geometric outward normal. -/
theorem bounded_trace : Specs.ExpandedFA.PartIV.SecondTraceBound.BoundedTrace := by
  intro 𝕜 _ d Ω hΩb hΩ p _ hp1 hp B ν hν
  obtain ⟨C, hC, hvalue⟩ := higher_value_trace_bound hΩb hΩ hp1 hp B
  obtain ⟨D, hD, hnormal⟩ := normal_trace_fractional_bound hΩb hΩ hp1 hp B ν hν
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  intro T hT u
  obtain ⟨g, hg, hgb⟩ := hvalue T hT u
  obtain ⟨h, hh, hhb⟩ := hnormal T hT u
  refine ⟨g, h, ?_, ?_⟩
  · rw [hg, hh]
    exact canonical_hasDomainJets ν hν T u
  · exact (add_le_add hgb hhb).trans_eq (add_mul C D ‖u‖).symm

end ExpandedFA.PartIV.SecondTraceBound

/-- The public bounded two-jet trace theorem; auxiliary declarations are
kept in this module's own namespace for compatibility with the other components. -/
theorem ExpandedFA.PartIV.SecondTrace.bounded_trace :
    Specs.ExpandedFA.PartIV.SecondTraceBound.BoundedTrace :=
  ExpandedFA.PartIV.SecondTraceBound.bounded_trace
