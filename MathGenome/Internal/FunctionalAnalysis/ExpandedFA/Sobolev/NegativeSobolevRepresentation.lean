import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.NegativeSobolevRepresentation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.PoincareInequality
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpDuality
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! Negative Sobolev representation, `fa2:p4:negative-sobolev`.
We use the original full-norm closure of compact tests. Hahn–Banach on the
finite sum-norm product and scalar-linear Lp duality give optimal coefficients.
For the derivative-only assertion, Poincaré bounds the inverse gradient map
on its range. No closed-range or boundary-regularity assumption is needed
for the extension argument, and empty domains remain included in all dimensions. -/

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal Distributions

namespace ExpandedFA.Sobolev.NegativeSobolev
open ExpandedFA.Distributions ExpandedFA.FunctionSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {hp : p ≠ ∞}

/-- First-order multi-indices are exactly zero and the coordinate indices. -/
theorem firstIndex_bijective (d : ℕ) :
    Function.Bijective (firstIndex (d := d)) := by
  classical
  constructor
  · intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some j =>
        have hh := congrArg (fun α : DerivativeIndex d 1 => α.val j) h
        simp [firstIndex, zeroIndex, coordinateIndex] at hh
    | some i =>
      cases b with
      | none =>
        have hh := congrArg (fun α : DerivativeIndex d 1 => α.val i) h
        simp [firstIndex, zeroIndex, coordinateIndex] at hh
      | some j =>
        congr 1
        by_contra hij
        have hh := congrArg (fun α : DerivativeIndex d 1 => α.val i) h
        simp [firstIndex, coordinateIndex, hij] at hh
  · intro α
    by_cases hz : ∀ i, α.val i = 0
    · refine ⟨none, ?_⟩
      apply Subtype.ext
      exact funext (fun i => (hz i).symm)
    · obtain ⟨i, hi⟩ := not_forall.mp hz
      have hi1 : (α.val i).val = 1 := by
        have := (α.val i).isLt
        have : (α.val i).val ≠ 0 := fun h => hi (Fin.ext h)
        omega
      have hrest : ∑ j ∈ Finset.univ.erase i, (α.val j).val = 0 := by
        have hs := Finset.add_sum_erase Finset.univ (fun j => (α.val j).val)
          (Finset.mem_univ i)
        have ha := α.property
        omega
      refine ⟨some i, ?_⟩
      apply Subtype.ext
      funext j
      apply Fin.ext
      by_cases hji : j = i
      · subst j
        simpa [firstIndex, coordinateIndex] using hi1.symm
      · have hj := Finset.single_le_sum (fun j _ => Nat.zero_le (α.val j).val)
          (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
        rw [hrest] at hj
        simpa [firstIndex, coordinateIndex, hji] using (Nat.eq_zero_of_le_zero hj).symm

def firstIndexEquiv (d : ℕ) : Option (Fin d) ≃ DerivativeIndex d 1 :=
  Equiv.ofBijective firstIndex (firstIndex_bijective d)

theorem full_norm : Specs.ExpandedFA.Sobolev.NegativeSobolevRepresentation.FullNorm := by
  intro 𝕜 _ d Ω p _ hp u
  change ‖u.val.val‖ = _
  rw [PiLp.norm_eq_of_L1, ← Equiv.sum_comp (firstIndexEquiv d)]
  exact Fintype.sum_option _

/-- The full jet preserves the norm already fixed by the Sobolev interface. -/
def firstJetIsometry : W0 𝕜 Ω p hp →ₗᵢ[𝕜] FirstProduct 𝕜 Ω p where
  toLinearMap := firstJet
  norm_map' u := by
    rw [PiLp.norm_eq_of_L1]
    change (∑ i : Option (Fin d), ‖u.val.val (firstIndex i)‖) = ‖u‖
    rw [Fintype.sum_option]
    exact (full_norm 𝕜 d Ω p hp u).symm

section FiniteProduct
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A coordinate inclusion into a finite sum-norm product. -/
def sumSingle (i : ι) : E →L[𝕜] PiLp 1 (fun _ : ι => E) :=
  LinearMap.mkContinuous
    { toFun := fun x : E => PiLp.single (β := fun _ : ι => E) 1 i x
      map_add' := fun x y => PiLp.single_add 1 i
      map_smul' := by intro c x; ext j; simp [PiLp.single_apply, PiLp.smul_apply] }
    1 (by intro x; simp [PiLp.norm_single])

/-- A finite sum-norm product's dual norm is the maximum coordinate-dual norm.
The formulation also works for an empty product. -/
theorem finite_product_duality (μ : Measure (Domain d)) [SigmaFinite μ]
    [ENNReal.HolderConjugate p q] (hp : p ≠ ∞)
    (L : PiLp 1 (fun _ : ι => Lp 𝕜 p μ) →L[𝕜] 𝕜) :
    ∃ f : ι → Lp 𝕜 q μ,
      (∀ v, L v = ∑ i, ∫ x, v i x * f i x ∂μ) ∧ ‖f‖ = ‖L‖ := by
  have hex (i : ι) := lp_duality_sigmaFinite μ p q hp (L.comp (sumSingle i))
  choose f hf using fun i => ExistsUnique.exists (hex i)
  have hcoord (i : ι) : ‖f i‖ = ‖L.comp (sumSingle i)‖ := (hf i).2
  have hrep (v : PiLp 1 (fun _ : ι => Lp 𝕜 p μ)) :
      L v = ∑ i, ∫ x, v i x * f i x ∂μ := by
    have hv : v = ∑ i, PiLp.single 1 i (v i) := by
      ext i
      simp
    calc
      L v = L (∑ i, PiLp.single 1 i (v i)) := congrArg L hv
      _ = ∑ i, L (PiLp.single 1 i (v i)) := map_sum L _ _
      _ = _ := Finset.sum_congr rfl (fun i _ => by simpa [sumSingle] using ((hf i).1 (v i)).2)
  refine ⟨f, hrep, le_antisymm ?_ ?_⟩
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg L)).mpr
    intro i
    rw [hcoord]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
    intro x
    simpa [sumSingle, PiLp.norm_single] using L.le_opNorm (PiLp.single 1 i x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
    intro v
    rw [hrep]
    calc
      ‖∑ i, ∫ x, v i x * f i x ∂μ‖ ≤ ∑ i, ‖∫ x, v i x * f i x ∂μ‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖f i‖ * ‖v i‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [← (lp_pairing_integral μ p q (f i) (v i)).2]
        exact lp_pairing_apply_bound μ p q (f i) (v i)
      _ ≤ ∑ i, ‖f‖ * ‖v i‖ := Finset.sum_le_sum
        (fun i _ => mul_le_mul_of_nonneg_right (norm_le_pi_norm f i) (norm_nonneg _))
      _ = ‖f‖ * ‖v‖ := by rw [← Finset.mul_sum, PiLp.norm_eq_of_L1]

end FiniteProduct

/-- Hahn–Banach along any isometric linear embedding, including zero spaces. -/
theorem extend_isometry {E V : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] (j : E →ₗᵢ[𝕜] V)
    (F : E →L[𝕜] 𝕜) : ∃ L : V →L[𝕜] 𝕜,
      (∀ u, L (j u) = F u) ∧ ‖L‖ = ‖F‖ := by
  let e := j.equivRange
  let H := F.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  obtain ⟨L, hL, hn⟩ := exists_extension_norm_eq (LinearMap.range j.toLinearMap) H
  refine ⟨L, ?_, hn.trans ?_⟩
  · intro u
    simpa [H, e] using hL (e u)
  · apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F)
      intro u
      simpa [H] using F.le_opNorm (e.symm u)
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg H)
      intro u
      simpa [H] using H.le_opNorm (e u)

theorem full_representation :
    Specs.ExpandedFA.Sobolev.NegativeSobolevRepresentation.FullRepresentation := by
  intro 𝕜 _ d Ω p q _ _ _ hp F
  -- Fix the normed structures before elaborating the nested subspace map.
  obtain ⟨L, hL, hn⟩ := @extend_isometry 𝕜 inferInstance
    (W0 𝕜 Ω p hp) (FirstProduct 𝕜 Ω p)
    inferInstance inferInstance inferInstance inferInstance
    (firstJetIsometry (𝕜 := 𝕜) (Ω := Ω) (p := p) (hp := hp)) F
  obtain ⟨f, hf, hfn⟩ := finite_product_duality (p := p) (q := q) (volume.restrict (Ω : Set (Domain d))) hp L
  refine ⟨f, ?_, ?_, hfn.trans hn⟩
  · intro u i
    exact (Lp.memLp _).integrable_mul (Lp.memLp _)
  · intro u
    rw [← hL u, hf]
    exact Fintype.sum_option _


/-- A compact test lies in the very full-norm closure used in the theorem. -/
theorem test_inclusion :
    Specs.ExpandedFA.Sobolev.NegativeSobolevRepresentation.TestInclusion := by
  intro 𝕜 _ d Ω p _ hp φ
  let v : SobolevSpace 𝕜 d Ω 1 p := testToSobolev (p := p) 1 φ
  have hv0 : v.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] φ := by
    rw [testToSobolev_underlying]
    exact testToDomainLp_coe φ
  have hv : v ∈ Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.smoothSubmodule 𝕜 d Ω 1 p :=
    ⟨φ, hv0⟩
  exact ⟨⟨v, Submodule.le_topologicalClosure _ hv⟩, hv0⟩

/-- The minus sign in distributional differentiation yields the plus sign
in the displayed integral representation. -/
theorem distribution_interpretation :
    Specs.ExpandedFA.Sobolev.NegativeSobolevRepresentation.DistributionInterpretation := by
  intro 𝕜 _ d Ω p q _ _ _ hp F f hF φ u hu
  have he : u.val = testToSobolev (p := p) 1 φ := by
    apply sobolev_underlying_injective 𝕜 d Ω 1 p
    change u.val.val (zeroIndex d 1) = (testToSobolev (p := p) 1 φ).val (zeroIndex d 1)
    rw [testToSobolev_underlying]
    exact Lp.ext (hu.trans (testToDomainLp_coe (p := p) φ).symm)
  rw [hF, Fintype.sum_option]
  simp only [firstIndex, coefficientDistribution, sub_apply,
    sum_apply,
    Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue,
    List.length_singleton, pow_one, smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, neg_one_mul, lpDistribution_apply]
  rw [Finset.sum_neg_distrib, sub_neg_eq_add]
  congr 1
  · apply integral_congr_ae
    filter_upwards [hu] with x hx
    rw [hx]
  · apply Finset.sum_congr rfl
    intro i _
    have hder : u.val.val (coordinateIndex i) =ᵐ[volume.restrict (Ω : Set (Domain d))]
        testPartialCLM [i] φ := by
      rw [he, testToSobolev_coordinate]
      exact testToDomainLp_coe _
    apply integral_congr_ae
    filter_upwards [hder] with x hx
    rw [hx]

@[simp] theorem gradientJet_norm (u : W0 𝕜 Ω p hp) :
    ‖gradientJet u‖ = ∑ i : Fin d, ‖u.val.val (coordinateIndex i)‖ :=
  PiLp.norm_eq_of_L1 _

theorem gradientJet_norm_le (u : W0 𝕜 Ω p hp) : ‖gradientJet u‖ ≤ ‖u‖ := by
  rw [gradientJet_norm, full_norm 𝕜 d Ω p hp u]
  exact le_add_of_nonneg_left (norm_nonneg _)

/-- Poincaré is used only on its actual positive-dimensional/empty scope.
A coordinate strip supplies a constant independent of p. -/
theorem full_norm_le_gradient (hΩ : Bornology.IsBounded (Ω : Set (Domain d)))
    (hdim : 0 < d ∨ (Ω : Set (Domain d)) = ∅) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
      (u : W0 𝕜 Ω p hp), ‖u‖ ≤ K * ‖gradientJet u‖ := by
  classical
  rcases hdim with hd | he
  · let i : Fin d := ⟨0, hd⟩
    obtain ⟨a, b, hab, hs⟩ := exists_coordinate_strip i
      (Bornology.IsBounded.image (ContinuousLinearMap.proj i : Domain d →L[ℝ] ℝ) hΩ)
    refine ⟨(b - a) + 1, by linarith, ?_⟩
    intro p _ hp u
    have hP := poincare_coordinate_strip 𝕜 d Ω i a b hab hs p hp u
    have hi : ‖u.val.val (coordinateIndex i)‖ ≤ ‖gradientJet u‖ :=
      PiLp.norm_apply_le (gradientJet u) i
    rw [full_norm 𝕜 d Ω p hp u, ← gradientJet_norm]
    calc
      ‖u.val.val (zeroIndex d 1)‖ + ‖gradientJet u‖ ≤
          (b - a) * ‖gradientJet u‖ + ‖gradientJet u‖ := by
        gcongr
        exact hP.trans (mul_le_mul_of_nonneg_left hi (sub_pos.mpr hab).le)
      _ = _ := by ring
  · refine ⟨1, le_rfl, ?_⟩
    intro p _ hp u
    rw [full_norm 𝕜 d Ω p hp u, poincare_empty 𝕜 d Ω he p hp u,
      zero_add, gradientJet_norm, one_mul]

theorem derivative_norm_equivalence :
    Specs.ExpandedFA.Sobolev.NegativeSobolevRepresentation.DerivativeNormEquivalence := by
  intro 𝕜 _ d Ω hΩ hdim
  obtain ⟨K, hK, hbound⟩ := full_norm_le_gradient (𝕜 := 𝕜) hΩ hdim
  refine ⟨K, hK, ?_⟩
  intro p _ hp
  refine ⟨?_, fun u => ⟨gradientJet_norm_le u, hbound p hp u⟩⟩
  intro u v huv
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  calc
    ‖u - v‖ ≤ K * ‖gradientJet (u - v)‖ := hbound p hp (u - v)
    _ = 0 := by rw [map_sub, huv, sub_self, norm_zero, mul_zero]

/-- Pulling back along the gradient range preserves exactly the same original
vectors. Its inverse is bounded by the established Poincaré estimate. -/
theorem functional_on_gradient (K : ℝ) (hK : 1 ≤ K)
    (hinj : Function.Injective (gradientJet (𝕜 := 𝕜) (Ω := Ω) (p := p) (hp := hp)))
    (hbound : ∀ u : W0 𝕜 Ω p hp, ‖u‖ ≤ K * ‖gradientJet u‖)
    (F : W0 𝕜 Ω p hp →L[𝕜] 𝕜) :
    ∃ G : GradientSpace 𝕜 Ω p hp →L[𝕜] 𝕜,
      (∀ u, G (gradientIntoRange u) = F u) ∧ ‖F‖ ≤ ‖G‖ ∧ ‖G‖ ≤ K * ‖F‖ := by
  let e : W0 𝕜 Ω p hp ≃ₗ[𝕜] GradientSpace 𝕜 Ω p hp :=
    LinearEquiv.ofInjective gradientJet hinj
  have he (v : GradientSpace 𝕜 Ω p hp) : gradientJet (e.symm v) = v.val :=
    congrArg Subtype.val (e.apply_symm_apply v)
  let G : GradientSpace 𝕜 Ω p hp →L[𝕜] 𝕜 :=
    (F.toLinearMap.comp e.symm.toLinearMap).mkContinuous (K * ‖F‖) (by
      intro v
      change ‖F (e.symm v)‖ ≤ _
      calc
        ‖F (e.symm v)‖ ≤ ‖F‖ * ‖e.symm v‖ :=
          @ContinuousLinearMap.le_opNorm 𝕜 𝕜 (W0 𝕜 Ω p hp) 𝕜
            inferInstance inferInstance inferInstance inferInstance
            inferInstance inferInstance (RingHom.id 𝕜) inferInstance F _
        _ ≤ ‖F‖ * (K * ‖gradientJet (e.symm v)‖) :=
          mul_le_mul_of_nonneg_left (hbound _) (@norm_nonneg (W0 𝕜 Ω p hp →L[𝕜] 𝕜) inferInstance F)
        _ = (K * ‖F‖) * ‖v‖ := by rw [he]; change ‖F‖ * (K * ‖v‖) = _; ring)
  have hGF (u : W0 𝕜 Ω p hp) : G (gradientIntoRange u) = F u := by
    change F (e.symm (e u)) = F u
    rw [e.symm_apply_apply]
  refine ⟨G, hGF, ?_, ?_⟩
  · apply @ContinuousLinearMap.opNorm_le_bound 𝕜 𝕜 (W0 𝕜 Ω p hp) 𝕜
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance (RingHom.id 𝕜) F _ (norm_nonneg G)
    intro u
    rw [← hGF]
    exact (G.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (gradientJet_norm_le u) (norm_nonneg G))
  · exact LinearMap.mkContinuous_norm_le _ (mul_nonneg (by linarith) (@norm_nonneg (W0 𝕜 Ω p hp →L[𝕜] 𝕜) inferInstance F)) _

theorem derivative_representation :
    Specs.ExpandedFA.Sobolev.NegativeSobolevRepresentation.DerivativeRepresentation := by
  intro 𝕜 _ d Ω hΩ hdim
  obtain ⟨K, hK, hbound⟩ := derivative_norm_equivalence 𝕜 d Ω hΩ hdim
  refine ⟨K, hK, ?_⟩
  intro p q _ _ _ hp F
  obtain ⟨G, hGF, hnF, hnG⟩ := functional_on_gradient K hK (hbound p hp).1
    (fun u => ((hbound p hp).2 u).2) F
  obtain ⟨L, hL, hnL⟩ := exists_extension_norm_eq (GradientSpace 𝕜 Ω p hp) G
  obtain ⟨f, hf, hfn⟩ := finite_product_duality (p := p) (q := q) (volume.restrict (Ω : Set (Domain d))) hp L
  refine ⟨G, f, hGF, ?_, ?_, hfn.trans hnL, hnF, hnG⟩
  · intro u i
    exact (Lp.memLp _).integrable_mul (Lp.memLp _)
  · intro u
    rw [← hGF u, ← hL (gradientIntoRange u), hf]
    rfl

end ExpandedFA.Sobolev.NegativeSobolev
