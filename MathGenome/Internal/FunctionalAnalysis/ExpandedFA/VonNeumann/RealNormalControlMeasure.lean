import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.RealNormalControlMeasure
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.VonNeumann.RealAbelianComplexification
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.VonNeumann.NormalAlgebraControlMeasure
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.RealFugledePutnam

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
namespace ExpandedFA.VonNeumann.RealNormalControlMeasure
universe u
open TraceIdeals.RealComplexification
open RealAbelianComplexification
open RealAbelianComplexification.Spec.NativeLp
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local instance : CompleteSpace (Space H) := TraceIdeals.RealComplexification.Spec.completeSpace

/-- Exact algebra bridge, on the existing complexification. -/
theorem complexAlgebra_normalAlgebra (N : H →L[ℝ] H) :
    complexAlgebra (Spec.normalAlgebra N) = NormalAlgebraControlMeasure.Spec.normalAlgebra (operator N) := by
  have hR : (Spec.normalAlgebra N : Set (H →L[ℝ] H)) =
      Set.centralizer (Set.centralizer (StarAlgebra.adjoin ℝ {N} : Set (H →L[ℝ] H))) := by
    rw [Spec.normalAlgebra, StarSubalgebra.coe_centralizer,
      StarMemClass.star_coe_eq, Set.union_self, StarSubalgebra.coe_centralizer,
      StarMemClass.star_coe_eq, Set.union_self]
  have hC : (NormalAlgebraControlMeasure.Spec.normalAlgebra (operator N) : Set _) =
      Set.centralizer (Set.centralizer (StarAlgebra.adjoin ℂ {operator N} :
        Set (Space H →L[ℂ] Space H))) := by
    rw [NormalAlgebraControlMeasure.Spec.normalAlgebra, StarSubalgebra.coe_centralizer,
      StarMemClass.star_coe_eq, Set.union_self, StarSubalgebra.coe_centralizer,
      StarMemClass.star_coe_eq, Set.union_self]
  apply SetLike.coe_injective
  rw [complexAlgebra_carrier]
  change complexSpanSet (Spec.normalAlgebra N : Set (H →L[ℝ] H)) = _
  rw [hR, hC]
  exact generated_double_commutants H N

/-- Membership of a complexified real operator is equivalent to actual real
membership, not to membership in a different real operator space. -/
theorem operator_mem_iff (N T : H →L[ℝ] H) :
    operator T ∈ NormalAlgebraControlMeasure.Spec.normalAlgebra (operator N) ↔ T ∈ Spec.normalAlgebra N := by
  rw [← complexAlgebra_normalAlgebra, mem_complexAlgebra]
  simp only [realPart_operator, imagPart_operator, zero_mem, and_true]

theorem normalAlgebra_abelian (N : H →L[ℝ] H) (hN : IsStarNormal N) :
    SeparableMASA.Spec.RealIsAbelian (Spec.normalAlgebra N) := by
  intro S hS T hT
  apply operator_injective
  rw [operator_mul, operator_mul]
  exact NormalAlgebraControlMeasure.normalAlgebra_abelian _
    (SpectralMeasure.RealFugledePutnam.operator_normal N hN) _
    ((operator_mem_iff N S).mpr hS) _ ((operator_mem_iff N T).mpr hT)

theorem normalAlgebra_wotClosed (N : H →L[ℝ] H) :
    SeparableMASA.Spec.RealIsWOTClosed (Spec.normalAlgebra N) := by
  have hc : SeparableMASA.Spec.IsWOTClosed (complexAlgebra (Spec.normalAlgebra N)) := by
    rw [complexAlgebra_normalAlgebra]
    exact NormalAlgebraControlMeasure.normalAlgebra_wotClosed _
  exact ((closed_algebras H (Spec.normalAlgebra N)).1).mpr hc

/-- Symmetrization is pointwise, rather than only an almost-everywhere law. -/
def symmetrize {X : Type*} (τ : X → X) (f : X → ℂ) : X → ℂ :=
  (2 : ℂ)⁻¹ • (f + star (f ∘ τ))

lemma symmetrize_compatible {X : Type*} (τ : X → X)
    (hi : Function.Involutive τ) (f : X → ℂ) :
    Spec.Compatible τ (symmetrize τ f) := by
  intro z
  simp [symmetrize, hi z, star_add, add_comm]

lemma symmetrize_bounded {X : Type*} [MeasurableSpace X] (τ : X → X)
    (hm : Measurable τ) (f : X → ℂ)
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) :
    SpectralMeasure.Spec.IsBoundedMeasurable (symmetrize τ f) := by
  have hcomp : SpectralMeasure.Spec.IsBoundedMeasurable (f ∘ τ) :=
    ⟨hf.1.comp hm, hf.2.imp (fun C hC x => hC (τ x))⟩
  exact (hf.add hcomp.star).smul _

/-- Every native fixed class has a bounded Borel representative with exact
pointwise equivariance. No completeness or finiteness of μ is needed. -/
theorem exists_compatible_representative {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (D : InvolutionData μ) (h : Fixed D ∞) :
    ∃ f : X → ℂ, SpectralMeasure.Spec.IsBoundedMeasurable f ∧
      Spec.Compatible D.tau f ∧ f =ᵐ[μ] h.val := by
  obtain ⟨f, hf, heq⟩ := NormalAlgebraControlMeasure.exists_bounded_representative μ h.val
  refine ⟨symmetrize D.tau f,
    symmetrize_bounded D.tau D.measurePreserving.measurable f hf,
    symmetrize_compatible D.tau D.involutive f, ?_⟩
  filter_upwards [heq, D.measurePreserving.quasiMeasurePreserving.ae_eq_comp heq,
    fixed_ae D h] with x hx htx hfix
  change f (D.tau x) = h.val (D.tau x) at htx
  simp only [symmetrize, Pi.smul_apply, Pi.add_apply, Pi.star_apply,
    Function.comp_apply, hx, htx, hfix, star_star, smul_eq_mul]
  ring

/-- An exactly equivariant bounded Borel symbol gives a native fixed class. -/
def classOfCompatible {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (D : InvolutionData μ) (f : X → ℂ)
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) (hc : Spec.Compatible D.tau f) :
    Fixed D ∞ :=
  ⟨(NormalAlgebraControlMeasure.bounded_memLp_top μ hf).toLp f, by
    apply (mem_fixedSubmodule_iff_ae D _).mpr
    have heq := (NormalAlgebraControlMeasure.bounded_memLp_top μ hf).coeFn_toLp
    filter_upwards [heq, D.measurePreserving.quasiMeasurePreserving.ae_eq_comp heq]
      with x hx htx
    simp only [Function.comp_apply] at htx
    rw [htx, hx, hc x]⟩

lemma classOfCompatible_ae {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (D : InvolutionData μ) (f : X → ℂ)
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) (hc : Spec.Compatible D.tau f) :
    (classOfCompatible D f hf hc).val =ᵐ[μ] f := (NormalAlgebraControlMeasure.bounded_memLp_top μ hf).coeFn_toLp

/-- Instantiate the upstream full covariance on every Borel subset of the
spectrum. The corresponding projections remain complex operators. -/
theorem projection_covariance (N : H →L[ℝ] H)
    (E : SpectralMeasure.ProjectionValuedMeasure (Spec.Spectrum N) (Space H))
    (hE : SpectralMeasure.NormalPVM.Spec.Resolves (operator N) E)
    (B : Set (Spec.Spectrum N)) (hB : MeasurableSet B) (p : Space H) :
    conjugation (E B (conjugation p)) =
      E (SpectralMeasure.RealFugledePutnam.spectrumConjugation N ⁻¹' B) p := by
  classical
  let τ := SpectralMeasure.RealFugledePutnam.spectrumConjugation N
  let f := B.indicator (fun _ : Spec.Spectrum N => (1 : ℂ))
  have hf : SpectralMeasure.Spec.IsBoundedMeasurable f :=
    SpectralMeasure.BorelNormSpectrum.bounded_indicator B hB
      (SpectralMeasure.BorelNormSpectrum.bounded_const 1)
  have hi : star (f ∘ τ) = (τ ⁻¹' B).indicator (fun _ => (1 : ℂ)) := by
    funext z
    by_cases hz : τ z ∈ B <;> simp [f, hz]
  have hh := SpectralMeasure.RealFugledePutnam.integral_conjugation N E hE f hf
  rw [hi, SpectralMeasure.BorelNormSpectrum.integral_indicator_one E _
    (τ.continuous.measurable hB),
    show E.spectralIntegral f = E B from
      SpectralMeasure.BorelNormSpectrum.integral_indicator_one E B hB] at hh
  exact congrArg (fun A : Space H →L[ℂ] Space H => A p) hh

/-- Real separating vectors, not a preselected complex control measure. -/
theorem spectral_control [TopologicalSpace.SeparableSpace H]
    (N : H →L[ℝ] H) (hN : IsStarNormal N) : Nonempty (Spec.SpectralControl N) := by
  obtain ⟨E, hE, huniq⟩ := SpectralMeasure.NormalPVM.normal_spectral_theorem
    (Space H) (operator N) (SpectralMeasure.RealFugledePutnam.operator_normal N hN)
  obtain ⟨e, he⟩ := SeparableMASA.real_abelian_separating H (Spec.normalAlgebra N)
    (normalAlgebra_abelian N hN) (normalAlgebra_wotClosed N)
  have heC : SeparableMASA.Spec.IsSeparating (NormalAlgebraControlMeasure.Spec.normalAlgebra (operator N)) (inclusion e) := by
    rw [← complexAlgebra_normalAlgebra]
    exact separating_transport (Spec.normalAlgebra N) e he
  let μ := E.diagonalMeasure (inclusion e)
  let τ := SpectralMeasure.RealFugledePutnam.spectrumConjugation N
  have hi : Function.Involutive τ := by intro z; ext; simp [τ,
    SpectralMeasure.RealFugledePutnam.spectrumConjugation]
  have hmp : MeasurePreserving τ μ μ := by
    refine ⟨τ.continuous.measurable, ?_⟩
    apply Measure.ext
    intro B hB
    rw [Measure.map_apply τ.continuous.measurable hB]
    change μ (τ ⁻¹' B) = μ B
    rw [E.diagonalMeasure_apply _ _ (τ.continuous.measurable hB),
      E.diagonalMeasure_apply _ _ hB]
    have hp := projection_covariance N E hE B hB (inclusion e)
    have hefix : conjugation (inclusion e) = inclusion e := by
      change (e, -(0 : H)) = (e, 0)
      simp
    rw [hefix] at hp
    rw [← hp, conjugation.norm_map]
  exact ⟨{
    E := E, Φ := E.spectralIntegral, e := e, μ := μ,
    finite := inferInstance, regular := inferInstance,
    resolves := hE, unique := huniq,
    calculus := SpectralMeasure.BorelNormSpectrum.borel_calculus E,
    coordinate := SpectralMeasure.NormalPVM.continuousIntegral_coordinate E hE,
    separating := he, complexSeparating := heC,
    vectorMeasure := E.diagonalMeasure_apply (inclusion e),
    control := NormalAlgebraControlMeasure.controlMeasure_of_separating
      (SpectralMeasure.RealFugledePutnam.operator_normal N hN) E hE (inclusion e) heC,
    τ := τ, tau_apply := fun _ => rfl, involutive := hi,
    measurePreserving := hmp, covariance := projection_covariance N E hE }⟩


/-- Instantiate compatible Borel invariance and actual bounded restriction
from the real Fuglede–Putnam interface. -/
theorem descent (N : H →L[ℝ] H) (hN : IsStarNormal N)
    (C : Spec.SpectralControl N) (f : Spec.Spectrum N → ℂ)
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) (hc : Spec.Compatible C.τ f) :
    (∀ p : Space H, conjugation p = p → conjugation (C.Φ f p) = C.Φ f p) ∧
    SpectralMeasure.RealFugledePutnam.Spec.UniqueRealRestriction (C.Φ f) (Spec.realCalculus C.Φ f) ∧
    operator (Spec.realCalculus C.Φ f) = C.Φ f := by
  have hs : ∀ z ∈ spectrum ℂ (operator N), star z ∈ spectrum ℂ (operator N) :=
    fun z hz => (SpectralMeasure.RealFugledePutnam.spectrum_conjugation N z).mp hz
  have hcomp : ∀ z : Spec.Spectrum N,
      f ⟨star z.val, hs z.val z.property⟩ = star (f z) := by
    intro z
    have hz : (⟨star z.val, hs z.val z.property⟩ : Spec.Spectrum N) = C.τ z :=
      Subtype.ext (C.tau_apply z).symm
    rw [hz]
    exact hc z
  have hInv := SpectralMeasure.RealFugledePutnam.compatible_borel_invariance
    H N hN C.E C.resolves C.Φ C.calculus (spectrum ℂ (operator N))
    (Set.Subset.refl _) hs f hf hcomp
  change (∀ p : Space H, conjugation p = p → conjugation (C.Φ f p) = C.Φ f p) at hInv
  exact ⟨hInv, SpectralMeasure.RealFugledePutnam.restriction_of_fixed (C.Φ f) hInv⟩

/-- The original real algebra coordinate of the native complex L∞ calculus. -/
def realLinearCalculus (N : H →L[ℝ] H) (hN : IsStarNormal N)
    (C : Spec.SpectralControl N) : Fixed C.involutionData ∞ →ₗ[ℝ] Spec.normalAlgebra N where
  toFun h :=
    let G := NormalAlgebraControlMeasure.linftyCalculus
      (SpectralMeasure.RealFugledePutnam.operator_normal N hN) C.E C.resolves C.μ C.control
    ⟨operatorRealPart (G h.val : Space H →L[ℂ] Space H), by
      have hm := (complexAlgebra_normalAlgebra N).ge (G h.val).property
      exact ((mem_complexAlgebra _ _).mp hm).1⟩
  map_add' h k := by
    apply Subtype.ext
    change operatorRealPart
      (NormalAlgebraControlMeasure.linftyCalculus
        (SpectralMeasure.RealFugledePutnam.operator_normal N hN) C.E C.resolves C.μ C.control
          (h.val + k.val) : Space H →L[ℂ] Space H) = _
    simp only [map_add]
    exact realPart_add _ _
  map_smul' a h := by
    apply Subtype.ext
    change operatorRealPart
      (NormalAlgebraControlMeasure.linftyCalculus
        (SpectralMeasure.RealFugledePutnam.operator_normal N hN) C.E C.resolves C.μ C.control
          ((a : ℂ) • h.val) : Space H →L[ℂ] Space H) = _
    simp only [map_smul]
    change operatorRealPart ((a : ℂ) •
      (NormalAlgebraControlMeasure.linftyCalculus
        (SpectralMeasure.RealFugledePutnam.operator_normal N hN) C.E C.resolves C.μ C.control
          h.val : Space H →L[ℂ] Space H)) = a • operatorRealPart _
    simp only [RealAbelianComplexification.realPart_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]

/-- On every compatible representative the construction is the actual real
restriction, and complexifying recovers the original spectral integral. -/
theorem realLinearCalculus_on_representative (N : H →L[ℝ] H) (hN : IsStarNormal N)
    (C : Spec.SpectralControl N) (h : Fixed C.involutionData ∞)
    (f : Spec.Spectrum N → ℂ) (hf : SpectralMeasure.Spec.IsBoundedMeasurable f)
    (hc : Spec.Compatible C.τ f) (heq : f =ᵐ[C.μ] h.val) :
    (realLinearCalculus N hN C h : H →L[ℝ] H) = Spec.realCalculus C.Φ f ∧
    operator (realLinearCalculus N hN C h : H →L[ℝ] H) = C.Φ f := by
  have hh := NormalAlgebraControlMeasure.linftyCalculus_eq
    (SpectralMeasure.RealFugledePutnam.operator_normal N hN) C.E C.resolves C.μ C.control h.val hf heq
  rw [← SpectralMeasure.FugledePutnam.calculus_eq_integral C.E C.Φ C.calculus f hf] at hh
  have hr : (realLinearCalculus N hN C h : H →L[ℝ] H) = Spec.realCalculus C.Φ f :=
    congrArg operatorRealPart hh
  exact ⟨hr, (congrArg operator hr).trans (descent N hN C f hf hc).2.2⟩

theorem realLinearCalculus_extension (N : H →L[ℝ] H) (hN : IsStarNormal N)
    (C : Spec.SpectralControl N) (h : Fixed C.involutionData ∞) :
    operator (realLinearCalculus N hN C h : H →L[ℝ] H) =
      (NormalAlgebraControlMeasure.linftyCalculus
        (SpectralMeasure.RealFugledePutnam.operator_normal N hN) C.E C.resolves C.μ C.control h.val :
          Space H →L[ℂ] Space H) := by
  obtain ⟨f, hf, hc, heq⟩ := exists_compatible_representative C.involutionData h
  have hh := NormalAlgebraControlMeasure.linftyCalculus_eq
    (SpectralMeasure.RealFugledePutnam.operator_normal N hN) C.E C.resolves C.μ C.control h.val hf heq
  rw [← SpectralMeasure.FugledePutnam.calculus_eq_integral C.E C.Φ C.calculus f hf] at hh
  exact (realLinearCalculus_on_representative N hN C h f hf hc heq).2.trans hh.symm

theorem realLinearCalculus_norm (N : H →L[ℝ] H) (hN : IsStarNormal N)
    (C : Spec.SpectralControl N) (h : Fixed C.involutionData ∞) :
    ‖realLinearCalculus N hN C h‖ = ‖h‖ := by
  change ‖(realLinearCalculus N hN C h : H →L[ℝ] H)‖ = ‖h.val‖
  rw [← operator_norm, realLinearCalculus_extension]
  exact NormalAlgebraControlMeasure.linftyCalculus_norm
    (SpectralMeasure.RealFugledePutnam.operator_normal N hN) C.E C.resolves C.μ C.control h.val

theorem realLinearCalculus_mul (N : H →L[ℝ] H) (hN : IsStarNormal N)
    (C : Spec.SpectralControl N) (h k : Fixed C.involutionData ∞) :
    realLinearCalculus N hN C (h*k) = realLinearCalculus N hN C h * realLinearCalculus N hN C k := by
  apply Subtype.ext
  apply operator_injective
  change operator (realLinearCalculus N hN C (h*k) : H →L[ℝ] H) =
    operator ((realLinearCalculus N hN C h : H →L[ℝ] H) *
      (realLinearCalculus N hN C k : H →L[ℝ] H))
  rw [operator_mul, realLinearCalculus_extension, realLinearCalculus_extension,
    realLinearCalculus_extension]
  exact congrArg Subtype.val (NormalAlgebraControlMeasure.linftyCalculus_mul
    (SpectralMeasure.RealFugledePutnam.operator_normal N hN) C.E C.resolves C.μ C.control h.val k.val)

theorem realLinearCalculus_star (N : H →L[ℝ] H) (hN : IsStarNormal N)
    (C : Spec.SpectralControl N) (h : Fixed C.involutionData ∞) :
    realLinearCalculus N hN C (star h) = star (realLinearCalculus N hN C h) := by
  apply Subtype.ext
  apply operator_injective
  change operator (realLinearCalculus N hN C (star h) : H →L[ℝ] H) =
    operator (star (realLinearCalculus N hN C h : H →L[ℝ] H))
  rw [← operator_star, realLinearCalculus_extension, realLinearCalculus_extension]
  exact congrArg Subtype.val (NormalAlgebraControlMeasure.linftyCalculus_star
    (SpectralMeasure.RealFugledePutnam.operator_normal N hN) C.E C.resolves C.μ C.control h.val)

/-- The given spectral involution is the actual complex conjugation map. -/
lemma tau_eq (N : H →L[ℝ] H) (C : Spec.SpectralControl N) :
    C.τ = SpectralMeasure.RealFugledePutnam.spectrumConjugation N := by
  ext z
  exact C.tau_apply z

/-- Symmetrizing any Borel symbol for an actual real operator leaves that
operator unchanged. This proves surjectivity onto the original real algebra. -/
theorem compatible_borel_surjective (N : H →L[ℝ] H) (hN : IsStarNormal N)
    (C : Spec.SpectralControl N) (T : H →L[ℝ] H) (hT : T ∈ Spec.normalAlgebra N) :
    ∃ f : Spec.Spectrum N → ℂ, SpectralMeasure.Spec.IsBoundedMeasurable f ∧
      Spec.Compatible C.τ f ∧ C.Φ f = operator T := by
  obtain ⟨f, hf, hTf⟩ := NormalAlgebraControlMeasure.borel_surjective_of_separating
    (SpectralMeasure.RealFugledePutnam.operator_normal N hN) C.E C.resolves
    (inclusion C.e) C.complexSeparating (operator T) ((operator_mem_iff N T).mpr hT)
  have hcomp : SpectralMeasure.Spec.IsBoundedMeasurable (f ∘ C.τ) :=
    ⟨hf.1.comp C.τ.continuous.measurable, hf.2.imp (fun M hM z => hM (C.τ z))⟩
  have hsymm := SpectralMeasure.RealFugledePutnam.integral_conjugation N C.E C.resolves f hf
  rw [← tau_eq N C, hTf, SpectralMeasure.RealFugledePutnam.conjugateOperator_real] at hsymm
  refine ⟨symmetrize C.τ f, symmetrize_bounded C.τ C.τ.continuous.measurable f hf,
    symmetrize_compatible C.τ C.involutive f, ?_⟩
  rw [SpectralMeasure.FugledePutnam.calculus_eq_integral C.E C.Φ C.calculus _
    (symmetrize_bounded C.τ C.τ.continuous.measurable f hf)]
  rw [symmetrize, C.E.spectralIntegral_smul _ _ (hf.add hcomp.star),
    C.E.spectralIntegral_add _ _ hf hcomp.star, hTf, ← hsymm]
  rw [← two_smul ℂ (operator T), smul_smul]
  norm_num

theorem realLinearCalculus_surjective (N : H →L[ℝ] H) (hN : IsStarNormal N)
    (C : Spec.SpectralControl N) : Function.Surjective (realLinearCalculus N hN C) := by
  intro T
  obtain ⟨f, hf, hc, hΦ⟩ := compatible_borel_surjective N hN C T T.property
  let h := classOfCompatible C.involutionData f hf hc
  refine ⟨h, ?_⟩
  apply Subtype.ext
  apply operator_injective
  exact (realLinearCalculus_on_representative N hN C h f hf hc
    (classOfCompatible_ae C.involutionData f hf hc).symm).2.trans hΦ

/-- No identification of existentially chosen complex and real measures is
used: all constructions here use the input C's vector control measure. -/
def algebraModel (N : H →L[ℝ] H) (hN : IsStarNormal N)
    (C : Spec.SpectralControl N) : Spec.AlgebraModel N := by
  let F := realLinearCalculus N hN C
  let I : Fixed C.involutionData ∞ →ₗᵢ[ℝ] Spec.normalAlgebra N :=
    { F with norm_map' := realLinearCalculus_norm N hN C }
  let Ψ := LinearEquiv.ofBijective F ⟨I.injective, realLinearCalculus_surjective N hN C⟩
  refine { C with
    Ψ := Ψ
    descent := descent N hN C
    image := ?_
    multiplicative := realLinearCalculus_mul N hN C
    star_preserving := realLinearCalculus_star N hN C
    isometric := realLinearCalculus_norm N hN C
    representatives := exists_compatible_representative C.involutionData
    on_representatives := realLinearCalculus_on_representative N hN C
    real_coordinate := ?_ }
  · intro T
    constructor
    · intro hT
      obtain ⟨f, hf, hc, hΦ⟩ := compatible_borel_surjective N hN C T hT
      exact ⟨f, hf, hc, by
        change operatorRealPart (C.Φ f) = T
        rw [hΦ, realPart_operator]⟩
    · rintro ⟨f, hf, hc, rfl⟩
      apply (operator_mem_iff N _).mp
      rw [(descent N hN C f hf hc).2.2,
        SpectralMeasure.FugledePutnam.calculus_eq_integral C.E C.Φ C.calculus f hf]
      exact NormalAlgebraControlMeasure.spectralIntegral_mem
        (SpectralMeasure.RealFugledePutnam.operator_normal N hN) C.E C.resolves f hf
  · change operatorRealPart (C.Φ (fun z => (z : ℂ))) = N
    rw [C.coordinate, realPart_operator]

/-- The corrected finite real normal control and algebra theorem. -/
theorem real_normal_control_measure : Spec.RealNormalControlMeasure.{u} := by
  intro H _ _ _ _ N hN
  obtain ⟨C⟩ := spectral_control N hN
  exact ⟨algebraModel N hN C⟩
/-- Complexification preserves and reflects two-sided bounded inverses. -/
lemma operator_isUnit_iff (A : H →L[ℝ] H) : IsUnit (operator A) ↔ IsUnit A := by
  rw [isUnit_iff_exists, isUnit_iff_exists]
  change (∃ B : Space H →L[ℂ] Space H,
    (operator A).comp B = ContinuousLinearMap.id ℂ (Space H) ∧
      B.comp (operator A) = ContinuousLinearMap.id ℂ (Space H)) ↔
    ∃ B : H →L[ℝ] H, A.comp B = ContinuousLinearMap.id ℝ H ∧
      B.comp A = ContinuousLinearMap.id ℝ H
  exact (TraceIdeals.RealComplexification.invertibility H A).1.symm

/-- The intrinsic real spectrum is exactly the real section of the actual
complexification spectrum, including the empty zero-space spectrum. -/
lemma real_spectrum_iff (N : H →L[ℝ] H) (t : ℝ) :
    t ∈ spectrum ℝ N ↔ (t : ℂ) ∈ spectrum ℂ (operator N) := by
  rw [spectrum.mem_iff, spectrum.mem_iff]
  have he : operator (algebraMap ℝ (H →L[ℝ] H) t - N) =
      algebraMap ℂ (Space H →L[ℂ] Space H) (t : ℂ) - operator N := by
    rw [sub_eq_add_neg, operator_add, operator_neg,
      Algebra.algebraMap_eq_smul_one, operator_real_smul, operator_one]
    rw [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg]
  rw [← he, operator_isUnit_iff]

/-- In the self-adjoint case the spectral involution is the identity, so the
native fixed L∞ algebra is precisely the usual real-valued scalar calculus
on the intrinsic real spectrum. -/
theorem selfAdjoint_specialization : Spec.SelfAdjointSpecialization.{u} := by
  intro H _ _ _ _ N hN
  have hnormal : IsStarNormal N := hN.isStarNormal
  obtain ⟨C⟩ := real_normal_control_measure H N hnormal
  refine ⟨C, ?_, real_spectrum_iff N⟩
  intro z
  have hNC : IsSelfAdjoint (operator N) := by
    change star (operator N) = operator N
    rw [operator_star, hN.star_eq]
  have hz : (z : ℂ) = ((z : ℂ).re : ℂ) := hNC.mem_spectrum_eq_re z.property
  refine ⟨by rw [hz]; simp, ?_⟩
  apply Subtype.ext
  rw [C.tau_apply, hz]
  simp

/-- Embedding native real L∞ into the identity-involution real form. -/
def realFixedMap {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (D : InvolutionData μ) (hid : ∀ x, D.tau x = x) :
    Lp ℝ ∞ μ →ₗ[ℝ] Fixed D ∞ where
  toFun h := ⟨Complex.ofRealCLM.compLp h, by
    apply (mem_fixedSubmodule_iff_ae D _).mpr
    filter_upwards [Complex.ofRealCLM.coeFn_compLp h] with x hx
    rw [hid, hx]
    simp⟩
  map_add' h k := by
    apply Subtype.ext
    exact (Complex.ofRealCLM.compLpₗ ∞ μ).map_add h k
  map_smul' a h := by
    apply Subtype.ext
    exact (Complex.ofRealCLM.compLpₗ ∞ μ).map_smul a h

lemma realFixedMap_ae {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (D : InvolutionData μ) (hid : ∀ x, D.tau x = x) (h : Lp ℝ ∞ μ) :
    (realFixedMap D hid h).val =ᵐ[μ] fun x => (h x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLp h

lemma realFixedMap_norm {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (D : InvolutionData μ) (hid : ∀ x, D.tau x = x) (h : Lp ℝ ∞ μ) :
    ‖realFixedMap D hid h‖ = ‖h‖ := by
  change ‖(realFixedMap D hid h).val‖ = ‖h‖
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable h)
  filter_upwards [realFixedMap_ae D hid h] with x hx
  rw [hx, Complex.norm_real]

lemma realFixedMap_surjective {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (D : InvolutionData μ) (hid : ∀ x, D.tau x = x) :
    Function.Surjective (realFixedMap D hid) := by
  intro h
  let r := Complex.reCLM.compLp h.val
  refine ⟨r, ?_⟩
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [realFixedMap_ae D hid r, Complex.reCLM.coeFn_compLp h.val,
    fixed_ae D h] with x hx hr hfix
  rw [hid x] at hfix
  rw [hx]
  change r x = (h.val x).re at hr
  rw [hr]
  apply Complex.ext
  · rfl
  · have him := congrArg Complex.im hfix
    simp only [Complex.star_def, Complex.conj_im] at him
    change 0 = (h.val x).im
    linarith

def realFixedEquiv {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (D : InvolutionData μ) (hid : ∀ x, D.tau x = x) :
    Lp ℝ ∞ μ ≃ₗ[ℝ] Fixed D ∞ :=
  LinearEquiv.ofBijective (realFixedMap D hid)
    ⟨(show Lp ℝ ∞ μ →ₗᵢ[ℝ] Fixed D ∞ from
      { realFixedMap D hid with norm_map' := realFixedMap_norm D hid }).injective,
      realFixedMap_surjective D hid⟩

lemma realFixedEquiv_mul {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (D : InvolutionData μ) (hid : ∀ x, D.tau x = x) (h k : Lp ℝ ∞ μ) :
    realFixedEquiv D hid ((ContinuousLinearMap.mul ℝ ℝ).holder ∞ h k) =
      realFixedEquiv D hid h * realFixedEquiv D hid k := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [realFixedMap_ae D hid ((ContinuousLinearMap.mul ℝ ℝ).holder ∞ h k),
    (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := ∞) h k,
    coeFn_fixedProduct D (realFixedEquiv D hid h) (realFixedEquiv D hid k),
    realFixedMap_ae D hid h, realFixedMap_ae D hid k] with x h1 h2 h3 h4 h5
  change (realFixedMap D hid ((ContinuousLinearMap.mul ℝ ℝ).holder ∞ h k)).val x =
    (realFixedEquiv D hid h * realFixedEquiv D hid k).val x
  rw [h1, h2, h3]
  change ((h x * k x : ℝ) : ℂ) = (realFixedMap D hid h).val x * (realFixedMap D hid k).val x
  rw [h4, h5, Complex.ofReal_mul]

lemma realFixedEquiv_star {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (D : InvolutionData μ) (hid : ∀ x, D.tau x = x) (h : Lp ℝ ∞ μ) :
    star (realFixedEquiv D hid h) = realFixedEquiv D hid h := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [coeFn_fixedStar D (realFixedEquiv D hid h), realFixedMap_ae D hid h]
    with x h1 h2
  change (star (realFixedEquiv D hid h)).val x = (realFixedMap D hid h).val x
  rw [h1]
  change star ((realFixedMap D hid h).val x) = (realFixedMap D hid h).val x
  rw [h2]
  simp

/-- Native real L∞ pullback along the actual spectral homeomorphism. -/
def realLpPullback {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (κ : X ≃ₜ Y) (μ : Measure X) : Lp ℝ ∞ (μ.map κ) ≃ₗ[ℝ] Lp ℝ ∞ μ := by
  let mp : MeasurePreserving κ μ (μ.map κ) := ⟨κ.continuous.measurable, rfl⟩
  let F := Lp.compMeasurePreservingₗᵢ ℝ κ mp (E := ℝ) (p := ∞)
  apply LinearEquiv.ofBijective F.toLinearMap
  refine ⟨F.injective, ?_⟩
  intro h
  have mp' : MeasurePreserving κ.symm (μ.map κ) μ := by
    refine ⟨κ.symm.continuous.measurable, ?_⟩
    apply Measure.ext
    intro B hB
    rw [Measure.map_apply κ.symm.continuous.measurable hB,
      Measure.map_apply κ.continuous.measurable (κ.symm.continuous.measurable hB)]
    congr 1
    ext x
    simp only [Set.mem_preimage, κ.symm_apply_apply]
  refine ⟨Lp.compMeasurePreserving κ.symm mp' h, ?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (Lp.compMeasurePreserving κ.symm mp' h) mp,
    mp.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_compMeasurePreserving h mp')]
    with x h1 h2
  change (Lp.compMeasurePreserving κ mp (Lp.compMeasurePreserving κ.symm mp' h)) x = h x
  exact h1.trans (by simpa only [Function.comp_apply, κ.symm_apply_apply] using h2)

lemma realLpPullback_ae {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (κ : X ≃ₜ Y) (μ : Measure X) (h : Lp ℝ ∞ (μ.map κ)) :
    realLpPullback κ μ h =ᵐ[μ] fun x => h (κ x) := by
  change Lp.compMeasurePreserving κ ⟨κ.continuous.measurable, rfl⟩ h =ᵐ[μ] _
  exact Lp.coeFn_compMeasurePreserving _ _

lemma realLpPullback_norm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (κ : X ≃ₜ Y) (μ : Measure X) (h : Lp ℝ ∞ (μ.map κ)) :
    ‖realLpPullback κ μ h‖ = ‖h‖ := by
  change ‖Lp.compMeasurePreserving κ ⟨κ.continuous.measurable, rfl⟩ h‖ = ‖h‖
  exact Lp.norm_compMeasurePreserving _ _

lemma realLpPullback_mul {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (κ : X ≃ₜ Y) (μ : Measure X) (h k : Lp ℝ ∞ (μ.map κ)) :
    realLpPullback κ μ ((ContinuousLinearMap.mul ℝ ℝ).holder ∞ h k) =
      (ContinuousLinearMap.mul ℝ ℝ).holder ∞ (realLpPullback κ μ h) (realLpPullback κ μ k) := by
  apply Lp.ext
  let mp : MeasurePreserving κ μ (μ.map κ) := ⟨κ.continuous.measurable, rfl⟩
  filter_upwards [realLpPullback_ae κ μ ((ContinuousLinearMap.mul ℝ ℝ).holder ∞ h k),
    mp.quasiMeasurePreserving.ae_eq_comp ((ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := ∞) h k),
    (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := ∞) (realLpPullback κ μ h) (realLpPullback κ μ k),
    realLpPullback_ae κ μ h, realLpPullback_ae κ μ k] with x h1 h2 h3 h4 h5
  simpa only [h1, h3, h4, h5, Function.comp_apply, ContinuousLinearMap.mul_apply'] using h2

/-- The homeomorphism from the complexification spectrum to the actual real
spectrum when all its points are real. -/
def realSpectrumHomeomorph (N : H →L[ℝ] H)
    (hreal : ∀ z : Spec.Spectrum N, (z : ℂ) = ((z : ℂ).re : ℂ)) :
    Spec.Spectrum N ≃ₜ spectrum ℝ N where
  toFun z := ⟨(z : ℂ).re, (real_spectrum_iff N _).mpr (by rw [← hreal z]; exact z.property)⟩
  invFun t := ⟨(t : ℝ), (real_spectrum_iff N _).mp t.property⟩
  left_inv z := Subtype.ext (hreal z).symm
  right_inv t := Subtype.ext (Complex.ofReal_re _)
  continuous_toFun := (Complex.continuous_re.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (Complex.continuous_ofReal.comp continuous_subtype_val).subtype_mk _

theorem real_scalar_specialization : Spec.RealScalarSpecialization.{u} := by
  intro H _ _ _ _ N hN
  obtain ⟨C, hreal, _⟩ := selfAdjoint_specialization H N hN
  have hz : ∀ z : Spec.Spectrum N, (z : ℂ) = ((z : ℂ).re : ℂ) := by
    intro z
    exact Complex.ext rfl (by simpa only [Complex.ofReal_im] using (hreal z).1)
  let κ := realSpectrumHomeomorph N hz
  let ν := C.μ.map κ
  let D := C.toSpectralControl.involutionData
  have hid : ∀ x, D.tau x = x := fun x => (hreal x).2
  let U : Lp ℝ ∞ ν ≃ₗ[ℝ] Spec.normalAlgebra N :=
    (realLpPullback κ C.μ).trans ((realFixedEquiv D hid).trans C.Ψ)
  letI := C.finite
  have hfin : IsFiniteMeasure ν := inferInstance
  letI := hfin
  refine ⟨C, ⟨{
    κ := κ, realCoordinate := fun _ => rfl,
    ν := ν, measure_eq := rfl, finite := hfin, regular := inferInstance,
    U := U, isometric := ?_, multiplicative := ?_, selfAdjoint := ?_, on_representatives := ?_
  }⟩⟩
  · intro h
    change ‖C.Ψ (realFixedEquiv D hid (realLpPullback κ C.μ h))‖ = ‖h‖
    rw [C.isometric]
    change ‖realFixedMap D hid (realLpPullback κ C.μ h)‖ = ‖h‖
    rw [realFixedMap_norm, realLpPullback_norm]
  · intro h k
    change C.Ψ (realFixedEquiv D hid (realLpPullback κ C.μ
      ((ContinuousLinearMap.mul ℝ ℝ).holder ∞ h k))) =
      C.Ψ (realFixedEquiv D hid (realLpPullback κ C.μ h)) *
        C.Ψ (realFixedEquiv D hid (realLpPullback κ C.μ k))
    rw [realLpPullback_mul, realFixedEquiv_mul, C.multiplicative]
  · intro h
    change star (C.Ψ (realFixedEquiv D hid (realLpPullback κ C.μ h)) : H →L[ℝ] H) = _
    have he := C.star_preserving (realFixedEquiv D hid (realLpPullback κ C.μ h))
    rw [realFixedEquiv_star] at he
    exact congrArg Subtype.val he.symm
  · intro h f hf hb heq
    let g : Spec.Spectrum N → ℂ := fun z => (f (κ z) : ℂ)
    have hgb : SpectralMeasure.Spec.IsBoundedMeasurable g := by
      refine ⟨Complex.continuous_ofReal.measurable.comp (hf.comp κ.continuous.measurable), ?_⟩
      obtain ⟨M, hM⟩ := hb
      exact ⟨M, fun z => by simpa only [g, Complex.norm_real] using hM (κ z)⟩
    have hgc : Spec.Compatible C.τ g := by
      intro z
      change g (D.tau z) = star (g z)
      rw [hid z]
      simp [g]
    have hge : g =ᵐ[C.μ] (realFixedEquiv D hid (realLpPullback κ C.μ h)).val := by
      let mp : MeasurePreserving κ C.μ ν := ⟨κ.continuous.measurable, rfl⟩
      filter_upwards [realFixedMap_ae D hid (realLpPullback κ C.μ h),
        realLpPullback_ae κ C.μ h, mp.quasiMeasurePreserving.ae_eq_comp heq]
        with x h1 h2 h3
      change f (κ x) = h (κ x) at h3
      change (f (κ x) : ℂ) = (realFixedMap D hid (realLpPullback κ C.μ h)).val x
      rw [h1, h2, h3]
    exact (C.on_representatives (realFixedEquiv D hid (realLpPullback κ C.μ h))
      g hgb hgc hge).1

end ExpandedFA.VonNeumann.RealNormalControlMeasure
