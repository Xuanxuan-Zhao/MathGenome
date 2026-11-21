import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.HomogeneousWaveCompletion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.AbstractWaveEnergy
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.ClosabilityAndDoubleAdjoint

noncomputable section
open Set UniformSpace
open scoped NNReal
namespace ExpandedFA.Models.HomogeneousWaveCompletion
open Unbounded AbstractWaveEnergy
universe u
section Generic
variable {𝕜 : Type*} [RCLike 𝕜] {H : Type u}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem quotient_norm : Spec.QuotientNorm (𝕜 := 𝕜) (H := H) := by
  intro S u
  rfl

theorem quotient_kernel : Spec.QuotientKernel (𝕜 := 𝕜) (H := H) := by
  intro S u v
  change (Submodule.Quotient.mk u : S.domain ⧸ LinearMap.ker S.toFun) = Submodule.Quotient.mk v ↔ _
  rw [Submodule.Quotient.eq]
  change S.toFun (u - v) = 0 ↔ _
  rw [map_sub, sub_eq_zero]
  constructor
  · intro h
    apply (mem_kernel_iff S _).mpr
    refine ⟨S.domain.sub_mem u.prop v.prop, ?_⟩
    change S.toFun (u - v) = 0
    simpa only [map_sub] using sub_eq_zero.mpr h
  · intro h
    obtain ⟨_, h⟩ := (mem_kernel_iff S _).mp h
    change S.toFun (u - v) = 0 at h
    simpa only [map_sub, sub_eq_zero] using h

variable [CompleteSpace H]

theorem range_closure (L S : Operator 𝕜 H H) (hS : IsNonnegativeSquareRoot L S) :
    S.toFun.range.topologicalClosure = Hzero L := by
  have h := orthogonal_range_eq_kernel_hilbertAdjoint S hS.1.1
  change S.toFun.range.orthogonal = S.adjoint.ker at h
  rw [hS.1.2.1, hS.2.2] at h
  rw [← Submodule.orthogonal_orthogonal_eq_closure, h]

/-- Thus the represented quotient is exactly D(S)/ker L, including nonzero kernels. -/
theorem source_quotient (L S : Operator 𝕜 H H)
    (hS : IsNonnegativeSquareRoot L S) (u v : S.domain) :
    quotientMap S u = quotientMap S v ↔ (u : H) - (v : H) ∈ L.ker := by
  rw [quotient_kernel S u v, hS.2.2]

def quotientToHzero (L S : Operator 𝕜 H H) (hS : IsNonnegativeSquareRoot L S) :
    DisplacementQuotient S →ₗᵢ[𝕜] Hzero L where
  toLinearMap :=
    (Submodule.inclusion (show S.toFun.range ≤ Hzero L from
      (S.toFun.range.le_topologicalClosure).trans_eq (range_closure L S hS))).comp
        (quotientRange S).toLinearMap
  norm_map' _ := rfl

theorem quotientToHzero_dense (L S : Operator 𝕜 H H) (hS : IsNonnegativeSquareRoot L S) :
    DenseRange (quotientToHzero L S hS) := by
  have hi : DenseRange (Submodule.inclusion (show S.toFun.range ≤ Hzero L from
      S.toFun.range.le_topologicalClosure.trans_eq (range_closure L S hS))) := by
    apply (denseRange_inclusion_iff (show (S.toFun.range : Set H) ⊆ Hzero L from
      S.toFun.range.le_topologicalClosure.trans_eq (range_closure L S hS))).mpr
    exact (range_closure L S hS).symm.le
  exact hi.comp (quotientRange S).surjective.denseRange
    (continuous_subtype_val.subtype_mk _)

def completionIsometry (L S : Operator 𝕜 H H) (hS : IsNonnegativeSquareRoot L S) :
    DisplacementCompletion S →ₗᵢ[𝕜] Hzero L := (quotientToHzero L S hS).fromCompletion

theorem completionIsometry_surjective (L S : Operator 𝕜 H H)
    (hS : IsNonnegativeSquareRoot L S) : Function.Surjective (completionIsometry L S hS) := by
  have hd : DenseRange (completionIsometry L S hS) := by
    apply (quotientToHzero_dense L S hS).mono
    intro y ⟨q, hq⟩
    refine ⟨displacementEmbedding S q, ?_⟩
    exact ((quotientToHzero L S hS).fromCompletion_apply_coe q).trans hq
  exact Set.range_eq_univ.mp
    ((completionIsometry L S hS).isometry.isClosedEmbedding.isClosed_range.closure_eq.symm.trans
      hd.closure_eq)

def completionEquiv (L S : Operator 𝕜 H H) (hS : IsNonnegativeSquareRoot L S) :
    DisplacementCompletion S ≃ₗᵢ[𝕜] Hzero L :=
  LinearIsometryEquiv.ofSurjective (completionIsometry L S hS)
    (completionIsometry_surjective L S hS)

theorem completion_identification : Spec.CompletionIdentification (𝕜 := 𝕜) (H := H) := by
  intro L S hS
  refine ⟨completionEquiv L S hS, fun u => ?_⟩
  change ((quotientToHzero L S hS).fromCompletion
    ((quotientMap S u : DisplacementQuotient S) : Completion (DisplacementQuotient S)) : H) = S u
  rw [LinearIsometry.fromCompletion_apply_coe]
  rfl


variable [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]

/-- Internal construction data, all obtained below from the actual upstream
spectral calculus. None of these laws are hypotheses of the final theorem. -/
structure GraphEvolution (F : WaveFamily (𝕜 := 𝕜) (H := H)) where
  state : ℝ → (GraphDomain F.S × H) →ₗ[𝕜] (GraphDomain F.S × H)
  position_eq : ∀ t x, position F.S (state t x).1 = F.displacement x.1 x.2 t
  gradient_eq : ∀ t x, gradient F.S (state t x).1 =
    F.cosine t (gradient F.S x.1) + F.sine t x.2
  velocity_eq : ∀ t x, (state t x).2 = F.velocity x.1 x.2 t
  zero : ∀ x, state 0 x = x
  add : ∀ s t x, state (s+t) x = state s (state t x)
  norm_sq : ∀ t u v,
    ‖F.cosine t (gradient F.S u) + F.sine t v‖ ^ 2 + ‖F.velocity u v t‖ ^ 2 =
      ‖gradient F.S u‖ ^ 2 + ‖v‖ ^ 2
  continuous_cosine : ∀ x, Continuous (fun t => F.cosine t x)
  continuous_sine : ∀ x, Continuous (fun t => F.sine t x)

namespace GraphEvolution
section Evolution
variable {L : Operator 𝕜 H H} {F : WaveFamily (𝕜 := 𝕜) (H := H)}
variable (hS : IsNonnegativeSquareRoot L F.S) (G : GraphEvolution F)
include G

lemma cosine_range (t : ℝ) (u : F.S.domain) :
    F.cosine t (F.S u) ∈ F.S.toFun.range := by
  have he := G.gradient_eq t (u, 0)
  simp only [map_zero, add_zero] at he
  exact ⟨GraphDomain.toDomain F.S (G.state t (u, 0)).1, he⟩

lemma sine_range (t : ℝ) (v : H) : F.sine t v ∈ F.S.toFun.range := by
  have he := G.gradient_eq t (0, v)
  simp only [map_zero, zero_add] at he
  exact ⟨GraphDomain.toDomain F.S (G.state t (0, v)).1, he⟩

include hS

lemma cosine_preserves (t : ℝ) (v : Hzero L) : F.cosine t v ∈ Hzero L := by
  apply (range_closure L F.S hS).le
  apply map_mem_closure (F.cosine t).continuous
    (show (v : H) ∈ closure (F.S.toFun.range : Set H) from
      (range_closure L F.S hS).symm.le v.prop)
  rintro _ ⟨u, rfl⟩
  exact G.cosine_range t u

lemma sine_mem (t : ℝ) (v : H) : F.sine t v ∈ Hzero L :=
  (show F.S.toFun.range ≤ Hzero L from
    F.S.toFun.range.le_topologicalClosure.trans_eq (range_closure L F.S hS))
      (G.sine_range t v)

def restrictedCosine (t : ℝ) : Hzero L →L[𝕜] Hzero L :=
  ((F.cosine t).comp (Hzero L).subtypeL).codRestrict _ (G.cosine_preserves hS t)
def restrictedSine (t : ℝ) : Hzero L →L[𝕜] Hzero L :=
  ((F.sine t).comp (Hzero L).subtypeL).codRestrict _ (fun v => G.sine_mem hS t v)

def rotation (t : ℝ) : EnergyCoordinates L →L[𝕜] EnergyCoordinates L :=
  let a := G.restrictedCosine hS t
  let b := G.restrictedSine hS t
  let f := WithLp.fstL 2 𝕜 (Hzero L) (Hzero L)
  let g := WithLp.sndL 2 𝕜 (Hzero L) (Hzero L)
  (WithLp.prodContinuousLinearEquiv 2 𝕜 (Hzero L) (Hzero L)).symm.toContinuousLinearMap.comp
    ((a.comp f + b.comp g).prod ((-b).comp f + a.comp g))

@[simp] lemma rotation_fst (t : ℝ) (x : EnergyCoordinates L) :
    ((G.rotation hS t x).fst : H) = F.cosine t x.fst + F.sine t x.snd := rfl
@[simp] lemma rotation_snd (t : ℝ) (x : EnergyCoordinates L) :
    ((G.rotation hS t x).snd : H) = -F.sine t x.fst + F.cosine t x.snd := rfl

lemma velocity_mem (t : ℝ) (u : GraphDomain F.S) (v : Hzero L) :
    F.velocity u v t ∈ Hzero L := by
  exact (Hzero L).add_mem ((Hzero L).neg_mem (G.sine_mem hS t _))
    (G.cosine_preserves hS t v)

def coreState (t : ℝ) (p : F.S.domain × Hzero L) : F.S.domain × Hzero L :=
  (GraphDomain.toDomain F.S (G.state t (p.1, p.2)).1,
    ⟨(G.state t (p.1, p.2)).2, by
      rw [G.velocity_eq]; exact G.velocity_mem hS t p.1 p.2⟩)

lemma coreState_zero (p : F.S.domain × Hzero L) : G.coreState hS 0 p = p := by
  apply Prod.ext
  · exact congrArg (fun x : GraphDomain F.S × H => GraphDomain.toDomain F.S x.1) (G.zero (p.1, p.2))
  · apply Subtype.ext
    exact congrArg Prod.snd (G.zero (p.1, p.2))

lemma coreState_add (s t : ℝ) (p : F.S.domain × Hzero L) :
    G.coreState hS (s+t) p = G.coreState hS s (G.coreState hS t p) := by
  apply Prod.ext
  · exact congrArg (fun x : GraphDomain F.S × H => GraphDomain.toDomain F.S x.1) (G.add s t (p.1, p.2))
  · apply Subtype.ext
    exact congrArg Prod.snd (G.add s t (p.1, p.2))

end Evolution
end GraphEvolution

@[simp] theorem completionEquiv_apply (L S : Operator 𝕜 H H)
    (hS : IsNonnegativeSquareRoot L S) (u : S.domain) :
    (completionEquiv L S hS (displacementEmbedding S (quotientMap S u)) : H) = S u := by
  change ((quotientToHzero L S hS).fromCompletion
    ((quotientMap S u : DisplacementQuotient S) : Completion (DisplacementQuotient S)) : H) = S u
  rw [LinearIsometry.fromCompletion_apply_coe]
  rfl

theorem originalData_dense (L S : Operator 𝕜 H H) :
    DenseRange (fun p : S.domain × Hzero L => originalData L S p.1 p.2) := by
  have hq : Function.Surjective (quotientMap S) := Submodule.mkQ_surjective (LinearMap.ker S.toFun)
  have he : DenseRange (fun u : S.domain => displacementEmbedding S (quotientMap S u)) :=
    (Completion.denseRange_coe (α := DisplacementQuotient S)).comp
      hq.denseRange
      (Completion.continuous_coe (DisplacementQuotient S))
  exact (WithLp.equiv 2 _).symm.surjective.denseRange.comp
    (he.prodMap denseRange_id) (WithLp.prod_continuous_toLp 2 _ _)

def coreCoordinates (L S : Operator 𝕜 H H) (hS : IsNonnegativeSquareRoot L S)
    (p : S.domain × Hzero L) : EnergyCoordinates L :=
  energyCoordinates L S (completionEquiv L S hS) (originalData L S p.1 p.2)

@[simp] theorem coreCoordinates_fst (L S : Operator 𝕜 H H)
    (hS : IsNonnegativeSquareRoot L S) (p : S.domain × Hzero L) :
    ((coreCoordinates L S hS p).fst : H) = S p.1 := completionEquiv_apply L S hS p.1
@[simp] theorem coreCoordinates_snd (L S : Operator 𝕜 H H)
    (hS : IsNonnegativeSquareRoot L S) (p : S.domain × Hzero L) :
    (coreCoordinates L S hS p).snd = p.2 := rfl

theorem coreCoordinates_dense (L S : Operator 𝕜 H H)
    (hS : IsNonnegativeSquareRoot L S) : DenseRange (coreCoordinates L S hS) :=
  (energyCoordinates L S (completionEquiv L S hS)).surjective.denseRange.comp
    (originalData_dense L S) (energyCoordinates L S (completionEquiv L S hS)).continuous

namespace GraphEvolution
section CompleteEvolution
variable {L : Operator 𝕜 H H} {F : WaveFamily (𝕜 := 𝕜) (H := H)}
variable (hS : IsNonnegativeSquareRoot L F.S) (G : GraphEvolution F)

lemma rotation_core (t : ℝ) (p : F.S.domain × Hzero L) :
    G.rotation hS t (coreCoordinates L F.S hS p) =
      coreCoordinates L F.S hS (G.coreState hS t p) := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext <;> apply Subtype.ext
  · simp only [WithLp.equiv_apply, WithLp.ofLp_fst, rotation_fst,
      coreCoordinates_fst, coreCoordinates_snd, coreState]
    have hg := G.gradient_eq t (p.1, p.2)
    change F.S (GraphDomain.toDomain F.S (G.state t (p.1, p.2)).1) =
      F.cosine t (F.S p.1) + F.sine t p.2 at hg
    exact hg.symm
  · simp only [WithLp.equiv_apply, WithLp.ofLp_snd, rotation_snd,
      coreCoordinates_fst, coreCoordinates_snd, coreState]
    have hv := G.velocity_eq t (p.1, p.2)
    change (G.state t (p.1, p.2)).2 = -F.sine t (F.S p.1) + F.cosine t p.2 at hv
    exact hv.symm

lemma rotation_norm (t : ℝ) (x : EnergyCoordinates L) : ‖G.rotation hS t x‖ = ‖x‖ := by
  apply (coreCoordinates_dense L F.S hS).induction_on (p := fun x => ‖G.rotation hS t x‖ = ‖x‖) x
    (isClosed_eq ((G.rotation hS t).continuous.norm) continuous_norm)
  intro p
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change ‖((G.rotation hS t (coreCoordinates L F.S hS p)).fst : H)‖ ^ 2 +
    ‖((G.rotation hS t (coreCoordinates L F.S hS p)).snd : H)‖ ^ 2 =
    ‖((coreCoordinates L F.S hS p).fst : H)‖ ^ 2 + ‖(p.2 : H)‖ ^ 2
  simp only [rotation_fst, rotation_snd, coreCoordinates_fst, coreCoordinates_snd]
  exact G.norm_sq t p.1 p.2

lemma rotation_zero (x : EnergyCoordinates L) : G.rotation hS 0 x = x := by
  apply (coreCoordinates_dense L F.S hS).induction_on (p := fun x => G.rotation hS 0 x = x) x
    (isClosed_eq (G.rotation hS 0).continuous continuous_id)
  intro p
  rw [G.rotation_core hS, G.coreState_zero hS]

lemma rotation_add (s t : ℝ) (x : EnergyCoordinates L) :
    G.rotation hS (s+t) x = G.rotation hS s (G.rotation hS t x) := by
  apply (coreCoordinates_dense L F.S hS).induction_on (p := fun x => G.rotation hS (s+t) x = G.rotation hS s (G.rotation hS t x)) x
    (isClosed_eq (G.rotation hS (s+t)).continuous
      ((G.rotation hS s).continuous.comp (G.rotation hS t).continuous))
  intro p
  rw [G.rotation_core hS, G.rotation_core hS, G.rotation_core hS, G.coreState_add hS]

lemma rotation_continuous (x : EnergyCoordinates L) : Continuous (fun t => G.rotation hS t x) := by
  change Continuous (fun t => WithLp.toLp 2
    ((G.restrictedCosine hS t x.fst + G.restrictedSine hS t x.snd),
      (-G.restrictedSine hS t x.fst + G.restrictedCosine hS t x.snd)))
  apply (WithLp.prod_continuous_toLp 2 _ _).comp
  apply Continuous.prodMk
  · exact ((G.continuous_cosine (x.fst : H)).add
      (G.continuous_sine (x.snd : H))).subtype_mk _
  · exact ((G.continuous_sine (x.fst : H)).neg.add
      (G.continuous_cosine (x.snd : H))).subtype_mk _

def rotationEquiv (t : ℝ) : EnergyCoordinates L ≃ₗᵢ[𝕜] EnergyCoordinates L :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (G.rotation hS t).toLinearMap
      norm_map' := G.rotation_norm hS t }
    (fun x => ⟨G.rotation hS (-t) x, by
      change G.rotation hS t (G.rotation hS (-t) x) = x
      rw [← G.rotation_add hS, add_neg_cancel, G.rotation_zero hS]⟩)

def completedEvolution (t : ℝ) : EnergySpace L F.S ≃ₗᵢ[𝕜] EnergySpace L F.S :=
  let e := energyCoordinates L F.S (completionEquiv L F.S hS)
  (e.trans (G.rotationEquiv hS t)).trans e.symm

end CompleteEvolution
end GraphEvolution

section Assembly
variable {L : Operator 𝕜 H H} {F : WaveFamily (𝕜 := 𝕜) (H := H)}
variable (hS : IsNonnegativeSquareRoot L F.S) (G : GraphEvolution F)
include hS G

/-- Assemble the completion, the exact restricted PVM rotation and the unique
continuous extension, from established graph-domain wave laws. -/
theorem homogeneous_of_graphEvolution
    (drift : ∃ P : H →L[𝕜] H, IsKernelProjection L P ∧
      ∀ (u : GraphDomain F.S) (v : H) t,
        P (F.displacement u v t) = P (position F.S u) + t • P v) :
    HomogeneousWave L F := by
  let e := energyCoordinates L F.S (completionEquiv L F.S hS)
  refine ⟨hS, completionEquiv L F.S hS, completionEquiv_apply L F.S hS,
    originalData_dense L F.S, G.completedEvolution hS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, drift⟩
  · intro x
    change e.symm (G.rotation hS 0 (e x)) = x
    rw [G.rotation_zero hS, e.symm_apply_apply]
  · intro s t x
    change e.symm (G.rotation hS (s+t) (e x)) =
      e.symm (G.rotation hS s (e (e.symm (G.rotation hS t (e x)))))
    rw [e.apply_symm_apply, G.rotation_add hS]
  · intro x
    exact e.symm.continuous.comp (G.rotation_continuous hS (e x))
  · intro t x y
    exact (G.completedEvolution hS t).inner_map_map x y
  · intro t x
    change ((e (e.symm (G.rotation hS t (e x)))).fst : H) =
      F.cosine t (e x).fst + F.sine t (e x).snd ∧
      ((e (e.symm (G.rotation hS t (e x)))).snd : H) =
        -F.sine t (e x).fst + F.cosine t (e x).snd
    rw [e.apply_symm_apply]
    exact ⟨rfl, rfl⟩
  · intro t u v w hw
    refine ⟨G.velocity_mem hS t u v, ?_⟩
    have hw' : w = (G.state t (u, v)).1 := by
      apply (show Function.Injective (position F.S) from fun _ _ h => Subtype.ext h)
      exact hw.trans (G.position_eq t (u, v)).symm
    apply e.injective
    change e (e.symm (G.rotation hS t
      (coreCoordinates L F.S hS (GraphDomain.toDomain F.S u, v)))) =
      coreCoordinates L F.S hS (GraphDomain.toDomain F.S w,
        ⟨F.velocity u v t, G.velocity_mem hS t u v⟩)
    rw [e.apply_symm_apply, G.rotation_core hS]
    congr 1
    apply Prod.ext
    · exact congrArg (GraphDomain.toDomain F.S) hw'.symm
    · apply Subtype.ext
      exact G.velocity_eq t (u, v)
  · intro t V hV heq
    exact (originalData_dense L F.S).equalizer hV (G.completedEvolution hS t).continuous
      (funext heq)

end Assembly

omit [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H] in
theorem degenerate_energy : Spec.DegenerateEnergy (𝕜 := 𝕜) (H := H) := by
  intro L S hS hker
  have hz : Hzero L = ⊥ := by
    change L.ker.orthogonal = ⊥
    rw [hker, Submodule.top_orthogonal_eq_bot]
  haveI : Subsingleton (Hzero L) := by rw [hz]; infer_instance
  haveI : Subsingleton (DisplacementCompletion S) :=
    (completionEquiv L S hS).injective.subsingleton
  refine ⟨inferInstance, ?_⟩
  exact (WithLp.equiv 2 _).injective.subsingleton

omit [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H] in
theorem zero_operator_energy : Spec.ZeroOperatorEnergy (𝕜 := 𝕜) (H := H) := by
  intro S hS
  exact degenerate_energy (0 : Operator 𝕜 H H) S hS LinearPMap.ker_zero

omit [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H] in
theorem zero_hilbert_energy : Spec.ZeroHilbertEnergy (𝕜 := 𝕜) (H := H) := by
  intro _ L S hS
  apply degenerate_energy L S hS
  exact Subsingleton.elim _ _

end Generic

section Real
open RealNonnegativeSpectralCalculus
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def realGraphEvolution (C : Calculus (H := H)) : GraphEvolution (realFamily C) where
  state := realStateLinear C
  position_eq := realGraphState_position C
  gradient_eq := realGraphState_gradient C
  velocity_eq := realGraphState_velocity C
  zero := realGraphState_zero C
  add := realGraphState_add C
  norm_sq := fun t u v => real_formula_energy C u v t
  continuous_cosine := continuous_cosine_apply C
  continuous_sine := continuous_sine_apply C

theorem real_homogeneous_wave : Spec.RealTheorem.{u} := by
  intro H _ _ _ L hL
  obtain ⟨C, hC, hWave⟩ := real_abstract_wave_energy H L hL
  refine ⟨C, hC, homogeneous_of_graphEvolution hWave.1 (realGraphEvolution C) ?_⟩
  exact hWave.2.2.2.1

end Real

section Complex
open RealNonnegativeSpectralCalculus
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 H}
local instance : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H

def complexGraphEvolution (C : MeasurableSpectralCalculus.BoundedRealization E) :
    GraphEvolution (complexFamily C) where
  state := complexStateLinear C
  position_eq := complexGraphState_position C
  gradient_eq := complexGraphState_gradient C
  velocity_eq := complexGraphState_velocity C
  zero := complexGraphState_zero C
  add := complexGraphState_add C
  norm_sq := fun t u v => complex_formula_energy C u v t
  continuous_cosine := continuous_complex_cosine_apply C
  continuous_sine := continuous_complex_sine_apply C

theorem complex_homogeneous_wave : Spec.ComplexTheorem.{u} := by
  intro H _ _ _ L hL
  letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
  obtain ⟨E, C, hC, hWave⟩ := complex_abstract_wave_energy H L hL
  refine ⟨E, C, hC, homogeneous_of_graphEvolution hWave.1 (complexGraphEvolution C) ?_⟩
  exact hWave.2.2.2.1

end Complex

theorem homogeneous_wave_completion : Spec.FullTheorem.{u} :=
  ⟨real_homogeneous_wave, complex_homogeneous_wave⟩

end ExpandedFA.Models.HomogeneousWaveCompletion
