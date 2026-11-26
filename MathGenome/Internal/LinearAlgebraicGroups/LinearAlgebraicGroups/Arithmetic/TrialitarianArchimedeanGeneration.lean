import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianArchimedeanGeneration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TrialitarianLocalForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinIsotropy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RealDefiniteSpin
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ScalarEvenSpinLocalDensity
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAdelicApproximation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.StrongApproximationF4
import Batteries.Tactic.OpenPrivate

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Topology
open scoped TensorProduct

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianArchimedeanGeneration (ArchimedeanInputs)

universe u

namespace LinearAlgebraicGroups.Arithmetic.TrialitarianArchimedeanGeneration

open AdelicGroups CompactProductIsolation
open Specs.Arithmetic.ProjectiveRecurrence
  (cocharacterRadicalPoints localPointSet parabolicRadicalPoints)
open Specs.Arithmetic.TrialitarianLocalForms (HasPositiveSplitRank IsTrialitarian D4Diagram)
open Specs.GeometricRadicals (IsSemisimple)
open Specs.IntegralModels (MatrixRealization)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open private rankPositiveOfIsotropic mapContracted
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalCompactnessCriterion
open private noncentral_of_contracting_tangent localPlus_eq_radicalClosure
  subsingleton_of_compact_contracted
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAdelicApproximation
open private infiniteNormedField
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.WeakApproximationLocalSmoothImage
open private localPointSet_eq_image from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence
open private diagramAfterScalarExtension simplyConnectedAfterScalarExtension
  isAlgClosed_of_complexEquiv quasiSplit_of_algClosed positiveSplitRank_of_quasiSplit
  absoluteAlmostSimple not_transitive_over_real fixedVectorVertex
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TrialitarianLocalForms
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private asMatrix_isClosedEmbedding from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups

section CompactSpin

open LinearAlgebraicGroups.Albert.CliffordSpecification (coefficientForm)
open LinearAlgebraicGroups.Albert.CliffordModel (coefficientForm_tmul)
open LinearAlgebraicGroups.Albert.SpinSpecification
  (IsSpinPointRepresentation ScalarClifford spinUnits coefficientMap)
open LinearAlgebraicGroups.Albert
open private orderedBasis from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private glEvaluation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open RealDefiniteSpinSpec (IsDefinite spinPoints cliffordPoints)
open Specs.AdjointRepresentation (GroupPoints)
open private matrixPresentation continuous_glEvaluation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private coordinateMap coordinateMap_spec from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels

variable {F : Type u} [Field F]
variable {V : Type u} [AddCommGroup V] [Module F V]
variable {I : Type u} [LinearOrder I] [Fintype I]

private theorem continuousSpinCoordinates [TopologicalSpace F] [IsTopologicalRing F]
    {G : AffineAlgebraicGroup F} (j : MatrixRealization G) (q : QuadraticForm F V)
    (spin : ∀ S : TestAlgebra F, GroupPoints G.val S →* (ScalarClifford q S)ˣ)
    (hspin : IsSpinPointRepresentation q G.val spin)
    (r : F ≃+* ℝ) (hr : Continuous r) :
    letI := r.toRingHom.toAlgebra
    letI := moduleTopology ℝ (ScalarClifford q ℝ)
    Continuous (fun p : PointsIn j F => coefficientMap q F (Algebra.ofId F ℝ)
      (spin (CommAlgCat.of F F) p : ScalarClifford q F)) := by
  letI : Algebra F ℝ := r.toRingHom.toAlgebra
  letI : TopologicalSpace (ScalarClifford q ℝ) := moduleTopology ℝ _
  letI := IsModuleTopology.toContinuousAdd ℝ (ScalarClifford q ℝ)
  letI := IsModuleTopology.toContinuousSMul ℝ (ScalarClifford q ℝ)
  obtain ⟨B, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.property.1
  let A := B.unop
  obtain ⟨a, ha, hcoord⟩ := matrixPresentation A e j
  let eval (p : PointsIn j F) : A ⟶ CommAlgCat.of F F := coordinateMap (p ≫ e.inv)
  have hEval (x : A) : Continuous (fun p : PointsIn j F => (eval p).hom x) := by
    obtain ⟨b, rfl⟩ := ha x
    have he (p : PointsIn j F) : (eval p).hom (a.hom b) = glEvaluation (asMatrix j F p) b :=
      (DFunLike.congr_fun (hcoord F p) b).symm
    simp_rw [he]
    exact (continuous_glEvaluation b).comp continuous_induced_dom
  -- Naturality expresses every spin point by evaluating a single tensor at the universal point.
  have hnat (p : PointsIn j F) :
      spin (CommAlgCat.of F F) p = Units.map (coefficientMap q A (eval p).hom).toMonoidHom
        (spin A e.hom) := by
    let p' : Points G.val.X (CommAlgCat.of F F) := p
    have h := hspin.2 (eval p) e.hom
    change spin (CommAlgCat.of F F) ((testSpec F).map (eval p).op ≫ e.hom) = _ at h
    rwa [show (testSpec F).map (eval p).op = p' ≫ e.inv from coordinateMap_spec _,
      Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  simp_rw [hnat]
  change Continuous (fun p : PointsIn j F =>
    coefficientMap q F (Algebra.ofId F ℝ)
      (coefficientMap q A (eval p).hom (spin A e.hom : ScalarClifford q A)))
  generalize (spin A e.hom : ScalarClifford q A) = z
  induction z using TensorProduct.inductionOn with
  | tmul a c =>
    change Continuous (fun p : PointsIn j F => r ((eval p).hom a) ⊗ₜ[F] c)
    have h (t : ℝ) : t ⊗ₜ[F] c = t • ((1 : ℝ) ⊗ₜ[F] c) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    convert (hr.comp (hEval a)).smul (continuous_const (y := (1 : ℝ) ⊗ₜ[F] c)) using 1
    exact funext (fun p => h (r ((eval p).hom a)))
  | add x y hx hy =>
    simp only [map_add]
    exact hx.add hy

omit [Fintype I] in
private theorem cliffordSpinComparison
    (q : QuadraticForm F V) (b : Module.Basis I F V) [Algebra F ℝ] :
    ∃ e : ScalarClifford q ℝ ≃ₐ[ℝ] CliffordAlgebra (coefficientForm ℝ q b),
      ∀ a : (ScalarClifford q ℝ)ˣ,
        a ∈ spinUnits q ℝ ↔
        Units.map e.toMonoidHom a ∈ spinPoints (coefficientForm ℝ q b) := by
  obtain ⟨e, _, h⟩ := SpinFunctor.intrinsicCriterion q b ℝ
  refine ⟨e, fun a => (h a).trans ?_⟩
  let Q := coefficientForm ℝ q b
  let U := LinearMap.range (CliffordAlgebra.ι Q)
  let g := Units.map e.toMonoidHom a
  let f (x : CliffordAlgebra Q) := (g : CliffordAlgebra Q) * x * ↑g⁻¹
  let k (x : CliffordAlgebra Q) := (↑g⁻¹ : CliffordAlgebra Q) * x * g
  change (_ ∧ _ ∧ f '' U = U) ↔ (_ ∧ _ ∧ Set.MapsTo f U U ∧ Set.MapsTo k U U)
  have hfk (x : CliffordAlgebra Q) : f (k x) = x := by simp [f, k, mul_assoc]
  have hkf (x : CliffordAlgebra Q) : k (f x) = x := by simp [f, k, mul_assoc]
  constructor
  · rintro ⟨he, hn, hf⟩
    refine ⟨he, hn, (fun y hy => hf.le ⟨y, hy, rfl⟩), ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hf.symm ▸ hy
    simpa only [hkf] using hx
  · rintro ⟨he, hn, hf, hk⟩
    exact ⟨he, hn, Set.Subset.antisymm (Set.MapsTo.image_subset hf)
      (fun y hy => ⟨k y, hk hy, hfk y⟩)⟩

private theorem connectedOfDefiniteSpin [TopologicalSpace F] [IsTopologicalRing F]
    {G : AffineAlgebraicGroup F} (j : MatrixRealization G) [CompactSpace (PointsIn j F)]
    (q : QuadraticForm F V) (b : Module.Basis I F V) (hd : 2 ≤ Fintype.card I)
    (r : F ≃+* ℝ) (hr : Continuous r)
    (hq : (∀ x ≠ 0, 0 < r (q x)) ∨ (∀ x ≠ 0, r (q x) < 0))
    (spin : ∀ S : TestAlgebra F, GroupPoints G.val S →* (ScalarClifford q S)ˣ)
    (hspin : IsSpinPointRepresentation q G.val spin) :
    ConnectedSpace (PointsIn j F) := by
  letI : Algebra F ℝ := r.toRingHom.toAlgebra
  let a : F ≃ₐ[F] ℝ := AlgEquiv.ofBijective (Algebra.ofId F ℝ) ⟨r.injective, r.surjective⟩
  let Q := coefficientForm ℝ q b
  letI : Module.Finite ℝ (ℝ ⊗[F] V) := Module.Finite.of_basis (b.baseChange ℝ)
  have hdQ : 2 ≤ Module.finrank ℝ (ℝ ⊗[F] V) := by
    rwa [Module.finrank_eq_card_basis (b.baseChange ℝ)]
  have ht : Function.Surjective (fun x : V => (1 : ℝ) ⊗ₜ[F] x) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul t x =>
      obtain ⟨s, rfl⟩ := r.surjective t
      refine ⟨s • x, ?_⟩
      change (1 : ℝ) ⊗ₜ[F] (s • x) = r s ⊗ₜ[F] x
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      rfl
    | add x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, TensorProduct.tmul_add _ _ _⟩
  have hQ : IsDefinite Q := by
    rcases hq with hq | hq
    · left
      rintro z hz
      obtain ⟨x, rfl⟩ := ht z
      simp only [Q, coefficientForm_tmul, one_mul]
      exact hq x (fun h => hz (by simp [h]))
    · right
      rintro z hz
      obtain ⟨x, rfl⟩ := ht z
      simp only [Q, coefficientForm_tmul, one_mul]
      exact hq x (fun h => hz (by simp [h]))
  obtain ⟨e, he⟩ := cliffordSpinComparison q b
  let S₁ := SpinFunctor.Spin q F b
  let S₂ := SpinFunctor.Spin q ℝ b
  let φ : S₁ ≃ S₂ :=
    { toFun := SpinFunctor.map q b a.toAlgHom
      invFun := SpinFunctor.map q b a.symm.toAlgHom
      left_inv := fun x => by rw [← SpinFunctor.map_comp]; simp
      right_inv := fun x => by rw [← SpinFunctor.map_comp]; simp }
  let g (p : PointsIn j F) : S₁ := ⟨spin (CommAlgCat.of F F) p, by
    change spin (CommAlgCat.of F F) p ∈ spinUnits q F
    rw [← (hspin.1 (CommAlgCat.of F F)).2]
    exact Set.mem_range_self p⟩
  have hg : Function.Bijective g := by
    refine ⟨fun p p' h => (hspin.1 _).1 (congrArg Subtype.val h), ?_⟩
    intro x
    have hx : (x : (ScalarClifford q F)ˣ) ∈ spinUnits q F := x.property
    rw [← (hspin.1 (CommAlgCat.of F F)).2] at hx
    obtain ⟨p, hp⟩ := hx
    exact ⟨p, Subtype.ext hp⟩
  let f (p : PointsIn j F) : CliffordAlgebra Q := e (φ (g p) : (ScalarClifford q ℝ)ˣ)
  have hf : Function.Injective f := fun x y h =>
    hg.1 (φ.injective (Subtype.ext (Units.ext (e.injective h))))
  have hrange : Set.range f = cliffordPoints Q := by
    ext c
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨Units.map e.toMonoidHom (φ (g p)), (he _).mp (φ (g p)).property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      let y := Units.map e.symm.toMonoidHom x
      have hy : Units.map e.toMonoidHom y = x := Units.ext (e.apply_symm_apply _)
      obtain ⟨p, hp⟩ := (φ.surjective.comp hg.2) ⟨y, (he y).mpr (hy ▸ hx)⟩
      exact ⟨p, (congrArg (fun z : S₂ => e (z : (ScalarClifford q ℝ)ˣ)) hp).trans
        (congrArg Units.val hy)⟩
  letI : TopologicalSpace (CliffordAlgebra Q) := moduleTopology ℝ _
  letI : TopologicalSpace (ScalarClifford q ℝ) := moduleTopology ℝ _
  letI : ContinuousAdd (CliffordAlgebra Q) := IsModuleTopology.toContinuousAdd ℝ _
  have hcont : Continuous f := (IsModuleTopology.continuous_of_linearMap e.toLinearMap).comp
    (continuousSpinCoordinates j q spin hspin r hr)
  let c := orderedBasis Q (b.baseChange ℝ)
  let coordinateHomeo : CliffordAlgebra Q ≃ₜ (_ → ℝ) :=
    { toEquiv := c.equivFun.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap c.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap c.equivFun.symm.toLinearMap }
  letI : T2Space (CliffordAlgebra Q) := coordinateHomeo.isEmbedding.t2Space
  let eq : PointsIn j F ≃ cliffordPoints Q := Equiv.ofBijective
    (fun p => ⟨f p, hrange ▸ Set.mem_range_self p⟩)
    ⟨fun _ _ h => hf (congrArg Subtype.val h), fun ⟨x, hx⟩ => by
      rw [← hrange] at hx
      obtain ⟨p, hp⟩ := hx
      exact ⟨p, Subtype.ext hp⟩⟩
  -- Compactness of the matrix point space gives continuity of the inverse comparison.
  let homeo := Continuous.homeoOfEquivCompactToT2 (f := eq) (hcont.subtype_mk _)
  letI : ConnectedSpace (cliffordPoints Q) :=
    isConnected_iff_connectedSpace.mp (RealDefiniteSpin.pathConnected Q hQ hdQ).isConnected
  exact homeo.symm.surjective.connectedSpace homeo.symm.continuous

end CompactSpin

section Archimedean

variable {K : Type u} [Field K] [NumberField K]

open Specs.ExceptionalAdelicApproximation (numberPlaces)

local instance numberCompletionField (w : (numberPlaces K).Place) :
    Field ((numberPlaces K).Completion w) :=
  GlobalFieldData.instFieldCompletion (numberPlaces K) w

local instance numberCompletionTopology (w : (numberPlaces K).Place) :
    TopologicalSpace ((numberPlaces K).Completion w) :=
  GlobalFieldData.instTopologicalSpaceCompletion (numberPlaces K) w

local instance numberCompletionAlgebra (w : (numberPlaces K).Place) :
    Algebra K ((numberPlaces K).Completion w) :=
  completionAlgebra (numberPlaces K) w

private theorem densityOfPositiveSplitRank (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : IsSemisimple G) (hSC : GeometricallySimplyConnected G) (hT : IsTrialitarian G)
    (w : NumberField.InfinitePlace K)
    (hr : HasPositiveSplitRank (baseChangedAlgebraicGroup w.Completion G)) :
    let D : GlobalFieldData.{u,u} K := numberPlaces K
    Dense (Subgroup.closure (localPointSet D i (.inr w)
      (cocharacterRadicalPoints (baseChangedAlgebraicGroup (D.Completion (.inr w)) G))) :
        Set (LocalPoints D i (.inr w))) ∧
    Dense (Subgroup.closure {x : LocalPoints D i (.inr w) | Contracted x} :
      Set (LocalPoints D i (.inr w))) := by
  let D : GlobalFieldData.{u,u} K := numberPlaces K
  let F := w.Completion
  letI : NontriviallyNormedField F := infiniteNormedField w
  letI : Algebra K F := completionAlgebra D (.inr w)
  let H := baseChangedAlgebraicGroup F G
  obtain ⟨_, j₀, _, e₀, he, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison K F G i
  let j : MatrixRealization H := j₀
  let e : PointsIn j F ≃ₜ* LocalPoints D i (.inr w) := e₀
  have hd := TrialitarianLocalForms.localGeneration D G hG hSC hT i (.inr w) hr
  rw [localPlus_eq_radicalClosure] at hd
  have hpar := StrongApproximationF4.parabolicPoints_are_contracted H j
  constructor
  · apply hd.mono (Subgroup.closure_mono ?_)
    rintro _ ⟨p, hp, heq⟩
    exact ⟨p, (hpar hp).1, heq⟩
  · apply hd.mono (Subgroup.closure_mono ?_)
    intro x hx
    have hset := localPointSet_eq_image D i (.inr w) j e he (parabolicRadicalPoints H)
    have hx' : x ∈ localPointSet D i (.inr w) (parabolicRadicalPoints H) := hx
    obtain ⟨p, hp, rfl⟩ := hset ▸ hx'
    exact mapContracted e.toMonoidHom e.continuous (hpar hp).2

private theorem positiveSplitRankOfNoncompact (G : AffineAlgebraicGroup K)
    (i : MatrixRealization G) (hG : IsSemisimple G) (w : NumberField.InfinitePlace K)
    (hn : ¬ CompactSpace (LocalPoints (numberPlaces K) i (.inr w))) :
    HasPositiveSplitRank (baseChangedAlgebraicGroup w.Completion G) := by
  let D : GlobalFieldData.{u,u} K := numberPlaces K
  let F := w.Completion
  letI : Algebra K F := completionAlgebra D (.inr w)
  let H := baseChangedAlgebraicGroup F G
  have hH := (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := F)
    G hG.1 hG.2.1).mpr hG
  obtain ⟨_, j₀, _, e₀, _, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison K F G i
  let j : MatrixRealization H := j₀
  let e : PointsIn j F ≃ₜ* LocalPoints D i (.inr w) := e₀
  have hn' : ¬ CompactSpace (PointsIn j F) := fun h => by
    letI := h
    exact hn (e.surjective.compactSpace e.continuous)
  have hiso := (LocalCompactnessCriterion.localCompactness D rfl (.inr w) H j hH).not.mp hn'
  obtain ⟨T, _, a, L, hv⟩ := LocalCocharacterEvaluation.isotropicContractingLie
    H hH (rankPositiveOfIsotropic H hiso)
  exact ⟨a ≫ T.inclusion, noncentral_of_contracting_tangent L hv⟩

private theorem positiveSplitRankAtComplex (G : AffineAlgebraicGroup K)
    (hG : IsSemisimple G) (hSC : GeometricallySimplyConnected G) (diagram : D4Diagram G)
    (w : NumberField.InfinitePlace K) (hw : w.IsComplex) :
    HasPositiveSplitRank (baseChangedAlgebraicGroup w.Completion G) := by
  let D : GlobalFieldData.{u,u} K := numberPlaces K
  let F := w.Completion
  letI : Algebra K F := completionAlgebra D (.inr w)
  let H := baseChangedAlgebraicGroup F G
  have hH := (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := F)
    G hG.1 hG.2.1).mpr hG
  have hSCH := simplyConnectedAfterScalarExtension diagram hG hSC F
  obtain ⟨d⟩ := diagramAfterScalarExtension diagram F
  letI : IsAlgClosed F := isAlgClosed_of_complexEquiv
    (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)
  exact positiveSplitRank_of_quasiSplit (absoluteAlmostSimple d hH hSCH)
    (quasiSplit_of_algClosed (reductive_of_semisimple H hH))

open Specs.Arithmetic.IsotropicSpinGeneration (IsRegular)
open Specs.Arithmetic.NontrialitarianSpinModels (gramAdjoint)
open private scalarSpinRepresentation reindexGramAdjoint
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ScalarEvenSpinLocalDensity

private theorem connectedOfCompactRealModel {F : Type u} [Field F] [TopologicalSpace F]
    [IsTopologicalRing F] [CharZero F] (H : AffineAlgebraicGroup F) (j : MatrixRealization H)
    (d : D4Diagram H) (hH : IsSemisimple H) (hSC : GeometricallySimplyConnected H)
    (r : F ≃+* ℝ) (hr : IsHomeomorph r) (hc : CompactSpace (PointsIn j F)) :
    ConnectedSpace (PointsIn j F) := by
  classical
  letI := hc
  have hs := absoluteAlmostSimple d hH hSC
  have hv := fixedVectorVertex d (not_transitive_over_real d r)
  obtain ⟨L, _, _, _, _, ρ, M, _, ho, ⟨model⟩⟩ :=
    NontrialitarianSpinModels.nontrialitarianSpinModel F H 4 (by decide) hs hSC hv
  let I := ULift.{u} (Fin 4)
  letI : Nonempty I := ⟨⟨0⟩⟩
  letI : LinearOrder (I ⊕ I) :=
    LinearOrder.lift' (Fintype.equivFin (I ⊕ I)) (Fintype.equivFin (I ⊕ I)).injective
  have h₂ : (2 : F) ≠ 0 := by norm_num
  have hI : 4 ≤ Fintype.card I := by simp [I]
  have hc' : letI : TopologicalSpace F := TopologicalSpace.induced r inferInstance
      IsCompact (Set.univ : Set (PointsIn j F)) := by
    rw [← hr.isInducing.eq_induced]
    exact isCompact_univ
  obtain ⟨n, E, B, q, hn, _, hpol, hreg, hAdj, hdef⟩ :=
    QuaternionSpinIsotropy.compactRealModel H M model hI (ho h₂) F r j hc'
  let E₀ := (Algebra.TensorProduct.lid F ρ.fixedSubalgebra).symm.trans E
  have hE₀ (x : ρ.fixedSubalgebra) :
      E₀ (M.involution.toLinearMap x) = gramAdjoint B (E₀ x) := by
    have hh := hAdj (1 ⊗ₜ[F] x)
    rw [SymplecticIsometryDescent.Involution.baseChange_tmul] at hh
    exact hh
  have hn' : Fintype.card (Fin n) = Fintype.card (I ⊕ I) := by
    simpa [I, Fintype.card_sum, two_mul] using hn
  let s : Fin n ≃ I ⊕ I := Fintype.equivOfCardEq hn'
  let reindex := Matrix.reindexAlgEquiv F F s
  let E₁ := E₀.trans reindex
  let B₁ := Units.map reindex.toMonoidHom B
  let t := LinearEquiv.funCongrLeft F F s
  let q₁ := q.comp t.toLinearMap
  let b := Pi.basisFun F (I ⊕ I)
  have ht (i : I ⊕ I) : t (b i) = Pi.single (s.symm i) 1 := by
    ext k
    simp [t, b, LinearMap.funLeft_apply, Pi.single_apply, s.eq_symm_apply]
  have hB : LinearMap.BilinForm.toMatrix b q₁.polarBilin = B₁.val := by
    ext i k
    simp only [LinearMap.BilinForm.toMatrix_apply, q₁, QuadraticMap.polarBilin_comp,
      LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, ht, hpol]
    change Matrix.toLinearMap₂' F B.val (Pi.single (s.symm i) 1)
      (Pi.single (s.symm k) 1) = _
    exact Matrix.toBilin'_single B.val (s.symm i) (s.symm k)
  have hreg₁ : IsRegular q₁ := by
    left
    rw [show q₁.polarBilin = q.polarBilin.compl₁₂ t.toLinearMap t.toLinearMap from
      QuadraticMap.polarBilin_comp q t.toLinearMap]
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply t.map_eq_zero_iff.mp
    apply hreg.1 (t x)
    intro y
    obtain ⟨z, rfl⟩ := t.surjective y
    exact DFunLike.congr_fun hx z
  have hAdj₁ (x : ρ.fixedSubalgebra) :
      E₁ (M.involution.toLinearMap x) = gramAdjoint B₁ (E₁ x) := by
    change reindex (E₀ (M.involution.toLinearMap x)) = _
    rw [hE₀]
    exact reindexGramAdjoint s B (E₀ x)
  have hdef₁ : (∀ x ≠ 0, 0 < r (q₁ x)) ∨ (∀ x ≠ 0, r (q₁ x) < 0) := by
    rcases hdef with h | h
    · exact Or.inl (fun x hx => h (t x) (fun hz => hx (t.map_eq_zero_iff.mp hz)))
    · exact Or.inr (fun x hx => h (t x) (fun hz => hx (t.map_eq_zero_iff.mp hz)))
  obtain ⟨spin, hspin⟩ := scalarSpinRepresentation b
    NontrialitarianSpinModels.splitProjectiveSpinAction model hs h₂ E₁ B₁ hB hAdj₁ hreg₁
  exact connectedOfDefiniteSpin j q₁ b (by simp [I, Fintype.card_sum]) r hr.continuous hdef₁ spin hspin

private theorem connectedAtCompactReal (G : AffineAlgebraicGroup K)
    (i : MatrixRealization G) (hG : IsSemisimple G) (hSC : GeometricallySimplyConnected G)
    (diagram : D4Diagram G) (w : NumberField.InfinitePlace K) (hw : w.IsReal)
    (hc : CompactSpace (LocalPoints (numberPlaces K) i (.inr w))) :
    ConnectedSpace (LocalPoints (numberPlaces K) i (.inr w)) := by
  let D : GlobalFieldData.{u,u} K := numberPlaces K
  let F := w.Completion
  letI : NontriviallyNormedField F := infiniteNormedField w
  letI : Algebra K F := completionAlgebra D (.inr w)
  let H := baseChangedAlgebraicGroup F G
  have hH := (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := F)
    G hG.1 hG.2.1).mpr hG
  have hSCH := simplyConnectedAfterScalarExtension diagram hG hSC F
  obtain ⟨d⟩ := diagramAfterScalarExtension diagram F
  obtain ⟨_, j₀, _, e₀, _, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison K F G i
  let j : MatrixRealization H := j₀
  let e : PointsIn j F ≃ₜ* LocalPoints D i (.inr w) := e₀
  let r := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hr : IsHomeomorph r :=
    (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph.isHomeomorph
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  letI := hc
  letI := connectedOfCompactRealModel H j d hH hSCH r hr
    (e.symm.surjective.compactSpace e.symm.continuous)
  exact e.surjective.connectedSpace e.continuous

/-- Archimedean generation and compact connectedness in the given adelic realization. -/
theorem archimedeanInputs : ArchimedeanInputs.{u} := by
  intro K _ hK D hD G hG hSC hT i w
  subst D
  obtain ⟨diagram, hdiagram⟩ := hT
  rcases w.isReal_or_isComplex with hw | hw
  · exact ⟨fun hn => densityOfPositiveSplitRank G i hG hSC ⟨diagram, hdiagram⟩ w
      (positiveSplitRankOfNoncompact G i hG w hn),
      connectedAtCompactReal G i hG hSC diagram w hw⟩
  · have hd := densityOfPositiveSplitRank G i hG hSC ⟨diagram, hdiagram⟩ w
      (positiveSplitRankAtComplex G hG hSC diagram w hw)
    refine ⟨fun _ => hd, fun hc => ?_⟩
    let D : GlobalFieldData.{u,u} K := numberPlaces K
    let F := w.Completion
    letI : NontriviallyNormedField F := infiniteNormedField w
    letI : Algebra K F := completionAlgebra D (.inr w)
    have hc' : CompactSpace (PointsIn i F) := hc
    letI := hc'
    letI : T2Space (PointsIn i F) :=
      (asMatrix_isClosedEmbedding i F).isEmbedding.t2Space
    have hd' : Dense (Subgroup.closure {x : PointsIn i F | Contracted x} :
        Set (PointsIn i F)) := hd.2
    letI : Subsingleton (PointsIn i F) := subsingleton_of_compact_contracted hd'
    exact (inferInstance : ConnectedSpace (PointsIn i F))

end Archimedean

end LinearAlgebraicGroups.Arithmetic.TrialitarianArchimedeanGeneration
