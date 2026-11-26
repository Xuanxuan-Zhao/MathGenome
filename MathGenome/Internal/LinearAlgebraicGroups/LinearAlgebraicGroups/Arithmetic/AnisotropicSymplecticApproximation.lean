import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AnisotropicSymplecticApproximation
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicTensorQuotients
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.UnitaryCayleyChart
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.CompactProductIsolation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuotientTransport
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalCocharacterEvaluation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AlmostEverywhereSplitAlgebras
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RationalRealization
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicTypeC
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Batteries.Tactic.OpenPrivate


import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure
set_option Elab.async false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MeasureTheory Topology
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct RestrictedProduct Matrix Classical Polynomial

universe u v

namespace LinearAlgebraicGroups.Arithmetic.AnisotropicSymplecticApproximation

open Specs.Arithmetic.AnisotropicSymplecticApproximation
open Specs.Arithmetic.LocalProjectedClosure (LocalNormalClosure FiniteCovolumeSubgroup)
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.Arithmetic.LocalQuotientMixing (MixingCases)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open Specs.IntegralModels (MatrixRealization)
open Specs.Unipotent (Index baseChangedAlgebraicGroup)
open AdelicGroups (Adeles LocalPoints Outside StrongApproximation localSubgroup PointsIn asMatrix localPoint)
open ArithmeticLatticeProjection (FinitePoints diagonalSubgroup lattice forgetPlaces FiniteInvariantQuotientMeasure)
open CompactProductIsolation (Contracted insertFinite diagonalClosure projectedArithmetic)
open LocalQuotientTransport (RightCosets RightInvariant coset rightTranslate imageSubgroup)
open LocalAlgebraicTransport (pointTopology RationalPoints evaluation)
open Specs.StandardGroups (GLCoordinates universalMatrix)
open private coordinateMap coordinateMap_spec from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels
open private glEvaluation glEvaluation_entry from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private matrixPresentation glVal_isEmbedding continuous_glEvaluation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups

/-- Inversion takes the invariant measure on `P ⧸ H` to a right-invariant
measure on `H ∖ P`. -/
theorem rightInvariantMeasureOfFiniteQuotient {P : Type u} [Group P]
    [TopologicalSpace P] [IsTopologicalGroup P] (H : Subgroup P)
    (h : FiniteInvariantQuotientMeasure H) :
    ∃ ν : Measure (RightCosets H), IsFiniteMeasure ν ∧ ν ≠ 0 ∧ RightInvariant ν := by
  unfold FiniteInvariantQuotientMeasure at h
  borelize (P ⧸ H)
  obtain ⟨ν, hfin, hpos, hinv⟩ := h
  let q : P ⧸ H → RightCosets H := Quotient.map' Inv.inv (by
    intro x y hxy
    rw [QuotientGroup.rightRel_apply, inv_inv]
    simpa only [mul_inv_rev, inv_inv] using H.inv_mem (QuotientGroup.leftRel_apply.mp hxy))
  have hq : Continuous q := continuous_quot_map _ continuous_inv
  have hμ : ν ≠ 0 := by
    intro hz
    have hpos' : 0 < ν Set.univ := isOpen_univ.measure_pos ν Set.univ_nonempty
    simp [hz] at hpos'
  refine ⟨ν.map q, inferInstance, (Measure.map_ne_zero_iff hq.measurable.aemeasurable).mpr hμ, ?_⟩
  intro a
  have ha : Measurable (rightTranslate (H := H) a) :=
    ((LocalQuotientTransport.quotient_action H).2.2.comp
      (continuous_id.prodMk continuous_const)).measurable
  have hsmul : Measurable (a⁻¹ • · : P ⧸ H → P ⧸ H) :=
    (continuous_const_smul _).measurable
  have he : rightTranslate a ∘ q = q ∘ (a⁻¹ • ·) := by
    funext z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    change coset H (g⁻¹ * a) = coset H ((a⁻¹ * g)⁻¹)
    rw [mul_inv_rev, inv_inv]
  refine ⟨ha, ?_⟩
  rw [Measure.map_map ha hq.measurable, he, ← Measure.map_map hq.measurable hsmul]
  congr 1
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hsmul hs, measure_preimage_smul ν a⁻¹ s]

/-- Apply the conditional finite-covolume input under a topological group
comparison with the original affine points over the local field. -/
theorem fullProjectionOfLocalModel (hfull : FiniteCovolumeSubgroup.{u})
    {F P : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    (J : AffineAlgebraicGroup F) (hJ : IsAbsolutelyAlmostSimple J) (hmix : MixingCases J)
    (H : Subgroup P) (hclosed : IsClosed (H : Set P)) (hnd : ¬ DiscreteTopology H)
    (hμ : FiniteInvariantQuotientMeasure H) :
    letI := pointTopology J.val.X
    IsTopologicalGroup (RationalPoints J.val.X) →
    (P ≃ₜ* RationalPoints J.val.X) → H = ⊤ := by
  let _ := pointTopology J.val.X
  intro htop e
  let : IsTopologicalGroup (RationalPoints J.val.X) := htop
  obtain ⟨ν, hfin, hpos, hinv⟩ := rightInvariantMeasureOfFiniteQuotient H hμ
  have := hfin
  obtain ⟨hm, hc, hd⟩ := LocalQuotientTransport.subgroup_transport e H
  obtain ⟨q, _, hq⟩ := LocalQuotientTransport.quotient_transport e H
  obtain ⟨hfin', hpos', hinv', _⟩ :=
    LocalQuotientTransport.measure_transport e q hq ν hinv hpos
  have := hfin'
  have he := hfull F J hJ hmix (imageSubgroup e H) (hc.mp hclosed) (hnd ∘ hd.mpr)
    (ν.map q) hpos' hinv'
  apply top_unique
  intro x _
  exact (hm x).mp (he ▸ Subgroup.mem_top (e x))

/-- The projected arithmetic subgroup is dense if its nondiscrete closed
finite-covolume closure is the whole product. The contraction argument then
embeds every element of the product in the adelic diagonal closure. -/
theorem isolateFactorsOfFullProjection {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (S J : Finset D.Place) (hJ : J.Nonempty) (hd : Disjoint J S)
    (U : Subgroup (Adeles D i (S ∪ J)))
    (hU : IsCompact (U : Set (Adeles D i (S ∪ J))))
    (hU' : IsOpen (U : Set (Adeles D i (S ∪ J))))
    (hcompact : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hnoncompact : ¬ CompactSpace (FinitePoints D i S))
    (hfull : ∀ H : Subgroup (FinitePoints D i J),
      IsClosed (H : Set (FinitePoints D i J)) → ¬ DiscreteTopology H →
      FiniteInvariantQuotientMeasure H → H = ⊤)
    (hcontract : Dense (Subgroup.closure {x : FinitePoints D i J | Contracted x} :
      Set (FinitePoints D i J))) :
    ∀ x : FinitePoints D i J, insertFinite D i S J x ∈ diagonalClosure D i S := by
  obtain ⟨hnd, H, hH, _, hμ⟩ := ArithmeticLatticeProjection.projectionProperties
    D i S (S ∪ J) J U Finset.subset_union_left Finset.subset_union_right
    hcompact hnoncompact hJ hd hU hU'
  have hclosed : IsClosed (H : Set (FinitePoints D i J)) := by rw [hH]; exact isClosed_closure
  have hnd' : ¬ DiscreteTopology H := by
    intro h
    apply hnd
    have hi : (projectedArithmetic D i S J U : Set (FinitePoints D i J)) ⊆ H := by
      rw [hH]
      exact subset_closure
    exact (isDiscrete_iff_discreteTopology.mpr h).mono hi
  have htop := hfull H hclosed hnd' hμ
  have hP : Dense (projectedArithmetic D i S J U : Set (FinitePoints D i J)) := by
    rw [dense_iff_closure_eq]
    calc
      _ = (H : Set (FinitePoints D i J)) := hH.symm
      _ = Set.univ := by rw [htop, Subgroup.coe_top]
  exact (CompactProductIsolation.isolateAdelicFactors D i S J hd U hU hU').2 hP hcontract

/-- With compact archimedean factors outside the omitted set, singleton
arithmetic projections suffice away from a finite set of exceptions. -/
theorem strongApproximationOfLocalProjections {K : Type u} [Field K]
    {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (S J : Finset D.Place) (hd : Disjoint J S)
    (harch : ∀ w : D.InfinitePlace, Sum.inr w ∉ S → CompactSpace (LocalPoints D i (.inr w)))
    (hcompact : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hnoncompact : ¬ CompactSpace (FinitePoints D i S))
    (hfull : ∀ w : Outside D S, w.1 ∉ J → ∀ H : Subgroup (FinitePoints D i {w.1}),
      IsClosed (H : Set (FinitePoints D i {w.1})) → ¬ DiscreteTopology H →
      FiniteInvariantQuotientMeasure H → H = ⊤)
    (hcontract : ∀ w : Outside D S, w.1 ∉ J →
      Dense (Subgroup.closure {x : FinitePoints D i {w.1} | Contracted x} :
        Set (FinitePoints D i {w.1})))
    (hrem : DenseRange (ArithmeticLatticeProjection.rationalProjection D i J)) :
    StrongApproximation D i S := by
  have hsingle (w : Outside D S) (hw : w.1 ∉ J) (a : LocalPoints D i w.1) :
      RestrictedProduct.mulSingle (fun k : Outside D S => localSubgroup D i k.1) w a ∈
        diagonalClosure D i S := by
    let T : Finset D.Place := {w.1}
    have hT : Disjoint T S := by simpa [T] using w.2
    let U := ArithmeticLatticeProjection.integralOutside D i (S ∪ T)
    obtain ⟨hUc, hUo⟩ := ArithmeticLatticeProjection.compactOpenOutside D i (S ∪ T)
      fun x hx => harch x (fun hx' => hx (Finset.mem_union_left _ hx'))
    have hins := isolateFactorsOfFullProjection D i S T ⟨w.1, Finset.mem_singleton_self _⟩
      hT U hUc hUo hcompact hnoncompact (hfull w hw) (hcontract w hw)
    obtain ⟨x, hx⟩ := CompactProductIsolation.mulSingle_mem_range_insertFinite D i hT w
      (Finset.mem_singleton_self _) a
    exact hx ▸ hins x
  exact ((CompactProductIsolation.projectToRemainingPlaces D i S J hd).2 hsingle).2.2.mp hrem

set_option backward.isDefEq.respectTransparency false in
/-- A singleton subproduct of completions is the original local point group. -/
def singletonLocalPoints {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.Place) :
    FinitePoints D i {w} ≃ₜ* LocalPoints D i w := by
  let w₀ : (↑({w} : Finset D.Place) : Set D.Place) := ⟨w, Finset.mem_singleton_self _⟩
  letI : Unique (↑({w} : Finset D.Place) : Set D.Place) :=
    ⟨⟨w₀⟩, fun x => Subtype.ext (Finset.mem_singleton.mp x.property)⟩
  let A := fun x : (↑({w} : Finset D.Place) : Set D.Place) => LocalPoints D i x.1
  let e := MulEquiv.piUnique A
  let h := Homeomorph.piUnique A
  exact { toMulEquiv := e, continuous_toFun := h.continuous, continuous_invFun := h.symm.continuous }

set_option backward.isDefEq.respectTransparency false in
private theorem localPointTopology_eq_matrixTopology {F : Type u} [Field F]
    [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (J : AffineAlgebraicGroup F) (j : MatrixRealization J) :
    pointTopology J.val.X = (inferInstance : TopologicalSpace (PointsIn j F)) := by
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr J.prop.1
  let coords : Γ(J.val.X.left, ⊤) ⟶ CommRingCat.of A.unop :=
    e.hom.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A.unop)).hom
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have hg : Function.Surjective coords := ConcreteCategory.bijective_of_isIso coords |>.2
  let evalAt (p : RationalPoints J.val.X) := (coordinateMap (p ≫ e.inv)).hom
  have heval (p : RationalPoints J.val.X) (a : Γ(J.val.X.left, ⊤)) :
      evaluation p a = evalAt p (coords a) := by
    let f := coordinateMap (p ≫ e.inv)
    have hf := congrArg Over.Hom.left (coordinateMap_spec (p ≫ e.inv))
    rw [algSpec_map_left] at hf
    have hp : (p ≫ e.inv) ≫ e.hom = p := by simp
    have hcomp : e.hom.left.appTop ≫ (p ≫ e.inv).left.appTop = p.left.appTop := by
      rw [← Scheme.Hom.comp_appTop]
      exact congrArg (fun m => m.left.appTop) hp
    change Spec.map (CommRingCat.ofHom f.hom.toRingHom) = (p ≫ e.inv).left at hf
    change (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom) a = f.hom (coords a)
    rw [← hcomp, Category.assoc, ← hf, Scheme.ΓSpecIso_naturality]
    rfl
  obtain ⟨d, hsurj, hd⟩ := matrixPresentation A.unop e j
  let mat := fun p : PointsIn j F => (asMatrix j F p).val
  have hm : IsInducing mat := glVal_isEmbedding.isInducing.comp (IsInducing.induced (asMatrix j F))
  apply le_antisymm
  · rw [hm.eq_induced]
    apply continuous_iff_le_induced.mp
    let _ := pointTopology J.val.X
    apply continuous_matrix
    intro k l
    let z := universalMatrix F (Index.{u} j.size) k l
    obtain ⟨b, hb⟩ := hg (d.hom z)
    have h (p : RationalPoints J.val.X) : (mat p) k l = evaluation p b := by
      rw [heval, hb]
      have hc := congrArg (fun f : GLCoordinates F (Index.{u} j.size) →ₐ[F] F => f z) (hd F p)
      exact (glEvaluation_entry (asMatrix j F p) k l).symm.trans hc
    simp_rw [h]
    exact (continuous_apply b).comp continuous_induced_dom
  · apply continuous_iff_le_induced.mp
    apply continuous_pi
    intro a
    simp_rw [heval]
    obtain ⟨z, hz⟩ := hsurj (coords a)
    have he (p : PointsIn j F) : evalAt p (coords a) = glEvaluation (asMatrix j F p) z := by
      rw [← hz]
      exact congrArg (fun f : GLCoordinates F (Index.{u} j.size) →ₐ[F] F => f z) (hd F p).symm
    simp_rw [he]
    exact (continuous_glEvaluation (R := F) z).comp (IsInducing.induced (asMatrix j F)).continuous


private theorem completionMatrixComparison {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.Place) :
    ∃ j : MatrixRealization (baseChangedAlgebraicGroup (D.Completion w) G),
      Nonempty (PointsIn j (D.Completion w) ≃ₜ* LocalPoints D i w) := by
  let F := D.Completion w
  obtain ⟨j, hj⟩ := LocalCocharacterEvaluation.completionPointTopology (F := F) G i
  let e : PointsIn j F ≃* LocalPoints D i w :=
    baseChangePointGroupEquiv F G.val (CommAlgCat.of F F)
  let l : PointsIn j F ≃ₜ LocalPoints D i w := hj.homeomorph _
  refine ⟨j, ⟨{
    toMulEquiv := e
    continuous_toFun := l.continuous
    continuous_invFun := ?_ }⟩⟩
  have he : (e.symm : LocalPoints D i w → PointsIn j F) = l.symm := by
    funext x
    apply e.injective
    exact (e.apply_symm_apply x).trans (l.apply_symm_apply x).symm
  change Continuous (e.symm : LocalPoints D i w → PointsIn j F)
  rw [he]
  exact l.symm.continuous

/-- The two point topologies used by the arithmetic and local quotient
theorems give a topological group identification over the actual completion. -/
theorem completionPointsComparison {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.Place) :
    let J := baseChangedAlgebraicGroup (D.Completion w) G
    letI := pointTopology J.val.X
    Nonempty (LocalPoints D i w ≃ₜ* RationalPoints J.val.X) := by
  let F := D.Completion w
  let J := baseChangedAlgebraicGroup F G
  obtain ⟨j, ⟨d⟩⟩ := completionMatrixComparison D i w
  let hasComparison (t : TopologicalSpace (PointsIn j F)) : Prop :=
    letI := t
    Nonempty (LocalPoints D i w ≃ₜ* PointsIn j F)
  have htop := localPointTopology_eq_matrixTopology J j
  have hd : hasComparison (inferInstance : TopologicalSpace (PointsIn j F)) := ⟨d.symm⟩
  exact (congrArg hasComparison htop).mpr hd

/-- For a finite completion satisfying the local mixing hypotheses, apply the
finite-covolume premise to the subgroup obtained by arithmetic projection. -/
theorem fullProjectionOfFiniteCompletion (hfull : FiniteCovolumeSubgroup.{u})
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.FinitePlace)
    (hG : IsAbsolutelyAlmostSimple G)
    (hmix : MixingCases (baseChangedAlgebraicGroup (D.Completion (.inl w)) G))
    (H : Subgroup (FinitePoints D i {Sum.inl w}))
    (hclosed : IsClosed (H : Set (FinitePoints D i {Sum.inl w})))
    (hnd : ¬ DiscreteTopology H) (hμ : FiniteInvariantQuotientMeasure H) : H = ⊤ := by
  let F := D.Completion (.inl w)
  let _ : Algebra K F := AdelicGroups.completionAlgebra D (.inl w)
  let _ : ValuativeRel F := inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
  let : IsNonarchimedeanLocalField F := GlobalFieldData.finiteCompletion_isLocalField D w
  let L := baseChangedAlgebraicGroup F G
  let _ := pointTopology L.val.X
  obtain ⟨e⟩ := completionPointsComparison D i (.inl w)
  have hL := OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G hG
  have htop := LocalAlgebraicTransport.rationalPointTopologicalGroup L
  exact fullProjectionOfLocalModel hfull L hL hmix H hclosed hnd hμ htop
    ((singletonLocalPoints D i (.inl w)).trans e)

open SymplecticIsometryDescent (Involution PointsOf isometryPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (IsSemisimple)
open private central_iff_comp_eq_zero cocharacter_into_finite_is_zero reductive_of_semisimple
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank
open private liftToSchemeKernel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel

private theorem noncentral_of_nontrivial_cocharacter {F : Type u} [Field F]
    (G : AffineAlgebraicGroup F) (hG : IsSemisimple G) (c : Cocharacter G.val)
    (hc : c ≠ 0) : Specs.Arithmetic.OppositeRadicals.IsNoncentral c := by
  have hR := reductive_of_semisimple G hG
  obtain ⟨Z, Q, q, hq, _⟩ := Descent.AdjointCocharacters.adjointQuotientExists G hR
  by_contra hcentral
  have hcentral' : Specs.RelativeRank.IsCentralCocharacter c := by
    intro X g
    by_contra hg
    exact hcentral ⟨X, g, hg⟩
  obtain ⟨a, ha⟩ := liftToSchemeKernel hq.2.1 c ((central_iff_comp_eq_zero hq c).mp hcentral')
  have hfin := (Reductive.CentralDerived.semisimpleIffFiniteCentre G hR Z hq.1).mp hG
  have hz := cocharacter_into_finite_is_zero (Specs.Unipotent.closedSubgroupAlgebraicGroup Z) hfin a
  exact hc (ha.symm.trans ((congrArg (fun a => a ≫ Z.inclusion) hz).trans zero_comp))

private theorem involutionAnisotropic {K A : Type u} [Field K] [Ring A] [Algebra K A]
    (s : Involution K A) (G : AffineAlgebraicGroup K)
    (comparison : PointsOf G.val ≅ isometryPoints s)
    (hs : IsSemisimple G) (ha : GloballyAnisotropic G) :
    Specs.AnisotropicSymplecticInvolutionTensors.IsAnisotropic s := by
  rintro ⟨c, hc⟩
  let M := StandardGroups.multiplicativeGroup K
  let m := StandardGroups.multiplicativeGroupPointsIso K
  let e := AffineAlgebraicGroup.groupHomEquiv M G
  let f := e.symm (m.hom ≫ c ≫ comparison.inv)
  let d : Cocharacter G.val := (DiagonalizableGroups.multiplicativeGroupIso K).hom ≫ f
  apply ha
  refine ⟨d, noncentral_of_nontrivial_cocharacter G hs d ?_⟩
  intro hd
  have hf : f = 0 := by
    calc
      f = (DiagonalizableGroups.multiplicativeGroupIso K).inv ≫ d := by simp [d]
      _ = 0 := by rw [hd, comp_zero]
  have hnatural : (groupPointsFunctor K).map f = m.hom ≫ c ≫ comparison.inv :=
    e.apply_symm_apply _
  let R := CommAlgCat.of K (LaurentPolynomial K)
  let t : Rˣ := (LaurentPolynomial.isUnit_T (R := K) 1).unit
  have hft : ∀ t₁ t₂ : Rˣ, c.app R t₁ = c.app R t₂ := by
    intro t₁ t₂
    apply (ConcreteCategory.bijective_of_isIso (comparison.inv.app R)).1
    have hp (t : Rˣ) : comparison.inv.app R (c.app R t) =
        (m.hom ≫ c ≫ comparison.inv).app R (m.inv.app R t) := by
      change _ = comparison.inv.app R (c.app R (m.hom.app R (m.inv.app R t)))
      exact congrArg (fun x => comparison.inv.app R (c.app R x))
        (GrpCat.hom_inv_apply (m.app R) t).symm
    rw [hp t₁, hp t₂, ← hnatural, hf]
    change (m.inv.app R t₁) ≫ (0 : M.val ⟶ G.val).hom.hom =
      (m.inv.app R t₂) ≫ (0 : M.val ⟶ G.val).hom.hom
    change (m.inv.app R t₁) ≫ toUnit M.val.X ≫ η[G.val.X] =
      (m.inv.app R t₂) ≫ toUnit M.val.X ≫ η[G.val.X]
    let X := (testSpec K).obj (op R)
    let p (t : Rˣ) : X ⟶ M.val.X := m.inv.app R t
    change p t₁ ≫ toUnit M.val.X ≫ η[G.val.X] = p t₂ ≫ toUnit M.val.X ≫ η[G.val.X]
    simp only [← Category.assoc]
    exact congrArg (fun z => z ≫ η[G.val.X])
      (toUnit_unique (p t₁ ≫ toUnit M.val.X) (p t₂ ≫ toUnit M.val.X))
  have ht := hc R (hft t 1)
  have he := congrArg (fun z : Rˣ => LaurentPolynomial.degree (z : LaurentPolynomial K)) ht
  change LaurentPolynomial.degree ((LaurentPolynomial.isUnit_T (R := K) 1).unit : LaurentPolynomial K)
    = LaurentPolynomial.degree (1 : LaurentPolynomial K) at he
  rw [IsUnit.unit_spec, ← LaurentPolynomial.T_zero, LaurentPolynomial.degree_T,
    LaurentPolynomial.degree_T] at he
  exact (by decide : (1 : WithBot ℤ) ≠ 0) he

section MatrixRealization

open Specs.StandardGroups (generalLinearPoints)
open private closedImmersion_of_injective_test_points
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RationalRealization

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K}

private def realizationOfNaturalMatrices (n : ℕ)
    (a : PointsOf G.val ⟶ generalLinearPoints K (Index.{u} n))
    (ha : ∀ R, Function.Injective (a.app R)) : MatrixRealization G := by
  let M := StandardGroups.generalLinearGroup K (Index.{u} n)
  let c := StandardGroups.generalLinearGroupPointsIso K (Index.{u} n)
  let e := AffineAlgebraicGroup.groupHomEquiv G M
  let f := e.symm (a ≫ c.inv)
  have hf : (groupPointsFunctor K).map f ≫ c.hom = a := by
    have he : (groupPointsFunctor K).map f = a ≫ c.inv := e.apply_symm_apply _
    rw [he, Category.assoc, c.inv_hom_id, Category.comp_id]
  refine ⟨n, M, c, f, ?_⟩
  apply closedImmersion_of_injective_test_points f
  intro R p q hpq
  apply ha R
  rw [← hf]
  change c.hom.app R (p ≫ f.hom.hom) = c.hom.app R (q ≫ f.hom.hom)
  exact congrArg (fun z => c.hom.app R z) hpq

set_option backward.isDefEq.respectTransparency false in
private theorem asMatrix_realizationOfNaturalMatrices (n : ℕ)
    (a : PointsOf G.val ⟶ generalLinearPoints K (Index.{u} n))
    (ha : ∀ R, Function.Injective (a.app R))
    (R : Type u) [CommRing R] [Algebra K R] (g : PointsIn (realizationOfNaturalMatrices n a ha) R) :
    asMatrix (realizationOfNaturalMatrices n a ha) R g = a.app (CommAlgCat.of K R) g := by
  let M := StandardGroups.generalLinearGroup K (Index.{u} n)
  let c := StandardGroups.generalLinearGroupPointsIso K (Index.{u} n)
  let e := AffineAlgebraicGroup.groupHomEquiv G M
  let f := e.symm (a ≫ c.inv)
  have hf : (groupPointsFunctor K).map f ≫ c.hom = a := by
    have he : (groupPointsFunctor K).map f = a ≫ c.inv := e.apply_symm_apply _
    rw [he, Category.assoc, c.inv_hom_id, Category.comp_id]
  exact congrArg (fun h => h.app (CommAlgCat.of K R) g) hf

end MatrixRealization

section ColumnRepresentation

open Specs.AnisotropicTensorQuotients
  (columnBasis matrixColumnAction matrixOfUnits symplecticMatrixModel)
open Specs.DivisionOctonionOrthogonalTensors (matrixCoordinates)
open private columnBasis_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicTensorQuotients
open Specs.StandardGroups (generalLinearPoints)
open scoped BigOperators

variable {K A B : Type u} [Field K] [Ring A] [Algebra K A] [DivisionRing B] [Algebra K B]
  {r : ℕ} {J : Type u} [Fintype J] [DecidableEq J]
  (b : Module.Basis J K B)
  (E : ∀ (R : Type u) [CommRing R] [Algebra K R],
    (R ⊗[K] A) ≃ₐ[R] Matrix (Fin r) (Fin r) (R ⊗[K] B))

private def columnMatrix (R : Type u) [CommRing R] [Algebra K R] :
    (R ⊗[K] A) →ₐ[R] Matrix (Fin r × J) (Fin r × J) R :=
  (LinearMap.toMatrixAlgEquiv (columnBasis (I := Fin r) (b.baseChange R))).toAlgHom.comp
    (matrixColumnAction.comp (E R).toAlgHom)

private theorem columnMatrix_units (R : Type u) [CommRing R] [Algebra K R] (g : (R ⊗[K] A)ˣ) :
    (matrixOfUnits (columnBasis (I := Fin r) (b.baseChange R))
      (matrixColumnAction.comp (E R).toAlgHom) g).val = columnMatrix b E R g.val := rfl

private theorem columnMatrix_injective (R : Type u) [CommRing R] [Algebra K R] :
    Function.Injective (columnMatrix b E R) := by
  intro x y h
  apply (E R).injective
  have hxy : matrixColumnAction (E R x) = matrixColumnAction (E R y) :=
    (LinearMap.toMatrixAlgEquiv (columnBasis (I := Fin r) (b.baseChange R))).injective h
  ext i j
  have he := congrArg (fun (m : Module.End R (Fin r → R ⊗[K] B)) =>
    m (Pi.single j 1) i) hxy
  change (E R x *ᵥ Pi.single j 1) i = (E R y *ᵥ Pi.single j 1) i at he
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using he

private theorem columnMatrix_entry (R : Type u) [CommRing R] [Algebra K R]
    (x : R ⊗[K] A) (i j : Fin r) (a d : J) :
    columnMatrix b E R x (i, a) (j, d) =
      (b.baseChange R).repr (E R x i j * (1 ⊗ₜ[K] b d)) a := by
  classical
  change LinearMap.toMatrix _ _ (matrixColumnAction (E R x)) (i, a) (j, d) = _
  rw [LinearMap.toMatrix_apply, columnBasis_apply, Module.Basis.baseChange_apply]
  change (b.baseChange R).repr ((E R x).mulVec (Pi.single j (1 ⊗ₜ[K] b d)) i) a = _
  rw [Matrix.mulVec_single]
  rfl

private theorem columnMatrix_tmul (R : Type u) [CommRing R] [Algebra K R]
    (e : A ≃ₐ[K] Matrix (Fin r) (Fin r) B)
    (hE : ∀ (R : Type u) [CommRing R] [Algebra K R] (a : A),
      E R (1 ⊗ₜ[K] a) = (e a).map (Specs.SymplecticDivisionForms.intoTensor R B))
    (x : A) (i j : Fin r) (a d : J) :
    columnMatrix b E R (1 ⊗ₜ[K] x) (i, a) (j, d) =
      algebraMap K R (b.repr (e x i j * b d) a) := by
  rw [columnMatrix_entry, hE R x]
  change (b.baseChange R).repr (((1 : R) ⊗ₜ[K] e x i j) * (1 ⊗ₜ[K] b d)) a = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]

private theorem columnMatrix_naturality
    (e : A ≃ₐ[K] Matrix (Fin r) (Fin r) B)
    (hE : ∀ (R : Type u) [CommRing R] [Algebra K R] (a : A),
      E R (1 ⊗ₜ[K] a) = (e a).map (Specs.SymplecticDivisionForms.intoTensor R B))
    {R S : TestAlgebra K} (f : R ⟶ S) (x : R ⊗[K] A) :
    columnMatrix b E S (SymplecticIsometryDescent.tensorMap (A := A) f x) =
      (columnMatrix b E R x).map f.hom := by
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
    have hR (z : R) : (z ⊗ₜ[K] x) = z • ((1 : R) ⊗ₜ[K] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hS (z : S) : (z ⊗ₜ[K] x) = z • ((1 : S) ⊗ₜ[K] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    change columnMatrix b E S (f.hom z ⊗ₜ[K] x) = _
    rw [hR, hS, map_smul, map_smul]
    apply Matrix.ext
    rintro ⟨i, a⟩ ⟨j, d⟩
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
      columnMatrix_tmul b E _ e hE, AlgHom.commutes]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    exact (Matrix.map_add _ (map_add f.hom) _ _).symm


private def columnIndex : Index.{u} (Fintype.card (Fin r × J)) ≃ Fin r × J :=
  Equiv.ulift.trans (Fintype.equivFin (Fin r × J)).symm

private def columnRepresentation (s : Involution K A)
    (e : A ≃ₐ[K] Matrix (Fin r) (Fin r) B)
    (hE : ∀ (R : Type u) [CommRing R] [Algebra K R] (a : A),
      E R (1 ⊗ₜ[K] a) = (e a).map (Specs.SymplecticDivisionForms.intoTensor R B)) :
    isometryPoints s ⟶ generalLinearPoints K (Index.{u} (Fintype.card (Fin r × J))) where
  app R := GrpCat.ofHom
    ((Units.map ((Matrix.reindexRingEquiv R (columnIndex (r := r) (J := J)).symm).toMonoidHom)).comp
      ((Units.map (columnMatrix b E R).toMonoidHom).comp (s.baseChange R).isometries.subtype))
  naturality R S f := by
    apply GrpCat.ext
    intro g
    apply Units.ext
    have h := columnMatrix_naturality b E e hE f (g.val : R ⊗[K] A)
    ext i j
    change columnMatrix b E S (SymplecticIsometryDescent.tensorMap (A := A) f
      (g.val : R ⊗[K] A)) (columnIndex i) (columnIndex j) =
      f.hom (columnMatrix b E R (g.val : R ⊗[K] A) (columnIndex i) (columnIndex j))
    exact congrFun (congrFun h (columnIndex i)) (columnIndex j)

private theorem columnRepresentation_injective (s : Involution K A)
    (e : A ≃ₐ[K] Matrix (Fin r) (Fin r) B)
    (hE : ∀ (R : Type u) [CommRing R] [Algebra K R] (a : A),
      E R (1 ⊗ₜ[K] a) = (e a).map (Specs.SymplecticDivisionForms.intoTensor R B))
    (R : TestAlgebra K) : Function.Injective ((columnRepresentation b E s e hE).app R) := by
  intro g h he
  apply Subtype.ext
  apply Units.ext
  apply columnMatrix_injective b E R
  exact (Matrix.reindexRingEquiv R (columnIndex (r := r) (J := J)).symm).injective
    (congrArg Units.val he)

end ColumnRepresentation



section WeakApproximation

open LocalNormOneCommutators.Spec (coordinateTopology)
open UnitaryCayleyChart (isometryExtension)
open Specs.StandardGroups (generalLinearPoints)
open Specs.IntegralModels
open Function

private theorem continuous_coordinate_linearMap
    {F V I : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [AddCommGroup V] [Module F V] [Fintype I] [DecidableEq I]
    (b : Module.Basis I F V) (f : V →ₗ[F] F) :
    let _ := coordinateTopology b
    Continuous f := by
  let _ := coordinateTopology b
  have he (x : V) : f x = ∑ i, b.repr x i * f (b i) :=
    calc
      f x = f (∑ i, b.repr x i • b i) := congrArg f (b.sum_repr x).symm
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        exact map_smul f (b.repr x j) (b j)
  change Continuous (fun x => f x)
  rw [show (fun x => f x) = _ from funext he]
  have hb : Continuous (fun x : V => fun i : I => b.repr x i) :=
    continuous_induced_dom
  exact continuous_finsetSum _ fun i _ => ((continuous_apply i).comp hb).mul continuous_const

/-- Natural coordinates transport Cayley approximation to the given scheme points. -/
private theorem weakApproximationOfNaturalMatrices
    {K A : Type u} [Field K] [Ring A] [Algebra K A] [Module.Finite K A]
    (D : GlobalFieldData.{u,v} K) (s : Involution K A)
    {G : AffineAlgebraicGroup K} (c : PointsOf G.val ≅ isometryPoints s)
    (i : MatrixRealization G)
    (L : ∀ w : D.Place, (D.Completion w ⊗[K] A) →ₗ[D.Completion w]
      Matrix (Index.{u} i.size) (Index.{u} i.size) (D.Completion w))
    (hi : ∀ w (x : LocalPoints D i w), (asMatrix i (D.Completion w) x).val =
      L w (((c.hom.app (CommAlgCat.of K (D.Completion w))) x).val : D.Completion w ⊗[K] A))
    (h : UnitaryCayleyChart.WeakApproximation D s) :
    AdelicGroups.WeakApproximation D i := by
  classical
  intro T
  let F (w : T) := D.Completion w.1
  let Aₚ (w : T) := F w ⊗[K] A
  let b (w : T) := Module.finBasis (F w) (Aₚ w)
  let _ (w : T) := coordinateTopology (b w)
  let inv (w : T) : (s.baseChange (F w)).isometries → LocalPoints D i w.1 :=
    fun x => c.inv.app (CommAlgCat.of K (F w)) x
  have hinv : ∀ w, Continuous (inv w) := by
    intro w
    apply (IsInducing.induced (asMatrix i (F w))).continuous_iff.mpr
    have hm : IsEmbedding (Units.val : Matrix.GeneralLinearGroup (Index.{u} i.size) (F w) →
        Matrix (Index.{u} i.size) (Index.{u} i.size) (F w)) := glVal_isEmbedding
    apply hm.isInducing.continuous_iff.mpr
    apply continuous_matrix
    intro l m
    have he (x : (s.baseChange (F w)).isometries) :
        (asMatrix i (F w) (inv w x)).val l m = L w.1 (x.val : Aₚ w) l m := by
      rw [hi, show c.hom.app (CommAlgCat.of K (F w)) (inv w x) = x from
        GrpCat.hom_inv_apply (c.app (CommAlgCat.of K (F w))) x]
    change Continuous (fun x => (asMatrix i (F w) (inv w x)).val l m)
    simp_rw [he]
    let f : Aₚ w →ₗ[F w] F w :=
      (Matrix.entryLinearMap (F w) (F w) l m).comp (L w.1)
    exact (continuous_coordinate_linearMap (b w) f).comp
      (Units.continuous_val.comp continuous_subtype_val)
  let P : (∀ w : T, (s.baseChange (F w)).isometries) → FinitePoints D i T :=
    fun x w => inv w (x w)
  have hP : Continuous P := continuous_pi fun w => (hinv w).comp (continuous_apply w)
  have hp : Surjective P := by
    intro x
    refine ⟨fun w => c.hom.app (CommAlgCat.of K (F w)) (x w), funext fun w => ?_⟩
    exact GrpCat.inv_hom_apply (c.app (CommAlgCat.of K (F w))) (x w)
  have hd := hp.denseRange.dense_image hP (h T b)
  have hr : P '' Set.range (fun g : s.isometries => fun w : T =>
      isometryExtension (F := F w) s g) ⊆ Set.range (fun g : Specs.IntegralModels.RationalPoints G =>
        fun w : T => localPoint D i w.1 g) := by
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    let g₀ := isometryExtension (F := K) s g
    refine ⟨c.inv.app (CommAlgCat.of K K) g₀, funext fun w => ?_⟩
    let a := CommAlgCat.ofHom (Algebra.ofId K (F w))
    have hh : (isometryPoints s).map a g₀ = isometryExtension (F := F w) s g := by
      apply Subtype.ext
      apply Units.ext
      change SymplecticIsometryDescent.tensorMap (A := A) a (1 ⊗ₜ[K] (g.val : A)) =
        (1 : F w) ⊗ₜ[K] (g.val : A)
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl
    have hn := congrArg (fun m => m g₀) (c.inv.naturality a)
    change c.inv.app (CommAlgCat.of K (F w)) ((isometryPoints s).map a g₀) =
      localPoint D i w.1 (c.inv.app (CommAlgCat.of K K) g₀) at hn
    rw [hh] at hn
    exact hn.symm
  exact hd.mono hr

end WeakApproximation

section LocalModels

open private groupBaseChangePointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations

open Specs.SymplecticDivisionForms (SplitComparison)
open Specs.SymplecticInvolutionModels.DivisionForms
  (toDivisionInvolution SplitLocalModel NonarchimedeanLocalAlternatives)
open Specs.SymplecticDatumTorusAndBorel (HyperbolicIndex)
open Specs.SymplecticMatrixStructure (symplecticPoints)
open Specs.GeometricRadicals (IsSplitReductive)
open _root_.Specs.RM03.CSA (isCentralSimple)
open private isometryPointsBaseChange splitComparisonBaseChange splitLocalModel_of_field
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels

private def completionIsometryComparison
    {K A F : Type u} [Field K] [Ring A] [Algebra K A] [Field F] [Algebra K F]
    {G : AffineAlgebraicGroup K} {s : Involution K A}
    (c : PointsOf G.val ≅ isometryPoints s) :
    PointsOf (baseChangedAlgebraicGroup F G).val ≅ isometryPoints (s.baseChange F) :=
  groupBaseChangePointIso F G.val ≪≫
    Functor.isoWhiskerLeft (restrictTestAlgebra K F) c ≪≫ (isometryPointsBaseChange s).symm

private theorem splitSymplecticAtSplitAlgebra
    {K A L F : Type u} [Field K] [Ring A] [Algebra K A] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [Field F] [Algebra K F]
    (hA : isCentralSimple K A) (s : Involution K A) {n r : ℕ}
    (hc : SplitComparison (toDivisionInvolution s) L (n + 1))
    (e : (F ⊗[K] A) ≃ₐ[F] Matrix (Fin r) (Fin r) F)
    {G : AffineAlgebraicGroup K} (c : PointsOf G.val ≅ isometryPoints s) :
    Nonempty (PointsOf (baseChangedAlgebraicGroup F G).val ≅
      symplecticPoints F (HyperbolicIndex.{u} (n + 1))) := by
  have hB := _root_.RM03.CSA.isCentralSimple_baseChange (L := F) hA
  have hr : 0 < r := by
    by_contra! hz
    have hz : r = 0 := Nat.eq_zero_of_le_zero hz
    subst r
    let : IsSimpleRing (F ⊗[K] A) := hB.1
    exact zero_ne_one (e.injective (Subsingleton.elim (e 0) (e 1)))
  have hs := splitComparisonBaseChange (F := F) s hc
  obtain ⟨_, _, _, _, _, _, m, _⟩ := splitLocalModel_of_field hB (s.baseChange F) hs hr e
  exact ⟨completionIsometryComparison c ≪≫ m⟩

private theorem finiteNonsplitCompletions
    {K A L : Type u} [Field K] [Ring A] [Algebra K A] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (D : GlobalFieldData.{u,v} K)
    (hA : isCentralSimple K A) (s : Involution K A) (n : ℕ)
    (hc : SplitComparison (toDivisionInvolution s) L (n + 1))
    {G : AffineAlgebraicGroup K} (c : PointsOf G.val ≅ isometryPoints s) :
    {w : D.FinitePlace | ¬ Nonempty (PointsOf
      (baseChangedAlgebraicGroup (D.Completion (.inl w)) G).val ≅
        symplecticPoints (D.Completion (.inl w)) (HyperbolicIndex.{u} (n + 1)))}.Finite := by
  refine (AlmostEverywhereSplitAlgebras.almost_everywhere_split D hA).subset ?_
  intro w hw
  let F := D.Completion (.inl w)
  let : Algebra K F := AdelicGroups.completionAlgebra D (.inl w)
  change ¬ Nonempty ((F ⊗[K] A) ≃ₐ[F] Matrix
      (Fin (_root_.Specs.RM03.CSA.degree K A)) (Fin (_root_.Specs.RM03.CSA.degree K A)) F)
  intro he
  obtain ⟨e⟩ := he
  exact hw (splitSymplecticAtSplitAlgebra hA s hc e c)

private theorem splitReductiveOfSymplecticPoints
    {F : Type u} [Field F] (G : AffineAlgebraicGroup F) (hG : IsAbsolutelyAlmostSimple G)
    (n : ℕ) (c : PointsOf G.val ≅ symplecticPoints F (HyperbolicIndex.{u} (n + 1))) :
    IsSplitReductive G := by
  obtain ⟨T, _, _, _, _, _, _, ht, hmax, _⟩ := _root_.LinearAlgebraicGroups.RootData.SymplecticDatumTorusAndBorel.torusAndBorel F n G c
  exact ⟨reductive_of_semisimple G hG.1, T, ht, hmax⟩

end LocalModels

section QuotientTransport

open Filter
open scoped Pointwise

private theorem compactQuotient_of_surjective {P Q : Type*} [Group P] [Group Q]
    [TopologicalSpace P] [TopologicalSpace Q] (f : P →* Q)
    (hf : Continuous f) (hs : Function.Surjective f) (H : Subgroup P) (J : Subgroup Q)
    (h : H ≤ J.comap f) (hc : CompactSpace (P ⧸ H)) : CompactSpace (Q ⧸ J) := by
  let e : P ⧸ H → Q ⧸ J := Quotient.map' f (by
    intro x y hxy
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv, ← map_mul]
    exact h (QuotientGroup.leftRel_apply.mp hxy))
  have he : Continuous e := continuous_quot_map _ hf
  have hes : Function.Surjective e := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨z, rfl⟩ := hs y
    exact ⟨QuotientGroup.mk z, rfl⟩
  refine ⟨?_⟩
  rw [← hes.range_eq, ← Set.image_univ]
  exact isCompact_univ.image he

private theorem continuousAdelicHom
    {P K : Type*} [Group P] [TopologicalSpace P]
    [Field K] {G : AffineAlgebraicGroup K} (D : GlobalFieldData K)
    (i : MatrixRealization G) (S : Finset D.Place)
    (f : P →* Adeles D i S)
    (hmul : ∀ a : P, Continuous (fun z : P => z * a))
    (hf : ∀ w : Outside D S, Continuous (fun p : P => f p w))
    (U : Subgroup P) (hU : IsOpen (U : Set P))
    (hU' : ∀ p ∈ U, ∀ w : Outside D S, f p w ∈ localSubgroup D i w.1) :
    Continuous f := by
  let p : U → Πʳ w : Outside D S, [LocalPoints D i w.1, localSubgroup D i w.1]_[⊤] :=
    fun x => ⟨fun w => f x w, Filter.eventually_top.mpr (hU' x x.property)⟩
  have hp : Continuous p := RestrictedProduct.continuous_rng_of_top.mpr
    (continuous_pi fun w => (hf w).comp continuous_subtype_val)
  have hrest : Continuous (f ∘ (Subtype.val : U → P)) :=
    (RestrictedProduct.continuous_inclusion (R := fun w : Outside D S => LocalPoints D i w.1)
      (A := fun w : Outside D S => ↑(localSubgroup D i w.1)) le_top).comp hp
  have he : IsOpenEmbedding (Subtype.val : U → P) := IsOpen.isOpenEmbedding_subtypeVal hU
  have h₁ : ContinuousAt f (1 : P) := he.continuousAt_iff.mp (hrest.continuousAt (x := 1))
  apply continuous_iff_continuousAt.mpr
  intro a
  let e : P ≃ₜ P :=
    { toEquiv := Equiv.mulRight a
      continuous_toFun := hmul a
      continuous_invFun := hmul a⁻¹ }
  have hc : ContinuousAt (f ∘ e) 1 := by
    change ContinuousAt (fun x => f (x * a)) 1
    simp_rw [map_mul]
    exact h₁.mul continuousAt_const
  have hh := e.isOpenEmbedding.continuousAt_iff.mp hc
  simpa [e, Equiv.mulRight] using hh

end QuotientTransport

section MatrixAdeles

open Filter
open scoped NumberField
open Specs.AnisotropicTensorQuotients
  (CompactMatrixQuotient localConditions GlobalMatrixQuotientCompact MatrixModel
    functionAtPlace numberAtPlace)
open TensorAdelicReduction (integralMatrices FunctionMatrixAdeles NumberMatrixAdeles)
open private mem_localConditions MatrixAdeles matrixAt continuous_matrixAt adelicMatrixGroup
  continuous_matrixAdeles_mul_const from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicTensorQuotients
open private eventually_outside glIntegral_compactOpen from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
  {I : Type u} [Fintype I] [DecidableEq I]

private def reindexGL {I J R : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [CommRing R] (e : I ≃ J) : GL I R ≃* GL J R :=
  Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv

private theorem reindexGL_continuous {I J R : Type u}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [CommRing R]
    [TopologicalSpace R] (e : I ≃ J) :
    Continuous (reindexGL (R := R) e) := by
  apply Units.continuous_iff.mpr
  have h : Continuous (fun g : GL I R => (reindexGL e g).val) :=
    continuous_matrix fun i j => by
      change Continuous (fun g : GL I R => g.val (e.symm i) (e.symm j))
      have hv : Continuous (fun g : GL I R => (g.val : I → I → R)) := Units.continuous_val
      exact (continuous_apply (e.symm j)).comp ((continuous_apply (e.symm i)).comp hv)
  refine ⟨h, ?_⟩
  have hi : (fun g : GL I R => (reindexGL e g)⁻¹.val) =
      fun g : GL I R => (reindexGL e g⁻¹).val := by
    funext g
    rw [map_inv]
  rw [hi]
  apply continuous_matrix
  intro i j
  change Continuous (fun g : GL I R => g⁻¹.val (e.symm i) (e.symm j))
  have hv : Continuous (fun g : GL I R => (g⁻¹.val : I → I → R)) := Units.continuous_coe_inv
  exact (continuous_apply (e.symm j)).comp ((continuous_apply (e.symm i)).comp hv)

private theorem reindexGL_integral {I J R : Type u}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [CommRing R]
    (e : I ≃ J) (O : Subring R) (g : GL I R) :
    reindexGL e g ∈ integralMatrices O ↔ g ∈ integralMatrices O := by
  have hn {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
      (d : I ≃ J) (x : GL I R) :
      x ∈ integralMatrices O → reindexGL d x ∈ integralMatrices O := by
    rintro ⟨y, rfl⟩
    exact ⟨reindexGL d y, Units.ext rfl⟩
  constructor
  · intro h
    have he : reindexGL e.symm (reindexGL e g) = g := by
      apply Units.ext
      apply Matrix.ext
      intro x y
      change g.val (e.symm (e x)) (e.symm (e y)) = g.val x y
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact he ▸ hn e.symm _ h
  · exact hn e g

private theorem localMatrixModel_iff {D : GlobalFieldData.{u,v} K} (i : MatrixRealization G)
    (e : Index.{u} i.size ≃ I) (w : D.FinitePlace) (g : LocalPoints D i (.inl w)) :
    g ∈ localSubgroup D i (.inl w) ↔
      reindexGL e (asMatrix i (D.Completion (.inl w)) g) ∈ integralMatrices (D.integers w).toSubring :=
  (reindexGL_integral e _ _).symm

private theorem matrixAdelesEventualIntegral (D : GlobalFieldData.{u,v} K)
    (x : MatrixAdeles D I) :
    ∀ᶠ w : D.FinitePlace in cofinite,
      matrixAt D (.inl w) x ∈ integralMatrices (D.integers w).toSubring := by
  cases D with
  | number h =>
    let := h
    exact (show NumberMatrixAdeles K I from x).1.property
  | function F t => exact (show FunctionMatrixAdeles K I from x).property

private theorem matrixAdelesIntegralOpen (D : GlobalFieldData.{u,v} K) :
    IsOpen {x : MatrixAdeles D I | ∀ w : D.FinitePlace,
      matrixAt D (.inl w) x ∈ integralMatrices (D.integers w).toSubring} := by
  have hOpen (w : D.FinitePlace) : IsOpen
      (integralMatrices (I := I) (D.integers w).toSubring : Set (GL I (D.FiniteCompletion w))) := by
    obtain ⟨hc, ho, _⟩ := D.integers_properties w
    exact (glIntegral_compactOpen (D.integers w) hc ho).2
  cases D with
  | number h =>
    let := h
    exact (RestrictedProduct.isOpen_forall_mem hOpen).preimage continuous_fst
  | function F t => exact RestrictedProduct.isOpen_forall_mem hOpen

private theorem matrixAdelesOfPoints (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (e : Index.{u} i.size ≃ I) (x : Adeles D i ∅) :
    ∃ y : MatrixAdeles D I, ∀ w : Outside D (∅ : Finset D.Place),
      matrixAt D w.1 y = reindexGL e (asMatrix i (D.Completion w.1) (x w)) := by
  let w₀ (w : D.Place) : Outside D (∅ : Finset D.Place) := ⟨w, Finset.notMem_empty w⟩
  let y (w : D.Place) : GL I (D.Completion w) := reindexGL e (asMatrix i _ (x (w₀ w)))
  have hy : ∀ᶠ w : D.FinitePlace in cofinite, y (.inl w) ∈ integralMatrices (D.integers w).toSubring := by
    have h : Function.Injective (fun w : D.FinitePlace => w₀ (.inl w)) :=
      fun _ _ hab => Sum.inl_injective (congrArg Subtype.val hab)
    filter_upwards [h.tendsto_cofinite x.property] with w hw
    exact (localMatrixModel_iff i e w _).mp hw
  cases D with
  | number h =>
    let := h
    use ((⟨fun w => y (.inl w), hy⟩, fun w => y (.inr w)) : NumberMatrixAdeles K I)
    rintro ⟨w, hw⟩
    cases w <;> rfl
  | function F t =>
    use (⟨fun w => y (.inl w), hy⟩ : FunctionMatrixAdeles K I)
    rintro ⟨w, hw⟩
    cases w with
    | inl w => rfl
    | inr w => exact w.elim

private theorem globalMatrixQuotient_coordinates
    (D : GlobalFieldData.{u,v} K) (M : MatrixModel K I) (hc : GlobalMatrixQuotientCompact D M) :
    ∃ δ : GL I K →* MatrixAdeles D I,
      (∀ g w, matrixAt D w (δ g) = Matrix.GeneralLinearGroup.map (D.embedding w) g) ∧
      CompactMatrixQuotient (adelicMatrixGroup D M) (M K (RingHom.id K)) δ := by
  cases D with
  | number h =>
    let := h
    let G := adelicMatrixGroup (.number h : GlobalFieldData.{u,v} K) M
    have he : G =
        localConditions numberAtPlace (fun (w : NumberPlace K) => M w.Completion w.embedding) := by
      ext x
      simp only [G, adelicMatrixGroup, mem_localConditions]
      constructor <;> intro hx w <;> cases w
      · exact hx (.inl _)
      · exact hx (.inr _)
      · exact hx (.inl _)
      · exact hx (.inr _)
    obtain ⟨δ, hδ, hc⟩ := hc
    refine ⟨δ, fun g w => ?_, ?_⟩
    · cases w with
      | inl w => exact hδ g (.inl w)
      | inr w => exact hδ g (.inr w)
    · change CompactMatrixQuotient G (M K (RingHom.id K)) δ
      rw [he]
      exact hc
  | function F t =>
    let G := adelicMatrixGroup (.function F t) M
    have he : G =
        localConditions functionAtPlace (fun (w : FunctionPlace K) => M w.Completion w.embedding) := by
      ext x
      simp only [G, adelicMatrixGroup, mem_localConditions]
      exact ⟨fun h w => h (.inl w), fun h w => by
        cases w with
        | inl w => exact h w
        | inr w => exact w.elim⟩
    obtain ⟨δ, hδ, hc⟩ := hc
    refine ⟨δ, fun g w => ?_, ?_⟩
    · cases w with
      | inl w => exact hδ g w
      | inr w => exact w.elim
    · change CompactMatrixQuotient G (M K (RingHom.id K)) δ
      rw [he]
      exact hc

set_option maxHeartbeats 650000 in
private theorem compactFromGlobalMatrixModel
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (e : Index.{u} i.size ≃ I)
    (M : MatrixModel K I)
    (hM : ∀ w : D.Place, M (D.Completion w) (D.embedding w) =
      ((reindexGL (R := D.Completion w) e).toMonoidHom.comp (asMatrix i (D.Completion w))).range)
    (hRat : M K (RingHom.id K) =
      ((reindexGL (R := K) e).toMonoidHom.comp i.onPoints).range)
    (hc : GlobalMatrixQuotientCompact D M) :
    CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i) := by
  obtain ⟨δ, hδ, hc⟩ := globalMatrixQuotient_coordinates D M hc
  let H := adelicMatrixGroup D M
  let f w : LocalPoints D i w →* GL I (D.Completion w) :=
    (reindexGL e).toMonoidHom.comp (asMatrix i (D.Completion w))
  have hf w : Function.Injective (f w) :=
    (reindexGL e).injective.comp (AdelicGroups.localMatrixEmbedding D i w).injective
  let d w := (MonoidHom.ofInjective (hf w)).symm
  let h w : H →* (f w).range :=
    ((matrixAt D w).comp H.subtype).codRestrict _ (fun x =>
      hM w ▸ (mem_localConditions (matrixAt D) _ _).mp x.property w)
  let p w : H →* LocalPoints D i w := (d w).toMonoidHom.comp (h w)
  have hp (w : D.Place) (x : H) : f w (p w x) = matrixAt D w x :=
    congrArg Subtype.val ((d w).symm_apply_apply (h w x))
  have hi (w : D.FinitePlace) (x : H) :
      p (.inl w) x ∈ localSubgroup D i (.inl w) ↔
        matrixAt D (.inl w) x.val ∈ integralMatrices (D.integers w).toSubring := by
    rw [← hp (.inl w) x]
    exact localMatrixModel_iff i e w _
  let m : H →* Adeles D i ∅ :=
    { toFun := fun x => ⟨fun w => p w.1 x,
        eventually_outside D ∅ (p := fun w => p w x ∈ localSubgroup D i w)
          ((matrixAdelesEventualIntegral D x.val).mono fun w hw => (hi w x).mpr hw)
          (fun w => by exact Subgroup.mem_top _)⟩
      map_one' := RestrictedProduct.ext _ _ fun w => map_one (p w.1)
      map_mul' := fun x y => RestrictedProduct.ext _ _ fun w => map_mul (p w.1) x y }
  let U : Subgroup H := ⨅ w : D.FinitePlace,
    (integralMatrices (D.integers w).toSubring).comap ((matrixAt D (.inl w)).comp H.subtype)
  have hU (x : H) : x ∈ U ↔ ∀ w : D.FinitePlace,
      matrixAt D (.inl w) x.val ∈ integralMatrices (D.integers w).toSubring := Subgroup.mem_iInf
  have hUo : IsOpen (U : Set H) := by
    have he : (U : Set H) = Subtype.val ⁻¹' {x : MatrixAdeles D I | ∀ w : D.FinitePlace,
        matrixAt D (.inl w) x ∈ integralMatrices (D.integers w).toSubring} := Set.ext hU
    rw [he]
    exact (matrixAdelesIntegralOpen D).preimage continuous_subtype_val
  have hcont : Continuous m := by
    refine continuousAdelicHom D i ∅ m ?_ ?_ U hUo ?_
    · intro a
      exact ((continuous_matrixAdeles_mul_const D a.val).comp continuous_subtype_val).subtype_mk _
    · intro w
      let equiv : GL (Index.{u} i.size) (D.Completion w.1) ≃ₜ* GL I (D.Completion w.1) :=
        { toMulEquiv := reindexGL e
          continuous_toFun := reindexGL_continuous e
          continuous_invFun := reindexGL_continuous e.symm }
      have hInd : IsInducing (f w.1) :=
        equiv.toHomeomorph.isInducing.comp (IsInducing.induced (asMatrix i (D.Completion w.1)))
      apply hInd.continuous_iff.mpr
      change Continuous (fun x : H => f w.1 (p w.1 x))
      simp_rw [hp]
      exact (continuous_matrixAt D w.1).comp continuous_subtype_val
    · rintro x hx ⟨w, hw⟩
      change p w x ∈ localSubgroup D i w
      cases w with
      | inl w => exact (hi w x).mpr ((hU x).mp hx w)
      | inr w => exact Subgroup.mem_top _
  have hsurj : Function.Surjective m := by
    intro x
    obtain ⟨y, hy⟩ := matrixAdelesOfPoints D i e x
    have hyH : y ∈ H := (mem_localConditions (matrixAt D) _ _).mpr (fun w => by
      let w' : Outside D (∅ : Finset D.Place) := ⟨w, Finset.notMem_empty _⟩
      rw [hM w, hy w']
      exact ⟨x w', rfl⟩)
    refine ⟨⟨y, hyH⟩, RestrictedProduct.ext _ _ fun w => (hf w.1) ?_⟩
    change f w.1 (p w.1 ⟨y, hyH⟩) = f w.1 (x w)
    rw [hp]
    exact hy w
  apply compactQuotient_of_surjective m hcont hsurj
    ((Subgroup.map δ (M K (RingHom.id K))).subgroupOf H) (diagonalSubgroup D i) _ hc.2
  intro x hx
  change ∃ g ∈ M K (RingHom.id K), δ g = x.val at hx
  obtain ⟨g, hg, hgx⟩ := hx
  rw [hRat] at hg
  obtain ⟨g₀, rfl⟩ := hg
  change ∃ g : Specs.IntegralModels.RationalPoints G,
    ∀ w : Outside D (∅ : Finset D.Place), m x w = localPoint D i w.1 g
  refine ⟨g₀, fun w => hf w.1 ?_⟩
  change f w.1 (p w.1 x) = reindexGL e (asMatrix i (D.Completion w.1) (localPoint D i w.1 g₀))
  rw [hp, ← hgx, hδ, AdelicGroups.localPoint_matrix]
  apply Units.ext
  rfl

end MatrixAdeles

section TensorApplication

open Specs.AnisotropicTensorQuotients (columnBasis matrixColumnAction matrixOfUnits symplecticMatrixModel)
open Specs.SymplecticDivisionForms (SplitComparison)
open Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)
open _root_.Specs.RM03.CSA (isCentralSimple)
open Specs.StandardGroups (generalLinearPoints)

private theorem compactQuotient_changeRealization {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i j : MatrixRealization G)
    (h : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i)) :
    CompactSpace (Adeles D j ∅ ⧸ diagonalSubgroup D j) := by
  let e := AdelicGroups.changeRealization D i j ∅
  apply compactQuotient_of_surjective e.toMonoidHom e.continuous e.surjective _ _ _ h
  intro x hx
  obtain ⟨g, hg⟩ := hx
  exact ⟨g, fun w => hg w⟩

private theorem weakApproximation_changeRealization {K : Type u} [Field K]
    {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K) (i j : MatrixRealization G)
    (h : AdelicGroups.WeakApproximation D i) : AdelicGroups.WeakApproximation D j := by
  intro T
  let e (w : T) := AdelicGroups.changePoints i j (D.Completion w.1)
  let p : FinitePoints D i T → FinitePoints D j T := fun x w => e w (x w)
  have hp : Continuous p := continuous_pi fun w =>
    (AdelicGroups.continuous_changePoints i j (D.Completion w.1)).comp (continuous_apply w)
  have hs : Function.Surjective p := fun x =>
    ⟨fun w => (e w).symm (x w), funext fun w => (e w).apply_symm_apply _⟩
  exact hs.denseRange.dense_image hp (h T) |>.mono (by
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem compactnessAndWeakApproximation_of_symplecticModel
    {K A L : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    [Ring A] [Algebra K A] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (hA : isCentralSimple K A) (s : Involution K A) (n : ℕ)
    (hc : SplitComparison (toDivisionInvolution s) L n)
    (G : AffineAlgebraicGroup K) (hG : IsAbsolutelyAlmostSimple G)
    (ha : GloballyAnisotropic G) (c : PointsOf G.val ≅ isometryPoints s) :
    ∀ j : MatrixRealization G, CompactSpace (Adeles D j ∅ ⧸ diagonalSubgroup D j) ∧
      AdelicGroups.WeakApproximation D j := by
  obtain ⟨r, B, hDiv, hAlg, _, model, d, b, E, hE, hcomp⟩ :=
    AnisotropicTensorQuotients.symplecticCompactness D hA s hc
      (involutionAnisotropic s G c hG.1 ha)
  let := hDiv
  let := hAlg
  let : Module.Finite K A := hA.2.2
  let J := ULift.{u} (Fin d)
  let size := Fintype.card (Fin r × J)
  let ρ := columnRepresentation b E s model.equiv hE
  let τ : PointsOf G.val ⟶ generalLinearPoints K (Index.{u} size) := c.hom ≫ ρ
  have hτ (R : TestAlgebra K) : Function.Injective (τ.app R) := by
    change Function.Injective (fun g => ρ.app R (c.hom.app R g))
    exact (columnRepresentation_injective b E s model.equiv hE R).comp
      (ConcreteCategory.bijective_of_isIso (c.hom.app R)).1
  let i := realizationOfNaturalMatrices size τ hτ
  let e : Index.{u} i.size ≃ Fin r × J := columnIndex
  have hm (R : Type u) [CommRing R] [Algebra K R] (g : PointsIn i R) :
      asMatrix i R g = ρ.app (CommAlgCat.of K R) (c.hom.app (CommAlgCat.of K R) g) :=
    asMatrix_realizationOfNaturalMatrices size τ hτ R g
  have hM (R : Type u) [Field R] (a : K →+* R) :
      letI : Algebra K R := a.toAlgebra
      symplecticMatrixModel s b E R a =
        ((reindexGL (R := R) e).toMonoidHom.comp (asMatrix i R)).range := by
    let _ : Algebra K R := a.toAlgebra
    let f : (R ⊗[K] A)ˣ →* GL (Fin r × J) R :=
      matrixOfUnits (columnBasis (I := Fin r) (b.baseChange R)) (matrixColumnAction.comp (E R).toAlgHom)
    have he (g : PointsIn i R) : reindexGL e (asMatrix i R g) =
        f ((c.hom.app (CommAlgCat.of K R)) g).val := by
      rw [hm R g]
      apply Units.ext
      change _ = (matrixOfUnits (columnBasis (I := Fin r) (b.baseChange R))
        (matrixColumnAction.comp (E R).toAlgHom) ((c.hom.app (CommAlgCat.of K R)) g).val).val
      rw [columnMatrix_units]
      apply Matrix.ext
      intro i j
      change columnMatrix b E R ((c.hom.app (CommAlgCat.of K R) g).val : R ⊗[K] A)
          (e (e.symm i)) (e (e.symm j)) = _
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change (s.baseChange R).isometries.map f =
      ((reindexGL (R := R) e).toMonoidHom.comp (asMatrix i R)).range
    apply SetLike.ext
    intro m
    constructor
    · rintro ⟨z, hz, hm⟩
      let x : (s.baseChange R).isometries := ⟨z, hz⟩
      let g : PointsIn i R := c.inv.app (CommAlgCat.of K R) x
      have hg : c.hom.app (CommAlgCat.of K R) g = x :=
        GrpCat.hom_inv_apply (c.app (CommAlgCat.of K R)) x
      refine ⟨g, (he g).trans ?_⟩
      change f ((c.hom.app (CommAlgCat.of K R) g).val) = m
      exact (congrArg (fun z : (s.baseChange R).isometries => f z.val) hg).trans hm
    · rintro ⟨g, rfl⟩
      let x : (s.baseChange R).isometries := c.hom.app (CommAlgCat.of K R) g
      exact ⟨x.val, x.property, (he g).symm⟩
  have hci := compactFromGlobalMatrixModel D i e (symplecticMatrixModel s b E)
    (fun w => hM (D.Completion w) (D.embedding w)) (hM K (RingHom.id K)) hcomp
  have hw := UnitaryCayleyChart.symplecticWeakApproximation D s n hc
  have hwi := weakApproximationOfNaturalMatrices D s c i
    (fun w => ((Matrix.reindexAlgEquiv (D.Completion w) (D.Completion w) e.symm).toLinearMap).comp
      (columnMatrix b E (D.Completion w)).toLinearMap)
    (fun w g => congrArg Units.val (hm (D.Completion w) g)) hw
  intro j
  exact ⟨compactQuotient_changeRealization D i j hci, weakApproximation_changeRealization D i j hwi⟩

end TensorApplication

section RadicalGeneration

open Filter
open Specs.Arithmetic.ProjectiveRecurrence (cocharacterRadicalPoints)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open CocharacterDynamics (LimitDecomposition)
open _root_.LinearAlgebraicGroups.Specs (SubgroupSections)
open Specs.BorelProper (IsParabolic)
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private testPointSections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private rationalSourceIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalDensity

private def matrixPointSections {F : Type u} [Field F] (G : AffineAlgebraicGroup F)
    (i : MatrixRealization G) : PointsIn i F ≃* (𝟙_ (SchemeOver F) ⟶ G.val.X) :=
  testPointSections G.val

private theorem radicalSections_cocharacterPoints
    {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (G : AffineAlgebraicGroup F) (i : MatrixRealization G)
    (P : ClosedSubgroup G.val) (hP : IsParabolic G P)
    (U : ClosedSubgroup P.group) (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P) U)
    (x : 𝟙_ (SchemeOver F) ⟶ G.val.X)
    (hx : x ∈ SubgroupSections (subgroupOfSubgroup P U) (𝟙_ (SchemeOver F))) :
    (matrixPointSections G i).symm x ∈ cocharacterRadicalPoints G := by
  obtain ⟨c, R, _, _, hmatch, _⟩ := LocalCocharacterEvaluation.parabolicRadicalEvaluation.{u,u} G i P hP
  obtain ⟨a, ha⟩ := hmatch U hU
  obtain ⟨y, hy⟩ := hx
  let y' : 𝟙_ (SchemeOver F) ⟶ U.group.X := y
  refine ⟨c, R, (rationalSourceIso F).inv ≫ y' ≫ a.hom.hom.hom, ?_⟩
  change ((rationalSourceIso F).inv ≫ y' ≫ a.hom.hom.hom) ≫ R.contracting.inclusion.hom.hom =
    (rationalSourceIso F).inv ≫ x
  change y' ≫ (U.inclusion ≫ P.inclusion).hom.hom = x at hy
  have hcomp : a.hom.hom.hom ≫ R.contracting.inclusion.hom.hom =
      (U.inclusion ≫ P.inclusion).hom.hom :=
    congrArg (fun (f : U.group ⟶ G.val) => f.hom.hom) ha
  calc
    _ = (rationalSourceIso F).inv ≫ (y' ≫ (a.hom.hom.hom ≫ R.contracting.inclusion.hom.hom)) := by
      simp only [Category.assoc]
    _ = _ := congrArg (fun z => (rationalSourceIso F).inv ≫ z)
      ((congrArg (fun z => y' ≫ z) hcomp).trans hy)

private theorem leComapClosure {P Q : Type*} [Group P] [Group Q] (f : P →* Q)
    (H : Subgroup P) (S : Set Q) (h : ∀ x ∈ H, f x ∈ S) :
    H ≤ (Subgroup.closure S).comap f :=
  fun x hx => Subgroup.subset_closure (h x hx)

private theorem radicalSections_le_cocharacterClosure
    {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (G : AffineAlgebraicGroup F) (i : MatrixRealization G)
    (P : ClosedSubgroup G.val) (hP : IsParabolic G P)
    (U : ClosedSubgroup P.group) (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P) U) :
    SubgroupSections (subgroupOfSubgroup P U) (𝟙_ (SchemeOver F)) ≤
      (Subgroup.closure (cocharacterRadicalPoints G : Set (PointsIn i F))).comap
        (matrixPointSections G i).symm.toMonoidHom :=
  leComapClosure _ _ _ (radicalSections_cocharacterPoints G i P hP U hU)

private theorem top_of_top_le_comap {P Q : Type*} [Group P] [Group Q] (f : P ≃* Q)
    (H : Subgroup Q) (h : (⊤ : Subgroup P) ≤ H.comap f.toMonoidHom) : H = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := f.surjective y
  exact h (Subgroup.mem_top x)

private theorem parabolicGeneration_gives_cocharacterGeneration
    {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (G : AffineAlgebraicGroup F) (i : MatrixRealization G)
    (hG : unipotentGenerated G = ⊤) :
    Subgroup.closure (G := PointsIn i F) (cocharacterRadicalPoints G) = ⊤ := by
  apply top_of_top_le_comap (matrixPointSections G i).symm
  rw [← hG]
  exact iSup_le fun P => iSup_le fun hP => iSup_le fun U => iSup_le fun hU =>
    radicalSections_le_cocharacterClosure G i P hP U hU

private theorem contractedGeneration_of_parabolicGeneration
    {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (G : AffineAlgebraicGroup F) (i : MatrixRealization G)
    (hG : unipotentGenerated G = ⊤)
    {E : Type v} [NontriviallyNormedField E] [Algebra E F]
    (he : Continuous (algebraMap E F)) :
    Subgroup.closure {x : PointsIn i F | Contracted x} = ⊤ := by
  obtain ⟨t, ht⟩ := LocalCocharacterEvaluation.contractingScalarExists.{v} (E := E)
  apply top_unique
  rw [← parabolicGeneration_gives_cocharacterGeneration G i hG]
  apply Subgroup.closure_mono
  rintro x ⟨c, R, hx⟩
  exact ⟨_, LocalCocharacterEvaluation.contractingEvaluation G i c R he t ht x hx⟩

private theorem contractedGeneration_transport {P Q : Type*} [Group P] [Group Q]
    [TopologicalSpace P] [TopologicalSpace Q] (e : P ≃ₜ* Q)
    (h : Subgroup.closure {x : P | Contracted x} = ⊤) :
    Subgroup.closure {x : Q | Contracted x} = ⊤ := by
  apply top_unique
  rw [← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective, ← h, MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨x, ⟨a, ha⟩, rfl⟩
  refine ⟨e a, ?_⟩
  have hc : Continuous (e : P → Q) := e.continuous
  have h := (hc.tendsto 1).comp ha
  change Tendsto (fun n : ℕ => e a ^ n * e x * (e a ^ n)⁻¹) atTop (𝓝 1)
  simpa only [Function.comp_def, map_one, map_mul, map_inv, map_pow] using h

private theorem finiteContractedGeneration {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.FinitePlace)
    (h : unipotentGenerated (baseChangedAlgebraicGroup (D.Completion (.inl w)) G) = ⊤) :
    Dense (Subgroup.closure {x : FinitePoints D i {Sum.inl w} | Contracted x} :
      Set (FinitePoints D i {Sum.inl w})) := by
  let F := D.Completion (.inl w)
  let _ : Algebra K F := AdelicGroups.completionAlgebra D (.inl w)
  let _ : ValuativeRel F := inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
  let _ : IsNonarchimedeanLocalField F := D.finiteCompletion_isLocalField w
  let _ : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  let _ : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
  let _ : Valuation.RankOne (Valued.v (R := F) (Γ₀ := ValuativeRel.ValueGroupWithZero F)) := by
    change Valuation.RankOne (ValuativeRel.valuation F)
    infer_instance
  let nF : NontriviallyNormedField F := Valued.toNontriviallyNormedField F
    (ValuativeRel.ValueGroupWithZero F)
  let J := baseChangedAlgebraicGroup F G
  obtain ⟨j, ⟨e⟩⟩ := completionMatrixComparison D i (.inl w)
  have hcont : @Continuous F F nF.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace _
      (algebraMap F F) := by
    change Continuous (algebraMap F F)
    simpa using (continuous_id : Continuous (id : F → F))
  have hv := @contractedGeneration_of_parabolicGeneration.{u,u}
    F _ _ _ J j h F nF (Algebra.id F) hcont
  rw [contractedGeneration_transport (e.trans (singletonLocalPoints D i (.inl w)).symm) hv,
    Subgroup.coe_top]
  exact dense_univ

end RadicalGeneration

section FiniteApproximation

open Specs.SymplecticDivisionForms (SplitComparison)
open Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)
open Specs.SymplecticDatumTorusAndBorel (HyperbolicIndex)
open Specs.SymplecticMatrixStructure (symplecticPoints)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open _root_.Specs.RM03.CSA (isCentralSimple)

private theorem simplyConnectedOfSymplecticPoints {F : Type u} [Field F] (n : ℕ)
    (G : AffineAlgebraicGroup F)
    (c : PointsOf G.val ≅ symplecticPoints F (HyperbolicIndex.{u} (n + 1))) :
    GeometricallySimplyConnected G := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ :=
    _root_.LinearAlgebraicGroups.RootData.SymplecticDatum.basedComputation F n G c
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := h
  exact h

private theorem strongApproximation_when_archimedean_complement_compact
    (hfull : FiniteCovolumeSubgroup.{u}) {K A L : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) [Ring A] [Algebra K A]
    [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (hA : isCentralSimple K A) (s : Involution K A) (n : ℕ)
    (hs : SplitComparison (toDivisionInvolution s) L (n + 1))
    (G : AffineAlgebraicGroup K) (hG : IsAbsolutelyAlmostSimple G)
    (c : PointsOf G.val ≅ isometryPoints s)
    (i : MatrixRealization G) (S : Finset D.Place)
    (harch : ∀ w : D.InfinitePlace, Sum.inr w ∉ S → CompactSpace (LocalPoints D i (.inr w)))
    (hcompact : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hnoncompact : ¬ CompactSpace (FinitePoints D i S))
    (hweak : AdelicGroups.WeakApproximation D i) : StrongApproximation D i S := by
  let Bad : Set D.FinitePlace := {w | ¬ Nonempty (
    PointsOf (baseChangedAlgebraicGroup (D.Completion (.inl w)) G).val ≅
      symplecticPoints (D.Completion (.inl w)) (HyperbolicIndex.{u} (n + 1)))}
  have hBad : Bad.Finite := finiteNonsplitCompletions D hA s n hs c
  let : Finite D.InfinitePlace := by
    cases D with
    | number h =>
      let := h
      exact inferInstanceAs (Finite (NumberField.InfinitePlace K))
    | function F t => exact inferInstanceAs (Finite (PEmpty : Type u))
  let := Fintype.ofFinite D.InfinitePlace
  let T : Finset D.Place :=
    hBad.toFinset.image Sum.inl ∪ Finset.univ.image (Sum.inr : D.InfinitePlace → D.Place)
  let J := T \ S
  have hd : Disjoint J S := Finset.disjoint_sdiff.symm
  have hSplit (w : Outside D S) (hw : w.1 ∉ J) :
      ∃ p : D.FinitePlace, w.1 = .inl p ∧ p ∉ Bad := by
    have hT : w.1 ∉ T := fun hT => hw (Finset.mem_sdiff.mpr ⟨hT, w.2⟩)
    cases h : w.1 with
    | inl p =>
      refine ⟨p, rfl, fun hb => hT ?_⟩
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hBad.mem_toFinset.mpr hb, h.symm⟩)
    | inr p =>
      exact (hT (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, h.symm⟩))).elim
  apply strongApproximationOfLocalProjections D i S J hd harch hcompact hnoncompact
  · rintro ⟨w, hwS⟩ hw
    obtain ⟨p, hp, hsplit⟩ := hSplit ⟨w, hwS⟩ hw
    change w = Sum.inl p at hp
    subst w
    let F := D.Completion (.inl p)
    let L := baseChangedAlgebraicGroup F G
    have hL := OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G hG
    have hsplit : Nonempty (PointsOf L.val ≅ symplecticPoints F (HyperbolicIndex.{u} (n + 1))) :=
      not_not.mp hsplit
    obtain ⟨e⟩ := hsplit
    exact fullProjectionOfFiniteCompletion hfull D i p hG
      (Or.inl ⟨splitReductiveOfSymplecticPoints L hL n e, simplyConnectedOfSymplecticPoints n L e⟩)
  · rintro ⟨w, hwS⟩ hw
    obtain ⟨p, hp, hsplit⟩ := hSplit ⟨w, hwS⟩ hw
    change w = Sum.inl p at hp
    subst w
    let F := D.Completion (.inl p)
    let L := baseChangedAlgebraicGroup F G
    have hsplit : Nonempty (PointsOf L.val ≅ symplecticPoints F (HyperbolicIndex.{u} (n + 1))) :=
      not_not.mp hsplit
    obtain ⟨e⟩ := hsplit
    exact finiteContractedGeneration D i p (IsotropicTypeC.splitLocalGeneration F n L e)
  · exact hweak J

end FiniteApproximation


section ArchimedeanReduction

open Filter
open Specs.Arithmetic.ProjectiveRecurrence
  (cocharacterRadicalPoints localPointSet evaluateArchimedean)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open private localPointSet_eq_image from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence

private theorem contractedPi {I : Type*} [Finite I] {P : I → Type*}
    [∀ i, Group (P i)] [∀ i, TopologicalSpace (P i)]
    (h : ∀ i : I, Subgroup.closure {x : P i | Contracted x} = ⊤) :
    Subgroup.closure {x : ∀ i, P i | Contracted x} = ⊤ := by
  classical
  let C (i : I) : Set (P i) := {x | Contracted x}
  have h₁ (i : I) : 1 ∈ C i := by
    refine ⟨1, ?_⟩
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : P i)) atTop (𝓝 1))
  have hi : Set.univ.pi C ⊆ {x : ∀ i, P i | Contracted x} := by
    intro x hx
    have hC (i : I) := Set.mem_univ_pi.mp hx i
    choose a ha using hC
    exact ⟨a, tendsto_pi_nhds.mpr ha⟩
  apply top_unique
  have hp : Subgroup.closure (Set.univ.pi C) = ⊤ := by
    rw [Subgroup.closure_pi h₁]
    change Subgroup.pi Set.univ (fun i => Subgroup.closure ({x : P i | Contracted x})) = ⊤
    rw [show (fun i => Subgroup.closure ({x : P i | Contracted x})) =
      (fun i => (⊤ : Subgroup (P i))) from funext h]
    apply top_unique
    intro x _
    change ∀ i ∈ (Set.univ : Set I), x i ∈ (⊤ : Subgroup (P i))
    exact fun i _ => Subgroup.mem_top (x i)
  rw [← hp]
  exact Subgroup.closure_mono hi

private theorem noncompactProduct_mono
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    {S T : Finset D.Place} (hST : S ⊆ T)
    (hS : ¬ CompactSpace (FinitePoints D i S)) : ¬ CompactSpace (FinitePoints D i T) := by
  intro hT
  let _ := hT
  let f := forgetPlaces D i hST
  have hcont : Continuous f := by
    change Continuous (fun x : FinitePoints D i T => fun w : S => x ⟨w.1, hST w.2⟩)
    apply continuous_pi
    intro w
    let w' : T := ⟨w.1, hST w.2⟩
    exact continuous_apply w' 
  have hsurj : Function.Surjective f := by
    intro x
    refine ⟨fun w => if h : w.1 ∈ S then x ⟨w.1, h⟩ else 1, funext fun w => ?_⟩
    change (if h : w.1 ∈ S then x ⟨w.1, h⟩ else 1) = x w
    have hw : w.1 ∈ S := w.2
    rw [dite_eq_left hw]
  apply hS
  exact ⟨hsurj.range_eq ▸ isCompact_range hcont⟩

private theorem archimedeanContinuousScalars {K : Type u} [Field K] [NumberField K]
    (D : GlobalFieldData.{u,u} K) (hD : D = .number inferInstance) (w : D.InfinitePlace) :
    ∃ a : Algebra ℝ (D.Completion (.inr w)),
      letI := a
      Continuous (algebraMap ℝ (D.Completion (.inr w))) := by
  subst D
  obtain ⟨a, _, ha⟩ := LocalCocharacterEvaluation.archimedeanCompletionScalars w
  exact ⟨a, ha⟩

private theorem localCocharacterGeneration
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,u} K) (i : MatrixRealization G) (w : D.Place)
    (h : unipotentGenerated (baseChangedAlgebraicGroup (D.Completion w) G) = ⊤) :
    Subgroup.closure (localPointSet D i w
      (cocharacterRadicalPoints (baseChangedAlgebraicGroup (D.Completion w) G))) = ⊤ := by
  let F := D.Completion w
  let L := baseChangedAlgebraicGroup F G
  obtain ⟨_, j', _, e', he, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison K F G i
  let j : MatrixRealization L := j'
  let e : PointsIn j F ≃ₜ* LocalPoints D i w := e'
  let C : Set (PointsIn j F) := cocharacterRadicalPoints L
  have hs : localPointSet D i w (cocharacterRadicalPoints L) = e '' C :=
    localPointSet_eq_image D i w j e he C
  change Subgroup.closure (localPointSet D i w (cocharacterRadicalPoints L)) = ⊤
  rw [hs]
  change Subgroup.closure (e.toMonoidHom '' C) = ⊤
  rw [← MonoidHom.map_closure, parabolicGeneration_gives_cocharacterGeneration L j h,
    Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

private theorem localContractedGeneration
    {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,u} K) (i : MatrixRealization G) (w : D.Place)
    (h : unipotentGenerated (baseChangedAlgebraicGroup (D.Completion w) G) = ⊤)
    {E : Type v} [NontriviallyNormedField E] [Algebra E (D.Completion w)]
    (hE : Continuous (algebraMap E (D.Completion w))) :
    Subgroup.closure {x : LocalPoints D i w | Contracted x} = ⊤ := by
  obtain ⟨j, ⟨e⟩⟩ := completionMatrixComparison D i w
  exact contractedGeneration_transport e
    (contractedGeneration_of_parabolicGeneration _ j h hE)

set_option maxHeartbeats 600000 in
private theorem isolateArchimedeanFactors
    {K : Type u} [Field K] [NumberField K] (G : AffineAlgebraicGroup K)
    (i : MatrixRealization G)
    (D : GlobalFieldData.{u,u} K) (hD : D = .number inferInstance)
    (S : Finset D.Place) (A : Finset D.InfinitePlace)
    (hA : A.Nonempty) (hAS : ∀ w ∈ A, Sum.inr w ∉ S)
    (hRest : ∀ w : D.InfinitePlace, Sum.inr w ∉ S → w ∉ A →
      CompactSpace (LocalPoints D i (.inr w)))
    (hcompact : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hS : ¬ CompactSpace (FinitePoints D i S))
    (hG : IsAbsolutelyAlmostSimple G)
    (hGen : ∀ w ∈ A, unipotentGenerated (baseChangedAlgebraicGroup (D.Completion (.inr w)) G) = ⊤) :
    ((CompactProductIsolation.forgetOutside D i (S := S)
      (T := S ∪ A.image Sum.inr) Finset.subset_union_left).ker : Set (Adeles D i S))
      ⊆ diagonalClosure D i S := by
  let J : Finset D.Place := A.image Sum.inr
  let U := ArithmeticLatticeProjection.integralOutside D i (S ∪ J)
  have hJ : Disjoint J S := Finset.disjoint_left.mpr (by
    intro x hx hxS
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    exact hAS w hw hxS)
  obtain ⟨hUc, hUo⟩ := ArithmeticLatticeProjection.compactOpenOutside D i (S ∪ J)
    (fun w hw => hRest w (fun h => hw (Finset.mem_union_left _ h))
      (fun h => hw (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, h, rfl⟩))))
  have hgen (w : A) :=
    localCocharacterGeneration D i (.inr w.1) (hGen w.1 w.2)
  have hcontract (w : A) :
      Subgroup.closure {x : LocalPoints D i (.inr w.1) | Contracted x} = ⊤ := by
    obtain ⟨r, hr⟩ := archimedeanContinuousScalars D hD w.1
    let := r
    exact localContractedGeneration D i (.inr w.1) (hGen w.1 w.2) hr
  let f : A ≃ J := Equiv.ofBijective
    (fun w => ⟨Sum.inr w.1, Finset.mem_image.mpr ⟨w.1, w.2, rfl⟩⟩)
    ⟨fun x y h => Subtype.ext (Sum.inr_injective (congrArg Subtype.val h)), by
      intro x
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp x.2
      exact ⟨⟨w, hw⟩, Subtype.ext he⟩⟩
  let e : FinitePoints D i J ≃ₜ* (∀ w : A, LocalPoints D i (.inr w.1)) :=
    ContinuousMulEquiv.mk' (Homeomorph.piCongrLeft (Y := fun w : J => LocalPoints D i w.1) f).symm
      (fun _ _ => rfl)
  have hAT (w : A) : Sum.inr w.1 ∈ S ∪ J := Finset.mem_union_right _ (f w).2
  have hd := ProjectiveRecurrence.archimedeanLatticeProjection G i D hD S (S ∪ J) A U
    Finset.subset_union_left hA (fun w => hAS w.1 w.2) hAT
    hcompact hS hUc hUo hG (fun w => by rw [hgen w, Subgroup.coe_top]; exact dense_univ)
  have hcomp (g : FinitePoints D i (S ∪ J)) :
      e (forgetPlaces D i Finset.subset_union_right g) = evaluateArchimedean D i A hAT g :=
    rfl
  have hproj : Dense (projectedArithmetic D i S J U : Set (FinitePoints D i J)) := by
    apply (e.symm.surjective.denseRange.dense_image e.symm.continuous hd).mono
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨g, hg, ?_⟩
    rw [← hcomp g, ContinuousMulEquiv.symm_apply_apply]
  have hdcontract : Dense (Subgroup.closure {x : FinitePoints D i J | Contracted x} :
      Set (FinitePoints D i J)) := by
    rw [contractedGeneration_transport e.symm (contractedPi hcontract), Subgroup.coe_top]
    exact dense_univ
  have hinsert := (CompactProductIsolation.isolateAdelicFactors D i S J hJ U hUc hUo).2
    hproj hdcontract
  rw [← CompactProductIsolation.range_insertFinite_eq_ker D i hJ]
  rintro _ ⟨x, rfl⟩
  exact hinsert x

end ArchimedeanReduction


section ArchimedeanModels

open Filter
open Specs.AnisotropicTensorQuotients (columnBasis matrixColumnAction)
open Specs.GeometricRadicals (IsReductive)
open Specs.SymplecticDivisionForms (SplitComparison HermitianLaws dagger)
open Specs.SymplecticInvolutionModels
  (AntiAutomorphism HermitianPairing quaternionConjugate)
open Specs.SymplecticInvolutionModels.DivisionForms
  (toDivisionInvolution QuaternionLocalModel)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open QuaternionHermitianCocharacters (pairing adjoint)
open Specs.StandardGroups (generalLinearPoints)
open _root_.Specs.RM03.CSA (isCentralSimple degree)
open private pairing_mulVec from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionHermitianCocharacters
open private asMatrix_isClosedEmbedding
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
/-- A continuous homogeneous map with no nonzero zero has compact level
sets over an archimedean field. -/
private theorem compactLevel_of_anisotropic
    {F : Type u} [NormedField F] [NormedAlgebra ℝ F]
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace F V] [ProperSpace V]
    [NormedAddCommGroup W] [NormedSpace F W]
    (q : V → W) (hq : Continuous q)
    (hscale : ∀ t : F, ∀ v : V, q (t • v) = t ^ 2 • q v)
    (ha : ∀ v : V, q v = 0 → v = 0) (y : W) :
    IsCompact {v : V | q v = y} := by
  let S : Set V := Metric.sphere 0 1
  have hS := isCompact_sphere (0 : V) 1
  have hclosed : IsClosed {v : V | q v = y} := isClosed_eq hq continuous_const
  have normalize {v : V} (hv : v ≠ 0) :
      let t := algebraMap ℝ F ‖v‖⁻¹
      t • v ∈ S ∧ ‖q (t • v)‖ * ‖v‖ ^ 2 = ‖q v‖ := by
    dsimp only
    let t := algebraMap ℝ F ‖v‖⁻¹
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have ht : ‖t‖ = ‖v‖⁻¹ := by rw [norm_algebraMap', Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    constructor
    · change dist (t • v) 0 = 1
      rw [dist_zero_right, norm_smul, ht, inv_mul_cancel₀ hn.ne']
    · change ‖q (t • v)‖ * ‖v‖ ^ 2 = ‖q v‖
      rw [hscale, norm_smul, norm_pow, ht]
      field_simp [hn.ne']
  by_cases hs : S.Nonempty
  · obtain ⟨v, hv, hmin⟩ := hS.exists_isMinOn hs hq.norm.continuousOn
    have hv₀ : v ≠ 0 := by
      intro he
      have h : dist v 0 = 1 := hv
      simpa [he] using h
    let a := ‖q v‖
    have ha₀ : 0 < a := norm_pos_iff.mpr (fun h => hv₀ (ha v h))
    refine (isCompact_closedBall (0 : V) (max 1 (‖y‖ / a))).of_isClosed_subset hclosed ?_
    intro x hx
    change q x = y at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hx' : x = 0
    · simpa only [hx', norm_zero] using (le_trans zero_le_one (le_max_left (1 : ℝ) (‖y‖ / a)))
    have hnorm := normalize hx'
    have hb := mul_le_mul_of_nonneg_right (hmin hnorm.1) (sq_nonneg ‖x‖)
    change a * ‖x‖ ^ 2 ≤ _ at hb
    rw [hnorm.2, hx] at hb
    have hr : ‖x‖ ^ 2 ≤ ‖y‖ / a := (le_div_iff₀ ha₀).mpr (by simpa only [mul_comm] using hb)
    by_cases h : ‖x‖ ≤ 1
    · exact h.trans (le_max_left _ _)
    · exact (show ‖x‖ ≤ ‖x‖ ^ 2 by nlinarith [norm_nonneg x]).trans
        (hr.trans (le_max_right _ _))
  · refine (isCompact_singleton (x := (0 : V))).of_isClosed_subset hclosed ?_
    intro x _
    by_contra hn
    exact hs ⟨_, (normalize (show x ≠ 0 from hn)).1⟩

private theorem pairing_smul_diagonal {F B : Type u} [Field F] [Ring B] [Algebra F B]
    {r : ℕ} (b : AntiAutomorphism F B) (H : Matrix (Fin r) (Fin r) B)
    (hh : HermitianLaws b (pairing b.toAlgHom H))
    (t : F) (x : Fin r → B) :
    pairing b.toAlgHom H (t • x) (t • x) = t ^ 2 • pairing b.toAlgHom H x x := by
  let h := pairing b.toAlgHom H
  let bar := (MulOpposite.opLinearEquiv F).symm.toLinearMap.comp b.toLinearMap
  have right (x y : Fin r → B) : h x (t • y) = t • h x y := by
    have hs (a : B) : a * algebraMap F B t = t • a :=
      (Algebra.commutes t a).symm.trans (Algebra.smul_def' t a).symm
    simpa only [hs, Pi.smul_def] using hh.mul_right x y (algebraMap F B t)
  have left (x y : Fin r → B) : h (t • x) y = t • h x y := by
    calc
      _ = bar (h y (t • x)) := hh.symmetric y (t • x)
      _ = bar (t • h y x) := congrArg bar (right y x)
      _ = _ := (map_smul bar t _).trans (congrArg (t • ·) (hh.symmetric y x).symm)
  change h (t • x) (t • x) = _
  rw [left, right, ← mul_smul, pow_two]

private theorem isometry_pairing_preserved {F A B : Type u} [Field F]
    [Ring A] [Algebra F A] [DivisionRing B] [Algebra F B] {r : ℕ}
    (s : Involution F A) (e : A ≃ₐ[F] Matrix (Fin r) (Fin r) B)
    (b : AntiAutomorphism F B) (H : (Matrix (Fin r) (Fin r) B)ˣ)
    (he : ∀ a, e (s.toLinearMap a) = H.inv * dagger b (e a) * H.val)
    (g : (s.baseChange F).isometries) (x : Fin r → B) :
    let M := e (Algebra.TensorProduct.lid F A g.val.val)
    pairing b.toAlgHom H.val (M.mulVec x) (M.mulVec x) = pairing b.toAlgHom H.val x x := by
  let d := Algebra.TensorProduct.lid F A
  have hd (a : F ⊗[F] A) : d ((s.baseChange F).toLinearMap a) = s.toLinearMap (d a) := by
    induction a using TensorProduct.inductionOn with
    | tmul z a => rw [Involution.baseChange_tmul, Algebra.TensorProduct.lid_tmul,
        Algebra.TensorProduct.lid_tmul, map_smul]
    | add x y hx hy => simp only [map_add, hx, hy]
  let a := d g.val.val
  have h := congrArg (fun z => e (d z)) g.property
  change e (d ((s.baseChange F).toLinearMap g.val.val * g.val.val)) = e (d 1) at h
  rw [map_mul, map_mul, hd, he, map_one, map_one] at h
  let M := e a
  have hh : (H.inv * adjoint b.toAlgHom M * H.val) * M = 1 := h
  have hGram : (adjoint b.toAlgHom M * H.val) * M = H.val := by
    calc
      _ = H.val * ((H.inv * adjoint b.toAlgHom M * H.val) * M) := by
        simp only [← mul_assoc, H.val_inv, one_mul]
      _ = _ := by rw [hh, mul_one]
  change pairing b.toAlgHom H.val (M.mulVec x) (M.mulVec x) = _
  rw [pairing_mulVec, hGram]

set_option maxHeartbeats 750000 in
set_option backward.isDefEq.respectTransparency false in
private theorem compactQuaternionIsometryGroup
    {F A B : Type u} [NontriviallyNormedField F] [CompleteSpace F] [ProperSpace F]
    [NormedAlgebra ℝ F] [Ring A] [Algebra F A] [DivisionRing B] [Algebra F B]
    [FiniteDimensional F B] {r : ℕ}
    (s : Involution F A) (e : A ≃ₐ[F] Matrix (Fin r) (Fin r) B)
    (b : AntiAutomorphism F B) (H : (Matrix (Fin r) (Fin r) B)ˣ)
    (he : ∀ a, e (s.toLinearMap a) = H.inv * dagger b (e a) * H.val)
    (hh : HermitianLaws b (pairing b.toAlgHom H.val))
    (ha : ∀ x, pairing b.toAlgHom H.val x x = 0 → x = 0)
    (E : ∀ (R : Type u) [CommRing R] [Algebra F R],
      (R ⊗[F] A) ≃ₐ[R] Matrix (Fin r) (Fin r) (R ⊗[F] B))
    (hE : ∀ (R : Type u) [CommRing R] [Algebra F R] (a : A),
      E R (1 ⊗ₜ[F] a) = (e a).map (Specs.SymplecticDivisionForms.intoTensor R B))
    {G : AffineAlgebraicGroup F} (c : PointsOf G.val ≅ isometryPoints s)
    (j : MatrixRealization G) : CompactSpace (PointsIn j F) := by
  let J := ULift.{u} (Fin (Module.finrank F B))
  let d : Module.Basis J F B := (Module.finBasis F B).reindex Equiv.ulift.symm
  let size := Fintype.card (Fin r × J)
  let ρ := columnRepresentation d E s e hE
  let τ : PointsOf G.val ⟶ generalLinearPoints F (Index.{u} size) := c.hom ≫ ρ
  have hτ (R : TestAlgebra F) : Function.Injective (τ.app R) := by
    change Function.Injective (fun g => ρ.app R (c.hom.app R g))
    exact (columnRepresentation_injective d E s e hE R).comp
      (ConcreteCategory.bijective_of_isIso (c.hom.app R)).1
  let i := realizationOfNaturalMatrices size τ hτ
  let bindex : Index.{u} i.size ≃ Fin r × J := columnIndex
  let q : (Fin r → B) → B := fun x => pairing b.toAlgHom H.val x x
  let _ : NormedAddCommGroup B :=
    NormedAddCommGroup.induced B (J → F) d.equivFun.toAddEquiv.toAddMonoidHom d.equivFun.injective
  let _ : NormedSpace F B := NormedSpace.induced F B (J → F) d.equivFun.toLinearMap
  let _ : ProperSpace B := FiniteDimensional.proper F B
  let _ : ContinuousMul B := ⟨(LinearMap.mul F B).toContinuousBilinearMap.continuous₂⟩
  let bar := (MulOpposite.opLinearEquiv F).symm.toLinearMap.comp b.toLinearMap
  have hb : Continuous bar := bar.continuous_of_finiteDimensional
  have hq : Continuous q := by
    change Continuous (fun x : Fin r → B => ∑ j, (∑ i, bar (x i) * H.val i j) * x j)
    refine continuous_finsetSum _ (fun j _ => (continuous_finsetSum _ ?_).mul (continuous_apply j))
    exact fun i _ => (hb.comp (continuous_apply i)).mul continuous_const
  let C : Set (Matrix (Fin r) (Fin r) B) := Matrix.transpose ''
    (Set.univ.pi fun k : Fin r => {x : Fin r → B | q x = q (Pi.single k 1)})
  have hC : IsCompact C := by
    have ht : Continuous (Matrix.transpose : Matrix (Fin r) (Fin r) B → _) :=
      continuous_matrix fun x y => (continuous_apply x).comp (continuous_apply y)
    exact (isCompact_univ_pi fun k => compactLevel_of_anisotropic q hq
      (pairing_smul_diagonal b H.val hh) ha (q (Pi.single k 1))).image ht
  let m (g : PointsIn i F) : Matrix (Fin r) (Fin r) B :=
    e (Algebra.TensorProduct.lid F A (c.hom.app (CommAlgCat.of F F) g).val.val)
  have hm (g : PointsIn i F) : m g ∈ C := by
    refine ⟨(m g).transpose, Set.mem_univ_pi.mpr fun k => ?_, Matrix.transpose_transpose _⟩
    have hp := isometry_pairing_preserved s e b H he (c.hom.app (CommAlgCat.of F F) g)
      (Pi.single k 1)
    change q ((m g).mulVec (Pi.single k 1)) = q (Pi.single k 1) at hp
    change q ((m g).col k) = q (Pi.single k 1)
    simpa only [Matrix.mulVec_single_one] using hp
  let k : Matrix (Fin r) (Fin r) B →ₗ[F] Matrix (Index.{u} i.size) (Index.{u} i.size) F :=
    (Matrix.reindexAlgEquiv F F bindex.symm).toLinearMap.comp
      ((columnMatrix d E F).toLinearMap.comp
        ((Algebra.TensorProduct.includeRight : A →ₐ[F] F ⊗[F] A).toLinearMap.comp e.symm.toLinearMap))
  have hk₀ (g : PointsIn i F) : (asMatrix i F g).val = k (m g) := by
    have heq := asMatrix_realizationOfNaturalMatrices size τ hτ F g
    change (asMatrix i F g).val = _ 
    have ha : (Algebra.TensorProduct.includeRight : A →ₐ[F] F ⊗[F] A)
        (e.symm (m g)) = (c.hom.app (CommAlgCat.of F F) g).val.val := by
      dsimp only [m]
      rw [AlgEquiv.symm_apply_apply]
      exact (Algebra.TensorProduct.lid F A).symm_apply_apply _
    have hk (g : PointsIn i F) :
        (τ.app (CommAlgCat.of F F) g : GL (Index.{u} size) F).val =
          (Matrix.reindexAlgEquiv F F bindex.symm) (columnMatrix d E F
            (c.hom.app (CommAlgCat.of F F) g).val.val) := rfl
    rw [congrArg Units.val heq, hk]
    change _ = (Matrix.reindexAlgEquiv F F bindex.symm) (columnMatrix d E F
      ((Algebra.TensorProduct.includeRight : A →ₐ[F] F ⊗[F] A) (e.symm (m g))))
    rw [ha]
  have hc : IsCompact (k '' C) := hC.image k.continuous_of_finiteDimensional
  let M := Matrix (Index.{u} i.size) (Index.{u} i.size) F
  let f := (Units.embedProduct M) ∘ asMatrix i F
  have hclosed : IsClosedEmbedding f :=
    Units.isClosedEmbedding_embedProduct.comp (asMatrix_isClosedEmbedding i F)
  have hprod : IsCompact ((k '' C) ×ˢ (MulOpposite.op '' (k '' C))) :=
    hc.prod (hc.image MulOpposite.continuous_op)
  have hpre := hclosed.isCompact_preimage hprod
  have hall : f ⁻¹' ((k '' C) ×ˢ (MulOpposite.op '' (k '' C))) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g
    change (asMatrix i F g).val ∈ k '' C ∧ MulOpposite.op ((asMatrix i F g)⁻¹.val) ∈
      MulOpposite.op '' (k '' C)
    refine ⟨⟨m g, hm g, (hk₀ g).symm⟩, ?_⟩
    rw [← map_inv]
    exact ⟨_, ⟨m g⁻¹, hm g⁻¹, (hk₀ g⁻¹).symm⟩, rfl⟩
  let _ : CompactSpace (PointsIn i F) := ⟨hall ▸ hpre⟩
  let f := AdelicGroups.changePoints i j F
  exact ⟨f.surjective.range_eq ▸ isCompact_range (AdelicGroups.continuous_changePoints i j F)⟩

end ArchimedeanModels

section NumberFields

open Specs.SymplecticDivisionForms (SplitComparison)
open Specs.SymplecticInvolutionModels (HermitianPairing)
open Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open QuaternionHermitianCocharacters (pairing)
open _root_.Specs.RM03.CSA (isCentralSimple)
open private archimedeanTypeCOfRingEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicTypeC
open private splitComparisonBaseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels


open Specs.SymplecticInvolutionModels.DivisionForms (NonarchimedeanLocalAlternatives)

private theorem compactOrGeneratedOfArchimedeanModel
    {F A : Type u} [NontriviallyNormedField F] [CompleteSpace F] [ProperSpace F]
    [NormedAlgebra ℝ F] [Ring A] [Algebra F A] (s : Involution F A) (n : ℕ)
    (J : AffineAlgebraicGroup F) (hJ : IsAbsolutelyAlmostSimple J)
    (e : PointsOf J.val ≅ isometryPoints s) (j : MatrixRealization J)
    (alt : NonarchimedeanLocalAlternatives s (n + 1)) :
    CompactSpace (PointsIn j F) ∨ unipotentGenerated J = ⊤ := by
  have hR := reductive_of_semisimple J hJ.1
  rcases alt with h | h
  · obtain ⟨_, _, _, _, _, _, m, _⟩ := h
    exact Or.inr (IsotropicTypeC.splitLocalGeneration F n J (e ≪≫ m))
  · obtain ⟨B, hDiv, hAlg, hB, degB, model⟩ := h
    let := hDiv
    let := hAlg
    let _ : FiniteDimensional F B := hB.2.2
    obtain ⟨eB, b, H, hb, hH, hAdj, _, hLaws, hnondeg, hcentral, ⟨E, m, hE, _⟩, _⟩ := model
    let q := pairing b.toAlgHom H.val
    by_cases ha : ∀ x, q x x = 0 → x = 0
    · exact Or.inl (compactQuaternionIsometryGroup s eB b H hAdj hLaws ha E hE e j)
    · obtain ⟨x, hx⟩ := not_forall.mp ha
      have hx := not_imp.mp hx
      let form : HermitianPairing b (Fin (n + 1) → B) :=
        { value := q
          add_right := hLaws.add_right
          smul_right := hLaws.mul_right
          hermitian := hLaws.symmetric
          nondegenerate := hnondeg
          central_norm := hcentral }
      obtain ⟨y, hxy, hyx, hyy⟩ :=
        SymplecticInvolutionModels.quaternionHyperbolicPartner hB degB b hb form x hx.2 hx.1
      let _ : Infinite F := Infinite.of_injective (algebraMap ℝ F) (algebraMap ℝ F).injective
      exact Or.inr (IsotropicTypeC.quaternionLocalGeneration
        F J hR hB degB b hb H hH (e ≪≫ m) hnondeg hcentral x y hx.1 hyy hxy hyx)

set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency false in
private theorem symplecticArchimedeanCompactOrGenerated
    {K A L : Type u} [Field K] [NumberField K] [Ring A] [Algebra K A]
    [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (hA : isCentralSimple K A) (s : Involution K A) (n : ℕ)
    (hs : SplitComparison (toDivisionInvolution s) L (n + 1))
    (G : AffineAlgebraicGroup K) (hG : IsAbsolutelyAlmostSimple G)
    (c : PointsOf G.val ≅ isometryPoints s) (i : MatrixRealization G)
    (D : GlobalFieldData.{u,u} K) (hD : D = .number inferInstance) (w : D.InfinitePlace) :
    CompactSpace (LocalPoints D i (.inr w)) ∨
      unipotentGenerated (baseChangedAlgebraicGroup (D.Completion (.inr w)) G) = ⊤ := by
  subst D
  let D : GlobalFieldData.{u,u} K := .number inferInstance
  let F := w.Completion
  let _ : Algebra K F := AdelicGroups.completionAlgebra D (.inr w)
  let J := baseChangedAlgebraicGroup F G
  obtain ⟨normedAlg, finDim, _, _⟩ := ArchimedeanLieChart.completionRealStructures K w
  let _ : NormedAlgebra ℝ F := normedAlg
  let _ : NontriviallyNormedField F :=
    { toNormedField := inferInstanceAs (NormedField w.Completion)
      non_trivial := by
        refine ⟨algebraMap ℝ F 2, ?_⟩
        rw [norm_algebraMap']
        norm_num }
  let _ : FiniteDimensional ℝ F := finDim
  let _ : ProperSpace F := FiniteDimensional.proper ℝ F
  have hJ := OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G hG
  let t := s.baseChange F
  have hAf := _root_.RM03.CSA.isCentralSimple_baseChange (L := F) hA
  have hSf := splitComparisonBaseChange (F := F) s hs
  have hField : Nonempty (F ≃+* ℝ) ∨ Nonempty (F ≃+* ℂ) := by
    rcases w.isReal_or_isComplex with h | h
    · obtain ⟨e, _⟩ := numberRealCompletion w h
      exact Or.inl ⟨e⟩
    · obtain ⟨e, _⟩ := numberComplexCompletion w h
      exact Or.inr ⟨e⟩
  have alt := archimedeanTypeCOfRingEquiv hAf t hSf hField
  obtain ⟨j, ⟨j₀⟩⟩ := completionMatrixComparison D i (.inr w)
  let j' : MatrixRealization J := j
  have h : CompactSpace (PointsIn j' F) ∨ unipotentGenerated J = ⊤ :=
    compactOrGeneratedOfArchimedeanModel (F := F) (A := F ⊗[K] A) t n J hJ
      (completionIsometryComparison (F := F) c) j' alt
  let e₀ : PointsIn j' F ≃ₜ* PointsIn i F := j₀
  change CompactSpace (PointsIn i F) ∨ unipotentGenerated J = ⊤
  rcases h with h | h
  · let := h
    exact Or.inl ⟨e₀.surjective.range_eq ▸ isCompact_range e₀.continuous⟩
  · exact Or.inr h

private theorem strongApproximationOfNumberField
    (hfull : FiniteCovolumeSubgroup.{u}) {K A L : Type u} [Field K] [NumberField K]
    [Ring A] [Algebra K A] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (hA : isCentralSimple K A) (s : Involution K A) (n : ℕ)
    (hs : SplitComparison (toDivisionInvolution s) L (n + 1))
    (G : AffineAlgebraicGroup K) (hG : IsAbsolutelyAlmostSimple G)
    (c : PointsOf G.val ≅ isometryPoints s) (i : MatrixRealization G)
    (D : GlobalFieldData.{u,u} K) (hD : D = .number inferInstance)
    (S : Finset D.Place)
    (hcompact : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hS : ¬ CompactSpace (FinitePoints D i S))
    (hweak : AdelicGroups.WeakApproximation D i) :
    StrongApproximation D i S := by
  let _ : Finite D.InfinitePlace := by
    subst D
    exact inferInstanceAs (Finite (NumberField.InfinitePlace K))
  let _ : Fintype D.InfinitePlace := Fintype.ofFinite _
  let A : Finset D.InfinitePlace := Finset.univ.filter fun w =>
    Sum.inr w ∉ S ∧ ¬ CompactSpace (LocalPoints D i (.inr w))
  have hMem (w : D.InfinitePlace) :
      w ∈ A ↔ Sum.inr w ∉ S ∧ ¬ CompactSpace (LocalPoints D i (.inr w)) := by
    simp [A]
  have hRest (w : D.InfinitePlace) (hwS : Sum.inr w ∉ S) (hwA : w ∉ A) :
      CompactSpace (LocalPoints D i (.inr w)) := by
    by_contra hnc
    exact hwA ((hMem w).mpr ⟨hwS, hnc⟩)
  by_cases hne : A.Nonempty
  · let J : Finset D.Place := A.image Sum.inr
    let T := S ∪ J
    have hST : S ⊆ T := Finset.subset_union_left
    have hT : ¬ CompactSpace (FinitePoints D i T) := noncompactProduct_mono D i hST hS
    have hg (w : D.InfinitePlace) (hw : w ∈ A) :
        unipotentGenerated (baseChangedAlgebraicGroup (D.Completion (.inr w)) G) = ⊤ :=
      (symplecticArchimedeanCompactOrGenerated hA s n hs G hG c i D hD w).resolve_left
        ((hMem w).mp hw).2
    have hk := isolateArchimedeanFactors G i D hD S A hne (fun w hw => ((hMem w).mp hw).1)
      hRest hcompact hS hG hg
    have hcomp (w : D.InfinitePlace) (hw : Sum.inr w ∉ T) :
        CompactSpace (LocalPoints D i (.inr w)) :=
      hRest w (fun hwS => hw (hST hwS))
        (fun hwA => hw (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, hwA, rfl⟩)))
    have hstrong := strongApproximation_when_archimedean_complement_compact
      hfull D hA s n hs G hG c i T hcomp hcompact hT hweak
    exact ((CompactProductIsolation.enlargeOmittedSet D i S T hST).2 hk).2.2.mp hstrong
  · exact strongApproximation_when_archimedean_complement_compact
      hfull D hA s n hs G hG c i S
      (fun w hw => hRest w hw (fun hm => hne ⟨w, hm⟩)) hcompact hS hweak

end NumberFields

open Specs.SymplecticDivisionForms (SplitComparison)
open Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open _root_.Specs.RM03.CSA (isCentralSimple)


section NumberUniverse

/-- The local data used by the two adelic predicates, with their instance
choices recorded explicitly. -/
private structure LocalApproximationData (P : Type u) [Group P] where
  point : Type u
  group : Group point
  topology : TopologicalSpace point
  integral : @Subgroup point group
  extend : letI := group; P →* point

private def localApproximationData {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.Place) :
    LocalApproximationData (Specs.IntegralModels.RationalPoints G) :=
  ⟨LocalPoints D i w, inferInstance, inferInstance, localSubgroup D i w, localPoint D i w⟩

private def productCompactOfLocalData {P : Type u} [Group P] {W : Type*} (S : Finset W)
    (m : W → LocalApproximationData P) : Prop :=
  letI (w : S) : TopologicalSpace (m w.1).point := (m w.1).topology
  CompactSpace (∀ w : S, (m w.1).point)

private def strongApproximationOfLocalData {P : Type u} [Group P] {W : Type*}
    (S : Finset W) (m : W → LocalApproximationData P) : Prop :=
  let I := {w : W // w ∉ S}
  letI (w : I) : TopologicalSpace (m w.1).point := (m w.1).topology
  Dense {x : Πʳ w : I, [(m w.1).point, ↑(m w.1).integral] |
    ∃ g : P, ∀ w : I, x w = (m w.1).extend g}

private theorem numberLocalData_eq {K : Type u} [Field K] [h : NumberField K]
    {G : AffineAlgebraicGroup K} (i : MatrixRealization G) :
    (fun w : NumberPlace K => localApproximationData (.number h : GlobalFieldData.{u,u} K) i w) =
      (fun w : NumberPlace K => localApproximationData (.number h : GlobalFieldData.{u,v} K) i w) := by
  funext w
  cases w <;> rfl

private def finiteProductCompact {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (S : Finset D.Place) : Prop :=
  CompactSpace (FinitePoints D i S)

private theorem numberFiniteCompact_iff {K : Type u} [Field K] [h : NumberField K]
    {G : AffineAlgebraicGroup K} (i : MatrixRealization G) (S : Finset (NumberPlace K)) :
    finiteProductCompact (.number h : GlobalFieldData.{u,u} K) i S ↔
      finiteProductCompact (.number h : GlobalFieldData.{u,v} K) i S :=
  Iff.of_eq (congrArg (productCompactOfLocalData S) (numberLocalData_eq i))

private theorem numberStrongApproximation_iff {K : Type u} [Field K] [h : NumberField K]
    {G : AffineAlgebraicGroup K} (i : MatrixRealization G) (S : Finset (NumberPlace K)) :
    StrongApproximation (.number h : GlobalFieldData.{u,u} K) i S ↔
      StrongApproximation (.number h : GlobalFieldData.{u,v} K) i S := by
  change strongApproximationOfLocalData S
      (fun w => localApproximationData (.number h : GlobalFieldData.{u,u} K) i w) ↔
    strongApproximationOfLocalData S
      (fun w => localApproximationData (.number h : GlobalFieldData.{u,v} K) i w)
  exact Iff.of_eq (congrArg (strongApproximationOfLocalData S) (numberLocalData_eq i))

end NumberUniverse

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
theorem typeC_conditional.{fieldLevel, auxiliaryLevel}
    (_normal : LocalNormalClosure.{fieldLevel}) (full : FiniteCovolumeSubgroup.{fieldLevel}) : TypeC.{fieldLevel, auxiliaryLevel} := by
  intro K A L _ D _ _ _ _ _ hA s n hn hs G hG hSC ha hc
  obtain ⟨c⟩ := hc
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  intro i
  obtain ⟨hcompact, hweak⟩ :=
    compactnessAndWeakApproximation_of_symplecticModel D hA s (n + 1) hs G hG ha c i
  refine ⟨hcompact, fun S _ hS => ?_⟩
  cases D with
  | number h =>
    let := h
    let N : GlobalFieldData.{fieldLevel,fieldLevel} K := .number h
    obtain ⟨hcN, hwN⟩ :=
      compactnessAndWeakApproximation_of_symplecticModel N hA s (n + 1) hs G hG ha c i
    have hnN : ¬ finiteProductCompact N i S := fun hc =>
      hS ((numberFiniteCompact_iff.{fieldLevel, auxiliaryLevel} i S).mp hc)
    have hsN := strongApproximationOfNumberField full hA s n hs G hG c i N rfl S hcN hnN hwN
    exact (numberStrongApproximation_iff.{fieldLevel, auxiliaryLevel} i S).mp hsN
  | function F t =>
    exact strongApproximation_when_archimedean_complement_compact full (.function F t)
      hA s n hs G hG c i S (fun w _ => w.elim) hcompact hS hweak

end LinearAlgebraicGroups.Arithmetic.AnisotropicSymplecticApproximation

universe v8_closure_15795ed0cb7bbe10_u0 v8_closure_15795ed0cb7bbe10_u1
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«AnisotropicSymplecticApproximation».«typeC» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«AnisotropicSymplecticApproximation».«TypeC».{v8_closure_15795ed0cb7bbe10_u0, v8_closure_15795ed0cb7bbe10_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«AnisotropicSymplecticApproximation».«typeC_conditional».{v8_closure_15795ed0cb7bbe10_u0, v8_closure_15795ed0cb7bbe10_u1} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalProjectedClosure».«localNormalClosure».{v8_closure_15795ed0cb7bbe10_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalProjectedClosure».«localProjectedClosure».{v8_closure_15795ed0cb7bbe10_u0})
