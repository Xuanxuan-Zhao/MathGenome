import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AnisotropicDivisionApproximation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.CompactProductIsolation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.DivisionNormOneAdelicCompactness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.DivisionNormOneArchimedeanReduction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.DivisionNormOneFiniteSplitFactors
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicInnerTypeA
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuotientTransport
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalCocharacterEvaluation
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.NormOneGroup
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.QuaternionBasis
import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.Tactic.NoncommRing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuadraticIsotropy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

open scoped Classical CategoryTheory.MonObj

noncomputable section

universe u v

namespace LinearAlgebraicGroups.Arithmetic.AnisotropicDivisionApproximation

open Specs.Arithmetic.LocalProjectedClosure (LocalNormalClosure FiniteCovolumeSubgroup)

open MeasureTheory Topology
open ArithmeticLatticeProjection (FiniteInvariantQuotientMeasure)
open LocalQuotientTransport (RightCosets RightInvariant coset rightTranslate imageSubgroup)

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

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.Arithmetic.LocalQuotientMixing (MixingCases)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open LocalAlgebraicTransport (pointTopology RationalPoints)

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

open AdelicGroups (Adeles LocalPoints Outside StrongApproximation localSubgroup)
open ArithmeticLatticeProjection (FinitePoints diagonalSubgroup lattice forgetPlaces)
open CompactProductIsolation (Contracted insertFinite diagonalClosure projectedArithmetic)
open Specs.IntegralModels (MatrixRealization)

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

/-- Enlarging the omitted set preserves noncompactness of its local product. -/
private theorem noncompactFiniteProductOfSubset {K : Type u} [Field K]
    {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    {S T : Finset D.Place} (hST : S ⊆ T) (hS : ¬ CompactSpace (FinitePoints D i S)) :
    ¬ CompactSpace (FinitePoints D i T) := by
  intro hT
  let f := forgetPlaces D i hST
  have hf : Continuous (f : FinitePoints D i T → FinitePoints D i S) := by
    apply continuous_pi
    intro w
    let w' : (↑T : Set D.Place) := ⟨w.1, hST w.2⟩
    change Continuous fun x : FinitePoints D i T => x w'
    exact continuous_apply w'
  have hsurj : Function.Surjective f := by
    intro x
    refine ⟨fun w => if hw : w.1 ∈ S then x ⟨w.1, hw⟩ else 1, ?_⟩
    funext w
    change (if hw : w.1 ∈ S then x ⟨w.1, hw⟩ else 1) = x w
    have hw : w.1 ∈ S := w.2
    rw [dite_eq_left hw]
  have hc : IsCompact (Set.range f) := isCompact_range hf
  exact hS ⟨hsurj.range_eq ▸ hc⟩

/-- A finite product whose arithmetic projection is dense and whose contracted
elements generate densely can be moved to the omitted set. -/
theorem strongApproximationAfterIsolating {K : Type u} [Field K]
    {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (S J : Finset D.Place) (hd : Disjoint J S)
    (U : Subgroup (Adeles D i (S ∪ J)))
    (hU : IsCompact (U : Set (Adeles D i (S ∪ J))))
    (hU' : IsOpen (U : Set (Adeles D i (S ∪ J))))
    (hP : Dense (projectedArithmetic D i S J U : Set (FinitePoints D i J)))
    (hC : Dense (Subgroup.closure {x : FinitePoints D i J | Contracted x} :
      Set (FinitePoints D i J))) :
    StrongApproximation D i (S ∪ J) → StrongApproximation D i S := by
  intro hT
  have hins := (CompactProductIsolation.isolateAdelicFactors D i S J hd U hU hU').2 hP hC
  have hker :
      ((CompactProductIsolation.forgetOutside D i (S := S) (T := S ∪ J)
        Finset.subset_union_left).ker : Set (Adeles D i S)) ⊆ diagonalClosure D i S := by
    rw [← CompactProductIsolation.range_insertFinite_eq_ker D i hd]
    rintro _ ⟨x, rfl⟩
    exact hins x
  exact ((CompactProductIsolation.enlargeOmittedSet D i S (S ∪ J) Finset.subset_union_left).2
    hker).2.2.mp hT

open Filter

private theorem contractedConjugate {P : Type u} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] {g : P} (hg : Contracted g) (b : P) :
    Contracted (MulAut.conj b g) := by
  obtain ⟨a, ha⟩ := hg
  refine ⟨MulAut.conj b a, ?_⟩
  have hc : Continuous (MulAut.conj b : P → P) :=
    (continuous_const.mul continuous_id).mul continuous_const
  have h := (hc.tendsto 1).comp ha
  simpa only [Function.comp_def, map_one, map_mul, map_inv, map_pow] using h

/-- A single noncentral contracted element gives dense generation by contracted
elements, since that generating family contains all its conjugates. -/
theorem denseContractedOfNormalClosure (hnormal : LocalNormalClosure.{u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (J : AffineAlgebraicGroup F) (hJ : IsAbsolutelyAlmostSimple J) (hmix : MixingCases J) :
    letI := pointTopology J.val.X
    IsTopologicalGroup (RationalPoints J.val.X) →
    ∀ g : RationalPoints J.val.X, g ∉ Subgroup.center (RationalPoints J.val.X) →
      Contracted g → Dense (Subgroup.closure {x : RationalPoints J.val.X | Contracted x} : Set (RationalPoints J.val.X)) := by
  let _ := pointTopology J.val.X
  intro htop g hg hcon
  let : IsTopologicalGroup (RationalPoints J.val.X) := htop
  have hle : Group.conjugatesOfSet {g} ⊆ {x : RationalPoints J.val.X | Contracted x} := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨b, rfl⟩ := isConj_iff.mp hxy
    have hx' : x = g := Set.mem_singleton_iff.mp hx
    change Contracted (b * x * b⁻¹)
    rw [hx']
    exact contractedConjugate hcon b
  exact (dense_iff_closure_eq.mpr (hnormal F J hJ hmix g hg)).mono (Subgroup.closure_mono hle)

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

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct
open Specs.Unipotent (Index baseChangedAlgebraicGroup)
open private coordinateMap coordinateMap_spec from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels
open private glEvaluation glEvaluation_entry from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private matrixPresentation glVal_isEmbedding continuous_glEvaluation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
open Specs.StandardGroups (GLCoordinates universalMatrix)
open LocalAlgebraicTransport (evaluation)
open AdelicGroups (PointsIn asMatrix localPoint)
open Opposite

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
    (hL : IsAbsolutelyAlmostSimple (baseChangedAlgebraicGroup (D.Completion (.inl w)) G))
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
  have htop := LocalAlgebraicTransport.rationalPointTopologicalGroup L
  exact fullProjectionOfLocalModel hfull L hL hmix H hclosed hnd hμ htop
    ((singletonLocalPoints D i (.inl w)).trans e)

/-- An isomorphism of affine group schemes can be recovered from the
natural isomorphism of their group functors. -/
private theorem schemeIsoOfPointIso {K : Type u} [Field K]
    {G H : AffineAlgebraicGroup K}
    (e : (groupPointsFunctor K).obj G.val ≅ (groupPointsFunctor K).obj H.val) :
    ∃ f : G.val ≅ H.val, (groupPointsFunctor K).mapIso f = e := by
  obtain ⟨a, ha⟩ := (groupHomComparison K G.val H.val G.property.1).surjective e.hom
  obtain ⟨b, hb⟩ := (groupHomComparison K H.val G.val H.property.1).surjective e.inv
  have hab : a ≫ b = 𝟙 _ := (groupHomComparison K G.val G.val G.property.1).injective
    (by simp [ha, hb])
  have hba : b ≫ a = 𝟙 _ := (groupHomComparison K H.val H.val H.property.1).injective
    (by simp [ha, hb])
  exact ⟨⟨a, b, hab, hba⟩, Iso.ext ha⟩

/-- Pull a closed realization back along a group scheme isomorphism. -/
private def pullbackRealization {K : Type u} [Field K] {G H : AffineAlgebraicGroup K}
    (e : G.val ≅ H.val) (j : MatrixRealization H) : MatrixRealization G where
  size := j.size
  ambient := j.ambient
  matrix := j.matrix
  embedding := e.hom ≫ j.embedding
  closed := by
    change IsClosedImmersion (e.hom.hom.hom.left ≫ j.embedding.hom.hom.left)
    let : IsIso e.hom.hom.hom.left :=
      (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso e.hom
    let := j.closed
    infer_instance

private def schemePointsEquiv {K : Type u} [Field K] {G H : AffineAlgebraicGroup K}
    (e : G.val ≅ H.val) (j : MatrixRealization H) (R : Type u) [CommRing R] [Algebra K R] :
    PointsIn (pullbackRealization e j) R ≃* PointsIn j R :=
  (((groupPointsFunctor K).mapIso e).app (CommAlgCat.of K R)).groupIsoToMulEquiv

private theorem pullbackRealization_asMatrix {K : Type u} [Field K] {G H : AffineAlgebraicGroup K}
    (e : G.val ≅ H.val) (j : MatrixRealization H) (R : Type u) [CommRing R] [Algebra K R]
    (x : PointsIn (pullbackRealization e j) R) :
    asMatrix (pullbackRealization e j) R x = asMatrix j R (schemePointsEquiv e j R x) := by
  unfold asMatrix pullbackRealization schemePointsEquiv
  change (j.matrix.hom.app (CommAlgCat.of K R))
      (((groupPointsFunctor K).map (e.hom ≫ j.embedding)).app (CommAlgCat.of K R) x) = _
  rw [Functor.map_comp]
  rfl

/-- With the realization pulled back, the comparison of points also preserves
the topology from the closed matrix realization. -/
private def schemePointsHomeomorph {K : Type u} [Field K] {G H : AffineAlgebraicGroup K}
    (e : G.val ≅ H.val) (j : MatrixRealization H) (R : Type u)
    [CommRing R] [Algebra K R] [TopologicalSpace R] :
    PointsIn (pullbackRealization e j) R ≃ₜ* PointsIn j R where
  toMulEquiv := schemePointsEquiv e j R
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    change Continuous (asMatrix j R ∘ (schemePointsEquiv e j R : _ → _))
    rw [show (asMatrix j R ∘ schemePointsEquiv e j R) =
        asMatrix (pullbackRealization e j) R by
        exact funext (fun x => (pullbackRealization_asMatrix e j R x).symm)]
    exact continuous_induced_dom
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    change Continuous (asMatrix (pullbackRealization e j) R ∘
      ((schemePointsEquiv e j R).symm : _ → _))
    rw [show (asMatrix (pullbackRealization e j) R ∘ (schemePointsEquiv e j R).symm) =
        asMatrix j R by
        funext x
        exact (pullbackRealization_asMatrix e j R _).trans
          (congrArg (asMatrix j R) (MulEquiv.apply_symm_apply _ _))]
    exact continuous_induced_dom

open scoped RestrictedProduct in
private def adelicSchemeIso {K : Type u} [Field K] {G H : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (e : G.val ≅ H.val) (j : MatrixRealization H)
    (S : Finset D.Place) : Adeles D (pullbackRealization e j) S ≃ₜ* Adeles D j S := by
  let i := pullbackRealization e j
  let E (w : Outside D S) := schemePointsHomeomorph e j (D.Completion w.1)
  have hmat (w : Outside D S) (x : LocalPoints D i w.1) :
      asMatrix i (D.Completion w.1) x = asMatrix j (D.Completion w.1) (E w x) :=
    pullbackRealization_asMatrix e j _ x
  have hf (w : Outside D S) (x : LocalPoints D i w.1) :
      E w x ∈ localSubgroup D j w.1 ↔ x ∈ localSubgroup D i w.1 := by
    rcases w with ⟨w, hw⟩
    cases w with
    | inl z =>
      let U : Subgroup (Matrix.GeneralLinearGroup (Index.{u} j.size) (D.FiniteCompletion z)) :=
        (Matrix.GeneralLinearGroup.map (D.integers z).subtype).range
      change asMatrix j (D.Completion (.inl z)) (E ⟨.inl z, hw⟩ x) ∈ U ↔
        asMatrix i (D.Completion (.inl z)) x ∈ U
      rw [← hmat ⟨.inl z, hw⟩ x]
      rfl
    | inr z => exact iff_of_true (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hforward : ∀ᶠ w : Outside D S in cofinite, Set.MapsTo (E w)
      (localSubgroup D i w.1) (localSubgroup D j w.1) :=
    Filter.Eventually.of_forall fun w x hx => (hf w x).2 hx
  have hbackward : ∀ᶠ w : Outside D S in cofinite, Set.MapsTo (E w).symm
      (localSubgroup D j w.1) (localSubgroup D i w.1) :=
    Filter.Eventually.of_forall fun w x hx => (hf w ((E w).symm x)).1 (by
      rw [ContinuousMulEquiv.apply_symm_apply]
      exact hx)
  let f := RestrictedProduct.map (𝓕 := cofinite) (fun w => E w) hforward
  let g := RestrictedProduct.map (𝓕 := cofinite) (fun w => (E w).symm) hbackward
  refine
    { toFun := f
      invFun := g
      left_inv := fun x => RestrictedProduct.ext _ _ fun w => (E w).symm_apply_apply (x w)
      right_inv := fun x => RestrictedProduct.ext _ _ fun w => (E w).apply_symm_apply (x w)
      map_mul' := fun x y => RestrictedProduct.ext _ _ fun w => map_mul (E w) (x w) (y w)
      continuous_toFun := RestrictedProduct.mapAlong_continuous _ _ id tendsto_id _
        hforward fun w => (E w).continuous
      continuous_invFun := RestrictedProduct.mapAlong_continuous _ _ id tendsto_id _
        hbackward fun w => (E w).symm.continuous }

private theorem compactQuotientOfSurjective {P Q : Type*} [Group P] [Group Q]
    [TopologicalSpace P] [TopologicalSpace Q]
    (A : Subgroup P) (B : Subgroup Q) (f : P →* Q)
    (hf : Continuous f) (hs : Function.Surjective f) (hAB : A ≤ B.comap f)
    (hc : CompactSpace (P ⧸ A)) : CompactSpace (Q ⧸ B) := by
  let q : P ⧸ A → Q ⧸ B := Quotient.map' f (by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    rw [← map_inv, ← map_mul]
    exact hAB hxy)
  have hq : Continuous q := continuous_quot_map _ hf
  have hsurj : Function.Surjective q := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨z, rfl⟩ := hs y
    exact ⟨QuotientGroup.mk z, rfl⟩
  let := hc
  exact ⟨by simpa only [Set.image_univ, hsurj.range_eq] using isCompact_univ.image hq⟩

/-- Compactness of the full quotient is independent of a closed matrix
realization, with the same rational diagonal. -/
private theorem compactQuotientChangeRealization {K : Type u} [Field K]
    {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K) (i j : MatrixRealization G)
    (h : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i)) :
    CompactSpace (Adeles D j ∅ ⧸ diagonalSubgroup D j) := by
  let e := AdelicGroups.changeRealization D i j ∅
  apply compactQuotientOfSurjective (diagonalSubgroup D i) (diagonalSubgroup D j)
    e.toMonoidHom e.continuous e.surjective _ h
  rintro x ⟨g, hg⟩
  exact ⟨g, fun w => hg w⟩

private theorem schemePointsEquiv_localPoint {K : Type u} [Field K]
    {G H : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K)
    (e : G.val ≅ H.val) (j : MatrixRealization H) (w : D.Place)
    (x : Specs.IntegralModels.RationalPoints G) :
    schemePointsEquiv e j _ (localPoint D (pullbackRealization e j) w x) =
      localPoint D j w (schemePointsEquiv e j K x) := by
  let a := CommAlgCat.ofHom (Algebra.ofId K (D.Completion w))
  have h := (((groupPointsFunctor K).map e.hom).naturality a)
  exact DFunLike.congr_fun (congrArg GrpCat.Hom.hom h) x

/-- Pullback of a closed realization along an isomorphism of the original schemes
also pulls back compactness of the quotient by rational points. -/
private theorem compactQuotientPullbackRealization {K : Type u} [Field K]
    {G H : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K)
    (e : G.val ≅ H.val) (j : MatrixRealization H)
    (h : CompactSpace (Adeles D j ∅ ⧸ diagonalSubgroup D j)) :
    CompactSpace (Adeles D (pullbackRealization e j) ∅ ⧸
      diagonalSubgroup D (pullbackRealization e j)) := by
  let i := pullbackRealization e j
  let E := adelicSchemeIso D e j ∅
  apply compactQuotientOfSurjective (diagonalSubgroup D j) (diagonalSubgroup D i)
    E.symm.toMonoidHom E.symm.continuous E.symm.surjective _ h
  rintro x ⟨g, hg⟩
  let a : Specs.IntegralModels.RationalPoints G := (schemePointsEquiv e j K).symm g
  refine ⟨a, fun w => ?_⟩
  change (schemePointsEquiv e j (D.Completion w.1)).symm (x w) =
    localPoint D i w.1 a
  apply (schemePointsEquiv e j (D.Completion w.1)).injective
  rw [MulEquiv.apply_symm_apply]
  have hpoint := schemePointsEquiv_localPoint D e j w.1 a
  have ha : schemePointsEquiv e j K a = g := MulEquiv.apply_symm_apply _ _
  exact (hg w).trans ((congrArg (localPoint D j w.1) ha).symm.trans hpoint.symm)

section NormOnePresentation

open Specs.OuterTypeAModels (RepresentsNormOne)
open _root_.Specs.RM03.CSA (isCentralSimple)
open RM03.CSA.NormOneGroup (normOne normOneFunctor normHom)

variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  {hA : isCentralSimple K A} {b : Module.Basis I K A} {G : AffineAlgebraicGroup K}

private noncomputable def normOnePointIsoOf
    (p : ∀ R : TestAlgebra K, Points G.val.X R ≃ normOne (R := R) hA b)
    (hmul : ∀ R (x y : ((groupPointsFunctor K).obj G.val).obj R),
      (p R (x * y)).val = (p R x).val * (p R y).val)
    (hnat : ∀ {R S : TestAlgebra K} (f : R ⟶ S) (x : Points G.val.X R),
      (p S (mapPoints f x)).val =
        Algebra.TensorProduct.map f.hom (.id K A) (p R x).val) :
    (groupPointsFunctor K).obj G.val ≅ normOneFunctor hA b := by
  refine NatIso.ofComponents (fun R => ?_) ?_
  · letI := RM03.CSA.NormOneGroup.normOneGroup (R := R) hA b
    exact (show ((groupPointsFunctor K).obj G.val).obj R ≃* normOne (R := R) hA b from
      { toEquiv := p R
        map_mul' := fun x y => Subtype.ext (hmul R x y) }).toGrpIso
  · intro R S f
    ext x : 2
    exact Subtype.ext (hnat f x)

/-- Turn the pointwise norm-one comparison into an isomorphism of group functors. -/
private noncomputable def normOnePointIso (h : RepresentsNormOne hA b G) :
    (groupPointsFunctor K).obj G.val ≅ normOneFunctor hA b :=
  normOnePointIsoOf (Classical.choose h) (Classical.choose_spec h).1 (Classical.choose_spec h).2

open IsotropicInnerTypeA.Spec (NormOnePresentation)
open private existsPresentation pointCoord pointCoord_isInducing from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicInnerTypeA

/-- The norm-one coordinates give the same topology as the original closed
matrix realization, by transport from the coordinate equation model. -/
private theorem normOneCoordinatesInducing (h : RepresentsNormOne hA b G)
    (i : MatrixRealization G) {F : Type u} [Field F] [Algebra K F] [TopologicalSpace F]
    [IsTopologicalDivisionRing F] :
    IsInducing (fun x : PointsIn i F =>
      fun l => (b.baseChange F).repr ((normOnePointIso h).hom.app (CommAlgCat.of K F) x).val l) := by
  obtain ⟨P⟩ := existsPresentation hA b
  let pG := normOnePointIso h
  let pP := normOnePointIsoOf P.point P.point_mul P.point_natural
  obtain ⟨e, he⟩ := schemeIsoOfPointIso (pP ≪≫ pG.symm)
  let j := pullbackRealization e i
  let R := CommAlgCat.of K F
  let E := schemePointsHomeomorph e i F
  have he' : (groupPointsFunctor K).mapIso e ≪≫ pG = pP := by
    rw [he]
    simp
  have hc (x : PointsIn j F) :
      pG.hom.app R (E x) = P.point R x :=
    congrArg (fun α : (groupPointsFunctor K).obj P.group.val ≅ normOneFunctor hA b =>
      α.hom.app R x) he'
  let c := fun x : PointsIn i F => fun l => (b.baseChange F).repr (pG.hom.app R x).val l
  have hcoord : c = (pointCoord P j) ∘ E.symm := by
    funext x l
    change (b.baseChange F).repr (pG.hom.app R x).val l =
      (b.baseChange F).repr (P.point R (E.symm x)).val l
    rw [← hc, E.apply_symm_apply]
  change IsInducing c
  rw [hcoord]
  exact (pointCoord_isInducing (F := F) P j).comp E.symm.toHomeomorph.isInducing

open LocalNormOneCommutators.Spec
open RM03.CSA (isCentralSimple_baseChange reducedNorm_baseChange)
open RM03.CSA.NormOneGroup (normAt mapNormOne changeCoefficients isUnit_of_normAt_eq_one)
open private normAt_eq_reducedNorm from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicInnerTypeA
open private continuous_linear_coordinate exists_word_of_mem_commutator from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators

/-- Local commutator density gives simultaneous approximation in any
specified finite product of completions of the original norm-one group. -/
private theorem weakApproximationFromCommutators
    (h : RepresentsNormOne hA b G) (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (T : Finset D.Place)
    (hcomm : ∀ p : T, denseCommutators (isCentralSimple_baseChange (L := D.Completion p.1) hA)) :
    DenseRange (ArithmeticLatticeProjection.rationalProjection D i T) := by
  classical
  intro x
  apply mem_closure_iff_nhds.mpr
  intro V hV
  rw [nhds_pi] at hV
  obtain ⟨⟨P, W⟩, ⟨_, hW⟩, hsub⟩ :=
    (Filter.hasBasis_pi fun p : T => nhds_basis_opens (x p)).mem_iff.mp hV
  let U (p : T) := if p ∈ P then W p else Set.univ
  have hU (p : T) : x p ∈ U p ∧ IsOpen (U p) := by
    by_cases hp : p ∈ P
    · simpa only [U, ite_eq_left hp] using hW p hp
    · simp [U, hp]
  let F (p : T) := D.Completion p.1
  let B (p : T) := F p ⊗[K] A
  let c (p : T) : Module.Basis (Fin (Module.finrank (F p) (B p))) (F p) (B p) :=
    letI := (isCentralSimple_baseChange (L := F p) hA).2.2
    Module.finBasis (F p) (B p)
  let (p : T) : TopologicalSpace (B p) := coordinateTopology (c p)
  let ρ := (normOnePointIso h).hom
  let C (p : T) (z : LocalPoints D i p.1) (l : I) :=
    (b.baseChange (F p)).repr (ρ.app (CommAlgCat.of K (F p)) z).val l
  have hC (p : T) : IsInducing (C p) := normOneCoordinatesInducing h i
  choose O hO hEq using fun p => (hC p).isOpen_iff.mp (hU p).2
  let ψ (p : T) (z : (B p)ˣ) (l : I) := (b.baseChange (F p)).repr (z : B p) l
  have hψ (p : T) : Continuous (ψ p) := by
    refine continuous_pi fun l => ?_
    exact (continuous_linear_coordinate (c p) ((b.baseChange (F p)).coord l)).comp
      Units.continuous_val
  let J (p : T) := (ψ p) ⁻¹' O p
  have hJ (p : T) : IsOpen (J p) := (hO p).preimage (hψ p)
  have hword (p : T) : ∃ L : List ((B p)ˣ × (B p)ˣ), commutatorWord L ∈ J p := by
    let a := ρ.app (CommAlgCat.of K (F p)) (x p)
    let ha := isUnit_of_normAt_eq_one hA b a.val a.property
    let z := ha.unit
    have hz : z ∈ normOne (isCentralSimple_baseChange (L := F p) hA) := by
      change RM03.CSA.reducedNorm _ z.val = 1
      rw [show z.val = a.val from ha.unit_spec, ← normAt_eq_reducedNorm hA b]
      exact a.property
    have hzJ : z ∈ J p := by
      change (fun l => (b.baseChange (F p)).repr z.val l) ∈ O p
      rw [show z.val = a.val from ha.unit_spec]
      change x p ∈ (C p) ⁻¹' O p
      rw [hEq p]
      exact (hU p).1
    obtain ⟨z', hz'J, hz'⟩ := mem_closure_iff.mp (hcomm p (c p) hz) _ (hJ p) hzJ
    obtain ⟨L, rfl⟩ := exists_word_of_mem_commutator hz'
    exact ⟨L, hz'J⟩
  choose L hL using hword
  obtain ⟨Z, hZ, hloc⟩ := LocalNormOneCommutators.simultaneousApproximation D hA T c L J hJ hL
  let u := commutatorWord Z
  let R := CommAlgCat.of K K
  let a : RM03.CSA.NormOneGroup.normOne (R := K) hA b := ⟨1 ⊗ₜ[K] (u : A), by
    change RM03.CSA.reducedNorm hA (u : A) = 1 at hZ
    exact (normAt_eq_reducedNorm hA b _).trans
      ((reducedNorm_baseChange hA (u : A)).trans (by rw [hZ, map_one]))⟩
  let g : Specs.IntegralModels.RationalPoints G := (normOnePointIso h).inv.app R a
  have hg : ρ.app R g = a := (normOnePointIso h).app R |>.groupIsoToMulEquiv.apply_symm_apply a
  have hlocal (p : T) : (ρ.app (CommAlgCat.of K (F p)) (localPoint D i p.1 g)).val =
      (localizeUnit D p.1 u).val := by
    let f : R ⟶ CommAlgCat.of K (F p) := CommAlgCat.ofHom (Algebra.ofId K (F p))
    have hh := congrArg (fun z => z g) (ρ.naturality f)
    change ρ.app (CommAlgCat.of K (F p)) (localPoint D i p.1 g) =
      mapNormOne hA b f.hom (ρ.app R g) at hh
    rw [hh, hg]
    change changeCoefficients f.hom (1 ⊗ₜ[K] (u : A)) = (localizeUnit D p.1 u).val
    simp [changeCoefficients, localizeUnit]
  refine ⟨ArithmeticLatticeProjection.rationalProjection D i T g, hsub ?_, ⟨g, rfl⟩⟩
  intro p hp
  have hh : localPoint D i p.1 g ∈ U p := by
    rw [← hEq p]
    change C p (localPoint D i p.1 g) ∈ O p
    have heq : C p (localPoint D i p.1 g) = ψ p (localizeUnit D p.1 u) :=
      funext fun l => congrArg (fun z => (b.baseChange (F p)).repr z l) (hlocal p)
    rw [heq]
    exact hloc p
  change localPoint D i p.1 g ∈ W p
  simpa only [U, ite_eq_left hp] using hh

open private transportedAlgebraEquiv transportedAlgebraEquiv_one_tmul
  centralSimple_transport reducedNorm_transport from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicInnerTypeA

private theorem denseCommutatorsOfFieldEquiv {F L A : Type*}
    [Field F] [TopologicalSpace F] [Field L] [TopologicalSpace L] [Ring A] [Algebra F A]
    (e : F ≃+* L) (he : Continuous e.symm) (hA : isCentralSimple F A)
    (h : letI : Algebra L A := Algebra.compHom A e.symm.toRingHom
      denseCommutators (centralSimple_transport e hA)) :
    denseCommutators hA := by
  let : Algebra F L := e.toRingHom.toAlgebra
  let : Algebra L A := Algebra.compHom A e.symm.toRingHom
  intro b
  let f := transportedAlgebraEquiv (A := A) e
  have hr : Module.finrank F A = Module.finrank L A := by
    rw [← f.toLinearEquiv.finrank_eq, RM03.CSA.finrank_baseChange hA]
  let c := ((b.baseChange L).map f.toLinearEquiv).reindex (finCongr hr)
  have hc (x : A) (l : Fin (Module.finrank F A)) : e.symm (c.repr x (finCongr hr l)) = b.repr x l := by
    have hx : f.symm x = 1 ⊗ₜ[F] x := f.injective
      ((f.apply_symm_apply x).trans (transportedAlgebraEquiv_one_tmul e x).symm)
    dsimp [c]
    rw [Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply, Module.Basis.map_repr]
    change e.symm ((b.baseChange L).repr (f.symm x) l) = _
    rw [hx, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
    exact e.symm_apply_apply _
  let s : TopologicalSpace A := coordinateTopology b
  let t : TopologicalSpace A := coordinateTopology c
  have hv : @Continuous A A t s id := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro l
    simp_rw [Function.comp_apply, id_eq, ← hc _ l]
    exact he.comp ((continuous_apply _).comp continuous_induced_dom)
  let tU : TopologicalSpace Aˣ := @Units.instTopologicalSpaceUnits A t _
  let sU : TopologicalSpace Aˣ := @Units.instTopologicalSpaceUnits A s _
  have hcont : @Continuous Aˣ Aˣ tU sU id := by
    simpa only [Units.map_id, MonoidHom.coe_id] using
      (@Continuous.units_map A A _ _ t s (MonoidHom.id A) hv)
  intro x hx
  have hn : x ∈ LocalNormOneCommutators.Spec.normOne (centralSimple_transport e hA) := by
    change RM03.CSA.reducedNorm (centralSimple_transport e hA) (x : A) = 1
    change RM03.CSA.reducedNorm hA (x : A) = 1 at hx
    rw [reducedNorm_transport e hA, hx, map_one]
  have hmem := h c hn
  simpa only [Set.mem_preimage, id_eq, Set.image_id'] using
    (@closure_subset_preimage_closure_image Aˣ Aˣ tU sU id (commutator Aˣ : Set Aˣ) hcont x hmem)

private theorem localCommutatorsAtPlace (D : GlobalFieldData.{u,v} K) (w : D.Place) :
    denseCommutators (isCentralSimple_baseChange (L := D.Completion w) hA) := by
  cases w with
  | inl w =>
    let F := D.Completion (.inl w)
    let : ValuativeRel F := inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
    let : IsNonarchimedeanLocalField F := GlobalFieldData.finiteCompletion_isLocalField D w
    exact LocalNormOneCommutators.localAlgebras.{u,u}.1 (isCentralSimple_baseChange (L := F) hA)
  | inr w =>
    cases D with
    | function _ _ => exact w.elim
    | number hK =>
      let D' : GlobalFieldData.{u,v} K := .number hK
      let F := D'.Completion (.inr w)
      let : Field F := GlobalFieldData.instFieldCompletion D' (.inr w)
      let : TopologicalSpace F := GlobalFieldData.instTopologicalSpaceCompletion D' (.inr w)
      let : Algebra K F := AdelicGroups.completionAlgebra D' (.inr w)
      let hF := isCentralSimple_baseChange (L := F) hA
      change denseCommutators hF
      rcases w.isReal_or_isComplex with hr | hc
      · obtain ⟨e, he⟩ := numberRealCompletion w hr
        let e' : F ≃+* ℝ := e
        let E : w.Completion ≃ᵢ ℝ := ⟨e.toEquiv, he⟩
        have hE : Continuous e'.symm := E.symm.continuous
        let : Algebra ℝ (F ⊗[K] A) := Algebra.compHom _ e'.symm.toRingHom
        exact denseCommutatorsOfFieldEquiv e' hE hF
          (LocalNormOneCommutators.localAlgebras.{u,u}.2.1 (centralSimple_transport e' hF))
      · obtain ⟨e, he⟩ := numberComplexCompletion w hc
        let e' : F ≃+* ℂ := e
        let E : w.Completion ≃ᵢ ℂ := ⟨e.toEquiv, he⟩
        have hE : Continuous e'.symm := E.symm.continuous
        let : Algebra ℂ (F ⊗[K] A) := Algebra.compHom _ e'.symm.toRingHom
        exact denseCommutatorsOfFieldEquiv e' hE hF
          (LocalNormOneCommutators.localAlgebras.{u,u}.2.2 (centralSimple_transport e' hF))

/-- The actual norm-one scheme has weak approximation in the given closed
matrix realization, over both kinds of global field. -/
theorem normOneWeakApproximation (h : RepresentsNormOne hA b G)
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) : AdelicGroups.WeakApproximation D i :=
  fun T => weakApproximationFromCommutators h D i T fun p => localCommutatorsAtPlace (hA := hA) D p.1

private theorem finiteInfinitePlaces {K : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) : Finite D.InfinitePlace := by
  cases D with
  | number h => let := h; infer_instance
  | function _ _ => infer_instance

/-- Once the outside archimedean factors are compact, the finite local
comparison and weak approximation give density away from the omitted set. -/
theorem normOneStrongApproximationWithCompactInfinity
    (hfull : FiniteCovolumeSubgroup.{u}) (h : RepresentsNormOne hA b G)
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (S : Finset D.Place)
    (hG : IsAbsolutelyAlmostSimple G)
    (hcompact : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hnoncompact : ¬ CompactSpace (FinitePoints D i S))
    (harch : ∀ p : D.InfinitePlace, Sum.inr p ∉ S → CompactSpace (LocalPoints D i (.inr p)))
    (E : Finset D.FinitePlace)
    (hmix : ∀ p ∉ E, MixingCases (baseChangedAlgebraicGroup (D.Completion (.inl p)) G))
    (hcontract : ∀ p ∉ E, Dense
      (Subgroup.closure {x : FinitePoints D i {Sum.inl p} | Contracted x} :
        Set (FinitePoints D i {Sum.inl p}))) :
    StrongApproximation D i S := by
  let : Finite D.InfinitePlace := finiteInfinitePlaces D
  let : Fintype D.InfinitePlace := Fintype.ofFinite _
  let fl : D.FinitePlace ↪ D.Place := ⟨Sum.inl, Sum.inl_injective⟩
  let fr : D.InfinitePlace ↪ D.Place := ⟨Sum.inr, Sum.inr_injective⟩
  let J := (E.map fl ∪ (Finset.univ : Finset D.InfinitePlace).map fr) \ S
  have hJ : Disjoint J S := Finset.disjoint_sdiff.symm
  have hinf (p : D.InfinitePlace) (hp : Sum.inr p ∉ S) : Sum.inr p ∈ J :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ (Finset.mem_map.mpr
      ⟨p, Finset.mem_univ _, rfl⟩), hp⟩
  have hgood (p : D.FinitePlace) (hp : Sum.inl p ∉ S) (hw : Sum.inl p ∉ J) : p ∉ E := by
    intro hE
    exact hw (Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _
      (Finset.mem_map.mpr ⟨p, hE, rfl⟩), hp⟩)
  refine strongApproximationOfLocalProjections D i S J hJ harch hcompact hnoncompact
    ?_ ?_ (normOneWeakApproximation h D i J)
  · rintro ⟨p, hS⟩ hp
    cases p with
    | inl p =>
      exact fullProjectionOfFiniteCompletion hfull D i p
        (OppositeRadicals.absolutelyAlmostSimpleFieldExtension G hG) (hmix p (hgood p hS hp))
    | inr p => exact False.elim (hp (hinf p hS))
  · rintro ⟨p, hS⟩ hp
    cases p with
    | inl p => exact hcontract p (hgood p hS hp)
    | inr p => exact False.elim (hp (hinf p hS))

end NormOnePresentation

section CliffordQuaternion

open CliffordAlgebra

variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]

/-- The products of three pairwise orthogonal Clifford vectors satisfy the
quaternion relations. This construction is valid over any coefficient ring. -/
private def evenQuaternionBasis (q : QuadraticForm K V) (e₀ e₁ e₂ : V)
    (h₀₁ : QuadraticMap.polar q e₀ e₁ = 0)
    (h₀₂ : QuadraticMap.polar q e₀ e₂ = 0)
    (h₁₂ : QuadraticMap.polar q e₁ e₂ = 0) :
    QuaternionAlgebra.Basis (even q) (-(q e₀ * q e₁)) 0 (-(q e₀ * q e₂)) := by
  let x := CliffordAlgebra.ι q e₀
  let y := CliffordAlgebra.ι q e₁
  let z := CliffordAlgebra.ι q e₂
  let i : even q := ⟨x * y, ι_mul_ι_mem_evenOdd_zero q e₀ e₁⟩
  let j : even q := ⟨x * z, ι_mul_ι_mem_evenOdd_zero q e₀ e₂⟩
  have hyx : y * x = -(x * y) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact (ι_mul_ι_add_swap _ _).trans (by rw [h₀₁, map_zero])
  have hzx : z * x = -(x * z) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact (ι_mul_ι_add_swap _ _).trans (by rw [h₀₂, map_zero])
  have hzy : z * y = -(y * z) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact (ι_mul_ι_add_swap _ _).trans (by rw [h₁₂, map_zero])
  have hx : x * x = algebraMap K (CliffordAlgebra q) (q e₀) := ι_sq_scalar _ _
  have hy : y * y = algebraMap K (CliffordAlgebra q) (q e₁) := ι_sq_scalar _ _
  have hz : z * z = algebraMap K (CliffordAlgebra q) (q e₂) := ι_sq_scalar _ _
  refine ⟨i, j, i * j, ?_, ?_, rfl, ?_⟩
  · simp only [zero_smul, add_zero]
    apply Subtype.ext
    change (x * y) * (x * y) = -(q e₀ * q e₁) • (1 : CliffordAlgebra q)
    calc
      (x * y) * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
      _ = -((x * x) * (y * y)) := by rw [hyx]; noncomm_ring
      _ = _ := by rw [hx, hy, ← map_mul, ← map_neg, Algebra.algebraMap_eq_smul_one]
  · apply Subtype.ext
    change (x * z) * (x * z) = -(q e₀ * q e₂) • (1 : CliffordAlgebra q)
    calc
      (x * z) * (x * z) = x * (z * x) * z := by simp only [mul_assoc]
      _ = -((x * x) * (z * z)) := by rw [hzx]; noncomm_ring
      _ = _ := by rw [hx, hz, ← map_mul, ← map_neg, Algebra.algebraMap_eq_smul_one]
  · simp only [zero_smul, zero_sub]
    apply Subtype.ext
    change (x * z) * (x * y) = -((x * y) * (x * z))
    calc
      (x * z) * (x * y) = x * (z * x) * y := by simp only [mul_assoc]
      _ = -((x * x) * (z * y)) := by rw [hzx]; noncomm_ring
      _ = x * (y * x) * (-z) := by rw [hzy, hyx]; noncomm_ring
      _ = -((x * y) * (x * z)) := by simp only [mul_neg, mul_assoc]

private theorem evenCliffordFinrank {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (q : QuadraticForm K V) (b : Module.Basis (Fin 3) K V) :
    Module.finrank K (even q) = 4 := by
  let E := {s : Finset (Fin 3) // (s.card : ZMod 2) = 0}
  obtain ⟨B, hB⟩ := LinearAlgebraicGroups.Albert.CliffordModel.ordered_basis q b
  let w : E → CliffordAlgebra q := B ∘ Subtype.val
  have hw : LinearIndependent K w := B.linearIndependent.comp _ Subtype.val_injective
  have hE : Set.range w =
      LinearAlgebraicGroups.Albert.CliffordSpecification.orderedWord q b ''
        {s | (s.card : ZMod 2) = 0} := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s.val, s.property, (hB s.val).symm⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, hB s⟩
  have hn : Fintype.card E = 4 := by decide
  change Module.finrank K (evenOdd q 0) = 4
  rw [LinearAlgebraicGroups.Albert.CliffordModel.parity_span q b 0, ← hE,
    finrank_span_eq_card hw, hn]

private theorem ternaryBasis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (q : QuadraticForm K V)
    (h₂ : (2 : K) ≠ 0) (hdim : Module.finrank K V = 3) :
    ∃ b : Module.Basis (Fin 3) K V,
      ∀ i j, i ≠ j → QuadraticMap.polar q (b i) (b j) = 0 := by
  let : Invertible (2 : K) := (isUnit_iff_ne_zero.mpr h₂).invertible
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (QuadraticForm.associated_isSymm K q)
  let e := finCongr hdim
  refine ⟨b.reindex e, fun i j hij => ?_⟩
  change q.polarBilin (b.reindex e i) (b.reindex e j) = 0
  rw [← QuadraticMap.two_nsmul_associated K q]
  simp only [LinearMap.smul_apply, Module.Basis.reindex_apply]
  have h : QuadraticMap.associatedHom K q (b (e.symm i)) (b (e.symm j)) = 0 :=
    hb (e.symm.injective.ne hij)
  rw [h]
  simp

/-- An orthogonal ternary basis presents its even Clifford algebra as a
quaternion algebra. Simplicity of the source gives injectivity, and both
algebras have dimension four. -/
private theorem evenCliffordQuaternionEquiv {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (q : QuadraticForm K V) (b : Module.Basis (Fin 3) K V)
    (hb : ∀ i j, i ≠ j → QuadraticMap.polar q (b i) (b j) = 0)
    [IsSimpleRing (QuaternionAlgebra K (-(q (b 0) * q (b 1))) 0 (-(q (b 0) * q (b 2))))] :
    ∃ e : QuaternionAlgebra K (-(q (b 0) * q (b 1))) 0 (-(q (b 0) * q (b 2))) ≃ₐ[K] even q,
      ∀ x, e x = QuaternionAlgebra.lift
        (evenQuaternionBasis q (b 0) (b 1) (b 2) (hb _ _ (by decide))
          (hb _ _ (by decide)) (hb _ _ (by decide))) x := by
  let h := evenQuaternionBasis q (b 0) (b 1) (b 2)
    (hb _ _ (by decide)) (hb _ _ (by decide)) (hb _ _ (by decide))
  let f := QuaternionAlgebra.lift h
  let : Nontrivial (even q) := Module.nontrivial_of_finrank_pos
    (R := K) (by rw [evenCliffordFinrank q b]; decide)
  have hi : Function.Injective f := f.toRingHom.injective
  obtain ⟨B, _⟩ := LinearAlgebraicGroups.Albert.CliffordModel.ordered_basis q b
  let : FiniteDimensional K (CliffordAlgebra q) := Module.Finite.of_basis B
  let : FiniteDimensional K (even q) :=
    inferInstanceAs (FiniteDimensional K (even q).toSubmodule)
  have hd : Module.finrank K (QuaternionAlgebra K (-(q (b 0) * q (b 1))) 0
      (-(q (b 0) * q (b 2)))) = Module.finrank K (even q) :=
    (QuaternionAlgebra.finrank_eq_four _ _ _).trans (evenCliffordFinrank q b).symm
  exact ⟨AlgEquiv.ofBijective f ⟨hi,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd
      (f := f.toLinearMap)).mp hi⟩, fun _ => rfl⟩

open LinearAlgebraicGroups.Specs.Arithmetic.LocalQuadraticIsotropy (pureNorm)
open private quaternion_isUnit_or_zero quaternion_central from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuadraticIsotropy

/-- The pure norm of the quaternion model is a nonzero multiple of the
original ternary form after an invertible diagonal change of coordinates. -/
private theorem ternaryPureNormAnisotropic {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (q : QuadraticForm K V) (b : Module.Basis (Fin 3) K V)
    (h₂ : (2 : K) ≠ 0) (ha : ∀ x, q x = 0 → x = 0)
    (hb : ∀ i j, i ≠ j → QuadraticMap.polar q (b i) (b j) = 0) :
    ∀ x y z, pureNorm (-(q (b 0) * q (b 1))) (-(q (b 0) * q (b 2))) x y z = 0 →
      x = 0 ∧ y = 0 ∧ z = 0 := by
  let : Invertible (2 : K) := (isUnit_iff_ne_zero.mpr h₂).invertible
  have horth : (QuadraticMap.associatedHom K q).IsOrthoᵢ b := by
    intro i j hij
    change QuadraticMap.associatedHom K q (b i) (b j) = 0
    have h := congrArg (fun f : LinearMap.BilinForm K V => f (b i) (b j))
      (QuadraticMap.two_nsmul_associated K q)
    change (2 : ℕ) • QuadraticMap.associatedHom K q (b i) (b j) =
      QuadraticMap.polar q (b i) (b j) at h
    rw [hb i j hij, nsmul_eq_mul, Nat.cast_ofNat] at h
    exact (mul_eq_zero.mp h).resolve_left h₂
  let e : q.IsometryEquiv (QuadraticMap.weightedSumSquares K (fun i => q (b i))) := by
    rw [← q.basisRepr_eq_of_iIsOrtho b horth]
    exact q.isometryEquivBasisRepr b
  let a₀ := q (b 0)
  let a₁ := q (b 1)
  let a₂ := q (b 2)
  have h₀ : a₀ ≠ 0 := fun h => b.ne_zero 0 (ha _ h)
  have h₁ : a₁ ≠ 0 := fun h => b.ne_zero 1 (ha _ h)
  have h₂' : a₂ ≠ 0 := fun h => b.ne_zero 2 (ha _ h)
  have hdiag (t : Fin 3 → K) : q (e.symm t) = a₀ * t 0 ^ 2 + a₁ * t 1 ^ 2 + a₂ * t 2 ^ 2 := by
    rw [e.symm.map_app, QuadraticMap.weightedSumSquares_apply]
    simp [Fin.sum_univ_succ, a₀, a₁, a₂]
    ring
  intro x y z h
  let t : Fin 3 → K := ![a₁ * a₂ * z, a₂ * y, a₁ * x]
  have hscale : a₀ * q (e.symm t) =
      a₁ * a₂ * pureNorm (-(a₀ * a₁)) (-(a₀ * a₂)) x y z := by
    rw [hdiag]
    simp [pureNorm, t]
    ring
  change pureNorm (-(a₀ * a₁)) (-(a₀ * a₂)) x y z = 0 at h
  rw [h, mul_zero] at hscale
  have ht : t = 0 := e.symm.toLinearEquiv.injective (by
    rw [map_zero]
    exact ha _ ((mul_eq_zero.mp hscale).resolve_left h₀))
  have htx : a₁ * x = 0 := by simpa [t] using congrFun ht 2
  have hty : a₂ * y = 0 := by simpa [t] using congrFun ht 1
  have htz : a₁ * a₂ * z = 0 := by simpa [t] using congrFun ht 0
  exact ⟨(mul_eq_zero.mp htx).resolve_left h₁, (mul_eq_zero.mp hty).resolve_left h₂',
    (mul_eq_zero.mp htz).resolve_left (mul_ne_zero h₁ h₂')⟩

/-- The even Clifford algebra of an anisotropic ternary form has a central
division quaternion model. -/
theorem anisotropicTernaryEvenClifford {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (q : QuadraticForm K V)
    (h₂ : (2 : K) ≠ 0) (hdim : Module.finrank K V = 3) (ha : ∀ x, q x = 0 → x = 0) :
    ∃ α β : K, let D := QuaternionAlgebra K α 0 β
      (∀ d : D, IsUnit d ∨ d = 0) ∧
      α ≠ 0 ∧ β ≠ 0 ∧
      Algebra.IsCentral K D ∧ Nonempty (D ≃ₐ[K] even q) := by
  obtain ⟨b, hb⟩ := ternaryBasis q h₂ hdim
  have hp := ternaryPureNormAnisotropic q b h₂ ha hb
  let α := -(q (b 0) * q (b 1))
  let β := -(q (b 0) * q (b 2))
  let D := QuaternionAlgebra K α 0 β
  have hα : α ≠ 0 := neg_ne_zero.mpr (mul_ne_zero
    (fun h => b.ne_zero 0 (ha _ h)) (fun h => b.ne_zero 1 (ha _ h)))
  have hD : ∀ d : D, IsUnit d ∨ d = 0 := quaternion_isUnit_or_zero hp
  let : DivisionRing D := DivisionRing.ofIsUnitOrEqZero hD
  have hβ : β ≠ 0 := neg_ne_zero.mpr (mul_ne_zero
    (fun h => b.ne_zero 0 (ha _ h)) (fun h => b.ne_zero 2 (ha _ h)))
  obtain ⟨e, _⟩ := evenCliffordQuaternionEquiv q b hb
  exact ⟨α, β, hD, hα, hβ, quaternion_central h₂ hα, ⟨e⟩⟩

/-- Reversion on the quaternion generators is quaternion conjugation.
The identity holds over any commutative coefficient ring. -/
private theorem reverseEvenQuaternion {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (q : QuadraticForm K V) (e₀ e₁ e₂ : V)
    (h₀₁ : QuadraticMap.polar q e₀ e₁ = 0)
    (h₀₂ : QuadraticMap.polar q e₀ e₂ = 0)
    (h₁₂ : QuadraticMap.polar q e₁ e₂ = 0)
    (a : QuaternionAlgebra K (-(q e₀ * q e₁)) 0 (-(q e₀ * q e₂))) :
    let B := evenQuaternionBasis q e₀ e₁ e₂ h₀₁ h₀₂ h₁₂
    reverse ((QuaternionAlgebra.lift B a : even q) : CliffordAlgebra q) =
      ((QuaternionAlgebra.lift B (star a) : even q) : CliffordAlgebra q) := by
  let B := evenQuaternionBasis q e₀ e₁ e₂ h₀₁ h₀₂ h₁₂
  have hpair (x y : V) (h : QuadraticMap.polar q x y = 0) :
      reverse (CliffordAlgebra.ι q x * CliffordAlgebra.ι q y) =
        -(CliffordAlgebra.ι q x * CliffordAlgebra.ι q y) := by
    rw [reverse.map_mul, reverse_ι, reverse_ι, eq_neg_iff_add_eq_zero, add_comm,
      ι_mul_ι_add_swap, h, map_zero]
  have hi : reverse (B.i : CliffordAlgebra q) = -(B.i : CliffordAlgebra q) := hpair e₀ e₁ h₀₁
  have hj : reverse (B.j : CliffordAlgebra q) = -(B.j : CliffordAlgebra q) := hpair e₀ e₂ h₀₂
  have hk : reverse (B.k : CliffordAlgebra q) = -(B.k : CliffordAlgebra q) := by
    have h := congrArg Subtype.val B.j_mul_i
    simp only [zero_smul, zero_sub, Subalgebra.coe_mul, Subalgebra.coe_neg] at h
    have hmul := congrArg Subtype.val B.i_mul_j
    simp only [Subalgebra.coe_mul] at hmul
    rw [← hmul, reverse.map_mul, hi, hj, neg_mul_neg, hmul]
    exact h
  change reverse (B.lift a : CliffordAlgebra q) = (B.lift (star a) : CliffordAlgebra q)
  simp only [QuaternionAlgebra.Basis.lift, Subalgebra.coe_add, Subalgebra.coe_algebraMap,
    Subalgebra.coe_smul, map_add, map_smul, reverse.commutes, hi, hj, hk,
    QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
    QuaternionAlgebra.imK_star, zero_mul, add_zero, smul_neg, neg_smul, Subalgebra.coe_neg]

end CliffordQuaternion

section NormEquation
open _root_.RM03.CSA (IsCentralSimple reducedNorm reducedNorm_baseChange)
open _root_.RM03.CSA.NormOneGroup (normAt normAt_natural)
open private normAt_eq_reducedNorm from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicInnerTypeA
open private coord_change from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.NormOneGroup

variable {K A C I J : Type*} [Field K] [Ring A] [Algebra K A] [Ring C] [Algebra K C]
  [Fintype I] (hA : IsCentralSimple K A) (b : Module.Basis I K A)
  (f : A →ₐ[K] C) (t : C →ₗ[K] C)

private def normEquationDifference (R : Type*) [CommRing R] [Algebra K R]
    (x : R ⊗[K] A) : R ⊗[K] C :=
  let y := Algebra.TensorProduct.map (AlgHom.id K R) f x
  (t.baseChange R) y * y - algebraMap R (R ⊗[K] C) (normAt hA b x)

private theorem normEquationDifference_natural {R S : Type*} [CommRing R] [CommRing S]
    [Algebra K R] [Algebra K S] (a : R →ₐ[K] S) (x : R ⊗[K] A) :
    Algebra.TensorProduct.map a (AlgHom.id K C) (normEquationDifference hA b f t R x) =
      normEquationDifference hA b f t S (Algebra.TensorProduct.map a (AlgHom.id K A) x) := by
  let φ := Algebra.TensorProduct.map a (AlgHom.id K A)
  let ψ := Algebra.TensorProduct.map a (AlgHom.id K C)
  let F₁ := Algebra.TensorProduct.map (AlgHom.id K R) f
  let F₂ := Algebra.TensorProduct.map (AlgHom.id K S) f
  have hc (y : R ⊗[K] C) : ψ ((t.baseChange R) y) = (t.baseChange S) (ψ y) := by
    induction y with
    | tmul r c => simp [ψ, LinearMap.baseChange_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hf : ψ (F₁ x) = F₂ (φ x) := by
    induction x with
    | tmul r x => simp [φ, ψ, F₁, F₂]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hsc (r : R) : ψ (algebraMap R (R ⊗[K] C) r) = algebraMap S (S ⊗[K] C) (a r) := by
    change ψ (r ⊗ₜ[K] 1) = a r ⊗ₜ[K] 1
    simp [ψ]
  change ψ ((t.baseChange R) (F₁ x) * F₁ x - algebraMap R _ (normAt hA b x)) = _
  rw [map_sub, map_mul, hc, hf, hsc, ← normAt_natural hA b a]
  rfl

private theorem normEquationDifference_ground
    (h : ∀ a : A, t (f a) * f a = algebraMap K C (reducedNorm hA a))
    (x : K ⊗[K] A) : normEquationDifference hA b f t K x = 0 := by
  let e := Algebra.TensorProduct.lid K A
  obtain ⟨a, rfl⟩ := e.symm.surjective x
  change normEquationDifference hA b f t K (1 ⊗ₜ[K] a) = 0
  have hn : normAt hA b ((1 : K) ⊗ₜ[K] a) = reducedNorm hA a :=
    (normAt_eq_reducedNorm hA b _).trans (reducedNorm_baseChange hA a)
  unfold normEquationDifference
  dsimp only
  rw [hn, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, LinearMap.baseChange_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, h, sub_eq_zero]
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul]
  change (reducedNorm hA a) • ((1 : K) ⊗ₜ[K] (1 : C)) =
    algebraMap K (K ⊗[K] C) (reducedNorm hA a)
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

/-- A reduced-norm polynomial identity verified over an infinite field
holds over every commutative test algebra. -/
private theorem normEquationOnTestAlgebras [Infinite K] (c : Module.Basis J K C)
    (h : ∀ a : A, t (f a) * f a = algebraMap K C (reducedNorm hA a))
    (R : Type*) [CommRing R] [Algebra K R] (x : R ⊗[K] A) :
    normEquationDifference hA b f t R x = 0 := by
  let P := MvPolynomial I K
  let X : P ⊗[K] A := ∑ i, MvPolynomial.X i ⊗ₜ[K] b i
  let Y := normEquationDifference hA b f t P X
  have hY : Y = 0 := by
    apply (c.baseChange P).repr.injective
    apply Finsupp.ext
    intro j
    rw [map_zero, Finsupp.zero_apply]
    apply MvPolynomial.funext
    intro z
    let a : P →ₐ[K] K := MvPolynomial.aeval z
    have hz : Algebra.TensorProduct.map a (AlgHom.id K C) Y = 0 :=
      (normEquationDifference_natural hA b f t a X).trans
        (normEquationDifference_ground hA b f t h _)
    have hcoord := coord_change c a Y j
    change (c.baseChange K).repr (Algebra.TensorProduct.map a (AlgHom.id K C) Y) j =
      a ((c.baseChange P).repr Y j) at hcoord
    change a ((c.baseChange P).repr Y j) = a 0
    rw [← hcoord, hz, map_zero, Finsupp.zero_apply, map_zero]
  let a : P →ₐ[K] R := MvPolynomial.aeval (fun i => (b.baseChange R).repr x i)
  have hX (i : I) : a (MvPolynomial.X i) = (b.baseChange R).repr x i :=
    MvPolynomial.aeval_X _ i
  have hx : Algebra.TensorProduct.map a (AlgHom.id K A) X = x := by
    simp only [X, map_sum, Algebra.TensorProduct.map_tmul, hX, AlgHom.id_apply]
    simpa only [Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      using (b.baseChange R).sum_repr x
  have hy := normEquationDifference_natural hA b f t a X
  change Algebra.TensorProduct.map a (AlgHom.id K C) Y = _ at hy
  rw [hY, map_zero, hx] at hy
  exact hy.symm

end NormEquation

section CliffordVectors

open LinearAlgebraicGroups.Albert CliffordAlgebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

private theorem cliffordAnticommute (q : QuadraticForm R V) (x y : V)
    (h : QuadraticMap.polar q x y = 0) :
    CliffordAlgebra.ι q y * CliffordAlgebra.ι q x =
      -(CliffordAlgebra.ι q x * CliffordAlgebra.ι q y) := by
  rw [eq_neg_iff_add_eq_zero, add_comm, ι_mul_ι_add_swap, h, map_zero]

private theorem reverseCliffordTriple (q : QuadraticForm R V) (x y z : V)
    (hxy : QuadraticMap.polar q x y = 0) (hxz : QuadraticMap.polar q x z = 0)
    (hyz : QuadraticMap.polar q y z = 0) :
    reverse (CliffordAlgebra.ι q x * CliffordAlgebra.ι q y * CliffordAlgebra.ι q z) =
      -(CliffordAlgebra.ι q x * CliffordAlgebra.ι q y * CliffordAlgebra.ι q z) := by
  let X := CliffordAlgebra.ι q x
  let Y := CliffordAlgebra.ι q y
  let Z := CliffordAlgebra.ι q z
  have hYX : Y * X = -(X * Y) := cliffordAnticommute q x y hxy
  have hZX : Z * X = -(X * Z) := cliffordAnticommute q x z hxz
  have hZY : Z * Y = -(Y * Z) := cliffordAnticommute q y z hyz
  rw [reverse.map_mul, reverse.map_mul, reverse_ι, reverse_ι, reverse_ι]
  change Z * (Y * X) = -(X * Y * Z)
  calc
    Z * (Y * X) = -((Y * Z) * X) := by rw [← mul_assoc, hZY, neg_mul]
    _ = Y * (X * Z) := by rw [mul_assoc, hZX, mul_neg, neg_neg]
    _ = -(X * Y * Z) := by rw [← mul_assoc, hYX, neg_mul]

private theorem orderedWordList {I : Type*} [LinearOrder I]
    (q : QuadraticForm R V) (b : Module.Basis I R V) (s : Finset I) :
    ∃ l : List I, l.length = s.card ∧ l.Pairwise (· < ·) ∧
      CliffordSpecification.orderedWord q b s =
        (l.map (fun i => CliffordAlgebra.ι q (b i))).prod := by
  let f := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := s) rfl)
  refine ⟨List.ofFn f, List.length_ofFn, List.pairwise_ofFn.mpr ?_, ?_⟩
  · intro i j hij
    exact f.strictMono hij
  · rw [List.map_ofFn]
    rfl

private theorem reverseTernaryVolume (q : QuadraticForm R V) (b : Module.Basis (Fin 3) R V)
    (hb : ∀ i j, i ≠ j → QuadraticMap.polar q (b i) (b j) = 0) :
    reverse (CliffordSpecification.orderedWord q b Finset.univ) =
      -CliffordSpecification.orderedWord q b Finset.univ := by
  obtain ⟨l, hlen, hp, hw⟩ := orderedWordList q b Finset.univ
  have hl : l.length = 3 := by simpa using hlen
  obtain ⟨i, j, k, rfl⟩ := List.length_eq_three.mp hl
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hp
  obtain ⟨⟨hij, hik⟩, hjk⟩ := hp
  rw [hw]
  simpa [mul_assoc] using reverseCliffordTriple q (b i) (b j) (b k)
    (hb _ _ (ne_of_lt hij)) (hb _ _ (ne_of_lt hik)) (hb _ _ (ne_of_lt hjk.1))

/-- The odd elements fixed by reversion in a ternary Clifford algebra are the
embedded vectors. -/
private theorem ternaryVectorsOfOddReverseFixed [Invertible (2 : R)]
    (q : QuadraticForm R V) (b : Module.Basis (Fin 3) R V)
    (hb : ∀ i j, i ≠ j → QuadraticMap.polar q (b i) (b j) = 0)
    {x : CliffordAlgebra q} (hx : x ∈ evenOdd q 1) (hr : reverse x = x) :
    x ∈ LinearMap.range (CliffordAlgebra.ι q) := by
  let ω := CliffordSpecification.orderedWord q b Finset.univ
  have hω : reverse ω = -ω := reverseTernaryVolume q b hb
  have hd : ∃ v : V, ∃ a : R, x = CliffordAlgebra.ι q v + a • ω := by
    clear hr
    rw [LinearAlgebraicGroups.Albert.CliffordModel.parity_span q b 1] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨s, hs, rfl⟩ := hy
      change (s.card : ZMod 2) = 1 at hs
      have hc₀ : s.card ≠ 0 := by
        intro h
        have hh : (0 : ZMod 2) ≠ 1 := by decide
        exact hh (by simpa only [h, Nat.cast_zero] using hs)
      have hc₂ : s.card ≠ 2 := by
        intro h
        have hh : ((2 : ℕ) : ZMod 2) ≠ 1 := by decide
        exact hh (by simpa only [h] using hs)
      have hc₃ : s.card ≤ 3 := by simpa using (Finset.card_le_univ s)
      have hc : s.card = 1 ∨ s.card = 3 := by omega
      rcases hc with hc | hc
      · obtain ⟨l, hl, _, hw⟩ := orderedWordList q b s
        obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp (hl.trans hc)
        exact ⟨b i, 0, by simp [hw]⟩
      · have h : s = Finset.univ := s.eq_univ_of_card (by simpa using hc)
        subst s
        exact ⟨0, 1, by simp [ω]⟩
    | zero => exact ⟨0, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨v, a, rfl⟩ := hx
      obtain ⟨w, c, rfl⟩ := hy
      exact ⟨v + w, a + c, by simp only [map_add, add_smul]; abel⟩
    | smul c x _ hx =>
      obtain ⟨v, a, rfl⟩ := hx
      exact ⟨c • v, c * a, by rw [map_smul, smul_add, smul_smul]⟩
  obtain ⟨v, a, rfl⟩ := hd
  have hneg : -(a • ω) = a • ω := by
    simpa only [map_add, map_smul, reverse_ι, hω, smul_neg, add_left_cancel_iff] using hr
  have htwo : (2 : R) • (a • ω) = 0 := by
    rw [two_smul, ← neg_eq_iff_add_eq_zero]
    exact hneg
  have ha : a • ω = 0 := by
    have h := congrArg (fun z : CliffordAlgebra q => (⅟ (2 : R)) • z) htwo
    rw [smul_smul, invOf_mul_self, one_smul, smul_zero] at h
    exact h
  exact ⟨v, by rw [ha, add_zero]⟩

/-- In ternary dimension, the even norm-one condition ensures vector preservation
even over commutative test rings. -/
theorem ternaryEvenNormOnePreservesVectors [Invertible (2 : R)]
    (q : QuadraticForm R V) (b : Module.Basis (Fin 3) R V)
    (hb : ∀ i j, i ≠ j → QuadraticMap.polar q (b i) (b j) = 0)
    (a : (CliffordAlgebra q)ˣ) (ha : a.val ∈ evenOdd q 0)
    (hn : reverse a.val * a.val = 1) :
    Set.MapsTo (fun x : CliffordAlgebra q => a.val * x * a⁻¹.val)
      (LinearMap.range (CliffordAlgebra.ι q)) (LinearMap.range (CliffordAlgebra.ι q)) := by
  have he : reverse a.val = a⁻¹.val := by
    calc
      reverse a.val = (reverse a.val * a.val) * a⁻¹.val := by simp [mul_assoc]
      _ = a⁻¹.val := by rw [hn, one_mul]
  have hai : a⁻¹.val ∈ evenOdd q 0 := he ▸ (reverse_mem_evenOdd_iff (x := a.val) (n := 0)).mpr ha
  rintro _ ⟨x, rfl⟩
  apply ternaryVectorsOfOddReverseFixed q b hb
  · have h₁ : a.val * CliffordAlgebra.ι q x ∈ evenOdd q 1 := by
      simpa only [zero_add] using SetLike.mul_mem_graded ha (ι_mem_evenOdd_one q x)
    simpa only [add_zero] using SetLike.mul_mem_graded h₁ hai
  · have hi : reverse a⁻¹.val = a.val := by rw [← he, reverse_reverse]
    change reverse (a.val * CliffordAlgebra.ι q x * a⁻¹.val) =
      a.val * CliffordAlgebra.ι q x * a⁻¹.val
    rw [reverse.map_mul, reverse.map_mul, hi, he, reverse_ι, mul_assoc]

open LinearAlgebraicGroups.Albert.SpinSpecification
  (ScalarClifford vectors evenPart reversion spinUnits conjugate)
open private cliffordEquiv cliffordEquiv_vector cliffordEquiv_even from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private baseChangeEquiv_reverse from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CliffordModel

/-- On every scalar extension, an even norm-one ternary Clifford unit
preserves the vector summand in both directions. -/
theorem ternarySpinUnitsIff {S : Type*} [CommRing S] [Algebra R S] [Invertible (2 : S)]
    (q : QuadraticForm R V) (b : Module.Basis (Fin 3) R V)
    (hb : ∀ i j, i ≠ j → QuadraticMap.polar q (b i) (b j) = 0)
    (a : (ScalarClifford q S)ˣ) :
    a ∈ spinUnits q S ↔ a.val ∈ evenPart q S ∧ reversion q S a.val * a.val = 1 := by
  refine ⟨fun h => ⟨h.1, h.2.1⟩, ?_⟩
  rintro ⟨ha, hn⟩
  let Q := CliffordSpecification.coefficientForm S q b
  let c := b.baseChange S
  have hc (i j : Fin 3) (hij : i ≠ j) :
      QuadraticMap.polar Q (c i) (c j) = 0 := by
    change QuadraticMap.polar (LinearMap.BilinForm.baseChange S (q.toBilin b)).toQuadraticMap (c i) (c j) = 0
    rw [LinearMap.BilinMap.polar_toQuadraticMap]
    simp only [c, Module.Basis.baseChange_apply, LinearMap.BilinForm.baseChange_tmul,
      one_mul]
    rw [← add_smul, ← LinearMap.BilinMap.polar_toQuadraticMap, q.toQuadraticMap_toBilin,
      hb i j hij, zero_smul]
  let e := cliffordEquiv q S b
  let u : (CliffordAlgebra Q)ˣ := Units.map e.toMonoidHom a
  have hu : u.val ∈ evenOdd Q 0 := (cliffordEquiv_even q S b a.val).mpr ha
  have hnu : reverse u.val * u.val = 1 := by
    change reverse (e a.val) * e a.val = 1
    rw [show reverse (e a.val) = e (reversion q S a.val) from
      (baseChangeEquiv_reverse S q b _).symm, ← map_mul, hn, map_one]
  have hinv : reverse u.val = u⁻¹.val := by
    calc
      reverse u.val = (reverse u.val * u.val) * u⁻¹.val := by simp [mul_assoc]
      _ = u⁻¹.val := by rw [hnu, one_mul]
  have hui : u⁻¹.val ∈ evenOdd Q 0 := hinv ▸
    (reverse_mem_evenOdd_iff (x := u.val) (n := 0)).mpr hu
  have hni : reverse u⁻¹.val * u⁻¹.val = 1 := by
    rw [← hinv, reverse_reverse, hinv, Units.mul_inv]
  have hM (g : (ScalarClifford q S)ˣ)
      (hpres : Set.MapsTo (fun x : CliffordAlgebra Q =>
        e g.val * x * e g⁻¹.val) (LinearMap.range (CliffordAlgebra.ι Q))
          (LinearMap.range (CliffordAlgebra.ι Q))) :
      Set.MapsTo (conjugate q S g) (LinearMap.range (vectors q S))
        (LinearMap.range (vectors q S)) := by
    rintro y ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hpres (LinearMap.mem_range_self _ x)
    refine ⟨z, e.injective ?_⟩
    change e (vectors q S z) = e (g.val * vectors q S x * g⁻¹.val)
    rw [map_mul, map_mul, cliffordEquiv_vector, cliffordEquiv_vector]
    exact hz
  refine ⟨ha, hn, hM a ?_, hM a⁻¹ ?_⟩
  · exact ternaryEvenNormOnePreservesVectors Q c hc u hu hnu
  · exact ternaryEvenNormOnePreservesVectors Q c hc u⁻¹ hui hni

end CliffordVectors

section SpinNormOne

open CliffordAlgebra
open LinearAlgebraicGroups.Albert
open SpinSpecification (ScalarClifford evenPart reversion spinUnits SchemePoints
  IsSpinPointRepresentation coefficientMap)
open Specs.OuterTypeAModels (RepresentsNormOne)
open _root_.RM03.CSA (IsCentralSimple reducedNorm)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)
open _root_.RM03.CSA.NormOneGroup (isUnit_of_normAt_eq_one)

variable {K V A I : Type u} [Field K] [Infinite K] [AddCommGroup V] [Module K V]
  [Ring A] [Algebra K A] [Fintype I]
  (q : QuadraticForm K V) (b : Module.Basis (Fin 3) K V)
  (j : A ≃ₐ[K] even q)

/-- Inclusion of the coefficient extension of the even Clifford algebra. -/
private def normModelInClifford (S : Type*) [CommRing S] [Algebra K S] :
    S ⊗[K] A →ₐ[K] ScalarClifford q S :=
  Algebra.TensorProduct.map (AlgHom.id K S) ((even q).val.comp j.toAlgHom)

omit [Infinite K] in
private theorem normModelInClifford_injective_range
    (S : Type*) [CommRing S] [Algebra K S] :
    Function.Injective (normModelInClifford q j S) ∧
      Set.range (normModelInClifford q j S) = (evenPart q S : Set (ScalarClifford q S)) := by
  let l : even q →ₗ[K] CliffordAlgebra q := (even q).val.toLinearMap
  let E := j.toLinearEquiv.baseChange K S A (even q)
  have hmap (x : S ⊗[K] A) :
      normModelInClifford q j S x = l.baseChange S (E x) := by
    induction x with
    | tmul s a => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hinj : Function.Injective (l.baseChange S) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap l Subtype.val_injective
  refine ⟨fun x y h => E.injective (hinj ((hmap x).symm.trans (h.trans (hmap y)))), ?_⟩
  ext x
  change (∃ a, normModelInClifford q j S a = x) ↔ ∃ a, l.baseChange S a = x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨E a, (hmap a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨E.symm a, (hmap _).trans (congrArg _ (E.apply_symm_apply _))⟩

omit [Infinite K] in
private theorem normModelInClifford_natural
    {S T : Type*} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]
    (a : S →ₐ[K] T) (x : S ⊗[K] A) :
    normModelInClifford q j T (Algebra.TensorProduct.map a (AlgHom.id K A) x) =
      coefficientMap q S a (normModelInClifford q j S x) := by
  induction x with
  | tmul s x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
/-- A ternary even-algebra identification intertwining reversion norm
with reduced norm represents the same group on every test algebra. -/
private theorem representsNormOneOfTernaryClifford
    (h₂ : (2 : K) ≠ 0)
    (hb : ∀ i k, i ≠ k → QuadraticMap.polar q (b i) (b k) = 0)
    (hA : _root_.Specs.RM03.CSA.isCentralSimple K A) (d : Module.Basis I K A)
    (hn : ∀ x : A, reverse (j x : CliffordAlgebra q) * (j x : CliffordAlgebra q) =
      algebraMap K (CliffordAlgebra q) (reducedNorm hA x))
    (G : AffineAlgebraicGroup K)
    (e : ∀ S : TestAlgebra K, SchemePoints G.val S →* (ScalarClifford q S)ˣ)
    (he : IsSpinPointRepresentation q G.val e) :
    RepresentsNormOne hA d G := by
  classical
  let f := (even q).val.comp j.toAlgHom
  let F (S : TestAlgebra K) := normModelInClifford q j S
  have hi S : Function.Injective (F S) := (normModelInClifford_injective_range q j S).1
  have hr S : Set.range (F S) = (evenPart q S : Set (ScalarClifford q S)) :=
    (normModelInClifford_injective_range q j S).2
  obtain ⟨c, _⟩ := CliffordModel.ordered_basis q b
  have hnorm (S : TestAlgebra K) (x : S ⊗[K] A) :
      reversion q S (F S x) * F S x = algebraMap S (ScalarClifford q S) (normAt hA d x) :=
    sub_eq_zero.mp (normEquationOnTestAlgebras hA d f reverse c hn S x)
  have hspin (S : TestAlgebra K) (x : S ⊗[K] A) (y : (ScalarClifford q S)ˣ)
      (hxy : F S x = y.val) :
      y ∈ spinUnits q S ↔ normAt hA d x = 1 := by
    let : Invertible (2 : S) := (show IsUnit (2 : S) from
      by simpa only [map_ofNat] using ((isUnit_iff_ne_zero.mpr h₂).map (algebraMap K S))).invertible
    let : IsSimpleRing A := hA.1
    let : Nontrivial (CliffordAlgebra q) :=
      Function.Injective.nontrivial (show Function.Injective f from Subtype.val_injective.comp j.injective)
    have hS : Function.Injective (algebraMap S (ScalarClifford q S)) :=
      Algebra.TensorProduct.includeLeft_injective (R := K) (S := (S : Type u))
        (A := (S : Type u)) (B := CliffordAlgebra q) (algebraMap K (CliffordAlgebra q)).injective
    have hx : F S x ∈ evenPart q S := by
      change F S x ∈ (evenPart q S : Set _)
      rw [← hr S]
      exact Set.mem_range_self x
    rw [ternarySpinUnitsIff q b hb y, ← hxy, hnorm, ← map_one (algebraMap S (ScalarClifford q S)),
      hS.eq_iff]
    exact and_iff_right hx
  have pointsEquiv (S : TestAlgebra K) : ∃ p : Points G.val.X S ≃
      {x : S ⊗[K] A // normAt hA d x = 1},
      ∀ x : Points G.val.X S, F S (p x).val = (e S x).val := by
    let φ (x : {x : S ⊗[K] A // normAt hA d x = 1}) : (ScalarClifford q S)ˣ :=
      Units.map (F S).toMonoidHom ((isUnit_of_normAt_eq_one hA d x.val x.property).unit)
    have hφ (x : {x : S ⊗[K] A // normAt hA d x = 1}) : (φ x).val = F S x.val :=
      congrArg (F S) (IsUnit.unit_spec _)
    let φ' (x : {x : S ⊗[K] A // normAt hA d x = 1}) :
        {y : (ScalarClifford q S)ˣ // y ∈ spinUnits q S} :=
      ⟨φ x, (hspin S x.val (φ x) (hφ x).symm).mpr x.property⟩
    have hinj : Function.Injective φ' := by
      intro x y h
      exact Subtype.ext (hi S ((hφ x).symm.trans
        ((congrArg (fun z => z.val.val) h).trans (hφ y))))
    have hsurj : Function.Surjective φ' := by
      rintro ⟨y, hy⟩
      have hmem : y.val ∈ Set.range (F S) := (hr S).symm ▸ hy.1
      obtain ⟨x, hx⟩ := hmem
      let z : {x : S ⊗[K] A // normAt hA d x = 1} := ⟨x, (hspin S x y hx).mp hy⟩
      exact ⟨z, Subtype.ext (Units.ext ((hφ z).trans hx))⟩
    let ψ' (x : Points G.val.X S) : {y : (ScalarClifford q S)ˣ // y ∈ spinUnits q S} :=
      ⟨e S x, (he.1 S).2 ▸ Set.mem_range_self x⟩
    have hψ : Function.Bijective ψ' := by
      refine ⟨fun x y h => (he.1 S).1 (congrArg Subtype.val h), ?_⟩
      rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := (he.1 S).2.symm ▸ hy
      exact ⟨x, Subtype.ext hx⟩
    let E := Equiv.ofBijective φ' ⟨hinj, hsurj⟩
    refine ⟨(Equiv.ofBijective ψ' hψ).trans E.symm, fun x => ?_⟩
    change F S (E.symm (ψ' x)).val = (e S x).val
    have h := congrArg (fun z => z.val.val) (E.apply_symm_apply (ψ' x))
    exact (hφ _).symm.trans h
  choose p hp using pointsEquiv
  refine ⟨p, ?_, ?_⟩
  · intro S x y
    apply hi S
    calc
      F S (p S (x * y)).val = (e S (x * y)).val := hp S _
      _ = (e S x).val * (e S y).val := congrArg Units.val ((e S).map_mul x y)
      _ = F S ((p S x).val * (p S y).val) :=
        (map_mul (F S) _ _).trans
          (congrArg₂ (· * ·) (hp S x) (hp S y)) |>.symm
  · intro S T a x
    apply hi T
    calc
      F T (p T (mapPoints a x)).val = (e T (mapPoints a x)).val := hp T _
      _ = coefficientMap q S a.hom (e S x).val := congrArg Units.val (he.2 a x)
      _ = coefficientMap q S a.hom (F S (p S x).val) := congrArg _ (hp S x).symm
      _ = F T (Algebra.TensorProduct.map a.hom (AlgHom.id K A) (p S x).val) :=
        (normModelInClifford_natural q j a.hom _).symm

open private quaternion_reduced_norm quaternion_isUnit_or_zero quaternion_central from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuadraticIsotropy

/-- The spin functor of an anisotropic ternary form in characteristic zero
is the reduced-norm-one functor of a central division quaternion algebra. -/
theorem anisotropicTernarySpinNormOne {K V : Type u} [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (q : QuadraticForm K V)
    (hdim : Module.finrank K V = 3) (ha : ∀ x, q x = 0 → x = 0)
    (G : AffineAlgebraicGroup K)
    (e : ∀ S : TestAlgebra K, SchemePoints G.val S →* (ScalarClifford q S)ˣ)
    (he : IsSpinPointRepresentation q G.val e) :
    ∃ (A : Type u) (dA : DivisionRing A), letI := dA
      ∃ aA : Algebra K A, letI := aA
        ∃ (hA : IsCentralSimple K A) (bA : Module.Basis (Index.{u} 4) K A),
          RepresentsNormOne hA bA G := by
  have h₂ : (2 : K) ≠ 0 := two_ne_zero
  obtain ⟨b, hb⟩ := ternaryBasis q h₂ hdim
  let α := -(q (b 0) * q (b 1))
  let β := -(q (b 0) * q (b 2))
  let A := QuaternionAlgebra K α 0 β
  have hc (i : Fin 3) : q (b i) ≠ 0 := fun h => b.ne_zero i (ha _ h)
  have hα : α ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (hc 0) (hc 1))
  have hβ : β ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (hc 0) (hc 2))
  have hD : ∀ x : A, IsUnit x ∨ x = 0 :=
    quaternion_isUnit_or_zero (ternaryPureNormAnisotropic q b h₂ ha hb)
  let inst : DivisionRing A := DivisionRing.ofIsUnitOrEqZero hD
  let := inst
  let hA : IsCentralSimple K A := ⟨inferInstance, quaternion_central h₂ hα, inferInstance⟩
  let d : Module.Basis (Index.{u} 4) K A := (QuaternionAlgebra.basisOneIJK α 0 β).reindex Equiv.ulift.symm
  obtain ⟨j, hj⟩ := evenCliffordQuaternionEquiv q b hb
  let f : A →ₐ[K] CliffordAlgebra q := (even q).val.comp j.toAlgHom
  have hrev (x : A) : reverse (f x) = f (star x) := by
    change reverse (j x : CliffordAlgebra q) = (j (star x) : CliffordAlgebra q)
    rw [hj x, hj (star x)]
    exact reverseEvenQuaternion q _ _ _ (hb _ _ (by decide)) (hb _ _ (by decide))
      (hb _ _ (by decide)) x
  have hn (x : A) : reverse (f x) * f x =
      algebraMap K (CliffordAlgebra q) (reducedNorm hA x) := by
    rw [hrev x, ← map_mul, star_comm_self', x.mul_star_eq_coe]
    change f (algebraMap K A (x * star x).re) = _
    rw [f.commutes]
    exact congrArg _ (quaternion_reduced_norm h₂ hα hβ hA x).symm
  exact ⟨A, inst, inferInstance, hA, d, representsNormOneOfTernaryClifford q b j h₂ hb hA d hn G e he⟩

/-- The rank-one spin application follows from the division inner type A
application for the original global group and each original realization. -/
theorem rankOneOfInnerTypeA
    (hInner : Specs.Arithmetic.AnisotropicDivisionApproximation.InnerTypeA.{u,v}) :
    Specs.Arithmetic.AnisotropicDivisionApproximation.RankOneQuadraticSpin.{u,v} := by
  intro K V _ _ _ _ _ q _ ha hdim G e hG hsc hani he
  obtain ⟨A, instD, instA, hA, b, hm⟩ := anisotropicTernarySpinNormOne q hdim ha G e he
  let := instD
  let := instA
  exact hInner (GlobalFieldData.number.{u,v} inferInstance) hA b G hG hsc hani hm

end SpinNormOne

/-- Compactness of the full adelic quotient and strong approximation for the
norm-one group of a central division algebra. -/
theorem innerTypeA : Specs.Arithmetic.AnisotropicDivisionApproximation.InnerTypeA.{u,v} := by
  intro K A _ D _ _ hA I _ b G hG hsc _ hModel i
  have hcompact := DivisionNormOneAdelicCompactness.compactQuotient D hA b G hModel i
  obtain ⟨E, hgood⟩ :=
    DivisionNormOneFiniteSplitFactors.finiteSplitFactors D hA b G hG hsc hModel
  refine ⟨hcompact, ?_⟩
  intro S hSne hS
  obtain ⟨T, _, harch, hT, liftApproximation⟩ :=
    DivisionNormOneArchimedeanReduction.archimedeanReduction D hA b G hG hsc hModel i
      hcompact S hSne hS
  exact liftApproximation (normOneStrongApproximationWithCompactInfinity
    LocalProjectedClosure.localProjectedClosure hModel D i T hG hcompact hT harch E
    (fun p hp => Or.inl ⟨(hgood p hp).1, (hgood p hp).2.1⟩)
    (fun p hp => (hgood p hp).2.2 i))

/-- The ternary spin group has the same adelic conclusions through its
even Clifford norm-one model. -/
theorem rankOneQuadraticSpin :
    Specs.Arithmetic.AnisotropicDivisionApproximation.RankOneQuadraticSpin.{u,v} :=
  rankOneOfInnerTypeA innerTypeA

end LinearAlgebraicGroups.Arithmetic.AnisotropicDivisionApproximation
