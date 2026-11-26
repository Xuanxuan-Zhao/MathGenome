import Specs.LinearAlgebraicGroups.Arithmetic.AnisotropicSpinQuotients
import LinearAlgebraicGroups.Arithmetic.AnisotropicTensorQuotients
import LinearAlgebraicGroups.Arithmetic.LocalQuadraticIsotropy
import LinearAlgebraicGroups.Arithmetic.SpinScalarExtension
import LinearAlgebraicGroups.Arithmetic.AdelicGroups
import LinearAlgebraicGroups.Arithmetic.KummerObstructions
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import LinearAlgebraicGroups.Albert.SpinFunctor
import LinearAlgebraicGroups.Affine.SchemeImageQuotient
import LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.RingTheory.Localization.Integer
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Polynomial.BigOperators

open AlgebraicGeometry CategoryTheory Filter Set Topology
open LinearAlgebraicGroups.Arithmetic
open scoped RestrictedProduct NNReal BigOperators Polynomial RatFunc

set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace LinearAlgebraicGroups.Arithmetic.AnisotropicSpinQuotients

open Polynomial

open AdelicGroups
open Specs.Arithmetic.AnisotropicSpinQuotients


theorem compactOfCoverReductionUsingObstructions.{u} : CompactOfCoverReduction.{u} := by
  intro G H P Q E _ _ _ _ _ _ _ _ _ F f dG dH ν C A hcomm hker hC hA hF hreduce
  classical
  let labels := A ∩ Set.range ν
  have hlabels : labels.Finite := hA.subset Set.inter_subset_left
  let representative (a : labels) : Q := Classical.choose a.property.2
  have hrep (a : labels) : ν (representative a) = a.val := Classical.choose_spec a.property.2
  let B : Set H := ⋃ a : labels, (fun y => y * (dH (representative a))⁻¹) '' C
  have hB : IsCompact B := by
    letI : Finite labels := hlabels.to_subtype
    exact isCompact_iUnion fun a => hC.image (continuous_mul_const _)
  let quotient : G → G ⧸ dG.range := QuotientGroup.mk
  have hsurj : quotient '' (F ⁻¹' B) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨q, hq, hνq⟩ := hreduce g
    let a : labels := ⟨ν q, hνq, ⟨q, rfl⟩⟩
    have hv : ν (q * (representative a)⁻¹) = 1 := by
      rw [map_mul, map_inv, hrep a]
      exact mul_inv_cancel _
    obtain ⟨p, hp⟩ := (hker _).mp hv
    refine ⟨g * dG p, ?_, ?_⟩
    · change F (g * dG p) ∈ B
      refine Set.mem_iUnion.mpr ⟨a, F g * dH q, hq, ?_⟩
      simp only [map_mul, hcomm, hp, map_inv, mul_assoc]
    · exact QuotientGroup.mk_mul_of_mem g ⟨p, rfl⟩
  rw [← isCompact_univ_iff, ← hsurj]
  exact (hF B hB).image continuous_quot_mk

/-- Compact subsets of a restricted product are integral off one finite set of indices. -/
theorem compactRestrictedProductIntegrality {W : Type*} {H : W → Type*}
    [∀ w, TopologicalSpace (H w)] (B : ∀ w, Set (H w)) (hB : ∀ w, IsOpen (B w))
    (C : Set (Πʳ w, [H w, B w])) (hC : IsCompact C) :
    ∃ T : Finset W, ∀ c ∈ C, ∀ w ∉ T, c w ∈ B w := by
  classical
  let U (T : Finset W) : Set (Πʳ w, [H w, B w]) :=
    {c | ∀ w, w ∉ T → c w ∈ B w}
  have hU (T : Finset W) : IsOpen (U T) := RestrictedProduct.isOpen_forall_imp_mem hB
  have hcover : C ⊆ ⋃ T, U T := by
    intro c _
    have hfinite : {w | c w ∉ B w}.Finite := Filter.eventually_cofinite.mp c.2
    refine Set.mem_iUnion.mpr ⟨hfinite.toFinset, fun w hw => ?_⟩
    simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hw
  obtain ⟨Ts, hTs⟩ := hC.elim_finite_subcover U hU hcover
  refine ⟨Ts.biUnion id, ?_⟩
  intro c hc w hw
  obtain ⟨T, hT, hc'⟩ := Set.mem_iUnion₂.mp (hTs hc)
  exact hc' w (fun h => hw (Finset.mem_biUnion.mpr ⟨T, hT, h⟩))

/-- Coordinatewise maps with compact inverse images have compact inverse
images on restricted products when the inverse image of almost every local
integral set is contained in the corresponding source integral set. -/
theorem compactRestrictedProductPreimage {W : Type*} {G H : W → Type*}
    [∀ w, TopologicalSpace (G w)] [∀ w, TopologicalSpace (H w)] [∀ w, T2Space (H w)]
    (A : ∀ w, Set (G w)) (B : ∀ w, Set (H w)) (hB : ∀ w, IsOpen (B w))
    (φ : ∀ w, G w → H w) (hφ : ∀ w, Continuous (φ w))
    (hmap : ∀ᶠ w in cofinite, MapsTo (φ w) (A w) (B w))
    (hrev : ∀ᶠ w in cofinite, (φ w) ⁻¹' B w ⊆ A w)
    (hproper : ∀ w (C : Set (H w)), IsCompact C → IsCompact ((φ w) ⁻¹' C))
    (C : Set (Πʳ w, [H w, B w])) (hC : IsCompact C) :
    IsCompact ((RestrictedProduct.map φ hmap) ⁻¹' C) := by
  classical
  let F := RestrictedProduct.map φ hmap
  have hF : Continuous F :=
    RestrictedProduct.mapAlong_continuous G H id tendsto_id φ hmap hφ
  obtain ⟨S, hbound⟩ := compactRestrictedProductIntegrality B hB C hC
  let U (w : W) := φ w ⁻¹' ((fun c : Πʳ w, [H w, B w] => c w) '' C)
  have hUc (w : W) : IsCompact (U w) :=
    hproper w _ (hC.image (RestrictedProduct.continuous_eval w))
  let P := {x : Πʳ w, [G w, A w] | ∀ w, x w ∈ U w}
  have hcof : ∀ᶠ w in cofinite, U w ⊆ A w := by
    have hS : ∀ᶠ w in cofinite, w ∉ S := by
      apply eventually_cofinite.mpr
      convert S.finite_toSet using 1
      ext w
      simp
    filter_upwards [hrev, hS] with w hw hws x hx
    obtain ⟨c, hc, he⟩ := hx
    exact hw (show φ w x ∈ B w from he ▸ hbound c hc w hws)
  have hP : IsCompact P := by
    let T : Set W := {w | U w ⊆ A w}
    have hT : cofinite ≤ 𝓟 T := Filter.le_principal_iff.mpr hcof
    have (w : W) : CompactSpace (U w) := isCompact_iff_compactSpace.mp (hUc w)
    let m (x : ∀ w, U w) : Πʳ w, [G w, A w]_[𝓟 T] :=
      ⟨fun w => (x w).val, Filter.eventually_principal.mpr fun w hw => hw (x w).property⟩
    let g := RestrictedProduct.inclusion _ _ hT ∘ m
    have hg : Continuous g :=
      (RestrictedProduct.continuous_inclusion hT).comp
        (RestrictedProduct.continuous_rng_of_principal.mpr
          (continuous_pi fun w => continuous_subtype_val.comp (continuous_apply w)))
    have hr : Set.range g = P := by
      ext x
      refine ⟨?_, fun hx => ⟨fun w => ⟨x w, hx w⟩, ?_⟩⟩
      · rintro ⟨y, rfl⟩ w
        exact (y w).property
      · exact RestrictedProduct.ext _ _ fun _ => rfl
    exact hr ▸ isCompact_range hg
  refine hP.of_isClosed_subset (hC.isClosed.preimage hF) ?_
  intro x hx w
  exact ⟨F x, hx, rfl⟩

theorem compactMonicPreimage {X Y B F I : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    [CommRing B] [NormedField F] [ProperSpace F]
    (c : X → I → F) (hc : IsClosedEmbedding c)
    (f : X → Y) (hf : Continuous f) (a : Y → B →+* F)
    (ha : ∀ b, Continuous (fun y => a y b))
    (hmonic : ∀ i, ∃ p : Polynomial B, p.Monic ∧ ∀ x, (p.map (a (f x))).IsRoot (c x i))
    (C : Set Y) (hC : IsCompact C) :
    IsCompact (f ⁻¹' C) := by
  classical
  have hbound (i : I) : ∃ b : ℝ≥0, ∀ x, f x ∈ C → ‖c x i‖₊ ≤ b := by
    obtain ⟨p, hp, hroot⟩ := hmonic i
    have hcoeff (n : Fin p.natDegree) : ∃ b : ℝ≥0, ∀ y ∈ C, ‖a y (p.coeff n)‖₊ ≤ b := by
      obtain ⟨b, hb⟩ := (hC.image (continuous_nnnorm.comp (ha (p.coeff n)))).bddAbove
      exact ⟨b, fun y hy => hb ⟨y, hy, rfl⟩⟩
    choose b hb using hcoeff
    refine ⟨Finset.univ.sup b + 1, fun x hx => ?_⟩
    let q := p.map (a (f x))
    have hmonic : q.Monic := hp.map _
    have hdeg : q.natDegree = p.natDegree := hp.natDegree_map _
    apply ((hroot x).norm_lt_cauchyBound hmonic.ne_zero).le.trans
    rw [Polynomial.cauchyBound, hmonic.leadingCoeff, nnnorm_one, div_one, hdeg]
    apply add_le_add_left
    refine Finset.sup_le fun n hn => ?_
    rw [Polynomial.coeff_map]
    exact (hb ⟨n, Finset.mem_range.mp hn⟩ (f x) hx).trans
      (Finset.le_sup (f := b) (Finset.mem_univ _))
  choose b hb using hbound
  let U := Set.pi Set.univ (fun i => Metric.closedBall (0 : F) (b i : ℝ))
  have hU : IsCompact U := isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine (hc.isCompact_preimage hU).of_isClosed_subset (hC.isClosed.preimage hf) ?_
  intro x hx i _
  rw [mem_closedBall_zero_iff]
  exact_mod_cast hb i x hx

theorem mem_valuationSubring_of_monic {F : Type*} [Field F] (O : ValuationSubring F)
    {p : Polynomial F} (hp : p.Monic) (hcoeff : ∀ n, p.coeff n ∈ O)
    {x : F} (hx : p.IsRoot x) : x ∈ O := by
  have hlift : p ∈ Polynomial.lifts O.subtype :=
    (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨p.coeff n, hcoeff n⟩, rfl⟩
  obtain ⟨q, hq, _, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hp
  have hx' : IsIntegral O x := by
    refine ⟨q, hmonic, ?_⟩
    change q.eval₂ O.subtype x = 0
    rw [← Polynomial.eval_map, hq]
    exact hx
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx'
  exact ha ▸ a.property

noncomputable section FiniteMorphism

set_option backward.isDefEq.respectTransparency false

open Opposite
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.IntegralModels (MatrixRealization)
open Specs.StandardGroups (GLCoordinates universalMatrix)
open Specs.Unipotent (Index)

universe u v

open private coordinateMap coordinateMap_spec from LinearAlgebraicGroups.Arithmetic.IntegralModels
open private glEvaluation glEvaluation_entry universalGeneralLinear from LinearAlgebraicGroups.Affine.StandardGroups
open private matrixPresentation continuous_glEvaluation glEvaluation_eventually
  eventually_outside glIntegral_iff from LinearAlgebraicGroups.Arithmetic.AdelicGroups

variable {K : Type u} [Field K] {G H : AffineAlgebraicGroup K}

private noncomputable def evaluatePoint {A : TestAlgebra K} (e : (testSpec K).obj (op A) ≅ G.val.X)
    {R : Type u} [CommRing R] [Algebra K R]
    (x : Points G.val.X (CommAlgCat.of K R)) : A →ₐ[K] R :=
  (coordinateMap (x ≫ e.inv)).hom

private theorem continuous_evaluatePoint {A : TestAlgebra K}
    (e : (testSpec K).obj (op A) ≅ G.val.X) (i : MatrixRealization G)
    {R : Type u} [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
    (a : A) : Continuous (fun x : PointsIn i R => evaluatePoint e x a) := by
  obtain ⟨d, hd, he⟩ := matrixPresentation A e i
  obtain ⟨z, rfl⟩ := hd a
  have heq (x : PointsIn i R) : evaluatePoint e x (d.hom z) = glEvaluation (asMatrix i R x) z :=
    congrArg (fun f : GLCoordinates K (Index.{u} i.size) →ₐ[K] R => f z) (he R x).symm
  simp_rw [heq]
  exact (continuous_glEvaluation (R := R) z).comp (IsInducing.induced (asMatrix i R)).continuous

private theorem eventually_integral_evaluatePoint {A : TestAlgebra K}
    (e : (testSpec K).obj (op A) ≅ G.val.X) (i : MatrixRealization G)
    (D : GlobalFieldData.{u,v} K) (a : A) :
    ∀ᶠ w : D.FinitePlace in cofinite, ∀ x ∈ integralPoints D i w,
      evaluatePoint e x a ∈ D.integers w := by
  obtain ⟨d, hd, he⟩ := matrixPresentation A e i
  obtain ⟨z, rfl⟩ := hd a
  filter_upwards [glEvaluation_eventually D z] with w hw x hx
  exact (congrArg (fun g : GLCoordinates K (Index.{u} i.size) →ₐ[K] _ => g z)
    (he (D.Completion (.inl w)) x)) ▸ hw _ hx

private theorem finite_coordinateMap {A B : TestAlgebra K}
    (eG : (testSpec K).obj (op A) ≅ G.val.X)
    (eH : (testSpec K).obj (op B) ≅ H.val.X) (f : G.val ⟶ H.val)
    (hf : IsFinite f.hom.hom.left) :
    (coordinateMap (eG.hom ≫ f.hom.hom ≫ eH.inv)).hom.toRingHom.Finite := by
  haveI : IsIso eG.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eG.hom))
  haveI : IsIso eH.inv.left := inferInstanceAs (IsIso ((Over.forget _).map eH.inv))
  let a := coordinateMap (eG.hom ≫ f.hom.hom ≫ eH.inv)
  let b := CommRingCat.ofHom a.hom.toRingHom
  change b.hom.Finite
  apply (IsFinite.SpecMap_iff b).mp
  change IsFinite ((testSpec K).map a.op).left
  rw [show (testSpec K).map a.op = _ from coordinateMap_spec _]
  exact inferInstanceAs (IsFinite (eG.hom.left ≫ f.hom.hom.left ≫ eH.inv.left))

private theorem evaluatePoint_pointMap {A B : TestAlgebra K}
    (eG : (testSpec K).obj (op A) ≅ G.val.X)
    (eH : (testSpec K).obj (op B) ≅ H.val.X)
    (f : G.val ⟶ H.val) (i : MatrixRealization G) (j : MatrixRealization H)
    {R : Type u} [CommRing R] [Algebra K R] (x : PointsIn i R) :
    (evaluatePoint eG x).comp (coordinateMap (eG.hom ≫ f.hom.hom ≫ eH.inv)).hom =
      evaluatePoint eH (pointMap f i j R x) := by
  change ((_ ≫ coordinateMap (x ≫ eG.inv)).hom : B →ₐ[K] R) = _
  congr 1
  apply Quiver.Hom.op_inj
  apply (algSpec.fullyFaithful (R := CommRingCat.of K)).map_injective
  rw [CategoryTheory.op_comp, Functor.map_comp]
  rw [coordinateMap_spec, coordinateMap_spec, coordinateMap_spec]
  change (x ≫ eG.inv) ≫ eG.hom ≫ f.hom.hom ≫ eH.inv = (x ≫ f.hom.hom) ≫ eH.inv
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private abbrev MatrixEntry (J : Type u) := (J × J) ⊕ (J × J)

private def matrixEntries {J L : Type u} [Fintype J] [DecidableEq J] [CommRing L]
    (m : Matrix.GeneralLinearGroup J L) : MatrixEntry J → L
  | .inl (s, t) => m.val s t
  | .inr (s, t) => m⁻¹.val s t

private theorem matrixEntries_closedEmbedding {J L : Type u}
    [Fintype J] [DecidableEq J] [CommRing L]
    [TopologicalSpace L] [IsTopologicalRing L] [T1Space L] :
    IsClosedEmbedding (matrixEntries (J := J) (L := L)) := by
  let e : (Matrix J J L × (Matrix J J L)ᵐᵒᵖ) ≃ₜ (MatrixEntry J → L) :=
    (((Homeomorph.refl _).prodCongr MulOpposite.opHomeomorph.symm).trans
      (Homeomorph.piCurry.symm.prodCongr Homeomorph.piCurry.symm)).trans
      (Homeomorph.sumPiEquivProdPi _ _ (fun _ => L)).symm
  convert e.isClosedEmbedding.comp (Units.isClosedEmbedding_embedProduct (α := Matrix J J L))
    using 1
  funext m x
  cases x <;> rfl

private theorem matrixEntry_evaluation {A : TestAlgebra K}
    (e : (testSpec K).obj (op A) ≅ G.val.X) (i : MatrixRealization G)
    (s : MatrixEntry (Index.{u} i.size)) :
    ∃ z : A, ∀ (R : Type u) [CommRing R] [Algebra K R] (x : PointsIn i R),
      evaluatePoint e x z = matrixEntries (asMatrix i R x) s := by
  obtain ⟨d, _, hd⟩ := matrixPresentation A e i
  let U := universalGeneralLinear (k := K) (ι := Index.{u} i.size)
  refine ⟨d.hom (matrixEntries U s), fun R _ _ x => ?_⟩
  let m := asMatrix i R x
  have hM : Matrix.GeneralLinearGroup.map (glEvaluation m).toRingHom U = m := by
    apply Matrix.GeneralLinearGroup.ext
    intro l n
    exact glEvaluation_entry _ l n
  have hE := congrArg (fun e : GLCoordinates K (Index.{u} i.size) →ₐ[K] R =>
    e (matrixEntries U s)) (hd R x)
  change _ = evaluatePoint e x (d.hom (matrixEntries U s)) at hE
  rw [← hE]
  calc
    glEvaluation m (matrixEntries U s) =
        matrixEntries (Matrix.GeneralLinearGroup.map (glEvaluation m).toRingHom U) s := by
      cases s with
      | inl t => rfl
      | inr t =>
        change glEvaluation m (U⁻¹.val t.1 t.2) =
          (Matrix.GeneralLinearGroup.map (glEvaluation m).toRingHom U)⁻¹.val t.1 t.2
        rw [← map_inv]
        rfl
    _ = _ := congrArg (fun n => matrixEntries n s) hM

private theorem isRoot_evaluatePoint {A B : TestAlgebra K}
    (eG : (testSpec K).obj (op A) ≅ G.val.X)
    (eH : (testSpec K).obj (op B) ≅ H.val.X)
    (f : G.val ⟶ H.val) (i : MatrixRealization G) (j : MatrixRealization H)
    {z : A} {p : Polynomial B}
    (hp : p.eval₂ (coordinateMap (eG.hom ≫ f.hom.hom ≫ eH.inv)).hom.toRingHom z = 0)
    {R : Type u} [CommRing R] [Algebra K R] (x : PointsIn i R) :
    (p.map (evaluatePoint eH (pointMap f i j R x)).toRingHom).IsRoot (evaluatePoint eG x z) := by
  rw [Polynomial.IsRoot, Polynomial.eval_map, ← evaluatePoint_pointMap eG eH f i j x]
  let g := (evaluatePoint eG x).toRingHom
  let a := (coordinateMap (eG.hom ≫ f.hom.hom ≫ eH.inv)).hom.toRingHom
  change p.eval₂ (g.comp a) (g z) = 0
  rw [← Polynomial.hom_eval₂, show p.eval₂ a z = 0 from hp, map_zero]

private theorem localMonicPreimage {X Y B F I : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    [CommRing B] [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (c : X → I → F) (hc : IsClosedEmbedding c)
    (f : X → Y) (hf : Continuous f) (a : Y → B →+* F)
    (ha : ∀ b, Continuous (fun y => a y b))
    (hmonic : ∀ i, ∃ p : Polynomial B, p.Monic ∧ ∀ x, (p.map (a (f x))).IsRoot (c x i))
    (C : Set Y) (hC : IsCompact C) :
    IsCompact (f ⁻¹' C) := by
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  letI : (Valued.v (R := F)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := F).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  letI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  exact compactMonicPreimage c hc f hf a ha hmonic C hC

private theorem archimedeanCompletion_proper (w : NumberField.InfinitePlace K) :
    ProperSpace w.Completion := by
  rcases w.isReal_or_isComplex with h | h
  · obtain ⟨e, he⟩ := numberRealCompletion w h
    refine ⟨fun x r => ?_⟩
    show IsCompact (Metric.closedBall x r)
    have hpre : e ⁻¹' Metric.closedBall (e x) r = Metric.closedBall x r := by
      ext y
      simp [Metric.mem_closedBall, he.dist_eq]
    rw [← hpre]
    exact he.isClosedEmbedding.isCompact_preimage (isCompact_closedBall _ _)
  · obtain ⟨e, he⟩ := numberComplexCompletion w h
    refine ⟨fun x r => ?_⟩
    show IsCompact (Metric.closedBall x r)
    have hpre : e ⁻¹' Metric.closedBall (e x) r = Metric.closedBall x r := by
      ext y
      simp [Metric.mem_closedBall, he.dist_eq]
    rw [← hpre]
    exact he.isClosedEmbedding.isCompact_preimage (isCompact_closedBall _ _)

private theorem completionMonicPreimage {X Y B I : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] [CommRing B]
    (D : GlobalFieldData.{u,v} K) (w : D.Place)
    (c : X → I → D.Completion w) (hc : IsClosedEmbedding c)
    (f : X → Y) (hf : Continuous f) (a : Y → B →+* D.Completion w)
    (ha : ∀ b, Continuous (fun y => a y b))
    (hmonic : ∀ i, ∃ p : Polynomial B, p.Monic ∧ ∀ x, (p.map (a (f x))).IsRoot (c x i))
    (C : Set Y) (hC : IsCompact C) :
    IsCompact (f ⁻¹' C) := by
  cases w with
  | inl w =>
    letI : ValuativeRel (D.Completion (.inl w)) :=
      inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
    letI : IsNonarchimedeanLocalField (D.Completion (.inl w)) :=
      inferInstanceAs (IsNonarchimedeanLocalField (D.FiniteCompletion w))
    exact localMonicPreimage c hc f hf a ha hmonic C hC
  | inr w =>
    cases D with
    | number h =>
      letI : NormedField ((GlobalFieldData.number.{u,v} h).Completion (.inr w)) :=
        inferInstanceAs (NormedField w.Completion)
      letI : ProperSpace ((GlobalFieldData.number.{u,v} h).Completion (.inr w)) :=
        archimedeanCompletion_proper w
      exact compactMonicPreimage c hc f hf a ha hmonic C hC
    | function F t => exact w.elim

set_option maxHeartbeats 1600000 in
private theorem finiteAdelicMorphismUsingCoordinates : FiniteAdelicMorphism.{u,v} := by
  classical
  intro K _ D G H f hf i j
  obtain ⟨A, ⟨eG⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.prop.1
  obtain ⟨B, ⟨eH⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr H.prop.1
  let a := coordinateMap (eG.hom ≫ f.hom.hom ≫ eH.inv)
  have ha : a.hom.toRingHom.Finite := finite_coordinateMap eG eH f hf
  let φ (w : D.Place) := pointMap f i j (D.Completion w)
  let c (w : D.Place) (x : LocalPoints D i w) := matrixEntries (asMatrix i (D.Completion w) x)
  let cH (w : D.Place) (x : LocalPoints D j w) := matrixEntries (asMatrix j (D.Completion w) x)
  have hc w : IsClosedEmbedding (c w) :=
    matrixEntries_closedEmbedding.comp (localMatrixEmbedding D i w)
  have hcH w : IsClosedEmbedding (cH w) :=
    matrixEntries_closedEmbedding.comp (localMatrixEmbedding D j w)
  choose z hz using matrixEntry_evaluation eG i
  choose y hy using matrixEntry_evaluation eH j
  have heval (w : D.Place) (x : LocalPoints D i w) (b : B.unop) :
      evaluatePoint eH (φ w x) b = evaluatePoint eG x (a.hom b) :=
    (congrArg (fun e : B.unop →ₐ[K] D.Completion w => e b)
      (evaluatePoint_pointMap eG eH f i j x)).symm
  have hφ (w : D.Place) : Continuous (φ w) := by
    apply (hcH w).isInducing.continuous_iff.mpr
    apply continuous_pi
    intro s
    have h (g : LocalPoints D i w) : cH w (φ w g) s = evaluatePoint eG g (a.hom (y s)) :=
      (hy s (D.Completion w) (φ w g)).symm.trans (heval w g (y s))
    change Continuous (fun g => cH w (φ w g) s)
    simp_rw [h]
    exact continuous_evaluatePoint eG i (a.hom (y s))
  have hmap : ∀ᶠ w : D.FinitePlace in cofinite,
      MapsTo (φ (.inl w)) (integralPoints D i w) (integralPoints D j w) := by
    have he := eventually_all.mpr fun s => eventually_integral_evaluatePoint eG i D (a.hom (y s))
    filter_upwards [he] with w hw x hx
    have h (s : MatrixEntry (Index.{u} j.size)) : cH (.inl w) (φ (.inl w) x) s ∈ D.integers w := by
      rw [show cH (.inl w) (φ (.inl w) x) s = evaluatePoint eG x (a.hom (y s)) from
        (hy s (D.Completion (.inl w)) (φ (.inl w) x)).symm.trans (heval (.inl w) x (y s))]
      exact hw s x hx
    exact (glIntegral_iff _ _).mpr ⟨fun l m => h (.inl (l,m)), fun l m => h (.inr (l,m))⟩
  choose p hp hroot using fun s => ha.to_isIntegral (z s)
  have hmonic (w : D.Place) (s : MatrixEntry (Index.{u} i.size)) (x : LocalPoints D i w) :
      ((p s).map (evaluatePoint eH (φ w x)).toRingHom).IsRoot (c w x s) := by
    rw [show c w x s = evaluatePoint eG x (z s) from (hz s (D.Completion w) x).symm]
    exact isRoot_evaluatePoint eG eH f i j (hroot s) x
  have hrev : ∀ᶠ w : D.FinitePlace in cofinite, (φ (.inl w)) ⁻¹' integralPoints D j w ⊆
      integralPoints D i w := by
    have he (s : MatrixEntry (Index.{u} i.size)) := eventually_all.mpr
      fun n : Fin ((p s).natDegree + 1) => eventually_integral_evaluatePoint eH j D ((p s).coeff n)
    filter_upwards [eventually_all.mpr he] with w hw x hx
    have hs (s : MatrixEntry (Index.{u} i.size)) : c (.inl w) x s ∈ D.integers w := by
      refine mem_valuationSubring_of_monic (D.integers w) ((hp s).map _) ?_ (hmonic (.inl w) s x)
      intro n
      rw [Polynomial.coeff_map]
      by_cases hn : n ≤ (p s).natDegree
      · exact hw s ⟨n, Nat.lt_succ_of_le hn⟩ (φ (.inl w) x) hx
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hn), map_zero]
        exact (D.integers w).zero_mem
    exact (glIntegral_iff _ _).mpr ⟨fun l m => hs (.inl (l,m)), fun l m => hs (.inr (l,m))⟩
  have hmap' : ∀ᶠ w : Outside D ∅ in cofinite,
      MapsTo (φ w.val) (localSubgroup D i w.val) (localSubgroup D j w.val) :=
    eventually_outside D ∅ (p := fun w => MapsTo (φ w)
      (localSubgroup D i w) (localSubgroup D j w)) hmap (fun _ _ _ => Subgroup.mem_top _)
  have hrev' : ∀ᶠ w : Outside D ∅ in cofinite, (φ w.val) ⁻¹'
      localSubgroup D j w.val ⊆ (localSubgroup D i w.val : Set _) :=
    eventually_outside D ∅ (p := fun w => (φ w) ⁻¹'
      localSubgroup D j w ⊆ (localSubgroup D i w : Set _))
      hrev (fun _ _ _ => Subgroup.mem_top _)
  have ht2 (w : D.Place) : T2Space (LocalPoints D j w) := (hcH w).isEmbedding.t2Space
  have hproper (w : D.Place) (C : Set (LocalPoints D j w)) (hC : IsCompact C) :
      IsCompact ((φ w) ⁻¹' C) := by
    exact completionMonicPreimage D w (c w) (hc w) (φ w) (hφ w)
      (fun y : LocalPoints D j w => (evaluatePoint eH y).toRingHom)
      (fun b => continuous_evaluatePoint eH j b) (fun s => ⟨p s, hp s, hmonic w s⟩)
      C hC
  let F : Adeles D i ∅ →* Adeles D j ∅ :=
    { toFun := RestrictedProduct.map (fun w : Outside D ∅ => φ w.val) hmap'
      map_one' := RestrictedProduct.ext _ _ (fun w => map_one (φ w.val))
      map_mul' := fun x y => RestrictedProduct.ext _ _ (fun w => map_mul (φ w.val) (x w) (y w)) }
  refine ⟨F, fun x w => rfl, ?_, ?_⟩
  · exact RestrictedProduct.mapAlong_continuous _ _ id tendsto_id _ hmap' (fun w => hφ w.val)
  · letI (w : Outside D ∅) : T2Space (LocalPoints D j w.val) := ht2 w.val
    exact compactRestrictedProductPreimage
      (fun w : Outside D ∅ => (localSubgroup D i w.val : Set _))
      (fun w => (localSubgroup D j w.val : Set _)) (fun w => localSubgroup_open D j w.val)
      (fun w => φ w.val) (fun w => hφ w.val) hmap' hrev' (fun w => hproper w.val)

end FiniteMorphism

section AdelicReduction

set_option backward.isDefEq.respectTransparency false

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.IntegralModels (MatrixRealization RationalPoints)

private theorem compactAlmostEverywhereIntegralUsingRestrictedProduct.{u,v} :
    CompactAlmostEverywhereIntegral.{u,v} := by
  intro K _ D H j C hC
  obtain ⟨T, hT⟩ := compactRestrictedProductIntegrality
    (fun w : Outside D ∅ => (localSubgroup D j w.val : Set (LocalPoints D j w.val)))
    (fun w => localSubgroup_open D j w.val) C hC
  refine ⟨Subtype.val '' (T : Set (Outside D ∅)), T.finite_toSet.image _, ?_⟩
  intro c hc w hw
  exact hT c hc w (fun h => hw ⟨w, h, rfl⟩)

/-- A finite cover transfers compact representatives when the local
square-class obstruction is integral at almost every finite place. -/
theorem compactOfSquareClassReductionWithFiniteCovers.{u,v} : CompactOfSquareClassReduction.{u,v} := by
  classical
  intro K _ D G H f i j dG dH hdG hdH hf ν νw hker hlocal htrivial hgood C hC hreduce
  obtain ⟨F, hFcoord, _, hFcompact⟩ := finiteAdelicMorphismUsingCoordinates D f hf i j
  obtain ⟨T, hT, hCT⟩ := compactAlmostEverywhereIntegralUsingRestrictedProduct D j C hC
  let bad : Set D.FinitePlace := {w | ¬ ∀ x ∈ integralPoints D j w,
      νw w x ∈ (Kummer.map (D.integers w).subtype 2).range}
  have hbad : bad.Finite := eventually_cofinite.mp hgood
  let S := T ∪ Sum.inl '' bad
  let A := (Kummer.UnramifiedOutside D S 2 : Set (Kummer.Classes K 2))
  have hA : A.Finite := by
    letI : Finite (Kummer.UnramifiedOutside D S 2) :=
      Kummer.globalFiniteness D S (hT.union (hbad.image _)) 2 (by norm_num)
    exact Set.toFinite _
  let f₀ : RationalPoints G →* RationalPoints H := pointMap f i j K
  refine compactOfCoverReductionUsingObstructions F f₀ dG dH ν C A
    ?_ hker hC hA hFcompact ?_
  · intro p
    apply RestrictedProduct.ext
    intro w
    rw [hFcoord (dG p) w, hdG p w, hdH (f₀ p) w]
    let α := (groupPointsFunctor K).map f
    let a := CommAlgCat.ofHom (Algebra.ofId K (D.Completion w.val))
    exact congrArg (fun k => k p) (α.naturality a).symm
  · intro x
    obtain ⟨h, c, hc, he⟩ := hreduce x
    refine ⟨h, ?_, ?_⟩
    · have hxc : F x * dH h = c := by
        apply RestrictedProduct.ext
        intro w
        change F x w * dH h w = c w
        exact (congrArg (fun z => z * dH h w) (hFcoord x w)).trans (he w).symm
      exact hxc ▸ hc
    · change ν h ∈ Kummer.UnramifiedOutside D S 2
      rw [Kummer.UnramifiedOutside, Subgroup.mem_iInf]
      rintro ⟨w, hw⟩
      let z : Outside D ∅ := ⟨.inl w, Finset.notMem_empty _⟩
      have hnotT : (.inl w : D.Place) ∉ T := fun hwT => hw (Or.inl hwT)
      have hnotBad : w ∉ bad := fun hw' => hw (Or.inr ⟨w, hw', rfl⟩)
      have hcint : c z ∈ integralPoints D j w := hCT c hc z hnotT
      have hν : νw w (c z) = Kummer.map (D.embedding (.inl w)) 2 (ν h) := by
        have he' : c z = pointMap f i j (D.Completion (.inl w)) (x z) * dH h z := he z
        calc
          νw w (c z) = νw w (pointMap f i j (D.Completion (.inl w)) (x z)) *
              νw w (dH h z) := by rw [he', map_mul]
          _ = νw w (localPoint D j (.inl w) h) := by
            have hd : dH h z = localPoint D j (.inl w) h := hdH h z
            exact (congrArg₂ (· * ·) (htrivial w (x z)) (congrArg (νw w) hd)).trans
              (one_mul (νw w (localPoint D j (.inl w) h)))
          _ = _ := hlocal w h
      change Kummer.map (D.embedding (.inl w)) 2 (ν h) ∈
        (Kummer.map (D.integers w).subtype 2).range
      rw [← hν]
      exact (not_not.mp hnotBad) (c z) hcint

end AdelicReduction

noncomputable section CliffordAction

set_option backward.isDefEq.respectTransparency false

open Opposite
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.Unipotent (Index)
open Albert.SpinSpecification (IsSpinPointRepresentation SchemePoints ScalarClifford
  IsVectorAction vectors conjugate)
open scoped TensorProduct CategoryTheory.MonObj

universe u

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
variable {n : ℕ} (q : QuadraticForm K V) (b : Module.Basis (Index.{u} n) K V)
variable (G : AffineAlgebraicGroup K)
variable (e : ∀ S : CommAlgCat.{u} K, SchemePoints G.val S →* (ScalarClifford q S)ˣ)
variable (he : IsSpinPointRepresentation q G.val e)

open private changeModule changeModule_basis changeModule_coord vectors_injective
  from LinearAlgebraicGroups.Albert.SpinFunctor

/-- Interpret a scheme point in the intrinsic Clifford subgroup. -/
private def spinPoint (S : CommAlgCat.{u} K) :
    ((groupPointsFunctor K).obj G.val).obj S →* Albert.SpinFunctor.Spin q S b :=
  (e S).codRestrict _ (fun x => by
    change (e S) x ∈ Albert.SpinSpecification.spinUnits q S
    rw [← (he.1 S).2]
    exact Set.mem_range_self x)

private theorem spinPoint_natural {S T : CommAlgCat.{u} K} (f : S ⟶ T)
    (x : ((groupPointsFunctor K).obj G.val).obj S) :
    spinPoint q b G e he T (((groupPointsFunctor K).obj G.val).map f x) =
      Albert.SpinFunctor.map q b f.hom (spinPoint q b G e he S x) := by
  apply Subtype.ext
  exact he.2 f x

/-- The matrix of the conjugation action in the original scalar-extended basis. -/
def cliffordActionMatrix (S : CommAlgCat.{u} K) :
    ((groupPointsFunctor K).obj G.val).obj S →* Matrix.GeneralLinearGroup (Index.{u} n) S :=
  (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (b.baseChange S)).toMulEquiv).toMonoidHom.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv S (S ⊗[K] V)).symm.toMonoidHom.comp
      ((Albert.SpinFunctor.vectorAction q S b).comp (spinPoint q b G e he S)))

private theorem cliffordActionMatrix_entry (S : CommAlgCat.{u} K)
    (x : ((groupPointsFunctor K).obj G.val).obj S)
    (i j : Index.{u} n) :
    (cliffordActionMatrix q b G e he S x).val i j =
      (b.baseChange S).coord i
        (Albert.SpinFunctor.vectorAction q S b (spinPoint q b G e he S x) (b.baseChange S j)) := by
  change LinearMap.toMatrixAlgEquiv (b.baseChange S) _ i j = _
  rw [LinearMap.toMatrixAlgEquiv_apply]
  rfl

private theorem cliffordActionMatrix_natural {S T : CommAlgCat.{u} K} (f : S ⟶ T)
    (x : ((groupPointsFunctor K).obj G.val).obj S) :
    Matrix.GeneralLinearGroup.map f.hom.toRingHom (cliffordActionMatrix q b G e he S x) =
      cliffordActionMatrix q b G e he T (((groupPointsFunctor K).obj G.val).map f x) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change f.hom ((cliffordActionMatrix q b G e he S x).val i j) = _
  rw [cliffordActionMatrix_entry, cliffordActionMatrix_entry, spinPoint_natural,
    ← changeModule_coord b f.hom]
  congr 1
  rw [Albert.SpinFunctor.vectorAction_naturality, changeModule_basis]

/-- The matrix-valued Clifford action is represented by a morphism of the actual
affine group schemes. -/
private theorem existsCliffordAction :
    ∃ f : G.val ⟶ (StandardGroups.generalLinearGroup K (Index.{u} n)).val,
      ∀ (S : CommAlgCat.{u} K) (x : ((groupPointsFunctor K).obj G.val).obj S),
        (StandardGroups.generalLinearGroupPointsIso K (Index.{u} n)).hom.app S
          (((groupPointsFunctor K).map f).app S x) = cliffordActionMatrix q b G e he S x := by
  let E := StandardGroups.generalLinearGroupPointsIso K (Index.{u} n)
  let a : (groupPointsFunctor K).obj G.val ⟶ Specs.StandardGroups.generalLinearPoints K (Index.{u} n) :=
    { app := fun S => GrpCat.ofHom (cliffordActionMatrix q b G e he S)
      naturality := by
        intro S T f
        apply GrpCat.ext
        intro x
        exact (cliffordActionMatrix_natural q b G e he f x).symm }
  obtain ⟨f, hf⟩ := (groupHomComparison K G.val _ G.prop.1).surjective (a ≫ E.inv)
  refine ⟨f, fun S x => ?_⟩
  change E.hom.app S (((groupPointsFunctor K).map f).app S x) = a.app S x
  change (groupPointsFunctor K).map f = a ≫ E.inv at hf
  rw [hf]
  exact GrpCat.hom_inv_apply (E.app S) (a.app S x)

open CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open LinearAlgebraicGroups.Specs (ClosedSubgroup IsSchemeKernel)
open Albert.SpinFunctor (schemePoints spinScheme muTwoScheme muTwoSchemePoints
  scalarSchemeInclusion scalarSchemeInclusion_points scalarSchemeInclusion_isClosedImmersion
  regularKernel vectorAction scalarEmbedding)
open Albert.SpinSpecification (muTwoPolynomial muTwoCoordinateRing)

open private affineGroupIsoOfPoints affineGroupIsoOfPoints_map
  from LinearAlgebraicGroups.Arithmetic.IntegralModels
open private schemeKernel_exists from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private kernelTorsorSquareOverRing finite_of_affine_faithfullyFlat_pullback
  from LinearAlgebraicGroups.Arithmetic.CentralCover

private theorem spinPoint_bijective (S : CommAlgCat.{u} K) :
    Function.Bijective (spinPoint q b G e he S) := by
  constructor
  · intro x y hx
    exact (he.1 S).1 (congrArg Subtype.val hx)
  · intro x
    have hx : x.val ∈ Set.range (e S) := by
      rw [(he.1 S).2]
      exact x.property
    obtain ⟨p, hp⟩ := hx
    exact ⟨p, Subtype.ext hp⟩

private def spinPointsComparison :
    (groupPointsFunctor K).obj G.val ≅ (groupPointsFunctor K).obj (spinScheme q b) :=
  NatIso.ofComponents (fun S =>
    ((MulEquiv.ofBijective _ (spinPoint_bijective q b G e he S)).trans
      (schemePoints q b S).symm).toGrpIso) (by
    intro S T a
    apply GrpCat.ext
    intro x
    apply (schemePoints q b T).injective
    change (schemePoints q b T)
      ((schemePoints q b T).symm (spinPoint q b G e he T
        (((groupPointsFunctor K).obj G.val).map a x))) =
      (schemePoints q b T) ((testSpec K).map a.op ≫
        (schemePoints q b S).symm (spinPoint q b G e he S x))
    rw [MulEquiv.apply_symm_apply, Albert.SpinFunctor.schemePoints_naturality,
      MulEquiv.apply_symm_apply, spinPoint_natural])

private def cliffordSchemeIso : G.val ≅ spinScheme q b :=
  affineGroupIsoOfPoints G.prop.1 (Albert.SpinFunctor.spinScheme_affine q b)
    (spinPointsComparison q b G e he)

private theorem cliffordSchemeIso_points
    (S : CommAlgCat.{u} K) (x : SchemePoints G.val S) :
    schemePoints q b S (x ≫ (cliffordSchemeIso q b G e he).hom.hom.hom) =
      spinPoint q b G e he S x := by
  let iso := spinPointsComparison q b G e he
  have hh := affineGroupIsoOfPoints_map G.prop.1 (Albert.SpinFunctor.spinScheme_affine q b) iso
  have hx := congrArg (fun a => a.app S x) hh
  change x ≫ (cliffordSchemeIso q b G e he).hom.hom.hom =
    (schemePoints q b S).symm (spinPoint q b G e he S x) at hx
  rw [hx, MulEquiv.apply_symm_apply]

private def spinScalarInclusion : muTwoScheme K ⟶ G.val :=
  scalarSchemeInclusion q b ≫ (cliffordSchemeIso q b G e he).inv

private theorem spinScalarInclusion_closed :
    IsClosedImmersion (spinScalarInclusion q b G e he).hom.hom.left := by
  letI : IsClosedImmersion (scalarSchemeInclusion q b).hom.hom.left :=
    scalarSchemeInclusion_isClosedImmersion q b
  let F := Grp.forget (SchemeOver K) ⋙ Over.forget _
  letI : IsIso (F.map (cliffordSchemeIso q b G e he).inv) := inferInstance
  change IsClosedImmersion
    ((scalarSchemeInclusion q b).hom.hom.left ≫ F.map (cliffordSchemeIso q b G e he).inv)
  infer_instance

private theorem spinScalarInclusion_point (S : CommAlgCat.{u} K)
    (t : SchemePoints (muTwoScheme K) S) :
    spinPoint q b G e he S (t ≫ (spinScalarInclusion q b G e he).hom.hom) =
      scalarEmbedding q S b (muTwoSchemePoints K S t) := by
  rw [← cliffordSchemeIso_points]
  change schemePoints q b S
    ((t ≫ (scalarSchemeInclusion q b).hom.hom ≫ (cliffordSchemeIso q b G e he).inv.hom.hom) ≫
      (cliffordSchemeIso q b G e he).hom.hom.hom) = _
  have hh : (cliffordSchemeIso q b G e he).inv.hom.hom ≫
      (cliffordSchemeIso q b G e he).hom.hom.hom = 𝟙 _ :=
    congrArg (fun a : spinScheme q b ⟶ spinScheme q b => a.hom.hom)
      (cliffordSchemeIso q b G e he).inv_hom_id
  simp only [Category.assoc, hh, Category.comp_id]
  exact scalarSchemeInclusion_points q b t

private theorem cliffordActionMatrix_eq_one
    (hreg : LinearMap.ker q.polarBilin = ⊥ ∨
      ∃ r : V, q r ≠ 0 ∧ LinearMap.ker q.polarBilin = K ∙ r)
    (S : CommAlgCat.{u} K) (x : SchemePoints G.val S) :
    cliffordActionMatrix q b G e he S x = 1 ↔
      ∃ t : SchemePoints (muTwoScheme K) S, t ≫ (spinScalarInclusion q b G e he).hom.hom = x := by
  let E := (LinearMap.GeneralLinearGroup.generalLinearEquiv S (S ⊗[K] V)).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (b.baseChange S)).toMulEquiv)
  change E (vectorAction q S b (spinPoint q b G e he S x)) = 1 ↔ _
  rw [← E.map_one, EmbeddingLike.apply_eq_iff_eq]
  constructor
  · intro hx
    let y : (vectorAction q S b).ker := ⟨spinPoint q b G e he S x, hx⟩
    let t := (muTwoSchemePoints K S).symm ((regularKernel q S b hreg).symm y)
    refine ⟨t, (spinPoint_bijective q b G e he S).1 ?_⟩
    rw [spinScalarInclusion_point, MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val ((regularKernel q S b hreg).apply_symm_apply y)
  · rintro ⟨t, rfl⟩
    rw [spinScalarInclusion_point]
    exact Albert.SpinFunctor.scalarEmbedding_trivial_action q S b (muTwoSchemePoints K S t)

private theorem scalarScheme_finite (K : Type u) [Field K] :
    IsFinite (muTwoScheme K).X.hom := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K (muTwoCoordinateRing K))))
  apply (IsFinite.SpecMap_iff _).mpr
  have hp : (muTwoPolynomial K).Monic := Polynomial.monic_X_pow_sub_C (1 : K) (by decide)
  exact RingHom.finite_algebraMap.mpr hp.finite_adjoinRoot

private theorem isPullbackKernelOfAffinePoints
    {H Z : LinearAlgebraicGroups.Specs.GroupScheme K}
    (f : G.val ⟶ H) (z : Z ⟶ G.val) (hH : IsAffine H.X.left) (hZ : IsAffine Z.X.left)
    (hz : IsClosedImmersion z.hom.hom.left)
    (hpoint : ∀ (S : CommAlgCat.{u} K) (x : SchemePoints G.val S),
      x ≫ f.hom.hom = 1 ↔ ∃ t : SchemePoints Z S, t ≫ z.hom.hom = x) :
    IsPullback z.hom.hom (toUnit Z.X) f.hom.hom η[H.X] := by
  letI := hH
  obtain ⟨N, hN⟩ := schemeKernel_exists f
  letI : IsAffine G.val.X.left := G.prop.1
  letI := N.isClosedImmersion
  letI : IsAffine N.group.X.left := isAffine_of_isAffineHom N.inclusion.hom.hom.left
  letI := hz
  letI : Mono z.hom.hom := Over.mono_of_mono_left _
  letI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  obtain ⟨A, ⟨a⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hZ
  have hz0 : z.hom.hom ≫ f.hom.hom = toUnit Z.X ≫ η[H.X] := by
    apply (cancel_epi a.hom).mp
    have ha := (hpoint A.unop (a.hom ≫ z.hom.hom)).2 ⟨a.hom, rfl⟩
    change (a.hom ≫ z.hom.hom) ≫ f.hom.hom = toUnit _ ≫ η[H.X] at ha
    simpa only [Category.assoc, comp_toUnit_assoc] using ha
  let p := hN.lift z.hom.hom (toUnit Z.X) hz0
  have hp : p ≫ N.inclusion.hom.hom = z.hom.hom := hN.lift_fst _ _ _
  obtain ⟨B, ⟨b⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr (show IsAffine N.group.X.left by infer_instance)
  have hb : (b.hom ≫ N.inclusion.hom.hom) ≫ f.hom.hom = 1 := by
    rw [Category.assoc, hN.w, ← Category.assoc, comp_toUnit]
    rfl
  obtain ⟨a', ha'⟩ := (hpoint B.unop (b.hom ≫ N.inclusion.hom.hom)).1 hb
  let r := b.inv ≫ a'
  have hr : r ≫ z.hom.hom = N.inclusion.hom.hom := by
    rw [Category.assoc, ha', Iso.inv_hom_id_assoc]
  have hp₁ : p ≫ r = 𝟙 _ := (cancel_mono z.hom.hom).mp
    (by rw [Category.assoc, hr, hp, Category.id_comp])
  have hr₁ : r ≫ p = 𝟙 _ := (cancel_mono N.inclusion.hom.hom).mp
    (by rw [Category.assoc, hp, hr, Category.id_comp])
  exact hN.of_iso' ⟨p, r, hp₁, hr₁⟩ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (hp.trans (Category.comp_id _).symm)
    ((comp_toUnit p).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

private theorem finite_of_finiteKernel
    {H Z : LinearAlgebraicGroups.Specs.GroupScheme K} (f : G.val ⟶ H) (z : Z ⟶ G.val)
    (hH : IsAffine H.X.left) (hZ : IsFinite Z.X.hom) (hz : IsClosedImmersion z.hom.hom.left)
    (hk : IsPullback z.hom.hom (toUnit Z.X) f.hom.hom η[H.X])
    (hflat : Flat f.hom.hom.left) (hsur : Surjective f.hom.hom.left) :
    IsFinite f.hom.hom.left := by
  letI := G.prop.1
  letI := hH
  letI := hflat
  letI := hsur
  let h := (Over.forget (Spec (CommRingCat.of K))).map_isPullback
    (kernelTorsorSquareOverRing f z hz hk)
  have hprod := Over.isPullback_of_binaryFan_isLimit
    (BinaryFan.mk (fst G.val.X Z.X) (snd G.val.X Z.X)) (tensorProductIsBinaryProduct _ _)
  have hf : IsFinite (fst G.val.X Z.X).left := MorphismProperty.of_isPullback hprod.flip hZ
  letI : IsAffine ((Over.forget (Spec (CommRingCat.of K))).obj G.val.X) := G.prop.1
  letI : IsAffine ((Over.forget (Spec (CommRingCat.of K))).obj H.X) := hH
  letI : Flat ((Over.forget (Spec (CommRingCat.of K))).map f.hom.hom) := hflat
  letI : Surjective ((Over.forget (Spec (CommRingCat.of K))).map f.hom.hom) := hsur
  exact finite_of_affine_faithfullyFlat_pullback h hf

open Specs.IntegralModels (MatrixRealization)

/-- Clifford conjugation of a regular form factors through a finite faithfully
flat morphism to its closed matrix image. Its full kernel is the scalar
square-root group scheme. -/
theorem regularSpinFiniteVectorCover
    (hreg : LinearMap.ker q.polarBilin = ⊥ ∨
      ∃ r : V, q r ≠ 0 ∧ LinearMap.ker q.polarBilin = K ∙ r) :
    ∃ (H : AffineAlgebraicGroup K)
      (f : G.val ⟶ H.val) (z : muTwoScheme K ⟶ G.val)
      (j : MatrixRealization H) (hj : j.size = n),
      IsFinite f.hom.hom.left ∧ Flat f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
      LocallyOfFinitePresentation f.hom.hom.left ∧ IsClosedImmersion z.hom.hom.left ∧
      IsPullback z.hom.hom (toUnit (muTwoScheme K).X) f.hom.hom η[H.val.X] ∧
      (∀ (S : CommAlgCat.{u} K) (t : SchemePoints (muTwoScheme K) S) (x : SchemePoints G.val S),
        (e S (t ≫ z.hom.hom)).val = algebraMap S _ (muTwoSchemePoints K S t).val.val ∧
          Commute (t ≫ z.hom.hom) x) ∧
      ∀ (S : CommAlgCat.{u} K) (x : SchemePoints G.val S),
        let m := (j.matrix.hom.app S) (((groupPointsFunctor K).map (f ≫ j.embedding)).app S x)
        Matrix.reindex (Equiv.cast (congrArg Index hj)) (Equiv.cast (congrArg Index hj)) m.val =
          (cliffordActionMatrix q b G e he S x).val := by
  let L := StandardGroups.generalLinearGroup K (Index.{u} n)
  let E := StandardGroups.generalLinearGroupPointsIso K (Index.{u} n)
  obtain ⟨a, ha⟩ := existsCliffordAction q b G e he
  obtain ⟨H, f, i, hi, _, _⟩ := schemeImageFactorization G L a
  obtain ⟨hcomp, hflat, hsur, hfp, _, hi⟩ := hi
  let z := spinScalarInclusion q b G e he
  have hz := spinScalarInclusion_closed q b G e he
  let j : MatrixRealization H := ⟨n, L, E, i, hi⟩
  letI := hi
  letI : Mono i.hom.hom := Over.mono_of_mono_left _
  have hcomp' : f.hom.hom ≫ i.hom.hom = a.hom.hom :=
    congrArg (fun p : G.val ⟶ L.val => p.hom.hom) hcomp
  have hker : IsPullback z.hom.hom (toUnit _) f.hom.hom η[H.val.X] := by
    apply isPullbackKernelOfAffinePoints G f z H.prop.1 (by
      change IsAffine (Spec (CommRingCat.of (muTwoCoordinateRing K)))
      infer_instance) hz
    intro S x
    have heq : x ≫ f.hom.hom = 1 ↔ x ≫ a.hom.hom = 1 := by
      rw [← hcomp', ← Category.assoc]
      exact ⟨fun h => by rw [h, MonObj.one_comp],
        fun h => (cancel_mono i.hom.hom).mp (h.trans (MonObj.one_comp _).symm)⟩
    rw [heq, ← cliffordActionMatrix_eq_one q b G e he hreg]
    have h := ha S x
    change E.hom.app S (x ≫ a.hom.hom) = cliffordActionMatrix q b G e he S x at h
    rw [← h, ← map_one (E.hom.app S).hom]
    exact (E.app S).groupIsoToMulEquiv.injective.eq_iff.symm
  refine ⟨H, f, z, j, rfl, finite_of_finiteKernel G f z H.prop.1 (scalarScheme_finite K)
    hz hker hflat hsur, hflat, hsur, hfp, hz, hker, ?_, ?_⟩
  · intro S t x
    have h := spinScalarInclusion_point q b G e he S t
    have ht : (e S (t ≫ z.hom.hom)).val = algebraMap S _ (muTwoSchemePoints K S t).val.val :=
      congrArg (fun a : Albert.SpinFunctor.Spin q S b => a.val.val) h
    refine ⟨ht, ?_⟩
    apply (he.1 S).1
    rw [map_mul, map_mul]
    apply Units.ext
    change (e S (t ≫ z.hom.hom)).val * (e S x).val =
      (e S x).val * (e S (t ≫ z.hom.hom)).val
    rw [ht]
    exact Algebra.commutes _ _
  · intro S x
    change (E.hom.app S (((groupPointsFunctor K).map (f ≫ i)).app S x)).val = _
    rw [hcomp, ha]

end CliffordAction

noncomputable section QuadraticCoordinates

open Albert.CliffordSpecification (coefficientForm)
open Module
open scoped TensorProduct NumberField
open AdelicLatticeBounds IsDedekindDomain

universe u

variable {K V I : Type u} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype I] [LinearOrder I] (q : QuadraticForm K V) (b : Basis I K V)

private def coordinateQuadraticPolynomial {R : Type*} [CommRing R] (a : I → I → R) :
    MvPolynomial I R :=
  ∑ i, ∑ j, MvPolynomial.C (a i j) * MvPolynomial.X i * MvPolynomial.X j

omit [LinearOrder I] in
private theorem coordinateQuadraticPolynomial_homogeneous {R : Type*} [CommRing R] (a : I → I → R) :
    (coordinateQuadraticPolynomial a).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact (MvPolynomial.isHomogeneous_C_mul_X ..).mul (MvPolynomial.isHomogeneous_X _ _)

omit [LinearOrder I] in
private theorem eval₂_coordinateQuadraticPolynomial {R S : Type*} [CommRing R] [CommRing S]
    (a : I → I → R) (f : R →+* S) (x : I → S) :
    (coordinateQuadraticPolynomial a).eval₂ f x = ∑ i, ∑ j, f (a i j) * x i * x j := by
  change MvPolynomial.eval₂Hom f x (coordinateQuadraticPolynomial a) = _
  simp only [coordinateQuadraticPolynomial, map_sum, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']

private theorem coordinateQuadraticPolynomial_eval (x : I → K) :
    (coordinateQuadraticPolynomial fun i j => q.toBilin b (b i) (b j)).eval x =
      q (b.equivFun.symm x) := by
  change (coordinateQuadraticPolynomial fun i j => q.toBilin b (b i) (b j)).eval₂ (RingHom.id K) x = _
  rw [eval₂_coordinateQuadraticPolynomial]
  let B := q.toBilin b
  have hB (y : V) : B y y = q y :=
    congrArg (fun f : QuadraticForm K V => f y) (QuadraticMap.toQuadraticMap_toBilin q b)
  rw [← hB, Basis.equivFun_symm_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    RingHom.id_apply, smul_eq_mul, Finset.mul_sum, B]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem coordinateQuadraticPolynomial_eval₂ {S : Type*} [CommRing S] [Algebra K S] (x : I → S) :
    (coordinateQuadraticPolynomial fun i j => q.toBilin b (b i) (b j)).eval₂ (algebraMap K S) x =
      coefficientForm S q b ((b.baseChange S).equivFun.symm x) := by
  rw [eval₂_coordinateQuadraticPolynomial, coefficientForm, LinearMap.BilinMap.toQuadraticMap_apply,
    Basis.equivFun_symm_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Basis.baseChange_apply, LinearMap.BilinForm.baseChange_tmul, mul_one, Algebra.smul_def,
    Algebra.algebraMap_self, RingHom.id_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem matrixAction_baseChange {S : Type*} [CommRing S] [Algebra K S]
    (m : Matrix.GeneralLinearGroup I S) (x : I → S) :
    (Matrix.GeneralLinearGroup.toLin' (b.baseChange S) m).toLinearEquiv
      ((b.baseChange S).equivFun.symm x) = (b.baseChange S).equivFun.symm (m.val.mulVec x) := by
  have h : (⇑((b.baseChange S).repr ((b.baseChange S).equivFun.symm x))) = x :=
    (b.baseChange S).equivFun.apply_symm_apply x
  rw [Matrix.GeneralLinearGroup.toLin'_apply, h, Basis.equivFun_symm_apply]
  exact Fintype.linearCombination_apply _ _ _

/-- A single nonzero normalization gives integral quadratic coefficients on
the standard lattice, with the same evaluations and invariance after scalar extension. -/
theorem existsIntegralQuadraticCoordinates [NumberField K] :
    ∃ (p : MvPolynomial I K) (a : K), a ≠ 0 ∧ p.IsHomogeneous 2 ∧
      IntegralOnReference (matrixLattice (R := 𝓞 K) (1 : Matrix.GeneralLinearGroup I K))
        (fun _ : Unit => p) ∧
      (∀ x, p.eval x = a * q (b.equivFun.symm x)) ∧
      (∀ (S : Type u) [CommRing S] [Algebra K S] (x : I → S),
        p.eval₂ (algebraMap K S) x =
          algebraMap K S a * coefficientForm S q b ((b.baseChange S).equivFun.symm x)) ∧
      (∀ (S : Type u) [CommRing S] [Algebra K S] (m : Matrix.GeneralLinearGroup I S),
        (∀ z, coefficientForm S q b ((Matrix.GeneralLinearGroup.toLin' (b.baseChange S) m).toLinearEquiv z) =
          coefficientForm S q b z) →
        ∀ x, p.eval₂ (algebraMap K S) (m.val.mulVec x) = p.eval₂ (algebraMap K S) x) := by
  classical
  let B : I × I → K := fun ij => q.toBilin b (b ij.1) (b ij.2)
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (𝓞 K)) B
  choose c hc using hd
  let p := coordinateQuadraticPolynomial (fun i j => algebraMap (𝓞 K) K (c (i,j)))
  let a := algebraMap (𝓞 K) K d.val
  have ha : a ≠ 0 := fun h => nonZeroDivisors.ne_zero d.property
    ((IsFractionRing.injective (𝓞 K) K) (h.trans (map_zero _).symm))
  have heq (i j : I) : algebraMap (𝓞 K) K (c (i,j)) = a * q.toBilin b (b i) (b j) := by
    simpa only [B, Algebra.smul_def, a] using hc (i,j)
  have heval {S : Type u} [CommRing S] [Algebra K S] (x : I → S) :
      p.eval₂ (algebraMap K S) x = algebraMap K S a *
        (coordinateQuadraticPolynomial fun i j => q.toBilin b (b i) (b j)).eval₂ (algebraMap K S) x := by
    rw [show p = coordinateQuadraticPolynomial (fun i j => algebraMap (𝓞 K) K (c (i,j))) from rfl]
    simp only [eval₂_coordinateQuadraticPolynomial, heq, map_mul, Finset.mul_sum, mul_assoc]
  have hscalar (S : Type u) [CommRing S] [Algebra K S] (x : I → S) :
      p.eval₂ (algebraMap K S) x =
        algebraMap K S a * coefficientForm S q b ((b.baseChange S).equivFun.symm x) :=
    (heval x).trans (congrArg _ (coordinateQuadraticPolynomial_eval₂ q b x))
  refine ⟨p, a, ha, coordinateQuadraticPolynomial_homogeneous _, ?_, ?_, @hscalar, ?_⟩
  · intro j w x hx
    have hx' : ∀ i, x i ∈ w.adicCompletionIntegers K := by
      have h := completedBasisLattice (R := 𝓞 K) (1 : Matrix.GeneralLinearGroup I K) w
      change x ∈ (completedLattice w (matrixLattice (R := 𝓞 K) (1 : Matrix.GeneralLinearGroup I K)) :
        Set (I → w.adicCompletion K)) at hx
      rw [h, map_one] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hyx' : y = x := by simpa using hyx
      exact hyx' ▸ hy
    rw [show p = coordinateQuadraticPolynomial (fun i j => algebraMap (𝓞 K) K (c (i,j))) from rfl,
      eval₂_coordinateQuadraticPolynomial]
    refine (w.adicCompletionIntegers K).toSubring.sum_mem fun i _ =>
      (w.adicCompletionIntegers K).toSubring.sum_mem fun j _ => ?_
    apply mul_mem (mul_mem ?_ (hx' i)) (hx' j)
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) K (w.adicCompletion K)]
    change (↑((algebraMap (𝓞 K) K) (c (i,j))) : w.adicCompletion K) ∈ w.adicCompletionIntegers K
    exact HeightOneSpectrum.coe_algebraMap_mem _ _ w (c (i,j))
  · intro x
    have h := heval (S := K) x
    rw [Algebra.algebraMap_self, RingHom.id_apply] at h
    change p.eval x = a * (coordinateQuadraticPolynomial fun i j => q.toBilin b (b i) (b j)).eval x at h
    exact h.trans (congrArg (a * ·) (coordinateQuadraticPolynomial_eval q b x))
  · intro S _ _ m hm x
    rw [hscalar, hscalar, ← matrixAction_baseChange b m x, hm]

end QuadraticCoordinates

noncomputable section TransportedLattices

open scoped NumberField
open AdelicLatticeBounds IsDedekindDomain
open private isLattice_matrixLattice coe_matrixLattice
  from LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

/-- The transported lattice is the inverse image of the completed reference lattice. -/
private theorem inverseMatrixLattice_carrier {L : Type*} [Field L]
    (O : ValuationSubring L) (m : Matrix.GeneralLinearGroup I L) :
    (matrixLattice (R := O) m⁻¹ : Set (I → L)) =
      m⁻¹.val.mulVec '' {x | ∀ i, x i ∈ O} := by
  rw [coe_matrixLattice, basisVectors]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨fun i => (z i : L), fun i => (z i).2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨fun i => ⟨z i, hz i⟩, rfl⟩

/-- The inverse images of the standard integer boxes are full local lattices.
They are unchanged off the finite set where the matrices fail integrality. -/
theorem numberTransportedLattices [NumberField K]
    (g : ∀ w : NumberFinitePlace K, Matrix.GeneralLinearGroup I (w.adicCompletion K))
    (hg : {w | g w ∉ (Matrix.GeneralLinearGroup.map (w.adicCompletionIntegers K).subtype).range}.Finite) :
    let L := matrixLattice (R := 𝓞 K) (1 : Matrix.GeneralLinearGroup I K)
    ∃ Q : ∀ w : NumberFinitePlace K,
        Submodule (w.adicCompletionIntegers K) (I → w.adicCompletion K),
      (∀ w, Submodule.IsLattice (w.adicCompletion K) (Q w)) ∧
      {w | Q w ≠ completedLattice w L}.Finite ∧
      ∀ w, (g w).val.mulVec '' (Q w : Set (I → w.adicCompletion K)) =
        (completedLattice w L : Set (I → w.adicCompletion K)) := by
  classical
  intro L
  let Q (w : NumberFinitePlace K) :=
    matrixLattice (R := w.adicCompletionIntegers K) (g w)⁻¹
  let T (w : NumberFinitePlace K) : Set (I → w.adicCompletion K) :=
    {y | ∀ i, y i ∈ w.adicCompletionIntegers K}
  have hL (w : NumberFinitePlace K) :
      (completedLattice w L : Set (I → w.adicCompletion K)) = T w := by
    dsimp only [L]
    rw [completedBasisLattice, map_one]
    change (1 : Matrix I I (w.adicCompletion K)).mulVec '' T w = T w
    simp only [Matrix.one_mulVec, Set.image_id']
  have hQ (w : NumberFinitePlace K) :
      (Q w : Set (I → w.adicCompletion K)) = (g w)⁻¹.val.mulVec '' T w :=
    inverseMatrixLattice_carrier _ _
  refine ⟨Q, fun w => isLattice_matrixLattice _, ?_, fun w => ?_⟩
  · refine hg.subset fun w hw h => ?_
    have hg' := (integralMatrixIffPreservesBox (w.adicCompletionIntegers K).toSubring (g w)⁻¹).mp
      (Subgroup.inv_mem _ h)
    apply hw
    apply SetLike.coe_injective
    exact (hQ w).trans (hg'.trans (hL w).symm)
  · rw [hQ, hL, Set.image_image]
    have hgf : (g w).val.mulVec ∘ (g w)⁻¹.val.mulVec = id := by
      funext z
      change (g w).val.mulVec ((g w)⁻¹.val.mulVec z) = z
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    change ((g w).val.mulVec ∘ (g w)⁻¹.val.mulVec) '' T w = T w
    rw [hgf, Set.image_id]

end TransportedLattices

section ScalarNorm

/-- If implementers differ by scalars and the scalar norm is the square, the
class of the norm descends through the action. The kernel is the image of the
norm-one implementers. -/
theorem squareClassOfScalarNorm {R A B : Type*} [CommRing R] [Group A] [Group B]
    (f : A →* B) (s : Rˣ →* A) (N : A →* Rˣ) (hf : Function.Surjective f)
    (hker : f.ker = s.range) (hN : ∀ t, N (s t) = t ^ 2) :
    ∃ ν : B →* Kummer.Classes R 2, (∀ a, ν (f a) = Kummer.classOf 2 (N a)) ∧
      ∀ b, ν b = 1 ↔ ∃ a : A, f a = b ∧ N a = 1 := by
  let p : A →* Kummer.Classes R 2 := (QuotientGroup.mk' _).comp N
  have h (a : A) : p a = 1 ↔ ∃ t : Rˣ, t ^ 2 = N a := by
    change (N a : Kummer.Classes R 2) = 1 ↔ _
    exact QuotientGroup.eq_one_iff _
  have hp : f.ker ≤ p.ker := by
    rw [hker]
    rintro _ ⟨t, rfl⟩
    exact (h _).2 ⟨t, (hN t).symm⟩
  let E := QuotientGroup.quotientKerEquivOfSurjective f hf
  let ν := (QuotientGroup.lift f.ker p hp).comp E.symm.toMonoidHom
  have hν (a : A) : ν (f a) = p a := by
    change QuotientGroup.lift f.ker p hp (E.symm (f a)) = p a
    rw [show f a = E (QuotientGroup.mk a) from rfl, E.symm_apply_apply]
    exact QuotientGroup.lift_mk f.ker hp a
  refine ⟨ν, hν, ?_⟩
  intro b
  obtain ⟨a, rfl⟩ := hf b
  rw [hν, h]
  constructor
  · rintro ⟨t, ht⟩
    have hs : f (s t) = 1 := MonoidHom.mem_ker.mp (hker ▸ ⟨t, rfl⟩)
    refine ⟨a * (s t)⁻¹, ?_, ?_⟩
    · rw [map_mul, map_inv, hs, inv_one, mul_one]
    · rw [map_mul, map_inv, hN, ht, mul_inv_cancel]
  · rintro ⟨a', hf', hN'⟩
    have hd : a'⁻¹ * a ∈ f.ker := by
      change f (a'⁻¹ * a) = 1
      rw [map_mul, map_inv, hf', inv_mul_cancel]
    rw [hker] at hd
    obtain ⟨t, ht⟩ := hd
    refine ⟨t, ?_⟩
    rw [← hN, ht, map_mul, map_inv, hN', inv_one, one_mul]

end ScalarNorm

private theorem polynomialSystemHasZero
    {F I J : Type*} [Field F] [Finite F]
    [Fintype I] [Fintype J] [Nonempty J]
    (hsize : 4 * Fintype.card J < Fintype.card I) (a : J → I → I → F[X]) :
    ∃ z : I → F[X], z ≠ 0 ∧ ∀ j, ∑ i, ∑ k, a j i k * z i * z k = 0 := by
  classical
  letI := Fintype.ofFinite F
  let d := Finset.univ.sup (fun p : J × I × I => (a p.1 p.2.1 p.2.2).natDegree)
  let N := 2 * Fintype.card J * (d + 1)
  let L := d + N + N + 1
  let U := I × Fin (N + 1)
  let W := J × Fin L
  let P (j : W) : MvPolynomial U F :=
    ∑ i : I, ∑ k : I, ∑ s : Fin (N + 1), ∑ t : Fin (N + 1),
      MvPolynomial.C (if s.val + t.val ≤ j.2.val then
        (a j.1 i k).coeff (j.2.val - (s.val + t.val)) else 0) *
        MvPolynomial.X (i,s) * MvPolynomial.X (k,t)
  have hhom (j : W) : (P j).IsHomogeneous 2 := by
    unfold P
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun _ _ => ?_
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun _ _ => ?_
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun _ _ => ?_
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun _ _ => ?_
    exact (MvPolynomial.isHomogeneous_C_mul_X ..).mul (MvPolynomial.isHomogeneous_X _ _)
  have hcount : (∑ j : W, (P j).totalDegree) < Fintype.card U := by
    calc
      _ ≤ ∑ _ : W, 2 := Finset.sum_le_sum fun j _ => (hhom j).totalDegree_le
      _ < _ := by
        have hI : 4 * Fintype.card J + 1 ≤ Fintype.card I := by omega
        have hN : 2 * Fintype.card J * (d + 1) < N + 1 := Nat.lt_succ_self N
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
          Fintype.card_fin, U, W]
        calc
          Fintype.card J * L * 2
              = (4 * Fintype.card J) * N + 2 * Fintype.card J * (d + 1) := by dsimp [L]; ring
          _ < (4 * Fintype.card J) * (N + 1) + (N + 1) := by nlinarith
          _ = (4 * Fintype.card J + 1) * (N + 1) := by ring
          _ ≤ Fintype.card I * (N + 1) := Nat.mul_le_mul_right _ hI
  let p := ringChar F
  have hp : p.Prime := CharP.char_is_prime F p
  have hdiv := char_dvd_card_solutions_of_fintype_sum_lt p hcount
  have hzero : ∀ j : W, (P j).eval (0 : U → F) = 0 := by
    intro j
    simp [P]
  obtain ⟨x, hpp, hx⟩ : ∃ x : U → F, (∀ j : W, (P j).eval x = 0) ∧ x ≠ 0 := by
    by_contra! hnone
    let Z := {x : U → F // ∀ j : W, (P j).eval x = 0}
    haveI : Unique Z := ⟨⟨⟨0,hzero⟩⟩, fun x => Subtype.ext (hnone x.val x.property)⟩
    change p ∣ Fintype.card Z at hdiv
    rw [Fintype.card_unique] at hdiv
    exact hp.not_dvd_one hdiv
  let z (i : I) : F[X] := ∑ s : Fin (N + 1), monomial s.val (x (i,s))
  have hz (i : I) (s : Fin (N + 1)) : (z i).coeff s.val = x (i,s) := by
    simp [z, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Fin.val_inj]
  have hdeg (i : I) : (z i).natDegree ≤ N := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro s _
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp s.isLt)
  have hcoeff (j : J) (l : Fin L) :
      (∑ i : I, ∑ k : I, a j i k * z i * z k).coeff l.val = (P (j,l)).eval x := by
    simp only [P, map_sum, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X, z, Finset.mul_sum, Finset.sum_mul,
      Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro t _
    rw [mul_assoc, Polynomial.monomial_mul_monomial]
    rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.X_pow_mul, ← mul_assoc,
      Polynomial.coeff_mul_C, Polynomial.coeff_mul_X_pow']
    by_cases h : s.val + t.val ≤ l.val
    · simp only [ite_eq_left h, mul_assoc]
    · simp [h]
  refine ⟨z, ?_, fun j => ?_⟩
  · intro h
    apply hx
    funext s
    simpa [h] using (hz s.1 s.2).symm
  · apply Polynomial.ext
    intro l
    by_cases hl : l < L
    · rw [hcoeff j ⟨l,hl⟩, hpp, Polynomial.coeff_zero]
    · have hd : (∑ i : I, ∑ k : I, a j i k * z i * z k).natDegree ≤ d + N + N := by
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro i _
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro k _
        have ha : (a j i k).natDegree ≤ d :=
          Finset.le_sup (f := fun p : J × I × I => (a p.1 p.2.1 p.2.2).natDegree)
            (b := (j,i,k)) (Finset.mem_univ _)
        calc
          (a j i k * z i * z k).natDegree ≤ (a j i k * z i).natDegree + (z k).natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ ((a j i k).natDegree + (z i).natDegree) + (z k).natDegree :=
            Nat.add_le_add_right Polynomial.natDegree_mul_le _
          _ ≤ d + N + N := Nat.add_le_add (Nat.add_le_add ha (hdeg i)) (hdeg k)
      have hL : d + N + N < l := Nat.lt_of_succ_le (Nat.le_of_not_gt hl)
      rw [Polynomial.coeff_zero]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt hL)


/-- The coefficient-counting argument for a finite extension of a rational
function field. It applies to quadratic forms with degenerate polar form. -/
private theorem functionFieldIsotropic
    {F K V : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] {I : Type*} [Fintype I]
    (t : SeparatingParameter F K) (q : QuadraticForm K V)
    (b : Module.Basis I K V) (hsize : 4 < Fintype.card I) :
    ∃ x : V, x ≠ 0 ∧ q x = 0 := by
  classical
  let R := F⟮X⟯
  let T := IntermediateField.adjoin F {t.element}
  let e := RatFunc.algEquivOfTranscendental t.element t.transcendental
  letI : Algebra R T := e.toRingHom.toAlgebra
  letI : Algebra R K := t.rationalAlgebra
  letI : IsScalarTower R T K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module.Finite T K := t.finite
  letI : Module.Finite R T := RingHom.finite_algebraMap.mp
    (RingHom.Finite.of_surjective e.toRingHom e.surjective)
  letI : Module.Finite R K := Module.Finite.trans (R := R) T K
  letI : Module R V := Module.compHom V (algebraMap R K)
  letI : IsScalarTower R K V := IsScalarTower.of_compHom R K V
  letI : Module.Finite K V := Module.Finite.of_basis b
  letI : Module.Finite R V := Module.Finite.trans (R := R) K V
  let J := Fin (Module.finrank R K)
  let A := Fin (Module.finrank R V)
  have hJ : Nonempty J := Fin.pos_iff_nonempty.mp (Module.finrank_pos (R := R) (M := K))
  let v := Module.finBasis R V
  let c := Module.finBasis R K
  have hA : 4 * Fintype.card J < Fintype.card A := by
    simp only [J, A, Fintype.card_fin, ← Module.finrank_mul_finrank R K V, Module.finrank_eq_card_basis b]
    rw [mul_comm 4]
    exact Nat.mul_lt_mul_of_pos_left hsize (Module.finrank_pos (R := R) (M := K))
  let B := (q.restrictScalars (S := R)).toBilin v
  let f (p : J × A × A) : R := c.repr (B (v p.2.1) (v p.2.2)) p.1
  obtain ⟨denom, hdenom⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors F[X]) f
  choose a ha using hdenom
  obtain ⟨z, hz, hsys⟩ := polynomialSystemHasZero hA (fun j i k => a (j,i,k))
  let zR (i : A) := algebraMap F[X] R (z i)
  let x := v.equivFun.symm zR
  refine ⟨x, ?_, ?_⟩
  · intro h
    apply hz
    have he : zR = 0 := v.equivFun.symm.injective (h.trans (map_zero _).symm)
    funext i
    apply IsFractionRing.injective F[X] R
    simpa [zR] using congrFun he i
  · have hrepr (j : J) :
        c.repr (q x) j = ∑ i : A, ∑ k : A, f (j,i,k) * zR i * zR k := by
      have hq : B x x = q x := by
        exact congrArg (fun q' : QuadraticMap R V K => q' x)
          (QuadraticMap.toQuadraticMap_toBilin (q.restrictScalars (S := R)) v)
      rw [← hq]
      change c.repr (B (v.equivFun.symm zR) (v.equivFun.symm zR)) j = _
      simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, LinearMap.sum_apply,
        LinearMap.smul_apply, Finset.smul_sum, Finsupp.finsetSum_apply, Finsupp.smul_apply,
        smul_eq_mul, f]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    apply c.repr.injective
    ext j
    simp only [map_zero, Finsupp.zero_apply]
    have h := congrArg (algebraMap F[X] R) (hsys j)
    have hden : algebraMap F[X] R (denom : F[X]) ≠ 0 := by
      exact fun h => nonZeroDivisors.ne_zero denom.property
        (IsFractionRing.injective F[X] R (h.trans (map_zero _).symm))
    apply (mul_eq_zero.mp ?_).resolve_left hden
    change algebraMap F[X] R (denom : F[X]) * c.repr (q x) j = 0
    rw [hrepr j, Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    simpa only [map_sum, map_mul, ha, Algebra.smul_def, zR, map_zero, mul_assoc] using h

/-- The function-field case follows from the dimension bound for anisotropic
quadratic forms over finite extensions of a rational function field. -/
theorem functionFieldSpinCompactness.{u,v} : FunctionFieldSpinCompactness.{u,v} := by
  intro K _ F _ _ _ t V _ _ q r hregular hanisotropic n b hsize
  have hcard : 4 < Fintype.card (Specs.Unipotent.Index.{u} n) := by
    simpa using (show 4 < n by omega)
  obtain ⟨x, hx, hq⟩ := functionFieldIsotropic t q b hcard
  exact (hx (hanisotropic x hq)).elim

noncomputable section SpinorNormComparison

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.Unipotent (Index)
open Specs.Arithmetic.LocalQuadraticIsotropy
open Specs.DivisionOctonionOrthogonalTensors (matrixCoordinates)
open Albert.CliffordSpecification (coefficientForm)
open Albert.SpinSpecification (IsSpinPointRepresentation SchemePoints ScalarClifford
  IsVectorAction vectors conjugate spinUnits reversion)
open Albert.SpinFunctor (vectorAction vectorAction_characterization vectorAction_preserves)
open scoped TensorProduct CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false

open CliffordAlgebra Matrix Matrix.GeneralLinearGroup
open private cliffordEquiv cliffordEquiv_even cliffordEquiv_vector scalar_injective
  conjugate_inverse vectors_injective from LinearAlgebraicGroups.Albert.SpinFunctor
open private baseChangeEquiv_reverse from LinearAlgebraicGroups.Albert.CliffordModel
open private cliffordWord cliffordWord_action cliffordWord_grade reflectionWord_det
  reflectionWordLinear reflectionWordLinear_apply hasSpinLift_iff_intrinsic
  from LinearAlgebraicGroups.Arithmetic.LocalQuadraticIsotropy

universe u v

/-- An even Clifford implementer in characteristic zero has an oriented
vector action. Compare with a reflection word using the graded centralizer. -/
private theorem det_of_even_implementer {F W I : Type*} [Field F] [CharZero F]
    [AddCommGroup W] [Module F W] [Fintype I] [LinearOrder I]
    (Q : QuadraticForm F W) (b : Module.Basis I F W)
    (hQ : LinearMap.ker Q.polarBilin = ⊥) (g : W ≃ₗ[F] W)
    (hg : ∀ x, Q (g x) = Q x) (a : (CliffordAlgebra Q)ˣ)
    (ha : a.val ∈ evenOdd Q 0)
    (hact : ∀ x, a.val * CliffordAlgebra.ι Q x = CliffordAlgebra.ι Q (g x) * a.val) :
    g.det = 1 := by
  classical
  letI : FiniteDimensional F W := Module.Finite.of_basis b
  obtain ⟨l, hl, hw⟩ := SpinOrthogonalWords.orthogonalWords Q (Or.inl hQ) g hg
  let m : List (ReflectionVector Q) := l.attach.map fun w => ⟨w.val, hl w.val w.prop⟩
  have hg' (x : W) : g x = reflectionWord Q m x := by
    rw [hw]
    simp [m, reflectionWord, List.foldr_map, Specs.Arithmetic.IsotropicSpinGeneration.reflection]
  let d := cliffordWord Q m
  have hd (x : W) : d.val * CliffordAlgebra.ι Q x = CliffordAlgebra.ι Q (g x) * involute d.val := by
    rw [hg']
    exact cliffordWord_action Q m x
  have hae : involute a.val = a.val := involute_eq_of_mem_even ha
  have hai : involute a⁻¹.val = a⁻¹.val := by
    have h : Units.map (involute (Q := Q)).toMonoidHom a = a := Units.ext hae
    exact congrArg Units.val ((map_inv (Units.map (involute (Q := Q)).toMonoidHom) a).trans
      (congrArg Inv.inv h))
  let c := a⁻¹.val * d.val
  have hc (x : W) : CliffordAlgebra.ι Q x * c = involute c * CliffordAlgebra.ι Q x := by
    have hx : CliffordAlgebra.ι Q x * a⁻¹.val = a⁻¹.val * CliffordAlgebra.ι Q (g x) := by
      calc
        _ = a⁻¹.val * (a.val * CliffordAlgebra.ι Q x) * a⁻¹.val := by
          rw [← mul_assoc a⁻¹.val, Units.inv_mul, one_mul]
        _ = _ := by rw [hact, mul_assoc a⁻¹.val, mul_assoc (CliffordAlgebra.ι Q (g x)), Units.mul_inv, mul_one]
    have htwist : involute d.val * CliffordAlgebra.ι Q x = CliffordAlgebra.ι Q (g x) * d.val := by
      simpa only [map_mul, involute_ι, involute_involute, mul_neg, neg_mul, neg_inj]
        using congrArg (involute (Q := Q)) (hd x)
    change CliffordAlgebra.ι Q x * (a⁻¹.val * d.val) = involute (a⁻¹.val * d.val) * CliffordAlgebra.ι Q x
    rw [← mul_assoc, hx, mul_assoc, ← htwist, map_mul, hai, mul_assoc]
  obtain ⟨r, hr⟩ := IsotropicSpinGeneration.gradedCentralizerCalculation Q b hQ c hc
  have hd' : d.val = a.val * algebraMap F _ r := by
    rw [← hr]
    change _ = a.val * (a⁻¹.val * d.val)
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have h₀ : d.val ∈ evenOdd Q 0 := by
    rw [hd', ← Algebra.commutes, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ ha
  letI : Nontrivial (CliffordAlgebra Q) := Function.Injective.nontrivial (scalar_injective Q b)
  have hlen : (m.length : ZMod 2) = 0 :=
    DirectSum.degree_eq_of_mem_mem (evenOdd Q) (cliffordWord_grade Q m) h₀ d.ne_zero
  have hpar : Even m.length := even_iff_two_dvd.mpr ((ZMod.natCast_eq_zero_iff _ _).mp hlen)
  have heq : reflectionWordLinear Q m = g.toLinearMap :=
    LinearMap.ext fun x => (reflectionWordLinear_apply Q m x).trans (hg' x).symm
  have hdet := reflectionWord_det Q m (by norm_num : (2 : F) ≠ 0)
  rw [heq, ← LinearEquiv.coe_det, hpar.neg_one_pow] at hdet
  exact Units.ext hdet

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
variable {n : ℕ} (q : QuadraticForm K V) (b : Module.Basis (Index.{u} n) K V)
variable {G : AffineAlgebraicGroup K}
variable (e : ∀ S : CommAlgCat.{u} K, SchemePoints G.val S →* (ScalarClifford q S)ˣ)
variable (he : IsSpinPointRepresentation q G.val e)

private theorem cliffordActionMatrix_eq_coordinates (S : CommAlgCat.{u} K)
    (x : ((groupPointsFunctor K).obj G.val).obj S) :
    cliffordActionMatrix q b G e he S x =
      matrixCoordinates (b.baseChange S) (vectorAction q S b (spinPoint q b G e he S x)) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  let g := vectorAction q S b (spinPoint q b G e he S x)
  let c := b.baseChange S
  calc
    _ = c.coord i (g (c j)) := cliffordActionMatrix_entry q b G e he S x i j
    _ = (LinearMap.toMatrix c c g.toLinearMap) i j := (LinearMap.toMatrix_apply c c g.toLinearMap i j).symm
    _ = _ := rfl

variable (L : Type u) [Field L] [Algebra K L]

/-- The intrinsic spin points and the Clifford implementers used to compute
the spinor norm have identical actions on the coefficient-extended space. -/
private theorem vectorAction_exists_iff
    (g : (L ⊗[K] V) ≃ₗ[L] (L ⊗[K] V)) :
    (∃ a : Albert.SpinFunctor.Spin q L b, vectorAction q L b a = g) ↔
      ∃ a : (CliffordAlgebra (coefficientForm L q b))ˣ,
        a.val ∈ evenOdd (coefficientForm L q b) 0 ∧ reverse a.val * a.val = 1 ∧
        ∀ x, a.val * CliffordAlgebra.ι _ x = CliffordAlgebra.ι _ (g x) * a.val := by
  let E := cliffordEquiv q L b
  have hrev (a : ScalarClifford q L) : E (reversion q L a) = reverse (E a) :=
    baseChangeEquiv_reverse L q b a
  have hvec (x : L ⊗[K] V) : E (vectors q L x) = CliffordAlgebra.ι _ x := cliffordEquiv_vector q L b x
  constructor
  · rintro ⟨a, rfl⟩
    let z := Units.map E.toMonoidHom a.val
    have hn := congrArg E a.property.2.1
    rw [map_mul, map_one, hrev] at hn
    refine ⟨z, (cliffordEquiv_even q L b _).mpr a.property.1, hn, ?_⟩
    intro x
    have h := congrArg E (vectorAction_characterization q L b a x)
    rw [hvec, conjugate, map_mul, map_mul, hvec] at h
    change CliffordAlgebra.ι _ (vectorAction q L b a x) = z.val * CliffordAlgebra.ι _ x * z⁻¹.val at h
    rw [h, mul_assoc, Units.inv_mul, mul_one]
  · rintro ⟨z, hgrade, hnorm, hact⟩
    let a := Units.map E.symm.toMonoidHom z
    have hz : E a.val = z.val := E.apply_symm_apply _
    have hzi : E a⁻¹.val = z⁻¹.val := E.apply_symm_apply _
    have h : IsVectorAction q L a g := by
      intro y
      apply E.injective
      rw [hvec, conjugate, map_mul, map_mul, hvec, hz, hzi, hact, mul_assoc, Units.mul_inv, mul_one]
    have ha : a ∈ spinUnits q L := by
      refine ⟨(cliffordEquiv_even q L b _).mp (hz.symm ▸ hgrade), ?_, ?_, ?_⟩
      · apply E.injective
        rw [map_mul, map_one, hrev, hz, hnorm]
      · rintro _ ⟨x, rfl⟩
        exact ⟨g x, h x⟩
      · rintro _ ⟨x, rfl⟩
        refine ⟨g.symm x, ?_⟩
        rw [← conjugate_inverse q L a⁻¹ (vectors q L (g.symm x)), inv_inv,
          ← h (g.symm x), LinearEquiv.apply_symm_apply]
    refine ⟨⟨a, ha⟩, ?_⟩
    ext x
    exact (vectors_injective q L b)
      ((vectorAction_characterization q L b ⟨a, ha⟩ x).trans (h x).symm)

private theorem spin_matrix_is_specialOrthogonal [CharZero L]
    (hQ : LinearMap.ker (coefficientForm L q b).polarBilin = ⊥)
    (a : Albert.SpinFunctor.Spin q L b) :
    vectorAction q L b a ∈ specialOrthogonal (coefficientForm L q b) := by
  let g := vectorAction q L b a
  have hg := vectorAction_preserves q L b a
  obtain ⟨z, hgrade, _, hact⟩ := (vectorAction_exists_iff q b L g).mp ⟨a, rfl⟩
  exact ⟨hg, det_of_even_implementer _ (b.baseChange L) hQ g hg z hgrade hact⟩

end SpinorNormComparison

noncomputable section FieldPoints

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.Unipotent (Index)
open Specs.IntegralModels (MatrixRealization)
open Specs.Arithmetic.LocalQuadraticIsotropy
open Specs.DivisionOctonionOrthogonalTensors (matrixCoordinates)
open Albert.CliffordSpecification (coefficientForm)
open Albert.SpinSpecification (IsSpinPointRepresentation SchemePoints ScalarClifford)
open Albert.SpinFunctor (vectorAction)
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory Opposite Matrix Matrix.GeneralLinearGroup

open private changeModule changeModule_smul changeModule_basis changeModule_coord polar_baseChange_tmul
  from LinearAlgebraicGroups.Albert.SpinFunctor
open private polarRadical_eq from LinearAlgebraicGroups.Arithmetic.SpinScalarExtension
open private lift_of_range from LinearAlgebraicGroups.Flag.BruhatCells
open private hasSpinLift_iff_intrinsic from LinearAlgebraicGroups.Arithmetic.LocalQuadraticIsotropy

universe u

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
variable {I : Type*} [Fintype I] [LinearOrder I] [DecidableEq I]
variable (q : QuadraticForm K V) (b : Module.Basis I K V)
variable {L E : Type u} [Field L] [Field E] [Algebra K L] [Algebra K E]

/-- Scalar extension of the closed matrix realization commutes with its
point matrices over arbitrary test fields. -/
private theorem asMatrix_natural {H : AffineAlgebraicGroup K} (j : MatrixRealization H)
    (φ : L →ₐ[K] E) (x : PointsIn j L) :
    asMatrix j E (((groupPointsFunctor K).obj H.val).map (CommAlgCat.ofHom φ) x) =
      map φ.toRingHom (asMatrix j L x) := by
  let α := (groupPointsFunctor K).map j.embedding ≫ j.matrix.hom
  exact congrArg (fun h => h x) (α.naturality (CommAlgCat.ofHom φ))

private theorem asMatrix_injective {H : AffineAlgebraicGroup K} (j : MatrixRealization H) :
    Function.Injective (asMatrix j L) := by
  letI := j.closed
  letI : Mono j.embedding.hom.hom := Over.mono_of_mono_left _
  intro x y h
  have h' : x ≫ j.embedding.hom.hom = y ≫ j.embedding.hom.hom :=
    (j.matrix.app (CommAlgCat.of K L)).groupIsoToMulEquiv.injective h
  exact (cancel_mono j.embedding.hom.hom).mp h'

/-- Closed equations descend from an extension field of the point field. -/
private theorem matrixRange_descends {H : AffineAlgebraicGroup K} (j : MatrixRealization H)
    (φ : L →ₐ[K] E) (m : GL (Index.{u} j.size) L) (y : PointsIn j E)
    (hy : asMatrix j E y = map φ.toRingHom m) :
    m ∈ (asMatrix j L).range := by
  let S := CommAlgCat.of K L
  let T := CommAlgCat.of K E
  let p : SchemePoints j.ambient.val S := j.matrix.inv.app S m
  let t := (testSpec K).map (CommAlgCat.ofHom φ).op
  let j₀ := j.embedding.hom.hom
  have hp : t ≫ p = y ≫ j₀ := by
    apply (j.matrix.app T).groupIsoToMulEquiv.injective
    have hn := congrArg (fun z => z m) (j.matrix.inv.naturality (CommAlgCat.ofHom φ))
    change (j.matrix.hom.app T) (t ≫ p) = ((asMatrix j E) y)
    rw [show t ≫ p = j.matrix.inv.app T (map φ.toRingHom m) from hn.symm, hy]
    exact GrpCat.hom_inv_apply (j.matrix.app T) _
  have ht : t.left.ker = ⊥ := by
    let t₀ : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of L) := t.left
    haveI : Surjective t₀ := ⟨fun x => ⟨IsLocalRing.closedPoint E, Subsingleton.elim _ _⟩⟩
    exact (IsSchemeTheoreticallyDominant.of_isDominant t₀).ker_eq_bot
  have hker : j₀.left.ker ≤ p.left.ker := by
    have h := y.left.le_ker_comp j₀.left
    have ht' : t.left ≫ p.left = y.left ≫ j₀.left := congrArg Over.Hom.left hp
    rw [← ht', Scheme.Hom.ker_comp, ht, Scheme.IdealSheafData.map_bot] at h
    exact h
  letI : IsClosedImmersion j₀.left := j.closed
  let g := IsClosedImmersion.lift j₀.left p.left hker
  have hg : g ≫ j₀.left = p.left := IsClosedImmersion.lift_fac _ _ _
  let x : PointsIn j L := Over.homMk g (by
    change g ≫ H.val.X.hom = ((testSpec K).obj (op S)).hom
    rw [← Over.w j₀, ← Category.assoc, hg]
    exact Over.w p)
  have hx : x ≫ j₀ = p := Over.OverMorphism.ext hg
  refine ⟨x, ?_⟩
  change (j.matrix.hom.app S) (x ≫ j₀) = m
  rw [hx]
  exact GrpCat.hom_inv_apply (j.matrix.app S) _

omit [Fintype I] [DecidableEq I] in
private theorem coefficientForm_natural (φ : L →ₐ[K] E) (x : L ⊗[K] V) :
    coefficientForm E q b (changeModule φ x) = φ (coefficientForm L q b x) := by
  let P := q.toBilin b
  suffices hp : ∀ x y : L ⊗[K] V,
      (LinearMap.BilinForm.baseChange E P) (changeModule φ x) (changeModule φ y) = φ ((LinearMap.BilinForm.baseChange L P) x y) by
    exact hp x x
  intro x y
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp [hx, hz]
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp [hy, hz]
    | tmul c y =>
      simp [changeModule, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def, AlgHom.commutes]

omit [LinearOrder I] in
private theorem matrixAction_natural (φ : L →ₐ[K] E) (m : GL I L) (x : L ⊗[K] V) :
    (matrixCoordinates (b.baseChange E)).symm (map φ.toRingHom m) (changeModule φ x) =
      changeModule φ ((matrixCoordinates (b.baseChange L)).symm m x) := by
  let g := (matrixCoordinates (b.baseChange L)).symm m
  let h := (matrixCoordinates (b.baseChange E)).symm (map φ.toRingHom m)
  apply (b.baseChange E).equivFun.injective
  funext i
  change (b.baseChange E).coord i (h (changeModule φ x)) =
    (b.baseChange E).coord i (changeModule φ (g x))
  rw [changeModule_coord]
  have h₁ := congrFun (LinearAlgebraicGroups.Arithmetic.DivisionOctonionOrthogonalTensors.matrixCoordinateComparison (b.baseChange L) g x).1 i
  have h₂ := congrFun (LinearAlgebraicGroups.Arithmetic.DivisionOctonionOrthogonalTensors.matrixCoordinateComparison (b.baseChange E) h (changeModule φ x)).1 i
  rw [show matrixCoordinates (b.baseChange L) g = m from MulEquiv.apply_symm_apply _ _] at h₁
  rw [show matrixCoordinates (b.baseChange E) h = map φ.toRingHom m
    from MulEquiv.apply_symm_apply _ _] at h₂
  change _ = (b.baseChange E).coord i (h (changeModule φ x)) at h₂
  change _ = (b.baseChange L).coord i (g x) at h₁
  rw [← h₂, ← h₁]
  simp only [Matrix.mulVec, dotProduct, Matrix.GeneralLinearGroup.map_apply, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro j _
  change φ (m.val i j) * (b.baseChange E).coord j (changeModule φ x) =
    φ (m.val i j) * φ ((b.baseChange L).coord j x)
  rw [changeModule_coord]

private def IsSpecialOrthogonalMatrix (m : GL I L) : Prop :=
  (matrixCoordinates (b.baseChange L)).symm m ∈ specialOrthogonal (coefficientForm L q b)

private theorem matrixCoordinates_det {R W J : Type*} [CommRing R] [AddCommGroup W]
    [Module R W] [Fintype J] [DecidableEq J] (c : Module.Basis J R W) (g : W ≃ₗ[R] W) :
    (matrixCoordinates c g).det = g.det := by
  apply Units.ext
  change (LinearMap.toMatrix c c g.toLinearMap).det = _
  rw [LinearMap.det_toMatrix c, LinearEquiv.coe_det]

private theorem isSpecialOrthogonalMatrix_map_iff [CharZero E] (φ : L →ₐ[K] E) (m : GL I L) :
    IsSpecialOrthogonalMatrix q b (map φ.toRingHom m) ↔ IsSpecialOrthogonalMatrix q b m := by
  let g := (matrixCoordinates (b.baseChange L)).symm m
  let h := (matrixCoordinates (b.baseChange E)).symm (map φ.toRingHom m)
  have hg : g.det = m.det := (matrixCoordinates_det (b.baseChange L) g).symm.trans
    (congrArg _ (MulEquiv.apply_symm_apply (matrixCoordinates (b.baseChange L)) m))
  have hh : h.det = (map φ.toRingHom m).det :=
    (matrixCoordinates_det (b.baseChange E) h).symm.trans
      (congrArg _ (MulEquiv.apply_symm_apply (matrixCoordinates (b.baseChange E)) _))
  change ((∀ x, coefficientForm E q b (h x) = coefficientForm E q b x) ∧ h.det = 1) ↔
    ((∀ x, coefficientForm L q b (g x) = coefficientForm L q b x) ∧ g.det = 1)
  have hdet : (map φ.toRingHom m).det = 1 ↔ m.det = 1 := by
    rw [Matrix.GeneralLinearGroup.map_det]
    constructor
    · intro h
      apply Units.ext
      apply φ.injective
      have hh := congrArg (fun z : Eˣ => z.val) h
      change φ.toRingHom (m.det : L) = 1 at hh
      exact hh.trans (φ.toRingHom.map_one).symm
    · intro h
      rw [h, map_one]
  rw [hg, hh, hdet]
  constructor
  · rintro ⟨hiso, hdet⟩
    refine ⟨fun x => φ.injective ?_, hdet⟩
    have he := hiso (changeModule φ x)
    change coefficientForm E q b
      ((matrixCoordinates (b.baseChange E)).symm (map φ.toRingHom m) (changeModule φ x)) =
        coefficientForm E q b (changeModule φ x) at he
    rw [matrixAction_natural b φ, coefficientForm_natural, coefficientForm_natural] at he
    exact he
  · rintro ⟨hiso, hdet⟩
    refine ⟨?_, hdet⟩
    change (∀ x, (coefficientForm E q b).comp h.toLinearMap x = coefficientForm E q b x)
    have hc (i : I) : changeModule φ (b.baseChange L i) = b.baseChange E i :=
      changeModule_basis b φ i
    have he (x : L ⊗[K] V) :
        (coefficientForm E q b).comp h.toLinearMap (changeModule φ x) =
          coefficientForm E q b (changeModule φ x) := by
      change coefficientForm E q b (h (changeModule φ x)) = _
      rw [show h (changeModule φ x) = changeModule φ (g x) from matrixAction_natural b φ m x,
        coefficientForm_natural, coefficientForm_natural, hiso]
    have hpol (i j : I) :
        ((coefficientForm E q b).comp h.toLinearMap).polarBilin
          (b.baseChange E i) (b.baseChange E j) =
        (coefficientForm E q b).polarBilin (b.baseChange E i) (b.baseChange E j) := by
      rw [← hc i, ← hc j]
      simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, he]
    have heq : ((coefficientForm E q b).comp h.toLinearMap).polarBilin =
        (coefficientForm E q b).polarBilin := by
      apply (b.baseChange E).ext
      intro i
      apply (b.baseChange E).ext
      intro j
      exact hpol i j
    intro x
    have h₂ : (2 : E) ≠ 0 := by norm_num
    have hp := LinearMap.congr_fun (LinearMap.congr_fun heq x) x
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul] at hp
    exact mul_left_cancel₀ h₂ hp

omit [Fintype I] [DecidableEq I] in
private theorem coefficientForm_ker [Module.Finite K V]
    (hq : LinearMap.ker q.polarBilin = ⊥) :
    LinearMap.ker (coefficientForm L q b).polarBilin = ⊥ := by
  rw [polarRadical_eq q b, hq, Submodule.baseChange_bot]

variable {G H : AffineAlgebraicGroup K} (i : MatrixRealization G) (j : MatrixRealization H)
variable (b' : Module.Basis (Index.{u} j.size) K V)
variable (e : ∀ S : CommAlgCat.{u} K, SchemePoints G.val S →* (ScalarClifford q S)ˣ)
variable (he : IsSpinPointRepresentation q G.val e)
variable (f : G.val ⟶ H.val)
variable (hmat : ∀ (S : CommAlgCat.{u} K) (x : SchemePoints G.val S),
  asMatrix j S (pointMap f i j S x) = cliffordActionMatrix q b' G e he S x)

set_option backward.isDefEq.respectTransparency false in
include hmat in
private theorem vectorAction_lift_iff (x : PointsIn j L)
    (hx : IsSpecialOrthogonalMatrix q b' (asMatrix j L x)) :
    HasSpinLift (coefficientForm L q b')
      ⟨(matrixCoordinates (b'.baseChange L)).symm (asMatrix j L x), hx⟩ ↔
        x ∈ (pointMap f i j L).range := by
  let S := CommAlgCat.of K L
  let g : specialOrthogonal (coefficientForm L q b') :=
    ⟨(matrixCoordinates (b'.baseChange L)).symm (asMatrix j L x), hx⟩
  change HasSpinLift _ g ↔ ∃ s : PointsIn i L, pointMap f i j L s = x
  rw [hasSpinLift_iff_intrinsic, ← vectorAction_exists_iff q b' L g.val]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨s, hs⟩ := (spinPoint_bijective q b' G e he S).surjective a
    refine ⟨s, (asMatrix_injective j) ?_⟩
    change asMatrix j S (pointMap f i j S s) = asMatrix j L x
    rw [hmat S s, cliffordActionMatrix_eq_coordinates q b' e he S s, hs, ha]
    exact MulEquiv.apply_symm_apply _ _
  · rintro ⟨s, rfl⟩
    refine ⟨spinPoint q b' G e he S s, (matrixCoordinates (b'.baseChange L)).injective ?_⟩
    have hm := (hmat S s).trans (cliffordActionMatrix_eq_coordinates q b' e he S s)
    exact hm.symm.trans (MulEquiv.apply_symm_apply _ _).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2400 in
set_option maxHeartbeats 2000000 in
include hmat in
/-- At field-valued points the finite vector image is the full special
orthogonal group. Geometric spin lifts suffice for the closed image. -/
private theorem vectorCover_image [CharZero K] [CharZero L]
    (hq : LinearMap.ker q.polarBilin = ⊥)
    (hfinite : IsFinite f.hom.hom.left) (hsurj : Surjective f.hom.hom.left)
    (m : GL (Index.{u} j.size) L) :
    m ∈ (asMatrix j L).range ↔ IsSpecialOrthogonalMatrix q b' m := by
  let E := AlgebraicClosure L
  letI : Algebra K E := ((algebraMap L E).comp (algebraMap K L)).toAlgebra
  let φ : L →ₐ[K] E := ⟨algebraMap L E, fun _ => rfl⟩
  let a := CommAlgCat.ofHom φ
  let T := CommAlgCat.of K E
  letI : Module.Finite K V := Module.Finite.of_basis b'
  letI : FiniteDimensional E (E ⊗[K] V) := Module.Finite.of_basis (b'.baseChange E)
  have hQ := coefficientForm_ker (L := E) q b' hq
  have hsol (s : ((groupPointsFunctor K).obj G.val).obj T) :
      IsSpecialOrthogonalMatrix q b' (asMatrix j E (pointMap f i j E s)) := by
    change IsSpecialOrthogonalMatrix q b' (asMatrix j T (pointMap f i j T s))
    rw [hmat T s, cliffordActionMatrix_eq_coordinates q b' e he T s]
    change (matrixCoordinates (b'.baseChange E)).symm
      (matrixCoordinates (b'.baseChange E) (vectorAction q E b' (spinPoint q b' G e he T s))) ∈ _
    rw [MulEquiv.symm_apply_apply]
    exact spin_matrix_is_specialOrthogonal q b' E hQ (spinPoint q b' G e he T s)
  constructor
  · rintro ⟨x, rfl⟩
    let y : PointsIn j E := ((groupPointsFunctor K).obj H.val).map a x
    haveI := hfinite
    let g₀ := f.hom.hom
    letI : Surjective g₀.left := hsurj
    obtain ⟨s, hs⟩ := lift_of_range (k := K) (K := E) g₀ y (Scheme.Hom.surjective g₀.left _)
    have hs' : pointMap f i j E s = y := hs
    refine (isSpecialOrthogonalMatrix_map_iff q b' φ _).mp ?_
    rw [← asMatrix_natural j φ x, show ((groupPointsFunctor K).obj H.val).map a x = y from rfl, ← hs']
    exact hsol s
  · intro hm
    have hm' := (isSpecialOrthogonalMatrix_map_iff q b' φ m).mpr hm
    let g : specialOrthogonal (coefficientForm E q b') :=
      ⟨(matrixCoordinates (b'.baseChange E)).symm (map φ.toRingHom m), hm'⟩
    obtain ⟨ν, hν⟩ := LocalQuadraticIsotropy.spinor_norm (coefficientForm E q b') hQ
    have hνg : ν g = 1 := by
      obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective (Subgroup.square Eˣ) (ν g)
      rw [← hz]
      apply (QuotientGroup.eq_one_iff z).mpr
      obtain ⟨t, ht⟩ := IsAlgClosed.isSquare (z : E)
      have hne : t ≠ 0 := by
        intro h
        simp [h] at ht
      exact ⟨Units.mk0 t hne, Units.ext ht⟩
    have hlift := (hasSpinLift_iff_intrinsic (coefficientForm E q b') g).mp ((hν.2.2 g).mp hνg)
    obtain ⟨c, hc⟩ := (vectorAction_exists_iff q b' E g.val).mpr hlift
    obtain ⟨s, hs⟩ := (spinPoint_bijective q b' G e he T).surjective c
    refine matrixRange_descends j φ m (pointMap f i j E s) ?_
    change asMatrix j T (pointMap f i j T s) = _
    rw [hmat T s, cliffordActionMatrix_eq_coordinates q b' e he T s, hs, hc]
    exact MulEquiv.apply_symm_apply _ _

end FieldPoints

noncomputable section NumberMatrixComparison

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.Unipotent (Index)
open Specs.IntegralModels (MatrixRealization RationalPoints)
open Specs.AnisotropicTensorQuotients (numberAtPlace orthogonalMatrixModel)
open Specs.DivisionOctonionOrthogonalTensors (matrixCoordinates)
open Matrix
open scoped NumberField TensorProduct

open private continuous_numberAtPlace mulVec_coordinates orthogonalTensors
  orthogonal_tensor_comparison from LinearAlgebraicGroups.Arithmetic.AnisotropicTensorQuotients
open private glIntegral_compactOpen eventually_outside from LinearAlgebraicGroups.Arithmetic.AdelicGroups

set_option backward.isDefEq.respectTransparency false

universe u v

private def reindexGL {R I J : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) : GL I R ≃* GL J R :=
  Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv

private theorem reindexGL_natural {R S I J : Type*} [CommRing R] [CommRing S]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (e : I ≃ J) (f : R →+* S)
    (m : GL I R) : reindexGL e (Matrix.GeneralLinearGroup.map f m) = Matrix.GeneralLinearGroup.map f (reindexGL e m) := by
  ext i j
  rfl

private theorem continuous_reindexGL {R I J : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) : Continuous (reindexGL (R := R) e) := by
  apply Units.continuous_iff.mpr
  have hv : Continuous (fun m : GL I R => (reindexGL e m).val) := by
    apply continuous_matrix
    intro i j
    exact (_root_.continuous_apply (e.symm j)).comp
      (Matrix.GeneralLinearGroup.continuous_apply _ continuous_id (e.symm i))
  refine ⟨hv, ?_⟩
  have h (x : GL I R) : ((reindexGL e x)⁻¹ : GL J R).val = (reindexGL e x⁻¹).val :=
    congrArg Units.val (map_inv (reindexGL e) x).symm
  simp_rw [h]
  exact hv.comp continuous_inv

private theorem reindexGL_homeomorph {R I J : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (e : I ≃ J) :
    IsHomeomorph (reindexGL (R := R) e) :=
  (Homeomorph.mk (reindexGL (R := R) e).toEquiv
    (continuous_reindexGL e) (continuous_reindexGL e.symm)).isHomeomorph

private theorem reindexGL_integral {L I J : Type*} [Field L]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (e : I ≃ J)
    (O : ValuationSubring L) (m : GL I L) :
    reindexGL e m ∈ (Matrix.GeneralLinearGroup.map O.subtype).range ↔ m ∈ (Matrix.GeneralLinearGroup.map O.subtype).range := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨x, rfl⟩ := (reindexGL e).surjective a
    exact ⟨x, (reindexGL e).injective ((reindexGL_natural e O.subtype x).trans ha)⟩
  · rintro ⟨a, rfl⟩
    exact ⟨reindexGL e a, (reindexGL_natural e O.subtype a).symm⟩

variable {K : Type u} [Field K] [NumberField K]
variable {H : AffineAlgebraicGroup K} (j : MatrixRealization H)

private def numberFieldData : GlobalFieldData.{u,v} K := .number inferInstance

private def numberMatrixPoint (L : Type u) [CommRing L] [Algebra K L] :
    PointsIn j L →* GL (Fin j.size) L :=
  (reindexGL Equiv.ulift).toMonoidHom.comp (asMatrix j L)

omit [NumberField K] in
private theorem numberMatrixPoint_natural {L E : Type u} [Field L] [Field E]
    [Algebra K L] [Algebra K E] (φ : L →ₐ[K] E) (x : PointsIn j L) :
    numberMatrixPoint j E (((groupPointsFunctor K).obj H.val).map (CommAlgCat.ofHom φ) x) =
      Matrix.GeneralLinearGroup.map φ.toRingHom (numberMatrixPoint j L x) := by
  change reindexGL Equiv.ulift (asMatrix j E _) = _
  rw [asMatrix_natural, reindexGL_natural]
  rfl

private abbrev numberLocalMatrix (D : GlobalFieldData.{u,v} K) (w : D.Place) :
    LocalPoints D j w →* GL (Fin j.size) (D.Completion w) :=
  numberMatrixPoint j (D.Completion w)

omit [NumberField K] in
private theorem numberLocalMatrix_integral (D : GlobalFieldData.{u,v} K) (w : D.FinitePlace)
    (x : LocalPoints D j (.inl w)) :
    numberLocalMatrix j D (.inl w) x ∈ (Matrix.GeneralLinearGroup.map (D.integers w).subtype).range ↔
      x ∈ integralPoints D j w :=
  reindexGL_integral Equiv.ulift (D.integers w) (asMatrix j (D.Completion (.inl w)) x)

omit [NumberField K] in
private theorem numberLocalMatrix_embedding (D : GlobalFieldData.{u,v} K) (w : D.Place) :
    IsClosedEmbedding (numberLocalMatrix j D w) :=
  ((reindexGL_homeomorph Equiv.ulift).isClosedEmbedding).comp (localMatrixEmbedding D j w)

private def numberAdelicMatrices (x : Adeles (numberFieldData.{u,v} (K := K)) j ∅) :
    LinearAlgebraicGroups.Arithmetic.TensorAdelicReduction.NumberMatrixAdeles K (Fin j.size) := by
  let D := numberFieldData.{u,v} (K := K)
  let W := Outside D ∅
  let a (w : NumberFinitePlace K) : W := ⟨.inl w, Finset.notMem_empty _⟩
  have ha : Function.Injective a := fun _ _ h => Sum.inl.inj (congrArg Subtype.val h)
  refine ⟨⟨fun w => numberLocalMatrix j D (.inl w) (x (a w)), ?_⟩,
    fun w => numberLocalMatrix j D (.inr w) (x ⟨.inr w, Finset.notMem_empty _⟩)⟩
  have hx := ha.tendsto_cofinite.eventually x.property
  filter_upwards [hx] with w hw
  exact (numberLocalMatrix_integral j D w (x (a w))).mpr hw

private def numberSplitAt (w : (numberFieldData.{u,v} (K := K)).Place) :
    LinearAlgebraicGroups.Arithmetic.TensorAdelicReduction.NumberMatrixAdeles K (Fin j.size) →*
      GL (Fin j.size) ((numberFieldData.{u,v} (K := K)).Completion w) := by
  cases w with
  | inl w => exact numberAtPlace (.inl w)
  | inr w => exact numberAtPlace (.inr w)

private theorem continuous_numberSplitAt (w : (numberFieldData.{u,v} (K := K)).Place) :
    Continuous (numberSplitAt j w) := by
  cases w with
  | inl w => exact continuous_numberAtPlace (.inl w)
  | inr w => exact continuous_numberAtPlace (.inr w)

private theorem numberAdelicMatrices_at (x : Adeles (numberFieldData.{u,v} (K := K)) j ∅) (w : Outside (numberFieldData.{u,v} (K := K)) ∅) :
    numberSplitAt j w.val (numberAdelicMatrices j x) = numberLocalMatrix j (numberFieldData.{u,v} (K := K)) w.val (x w) := by
  rcases w with ⟨w, hw⟩
  cases w <;> rfl

private theorem numberAdelicMatrices_compactBox
    (C : Set (LinearAlgebraicGroups.Arithmetic.TensorAdelicReduction.NumberMatrixAdeles K (Fin j.size)))
    (hC : IsCompact C) :
    IsCompact {x : Adeles (numberFieldData.{u,v} (K := K)) j ∅ | ∀ w : Outside (numberFieldData.{u,v} (K := K)) ∅,
      numberLocalMatrix j (numberFieldData.{u,v} (K := K)) w.val (x w) ∈ numberSplitAt j w.val '' C} := by
  let D := numberFieldData.{u,v} (K := K)
  classical
  let U (w : D.Place) := (numberLocalMatrix j D w) ⁻¹' (numberSplitAt j w '' C)
  have hU (w : D.Place) : IsCompact (U w) :=
    (numberLocalMatrix_embedding j D w).isCompact_preimage
      (hC.image (continuous_numberSplitAt j w))
  let B (w : NumberFinitePlace K) : Set (GL (Fin j.size) (w.adicCompletion K)) :=
    ↑(Matrix.GeneralLinearGroup.map (n := Fin j.size) (w.adicCompletionIntegers K).subtype).range
  have hB (w : NumberFinitePlace K) : IsOpen (B w) := by
    let E := w.adicCompletion K
    let O := w.adicCompletionIntegers K
    let r : Fin j.size ≃ Index.{u} j.size := Equiv.ulift.symm
    let B' : Set (GL (Index.{u} j.size) E) :=
      Set.range (Matrix.GeneralLinearGroup.map O.subtype)
    have he : B w = reindexGL r ⁻¹' B' :=
      Set.ext fun m => (reindexGL_integral r O m).symm
    letI : T2Space (w.adicCompletion K) := completionT2Space D (.inl w)
    have hB' : IsOpen B' := (glIntegral_compactOpen (ι := Index.{u} j.size)
      (w.adicCompletionIntegers K) (D.integers_properties w).1
        (D.integers_properties w).2.1).2
    rw [he]
    exact hB'.preimage (continuous_reindexGL r)
  obtain ⟨T, hT⟩ := compactRestrictedProductIntegrality B hB
    (Prod.fst '' C) (hC.image continuous_fst)
  have hsub : ∀ᶠ w : Outside D ∅ in cofinite, U w.val ⊆ localSubgroup D j w.val := by
    apply eventually_outside D ∅ (p := fun w => U w ⊆ localSubgroup D j w)
    · have hcof : ∀ᶠ w : NumberFinitePlace K in cofinite, w ∉ T := by
        apply eventually_cofinite.mpr
        simp
      filter_upwards [hcof] with w hw x hx
      obtain ⟨c, hc, hcx⟩ := hx
      apply (numberLocalMatrix_integral j D w x).mp
      exact hcx ▸ hT c.1 ⟨c, hc, rfl⟩ w hw
    · exact fun _ _ _ => Subgroup.mem_top _
  exact AdelicLatticeBounds.compactRestrictedProductBox
    (fun w : Outside D ∅ => (localSubgroup D j w.val : Set (LocalPoints D j w.val)))
    (fun w => U w.val) (fun w => hU w.val) hsub

open Albert.CliffordSpecification (coefficientForm)
open Specs.DivisionOctonionOrthogonalTensors (quadraticPolynomial specialOrthogonalGroup)
open LinearAlgebraicGroups.Composition.Specification (normBaseChange)
open Specs.Arithmetic.LocalQuadraticIsotropy (specialOrthogonal)
open LinearAlgebraicGroups.Arithmetic.TensorAdelicReduction (numberTensorAdelicReduction)

variable {V : Type u} [AddCommGroup V] [Module K V]
variable (q : QuadraticForm K V) (b : Module.Basis (Index.{u} j.size) K V)

private theorem reindex_matrixCoordinates {L W I J : Type*} [Field L]
    [AddCommGroup W] [Module L W] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (c : Module.Basis I L W) (r : I ≃ J) (g : W ≃ₗ[L] W) :
    reindexGL r (matrixCoordinates c g) = matrixCoordinates (c.reindex r) g := by
  ext i k
  change (LinearMap.toMatrix c c g.toLinearMap) (r.symm i) (r.symm k) =
    (LinearMap.toMatrix (c.reindex r) (c.reindex r) g.toLinearMap) i k
  simp only [LinearMap.toMatrix_apply, Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]

omit [NumberField K] in
private theorem numberMatrixPoint_range {L : Type u} [Field L] [Algebra K L]
    (himage : ∀ m : GL (Index.{u} j.size) L,
      m ∈ (asMatrix j L).range ↔ IsSpecialOrthogonalMatrix q b m)
    (m : GL (Fin j.size) L) :
    m ∈ (numberMatrixPoint j L).range ↔
      m ∈ orthogonalMatrixModel (b.reindex Equiv.ulift) q L (algebraMap K L) := by
  let r : Index.{u} j.size ≃ Fin j.size := Equiv.ulift
  let c := b.baseChange L
  let a := b.reindex r
  have hbase : a.baseChange L = c.reindex r := by
    ext i
    simp [a, c, Module.Basis.baseChange_apply]
  have hform : coefficientForm L q b = normBaseChange L q :=
    Albert.CliffordModel.coefficient_form_agreement L q b
  let m₀ := (reindexGL r).symm m
  let g := (matrixCoordinates c).symm m₀
  have hmatrix : matrixCoordinates (a.baseChange L) g = m := by
    rw [hbase, ← reindex_matrixCoordinates, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  have h₁ : m ∈ (numberMatrixPoint j L).range ↔ m₀ ∈ (asMatrix j L).range := by
    constructor
    · rintro ⟨x, h⟩
      exact ⟨x, (reindexGL r).injective (h.trans ((reindexGL r).apply_symm_apply m).symm)⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      change reindexGL r (asMatrix j L x) = m
      rw [hx, MulEquiv.apply_symm_apply]
  rw [h₁, himage]
  let M (aL : Algebra K L) : Prop :=
    letI := aL
    ∃ g' : specialOrthogonalGroup (normBaseChange L q), matrixCoordinates (a.baseChange L) g'.val = m
  change IsSpecialOrthogonalMatrix q b m₀ ↔ M ((algebraMap K L).toAlgebra)
  rw [toAlgebra_algebraMap]
  change g ∈ specialOrthogonal (coefficientForm L q b) ↔
    ∃ g' : specialOrthogonalGroup (normBaseChange L q), matrixCoordinates (a.baseChange L) g'.val = m
  rw [hform]
  exact ⟨fun h => ⟨⟨g, h⟩, hmatrix⟩, fun ⟨g', hg'⟩ =>
    (show g'.val = g from (matrixCoordinates (a.baseChange L)).injective (hg'.trans hmatrix.symm))
      ▸ g'.property⟩

omit [NumberField K] in
private theorem orthogonalModel_invariants {L : Type u} [Field L]
    (a : Module.Basis (Fin j.size) K V) (e : K →+* L) (m : GL (Fin j.size) L)
    (hm : m ∈ orthogonalMatrixModel a q L e) :
    m.det = 1 ∧ ∀ x, (quadraticPolynomial a q).eval₂ e (m.val.mulVec x) =
      (quadraticPolynomial a q).eval₂ e x := by
  letI := e.toAlgebra
  let c := a.baseChange L
  let Q := normBaseChange L q
  obtain ⟨g, rfl⟩ := (show ∃ g : specialOrthogonalGroup Q, matrixCoordinates c g.val = m from hm)
  refine ⟨(matrixCoordinates_det c g.val).trans g.property.2, ?_⟩
  intro x
  have h (y : Fin j.size → L) : (quadraticPolynomial a q).eval₂ e y = Q (c.equivFun.symm y) :=
    (LinearAlgebraicGroups.Arithmetic.DivisionOctonionOrthogonalTensors.quadraticPolynomialComparison
      a q).2 L y
  rw [h, h, mulVec_coordinates c, MulEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact g.property.1 _

/-- The tensor reduction over the number field gives compact right
representatives in the adelic group of the actual closed orthogonal image. -/
private theorem numberOrthogonalRepresentatives
    (hq : LinearMap.ker q.polarBilin = ⊥)
    (ha : ∀ x, q x = 0 → x = 0) (hn : 5 ≤ j.size)
    (himage : ∀ (L : Type u) [Field L] [Algebra K L] (m : GL (Index.{u} j.size) L),
      m ∈ (asMatrix j L).range ↔ IsSpecialOrthogonalMatrix q b m) :
    ∃ C : Set (Adeles (numberFieldData.{u,v} (K := K)) j ∅), IsCompact C ∧
      ∀ x : Adeles (numberFieldData.{u,v} (K := K)) j ∅, ∃ d : RationalPoints H, ∃ y ∈ C,
        ∀ w : Outside (numberFieldData.{u,v} (K := K)) ∅, y w = x w * localPoint (numberFieldData.{u,v} (K := K)) j w.val d := by
  let D := numberFieldData.{u,v} (K := K)
  let a := b.reindex (Equiv.ulift : Index.{u} j.size ≃ Fin j.size)
  let p : Unit → MvPolynomial (Fin j.size) K := fun _ => quadraticPolynomial a q
  let T := orthogonalTensors a q
  letI : Module.Finite K V := Module.Finite.of_basis b
  have hnd : q.polarBilin.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr hq
  obtain ⟨hhom, hzero, _⟩ :=
    LinearAlgebraicGroups.Arithmetic.DivisionOctonionOrthogonalTensors.orthogonalPolynomialModel.{u,u,u}
      a q hn hnd ha
  obtain ⟨δ, hδf, hδi, C, hC, _, hreduce⟩ :=
    numberTensorAdelicReduction p (fun _ => 2) T (fun _ => ⟨by decide, hhom⟩)
      (fun x hx => ⟨(), hzero x hx⟩)
  refine ⟨{x | ∀ w : Outside D ∅, numberLocalMatrix j D w.val (x w) ∈ numberSplitAt j w.val '' C},
    numberAdelicMatrices_compactBox j C hC, ?_⟩
  intro x
  let X := numberAdelicMatrices j x
  have hX (w : D.Place) :
      numberSplitAt j w X ∈ orthogonalMatrixModel a q (D.Completion w) (D.embedding w) := by
    let w' : Outside D ∅ := ⟨w, Finset.notMem_empty _⟩
    rw [show numberSplitAt j w X = numberLocalMatrix j D w (x w')
      from numberAdelicMatrices_at j x w']
    exact (numberMatrixPoint_range j q b (himage _) _).mp ⟨x w', rfl⟩
  have hinv (w : D.Place) :=
    orthogonalModel_invariants j q a (D.embedding w) (numberSplitAt j w X) (hX w)
  obtain ⟨m, hm, hXm⟩ := hreduce X
    (fun w => (hinv (.inl w)).1) (fun w => (hinv (.inr w)).1)
    (fun _ w z => (hinv (.inl w)).2 z) (fun _ w z => (hinv (.inr w)).2 z)
    ⟨(fun w => (orthogonal_tensor_comparison a q _ _).mp (hX (.inl w))),
      (fun w => (orthogonal_tensor_comparison a q _ _).mp (hX (.inr w)))⟩
  have hm' : m ∈ orthogonalMatrixModel a q K (RingHom.id K) :=
    (orthogonal_tensor_comparison a q _ _).mpr hm
  obtain ⟨d, hd⟩ := (numberMatrixPoint_range j q b (himage K) m).mpr hm'
  let dA := diagonal D j ∅ d
  refine ⟨d, x * dA, ?_, ?_⟩
  · intro w
    refine ⟨X * δ m, hXm, ?_⟩
    rw [map_mul, numberAdelicMatrices_at j x w]
    change _ = numberLocalMatrix j D w.val (x w * dA w)
    rw [map_mul]
    congr 1
    rw [diagonalCoordinates D j ∅ d w]
    have hδw : numberSplitAt j w.val (δ m) = Matrix.GeneralLinearGroup.map (D.embedding w.val) m := by
      obtain ⟨w, hw⟩ := w
      cases w with
      | inl w => exact hδf m w
      | inr w => exact hδi m w
    rw [hδw, ← hd]
    exact (numberMatrixPoint_natural j (Algebra.ofId K (D.Completion w.val)) d).symm
  · intro w
    change x w * dA w = _
    rw [diagonalCoordinates D j ∅ d w]

end NumberMatrixComparison

noncomputable section SpinorNormNaturality

open Specs.Arithmetic.LocalQuadraticIsotropy
open Specs.Arithmetic.IsotropicSpinGeneration (reflection)
open private reflectionWordLinear reflectionWordLinear_apply reflectionWord_even
  from LinearAlgebraicGroups.Arithmetic.LocalQuadraticIsotropy

private theorem squares_eq_power_range (F : Type*) [Field F] :
    Subgroup.square Fˣ = (powMonoidHom (α := Fˣ) 2).range := by
  ext z
  rw [Subgroup.mem_square]
  exact ⟨fun ⟨t, ht⟩ => ⟨t, (pow_two t).trans ht.symm⟩,
    fun ⟨t, ht⟩ => ⟨t, ht.symm.trans (pow_two t)⟩⟩

private def squareClassesToKummer (F : Type*) [Field F] :
    SquareClasses F ≃* Kummer.Classes F 2 :=
  QuotientGroup.quotientMulEquivOfEq (squares_eq_power_range F)

private theorem squareClassesToKummer_mk (F : Type*) [Field F] (z : Fˣ) :
    squareClassesToKummer F (QuotientGroup.mk' (Subgroup.square Fˣ) z) =
      Kummer.classOf 2 z := rfl

/-- Changing scalars in a reflection word changes the class by the induced
map on units. The image of the given semilinear map contains a basis. -/
private theorem spinorNorm_map_of_comparison
    {F E W W' I : Type*} [Field F] [Field E] [AddCommGroup W] [Module F W]
    [AddCommGroup W'] [Module E W'] [CharZero E]
    (φ : F →+* E) (τ : W →ₛₗ[φ] W') (b : Module.Basis I E W')
    (hspan : ∀ i, b i ∈ Set.range τ)
    (P : QuadraticForm F W) (Q : QuadraticForm E W')
    (hq : ∀ x, Q (τ x) = φ (P x))
    (g : specialOrthogonal P) (h : specialOrthogonal Q)
    (hact : ∀ x, h.val (τ x) = τ (g.val x))
    (ν : specialOrthogonal P →* SquareClasses F) (hν : IsSpinorNorm P ν)
    (ν' : specialOrthogonal Q →* SquareClasses E) (hν' : IsSpinorNorm Q ν') :
    squareClassesToKummer E (ν' h) = Kummer.map φ 2 (squareClassesToKummer F (ν g)) := by
  obtain ⟨l, hl, hg⟩ := hν.1 g
  let v (w : ReflectionVector P) : ReflectionVector Q :=
    ⟨τ w.val, hq w.val ▸ (map_ne_zero φ).2 w.property⟩
  have hpol (x y : W) : Q.polarBilin (τ x) (τ y) = φ (P.polarBilin x y) := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      ← map_add τ, hq, map_sub]
  have hreflection (w : ReflectionVector P) (x : W) :
      reflection Q (v w).val (τ x) = τ (reflection P w.val x) := by
    change τ x - (Q.polarBilin (τ w.val) (τ x) / Q (τ w.val)) • τ w.val = _
    rw [hpol, hq, ← map_div₀]
    change _ = τ (x - (P.polarBilin w.val x / P w.val) • w.val)
    rw [map_sub, LinearMap.map_smulₛₗ]
  have hword (l : List (ReflectionVector P)) (x : W) :
      reflectionWord Q (l.map v) (τ x) = τ (reflectionWord P l x) := by
    induction l with
    | nil => rfl
    | cons w l ih =>
      change reflection Q (v w).val (reflectionWord Q (l.map v) (τ x)) =
        τ (reflection P w.val (reflectionWord P l x))
      rw [ih, hreflection]
  have hmap : h.val.toLinearMap = reflectionWordLinear Q (l.map v) := by
    apply b.ext
    intro i
    obtain ⟨x, hx⟩ := hspan i
    rw [← hx, reflectionWordLinear_apply]
    change h.val (τ x) = _
    rw [hact, hg, hword]
  have hh (x : W') : h.val x = reflectionWord Q (l.map v) x :=
    (LinearMap.congr_fun hmap x).trans (reflectionWordLinear_apply Q _ x)
  have hnorm (l : List (ReflectionVector P)) :
      reflectionNorm Q (l.map v) = Units.map φ.toMonoidHom (reflectionNorm P l) := by
    induction l with
    | nil => simp [reflectionNorm]
    | cons w l ih =>
      change Units.mk0 (Q (τ w.val)) (v w).property * reflectionNorm Q (l.map v) =
        Units.map φ.toMonoidHom (Units.mk0 (P w.val) w.property * reflectionNorm P l)
      rw [ih, map_mul, show Units.mk0 (Q (τ w.val)) (v w).property =
        Units.map φ.toMonoidHom (Units.mk0 (P w.val) w.property) from Units.ext (hq _)]
  rw [hν.2.1 g l hl hg, hν'.2.1 h (l.map v) (by simpa only [List.length_map] using hl) hh,
    squareClassesToKummer_mk, squareClassesToKummer_mk, hnorm]
  rfl

end SpinorNormNaturality

noncomputable section IntegralSpinorNorm

open LinearAlgebraicGroups.Specs.Arithmetic.LocalQuadraticIsotropy
open Specs.Arithmetic.IsotropicSpinGeneration (reflection)
open Specs.DivisionOctonionOrthogonalTensors (matrixCoordinates)
open Matrix Matrix.GeneralLinearGroup
open Module

set_option backward.isDefEq.respectTransparency false

open private integral_generate integralWord integralReflect integralReflect_apply UnitVector
  reflectionWordLinear reflectionWordLinear_apply reflectionWord_even
  from LinearAlgebraicGroups.Arithmetic.LocalQuadraticIsotropy
open private mulVec_coordinates from LinearAlgebraicGroups.Arithmetic.AnisotropicTensorQuotients

universe u

/-- An isometry preserving an integral unimodular lattice at a place of
odd residue characteristic has its spinor norm represented by an integral unit. -/
private theorem integralMatrix_spinorNorm
    {F W I : Type u} [Field F] [CharZero F] {O : ValuationSubring F}
    [IsPrincipalIdealRing O] [AddCommGroup W] [Module F W] [Fintype I] [DecidableEq I]
    (b : Basis I F W) (Q : QuadraticForm F W)
    (h₂ : (2 : F)⁻¹ ∈ O)
    (hB : ∀ i j, Q.polarBilin (b i) (b j) ∈ O)
    (hdet : (LinearMap.BilinForm.toMatrix b Q.polarBilin).det ≠ 0)
    (hdetInt : (LinearMap.BilinForm.toMatrix b Q.polarBilin).det⁻¹ ∈ O)
    (g : specialOrthogonal Q)
    (hg : matrixCoordinates b g.val ∈ (Matrix.GeneralLinearGroup.map O.subtype).range)
    (ν : specialOrthogonal Q →* SquareClasses F) (hν : IsSpinorNorm Q ν) :
    squareClassesToKummer F (ν g) ∈ (Kummer.map O.subtype 2).range := by
  classical
  letI : FiniteDimensional F W := Module.Finite.of_basis b
  let τ : (I → O) →ₛₗ[O.subtype] W :=
    { toFun := fun y => b.equivFun.symm (O.subtype ∘ y)
      map_add' := fun x y => by simp only [← map_add]; rfl
      map_smul' := fun a y => by simp only [← map_smul]; rfl }
  let c := Pi.basisFun O I
  have hτbasis (i : I) : τ (c i) = b i := by
    apply b.equivFun.injective
    rw [show b.equivFun (τ (c i)) = O.subtype ∘ c i from b.equivFun.apply_symm_apply _]
    funext j
    by_cases hij : j = i
    · subst j
      simp [c, Pi.basisFun]
    · simp [c, Pi.basisFun, hij, Ne.symm hij]
  let B := LinearMap.BilinForm.toMatrix b Q.polarBilin
  let A : Matrix I I O := fun i j => ⟨B i j, by simpa only [B, LinearMap.BilinForm.toMatrix_apply] using hB i j⟩
  have hA : A.map O.subtype = B := rfl
  have hA' : O.subtype A.det = B.det :=
    (RingHom.map_det _ _).trans (congrArg Matrix.det hA)
  have hAunit : IsUnit A.det := by
    apply IsUnit.of_mul_eq_one (⟨B.det⁻¹, hdetInt⟩ : O)
    apply Subtype.ext
    change O.subtype A.det * B.det⁻¹ = 1
    rw [hA', mul_inv_cancel₀ hdet]
  have htwo : IsUnit (2 : O) := by
    apply IsUnit.of_mul_eq_one (⟨(2 : F)⁻¹, h₂⟩ : O)
    apply Subtype.ext
    change (2 : F) * (2 : F)⁻¹ = 1
    norm_num
  letI : Invertible (2 : O) := htwo.invertible
  let Q₀ : QuadraticForm O (I → O) :=
    ((⅟ (2 : O)) • (Matrix.toBilin' A)).toQuadraticMap
  have hBcomp (x y : I → O) :
      O.subtype (Matrix.toBilin' A x y) = Q.polarBilin (τ x) (τ y) := by
    have hm : O.subtype ∘ A.mulVec y = (A.map O.subtype).mulVec (O.subtype ∘ y) :=
      funext fun i => RingHom.map_mulVec O.subtype A y i
    rw [Matrix.toBilin'_apply', RingHom.map_dotProduct, hm, hA]
    exact LinearMap.BilinForm.dotProduct_toMatrix_mulVec b Q.polarBilin _ _
  have hQcomp (x : I → O) : O.subtype (Q₀ x) = Q (τ x) := by
    change O.subtype ((⅟ (2 : O)) * (Matrix.toBilin' A x x)) = _
    rw [map_mul, hBcomp]
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul, ← mul_assoc]
    have hh := congrArg O.subtype (invOf_mul_self (2 : O))
    rw [map_mul, map_ofNat, map_one] at hh
    change O.subtype (⅟ (2 : O)) * (2 : F) * Q (τ x) = _
    rw [hh, one_mul]
  have hPcomp (x y : I → O) : O.subtype (Q₀.polarBilin x y) = Q.polarBilin (τ x) (τ y) := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, map_sub, hQcomp, map_add]
  have hB₀ : Q₀.polarBilin = Matrix.toBilin' A := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact O.subtype_injective ((hPcomp x y).trans (hBcomp x y).symm)
  have hbij : Function.Bijective Q₀.polarBilin := by
    rw [hB₀]
    let B₀ := (toLin (mk'' Aᵀ (by simpa only [Matrix.det_transpose] using hAunit))).toLinearEquiv
    let E := B₀.trans c.toDualEquiv
    have hE : E.toLinearMap = Matrix.toBilin' A := by
      apply LinearMap.ext
      intro x
      change c.toDual (B₀ x) = Matrix.toBilin' A x
      apply c.ext
      intro i
      rw [Module.Basis.toDual_apply_left, Pi.basisFun_repr, Matrix.toBilin'_apply',
        Matrix.dotProduct_mulVec]
      have he : B₀ x = Aᵀ.mulVec x := Matrix.GeneralLinearGroup.toLin_apply _ _
      rw [he, Matrix.mulVec_transpose]
      simpa only [c, Pi.basisFun_apply] using
        (dotProduct_single_one (Matrix.vecMul x A) i).symm
    exact hE ▸ E.bijective
  obtain ⟨m, hm⟩ := hg
  let g₀ := (toLin m).toLinearEquiv
  have hg₀ (x : I → O) : τ (g₀ x) = g.val (τ x) := by
    apply b.equivFun.injective
    have h := mulVec_coordinates b (matrixCoordinates b g.val) (O.subtype ∘ x)
    rw [MulEquiv.symm_apply_apply] at h
    calc
      _ = O.subtype ∘ m.val.mulVec x := b.equivFun.apply_symm_apply _
      _ = (matrixCoordinates b g.val).val.mulVec (O.subtype ∘ x) := by
        rw [← hm]
        exact funext fun i => RingHom.map_mulVec O.subtype m.val x i
      _ = _ := h
  have h0 (x : I → O) : Q₀ (g₀ x) = Q₀ x := by
    apply O.subtype_injective
    simp only [hQcomp, hg₀, g.property.1]
  obtain ⟨l, hl⟩ := integral_generate htwo (Module.finrank O (I → O)) rfl Q₀ hbij g₀.toLinearMap h0
  let v (z : UnitVector Q₀) : ReflectionVector Q :=
    ⟨τ z.val, ((hQcomp z.val).symm ▸ (map_ne_zero_iff O.subtype O.subtype_injective).2 z.property.ne_zero)⟩
  have hreflect (z : UnitVector Q₀) (x : I → O) :
      reflection Q (v z).val (τ x) = τ (integralReflect Q₀ z x) := by
    rw [integralReflect_apply]
    change τ x - (Q.polarBilin (τ z.val) (τ x) / Q (τ z.val)) • τ z.val = _
    simp only [map_sub, LinearMap.map_smulₛₗ, map_mul, hPcomp]
    congr 2
    have hs : O.subtype z.property.unit.val = Q (τ z.val) := by
      rw [z.property.unit_spec, hQcomp]
    have hi : O.subtype z.property.unit⁻¹.val = (Q (τ z.val))⁻¹ := by
      rw [← hs]
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hi, div_eq_mul_inv, mul_comm]
  have hword (l : List (UnitVector Q₀)) (x : I → O) :
      reflectionWord Q (l.map v) (τ x) = τ (integralWord Q₀ l x) := by
    induction l with
    | nil => rfl
    | cons z l ih =>
      change reflection Q (v z).val (reflectionWord Q (l.map v) (τ x)) =
        τ (integralReflect Q₀ z (integralWord Q₀ l x))
      rw [ih, hreflect]
  have hmap : g.val.toLinearMap = reflectionWordLinear Q (l.map v) := by
    apply b.ext
    intro i
    rw [← hτbasis i, reflectionWordLinear_apply, hword, ← hl]
    exact (hg₀ _).symm
  have hact (x : W) : g.val x = reflectionWord Q (l.map v) x :=
    (LinearMap.congr_fun hmap x).trans (reflectionWordLinear_apply Q _ x)
  have hpar : Even (l.map v).length := reflectionWord_even Q g _ hact
  have hprod (l : List (UnitVector Q₀)) :
      reflectionNorm Q (l.map v) =
        Units.map O.subtype.toMonoidHom (l.map fun z => z.property.unit).prod := by
    induction l with
    | nil => simp [reflectionNorm]
    | cons z l ih =>
      change Units.mk0 (Q (τ z.val)) (v z).property * reflectionNorm Q (l.map v) = _
      rw [List.map_cons, List.prod_cons, map_mul, ih]
      congr 1
      apply Units.ext
      change Q (τ z.val) = O.subtype z.property.unit.val
      rw [z.property.unit_spec, hQcomp]
  refine ⟨Kummer.classOf 2 ((l.map fun z => z.property.unit).prod), ?_⟩
  rw [hν.2.1 g _ hpar hact, squareClassesToKummer_mk, hprod]
  rfl

end IntegralSpinorNorm

noncomputable section NumberFieldCompactness

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.Unipotent (Index)
open Specs.IntegralModels (MatrixRealization RationalPoints)
open Specs.Arithmetic.LocalQuadraticIsotropy
open Specs.DivisionOctonionOrthogonalTensors (matrixCoordinates)
open Albert.CliffordSpecification (coefficientForm)
open Albert.SpinSpecification (IsSpinPointRepresentation SchemePoints ScalarClifford)
open scoped TensorProduct CategoryTheory.MonObj
open Matrix

open private changeModule changeModule_smul changeModule_basis polar_baseChange_tmul
  from LinearAlgebraicGroups.Albert.SpinFunctor

set_option backward.isDefEq.respectTransparency false

universe u v

variable {K V : Type u} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
variable {G H : AffineAlgebraicGroup K} (i : MatrixRealization G) (j : MatrixRealization H)
variable (q : QuadraticForm K V) (b : Module.Basis (Index.{u} j.size) K V)

private def orthogonalPoint (L : Type u) [Field L] [Algebra K L]
    (hL : ∀ x : PointsIn j L, IsSpecialOrthogonalMatrix q b (asMatrix j L x)) :
    PointsIn j L →* specialOrthogonal (coefficientForm L q b) :=
  ((matrixCoordinates (b.baseChange L)).symm.toMonoidHom.comp (asMatrix j L)).codRestrict _ hL

omit [CharZero K] in
private theorem exists_extendedSpinorNorm (L : Type u) [Field L] [Algebra K L] [CharZero L]
    (hq : LinearMap.ker q.polarBilin = ⊥) :
    ∃ ν : specialOrthogonal (coefficientForm L q b) →* SquareClasses L,
      IsSpinorNorm (coefficientForm L q b) ν := by
  letI := Module.Finite.of_basis b
  letI := Module.Finite.of_basis (b.baseChange L)
  exact LocalQuadraticIsotropy.spinor_norm (coefficientForm L q b) (coefficientForm_ker q b hq)

variable {L E : Type u} [Field L] [Field E] [Algebra K L] [Algebra K E]
    [CharZero E]

omit [CharZero K] in
private theorem orthogonalPoint_spinorNorm_map
    (hL : ∀ x : PointsIn j L, IsSpecialOrthogonalMatrix q b (asMatrix j L x))
    (hE : ∀ x : PointsIn j E, IsSpecialOrthogonalMatrix q b (asMatrix j E x))
    (νL : specialOrthogonal (coefficientForm L q b) →* SquareClasses L)
    (νE : specialOrthogonal (coefficientForm E q b) →* SquareClasses E)
    (hνL : IsSpinorNorm (coefficientForm L q b) νL)
    (hνE : IsSpinorNorm (coefficientForm E q b) νE)
    (φ : L →ₐ[K] E) (x : PointsIn j L) :
    squareClassesToKummer E (νE (orthogonalPoint j q b E hE
      (((groupPointsFunctor K).obj H.val).map (CommAlgCat.ofHom φ) x))) =
      Kummer.map φ.toRingHom 2 (squareClassesToKummer L (νL (orthogonalPoint j q b L hL x))) := by
  let τ : (L ⊗[K] V) →ₛₗ[φ.toRingHom] E ⊗[K] V :=
    { toFun := changeModule φ
      map_add' := map_add _
      map_smul' := changeModule_smul φ }
  refine spinorNorm_map_of_comparison φ.toRingHom τ (b.baseChange E)
    (fun a => ⟨b.baseChange L a, changeModule_basis b φ a⟩)
    _ _ (coefficientForm_natural q b φ) _ _ ?_ νL hνL νE hνE
  intro z
  change (matrixCoordinates (b.baseChange E)).symm
    (asMatrix j E (((groupPointsFunctor K).obj H.val).map (CommAlgCat.ofHom φ) x))
      (changeModule φ z) = _
  rw [asMatrix_natural j φ x]
  exact matrixAction_natural b φ _ z

variable (D : GlobalFieldData.{u,v} K)

private theorem completion_charZero (w : D.Place) : CharZero (D.Completion w) :=
  Algebra.charZero_of_charZero K (D.Completion w)

set_option maxRecDepth 2400 in
set_option maxHeartbeats 1500000 in
private theorem goodPlaces_spinorNorm
    (hq : LinearMap.ker q.polarBilin = ⊥)
    (h : ∀ (L : Type u) [Field L] [Algebra K L],
      ∀ x : PointsIn j L, IsSpecialOrthogonalMatrix q b (asMatrix j L x))
    (ν : ∀ w : D.FinitePlace,
      specialOrthogonal (coefficientForm (D.Completion (.inl w)) q b) →*
        SquareClasses (D.FiniteCompletion w))
    (hν : ∀ w : D.FinitePlace, IsSpinorNorm (coefficientForm (D.Completion (.inl w)) q b) (ν w)) :
    ∀ᶠ w : D.FinitePlace in Filter.cofinite, ∀ x ∈ integralPoints D j w,
      squareClassesToKummer (D.FiniteCompletion w)
        (ν w (orthogonalPoint j q b (D.Completion (.inl w)) (h _) x)) ∈
          (Kummer.map (D.integers w).subtype 2).range := by
  letI : Module.Finite K V := Module.Finite.of_basis b
  let B := LinearMap.BilinForm.toMatrix b q.polarBilin
  have hB : B.det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
      (LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr hq)
  have he (z : K) : ∀ᶠ w : D.FinitePlace in Filter.cofinite, D.embedding (.inl w) z ∈ D.integers w :=
    Filter.eventually_cofinite.mpr (D.finite_nonintegral z)
  have hcoeff := Filter.eventually_all.mpr fun m : Index.{u} j.size × Index.{u} j.size =>
    he (B m.1 m.2)
  filter_upwards [hcoeff, he B.det⁻¹, he (2 : K)⁻¹] with w hw hwd hw₂ x hx
  let F := D.Completion (.inl w)
  let c := b.baseChange F
  let Q := coefficientForm F q b
  let O : ValuationSubring F := D.integers w
  let hz : CharZero F := Algebra.charZero_of_charZero K (D.Completion (.inl w))
  let hp : IsPrincipalIdealRing O := by
    change IsPrincipalIdealRing ↥(D.integers w)
    rw [D.integers_eq_valuationSubring w]
    letI := D.finiteCompletion_isLocalField w
    infer_instance
  have hQmat : LinearMap.BilinForm.toMatrix c Q.polarBilin = (D.embedding (.inl w)).mapMatrix B := by
    ext i k
    simp only [LinearMap.BilinForm.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      B, c, Module.Basis.baseChange_apply]
    exact polar_baseChange_tmul q F b (b i) (b k)
  have hQdet : (LinearMap.BilinForm.toMatrix c Q.polarBilin).det = D.embedding (.inl w) B.det := by
    rw [hQmat, RingHom.map_det]
  have hg : matrixCoordinates c ((orthogonalPoint j q b F (h F)) x).val ∈
      (Matrix.GeneralLinearGroup.map O.subtype).range := by
    change matrixCoordinates c ((matrixCoordinates c).symm (asMatrix j F x)) ∈ _
    rw [MulEquiv.apply_symm_apply]
    exact hx
  refine @integralMatrix_spinorNorm F (F ⊗[K] V) (Index.{u} j.size)
    _ hz O hp _ _ _ _ c Q ?_ ?_ ?_ ?_ _ hg (ν w) (hν w)
  · simpa only [map_inv₀, map_ofNat] using hw₂
  · intro i k
    have hz := congrArg (fun N : Matrix _ _ F => N i k) hQmat
    simp only [LinearMap.BilinForm.toMatrix_apply, RingHom.mapMatrix_apply] at hz
    rw [hz]
    exact hw (i,k)
  · rw [hQdet]
    exact (map_ne_zero (D.embedding (.inl w))).2 hB
  · rw [hQdet]
    simpa only [map_inv₀] using hwd

set_option maxRecDepth 2400 in
set_option maxHeartbeats 2000000 in
private theorem numberFieldSpinCompactness [NumberField K] :
    AnisotropicSpinCompactnessOver (numberFieldData.{u,v} (K := K)) := by
  classical
  intro V _ _ q r hr ha n b hn G e he i d hd
  have hq : LinearMap.ker q.polarBilin = ⊥ := by
    cases r with
    | none => exact hr
    | some a => exact ((by norm_num : (2 : K) ≠ 0) hr.1).elim
  obtain ⟨H, f, _, j, hj, hf, _, hsur, _, _, _, _, hm⟩ :=
    regularSpinFiniteVectorCover q b G e he (Or.inl hq)
  subst n
  have hmat (S : CommAlgCat.{u} K) (x : SchemePoints G.val S) :
      asMatrix j S (pointMap f i j S x) = cliffordActionMatrix q b G e he S x := by
    apply Matrix.GeneralLinearGroup.ext
    intro l m
    have h := congrArg (fun M : Matrix (Index.{u} j.size) (Index.{u} j.size) S => M l m) (hm S x)
    change _ = (cliffordActionMatrix q b G e he S x).val l m at h
    exact h
  have himage (L : Type u) [Field L] [Algebra K L] (m : Matrix.GeneralLinearGroup (Index.{u} j.size) L) :
      m ∈ (asMatrix j L).range ↔ IsSpecialOrthogonalMatrix q b m := by
    letI : CharZero L := Algebra.charZero_of_charZero K L
    exact vectorCover_image (L := L) q i j b e he f hmat hq hf hsur m
  have hSO (L : Type u) [Field L] [Algebra K L] (x : PointsIn j L) :
      IsSpecialOrthogonalMatrix q b (asMatrix j L x) :=
    (himage L _).mp ⟨x, rfl⟩
  let D : GlobalFieldData.{u,v} K := numberFieldData
  obtain ⟨C, hC, hrep⟩ :=
    numberOrthogonalRepresentatives.{u,v} j q b hq ha hn himage
  let ν (L : Type u) [Field L] [Algebra K L] [CharZero L] :
      specialOrthogonal (coefficientForm L q b) →* SquareClasses L :=
    (exists_extendedSpinorNorm j q b L hq).choose
  have hν (L : Type u) [Field L] [Algebra K L] [CharZero L] :=
    (exists_extendedSpinorNorm j q b L hq).choose_spec
  let wid (w : D.FinitePlace) : D.Place := .inl w
  letI instCharZeroCompletion (w : D.FinitePlace) : CharZero (D.Completion (wid w)) :=
    completion_charZero D (wid w)
  let ω (L : Type u) [Field L] [Algebra K L] [CharZero L] :
      PointsIn j L →* Kummer.Classes L 2 :=
    (squareClassesToKummer L).toMonoidHom.comp ((ν L).comp (orthogonalPoint j q b L (hSO L)))
  have hker (L : Type u) [Field L] [Algebra K L] [CharZero L] (x : PointsIn j L) :
      ω L x = 1 ↔ x ∈ (pointMap f i j L).range := by
    change squareClassesToKummer L (ν L (orthogonalPoint j q b L (hSO L) x)) = 1 ↔ _
    have h₁ : squareClassesToKummer L (ν L (orthogonalPoint j q b L (hSO L) x)) = 1 ↔
        ν L (orthogonalPoint j q b L (hSO L) x) = 1 :=
      ⟨fun h => (squareClassesToKummer L).injective (h.trans (map_one _).symm),
        fun h => h ▸ map_one _⟩
    exact h₁.trans (((hν L).2.2 _).trans (vectorAction_lift_iff q i j b e he f hmat x (hSO L x)))
  refine compactOfSquareClassReductionWithFiniteCovers D f i j d (diagonal D j ∅)
    hd (diagonalCoordinates D j ∅) hf (ω K) (fun w => ω (D.Completion (wid w)))
    (hker K) ?_ ?_ ?_ C hC ?_
  · intro w h
    exact orthogonalPoint_spinorNorm_map j q b (hSO K) (hSO (D.Completion (wid w)))
      (ν K) (ν (D.Completion (wid w))) (hν K) (hν (D.Completion (wid w)))
      (Algebra.ofId K (D.Completion (wid w))) h
  · intro w x
    exact (hker (D.Completion (wid w)) _).mpr ⟨x, rfl⟩
  · exact goodPlaces_spinorNorm j q b D hq hSO (fun w => ν (D.Completion (wid w)))
      (fun w => hν (D.Completion (wid w)))
  · intro x
    obtain ⟨F, hF, _, _⟩ := finiteAdelicMorphismUsingCoordinates D f hf i j
    obtain ⟨r, c, hc, hr⟩ := hrep (F x)
    exact ⟨r, c, hc, fun w => (hr w).trans
      (congrArg₂ (· * ·) (hF x w) (diagonalCoordinates D j ∅ r w).symm)⟩

end NumberFieldCompactness

theorem anisotropicSpinCompactness.{u,v} : AnisotropicSpinCompactness.{u,v} := by
  intro K _ D
  cases D with
  | number h =>
    letI := h
    exact @numberFieldSpinCompactness.{u,v} K _ _ h
  | function F t => exact functionFieldSpinCompactness t

end LinearAlgebraicGroups.Arithmetic.AnisotropicSpinQuotients
