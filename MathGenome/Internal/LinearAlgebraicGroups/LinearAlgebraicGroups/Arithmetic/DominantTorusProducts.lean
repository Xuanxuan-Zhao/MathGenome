import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.DominantTorusProducts
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriExist
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ReductiveLieCentralizers
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj BigOperators

universe u

namespace LinearAlgebraicGroups.Arithmetic.DominantTorusProducts

open LinearAlgebraicGroups.Specs hiding Lie
open LinearAlgebraicGroups.Specs.GeometricRadicals
open LinearAlgebraicGroups.Specs.DominantTorusProducts
open LinearAlgebraicGroups.Specs.Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open LinearAlgebraicGroups.Specs.SemisimpleLieCentralizer
open LinearAlgebraicGroups.Specs.CentralFrobeniusDescent (IsCentral)
open LinearAlgebraicGroups.Specs.EquivariantUnipotentSeries (onPoints)
open LinearAlgebraicGroups.SemisimpleLieCentralizer

open private central_in_charZero groupDimension groupDimension_lt_of_proper
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NontrivialRationalTorus
open private maximalTorus_exists geometricGroupReductive tangent_surjective_of_open
  trivial_of_le_trivial maximalTorus_over_closure commute_matrixDifferentials_iff
  onPoints_mapPoints from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ReductiveLieCentralizers
open private groupPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private onPoints_injective onPoints_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
open private unipotent_solvable from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private torus_split_of_algClosed torus_of_iso torus_smooth
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent
open LinearAlgebraicGroups.Specs.NontrivialRationalTorus
open LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.Specs.Relative.ReductiveLieCentralizers (IsMatrixCentralizer)
open LinearAlgebraicGroups.Specs.GeometricBorelConjugacy (IsReducedIdentityComponent)
open LinearAlgebraicGroups (faithfulLinearization identityLieStructure identityLieBracketMatrix
  adjointRepresentation lieMap lieFunctoriality)
open private smooth_coordinate_hopf from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private matrixDifferential_zero from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ReductiveLieCentralizers
open LinearAlgebraicGroups.Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.AdvCommAlg.Differentials.Tangent (PointLifts)

noncomputable section

variable {k : Type u} [Field k]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

private theorem exists_eval_ne_zero {σ : Type*} [Infinite k]
    {p : MvPolynomial σ k} (hp : p ≠ 0) :
    ∃ x : σ → k, MvPolynomial.aeval x p ≠ 0 := by
  by_contra! h
  apply hp
  apply MvPolynomial.funext
  intro x
  exact (h x).trans (map_zero _).symm

private theorem span_nonvanishing {σ : Type*} [Infinite k]
    (p : MvPolynomial σ k) (hp : p ≠ 0) :
    Submodule.span k {x : σ → k | MvPolynomial.aeval x p ≠ 0} = ⊤ := by
  let P := MvPolynomial σ k
  apply top_unique
  intro y _
  let t : P →ₐ[k] P := MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (y i))
  let s : P →ₐ[k] P := MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (y i))
  have hst : s.comp t = AlgHom.id k P := by
    apply MvPolynomial.algHom_ext
    intro i
    change s (t (MvPolynomial.X i)) = MvPolynomial.X i
    have h : t (MvPolynomial.X i) = MvPolynomial.X i + MvPolynomial.C (y i) :=
      MvPolynomial.aeval_X _ _
    rw [h, map_add]
    change MvPolynomial.aeval _ (MvPolynomial.X i) +
      MvPolynomial.aeval _ (MvPolynomial.C (y i)) = MvPolynomial.X i
    rw [MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    exact sub_add_cancel _ _
  have ht : Function.Injective t :=
    (show Function.LeftInverse s t from fun x => DFunLike.congr_fun hst x).injective
  have htp : t p ≠ 0 := by
    intro h
    apply hp
    exact ht (h.trans (map_zero t).symm)
  obtain ⟨x, hx⟩ := exists_eval_ne_zero (mul_ne_zero hp htp)
  rw [map_mul, mul_ne_zero_iff] at hx
  have hxt : MvPolynomial.aeval x (t p) = MvPolynomial.aeval (x + y) p := by
    change MvPolynomial.aeval x (MvPolynomial.aeval _ p) = _
    rw [MvPolynomial.comp_aeval_apply]
    have hh : (MvPolynomial.aeval (fun i : σ =>
        MvPolynomial.aeval x (MvPolynomial.X i + MvPolynomial.C (y i))) : P →ₐ[k] k) =
          MvPolynomial.aeval (x + y) := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X, map_add, MvPolynomial.aeval_X,
        MvPolynomial.aeval_C]
      rfl
    exact DFunLike.congr_fun hh p
  rw [hxt] at hx
  have h := (Submodule.span k {x : σ → k | MvPolynomial.aeval x p ≠ 0}).sub_mem
    (Submodule.subset_span hx.2) (Submodule.subset_span hx.1)
  simpa using h

private theorem reductive_of_semisimple (G : AffineAlgebraicGroup k) (hG : IsSemisimple G) :
    IsReductive G := by
  let U := geometricUnipotentRadical G
  have hu := GeometricRadicals.geometricUnipotentRadicalLargest G
  have hs := GeometricRadicals.geometricSolvableRadicalLargest G
  exact ⟨hG.1, hG.2.1, trivial_of_le_trivial
    (hs.2.2 U hu.1 (unipotent_solvable (closedSubgroupAlgebraicGroup U)
      hu.1.1 hu.1.2.1 hu.2.1)) hG.2.2⟩

private theorem torus_of_no_noncentral_semisimple [CharZero k] (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (hn : ¬ HasGeometricNoncentralSemisimple G) : IsTorus G.val := by
  letI := hG.2.1
  have hc := GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  let K := AlgebraicClosure k
  let H := GeometricGroup G
  have hH : IsReductive H := geometricGroupReductive G hG
  letI := hH.2.1
  have hcH := GeometricallyConnected.connectedSpace_of_subsingleton H.val.X.hom
  obtain ⟨T, hT⟩ := maximalTorus_exists H hH.1 hcH
  have hm := maximalTorus_over_closure H T hT
  have hcent := LinearAlgebraicGroups.Reductive.TorusCentralizer.maximalTorusCentralizer H hH T hT.1 hm
  have hcentral := central_in_charZero G hG.1 hc T hT hn
  obtain ⟨a, ha⟩ := (hcent H.val.X (𝟙 H.val.X)).mp (hcentral _ _)
  let b := T.inclusion.hom.hom
  haveI : Mono b := by
    letI := T.isClosedImmersion
    exact Over.mono_of_mono_left b
  have hba : b ≫ a = 𝟙 _ := by
    apply (cancel_mono b).mp
    simp [Category.assoc, show a ≫ b = 𝟙 _ from ha]
  letI : IsIso b := ⟨a, hba, ha⟩
  haveI : IsIso T.inclusion :=
    by
      exact (inferInstance : IsIso (Grp.mkIso (asIso b)
        (IsMonHom.one_hom (f := b)) (IsMonHom.mul_hom (f := b))).hom)
  have ht := torus_of_iso (asIso T.inclusion) hT.1
  exact ⟨K, inferInstance, inferInstance, inferInstance, torus_split_of_algClosed H ht⟩

private theorem matrixCentralizer_lie {G L : GroupScheme k} {I : Type u}
    [Fintype I] [DecidableEq I]
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I)
    (f : G ⟶ L) (y : Specs.Lie k G) (C : ClosedSubgroup G)
    (hC : IsMatrixCentralizer l f (InfinitesimalCommutator.matrixDifferential f l y) C)
    (x : Specs.Lie k G) :
    (∃ z : Specs.Lie k C.group, mapPointKernel C.inclusion z = x) ↔
      Commute (InfinitesimalCommutator.matrixDifferential f l x)
        (InfinitesimalCommutator.matrixDifferential f l y) := by
  rw [commute_matrixDifferentials_iff l f]
  let R := CommAlgCat.of k (DualNumber k)
  refine ⟨?_, ?_⟩
  · rintro ⟨z, rfl⟩
    apply (hC R _).mp
    exact ⟨z.toMul.val, rfl⟩
  · intro hx
    obtain ⟨z, hz⟩ := (hC R x.toMul.val).mpr hx
    have hz₁ : reduceTangentPoints C.group z = 1 := by
      apply onPoints_injective C.inclusion C.isClosedImmersion (CommAlgCat.of k k)
      change onPoints C.inclusion (CommAlgCat.of k k) (mapPoints (dualReduction k) z) =
        onPoints C.inclusion (CommAlgCat.of k k) 1
      rw [← onPoints_mapPoints,
        show onPoints C.inclusion R z = x.toMul.val from hz, map_one]
      exact x.toMul.property
    exact ⟨⟨z, hz₁⟩, Subtype.ext hz⟩

private theorem span_of_open {V : Type u} {I : Type u} [AddCommGroup V] [Module k V] [Infinite k] [Finite I]
    (b : Module.Basis I k V) (W : Submodule k V) (p : MvPolynomial I k) (hp : p ≠ 0)
    (h : ∀ x : V, MvPolynomial.aeval (b.equivFun x) p ≠ 0 → x ∈ W) : W = ⊤ := by
  classical
  let W' := W.comap b.equivFun.symm.toLinearMap
  have hspan : Submodule.span k {v : I → k | MvPolynomial.aeval v p ≠ 0} ≤ W' := by
    apply Submodule.span_le.mpr
    intro v hv
    exact h (b.equivFun.symm v) (by simpa using hv)
  rw [span_nonvanishing p hp] at hspan
  apply top_unique
  intro x _
  have hx : b.equivFun x ∈ W' := hspan (Submodule.mem_top)
  change b.equivFun.symm (b.equivFun x) ∈ W at hx
  simpa only [LinearEquiv.symm_apply_apply] using hx


private def toralVectors (G : AffineAlgebraicGroup k) : Set (Specs.Lie k G.val) :=
  { x | ∃ T : ClosedSubgroup G.val, IsTorus T.group ∧
      ∃ z : Specs.Lie k T.group, mapPointKernel T.inclusion z = x }

private theorem centralizer_lie_of_bracket {G L : AffineGroupCategory k}
    (s : IdentityLieStructure G.val) {I : Type u} [Fintype I] [DecidableEq I]
    (l : (groupPointsFunctor k).obj L.val ≅ StandardGroups.generalLinearPoints k I)
    (f : G.val ⟶ L.val) (hf : IsClosedImmersion f.hom.hom.left)
    (y : Specs.Lie k G.val) (C : ClosedSubgroup G.val)
    (hC : IsMatrixCentralizer l f (InfinitesimalCommutator.matrixDifferential f l y) C) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ x : Specs.Lie k G.val, (∃ z : Specs.Lie k C.group, mapPointKernel C.inclusion z = x)
      ↔ ⁅x, y⁆ = 0 := by
  letI := s.lieRing
  letI := s.lieAlgebra
  intro x
  letI : IsAffine G.val.X.left := G.property
  letI : IsAffine L.val.X.left := L.property
  let d := InfinitesimalCommutator.matrixDifferential f l
  obtain ⟨hinj, hbr⟩ := identityLieBracketMatrix k G.val L.val I f l hf
  have h (z : Specs.Lie k G.val) : d ⁅z, y⁆ = d z * d y - d y * d z := hbr s z y
  have hz : d (0 : Specs.Lie k G.val) = 0 := matrixDifferential_zero f l
  rw [matrixCentralizer_lie l f y C hC x]
  change Commute (d x) (d y) ↔ ⁅x, y⁆ = 0
  constructor
  · intro hc
    apply hinj
    change d ⁅x, y⁆ = d 0
    rw [h, hz]
    exact sub_eq_zero.mpr hc.eq
  · intro he
    have h' := (h x).symm
    rw [he, hz] at h'
    exact sub_eq_zero.mp h'

/-- The proper reductive centralizer supplies each Lie vector with nonnilpotent
adjoint, using the semisimple part of the vector for the centralizing equation. -/
private theorem proper_reductive_subgroup_of_nonnilpotent [CharZero k]
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (x : Specs.Lie k G.val)
    (hx : letI := (identityLieStructure G).lieRing
          letI := (identityLieStructure G).lieAlgebra
          ¬ IsNilpotent (LieAlgebra.ad k (Specs.Lie k G.val) x)) :
    ∃ D : ClosedSubgroup G.val, IsReductive (closedSubgroupAlgebraicGroup D) ∧
      groupDimension (closedSubgroupAlgebraicGroup D) < groupDimension G ∧
      ∃ w : Specs.Lie k D.group, mapPointKernel D.inclusion w = x := by
  classical
  let s := identityLieStructure G
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := hG.2.1
  have hc := GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  obtain ⟨r, L, ⟨l⟩, f, hf⟩ := faithfulLinearization k G
  let G' : AffineGroupCategory k := ⟨G.val, G.property.1⟩
  let L' : AffineGroupCategory k := ⟨L.val, L.property.1⟩
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation G
  letI : Algebra.Smooth k A := smooth_coordinate_hopf e hG.1
  let E := hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso e
  obtain ⟨y, hy, hxy, hny, _, _⟩ := rationalSemisimpleWitness k G L' s
    A E (ULift.{u} (Fin r)) l f hf x hx
  obtain ⟨C, hC, _, H, _, ho, hH⟩ :=
    LinearAlgebraicGroups.Relative.ReductiveLieCentralizers.semisimpleLieCentralizerComponentReductive
      k G hG (ULift.{u} (Fin r)) L' l f hf y hy
  let D := subgroupOfSubgroup C H
  have hLie := centralizer_lie_of_bracket (G := G') (L := L') s l f hf y C hC
  have hProper : ¬ IsIso D.inclusion := by
    intro hi
    letI := hi
    apply hny
    apply LinearMap.ext
    intro v
    have he := (lieFunctoriality k).2.2 _ _ _ (inv D.inclusion) D.inclusion v
    rw [IsIso.inv_hom_id, (lieFunctoriality k).2.1] at he
    have he' := (lieFunctoriality k).2.2 _ _ _ H.inclusion C.inclusion
      (mapPointKernel (inv D.inclusion) v)
    have hv := (hLie v).mp ⟨mapPointKernel H.inclusion
      (mapPointKernel (inv D.inclusion) v), he'.symm.trans he.symm⟩
    change ⁅y, v⁆ = 0
    exact (lie_skew y v).symm.trans (neg_eq_zero.mpr hv)
  obtain ⟨v, hv⟩ := (hLie x).mpr hxy
  obtain ⟨w, hw⟩ := tangent_surjective_of_open H ho v
  refine ⟨D, hH, groupDimension_lt_of_proper hG.1 hc D hProper, w, ?_⟩
  exact ((lieFunctoriality k).2.2 _ _ _ H.inclusion C.inclusion w).trans
    ((congrArg (mapPointKernel C.inclusion) hw).trans hv)

private theorem adjoint_nonnilpotent_spans [CharZero k] (G : AffineAlgebraicGroup k)
    [IsAffine G.val.X.left] (h : HasGeometricNoncentralSemisimple G) (W : Submodule k (Specs.Lie k G.val))
    (hW : ∀ x : Specs.Lie k G.val,
      (letI := (identityLieStructure G).lieRing
       letI := (identityLieStructure G).lieAlgebra
       ¬ IsNilpotent (LieAlgebra.ad k (Specs.Lie k G.val) x)) → x ∈ W) :
    W = ⊤ := by
  letI : IsAffine G.val.X.left := G.property.1
  let s := identityLieStructure G
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : Infinite k := Infinite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
  obtain ⟨n, b, -⟩ := adjointRepresentation k G s
  let I := ULift.{u} (Fin n)
  let M := genericMatrix (adjointMatrixFamily b)
  obtain ⟨_, hmem, hex⟩ := adjointNonnilpotentOpen k G s I b
  obtain ⟨x, hx⟩ := (hex h).2 inferInstance
  let q := M.charpoly - Polynomial.X ^ Fintype.card I
  change ¬ Set.range q.coeff ⊆ (RingHom.ker
    (MvPolynomial.aeval (b.equivFun x) : MvPolynomial I k →ₐ[k] k).toRingHom : Set _) at hx
  obtain ⟨_, ⟨j, rfl⟩, hj⟩ := Set.not_subset.mp hx
  have hp : q.coeff j ≠ 0 := by
    intro hz
    apply hj
    simp [hz]
  apply span_of_open b W (q.coeff j) hp
  intro z hz
  apply hW z
  apply (hmem z).mp
  change ¬ Set.range q.coeff ⊆ (RingHom.ker
    (MvPolynomial.aeval (b.equivFun z) : MvPolynomial I k →ₐ[k] k).toRingHom : Set _)
  intro hs
  exact hz (hs (Set.mem_range_self j))

private theorem toral_vectors_span [CharZero k] (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) :
    letI : IsAffine G.val.X.left := G.property.1
    Submodule.span k (toralVectors G) = ⊤ := by
  classical
  have key (d : ℕ) (A : AffineAlgebraicGroup k) (hA : IsReductive A)
      (hd : groupDimension A = d) :
      letI : IsAffine A.val.X.left := A.property.1
      Submodule.span k (toralVectors A) = ⊤ := by
    induction d using Nat.strong_induction_on generalizing A with
    | h d ih =>
      letI : IsAffine A.val.X.left := A.property.1
      by_cases h : HasGeometricNoncentralSemisimple A
      · apply adjoint_nonnilpotent_spans A h
        intro x hx
        obtain ⟨D, hD, hlt, w, hw⟩ := proper_reductive_subgroup_of_nonnilpotent A hA x hx
        let B := closedSubgroupAlgebraicGroup D
        letI : IsAffine D.group.X.left := B.property.1
        letI : IsAffine B.val.X.left := B.property.1
        have hB : Submodule.span k (toralVectors B) = ⊤ :=
          ih (groupDimension B) (hd ▸ hlt) B hD rfl
        let F := lieMap D.inclusion
        have hle : Submodule.span k (toralVectors B) ≤
            (Submodule.span k (toralVectors A)).comap F := by
          apply Submodule.span_le.mpr
          rintro _ ⟨T, hT, z, rfl⟩
          apply Submodule.subset_span
          exact ⟨subgroupOfSubgroup D T, hT, z,
            (lieFunctoriality k).2.2 _ _ _ T.inclusion D.inclusion z⟩
        have hws : w ∈ Submodule.span k (toralVectors B) := by rw [hB]; trivial
        have hfw : F w ∈ Submodule.span k (toralVectors A) := hle hws
        have hw' : F w = x := hw
        exact hw' ▸ hfw
      · apply top_unique
        intro x _
        let E : ClosedSubgroup A.val := ⟨A.val, 𝟙 _, by
          change IsClosedImmersion (𝟙 A.val.X.left)
          infer_instance⟩
        exact Submodule.subset_span
          ⟨E, torus_of_no_noncentral_semisimple A hA h, x, (lieFunctoriality k).2.1 _ _⟩
  exact key (groupDimension G) G hG rfl


private theorem finite_tori_span [CharZero k] (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) :
    letI : IsAffine G.val.X.left := G.property.1
    ∃ (m : ℕ) (T : Fin m → ClosedSubgroup G.val), (∀ i, IsTorus (T i).group) ∧
      ∀ y : Specs.Lie k G.val, ∃ x : ∀ i, Specs.Lie k (T i).group,
        (∑ i, mapPointKernel (T i).inclusion (x i)) = y := by
  classical
  letI : IsAffine G.val.X.left := G.property.1
  let s := identityLieStructure G
  obtain ⟨n, b, -⟩ := adjointRepresentation k G s
  letI : Module.Finite k (Specs.Lie k G.val) := Module.Finite.of_basis b
  let S := toralVectors G
  have hs : Submodule.span k S = ⊤ := toral_vectors_span G hG
  obtain ⟨b', hb', hspan, _⟩ := Submodule.exists_fun_fin_finrank_span_eq k S
  choose T hT z hz using hb'
  let m := Module.finrank k (Submodule.span k S)
  refine ⟨m, T, hT, ?_⟩
  let V (i : Fin m) := Specs.Lie k (T i).group
  letI (i : Fin m) : IsAffine (T i).group.X.left := (closedSubgroupAlgebraicGroup (T i)).property.1
  let L := LinearMap.lsum k V k (fun i => lieMap (T i).inclusion)
  have hle : Submodule.span k (Set.range b') ≤ LinearMap.range L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i (z i), (LinearMap.lsum_piSingle (R := k) (φ := V) k (fun j => lieMap (T j).inclusion) i _).trans (hz i)⟩
  intro y
  obtain ⟨w, hw⟩ := hle (by rw [hspan, hs]; exact Submodule.mem_top (x := y))
  refine ⟨w, ?_⟩
  simp only [L, LinearMap.lsum_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply] at hw
  exact hw

private def precomposePoints {X Y : SchemeOver k} {G : GroupScheme k} (a : X ⟶ Y) :
    (Y ⟶ G.X) →* (X ⟶ G.X) where
  toFun f := a ≫ f
  map_one' := MonObj.comp_one a
  map_mul' x y := MonObj.comp_mul a x y

private theorem ordered_product_point {G : AffineAlgebraicGroup k} {m : ℕ}
    (T : Fin m → ClosedSubgroup G.val) {X : SchemeOver k}
    (x : ∀ i, X ⟶ (T i).group.X) :
    Pi.lift x ≫ orderedSubgroupProduct T =
      (List.ofFn (fun i => x i ≫ (T i).inclusion.hom.hom)).prod := by
  let f := precomposePoints (G := G.val) (Pi.lift x)
  change f ((List.ofFn _).prod) = _
  rw [map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  change Pi.lift x ≫ Pi.π (fun j => (T j).group.X) i ≫ (T i).inclusion.hom.hom = _
  rw [← Category.assoc, Pi.lift_comp_π]

private theorem ordered_product_lifts {G : AffineAlgebraicGroup k} {m : ℕ}
    (T : Fin m → ClosedSubgroup G.val)
    (hs : letI : IsAffine G.val.X.left := G.property.1
      ∀ y : Specs.Lie k G.val, ∃ x : ∀ i, Specs.Lie k (T i).group,
        (∑ i, mapPointKernel (T i).inclusion (x i)) = y) :
    let a : Points (∏ᶜ fun i => (T i).group.X) (CommAlgCat.of k k) := Pi.lift (fun _ => 1)
    a ≫ orderedSubgroupProduct T = 1 ∧
      ∀ y : Points G.val.X (CommAlgCat.of k (DualNumber k)),
        mapPoints (dualReduction k) y = 1 →
        ∃ x : Points (∏ᶜ fun i => (T i).group.X) (CommAlgCat.of k (DualNumber k)),
          mapPoints (dualReduction k) x = a ∧ x ≫ orderedSubgroupProduct T = y := by
  letI : IsAffine G.val.X.left := G.property.1
  classical
  dsimp only
  constructor
  · rw [ordered_product_point]
    have he (i : Fin m) :
        (1 : Points (T i).group.X (CommAlgCat.of k k)) ≫ (T i).inclusion.hom.hom = 1 :=
      map_one (IsMonHom.monoidHom (T i).inclusion.hom.hom _)
    simp only [he, List.ofFn_const, List.prod_replicate, one_pow]
  · intro y hy
    let v : Specs.Lie k G.val := Additive.ofMul ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hs v
    let R := CommAlgCat.of k (DualNumber k)
    refine ⟨Pi.lift (fun i => (x i).toMul.val), ?_, ?_⟩
    · apply Pi.hom_ext
      intro i
      change (testSpec k).map (dualReduction k).op ≫
        Pi.lift (fun i => (x i).toMul.val) ≫ Pi.π _ i =
          Pi.lift (fun j => (1 : Points (T j).group.X (CommAlgCat.of k k))) ≫ Pi.π _ i
      rw [Pi.lift_comp_π, Pi.lift_comp_π]
      exact (x i).toMul.property
    · rw [ordered_product_point]
      let incl : Specs.Lie k G.val →+ Additive (Points G.val.X R) :=
        (Subgroup.subtype (reduceTangentPoints G.val).ker).toAdditive
      rw [← List.sum_ofFn] at hx
      have h := congrArg (fun w => (incl w).toMul) hx
      rw [map_list_sum, toMul_list_sum, List.map_map, List.map_ofFn] at h
      exact h

private theorem affine_product {m : ℕ} (X : Fin m → SchemeOver k)
    (hX : ∀ i, IsAffine (X i).left) : IsAffine (∏ᶜ X).left := by
  classical
  choose R e using fun i =>
    (AlgebraicGeometry.essImage_algSpec (R := CommRingCat.of k)).mpr (hX i)
  let F := testSpec k
  letI : PreservesLimitsOfSize.{0, 0} F := AlgebraicGeometry.preservesLimitsOfSize_algSpec
  let j : F.obj (∏ᶜ R) ≅ ∏ᶜ X :=
    PreservesProduct.iso F R ≪≫ Pi.mapIso (fun i => (e i).some)
  have hAff : IsAffine (F.obj (∏ᶜ R)).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (∏ᶜ R).unop)))
  let j' : (F.obj (∏ᶜ R)).left ≅ (∏ᶜ X).left := (Over.forget _).mapIso j
  exact @IsAffine.of_isIso _ _ j'.inv j'.isIso_inv hAff

private theorem smooth_torus_product [CharZero k] {G : AffineAlgebraicGroup k} {m : ℕ}
    (T : Fin m → ClosedSubgroup G.val) (hT : ∀ i, IsTorus (T i).group) :
    Smooth (∏ᶜ fun i => (T i).group.X).hom := by
  let X (i : Fin m) := (T i).group.X
  let I := ULift.{u} (Fin m)
  let G' (i : I) := closedSubgroupAlgebraicGroup (T i.down)
  have hi (i : I) : Smooth (G' i).val.X.hom ∧ ConnectedSpace (G' i).val.X.left := by
    refine ⟨torus_smooth (G' i) (hT i.down), ?_⟩
    obtain ⟨E, _, _, _, hE⟩ := hT i.down
    let A := baseChangedAlgebraicGroup E (G' i)
    haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap k E).injective
    haveI : ConnectedSpace A.val.X.left :=
      (EquivariantUnipotentSeries.split_torus_smooth_connected A hE).2
    let p : A.val.X.left ⟶ (G' i).val.X.left :=
      pullback.fst (G' i).val.X.hom (fieldSpecMap k E)
    haveI : Surjective (fieldSpecMap k E) :=
      ⟨fun x => ⟨IsLocalRing.closedPoint E, Subsingleton.elim _ _⟩⟩
    haveI : Surjective p := inferInstanceAs
      (Surjective (pullback.fst (G' i).val.X.hom (fieldSpecMap k E)))
    exact p.surjective.connectedSpace p.continuous
  have hs := (WordDomainGeometry.smoothConnectedGroupFiniteProduct I G' hi).1
  let e : (∏ᶜ fun i : I => X i.down) ≅ ∏ᶜ X := Pi.reindex Equiv.ulift X
  letI := hs
  haveI : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  rw [← Over.w e.inv]
  exact MorphismProperty.comp_mem @Smooth _ _ inferInstance hs

section Coordinates

open Ideal LinearMap

variable {A B C : Type u}
  [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]

private def augPart (e : A →ₐ[k] k) : A →ₗ[k] RingHom.ker e.toRingHom :=
  (LinearMap.id - (Algebra.linearMap k A).comp e.toLinearMap).codRestrict
    ((RingHom.ker e.toRingHom).restrictScalars k) (fun a => by
      change e (a - algebraMap k A (e a)) = 0
      rw [map_sub, e.commutes, Algebra.algebraMap_self_apply, sub_self])

private lemma augPart_apply (e : A →ₐ[k] k) (a : A) :
    (augPart e a : A) = a - algebraMap k A (e a) := rfl

private def cotAt (e : A →ₐ[k] k) : A →ₗ[k] PointCotangent e :=
  ((RingHom.ker e.toRingHom).toCotangent.restrictScalars k).comp (augPart e)

private lemma cotAt_mul (e : A →ₐ[k] k) (a b : A) :
    cotAt e (a * b) = e a • cotAt e b + e b • cotAt e a := by
  let m := RingHom.ker e.toRingHom
  let p := augPart e
  have h : p (a*b) = e a • p b + e b • p a + p a * p b := by
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_add]
    change (p (a*b) : A) = e a • (p b : A) + e b • (p a : A) + (p a : A) * (p b : A)
    dsimp only [p]
    simp only [augPart_apply, Algebra.smul_def, map_mul]
    ring
  have hz : m.toCotangent (p a * p b) = 0 :=
    (m.toCotangent_eq_zero _).mpr (by rw [pow_two]; exact Ideal.mul_mem_mul (p a).2 (p b).2)
  let q := m.toCotangent.restrictScalars k
  change q (p (a*b)) = e a • q (p b) + e b • q (p a)
  rw [h, map_add, map_add, map_smul, map_smul, show q (p a * p b) = 0 from hz, add_zero]

private lemma cotAt_algebraMap (e : A →ₐ[k] k) (t : k) :
    cotAt e (algebraMap k A t) = 0 := by
  have h : augPart e (algebraMap k A t) = 0 := by
    apply Subtype.ext
    change (augPart e (algebraMap k A t) : A) = 0
    rw [augPart_apply, e.commutes, Algebra.algebraMap_self_apply, sub_self]
  exact (congrArg ((RingHom.ker e.toRingHom).toCotangent) h).trans (map_zero _)

private lemma cotangent_image_mul (e : A →ₐ[k] k) (x y : PointCotangent e) :
    (RingHom.ker e.toRingHom).cotangentToQuotientSquare x *
      (RingHom.ker e.toRingHom).cotangentToQuotientSquare y = 0 := by
  let m := RingHom.ker e.toRingHom
  obtain ⟨a, rfl⟩ := m.toCotangent_surjective x
  obtain ⟨b, rfl⟩ := m.toCotangent_surjective y
  change m.cotangentToQuotientSquare (m.toCotangent a) *
    m.cotangentToQuotientSquare (m.toCotangent b) = 0
  rw [m.toCotangent_to_quotient_square, m.toCotangent_to_quotient_square]
  change Ideal.Quotient.mk (m^2) (a : A) * Ideal.Quotient.mk (m^2) (b : A) = 0
  rw [← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [pow_two]; exact Ideal.mul_mem_mul a.2 b.2)

private lemma cotAt_decompose (e : A →ₐ[k] k) (a : A) :
    algebraMap k (A ⧸ (RingHom.ker e.toRingHom)^2) (e a) +
      (RingHom.ker e.toRingHom).cotangentToQuotientSquare (cotAt e a) =
        Ideal.Quotient.mk ((RingHom.ker e.toRingHom)^2) a := by
  change algebraMap k _ (e a) + (RingHom.ker e.toRingHom).cotangentToQuotientSquare
    ((RingHom.ker e.toRingHom).toCotangent (augPart e a)) = _
  rw [Ideal.toCotangent_to_quotient_square, augPart_apply]
  let q := Ideal.Quotient.mk ((RingHom.ker e.toRingHom)^2)
  change algebraMap k _ (e a) + q (a - algebraMap k A (e a)) = q a
  rw [map_sub, Ideal.Quotient.mk_algebraMap]
  abel

private lemma cotangent_injective_of_lifts (f : A →ₐ[k] B) (ea : A →ₐ[k] k)
    (eb : B →ₐ[k] k) (he : eb.comp f = ea)
    (hlift : ∀ g : PointLifts k A k ea, ∃ h : PointLifts k B k eb, h.val.comp f = g.val) :
    Function.Injective
      (Ideal.mapCotangent (RingHom.ker ea.toRingHom) (RingHom.ker eb.toRingHom) f
        (fun a ha => show eb (f a) = 0 from (DFunLike.congr_fun he a).trans ha)) := by
  let ma := RingHom.ker ea.toRingHom
  let mb := RingHom.ker eb.toRingHom
  let hm : ma ≤ mb.comap f := fun a ha => show eb (f a) = 0 from
    (DFunLike.congr_fun he a).trans ha
  let F := Ideal.mapCotangent ma mb f hm
  change Function.Injective F
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  intro z hz
  change F z = 0 at hz
  obtain ⟨a, rfl⟩ := ma.toCotangent_surjective z
  change ma.toCotangent a = 0
  by_contra hne
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero k hne
  obtain ⟨ea', hea, _⟩ := pointTangentLifts k A ea
  obtain ⟨eb', heb, _⟩ := pointTangentLifts k B eb
  obtain ⟨h, hh⟩ := hlift (ea' l)
  obtain ⟨l', rfl⟩ := eb'.surjective h
  apply hl
  rw [← hea l a, ← DFunLike.congr_fun hh (a : A)]
  change ((eb' l').val (f a)).snd = 0
  rw [heb l' ⟨f a, hm a.2⟩]
  rw [show mb.toCotangent ⟨f a, hm a.2⟩ = 0 from hz, map_zero]

private lemma firstOrder_retraction (f : A →ₐ[k] B) (ea : A →ₐ[k] k)
    (eb : B →ₐ[k] k) (he : eb.comp f = ea)
    (hlift : ∀ g : PointLifts k A k ea, ∃ h : PointLifts k B k eb, h.val.comp f = g.val) :
    ∃ g : B →ₐ[k] A ⧸ (RingHom.ker ea.toRingHom)^2,
      g.comp f = Ideal.Quotient.mkₐ k _ := by
  let ma := RingHom.ker ea.toRingHom
  let mb := RingHom.ker eb.toRingHom
  let hm : ma ≤ mb.comap f := fun a ha => show eb (f a) = 0 from
    (DFunLike.congr_fun he a).trans ha
  let F := Ideal.mapCotangent ma mb f hm
  obtain ⟨r, hr⟩ := F.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (cotangent_injective_of_lifts f ea eb he hlift))
  let Q := A ⧸ ma^2
  let j := ma.cotangentToQuotientSquare.restrictScalars k
  let d := j.comp (r.comp (cotAt eb))
  let c := (Algebra.ofId k Q).comp eb
  have hd (b₁ b₂ : B) : d (b₁ * b₂) = eb b₁ • d b₂ + eb b₂ • d b₁ := by
    change (j.comp r) (cotAt eb (b₁ * b₂)) = _
    rw [cotAt_mul, map_add, map_smul, map_smul]
    rfl
  have hdc (b₁ b₂ : B) : d b₁ * d b₂ = 0 :=
    cotangent_image_mul ea _ _
  let g : B →ₐ[k] Q := AlgHom.ofLinearMap (c.toLinearMap + d)
    (by
      change c 1 + d 1 = 1
      have h : d (algebraMap k B 1) = 0 := by
        change (j.comp r) (cotAt eb (algebraMap k B 1)) = 0
        rw [cotAt_algebraMap, map_zero]
      rw [map_one] at h
      rw [map_one, h, add_zero])
    (fun b₁ b₂ => by
      change c (b₁*b₂) + d (b₁*b₂) = (c b₁ + d b₁) * (c b₂ + d b₂)
      rw [map_mul, hd, Algebra.smul_def, Algebra.smul_def, add_mul, mul_add, mul_add, hdc, add_zero]
      change c b₁ * c b₂ + (c b₁ * d b₂ + c b₂ * d b₁) = _
      ring)
  refine ⟨g, ?_⟩
  ext a
  change c (f a) + d (f a) = _
  have hc : c (f a) = algebraMap k Q (ea a) :=
    congrArg (algebraMap k Q) (DFunLike.congr_fun he a)
  have hq : cotAt eb (f a) = F (cotAt ea a) := by
    change mb.toCotangent (augPart eb (f a)) = F (ma.toCotangent (augPart ea a))
    rw [show F = Ideal.mapCotangent ma mb f hm from rfl, Ideal.mapCotangent_toCotangent]
    congr 1
    apply Subtype.ext
    change (augPart eb (f a) : B) = f (augPart ea a)
    simp only [augPart_apply, map_sub, f.commutes]
    rw [show eb (f a) = ea a from DFunLike.congr_fun he a]
  have hda : d (f a) = j (cotAt ea a) := by
    change j (r (cotAt eb (f a))) = _
    rw [hq]
    exact congrArg j (LinearMap.congr_fun hr (cotAt ea a))
  rw [hc, hda]
  exact cotAt_decompose ea a

/-- Two maps agreeing to first order differ one step further on each ideal power. -/
private lemma sub_mem_pow_succ (p q : A →ₐ[k] C) (I : Ideal A) (J : Ideal C)
    (hp : I ≤ J.comap p) (hq : I ≤ J.comap q)
    (hd : ∀ x ∈ I, p x - q x ∈ J^2) :
    ∀ (n : ℕ) (x : A), x ∈ I^(n+1) → p x - q x ∈ J^(n+2) := by
  have hpow (a : A →ₐ[k] C) (ha : I ≤ J.comap a) (n : ℕ) :
      I^n ≤ (J^n).comap a := by
    apply Ideal.map_le_iff_le_comap.mp
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr ha) _
  intro n
  induction n with
  | zero => simpa using hd
  | succ n ih =>
    intro x hx
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [map_mul, map_mul, show p a * p b - q a * q b =
        (p a - q a) * p b + q a * (p b - q b) by ring]
      apply Ideal.add_mem
      · have h₁ : (p a - q a) * p b ∈ J^2 * J^(n+1) :=
          Ideal.mul_mem_mul (hd a ha) (hpow p hp (n+1) hb)
        rw [← pow_add, show 2 + (n+1) = n+1+2 by omega] at h₁
        exact h₁
      · have h₂ : q a * (p b - q b) ∈ J * J^(n+2) :=
          Ideal.mul_mem_mul (hq ha) (ih b hb)
        rw [← pow_succ', show (n+2)+1 = n+1+2 by omega] at h₂
        exact h₂
    · intro a b ha hb
      simp only [map_add, add_sub_add_comm]
      exact Ideal.add_mem _ ha hb

/-- First-order surjectivity onto the target at a rational point forces
injectivity of coordinates when the source is smooth and the target integral. -/
private theorem injective_of_pointLifts [IsNoetherianRing A] [IsDomain A]
    [Algebra.FormallySmooth k B] (f : A →ₐ[k] B) (ea : A →ₐ[k] k) (eb : B →ₐ[k] k)
    (he : eb.comp f = ea)
    (hlift : ∀ g : PointLifts k A k ea, ∃ h : PointLifts k B k eb, h.val.comp f = g.val) :
    Function.Injective f := by
  let m := RingHom.ker ea.toRingHom
  let q (n : ℕ) : A →ₐ[k] A ⧸ m^n := Ideal.Quotient.mkₐ k _
  have mproper : m ≠ ⊤ := RingHom.ker_ne_top ea.toRingHom
  obtain ⟨g, hg⟩ := firstOrder_retraction f ea eb he hlift
  refine (injective_iff_map_eq_zero f).mpr ?_
  intro a ha
  apply Ideal.mem_bot.mp
  rw [← Ideal.iInf_pow_eq_bot_of_isDomain m mproper, Ideal.mem_iInf]
  intro n
  cases n with
  | zero => simp
  | succ n =>
    induction n with
    | zero =>
      rw [pow_one]
      change ea a = 0
      exact (DFunLike.congr_fun he a).symm.trans (by change eb (f a) = 0; rw [ha, map_zero])
    | succ n hn =>
      let N := n+2
      let R := A ⧸ m^N
      have hN : (2 : ℕ) ≤ N := by dsimp [N]; omega
      have hNM : m^N ≤ m^2 := Ideal.pow_le_pow_right hN
      let π : R →ₐ[k] A ⧸ m^2 := Ideal.Quotient.factorₐ k hNM
      let J : Ideal R := m.map (q N)
      have hJ (i : ℕ) : J^i = (m^i).map (q N) := (Ideal.map_pow _ _ _).symm
      have hker : RingHom.ker π.toRingHom = J^2 := by
        rw [hJ]
        exact Ideal.Quotient.factor_ker hNM
      have hnil : IsNilpotent (RingHom.ker π.toRingHom) := by
        refine ⟨N, ?_⟩
        rw [hker, ← pow_mul]
        apply eq_bot_iff.mpr
        rw [hJ]
        exact (Ideal.map_mono (Ideal.pow_le_pow_right (by omega))).trans
          (Ideal.map_quotient_self _).le
      have hsur : Function.Surjective π := Ideal.Quotient.factor_surjective hNM
      let g' := Algebra.FormallySmooth.liftOfSurjective g π hsur hnil
      let p := g'.comp f
      have hd (x : A) : p x - q N x ∈ J^2 := by
        rw [← hker]
        change π (p x - q N x) = 0
        rw [map_sub]
        change π (g' (f x)) - q 2 x = 0
        rw [Algebra.FormallySmooth.liftOfSurjective_apply, show g (f x) = q 2 x from DFunLike.congr_fun hg x,
          sub_self]
      have hq : m ≤ J.comap (q N) := Ideal.le_comap_map
      have hp : m ≤ J.comap p := by
        intro x hx
        change p x ∈ J
        rw [← sub_add_cancel (p x) (q N x)]
        exact J.add_mem (Ideal.pow_le_self (by decide) (hd x)) (hq hx)
      have hx := sub_mem_pow_succ p (q N) m J hp hq (fun x _ => hd x) n a hn
      change a ∈ m^N
      rw [hJ] at hx
      change p a - q N a ∈ (m^N).map (Ideal.Quotient.mk (m^N)) at hx
      rw [Ideal.map_quotient_self] at hx
      change p a - q N a = 0 at hx
      have hpzero : p a = 0 := by change g' (f a) = 0; rw [ha, map_zero]
      rw [hpzero, zero_sub, neg_eq_zero] at hx
      exact Ideal.Quotient.eq_zero_iff_mem.mp hx


end Coordinates

private abbrev affineSpec (A : TestAlgebra k) : SchemeOver k :=
  (testSpec k).obj (op A)

private abbrev affineSpecMap {A B : TestAlgebra k} (f : A →ₐ[k] B) :
    affineSpec B ⟶ affineSpec A :=
  (testSpec k).map (CommAlgCat.ofHom f).op

private def coordinates {A B : TestAlgebra k} (f : affineSpec B ⟶ affineSpec A) :
    A →ₐ[k] B :=
  ((AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of k)).preimage f).unop.hom

private theorem affineSpecMap_coordinates {A B : TestAlgebra k} (f : affineSpec B ⟶ affineSpec A) :
    affineSpecMap (coordinates f) = f :=
  (AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage f

private theorem affineSpecMap_injective {A B : TestAlgebra k} :
    Function.Injective (affineSpecMap (A := A) (B := B)) := by
  intro f g h
  have h' := (AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective h
  exact congrArg (fun j : op B ⟶ op A => j.unop.hom) h'

private theorem affineSpecMap_comp {A B C : TestAlgebra k}
    (f : B →ₐ[k] C) (g : A →ₐ[k] B) :
    affineSpecMap (f.comp g) = affineSpecMap f ≫ affineSpecMap g :=
  (testSpec k).map_comp (CommAlgCat.ofHom f).op (CommAlgCat.ofHom g).op

private theorem dominant_of_point_lifts {X Y : SchemeOver k}
    (f : X ⟶ Y) (a : Points X (CommAlgCat.of k k))
    (hs : Smooth X.hom) (hx : IsAffine X.left) (hy : IsAffine Y.left) (hi : IsIntegral Y.left)
    (ht : LocallyOfFiniteType Y.hom)
    (hl : ∀ y : Points Y (CommAlgCat.of k (DualNumber k)),
      mapPoints (dualReduction k) y = a ≫ f →
      ∃ x : Points X (CommAlgCat.of k (DualNumber k)),
        mapPoints (dualReduction k) x = a ∧ x ≫ f = y) :
    IsDominant f.left := by
  obtain ⟨Aop, ⟨eA⟩⟩ := (AlgebraicGeometry.essImage_algSpec (R := CommRingCat.of k)).mpr hy
  obtain ⟨Bop, ⟨eB⟩⟩ := (AlgebraicGeometry.essImage_algSpec (R := CommRingCat.of k)).mpr hx
  let A := Aop.unop
  let B := Bop.unop
  change affineSpec A ≅ Y at eA
  change affineSpec B ≅ X at eB
  let eA' := (Over.forget _).mapIso eA
  let eB' := (Over.forget _).mapIso eB
  haveI : IsIso eA.hom.left := eA'.isIso_hom
  haveI : IsIso eB.hom.left := eB'.isIso_hom
  haveI : IsIso eA.inv.left := eA'.isIso_inv
  haveI : IsIntegral Y.left := hi
  have hInt := IsIntegral.of_isIso eA.inv.left
  haveI : IsDomain A := (AlgebraicGeometry.affine_isIntegral_iff (CommRingCat.of A)).mp hInt
  have hf : LocallyOfFiniteType (affineSpec A).hom := by
    rw [← Over.w eA.hom]
    exact MorphismProperty.comp_mem @LocallyOfFiniteType _ _ inferInstance ht
  haveI : Algebra.FiniteType k A := RingHom.finiteType_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hf)
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hSmooth : Smooth (affineSpec B).hom := by
    rw [← Over.w eB.hom]
    exact MorphismProperty.comp_mem @Smooth _ _ inferInstance hs
  haveI : Algebra.Smooth k B := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hSmooth)
  let F := eB.hom ≫ f ≫ eA.inv
  let g : A →ₐ[k] B := coordinates F
  let ea : A →ₐ[k] k := coordinates (a ≫ f ≫ eA.inv)
  let eb : B →ₐ[k] k := coordinates (a ≫ eB.inv)
  have he : eb.comp g = ea := by
    apply affineSpecMap_injective (A := A) (B := CommAlgCat.of k k)
    rw [affineSpecMap_comp, show affineSpecMap eb = a ≫ eB.inv from affineSpecMap_coordinates _,
      show affineSpecMap g = F from affineSpecMap_coordinates _,
      show affineSpecMap ea = a ≫ f ≫ eA.inv from affineSpecMap_coordinates _]
    simp [F, Category.assoc]
  have hLift : ∀ q : PointLifts k A k ea,
      ∃ p : PointLifts k B k eb, p.val.comp g = q.val := by
    intro q
    let y : Points Y (CommAlgCat.of k (DualNumber k)) :=
      affineSpecMap (B := CommAlgCat.of k (DualNumber k)) q.val ≫ eA.hom
    have hy' : mapPoints (dualReduction k) y = a ≫ f := by
      change affineSpecMap (A := CommAlgCat.of k (DualNumber k)) (B := CommAlgCat.of k k)
        (TrivSqZeroExt.fstHom k k k) ≫ affineSpecMap q.val ≫ eA.hom = _
      rw [← Category.assoc, ← affineSpecMap_comp, q.property,
        show affineSpecMap (B := CommAlgCat.of k k) ea = a ≫ f ≫ eA.inv
          from affineSpecMap_coordinates _]
      simp [Category.assoc]
    obtain ⟨x, hred, hprod⟩ := hl y hy'
    let D := CommAlgCat.of k (DualNumber k)
    let K := CommAlgCat.of k k
    let p : B →ₐ[k] D := coordinates (x ≫ eB.inv)
    let r : D →ₐ[k] K := TrivSqZeroExt.fstHom k k k
    have hp : affineSpecMap (A := B) (B := D) p = x ≫ eB.inv :=
      affineSpecMap_coordinates _
    have hPred : r.comp p = eb := by
      apply affineSpecMap_injective (A := B) (B := K)
      calc
        affineSpecMap (r.comp p) = affineSpecMap r ≫ affineSpecMap p :=
          affineSpecMap_comp (A := B) (B := D) (C := K) r p
        _ = (mapPoints (dualReduction k) x) ≫ eB.inv := by
          rw [hp, ← Category.assoc]
        _ = a ≫ eB.inv := congrArg (· ≫ eB.inv) hred
        _ = affineSpecMap eb := (affineSpecMap_coordinates _).symm
    refine ⟨⟨p, hPred⟩, ?_⟩
    apply affineSpecMap_injective (A := A) (B := D)
    calc
      affineSpecMap (p.comp g) = affineSpecMap p ≫ affineSpecMap g :=
        affineSpecMap_comp (A := A) (B := B) (C := D) p g
      _ = (x ≫ eB.inv) ≫ F := by rw [hp, affineSpecMap_coordinates F]
      _ = (x ≫ f) ≫ eA.inv := by simp [F, Category.assoc]
      _ = y ≫ eA.inv := congrArg (· ≫ eA.inv) hprod
      _ = affineSpecMap q.val := by simp [y, Category.assoc]
  have hg := injective_of_pointLifts g ea eb he hLift
  have hD : IsDominant (affineSpecMap g).left := by
    constructor
    change DenseRange (PrimeSpectrum.comap g.toRingHom)
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    exact ((RingHom.injective_iff_ker_eq_bot _).mp hg).le.trans bot_le
  have hD' : IsDominant F.left := by
    rw [← affineSpecMap_coordinates F]
    exact hD
  letI := hD'
  have hD'' : IsDominant (F.left ≫ eA.hom.left) := inferInstance
  have hEq : F.left ≫ eA.hom.left = eB.hom.left ≫ f.left := by
    change (F ≫ eA.hom).left = (eB.hom ≫ f).left
    simp [F, Category.assoc]
  rw [hEq] at hD''
  exact @IsDominant.of_comp _ _ _ eB.hom.left f.left hD''

/-- In characteristic zero a connected semisimple affine group has a dominant
ordered multiplication from finitely many of its rational tori. -/
theorem dominantTorusProducts : DominantOrderedTorusProducts.{u} := by
  intro k _ _ G hG
  letI : IsAffine G.val.X.left := G.property.1
  letI := hG.2.1
  have hc := GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  have hi := WordDomainGeometry.smoothConnectedGroupIntegral G hG.1 hc
  obtain ⟨m, T, hT, htangent⟩ := finite_tori_span G (reductive_of_semisimple G hG)
  refine ⟨m, T, hT, ?_⟩
  let a : Points (∏ᶜ fun i => (T i).group.X) (CommAlgCat.of k k) := Pi.lift (fun _ => 1)
  obtain ⟨ha, hl⟩ := ordered_product_lifts T htangent
  apply dominant_of_point_lifts (orderedSubgroupProduct T) a (smooth_torus_product T hT)
    (affine_product _ (fun i => (closedSubgroupAlgebraicGroup (T i)).property.1))
    G.property.1 hi G.property.2.1
  intro y hy
  rw [show a ≫ orderedSubgroupProduct T = 1 from ha] at hy
  exact hl y hy

end

end LinearAlgebraicGroups.Arithmetic.DominantTorusProducts
