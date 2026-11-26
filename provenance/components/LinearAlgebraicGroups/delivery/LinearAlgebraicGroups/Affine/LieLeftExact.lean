import Specs.LinearAlgebraicGroups.Affine.LieLeftExact
import LinearAlgebraicGroups.Affine.LieBracket
import LinearAlgebraicGroups.Affine.ClosedSubgroups
import LinearAlgebraicGroups.Affine.StandardGroups
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace LinearAlgebraicGroups

noncomputable section

open InfinitesimalCommutator
open Specs.StandardGroups

open private bracket_naturality point_liftST_injective nat_apply map_commutator
  matrixDual matrixCoefficient matrixDual_kernel matrixCoefficient_add matrixCoefficient_scale
  matrixCoefficient_injective matrixTwo matrixTwo_ST matrix_commutator
  from LinearAlgebraicGroups.Affine.LieBracket
open private mapDualKernel_scale from LinearAlgebraicGroups.Affine.IdentityTangent

variable {k : Type u} [Field k]

private abbrev dualTest (k : Type u) [Field k] := CommAlgCat.of k (DualNumber k)
private abbrev baseTest (k : Type u) [Field k] := CommAlgCat.of k k

private abbrev pointEvaluation (R : TestAlgebra k) : Specs.GroupScheme k ⥤ Type u :=
  Grp.forget (SchemeOver k) ⋙ coyoneda.obj (op ((testSpec k).obj (op R)))

private theorem reduction_natural {G H : Specs.GroupScheme k} (f : G ⟶ H)
    (z : Points G.X (dualTest k)) :
    reduceTangentPoints H ((pointEvaluation (dualTest k)).map f z) =
      (pointEvaluation (baseTest k)).map f (reduceTangentPoints G z) :=
  (nat_apply ((groupPointsFunctor k).map f) (dualReduction k) z).symm

private theorem project_reduced {G H : Specs.GroupScheme k} (f : G ⟶ H)
    (z : Points G.X (dualTest k)) (x : Lie k H)
    (h : (pointEvaluation (dualTest k)).map f z = x.toMul.val) :
    (pointEvaluation (baseTest k)).map f (reduceTangentPoints G z) =
      (pointEvaluation (baseTest k)).map f
        (1 : ((groupPointsFunctor k).obj G).obj (baseTest k)) :=
  (reduction_natural f z).symm.trans
    ((congrArg (reduceTangentPoints H) h).trans
      (x.toMul.property.trans
        (((groupPointsFunctor k).map f).app (baseTest k)).hom.map_one.symm))

theorem lieLimitComparison : Specs.LieLimitComparison.{u} := by
  intro k _ J _ _ F c hc _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p i j f
    rw [← (lieFunctoriality k).2.2, ← c.π.naturality f]
    rfl
  · intro x hx
    let D := pointEvaluation (dualTest k)
    let B := pointEvaluation (baseTest k)
    have hD := isLimitOfPreserves D hc
    have hB := isLimitOfPreserves B hc
    let s : (F ⋙ D).sections := ⟨fun j => (x j).toMul.val,
      fun f => congrArg (fun p => p.toMul.val) (hx f)⟩
    let E := Types.isLimitEquivSections hD
    let z := E.symm s
    have hz (j : J) : D.map (c.π.app j) z = (x j).toMul.val :=
      congrArg (fun t : (F ⋙ D).sections => t.val j) (E.apply_symm_apply s)
    have hred : reduceTangentPoints c.pt z = 1 := by
      apply (Types.isLimitEquivSections hB).injective
      apply Subtype.ext
      funext j
      exact project_reduced (c.π.app j) z (x j) (hz j)
    refine ⟨⟨z, hred⟩, fun j => Subtype.ext (hz j), ?_⟩
    intro p hp
    apply Subtype.ext
    apply E.injective
    apply Subtype.ext
    funext j
    exact (congrArg (fun p => p.toMul.val) (hp j)).trans (hz j).symm
  · intro j p q
    exact (mapPointKernel (c.π.app j)).map_add p q
  · intro j s p
    exact (lieFunctoriality k).1 (c.π.app j) s p
  · intro j p q
    change mapPointKernel (c.π.app j) (lieBracket c.pt p q) =
      lieBracket (F.obj j) (mapPointKernel (c.π.app j) p) (mapPointKernel (c.π.app j) q)
    exact bracket_naturality (G := c.pt) (H := F.obj j) (c.π.app j)
      (lieBracket_isBracket _) (lieBracket_isBracket _) p q

theorem liePullbackComparison : Specs.LiePullbackComparison.{u} := by
  intro k _ P G H L p q f g h x y hxy
  let D := pointEvaluation (dualTest k)
  let B := pointEvaluation (baseTest k)
  let hD : IsLimit (PullbackCone.mk (D.map p) (D.map q) (D.map_isPullback h).w) :=
    (D.map_isPullback h).isLimit
  let hB : IsLimit (PullbackCone.mk (B.map p) (B.map q) (B.map_isPullback h).w) :=
    (B.map_isPullback h).isLimit
  let s : Types.PullbackObj (D.map f) (D.map g) :=
    ⟨(x.toMul.val, y.toMul.val), congrArg (fun a => a.toMul.val) hxy⟩
  let z := (PullbackCone.IsLimit.equivPullbackObj hD).symm s
  have hp : D.map p z = x.toMul.val := PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst hD s
  have hq : D.map q z = y.toMul.val := PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd hD s
  have hred : reduceTangentPoints P z = 1 := by
    apply PullbackCone.IsLimit.type_ext hB
    · exact project_reduced p z x hp
    · exact project_reduced q z y hq
  refine ⟨⟨z, hred⟩, ⟨Subtype.ext hp, Subtype.ext hq⟩, ?_⟩
  intro z' hz'
  apply Subtype.ext
  exact PullbackCone.IsLimit.type_ext hD
    ((congrArg (fun a => a.toMul.val) hz'.1).trans hp.symm)
    ((congrArg (fun a => a.toMul.val) hz'.2).trans hq.symm)

theorem lieKernelComparison : Specs.LieKernelComparison.{u} := by
  intro k _ N G H T i t f e hT h
  have hT' := IsTerminal.isTerminalObj (pointEvaluation (dualTest k)) _ hT
  have hzero (p : Lie k T) : p = 0 := by
    apply Subtype.ext
    exact congrArg (fun a : PUnit.{u+1} ⟶ (pointEvaluation (dualTest k)).obj T => a PUnit.unit)
      (hT'.hom_ext (↾fun _ => p.toMul.val) (↾fun _ => (1 : ((groupPointsFunctor k).obj T).obj (dualTest k))))
  have hcomp (p : Lie k N) : mapPointKernel f (mapPointKernel i p) = 0 := by
    calc
      _ = mapPointKernel (i ≫ f) p := ((lieFunctoriality k).2.2 _ _ _ i f p).symm
      _ = mapPointKernel (t ≫ e) p := by rw [h.w]
      _ = mapPointKernel e (mapPointKernel t p) := (lieFunctoriality k).2.2 _ _ _ t e p
      _ = 0 := by rw [hzero (mapPointKernel t p), map_zero]
  refine ⟨?_, Set.ext fun x => ⟨?_, ?_⟩⟩
  · intro p q hp
    obtain ⟨z, _, hu⟩ := liePullbackComparison k h (mapPointKernel i p) 0
      ((hcomp p).trans (map_zero (mapPointKernel e)).symm)
    exact (hu p ⟨rfl, hzero _⟩).trans (hu q ⟨hp.symm, hzero _⟩).symm
  · rintro ⟨p, rfl⟩
    exact hcomp p
  · intro hx
    obtain ⟨p, hp, _⟩ := liePullbackComparison k h x 0
      (hx.trans (map_zero (mapPointKernel e)).symm)
    exact ⟨p, hp.1⟩

theorem lieMap_ker {N G H T : Specs.GroupScheme k}
    [IsAffine N.X.left] [IsAffine G.X.left] [IsAffine H.X.left]
    {i : N ⟶ G} {t : N ⟶ T} {f : G ⟶ H} {e : T ⟶ H}
    (hT : IsTerminal T) (h : IsPullback i t f e) :
    Function.Injective (lieMap i) ∧ LinearMap.range (lieMap i) = LinearMap.ker (lieMap f) := by
  obtain ⟨hi, hr⟩ := lieKernelComparison k hT h
  exact ⟨hi, SetLike.coe_injective hr⟩

theorem affineAlgebraicPullback : Specs.AffineAlgebraicPullback.{u} := by
  intro k _ G H L f g
  let P := pullback f g
  let p := pullback.fst f g
  let q := pullback.snd f g
  have hs : IsPullback p.hom.hom q.hom.hom f.hom.hom g.hom.hom :=
    (Grp.forget (SchemeOver k)).map_isPullback (IsPullback.of_hasPullback f g)
  have ht : IsPullback p.hom.hom.left q.hom.hom.left f.hom.hom.left g.hom.hom.left :=
    (Over.forget (Spec (CommRingCat.of k))).map_isPullback hs
  let : IsAffine G.val.X.left := G.property.1
  let : IsAffine H.val.X.left := H.property.1
  let : IsAffine L.val.X.left := L.property.1
  let : IsAffine P.X.left := IsAffine.of_isPullback ht
  let hL : LocallyOfFiniteType (g.hom.hom.left ≫ H.val.X.hom) :=
    (show g.hom.hom.left ≫ H.val.X.hom = L.val.X.hom from Over.w _).symm ▸ L.property.2.1
  let : LocallyOfFiniteType g.hom.hom.left := locallyOfFiniteType_of_comp _ H.val.X.hom
  let : LocallyOfFiniteType p.hom.hom.left :=
    MorphismProperty.of_isPullback ht.flip (P := @LocallyOfFiniteType) inferInstance
  let : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  have hP : LocallyOfFiniteType (p.hom.hom.left ≫ G.val.X.hom) := inferInstance
  refine ⟨inferInstance, ?_, ?_⟩
  · exact (show p.hom.hom.left ≫ G.val.X.hom = P.X.hom from Over.w _) ▸ hP
  · let : IsAffine (Spec (CommRingCat.of k)) := inferInstance
    infer_instance

private theorem lieMap_closed_injective {G H : Specs.GroupScheme k} (f : G ⟶ H)
    (hf : IsClosedImmersion f.hom.hom.left) : Function.Injective (mapPointKernel f) := by
  intro x y h
  let := hf
  apply Subtype.ext
  apply Over.OverMorphism.ext
  exact (cancel_mono f.hom.hom.left).mp
    (congrArg (fun z : PointKernel H => z.toMul.val.left) h)

theorem lieClosedIntersection : Specs.LieClosedIntersection.{u} := by
  intro k _ P G H L p q f g hf hg h
  have compF (z : Lie k P) :
      mapPointKernel (p ≫ f) z = mapPointKernel f (mapPointKernel p z) :=
    (lieFunctoriality k).2.2 _ _ _ p f z
  have compG (z : Lie k P) :
      mapPointKernel (p ≫ f) z = mapPointKernel g (mapPointKernel q z) :=
    (congrArg (fun a => mapPointKernel a z) h.w).trans
      ((lieFunctoriality k).2.2 _ _ _ q g z)
  refine ⟨?_, Set.ext fun x => ⟨?_, ?_⟩⟩
  · intro x y he
    have ep := (lieMap_closed_injective f hf) ((compF x).symm.trans (he.trans (compF y)))
    have eq := (lieMap_closed_injective g hg) ((compG x).symm.trans (he.trans (compG y)))
    obtain ⟨z, _, hu⟩ := liePullbackComparison k h
      (mapPointKernel p x) (mapPointKernel q x) ((compF x).symm.trans (compG x))
    exact (hu x ⟨rfl, rfl⟩).trans (hu y ⟨ep.symm, eq.symm⟩).symm
  · rintro ⟨z, rfl⟩
    exact ⟨⟨mapPointKernel p z, (compF z).symm⟩, ⟨mapPointKernel q z, (compG z).symm⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    obtain ⟨z, hz, _⟩ := liePullbackComparison k h a b (ha.trans hb.symm)
    exact ⟨z, (compF z).trans ((congrArg (mapPointKernel f) hz.1).trans ha)⟩

private def trivialHopfGroupIsTerminal (k : Type u) [Field k] :
    IsTerminal (specGroup (CommHopfAlgCat.of k k)) := by
  let U := Grp.forget (SchemeOver k)
  apply IsTerminal.isTerminalOfObj U
  let e : (specGroup (CommHopfAlgCat.of k k)).X ≅ Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
    Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
      change (𝟙 _) ≫ (𝟙 _) = Spec.map (𝟙 (CommRingCat.of k))
      rw [Spec.map_id, Category.comp_id])
  exact Over.mkIdTerminal.ofIso e.symm

theorem lieHopfKernel : Specs.LieHopfKernel.{u} := by
  intro k _ A B a _
  exact lieKernelComparison k (trivialHopfGroupIsTerminal k) (schemeKernel k a).1

private theorem mapDualKernel_injective {F H : TestAlgebra k ⥤ GrpCat.{u}} (a : F ⟶ H)
    (ha : Function.Injective (a.app (dualTest k)).hom) :
    Function.Injective (mapDualKernel a) :=
  fun _ _ h => Subtype.ext (ha (congrArg (fun p => p.toMul.val) h))

private theorem mapDualKernel_surjective {F H : TestAlgebra k ⥤ GrpCat.{u}} (a : F ⟶ H)
    (hD : Function.Surjective (a.app (dualTest k)).hom)
    (hB : Function.Injective (a.app (baseTest k)).hom) :
    Function.Surjective (mapDualKernel a) := by
  intro x
  obtain ⟨z, hz⟩ := hD x.toMul.val
  have hz' : (F.map (dualReduction k)).hom z = 1 := by
    apply hB
    rw [nat_apply, hz, x.toMul.property, map_one]
  exact ⟨⟨z, hz'⟩, Subtype.ext hz⟩

private theorem isoDualKernel_bijective {F H : TestAlgebra k ⥤ GrpCat.{u}} (a : F ≅ H) :
    Function.Bijective (mapDualKernel a.hom) :=
  ⟨mapDualKernel_injective a.hom (a.app _).groupIsoToMulEquiv.injective,
    mapDualKernel_surjective a.hom (a.app _).groupIsoToMulEquiv.surjective
      (a.app _).groupIsoToMulEquiv.injective⟩

private def linearTangentCoordinate {G : Specs.GroupScheme k}
    (b : Specs.IdentityLieStructure G) {V : Type u} [AddCommMonoid V] [Module k V]
    (d : Lie k G → V)
    (ha : ∀ p q, d (p + q) = d p + d q)
    (hs : ∀ s p, d (scalePointKernel G s p) = s • d p) :
    letI := b.lieRing
    letI := b.lieAlgebra
    Lie k G →ₗ[k] V := by
  letI := b.lieRing
  letI := b.lieAlgebra
  refine { toFun := d, map_add' := ?_, map_smul' := ?_ }
  · intro p q
    have h := congrArg (fun g : AddGroup (PointKernel G) => g.toAdd.add p q) b.group_law
    exact (congrArg d h).trans (ha p q)
  · intro s p
    exact (congrArg d (congrFun (congrFun b.scalar_law s) p)).trans (hs s p)

section Matrices

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

private abbrev glKernel := DualKernel (generalLinearPoints k ι)
private abbrev slKernel := DualKernel (specialLinearPoints k ι)

private def infinitesimalMatrix (M : Matrix ι ι k) : Matrix ι ι (DualNumber k) :=
  fun i j => ((1 : Matrix ι ι k) i j, M i j)

private theorem det_infinitesimalMatrix (M : Matrix ι ι k) :
    (infinitesimalMatrix M).det = (1, M.trace) := by
  let C := TrivSqZeroExt.inlHom k k
  have he : infinitesimalMatrix M = 1 + (DualNumber.eps : DualNumber k) • M.map C := by
    apply Matrix.ext
    intro i j
    apply TrivSqZeroExt.ext
    · by_cases hij : i = j <;> simp [infinitesimalMatrix, Matrix.one_apply, C, hij]
    · by_cases hij : i = j <;>
        simp [infinitesimalMatrix, Matrix.one_apply, C, hij]
  rw [he, Matrix.det_one_add_smul, DualNumber.eps_pow_two, mul_zero, add_zero]
  apply TrivSqZeroExt.ext
  · simp
  · simp [Matrix.trace, TrivSqZeroExt.fst_sum, C]

private def glLift (M : Matrix ι ι k) : glKernel (k := k) (ι := ι) := by
  let U : Matrix.GeneralLinearGroup ι (DualNumber k) :=
    Matrix.GeneralLinearGroup.mk'' (infinitesimalMatrix M) (by
      rw [det_infinitesimalMatrix]
      exact TrivSqZeroExt.isUnit_iff_isUnit_fst (x := ((1, M.trace) : DualNumber k)) |>.mpr
        isUnit_one)
  refine ⟨U, ?_⟩
  apply Units.ext
  rfl

private theorem matrixCoefficient_surjective :
    Function.Surjective (matrixCoefficient (k := k) (ι := ι)) :=
  fun M => ⟨glLift M, rfl⟩

private def slToGL : specialLinearPoints k ι ⟶ generalLinearPoints k ι where
  app R := GrpCat.ofHom Matrix.SpecialLinearGroup.toGL
  naturality _ _ _ := by
    apply GrpCat.ext
    intro x
    apply Units.ext
    rfl

private theorem slCoefficient_range :
    Set.range (fun p : slKernel (k := k) (ι := ι) =>
      matrixCoefficient (mapDualKernel slToGL p)) = {M | M.trace = 0} := by
  ext M
  constructor
  · rintro ⟨p, rfl⟩
    let z := mapDualKernel slToGL p
    have hM : infinitesimalMatrix (matrixCoefficient z) = p.toMul.val.val := by
      apply Matrix.ext
      intro i j
      exact TrivSqZeroExt.ext
        (congrArg (fun x : DualNumber (Matrix ι ι k) => x.fst i j) (matrixDual_kernel z)).symm
        rfl
    have hdet := p.toMul.val.prop
    rw [← hM, det_infinitesimalMatrix] at hdet
    exact congrArg TrivSqZeroExt.snd hdet
  · intro hM
    let U : Matrix.SpecialLinearGroup ι (DualNumber k) :=
      ⟨infinitesimalMatrix M, by rw [det_infinitesimalMatrix, show M.trace = 0 from hM]; rfl⟩
    have hU : ((specialLinearPoints k ι).map (dualReduction k)).hom U = 1 :=
      Subtype.ext rfl
    exact ⟨⟨U, hU⟩, rfl⟩

private theorem matrixCoordinate_bracket {G : Specs.GroupScheme k}
    (a : (groupPointsFunctor k).obj G ⟶ generalLinearPoints k ι)
    (b : Specs.IdentityLieStructure G) (p q : Lie k G) :
    matrixCoefficient (mapDualKernel a (b.lieRing.toBracket.bracket p q)) =
      matrixCoefficient (mapDualKernel a p) * matrixCoefficient (mapDualKernel a q) -
      matrixCoefficient (mapDualKernel a q) * matrixCoefficient (mapDualKernel a p) := by
  let S := CommAlgCat.of k (TwoVariables k)
  let st : dualTest k ⟶ S := CommAlgCat.ofHom (liftST k)
  have hm := (nat_apply a st (b.lieRing.toBracket.bracket p q).toMul.val).symm.trans
    ((congrArg (a.app S).hom (b.commutator_law p q)).trans (map_commutator a p q))
  have h := congrArg (fun z : Matrix.GeneralLinearGroup ι (TwoVariables k) =>
    (matrixTwo z.val).snd.snd) hm
  change (matrixTwo (((generalLinearPoints k ι).map st).hom
    (mapDualKernel a (b.lieRing.toBracket.bracket p q)).toMul.val).val).snd.snd = _ at h
  rw [matrixTwo_ST, matrix_commutator] at h
  exact h

private def matrixCoordinate {G : Specs.GroupScheme k}
    (a : (groupPointsFunctor k).obj G ⟶ generalLinearPoints k ι)
    (b : Specs.IdentityLieStructure G) :
    letI := b.lieRing
    letI := b.lieAlgebra
    Lie k G →ₗ[k] Matrix ι ι k :=
  linearTangentCoordinate b (fun p => matrixCoefficient (mapDualKernel a p))
    (fun p q => by rw [map_add, matrixCoefficient_add])
    (fun s p => by rw [mapDualKernel_scale, matrixCoefficient_scale])

theorem lieGeneralLinear : Specs.LieGeneralLinear.{u} := by
  intro k ι _ _ _ G a b
  let := b.lieRing
  let := b.lieAlgebra
  let d := matrixCoordinate a.hom b
  have hd : Function.Bijective d :=
    (show Function.Bijective (matrixCoefficient (k := k) (ι := ι)) from
      ⟨matrixCoefficient_injective, matrixCoefficient_surjective⟩).comp (isoDualKernel_bijective a)
  exact ⟨LinearEquiv.ofBijective d hd, fun _ => rfl, matrixCoordinate_bracket a.hom b⟩

theorem lieSpecialLinear : Specs.LieSpecialLinear.{u} := by
  intro k ι _ _ _ G a b
  let := b.lieRing
  let := b.lieAlgebra
  let d := matrixCoordinate (a.hom ≫ slToGL) b
  let K := LinearMap.ker (Matrix.traceLinearMap ι k k)
  have hd (p : Lie k G.val) : d p =
      matrixCoefficient (mapDualKernel slToGL (mapDualKernel a.hom p)) := rfl
  have hr : Set.range d = {M | M.trace = 0} := by
    rw [← slCoefficient_range, show (d : Lie k G.val → Matrix ι ι k) =
      (fun p : slKernel (k := k) (ι := ι) => matrixCoefficient (mapDualKernel slToGL p)) ∘
        mapDualKernel a.hom from funext hd,
      (isoDualKernel_bijective a).2.range_comp]
  let D := d.codRestrict K (fun p => by
    change d p ∈ {M : Matrix ι ι k | M.trace = 0}
    rw [← hr]
    exact Set.mem_range_self p)
  have hi : Function.Injective d :=
    matrixCoefficient_injective.comp (((mapDualKernel_injective slToGL
      Matrix.SpecialLinearGroup.toGL_injective).comp (isoDualKernel_bijective a).1))
  have hD : Function.Bijective D := by
    refine ⟨fun p q h => hi (congrArg Subtype.val h), ?_⟩
    intro M
    have hm : M.val ∈ Set.range d := by rw [hr]; exact M.property
    obtain ⟨p, hp⟩ := hm
    exact ⟨p, Subtype.ext hp⟩
  exact ⟨LinearEquiv.ofBijective D hD, fun _ => rfl,
    matrixCoordinate_bracket (a.hom ≫ slToGL) b⟩

end Matrices

section OneDimensional

private theorem commutativePoints_bracket {G : Specs.AffineAlgebraicGroup k}
    {F : TestAlgebra k ⥤ GrpCat.{u}}
    (a : (groupPointsFunctor k).obj G.val ≅ F)
    (hcomm : ∀ x y : F.obj (CommAlgCat.of k (TwoVariables k)), x * y = y * x)
    (b : Specs.IdentityLieStructure G.val) (p q : Lie k G.val) :
    letI := b.lieRing
    ⁅p, q⁆ = 0 := by
  let : IsAffine G.val.X.left := G.property.1
  let S := CommAlgCat.of k (TwoVariables k)
  have hc : InfinitesimalCommutator.commutator F (mapDualKernel a.hom p) (mapDualKernel a.hom q) =
      1 := by
    let fs : dualTest k ⟶ S := CommAlgCat.ofHom (liftS k)
    let ft : dualTest k ⟶ S := CommAlgCat.ofHom (liftT k)
    let x := (F.map fs).hom (mapDualKernel a.hom p).toMul.val
    let y := (F.map ft).hom (mapDualKernel a.hom q).toMul.val
    change x * y * x⁻¹ * y⁻¹ = 1
    rw [mul_assoc x y x⁻¹, hcomm y x⁻¹, ← mul_assoc x x⁻¹ y, mul_inv_cancel, one_mul,
      mul_inv_cancel]
  have h := (map_commutator a.hom p q).trans hc
  have hb : b.lieRing.toBracket.bracket p q = (0 : PointKernel G.val) := by
    apply Subtype.ext
    apply point_liftST_injective G.val
    let st : dualTest k ⟶ S := CommAlgCat.ofHom (liftST k)
    change (((groupPointsFunctor k).obj G.val).map st).hom
      (b.lieRing.toBracket.bracket p q).toMul.val =
        (((groupPointsFunctor k).obj G.val).map st).hom 1
    exact (b.commutator_law p q).trans
      ((a.app S).groupIsoToMulEquiv.injective (h.trans (by
        change 1 = (a.hom.app S).hom ((((groupPointsFunctor k).obj G.val).map st).hom 1)
        rw [map_one, map_one])))
  exact hb

private abbrev gaKernel := DualKernel (additivePoints k)
private abbrev gmKernel := DualKernel (multiplicativePoints k)

private def gaCoordinate (p : gaKernel (k := k)) : k :=
  (Multiplicative.toAdd p.toMul.val).snd

private def gmCoordinate (p : gmKernel (k := k)) : k :=
  p.toMul.val.val.snd

private theorem gaCoordinate_bijective : Function.Bijective (gaCoordinate (k := k)) := by
  refine ⟨?_, ?_⟩
  · intro p q h
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact TrivSqZeroExt.ext
      ((congrArg Multiplicative.toAdd p.toMul.property).trans
        (congrArg Multiplicative.toAdd q.toMul.property).symm) h
  · intro a
    exact ⟨⟨Multiplicative.ofAdd ((0, a) : DualNumber k), rfl⟩, rfl⟩

private theorem gmCoordinate_bijective : Function.Bijective (gmCoordinate (k := k)) := by
  refine ⟨?_, ?_⟩
  · intro p q h
    apply Subtype.ext
    apply Units.ext
    exact TrivSqZeroExt.ext
      ((congrArg Units.val p.toMul.property).trans (congrArg Units.val q.toMul.property).symm) h
  · intro a
    let z : DualNumber k := (1, a)
    have h : IsUnit z := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr isUnit_one
    refine ⟨⟨h.unit, Units.ext (congrArg TrivSqZeroExt.fst h.unit_spec)⟩, ?_⟩
    exact congrArg TrivSqZeroExt.snd h.unit_spec

theorem lieAdditiveGroup : Specs.LieAdditiveGroup.{u} := by
  intro k _ G a b
  let := b.lieRing
  let := b.lieAlgebra
  let d := linearTangentCoordinate b (gaCoordinate ∘ mapDualKernel a.hom)
    (fun p q => by
      change gaCoordinate (mapDualKernel a.hom (p + q)) = _
      rw [map_add]
      rfl)
    (fun s p => by
      change gaCoordinate (mapDualKernel a.hom (scaleDualKernel _ s p)) = _
      rw [mapDualKernel_scale]
      change (dualNumberScale s _).snd = s * _
      rw [dualNumberScale, TrivSqZeroExt.snd_map]
      rfl)
  have hd : Function.Bijective d := gaCoordinate_bijective.comp (isoDualKernel_bijective a)
  exact ⟨LinearEquiv.ofBijective d hd, fun _ => rfl,
    commutativePoints_bracket a (fun x y =>
      congrArg (Multiplicative.ofAdd : TwoVariables k → Multiplicative (TwoVariables k))
        (add_comm (Multiplicative.toAdd x : TwoVariables k) (Multiplicative.toAdd y))) b⟩

theorem lieMultiplicativeGroup : Specs.LieMultiplicativeGroup.{u} := by
  intro k _ G a b
  let := b.lieRing
  let := b.lieAlgebra
  let d := linearTangentCoordinate b (gmCoordinate ∘ mapDualKernel a.hom)
    (fun p q => by
      change gmCoordinate (mapDualKernel a.hom (p + q)) = _
      rw [map_add]
      let x := mapDualKernel a.hom p
      let y := mapDualKernel a.hom q
      have hx : x.toMul.val.val.fst = 1 := congrArg Units.val x.toMul.property
      have hy : y.toMul.val.val.fst = 1 := congrArg Units.val y.toMul.property
      change (x.toMul.val.val * y.toMul.val.val).snd = gmCoordinate x + gmCoordinate y
      rw [DualNumber.snd_mul, hx, hy, one_mul, mul_one, add_comm]
      rfl)
    (fun s p => by
      change gmCoordinate (mapDualKernel a.hom (scaleDualKernel _ s p)) = _
      rw [mapDualKernel_scale]
      change (dualNumberScale s _).snd = s * _
      rw [dualNumberScale, TrivSqZeroExt.snd_map]
      rfl)
  have hd : Function.Bijective d := gmCoordinate_bijective.comp (isoDualKernel_bijective a)
  exact ⟨LinearEquiv.ofBijective d hd, fun _ => rfl,
    commutativePoints_bracket a (fun x y => Units.ext (mul_comm x.val y.val)) b⟩

end OneDimensional

theorem generalLinearGroup_lie (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :
    let G := StandardGroups.generalLinearGroup k ι
    Specs.LieGeneralLinearAt k ι G (StandardGroups.generalLinearGroupPointsIso k ι)
      (identityLieStructure G) :=
  lieGeneralLinear k ι _ (StandardGroups.generalLinearGroupPointsIso k ι) _

theorem specialLinearGroup_lie (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] :
    let G := StandardGroups.specialLinearGroup k ι
    Specs.LieSpecialLinearAt k ι G (StandardGroups.specialLinearGroupPointsIso k ι)
      (identityLieStructure G) :=
  lieSpecialLinear k ι _ (StandardGroups.specialLinearGroupPointsIso k ι) _

theorem additiveGroup_lie (k : Type u) [Field k] :
    let G := StandardGroups.additiveGroup k
    Specs.LieAdditiveGroupAt k G (StandardGroups.additiveGroupPointsIso k)
      (identityLieStructure G) :=
  lieAdditiveGroup k _ (StandardGroups.additiveGroupPointsIso k) _

theorem multiplicativeGroup_lie (k : Type u) [Field k] :
    let G := StandardGroups.multiplicativeGroup k
    Specs.LieMultiplicativeGroupAt k G (StandardGroups.multiplicativeGroupPointsIso k)
      (identityLieStructure G) :=
  lieMultiplicativeGroup k _ (StandardGroups.multiplicativeGroupPointsIso k) _

end
end LinearAlgebraicGroups
