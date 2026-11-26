import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.GrassmannianCharts
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.LocalProperties.FinitePresentation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.GrassmannianCharts

open Specs.GrassmannianCharts


noncomputable section

set_option backward.isDefEq.respectTransparency false in
theorem planeSplitAndRank : PlaneSplitAndRank.{u} := by
  intro k V _ _ _ _ d hd R L
  let P := L.toSubmodule
  have hexact : Function.Exact P.subtype P.mkQ := by
    rw [LinearMap.exact_iff, P.ker_mkQ, Submodule.range_subtype]
  obtain ⟨sectionMap, hsection⟩ :=
    Module.projective_lifting_property P.mkQ LinearMap.id P.mkQ_surjective
  let splitting := (@Function.Exact.splitSurjectiveEquiv R P (R ⊗[k] V)
    ((R ⊗[k] V) ⧸ P) _ _ _ _ _ _ _ P.subtype P.mkQ hexact P.injective_subtype)
    ⟨sectionMap, hsection⟩
  let e := splitting.val
  let retraction := LinearMap.fst R P ((R ⊗[k] V) ⧸ P) ∘ₗ e.toLinearMap
  have hret : ∀ x : P, retraction (P.subtype x) = x := by
    intro x
    have hx := DFunLike.congr_fun splitting.property.1 x
    change P.subtype x = e.symm (x, 0) at hx
    rw [hx]
    simp [retraction]
  have hfinite : Module.Finite R P :=
    Module.Finite.of_surjective retraction (fun x ↦ ⟨P.subtype x, hret x⟩)
  have hprojective : Module.Projective R P :=
    Module.Projective.of_split P.subtype retraction (LinearMap.ext hret)
  refine ⟨⟨retraction.ker, LinearMap.isCompl_of_proj hret⟩, hfinite, hprojective, ?_⟩
  intro p
  have hr := congrFun (Module.rankAtStalk_eq_of_equiv (R := R) (M := R ⊗[k] V)
    (N := P × ((R ⊗[k] V) ⧸ P)) e) p
  rw [Module.rankAtStalk_prod, Pi.add_apply, L.rankAtStalk_eq,
    Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_finrank_of_free,
    Pi.natCast_apply] at hr
  change Module.finrank k V = Module.rankAtStalk P p + (Module.finrank k V - d) at hr
  change Module.rankAtStalk P p = d
  omega

theorem planeEndpointSubmodules : PlaneEndpointSubmodules.{u} := by
  intro k V _ _ _ _ R
  constructor
  · intro L
    obtain ⟨_, hfinite, hprojective, hrank⟩ :=
      planeSplitAndRank k V 0 (Nat.zero_le _) R L
    let := hfinite
    let := hprojective
    have : Subsingleton L.toSubmodule :=
      Module.rankAtStalk_eq_zero_iff_subsingleton.mp (funext hrank)
    apply le_antisymm _ bot_le
    intro x hx
    exact (Submodule.mem_bot R).mpr (congrArg Subtype.val
      (Subsingleton.elim (⟨x, hx⟩ : L.toSubmodule) 0))
  · intro L
    have : Subsingleton ((R ⊗[k] V) ⧸ L.toSubmodule) :=
      Module.rankAtStalk_eq_zero_iff_subsingleton.mp (by
        funext p
        simpa using L.rankAtStalk_eq p)
    rw [← L.toSubmodule.ker_mkQ]
    exact LinearMap.ker_eq_top.mpr (LinearMap.ext fun x ↦ Subsingleton.elim _ _)

theorem planeEndpointsUnique : PlaneEndpointsUnique.{u} := by
  intro k V _ _ _ _ R
  obtain ⟨hbot, htop⟩ := planeEndpointSubmodules k V R
  constructor
  · let P : Submodule R (R ⊗[k] V) := ⊥
    let e := P.quotEquivOfEqBot rfl
    let L : Plane k V 0 R :=
      { toSubmodule := P
        finite_quotient := Module.Finite.equiv e.symm
        projective_quotient := Module.Projective.of_equiv e.symm
        rankAtStalk_eq := by
          intro p
          rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_baseChange]
          simp }
    exact ⟨⟨⟨L⟩, fun M ↦ Module.Grassmannian.ext (hbot M)⟩⟩
  · let P : Submodule R (R ⊗[k] V) := ⊤
    have : Subsingleton ((R ⊗[k] V) ⧸ P) := by
      constructor
      intro x y
      obtain ⟨a, rfl⟩ := P.mkQ_surjective x
      obtain ⟨b, rfl⟩ := P.mkQ_surjective y
      have h (v : R ⊗[k] V) : P.mkQ v = 0 :=
        (Submodule.Quotient.mk_eq_zero P).mpr Submodule.mem_top
      rw [h, h]
    let L : Plane k V (Module.finrank k V) R :=
      { toSubmodule := P
        finite_quotient := inferInstance
        projective_quotient := inferInstance
        rankAtStalk_eq := by
          intro p
          simp }
    exact ⟨⟨⟨L⟩, fun M ↦ Module.Grassmannian.ext (htop M)⟩⟩

private theorem rankAtStalk_functions {R J : Type u} [CommRing R] [Fintype J]
    (p : PrimeSpectrum R) : Module.rankAtStalk (J → R) p = Fintype.card J := by
  have : Nontrivial R := p.nontrivial
  rw [Module.rankAtStalk_eq_finrank_of_free]
  simp

section GraphCoordinates

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V)
  {d : ℕ} (I : Pivot ι d) (R : TestAlgebra k)

private def splitCoordinates :
    (R ⊗[k] V) ≃ₗ[R] (Inside I → R) × (Outside I → R) :=
  coordinates b R ≪≫ₗ
    LinearEquiv.piCongrLeft' R (fun _ : ι ↦ R)
      (Equiv.sumCompl fun i : ι ↦ i ∈ I.val).symm ≪≫ₗ
    LinearEquiv.sumPiEquivProdPi R (Inside I) (Outside I) (fun _ ↦ R)

private theorem splitCoordinates_fst (v : R ⊗[k] V) :
    (splitCoordinates b I R v).1 = pivotProjection b I R v := rfl

private theorem splitCoordinates_snd (v : R ⊗[k] V) (i : Outside I) :
    (splitCoordinates b I R v).2 i = coordinates b R v i.1 := rfl

private theorem splitCoordinates_graph (A : Matrix (Outside I) (Inside I) R)
    (v : Inside I → R) :
    splitCoordinates b I R (graphInclusion b I R A v) = (v, Matrix.toLin' A v) := by
  apply Prod.ext
  · funext i
    rw [splitCoordinates_fst]
    simp [pivotProjection, graphInclusion, graphColumns, i.property]
  · funext i
    rw [splitCoordinates_snd]
    simp [graphInclusion, graphColumns, i.property]

@[simp]
theorem pivotProjection_graph (A : Matrix (Outside I) (Inside I) R) :
    (pivotProjection b I R).comp (graphInclusion b I R A) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  exact (splitCoordinates_fst b I R _).symm.trans
    (congrArg Prod.fst (splitCoordinates_graph b I R A v))

private def graphQuotient (A : Matrix (Outside I) (Inside I) R) :
    (R ⊗[k] V) →ₗ[R] (Outside I → R) :=
  ((- Matrix.toLin' A).coprod LinearMap.id).comp (splitCoordinates b I R).toLinearMap

private theorem graphQuotient_surjective (A : Matrix (Outside I) (Inside I) R) :
    Function.Surjective (graphQuotient b I R A) := by
  intro y
  refine ⟨(splitCoordinates b I R).symm (0, y), ?_⟩
  simp [graphQuotient]

private theorem graphQuotient_ker (A : Matrix (Outside I) (Inside I) R) :
    (graphQuotient b I R A).ker = (graphInclusion b I R A).range := by
  apply Submodule.ext
  intro v
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  change - Matrix.toLin' A (splitCoordinates b I R v).1 + (splitCoordinates b I R v).2 = 0 ↔ _
  rw [neg_add_eq_zero]
  constructor
  · intro h
    refine ⟨(splitCoordinates b I R v).1, (splitCoordinates b I R).injective ?_⟩
    rw [splitCoordinates_graph]
    exact Prod.ext rfl h
  · rintro ⟨w, rfl⟩
    rw [splitCoordinates_graph]

/-- The plane whose normalized inclusion has the prescribed nonpivot entries. -/
def graphPlane (A : Matrix (Outside I) (Inside I) R) : Plane k V d R := by
  let q := graphQuotient b I R A
  let e := ((graphInclusion b I R A).range.quotEquivOfEq q.ker
    (graphQuotient_ker b I R A).symm).trans
      (q.quotKerEquivOfSurjective (graphQuotient_surjective b I R A))
  refine ⟨(graphInclusion b I R A).range, Module.Finite.equiv e.symm,
    Module.Projective.of_equiv e.symm, fun p ↦ ?_⟩
  rw [Module.rankAtStalk_eq_of_equiv e, rankAtStalk_functions]
  rw [Module.finrank_eq_card_basis b, Fintype.card_subtype_compl]
  congr 1
  simpa using I.property

@[simp] theorem graphPlane_toSubmodule (A : Matrix (Outside I) (Inside I) R) :
    (graphPlane b I R A).toSubmodule = (graphInclusion b I R A).range := rfl

theorem graphPlane_isPivot (A : Matrix (Outside I) (Inside I) R) :
    IsPivot b I R (graphPlane b I R A) := by
  have hproj (v) : pivotProjection b I R (graphInclusion b I R A v) = v :=
    DFunLike.congr_fun (pivotProjection_graph b I R A) v
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := hy
    apply Subtype.ext
    change pivotProjection b I R (graphInclusion b I R A a) =
      pivotProjection b I R (graphInclusion b I R A c) at h
    rw [hproj, hproj] at h
    exact congrArg (graphInclusion b I R A) h
  · intro v
    exact ⟨⟨graphInclusion b I R A v, ⟨v, rfl⟩⟩, hproj v⟩

private theorem graphInclusion_injective {A B : Matrix (Outside I) (Inside I) R}
    (h : (graphInclusion b I R A).range = (graphInclusion b I R B).range) : A = B := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  have hmem : graphInclusion b I R A v ∈ (graphInclusion b I R B).range :=
    h ▸ LinearMap.mem_range_self _ v
  obtain ⟨w, hw⟩ := hmem
  have hv := congrArg (pivotProjection b I R) hw
  change ((pivotProjection b I R).comp (graphInclusion b I R B)) w =
    ((pivotProjection b I R).comp (graphInclusion b I R A)) v at hv
  simp only [pivotProjection_graph, LinearMap.id_apply] at hv
  subst w
  have hc := congrArg (splitCoordinates b I R) hw
  rw [splitCoordinates_graph, splitCoordinates_graph] at hc
  exact congrArg Prod.snd hc.symm

private theorem exists_graphPlane (L : Plane k V d R) (h : IsPivot b I R L) :
    ∃ A, graphPlane b I R A = L := by
  let e := LinearEquiv.ofBijective ((pivotProjection b I R).comp L.toSubmodule.subtype) h
  let g := L.toSubmodule.subtype.comp e.symm.toLinearMap
  let A := LinearMap.toMatrix' ((LinearMap.snd R (Inside I → R) (Outside I → R)).comp
    ((splitCoordinates b I R).toLinearMap.comp g))
  have hp (v : Inside I → R) : pivotProjection b I R (g v) = v := e.apply_symm_apply v
  have hg : graphInclusion b I R A = g := by
    apply LinearMap.ext
    intro v
    apply (splitCoordinates b I R).injective
    rw [splitCoordinates_graph]
    apply Prod.ext
    · exact ((splitCoordinates_fst b I R _).trans (hp v)).symm
    · simp [A]
  refine ⟨A, Module.Grassmannian.ext ?_⟩
  rw [graphPlane_toSubmodule, hg]
  apply Submodule.ext
  intro v
  constructor
  · rintro ⟨w, rfl⟩
    exact (e.symm w).property
  · intro hv
    exact ⟨e ⟨v, hv⟩, by simp [g]⟩

/-- Each point of the affine parameter scheme gives its matrix of coordinates. -/
def chartMatrixEquiv :
    Points (chartScheme (k := k) I) R ≃ Matrix (Outside I) (Inside I) R :=
  let A := CommAlgCat.of k (chartAlgebra (k := k) I)
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  ff.homEquiv.symm.trans <| Quiver.Hom.opEquiv.symm.trans
    { toFun := fun f ↦ Matrix.of fun j i ↦ f.hom (MvPolynomial.X (j, i))
      invFun := fun M ↦ CommAlgCat.ofHom (MvPolynomial.aeval fun ji ↦ M ji.1 ji.2)
      left_inv := fun f ↦ by
        apply CommAlgCat.hom_ext
        apply MvPolynomial.algHom_ext
        rintro ⟨j, i⟩
        exact MvPolynomial.aeval_X _ (j, i)
      right_inv := fun M ↦ by
        ext j i
        exact MvPolynomial.aeval_X _ (j, i) }

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem chartMatrixEquiv_apply (p : Points (chartScheme (k := k) I) R) :
    chartMatrixEquiv I R p = matrixOfPoint I R p := rfl

/-- The graph chart over a test algebra, with its normalization. -/
def graphChartEquiv :
    Points (chartScheme (k := k) I) R ≃ {L : Plane k V d R // IsPivot b I R L} :=
  (chartMatrixEquiv I R).trans <| Equiv.ofBijective
    (fun A ↦ ⟨graphPlane b I R A, graphPlane_isPivot b I R A⟩)
    ⟨fun _ _ h ↦ graphInclusion_injective b I R
      (congrArg (fun L : {L : Plane k V d R // IsPivot b I R L} ↦ L.val.toSubmodule) h),
      fun L ↦ by
        obtain ⟨A, hA⟩ := exists_graphPlane b I R L.val L.property
        exact ⟨A, Subtype.ext hA⟩⟩

end GraphCoordinates

theorem graphCoordinates : GraphCoordinates.{u} := by
  intro k V ι _ _ _ _ _ b d I R
  exact ⟨graphChartEquiv b I R, fun _ ↦ rfl⟩

section GraphBaseChange

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V)
  {d : ℕ} (I : Pivot ι d) {R S : TestAlgebra k}

private theorem coordinates_basis (i j : ι) :
    coordinates b R (1 ⊗ₜ[k] b i) j = if i = j then 1 else 0 := by
  change (b.baseChange R).repr (1 ⊗ₜ[k] b i) j = _
  rw [← Module.Basis.baseChange_apply R b i, Module.Basis.repr_self, Finsupp.single_apply]

private theorem graphQuotient_basis (A : Matrix (Outside I) (Inside I) R)
    (i : ι) (j : Outside I) :
    graphQuotient b I R A (1 ⊗ₜ[k] b i) j =
      if hi : i ∈ I.val then -A j ⟨i, hi⟩ else if i = j.val then 1 else 0 := by
  have hfst :
      (splitCoordinates b I R (1 ⊗ₜ[k] b i)).1 =
        fun l ↦ if i = l.val then 1 else 0 := by
    ext l
    exact coordinates_basis b i l.val
  have hsnd := (splitCoordinates_snd b I R (1 ⊗ₜ[k] b i) j).trans
    (coordinates_basis b i j.val)
  change -(Matrix.toLin' A (splitCoordinates b I R (1 ⊗ₜ[k] b i)).1) j +
    (splitCoordinates b I R (1 ⊗ₜ[k] b i)).2 j = _
  rw [hfst, hsnd]
  by_cases hi : i ∈ I.val
  · rw [dite_eq_left hi]
    have hne : i ≠ j.val := fun h ↦ j.property (h ▸ hi)
    have hsingle : (fun l : Inside I ↦ if i = l.val then (1 : R) else 0) =
        Pi.single ⟨i, hi⟩ 1 := by
      ext l
      by_cases h : i = l.val
      · simp [h]
      · have he : l ≠ (⟨i, hi⟩ : Inside I) := fun hh ↦ h (congrArg Subtype.val hh.symm)
        simp [h, he]
    rw [hsingle, Matrix.toLin'_apply, Matrix.mulVec_single_one]
    simp [hne]
  · rw [dite_eq_right hi]
    have hzero : (fun l : Inside I ↦ if i = l.val then (1 : R) else 0) = 0 := by
      ext l
      have hne : i ≠ l.val := fun h ↦ hi (h.symm ▸ l.property)
      simp [hne]
    simp [hzero]

private def graphQuotientEquiv (A : Matrix (Outside I) (Inside I) R) :
    ((R ⊗[k] V) ⧸ (graphPlane b I R A).toSubmodule) ≃ₗ[R] (Outside I → R) :=
  let q := graphQuotient b I R A
  ((graphInclusion b I R A).range.quotEquivOfEq q.ker
    (graphQuotient_ker b I R A).symm).trans
      (q.quotKerEquivOfSurjective (graphQuotient_surjective b I R A))

@[simp] private theorem graphQuotientEquiv_mkQ (A : Matrix (Outside I) (Inside I) R)
    (v : R ⊗[k] V) :
    graphQuotientEquiv b I A ((graphPlane b I R A).toSubmodule.mkQ v) =
      graphQuotient b I R A v :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ (graphQuotient_surjective b I R A) v

set_option backward.isDefEq.respectTransparency false in
/-- Specializing the normalized entries gives canonical base change of the plane
for arbitrary test algebra maps. -/
theorem graphPlane_map (a : R ⟶ S) (A : Matrix (Outside I) (Inside I) R) :
    Module.Grassmannian.map a.hom (graphPlane b I R A) =
      graphPlane b I S (A.map a.hom) := by
  let : Algebra R S := a.hom.toAlgebra
  let : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq' <| IsScalarTower.algebraMap_eq k R S
  let e := (graphQuotientEquiv b I A).baseChange R S _ _ ≪≫ₗ
    TensorProduct.piScalarRight R S S (Outside I)
  let q := Module.Grassmannian.baseChangeMkQ S (graphPlane b I R A).toSubmodule
  have he : e.toLinearMap.comp q = graphQuotient b I S (A.map a.hom) := by
    apply (b.baseChange S).ext
    intro i
    rw [Module.Basis.baseChange_apply]
    funext j
    change e (q (1 ⊗ₜ[k] b i)) j = _
    simp only [e, q, Module.Grassmannian.baseChangeMkQ, LinearMap.comp_apply,
      LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearMap.baseChange_tmul, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
      graphQuotientEquiv_mkQ, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]
    rw [graphQuotient_basis, graphQuotient_basis]
    change a.hom _ * 1 = _
    rw [mul_one]
    split
    · simp [Matrix.map_apply, map_neg]
    · split <;> simp
  apply Module.Grassmannian.ext
  rw [Module.Grassmannian.map_toSubmodule]
  change q.ker = (graphPlane b I S (A.map a.hom)).toSubmodule
  rw [graphPlane_toSubmodule b I S, ← graphQuotient_ker b I S, ← he, LinearEquiv.ker_comp]

omit [Fintype ι] [DecidableEq ι] in
private theorem matrixOfPoint_map (a : R ⟶ S)
    (f : Points (chartScheme (k := k) I) R) :
    matrixOfPoint I S (mapPoints a f) = (matrixOfPoint I R f).map a.hom := by
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  have h : ff.preimage (mapPoints a f) = a.op ≫ ff.preimage f := by
    apply ff.map_injective
    rw [Functor.map_comp, ff.map_preimage, ff.map_preimage]
  ext j i
  change (ff.preimage (mapPoints a f)).unop.hom (MvPolynomial.X (j, i)) =
    a.hom ((ff.preimage f).unop.hom (MvPolynomial.X (j, i)))
  rw [h]
  rfl

/-- The graph maps form a natural transformation into the affine plane functor. -/
def graphChartMap :
    pointsFunctor (chartScheme (k := k) I) ⟶ planeFunctor k V d where
  app R := ↾fun p ↦ graphPlane b I R (matrixOfPoint I R p)
  naturality := by
    intro R S a
    apply ConcreteCategory.hom_ext
    intro p
    change Points (chartScheme (k := k) I) R at p
    change graphPlane b I S (matrixOfPoint I S (mapPoints a p)) =
      Module.Grassmannian.map a.hom (graphPlane b I R (matrixOfPoint I R p))
    rw [matrixOfPoint_map, graphPlane_map]

end GraphBaseChange

/-- Over a field at least one of the ordinary coordinate projections trivializes
the plane. The argument applies in particular to every residue field. -/
theorem fieldPivotCoverage : FieldPivotCoverage.{u} := by
  intro k V ι _ _ _ _ _ b d hd F _ _ L
  classical
  let R := CommAlgCat.of k F
  let P : Submodule F (F ⊗[k] V) := L.toSubmodule
  let : Module.Finite k V := Module.Finite.of_basis b
  obtain ⟨⟨Q, hQ⟩, hfinite, _, hr⟩ := planeSplitAndRank k V d hd R L
  let : Module.Finite F P := hfinite
  let : Module.Free F P := Module.Free.of_basis (Module.Basis.ofVectorSpace F P)
  let bc := b.baseChange F
  let q : Module.Dual F (F ⊗[k] V) →ₗ[F] Module.Dual F P := P.subtype.dualMap
  have hq : Function.Surjective q := by
    intro z
    let s : (F ⊗[k] V) →ₗ[F] P := P.projectionOnto Q hQ
    refine ⟨z.comp s, ?_⟩
    apply LinearMap.ext
    intro x
    change z (s (P.subtype x)) = z x
    exact congrArg z (P.projectionOnto_apply_left hQ x)
  let v : ι → Module.Dual F P := q ∘ bc.dualBasis
  have hspan : Submodule.span F (Set.range v) = ⊤ := by
    rw [show Set.range v = q '' Set.range bc.dualBasis from Set.range_comp _ _,
      ← Submodule.map_span, bc.dualBasis.span_eq, Submodule.map_top,
      LinearMap.range_eq_top.mpr hq]
  obtain ⟨κ, f, hf, hsp, hli⟩ := exists_linearIndependent' F v
  let : Fintype κ := Fintype.ofInjective f hf
  let T := Finset.univ.map ⟨f, hf⟩
  let e : κ ≃ ↥T := Equiv.ofBijective
    (fun j ↦ ⟨f j, Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩) ⟨
      fun j l h ↦ hf (congrArg Subtype.val h),
      fun j ↦ by
        obtain ⟨i, _, hi⟩ := Finset.mem_map.mp j.property
        exact ⟨i, Subtype.ext hi⟩⟩
  let D : Module.Basis κ F (Module.Dual F P) := Module.Basis.mk hli (hsp.trans hspan).ge
  have hP : Module.finrank F P = d := by
    have eq := hr (IsLocalRing.closedPoint F)
    change Module.rankAtStalk (R := F) P (IsLocalRing.closedPoint F) = d at eq
    rw [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply] at eq
    exact eq
  have hcard : T.card = d := by
    rw [Finset.card_map, Finset.card_univ, ← Module.finrank_eq_card_basis D]
    exact (Subspace.dual_finrank_eq (K := F) (V := P)).trans hP
  let I : Pivot ι d := ⟨T, hcard⟩
  let J : Module.Basis (Inside I) F (Module.Dual F P) := D.reindex e
  let E : P ≃ₗ[F] (Inside I → R) := (Module.evalEquiv F P).trans J.dualBasis.equivFun
  refine ⟨I, ?_⟩
  have hE : E.toLinearMap = (pivotProjection b I R).comp P.subtype := by
    apply LinearMap.ext
    intro w
    funext j
    change J.dualBasis.equivFun (Module.evalEquiv F P w) j =
      coordinates b R w.val j.val
    rw [Module.Basis.dualBasis_equivFun]
    change (J j) w = _
    have he (t : κ) : (e t).val = f t := rfl
    have hj : f (e.symm j) = j.val := (he (e.symm j)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply j))
    rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
    change (bc.dualBasis (f (e.symm j))) w.val = _
    rw [hj, Module.Basis.dualBasis_apply]
    rfl
  change Function.Bijective ((pivotProjection b I R).comp P.subtype)
  rw [← hE]
  exact E.bijective

section Transitions

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V)
  {d : ℕ} (I J : Pivot ι d) (R : TestAlgebra k)

private def graphRangeEquiv (A : Matrix (Outside I) (Inside I) R) :
    (Inside I → R) ≃ₗ[R] (graphInclusion b I R A).range :=
  LinearEquiv.ofLeftInverse (g := pivotProjection b I R)
    (DFunLike.congr_fun (pivotProjection_graph b I R A))

private theorem pivotProjection_graph_of_other (A : Matrix (Outside I) (Inside I) R) :
    (pivotProjection b J R).comp (graphInclusion b I R A) = pivotChange I R J A := by
  apply LinearMap.ext
  intro v
  change (LinearMap.funLeft R R Subtype.val)
    (coordinates b R ((coordinates b R).symm (graphColumns I R A v))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem isPivot_graphPlane_iff (A : Matrix (Outside I) (Inside I) R) :
    IsPivot b J R (graphPlane b I R A) ↔ Function.Bijective (pivotChange I R J A) := by
  let e := graphRangeEquiv b I R A
  have h : (pivotProjection b J R).comp (graphPlane b I R A).toSubmodule.subtype ∘ e =
      pivotChange I R J A := by
    funext v
    exact DFunLike.congr_fun (pivotProjection_graph_of_other b I J R A) v
  change Function.Bijective ((pivotProjection b J R).comp (graphPlane b I R A).toSubmodule.subtype) ↔ _
  rw [← h]
  exact (Function.Bijective.of_comp_iff _ e.bijective).symm

end Transitions

theorem graphBaseChange : GraphBaseChange.{u} := by
  intro k V ι _ _ _ _ _ b d I R S a A L h
  have heq : L = graphPlane b I R A := Module.Grassmannian.ext h
  rw [heq, graphPlane_map, graphPlane_toSubmodule]

set_option maxRecDepth 1000 in
theorem graphTransition : GraphTransition.{u} := by
  intro k V ι _ _ _ _ _ b d I J R A B h
  let eI := graphRangeEquiv b I R A
  let eJ := graphRangeEquiv b J R B
  let e := eI.trans ((LinearEquiv.ofEq _ _ h).trans eJ.symm)
  have he (v : Inside I → R) : graphInclusion b J R B (e v) = graphInclusion b I R A v := by
    let w := LinearEquiv.ofEq _ _ h (eI v)
    change ((eJ (eJ.symm w)).val : R ⊗[k] V) = _
    exact congrArg Subtype.val (eJ.apply_symm_apply w)
  refine ⟨e, ?_, ?_⟩
  · apply LinearMap.ext
    intro v
    change e v = pivotChange I R J A v
    have hp := congrArg (pivotProjection b J R) (he v)
    change ((pivotProjection b J R).comp (graphInclusion b J R B)) (e v) =
      ((pivotProjection b J R).comp (graphInclusion b I R A)) v at hp
    rw [pivotProjection_graph, pivotProjection_graph_of_other, LinearMap.id_apply] at hp
    exact hp
  · apply LinearMap.ext
    intro v
    change graphInclusion b J R B v = graphInclusion b I R A (e.symm v)
    simpa only [LinearEquiv.apply_symm_apply] using he (e.symm v)

section Overlaps

variable {k ι : Type u} [Field k] [Fintype ι] [DecidableEq ι]
  {d : ℕ} (I J : Pivot ι d) (R : TestAlgebra k)

omit [Fintype ι] in
private theorem pivotMinor_apply (A : Matrix (Outside I) (Inside I) R) (r c : Fin d) :
    pivotMinor I J R A r c =
      let i := (pivotOrder J).symm r
      let j := (pivotOrder I).symm c
      if h : i.val ∈ I.val then (Pi.single j (1 : R) : Inside I → R) ⟨i.val, h⟩ else A ⟨i.val, h⟩ j := by
  rw [pivotMinor, LinearMap.toMatrix'_apply]
  have hreindex : (fun t : Inside I ↦ (Pi.single c (1 : R) : Fin d → R) (pivotOrder I t)) =
      (Pi.single ((pivotOrder I).symm c) (1 : R) : Inside I → R) := by
    ext t
    rw [Pi.single_apply, Pi.single_apply]
    by_cases h : pivotOrder I t = c
    · have ht := ((pivotOrder I).eq_symm_apply.mpr h)
      simp [ht]
    · have ht : t ≠ (pivotOrder I).symm c := fun he ↦ h ((pivotOrder I).eq_symm_apply.mp he)
      simp [h, ht]
  change graphColumns I R A (fun t : Inside I ↦ (Pi.single c (1 : R) : Fin d → R) (pivotOrder I t))
      ((pivotOrder J).symm r).val = _
  rw [hreindex]
  by_cases h : ((pivotOrder J).symm r).val ∈ I.val
  · simp [graphColumns, h]
  · simp [graphColumns, h, Matrix.toLin'_apply]

omit [Fintype ι] in
private theorem pivotMinor_map {S : TestAlgebra k} (a : R →ₐ[k] S)
    (A : Matrix (Outside I) (Inside I) R) :
    (pivotMinor I J R A).map a = pivotMinor I J S (A.map a) := by
  ext r c
  rw [Matrix.map_apply, pivotMinor_apply, pivotMinor_apply]
  by_cases h : ((pivotOrder J).symm r).val ∈ I.val
  · rw [dite_eq_left h, dite_eq_left h]
    simp only [Pi.single_apply]
    split <;> simp
  · rw [dite_eq_right h, dite_eq_right h, Matrix.map_apply]

omit [Fintype ι] in
private theorem bijective_pivotChange_iff (A : Matrix (Outside I) (Inside I) R) :
    Function.Bijective (pivotChange I R J A) ↔ IsUnit (pivotMinor I J R A).det := by
  let eI := LinearEquiv.funCongrLeft R R (pivotOrder I).symm
  let eJ := LinearEquiv.funCongrLeft R R (pivotOrder J).symm
  let f := pivotChange I R J A
  have hcomp : Function.Bijective (eJ ∘ f ∘ eI.symm) ↔ Function.Bijective f :=
    (eJ.bijective.of_comp_iff' _).trans (Function.Bijective.of_comp_iff f eI.symm.bijective)
  have heq : (eJ ∘ f ∘ eI.symm) = (pivotMinor I J R A).mulVec := by
    change _ = ⇑(Matrix.mulVecLin (pivotMinor I J R A))
    rw [← Matrix.toLin'_apply']
    change ⇑(eJ.toLinearMap.comp (f.comp eI.symm.toLinearMap)) =
      ⇑(Matrix.toLin' (LinearMap.toMatrix' (eJ.toLinearMap.comp (f.comp eI.symm.toLinearMap))))
    rw [Matrix.toLin'_toMatrix']
  rw [heq] at hcomp
  rw [← hcomp, ← Matrix.isUnit_iff_isUnit_det]
  exact ⟨fun h ↦ Matrix.mulVec_surjective_iff_isUnit.mp h.surjective,
    fun h ↦ ⟨Matrix.mulVec_injective_of_isUnit h, Matrix.mulVec_surjective_iff_isUnit.mpr h⟩⟩

private theorem factor_basicOpen_affine {A : TestAlgebra k} (t : A)
    (φ : A ⟶ R) :
    let X := (testSpec k).obj (op A)
    let j := Scheme.Opens.ι (X := X.left) (PrimeSpectrum.basicOpen t)
    let Y : SchemeOver k := Over.mk (j ≫ X.hom)
    let i : Y ⟶ X := Over.homMk j rfl
    (∃ f : Points Y R, f ≫ i = (testSpec k).map φ.op) ↔ IsUnit (φ.hom t) := by
  dsimp only
  let X := (testSpec k).obj (op A)
  let U : X.left.Opens := PrimeSpectrum.basicOpen t
  let Y : SchemeOver k := Over.mk (U.ι ≫ X.hom)
  let i : Y ⟶ X := Over.homMk U.ι rfl
  let f := (testSpec k).map φ.op
  change (∃ g : Points Y R, g ≫ i = f) ↔ _
  have hf (q : PrimeSpectrum R) :
      f.left q ∈ U ↔ φ.hom t ∉ q.asIdeal :=
    Iff.rfl
  constructor
  · rintro ⟨g, hg⟩
    by_contra hnonunit
    obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hnonunit
    let q : PrimeSpectrum R := ⟨m, hm.isPrime⟩
    have hU : f.left q ∈ Set.range U.ι := by
      rw [← hg]
      exact ⟨g.left q, rfl⟩
    rw [Scheme.Opens.range_ι] at hU
    exact (hf q).mp hU hmem
  · intro h
    have hU : Set.range f.left ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨q, rfl⟩
      let : q.asIdeal.IsPrime := q.isPrime
      exact (hf q).mpr (q.asIdeal.notMem_of_isUnit h)
    let g := IsOpenImmersion.lift U.ι f.left hU
    have hg : g ≫ U.ι = f.left := IsOpenImmersion.lift_fac _ _ _
    let G : Points Y R := Over.homMk g (by
      change g ≫ (U.ι ≫ X.hom) = _
      rw [← Category.assoc, hg, Over.w f])
    exact ⟨G, Over.OverMorphism.ext hg⟩

end Overlaps

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
/-- A point lands in both charts exactly on the principal open of the new pivot minor. -/
theorem overlapCoordinates : OverlapCoordinates.{u} := by
  intro k V ι _ _ _ _ _ b d I J R L f h
  let A := CommAlgCat.of k (chartAlgebra (k := k) I)
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a : A ⟶ R := (ff.preimage f).unop
  have haf : (testSpec k).map a.op = f := ff.map_preimage _
  have heq : L = graphPlane b I R (matrixOfPoint I R f) := Module.Grassmannian.ext h
  have hdet : a.hom (overlapDet (k := k) I J) =
      (pivotMinor I J R (matrixOfPoint I R f)).det := by
    change a.hom ((pivotMinor I J A _).det) = _
    rw [AlgHom.map_det]
    change ((pivotMinor I J A _).map a.hom).det = _
    rw [pivotMinor_map]
    rfl
  rw [heq, isPivot_graphPlane_iff, bijective_pivotChange_iff, ← hdet]
  have hbasic := factor_basicOpen_affine R (overlapDet (k := k) I J) a
  change (∃ g : Points (chartOverlap k I J) R, g ≫ overlapInclusion I J = (testSpec k).map a.op)
    ↔ IsUnit (a.hom (overlapDet (k := k) I J)) at hbasic
  rw [haf] at hbasic
  exact hbasic.symm

section AffineProbes

variable {k : Type u} [Field k]

private def overOpen {S : SchemeOver k} {A : Scheme.{u}} (a : A ⟶ S.left) :
    SchemeOver k :=
  Over.mk (a ≫ S.hom)

private def overOpenInclusion {S : SchemeOver k} {A : Scheme.{u}} (a : A ⟶ S.left) :
    overOpen (S := S) a ⟶ S :=
  Over.homMk a rfl

/-- Morphisms of schemes over k are detected by affine probes. -/
theorem hom_ext_on_affines {S X : SchemeOver k} {f g : S ⟶ X}
    (h : ∀ (R : TestAlgebra k) (p : Points S R), p ≫ f = p ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  apply S.left.affineCover.hom_ext
  intro i
  let a := overOpenInclusion (S.left.affineCover.f i)
  obtain ⟨R, ⟨e⟩⟩ := (essImage_algSpec (G := overOpen (S.left.affineCover.f i))).mpr
    (inferInstanceAs (IsAffine (S.left.affineCover.X i)))
  have he : a ≫ f = a ≫ g := by
    rw [← cancel_epi e.hom, ← Category.assoc, ← Category.assoc]
    exact h R.unop (e.hom ≫ a)
  exact congrArg Over.Hom.left he

private theorem affineComponent_eq {A S X : SchemeOver k} {R : TestAlgebra k}
    (e : (testSpec k).obj (op R) ≅ A) (q : A ⟶ S)
    (α : pointsFunctor S ⟶ pointsFunctor X)
    (T : TestAlgebra k) (p : Points A T) :
    p ≫ (e.inv ≫ α.app R (e.hom ≫ q)) = α.app T (p ≫ q) := by
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a := ff.preimage (p ≫ e.inv)
  have ha : (testSpec k).map a.unop.op = p ≫ e.inv := ff.map_preimage _
  have eq := congrArg (fun t : Points S R ⟶ Points X T ↦ t (e.hom ≫ q))
    (α.naturality a.unop)
  change α.app T ((testSpec k).map a.unop.op ≫ (e.hom ≫ q)) =
    (testSpec k).map a.unop.op ≫ α.app R (e.hom ≫ q) at eq
  rw [ha, Category.assoc, Iso.inv_hom_id_assoc] at eq
  exact (Category.assoc p e.inv _).symm.trans eq.symm

private theorem exists_affineComponent {A S X : SchemeOver k} (hA : IsAffine A.left)
    (q : A ⟶ S) (α : pointsFunctor S ⟶ pointsFunctor X) :
    ∃ f : A ⟶ X, ∀ (R : TestAlgebra k) (p : Points A R),
      p ≫ f = α.app R (p ≫ q) := by
  obtain ⟨R, ⟨e⟩⟩ := essImage_algSpec.mpr hA
  exact ⟨e.inv ≫ α.app R.unop (e.hom ≫ q), affineComponent_eq e q α⟩

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_hom_of_affineTransformation {S X : SchemeOver k}
    (α : pointsFunctor S ⟶ pointsFunctor X) :
    ∃ f : S ⟶ X, ∀ (R : TestAlgebra k) (p : Points S R), p ≫ f = α.app R p := by
  classical
  let U := S.left.affineCover
  let a (i : U.I₀) := overOpenInclusion (S := S) (U.f i)
  choose f hf using fun i : U.I₀ ↦
    exists_affineComponent (inferInstanceAs (IsAffine (U.X i))) (a i) α
  have hg (i j : U.I₀) :
      pullback.fst (U.f i) (U.f j) ≫ (f i).left =
        pullback.snd (U.f i) (U.f j) ≫ (f j).left := by
    let B := overOpen (S := S) (pullback.fst (U.f i) (U.f j) ≫ U.f i)
    let b₁ : B ⟶ overOpen (S := S) (U.f i) := Over.homMk (pullback.fst _ _) (by simp [B, overOpen])
    let b₂ : B ⟶ overOpen (S := S) (U.f j) :=
      Over.homMk (pullback.snd _ _) (by simp [B, overOpen, pullback.condition])
    have hb : b₁ ≫ a i = b₂ ≫ a j := by
      apply Over.OverMorphism.ext
      exact pullback.condition
    have he : b₁ ≫ f i = b₂ ≫ f j := by
      apply hom_ext_on_affines
      intro R p
      simpa only [Category.assoc] using
        (hf i R (p ≫ b₁)).trans
          ((congrArg (fun q ↦ α.app R (p ≫ q)) hb).trans (hf j R (p ≫ b₂)).symm)
    exact congrArg Over.Hom.left he
  let g := U.glueMorphisms (fun i ↦ (f i).left) hg
  have g_over : g ≫ X.hom = S.hom := by
    apply U.hom_ext
    intro i
    rw [← Category.assoc]
    have hi : U.f i ≫ g = (f i).left := U.ι_glueMorphisms _ _ i
    rw [hi]
    exact Over.w (f i)
  let G : S ⟶ X := Over.homMk g g_over
  have hG (i : U.I₀) : a i ≫ G = f i := by
    apply Over.OverMorphism.ext
    change U.f i ≫ g = (f i).left
    exact U.ι_glueMorphisms _ _ i
  refine ⟨G, fun R p ↦ ?_⟩
  apply Over.OverMorphism.ext
  let W : ((testSpec k).obj (op R)).left.OpenCover := U.pullback₁ p.left
  apply W.hom_ext
  intro i
  let B := overOpen (S := (testSpec k).obj (op R)) (W.f i)
  let c : B ⟶ (testSpec k).obj (op R) := overOpenInclusion (W.f i)
  let t : B ⟶ overOpen (S := S) (U.f i) :=
    Over.homMk (pullback.snd p.left (U.f i)) (by
      change pullback.snd p.left (U.f i) ≫ (U.f i ≫ S.hom) =
        pullback.fst p.left (U.f i) ≫ ((testSpec k).obj (op R)).hom
      rw [← Category.assoc, ← pullback.condition, Category.assoc, Over.w p])
  have hct : c ≫ p = t ≫ a i := by
    apply Over.OverMorphism.ext
    exact pullback.condition
  have he : c ≫ (p ≫ G) = c ≫ α.app R p := by
    apply hom_ext_on_affines
    intro T q
    calc
      q ≫ (c ≫ (p ≫ G)) = (q ≫ t) ≫ f i := by
        rw [← Category.assoc c p G, hct, Category.assoc t, hG]
        simp only [Category.assoc]
      _ = α.app T ((q ≫ t) ≫ a i) := hf i T _
      _ = α.app T ((q ≫ c) ≫ p) := by
        simp only [Category.assoc, hct]
      _ = q ≫ (c ≫ α.app R p) := by
        have h := affineComponent_eq (Iso.refl ((testSpec k).obj (op R))) p α T (q ≫ c)
        change (q ≫ c) ≫ (𝟙 _ ≫ α.app R (𝟙 _ ≫ p)) = α.app T ((q ≫ c) ≫ p) at h
        rw [Category.id_comp, Category.id_comp, Category.assoc, Category.assoc] at h
        exact h.symm
  exact congrArg Over.Hom.left he

/-- The restricted Yoneda comparison for all schemes over k. -/
def affineProbesEquiv (S X : SchemeOver k) :
    (S ⟶ X) ≃ (pointsFunctor S ⟶ pointsFunctor X) := by
  let map : (S ⟶ X) → (pointsFunctor S ⟶ pointsFunctor X) := fun f ↦
    { app := fun _ ↦ ↾(· ≫ f)
      naturality := by
        intro R T a
        apply ConcreteCategory.hom_ext
        intro p
        change ((testSpec k).map a.op ≫ p) ≫ f = (testSpec k).map a.op ≫ (p ≫ f)
        exact Category.assoc _ _ _ }
  refine Equiv.ofBijective map ⟨fun f g h ↦ hom_ext_on_affines (fun R p ↦ ?_), fun α ↦ ?_⟩
  · exact congrArg (fun β : pointsFunctor S ⟶ pointsFunctor X ↦ β.app R p) h
  · obtain ⟨f, hf⟩ := exists_hom_of_affineTransformation α
    refine ⟨f, ?_⟩
    ext R p
    exact hf R p

@[simp] theorem affineProbesEquiv_apply {S X : SchemeOver k} (f : S ⟶ X)
    (R : TestAlgebra k) (p : Points S R) :
    (affineProbesEquiv S X f).app R p = p ≫ f := rfl

variable {V : Type u} [AddCommGroup V] [Module k V]

/-- Once the affine functor is represented, points on all schemes give the
compatible affine-probe descriptions. -/
def familyEquiv {d : ℕ} {X : SchemeOver k}
    (e : pointsFunctor X ≅ planeFunctor k V d) (S : SchemeOver k) :
    (S ⟶ X) ≃ Family k V d S :=
  (affineProbesEquiv S X).trans (Iso.homCongr (Iso.refl _) e)

@[simp] theorem familyEquiv_apply {d : ℕ} {X S : SchemeOver k}
    (e : pointsFunctor X ≅ planeFunctor k V d) (f : S ⟶ X)
    (R : TestAlgebra k) (p : Points S R) :
    (familyEquiv e S f).app R p = e.hom.app R (p ≫ f) := by
  change e.hom.app R ((affineProbesEquiv S X f).app R p) = _
  rw [affineProbesEquiv_apply]

end AffineProbes

section ChartLifts

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V)
  {d : ℕ} (I J : Pivot ι d)

@[simp] private theorem graphChartMap_apply (R : TestAlgebra k)
    (p : Points (chartScheme (k := k) I) R) :
    (graphChartMap b I).app R p = (graphChartEquiv b I R p).val := rfl

private theorem graphChartMap_injective (R : TestAlgebra k) :
    Function.Injective ((graphChartMap b I).app R : Points (chartScheme (k := k) I) R → Plane k V d R) := by
  intro p q h
  exact (graphChartEquiv b I R).injective (Subtype.ext h)

/-- The scheme-to-plane map defined by one polynomial chart. -/
def chartFamily {S : SchemeOver k} (f : S ⟶ chartScheme (k := k) I) :
    Family k V d S :=
  affineProbesEquiv S _ f ≫ graphChartMap b I

@[simp] theorem chartFamily_apply {S : SchemeOver k}
    (f : S ⟶ chartScheme (k := k) I) (R : TestAlgebra k) (p : Points S R) :
    (chartFamily b I f).app R p = (graphChartMap b I).app R (p ≫ f) := by
  change (graphChartMap b I).app R ((affineProbesEquiv S _ f).app R p) = _
  rw [affineProbesEquiv_apply]

private theorem chartFamily_comp {S T : SchemeOver k}
    (f : T ⟶ S) (g : S ⟶ chartScheme (k := k) I) :
    chartFamily b I (f ≫ g) = affineProbesEquiv T S f ≫ chartFamily b I g := by
  ext R p
  change Points T R at p
  change (chartFamily b I (f ≫ g)).app R p =
    (chartFamily b I g).app R ((affineProbesEquiv T S f).app R p)
  rw [affineProbesEquiv_apply, chartFamily_apply, chartFamily_apply, Category.assoc]

private theorem chartFamily_injective {S : SchemeOver k} :
    Function.Injective (chartFamily b I (S := S)) := by
  intro f g h
  apply hom_ext_on_affines
  intro R p
  apply graphChartMap_injective b I R
  exact (chartFamily_apply b I f R p).symm.trans
    ((congrArg (fun α : Family k V d S ↦ α.app R p) h).trans (chartFamily_apply b I g R p))

private def chartLift {S : SchemeOver k} (α : Family k V d S)
    (h : ∀ R (p : Points S R), IsPivot b I R (α.app R p)) : S ⟶ chartScheme (k := k) I := by
  let f (R : TestAlgebra k) (p : Points S R) :=
    (graphChartEquiv b I R).symm ⟨α.app R p, h R p⟩
  have hf (R : TestAlgebra k) (p : Points S R) :
      (graphChartMap b I).app R (f R p) = α.app R p := by
    rw [graphChartMap_apply, Equiv.apply_symm_apply]
  refine (affineProbesEquiv S (chartScheme (k := k) I)).symm
    { app := fun R ↦ ↾(f R), naturality := ?_ }
  intro R T a
  apply ConcreteCategory.hom_ext
  intro p
  change Points S R at p
  symm
  change mapPoints a (f R p) = f T (mapPoints a p)
  apply graphChartMap_injective b I T
  have hn₁ := congrArg (fun g : Points (chartScheme (k := k) I) R ⟶ Plane k V d T ↦
    g (f R p)) ((graphChartMap b I).naturality a)
  have hn₂ := congrArg (fun g : Points S R ⟶ Plane k V d T ↦ g p) (α.naturality a)
  change (graphChartMap b I).app T (mapPoints a (f R p)) =
    Module.Grassmannian.map a.hom ((graphChartMap b I).app R (f R p)) at hn₁
  change α.app T (mapPoints a p) = Module.Grassmannian.map a.hom (α.app R p) at hn₂
  rw [hn₁, hf, hf]
  exact hn₂.symm

@[simp] private theorem chartFamily_chartLift {S : SchemeOver k} (α : Family k V d S)
    (h : ∀ R (p : Points S R), IsPivot b I R (α.app R p)) :
    chartFamily b I (chartLift b I α h) = α := by
  unfold chartFamily chartLift
  rw [Equiv.apply_symm_apply]
  ext R p
  change (graphChartMap b I).app R ((graphChartEquiv b I R).symm ⟨α.app R p, h R p⟩) = _
  rw [graphChartMap_apply, Equiv.apply_symm_apply]
  rfl

private instance overlapInclusion_open : IsOpenImmersion (overlapInclusion (k := k) I J).left := by
  let U : (chartScheme (k := k) I).left.Opens := PrimeSpectrum.basicOpen (overlapDet (k := k) I J)
  change IsOpenImmersion U.ι
  infer_instance

private instance : Mono (overlapInclusion (k := k) I J) :=
  Over.mono_of_mono_left _

private theorem chartFamily_isPivot {S : SchemeOver k}
    (f : S ⟶ chartScheme (k := k) I) (R : TestAlgebra k) (p : Points S R) :
    IsPivot b I R ((chartFamily b I f).app R p) := by
  rw [chartFamily_apply, graphChartMap_apply]
  exact (graphChartEquiv b I R (p ≫ f)).property

private theorem overlap_point_iff (R : TestAlgebra k) (f : Points (chartScheme (k := k) I) R) :
    (∃ g : Points (chartOverlap k I J) R, g ≫ overlapInclusion I J = f) ↔
      IsPivot b J R ((graphChartMap b I).app R f) :=
  (overlapCoordinates k V ι b I J R ((graphChartMap b I).app R f) f rfl).symm

private theorem chartFamily_overlap_isPivot (R : TestAlgebra k)
    (p : Points (chartOverlap k I J) R) :
    IsPivot b J R ((chartFamily b I (overlapInclusion I J)).app R p) := by
  rw [chartFamily_apply]
  exact (overlap_point_iff b I J R _).mp ⟨p, rfl⟩

private def overlapLift {S : SchemeOver k} (f : S ⟶ chartScheme (k := k) I)
    (h : ∀ R (p : Points S R), IsPivot b J R ((chartFamily b I f).app R p)) :
    S ⟶ chartOverlap k I J := by
  let e (R : TestAlgebra k) (p : Points S R) :=
    ((overlap_point_iff b I J R (p ≫ f)).mpr ((chartFamily_apply b I f R p) ▸ h R p))
  let g (R : TestAlgebra k) (p : Points S R) := (e R p).choose
  have hg (R : TestAlgebra k) (p : Points S R) :
      g R p ≫ overlapInclusion I J = p ≫ f := (e R p).choose_spec
  refine (affineProbesEquiv S (chartOverlap k I J)).symm
    { app := fun R ↦ ↾(g R), naturality := ?_ }
  intro R T a
  apply ConcreteCategory.hom_ext
  intro p
  change Points S R at p
  symm
  change mapPoints a (g R p) = g T (mapPoints a p)
  rw [← cancel_mono (overlapInclusion (k := k) I J)]
  change ((testSpec k).map a.op ≫ g R p) ≫ overlapInclusion I J =
    g T (mapPoints a p) ≫ overlapInclusion I J
  simp only [Category.assoc, hg, mapPoints]

@[reassoc (attr := simp)] private theorem overlapLift_inclusion {S : SchemeOver k}
    (f : S ⟶ chartScheme (k := k) I)
    (h : ∀ R (p : Points S R), IsPivot b J R ((chartFamily b I f).app R p)) :
    overlapLift b I J f h ≫ overlapInclusion I J = f := by
  apply hom_ext_on_affines
  intro R p
  rw [← Category.assoc, ← affineProbesEquiv_apply (overlapLift b I J f h) R p]
  unfold overlapLift
  rw [Equiv.apply_symm_apply]
  exact ((overlap_point_iff b I J R (p ≫ f)).mpr
    ((chartFamily_apply b I f R p) ▸ h R p)).choose_spec

end ChartLifts

section Gluing

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V)
  {d : ℕ} (I J K : Pivot ι d)

local notation "O(" i ", " j ")" => overlapInclusion (k := k) i j

private def transition : chartOverlap k I J ⟶ chartOverlap k J I := by
  let α := chartFamily b I (O(I, J))
  let f := chartLift b J α (chartFamily_overlap_isPivot b I J)
  apply overlapLift b J I f
  have h : chartFamily b J f = α := chartFamily_chartLift _ _ _ _
  rw [h]
  exact chartFamily_isPivot b I (O(I, J))

private theorem transition_family :
    chartFamily b J (transition b I J ≫ O(J, I)) = chartFamily b I (O(I, J)) := by
  unfold transition
  rw [overlapLift_inclusion, chartFamily_chartLift]

private theorem transition_self : transition b I I = 𝟙 _ := by
  rw [← cancel_mono (O(I, I)), Category.id_comp]
  apply chartFamily_injective b I
  exact transition_family b I I

include b in
private theorem overlap_self_iso : IsIso (O(I, I)) := by
  let l := overlapLift b I I (𝟙 (chartScheme (k := k) I)) (chartFamily_isPivot b I _)
  have h : l ≫ O(I, I) = 𝟙 _ := overlapLift_inclusion b I I _ _
  exact ⟨⟨l, by rw [← cancel_mono (O(I, I)), Category.assoc, h, Category.comp_id, Category.id_comp], h⟩⟩

private abbrev TripleOverlap : SchemeOver k := pullback (O(I, J)) (O(I, K))

private def tripleProjection : TripleOverlap (k := k) I J K ⟶ chartScheme (k := k) I :=
  pullback.fst (O(I, J)) (O(I, K)) ≫ O(I, J)

omit [Fintype ι] in
private theorem tripleProjection_eq :
    tripleProjection (k := k) I J K = pullback.snd (O(I, J)) (O(I, K)) ≫ O(I, K) :=
  pullback.condition

private instance : Mono (tripleProjection (k := k) I J K) :=
  inferInstanceAs (Mono (pullback.fst (O(I, J)) (O(I, K)) ≫ O(I, J)))

private def rotate : TripleOverlap (k := k) I J K ⟶ TripleOverlap (k := k) J K I := by
  let q := pullback.fst (O(I, J)) (O(I, K)) ≫ transition b I J
  let p := q ≫ O(J, I)
  have h : chartFamily b J p = chartFamily b I (tripleProjection (k := k) I J K) := by
    change chartFamily b J ((pullback.fst (O(I, J)) (O(I, K)) ≫ transition b I J) ≫ O(J, I)) = _
    rw [Category.assoc, chartFamily_comp, transition_family, ← chartFamily_comp]
    rfl
  have hK (R : TestAlgebra k) (a : Points (TripleOverlap (k := k) I J K) R) :
      IsPivot b K R ((chartFamily b J p).app R a) := by
    rw [h, tripleProjection_eq, chartFamily_comp]
    change IsPivot b K R ((chartFamily b I (O(I, K))).app R
      ((affineProbesEquiv _ _ (pullback.snd (O(I, J)) (O(I, K)))).app R a))
    exact chartFamily_overlap_isPivot b I K _ _
  let r := overlapLift b J K p hK
  exact pullback.lift r q (overlapLift_inclusion _ _ _ _ _)

private theorem rotate_snd :
    rotate b I J K ≫ pullback.snd (O(J, K)) (O(J, I)) =
      pullback.fst (O(I, J)) (O(I, K)) ≫ transition b I J := by
  unfold rotate
  exact pullback.lift_snd _ _ _

private theorem rotate_family :
    chartFamily b J (rotate b I J K ≫ tripleProjection (k := k) J K I) =
      chartFamily b I (tripleProjection (k := k) I J K) := by
  rw [tripleProjection_eq (k := k) J K I, ← Category.assoc, rotate_snd, Category.assoc,
    chartFamily_comp, transition_family, ← chartFamily_comp]
  rfl

private theorem rotate_cycle :
    rotate b I J K ≫ rotate b J K I ≫ rotate b K I J = 𝟙 _ := by
  rw [← cancel_mono (tripleProjection (k := k) I J K), Category.id_comp]
  apply chartFamily_injective b I
  rw [Category.assoc, Category.assoc, chartFamily_comp, chartFamily_comp,
    rotate_family, ← chartFamily_comp, rotate_family, ← chartFamily_comp, rotate_family]

private def pivotGlueOver (d : ℕ) : CategoryTheory.GlueData (SchemeOver k) where
  J := Pivot ι d
  U I := chartScheme (k := k) I
  V p := chartOverlap k p.1 p.2
  f := overlapInclusion
  f_mono := fun _ _ ↦ inferInstance
  f_id := fun I ↦ overlap_self_iso b I
  t := transition b
  t_id := transition_self b
  t' := rotate b
  t_fac := rotate_snd b
  cocycle := rotate_cycle b

private def pivotGlue (d : ℕ) : Scheme.GlueData where
  toGlueData := (pivotGlueOver b d).mapGlueData (Over.forget (Spec (CommRingCat.of k)))
  f_open i j := overlapInclusion_open (k := k) i j

/-- The scheme glued from the ordinary affine pivot charts along the determinant opens. -/
def gluedGrassmannian (d : ℕ) : SchemeOver k := by
  let D := pivotGlue b d
  refine Over.mk (Multicoequalizer.desc D.toGlueData.diagram (Spec (CommRingCat.of k))
    (fun I ↦ (chartScheme (k := k) I).hom) ?_)
  rintro ⟨I, J⟩
  change (O(I, J)).left ≫ (chartScheme (k := k) I).hom =
    ((transition b I J).left ≫ (O(J, I)).left) ≫ (chartScheme (k := k) J).hom
  exact (Over.w (O(I, J))).trans (Over.w (transition b I J ≫ O(J, I))).symm

/-- The inclusion of a polynomial chart into the glued Grassmannian. -/
def gluedChart (I : Pivot ι d) : chartScheme (k := k) I ⟶ gluedGrassmannian b d := by
  let D := pivotGlue b d
  refine Over.homMk (D.ι I) ?_
  unfold gluedGrassmannian
  apply Multicoequalizer.π_desc

instance isOpenImmersion_gluedChart (I : Pivot ι d) :
    IsOpenImmersion (gluedChart b I).left :=
  Scheme.GlueData.ι_isOpenImmersion (pivotGlue b d) I

theorem gluedChart_cover (x : (gluedGrassmannian b d).left) :
    ∃ (I : Pivot ι d) (y : (chartScheme (k := k) I).left), (gluedChart b I).left y = x :=
  (pivotGlue b d).ι_jointly_surjective x

private theorem gluedChart_isPullback :
    IsPullback (O(I, J)) (transition b I J ≫ O(J, I)) (gluedChart b I) (gluedChart b J) := by
  let D := pivotGlue b d
  apply IsPullback.of_map_of_faithful (Over.forget (Spec (CommRingCat.of k)))
  exact IsPullback.of_isLimit (D.vPullbackConeIsLimit I J)

/-- The intersection of two polynomial charts is the determinant principal open
in the first chart, with its normalization transition to the second. -/
theorem gluedChart_overlap :
    ∃ e : chartOverlap k I J ≅ pullback (gluedChart b I) (gluedChart b J),
      e.hom ≫ pullback.fst (gluedChart b I) (gluedChart b J) = O(I, J) :=
  ⟨(gluedChart_isPullback b I J).isoPullback, (gluedChart_isPullback b I J).isoPullback_hom_fst⟩

/-- Two maps to polynomial charts give the same point of the glued scheme
exactly when their induced affine-probe planes agree. -/
theorem gluedChart_comp_eq_iff {S : SchemeOver k}
    (f : S ⟶ chartScheme (k := k) I) (g : S ⟶ chartScheme (k := k) J) :
    f ≫ gluedChart b I = g ≫ gluedChart b J ↔ chartFamily b I f = chartFamily b J g := by
  let W := gluedChart_isPullback b I J
  constructor
  · intro h
    let l := W.lift f g h
    have h₁ : l ≫ O(I, J) = f := W.lift_fst f g h
    have h₂ : l ≫ (transition b I J ≫ O(J, I)) = g := W.lift_snd f g h
    rw [← h₁, ← h₂, chartFamily_comp, chartFamily_comp, transition_family]
  · intro h
    let l := overlapLift b I J f (h ▸ chartFamily_isPivot b J g)
    have h₁ : l ≫ O(I, J) = f := overlapLift_inclusion _ _ _ _ _
    have h₂ : l ≫ (transition b I J ≫ O(J, I)) = g := by
      apply chartFamily_injective b J
      rw [chartFamily_comp, transition_family, ← chartFamily_comp, h₁, h]
    rw [← h₁, ← h₂]
    simpa only [Category.assoc] using congrArg (l ≫ ·) W.w

private def zeroVariableChartTerminal (I : Pivot ι d)
    [IsEmpty (Outside I × Inside I)] : IsTerminal (chartScheme (k := k) I) := by
  let E : CommAlgCat.of k (chartAlgebra (k := k) I) ≅ CommAlgCat.of k k :=
    CommAlgCat.isoMk (MvPolynomial.isEmptyAlgEquiv k (Outside I × Inside I))
  let X : SchemeOver k := (testSpec k).obj (op (CommAlgCat.of k k))
  let e : (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≅ X :=
    Over.isoMk (Iso.refl _) (by
      change (𝟙 (Spec (CommRingCat.of k))) ≫ Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _
      rw [Category.id_comp]
      exact Spec.map_id (CommRingCat.of k))
  let i : X ≅ chartScheme (k := k) I := (testSpec k).mapIso E.op
  exact Over.mkIdTerminal.ofIso (e ≪≫ i)

private def gluedTerminalOfUniquePivot (I : Pivot ι d) (h : ∀ J : Pivot ι d, J = I)
    [IsEmpty (Outside I × Inside I)] :
    IsTerminal (gluedGrassmannian b d) := by
  let c := gluedChart b I
  let : IsOpenImmersion c.left := isOpenImmersion_gluedChart b I
  have htop : c.left.opensRange = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨J, y, hy⟩ := gluedChart_cover b x
    cases h J
    exact ⟨y, hy⟩
  let : IsIso c.left := isIso_of_isOpenImmersion_of_opensRange_eq_top c.left htop
  exact (zeroVariableChartTerminal (k := k) I).ofIso (Over.isoMk (asIso c.left) (Over.w c))

private def gluedZeroTerminal : IsTerminal (gluedGrassmannian b 0) := by
  let I : Pivot ι 0 := ⟨∅, Finset.card_empty⟩
  let : IsEmpty (Outside I × Inside I) := ⟨fun x ↦ Finset.notMem_empty _ x.2.property⟩
  apply gluedTerminalOfUniquePivot b I
  intro J
  exact Subtype.ext (Finset.card_eq_zero.mp J.property)

private def gluedFullTerminal :
    IsTerminal (gluedGrassmannian b (Module.finrank k V)) := by
  let I : Pivot ι (Module.finrank k V) :=
    ⟨Finset.univ, by rw [Finset.card_univ, Module.finrank_eq_card_basis b]⟩
  let : IsEmpty (Outside I × Inside I) := ⟨fun x ↦ x.1.property (Finset.mem_univ _)⟩
  apply gluedTerminalOfUniquePivot b I
  intro J
  apply Subtype.ext
  apply Finset.eq_univ_of_card
  exact J.property.trans (Module.finrank_eq_card_basis b)

end Gluing

theorem pivotGluing : PivotGluing.{u} := by
  intro k V ι _ _ _ _ _ b d
  refine ⟨gluedGrassmannian b d, gluedChart b, isOpenImmersion_gluedChart b,
    gluedChart_cover b, gluedChart_overlap b, ?_⟩
  rintro (rfl | rfl)
  · exact ⟨gluedZeroTerminal b⟩
  · exact ⟨gluedFullTerminal b⟩

section Endpoints

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]

private def terminalFromAffinePoints {d : ℕ} {X : SchemeOver k}
    (e : pointsFunctor X ≅ planeFunctor k V d)
    (h : ∀ R : TestAlgebra k, Nonempty (Unique (Plane k V d R))) :
    IsTerminal X := by
  letI instanceUnique (R : TestAlgebra k) := (h R).some
  let family (S : SchemeOver k) : Family k V d S :=
    { app := fun R ↦ ↾fun _ ↦ (default : Plane k V d R)
      naturality := by
        intro R T a
        apply ConcreteCategory.hom_ext
        intro p
        exact Subsingleton.elim (α := Plane k V d T) _ _ }
  apply IsTerminal.ofUniqueHom (fun S ↦ (familyEquiv e S).symm (family S))
  intro S m
  apply (familyEquiv e S).injective
  rw [Equiv.apply_symm_apply]
  ext R p
  exact Subsingleton.elim (α := Plane k V d R) _ _

/-- Both endpoint schemes are canonically terminal over the base field. -/
theorem endpoints : Endpoints.{u} := by
  intro k V ι _ _ _ _ _ b
  let : Module.Finite k V := Module.Finite.of_basis b
  constructor
  · intro C
    exact ⟨terminalFromAffinePoints C.affinePoints
      (fun R ↦ (planeEndpointsUnique k V R).1)⟩
  · intro C
    exact ⟨terminalFromAffinePoints C.affinePoints
      (fun R ↦ (planeEndpointsUnique k V R).2)⟩

end Endpoints

section AffineRepresentability

open TensorProduct AlgebraTensorModule

section ChangeOfAlgebra

variable {k R S V : Type u} [CommRing k] [CommRing R] [CommRing S]
  [AddCommGroup V] [Module k V] [Algebra k R] [Algebra k S]
  {d : ℕ}

private def kernelWithAlgebra (L : Module.Grassmannian R (R ⊗[k] V) d)
    (A : { a : Algebra R S // letI := a; IsScalarTower k R S }) :
    Submodule S (S ⊗[k] V) :=
  @Module.Grassmannian.baseChangeMkQ k _ V _ _ R _ _ S _ _ A.val A.property L.toSubmodule |>.ker

private theorem planeMap_eq_ker [Algebra R S] [IsScalarTower k R S]
    (L : Module.Grassmannian R (R ⊗[k] V) d) :
    (Module.Grassmannian.map (IsScalarTower.toAlgHom k R S) L).toSubmodule =
      (Module.Grassmannian.baseChangeMkQ S L.toSubmodule).ker := by
  let a := IsScalarTower.toAlgHom k R S
  let A : { a : Algebra R S // letI := a; IsScalarTower k R S } :=
    ⟨a.toAlgebra, by
      have ht := IsScalarTower.algebraMap_eq k R S
      let := a.toAlgebra
      exact IsScalarTower.of_algebraMap_eq' ht⟩
  let B : { a : Algebra R S // letI := a; IsScalarTower k R S } := ⟨‹_›, ‹_›⟩
  have h : A = B := Subtype.ext (Algebra.algebra_ext _ _ (fun _ ↦ rfl))
  have he := congrArg (kernelWithAlgebra L) h
  exact he

end ChangeOfAlgebra

section PlaneBaseChange

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
  {d : ℕ} {R S : TestAlgebra k} [Algebra R S] [IsScalarTower k R S]

private def planeInclusionBaseChange (L : Plane k V d R) :
    S ⊗[R] L.toSubmodule →ₗ[S] S ⊗[k] V :=
  (cancelBaseChange k R S S V).toLinearMap.comp (L.toSubmodule.subtype.baseChange S)

private theorem planeInclusionBaseChange_range (L : Plane k V d R) :
    (planeInclusionBaseChange (S := S) L).range =
      (Module.Grassmannian.map (IsScalarTower.toAlgHom k R S) L).toSubmodule := by
  have he : (L.toSubmodule.mkQ.baseChange S).ker =
      (L.toSubmodule.subtype.baseChange S).range :=
    SetLike.ext (fun x ↦ SetLike.ext_iff.mp (lTensor_mkQ S L.toSubmodule) x)
  rw [planeMap_eq_ker]
  simp only [Module.Grassmannian.baseChangeMkQ, planeInclusionBaseChange,
    LinearMap.range_comp, ← he, Submodule.map_equiv_eq_comap_symm, ← LinearMap.ker_comp]

private def planePullbackEquiv (b : Module.Basis ι k V) [Finite ι]
    (hd : d ≤ Module.finrank k V) (L : Plane k V d R) :
    S ⊗[R] L.toSubmodule ≃ₗ[S]
      (Module.Grassmannian.map (IsScalarTower.toAlgHom k R S) L).toSubmodule := by
  let : Module.Finite k V := Module.Finite.of_basis b
  let h := (planeSplitAndRank k V d hd R L).1
  let C := h.choose
  let hC := h.choose_spec
  let p := L.toSubmodule.projectionOnto C hC
  have hp : p.comp L.toSubmodule.subtype = LinearMap.id :=
    LinearMap.ext (Submodule.projectionOnto_apply_left hC)
  have hS : (p.baseChange S).comp (L.toSubmodule.subtype.baseChange S) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hp, LinearMap.baseChange_id]
  have hi : Function.Injective (planeInclusionBaseChange (S := S) L) :=
    (cancelBaseChange k R S S V).injective.comp
      (show Function.LeftInverse (p.baseChange S)
        (L.toSubmodule.subtype.baseChange S) from DFunLike.congr_fun hS).injective
  exact LinearEquiv.ofInjective _ hi ≪≫ₗ LinearEquiv.ofEq _ _ (planeInclusionBaseChange_range L)

@[simp] private theorem planePullbackEquiv_coe (b : Module.Basis ι k V) [Finite ι]
    (hd : d ≤ Module.finrank k V) (L : Plane k V d R) (x : S ⊗[R] L.toSubmodule) :
    ((planePullbackEquiv b hd L x : (Module.Grassmannian.map
       (IsScalarTower.toAlgHom k R S) L).toSubmodule) : S ⊗[k] V) =
        planeInclusionBaseChange L x := rfl

private def tensorExtension :
    R ⊗[k] V →ₗ[R] S ⊗[k] V :=
  ((cancelBaseChange k R S S V).restrictScalars R).toLinearMap.comp
    (TensorProduct.mk R S (R ⊗[k] V) 1)

private theorem tensorExtension_tmul (r : R) (v : V) :
    tensorExtension (S := S) (r ⊗ₜ[k] v) = algebraMap R S r ⊗ₜ[k] v := by
  simp [tensorExtension, Algebra.smul_def]

private theorem planeMap_eq_span (L : Plane k V d R) :
    (Module.Grassmannian.map (IsScalarTower.toAlgHom k R S) L).toSubmodule =
      Submodule.span S (tensorExtension (S := S) '' (L.toSubmodule : Set (R ⊗[k] V))) := by
  rw [← planeInclusionBaseChange_range, planeInclusionBaseChange, LinearMap.range_comp,
    ← Submodule.baseChange, Submodule.baseChange_eq_span, Submodule.map_span]
  congr 1
  rw [Submodule.map_coe, Set.image_image]
  rfl

end PlaneBaseChange

section LocalPivots

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V)
  {d : ℕ} (I : Pivot ι d) {R S : TestAlgebra k} [Algebra R S] [IsScalarTower k R S]

private theorem pivotProjection_baseChange :
    (pivotProjection b I S).comp (cancelBaseChange k R S S V).toLinearMap =
      (piScalarRight R S S (Inside I)).toLinearMap.comp
        ((pivotProjection b I R).baseChange S) := by
  apply (LinearMap.cancel_right (cancelBaseChange k R S S V).symm.surjective).mp
  rw [LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.comp_id]
  apply (b.baseChange S).ext
  intro j
  rw [Module.Basis.baseChange_apply]
  funext i
  have h (T : TestAlgebra k) :
      pivotProjection b I T (1 ⊗ₜ[k] b j) i = if j = i.val then 1 else 0 := by
    change (b.baseChange T).repr (1 ⊗ₜ[k] b j) i.val = _
    rw [← Module.Basis.baseChange_apply T b j, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, cancelBaseChange_symm_tmul,
    LinearMap.baseChange_tmul, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, h]
  split <;> simp

private theorem isPivot_baseChange_iff (hd : d ≤ Module.finrank k V)
    (L : Plane k V d R) :
    IsPivot b I S (Module.Grassmannian.map (IsScalarTower.toAlgHom k R S) L) ↔
      Function.Bijective (((pivotProjection b I R).comp L.toSubmodule.subtype).baseChange S) := by
  let e := planePullbackEquiv (S := S) b hd L
  let p := (pivotProjection b I S).comp
    (Module.Grassmannian.map (IsScalarTower.toAlgHom k R S) L).toSubmodule.subtype
  let q := ((pivotProjection b I R).comp L.toSubmodule.subtype).baseChange S
  let c := piScalarRight R S S (Inside I)
  have he : p.comp e.toLinearMap = c.toLinearMap.comp q := by
    have hs : ((Module.Grassmannian.map (IsScalarTower.toAlgHom k R S) L).toSubmodule.subtype).comp
        e.toLinearMap = planeInclusionBaseChange L :=
      LinearMap.ext (planePullbackEquiv_coe b hd L)
    dsimp only [p]
    rw [LinearMap.comp_assoc, hs, planeInclusionBaseChange]
    change _ = _
    rw [← LinearMap.comp_assoc, pivotProjection_baseChange b I, LinearMap.comp_assoc,
      ← LinearMap.baseChange_comp]
  have hfun : p ∘ e = c ∘ q := congrArg DFunLike.coe he
  change Function.Bijective p ↔ _
  rw [← Function.Bijective.of_comp_iff p e.bijective, hfun,
    Function.Bijective.of_comp_iff' c.bijective q]

end LocalPivots

section LocalizedLinearMaps

variable {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

private theorem localizedMap_eq_baseChange (P : Submonoid R) (f : M →ₗ[R] N) :
    LocalizedModule.map P f =
      (LocalizedModule.equivTensorProduct P N).symm.toLinearMap.comp
        ((f.baseChange (Localization P)).comp (LocalizedModule.equivTensorProduct P M).toLinearMap) := by
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | _ x s =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LocalizedModule.map_mk,
      LocalizedModule.equivTensorProduct_apply_mk, LinearMap.baseChange_tmul]
    simp

private theorem surjective_baseChange_of_residueField
    [IsLocalRing R] [Module.Finite R N] {f : M →ₗ[R] N}
    (h : Function.Surjective (f.baseChange (IsLocalRing.ResidueField R))) :
    Function.Surjective f := by
  let F := IsLocalRing.ResidueField R
  let Q := N ⧸ f.range
  have hx : (f.range.mkQ.baseChange F).comp (f.baseChange F) = 0 := by
    rw [← LinearMap.baseChange_comp, LinearMap.range_mkQ_comp, LinearMap.baseChange_zero]
  have hzero : f.range.mkQ.baseChange F = 0 := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := h y
    exact DFunLike.congr_fun hx x
  have hs : Subsingleton (F ⊗[R] Q) := by
    apply subsingleton_iff_forall_eq 0 |>.mpr
    intro y
    obtain ⟨x, rfl⟩ := LinearMap.baseChange_surjective F f.range.mkQ_surjective y
    rw [hzero, LinearMap.zero_apply]
  have : Subsingleton Q := IsLocalRing.subsingleton_tensorProduct.mp hs
  rw [← LinearMap.range_eq_top, ← f.range.ker_mkQ, LinearMap.ker_eq_top]
  exact LinearMap.ext fun x ↦ Subsingleton.elim _ _

private theorem exists_away_surjective (p : PrimeSpectrum R) [Module.Finite R N]
    {f : M →ₗ[R] N} (h : Function.Surjective (f.baseChange p.asIdeal.ResidueField)) :
    ∃ a ∉ p.asIdeal, Function.Surjective (f.baseChange (Localization.Away a)) := by
  let Rp := Localization.AtPrime p.asIdeal
  let F := p.asIdeal.ResidueField
  have hloc : Function.Surjective (f.baseChange Rp) := by
    apply surjective_baseChange_of_residueField
    rw [LinearMap.baseChange_baseChange]
    exact (cancelBaseChange R Rp F F N).symm.surjective.comp
      (h.comp (cancelBaseChange R Rp F F M).surjective)
  have hploc : Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl f) := by
    rw [localizedMap_eq_baseChange]
    exact (LocalizedModule.equivTensorProduct _ _).symm.surjective.comp
      (hloc.comp (LocalizedModule.equivTensorProduct _ _).surjective)
  obtain ⟨a, ha, hs⟩ := Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective
    p.asIdeal f hploc
  rw [localizedMap_eq_baseChange] at hs
  refine ⟨a, ha, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hs ((LocalizedModule.equivTensorProduct (Submonoid.powers a) N).symm y)
  exact ⟨LocalizedModule.equivTensorProduct (Submonoid.powers a) M x,
    (LocalizedModule.equivTensorProduct (Submonoid.powers a) N).symm.injective hx⟩

end LocalizedLinearMaps

section PivotNeighborhood

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V)
  {d : ℕ} (hd : d ≤ Module.finrank k V) (R : TestAlgebra k)

private abbrev awayAlgebra (r : R) : TestAlgebra k :=
  CommAlgCat.of k (Localization.Away r)

private def awayMap (r : R) : R ⟶ awayAlgebra R r :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (Localization.Away r))

omit [DecidableEq ι] in
private theorem pivot_baseChange_bijective (I : Pivot ι d) (hd : d ≤ Module.finrank k V)
    (L : Plane k V d R) (S : Type u) [CommRing S] [Algebra R S]
    (h : Function.Surjective (((pivotProjection b I R).comp L.toSubmodule.subtype).baseChange S)) :
    Function.Bijective (((pivotProjection b I R).comp L.toSubmodule.subtype).baseChange S) := by
  let : Module.Finite k V := Module.Finite.of_basis b
  obtain ⟨_, hf, hproj, hrank⟩ := planeSplitAndRank k V d hd R L
  let := hf
  let := hproj
  refine Module.bijective_of_surjective_of_rankAtStalk_eq h fun m hm ↦ ?_
  let p : PrimeSpectrum S := ⟨m, hm.isPrime⟩
  have : Nontrivial R := (p.comap (algebraMap R S)).nontrivial
  change Module.rankAtStalk (S ⊗[R] L.toSubmodule) p =
    Module.rankAtStalk (S ⊗[R] (Inside I → R)) p
  have h₁ := Module.rankAtStalk_baseChange (R := R) (M := L.toSubmodule) p
  have h₂ := Module.rankAtStalk_baseChange (R := R) (M := Inside I → R) p
  rw [h₁, h₂, hrank, Module.rankAtStalk_eq_finrank_of_free]
  simpa using I.property.symm

include hd in
set_option maxHeartbeats 500000 in
private theorem plane_exists_pivot_away (L : Plane k V d R) (p : PrimeSpectrum R) :
    ∃ (r : R), r ∉ p.asIdeal ∧ ∃ I : Pivot ι d,
      IsPivot b I (awayAlgebra R r) (Module.Grassmannian.map (awayMap R r).hom L) := by
  let F := p.asIdeal.ResidueField
  let F' := CommAlgCat.of k F
  let L' := Module.Grassmannian.map (IsScalarTower.toAlgHom k R F') L
  obtain ⟨I, hI⟩ := fieldPivotCoverage k V ι b d hd F L'
  let f := (pivotProjection b I R).comp L.toSubmodule.subtype
  have hf : Function.Surjective (f.baseChange F) :=
    ((isPivot_baseChange_iff (R := R) (S := F') b I hd L).mp hI).2
  obtain ⟨r, hr, hs⟩ := exists_away_surjective (R := R) (M := L.toSubmodule)
    (N := Inside I → R) p (f := f) hf
  have hb := pivot_baseChange_bijective b R I hd L (Localization.Away r) hs
  let S := awayAlgebra R r
  let : Algebra R S := inferInstanceAs (Algebra R (Localization.Away r))
  let : IsScalarTower k R S := inferInstanceAs (IsScalarTower k R (Localization.Away r))
  have H := (isPivot_baseChange_iff (S := S) b I hd L).mpr hb
  exact ⟨r, hr, I, H⟩

end PivotNeighborhood

section LocalizationOfPlanes

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
  {d : ℕ} {R S T : TestAlgebra k}

private def tensorExtensionOfHom (a : R ⟶ S) : R ⊗[k] V →ₗ[k] S ⊗[k] V :=
  TensorProduct.map a.hom.toLinearMap LinearMap.id

private theorem tensorExtensionOfHom_comp (a : R ⟶ S) (c : S ⟶ T) (x : R ⊗[k] V) :
    tensorExtensionOfHom (a ≫ c) x = tensorExtensionOfHom c (tensorExtensionOfHom a x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r v => rfl
  | add x y hx hy => simp [hx, hy]

private theorem tensorExtension_eq_of_hom [Algebra R S] [IsScalarTower k R S]
    (a : R ⟶ S) (ha : a.hom = IsScalarTower.toAlgHom k R S) (x : R ⊗[k] V) :
    tensorExtension (S := S) x = tensorExtensionOfHom a x := by
  induction x using TensorProduct.inductionOn with
  | tmul r v => simp [tensorExtension_tmul, tensorExtensionOfHom, ha]
  | add x y hx hy => simp [hx, hy]

private theorem planeMap_eq_span_of_hom (a : R ⟶ S) (L : Plane k V d R) :
    (Module.Grassmannian.map a.hom L).toSubmodule =
      Submodule.span S (tensorExtensionOfHom a '' (L.toSubmodule : Set (R ⊗[k] V))) := by
  let : Algebra R S := a.hom.toAlgebra
  let : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq' (IsScalarTower.algebraMap_eq k R S)
  have ha : a.hom = IsScalarTower.toAlgHom k R S := AlgHom.ext fun _ ↦ rfl
  calc
    _ = Submodule.span S (tensorExtension (S := S) '' (L.toSubmodule : Set (R ⊗[k] V))) :=
      (congrArg (fun f ↦ (Module.Grassmannian.map f L).toSubmodule) ha).trans
        (planeMap_eq_span L)
    _ = _ := by
      rw [show (⇑(tensorExtension (S := S)) : R ⊗[k] V → S ⊗[k] V) =
        tensorExtensionOfHom a from funext (tensorExtension_eq_of_hom a ha)]

private theorem tensorExtension_mem_planeMap (a : R ⟶ S) (L : Plane k V d R)
    {x : R ⊗[k] V} (hx : x ∈ L.toSubmodule) :
    tensorExtensionOfHom a x ∈ (Module.Grassmannian.map a.hom L).toSubmodule := by
  rw [planeMap_eq_span_of_hom]
  exact Submodule.subset_span ⟨x, hx, rfl⟩

private instance tensorExtension_isLocalizedModule [Algebra R S] [IsScalarTower k R S]
    (M : Submonoid R) [IsLocalization M S] :
    IsLocalizedModule M (tensorExtension (k := k) (V := V) (R := R) (S := S)) := by
  unfold tensorExtension
  exact IsLocalizedModule.of_linearEquiv M _ ((cancelBaseChange k R S S V).restrictScalars R)

private instance awayTensorExtension_isLocalizedModule (r : R) :
    IsLocalizedModule (Submonoid.powers r)
      (tensorExtension (k := k) (V := V) (R := R) (S := awayAlgebra R r)) := by
  have : IsLocalization.Away r (awayAlgebra R r) :=
    inferInstanceAs (IsLocalization.Away r (Localization.Away r))
  exact tensorExtension_isLocalizedModule (Submonoid.powers r)

private theorem planeMap_eq_localized (r : R) (L : Plane k V d R) :
    (Module.Grassmannian.map (awayMap R r).hom L).toSubmodule =
      L.toSubmodule.localized' (awayAlgebra R r) (Submonoid.powers r) (tensorExtension (S := awayAlgebra R r)) := by
  rw [Submodule.localized'_eq_span]
  exact planeMap_eq_span L

private abbrev doubleAwayAlgebra (r s : R) : TestAlgebra k :=
  awayAlgebra (awayAlgebra R s) (algebraMap R (awayAlgebra R s) r)

private def doubleAwayRight (r s : R) : awayAlgebra R s ⟶ doubleAwayAlgebra r s :=
  awayMap _ _

private def doubleAwayLeft (r s : R) : awayAlgebra R r ⟶ doubleAwayAlgebra r s := by
  let a := (awayMap R s ≫ doubleAwayRight r s).hom
  have hu : IsUnit (a r) := IsLocalization.Away.algebraMap_isUnit
    (S := doubleAwayAlgebra r s) (algebraMap R (awayAlgebra R s) r)
  exact CommAlgCat.ofHom (IsLocalization.Away.liftAlgHom r hu)

private theorem doubleAway_comp (r s : R) :
    awayMap R r ≫ doubleAwayLeft r s = awayMap R s ≫ doubleAwayRight r s := by
  apply CommAlgCat.hom_ext
  ext x
  let a := (awayMap R s ≫ doubleAwayRight r s).hom
  have hu : IsUnit (a r) := IsLocalization.Away.algebraMap_isUnit
    (S := doubleAwayAlgebra r s) (algebraMap R (awayAlgebra R s) r)
  change IsLocalization.Away.lift r hu (algebraMap R (awayAlgebra R r) x) = a x
  exact IsLocalization.Away.lift_eq r hu x

private theorem mem_of_mem_localized' {A B M N : Type u}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    {r : A} [IsLocalization.Away r B] (f : M →ₗ[A] N)
    [IsLocalizedModule.Away r f] (P : Submodule A M) (x : M)
    (h : f x ∈ P.localized' B (Submonoid.powers r) f) :
    ∃ n : ℕ, r ^ n • x ∈ P := by
  obtain ⟨z, hz, s, hs⟩ := h
  have hsz := (IsLocalizedModule.mk'_eq_iff (S := Submonoid.powers r)).mp hs
  obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers r)
    (show f (s.val • x) = f z by simpa only [map_smul, Submonoid.smul_def] using hsz.symm)
  obtain ⟨n, hn⟩ := (t * s).property
  refine ⟨n, ?_⟩
  change r ^ n = (t * s).val at hn
  change t.val • (s.val • x) = t.val • z at ht
  rw [hn, Submonoid.coe_mul, mul_smul, ht]
  exact P.smul_mem _ hz

end LocalizationOfPlanes

section PlaneDescent

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
  {d : ℕ} {R : TestAlgebra k} (t : Finset R)

private theorem exists_away_above (ht : Ideal.span (t : Set R) = ⊤) (p : PrimeSpectrum R) :
    ∃ (i : (t : Set R)) (q : PrimeSpectrum (awayAlgebra R i.val)),
      PrimeSpectrum.comap (algebraMap R (awayAlgebra R i.val)) q = p := by
  have h : ∃ i : (t : Set R), i.val ∉ p.asIdeal := by
    by_contra! h
    have hp : Ideal.span (t : Set R) ≤ p.asIdeal := Ideal.span_le.mpr fun r hr ↦ h ⟨r, hr⟩
    exact p.isPrime.ne_top (top_le_iff.mp (ht ▸ hp))
  obtain ⟨i, hi⟩ := h
  have hmem : p ∈ (PrimeSpectrum.basicOpen i.val : Set (PrimeSpectrum R)) := hi
  exact ⟨i, (PrimeSpectrum.localization_away_comap_range (awayAlgebra R i.val) i.val).ge hmem⟩

private theorem plane_eq_of_localizations (ht : Ideal.span (t : Set R) = ⊤)
    {L M : Plane k V d R}
    (h : ∀ i : (t : Set R), Module.Grassmannian.map (awayMap R i.val).hom L =
      Module.Grassmannian.map (awayMap R i.val).hom M) : L = M := by
  apply Module.Grassmannian.ext
  refine Submodule.eq_of_isLocalized'_span (t : Set R) ht
    (fun i ↦ awayAlgebra R i.val) _ (fun i ↦ tensorExtension (S := awayAlgebra R i.val)) ?_
  intro i
  rw [← planeMap_eq_localized, ← planeMap_eq_localized, h i]

variable (L : ∀ i : (t : Set R), Plane k V d (awayAlgebra R i.val))

private def intersectPlanes : Submodule R (R ⊗[k] V) :=
  ⨅ i : (t : Set R), ((L i).toSubmodule.restrictScalars R).comap
    (tensorExtension (S := awayAlgebra R i.val))

set_option maxHeartbeats 800000 in
private theorem intersectPlanes_localized
    (h : ∀ i j : (t : Set R),
      Module.Grassmannian.map (doubleAwayLeft i.val j.val).hom (L i) =
        Module.Grassmannian.map (doubleAwayRight i.val j.val).hom (L j))
    (i : (t : Set R)) :
    (intersectPlanes t L).localized' (awayAlgebra R i.val) (Submonoid.powers i.val)
      (tensorExtension (S := awayAlgebra R i.val)) = (L i).toSubmodule := by
  classical
  let Si := awayAlgebra R i.val
  let fi := tensorExtension (V := V) (R := R) (S := Si)
  apply le_antisymm
  · rw [Submodule.localized'_eq_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact ((Submodule.mem_iInf _).mp hx) i
  intro y hy
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers i.val) fi y
  have hxi : fi x ∈ (L i).toSubmodule := by
    rw [← hs, Submonoid.smul_def, ← algebraMap_smul Si]
    exact (L i).toSubmodule.smul_mem _ hy
  have hloc (j : (t : Set R)) :
      ∃ n : ℕ, tensorExtension (S := awayAlgebra R j.val) ((i.val ^ n) • x) ∈ (L j).toSubmodule := by
    let Sj := awayAlgebra R j.val
    let T := doubleAwayAlgebra i.val j.val
    let fj := tensorExtension (R := R) (S := Sj) (V := V)
    have hxi' : tensorExtensionOfHom (awayMap R i.val) x ∈ (L i).toSubmodule :=
      tensorExtension_eq_of_hom (awayMap R i.val) rfl x ▸ hxi
    have hc := tensorExtension_mem_planeMap (doubleAwayLeft i.val j.val) (L i) hxi'
    rw [← tensorExtensionOfHom_comp, doubleAway_comp, tensorExtensionOfHom_comp, h i j] at hc
    change tensorExtensionOfHom (awayMap Sj (algebraMap R Sj i.val))
      (tensorExtensionOfHom (awayMap R j.val) x) ∈
      (Module.Grassmannian.map (awayMap Sj (algebraMap R Sj i.val)).hom (L j)).toSubmodule at hc
    rw [planeMap_eq_localized,
      ← tensorExtension_eq_of_hom (awayMap Sj (algebraMap R Sj i.val)) rfl,
      ← tensorExtension_eq_of_hom (awayMap R j.val) rfl] at hc
    let g := tensorExtension (R := Sj) (S := T) (V := V)
    have hg : IsLocalizedModule.Away (algebraMap R Sj i.val) g :=
      awayTensorExtension_isLocalizedModule (R := Sj) (algebraMap R Sj i.val)
    obtain ⟨n, hn⟩ := mem_of_mem_localized' (A := Sj) (B := T) g
      (L j).toSubmodule (fj x) hc
    refine ⟨n, ?_⟩
    simpa only [map_smul, ← map_pow, algebraMap_smul] using hn
  choose n hn using hloc
  let N := ∑ j : (t : Set R), n j
  have hx : i.val ^ N • x ∈ intersectPlanes t L := by
    apply (Submodule.mem_iInf _).mpr
    intro j
    have hj : n j ≤ N := Finset.single_le_sum (f := n) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    have he : i.val ^ N = i.val ^ (N - n j) * i.val ^ n j := by
      rw [← pow_add, Nat.sub_add_cancel hj]
    change tensorExtension (S := awayAlgebra R j.val) (i.val ^ N • x) ∈ (L j).toSubmodule
    rw [he, mul_smul, map_smul, ← algebraMap_smul (awayAlgebra R j.val)]
    exact (L j).toSubmodule.smul_mem _ (hn j)
  refine ⟨i.val ^ N • x, hx, ⟨i.val ^ N, ⟨N, rfl⟩⟩ * s, ?_⟩
  apply IsLocalizedModule.mk'_eq_iff.mpr
  change fi (i.val ^ N • x) = (i.val ^ N * s.val) • y
  rw [map_smul, mul_smul]
  exact congrArg (i.val ^ N • ·) hs.symm

private theorem finiteProjective_of_away {A M : Type u} [CommRing A] [AddCommGroup M]
    [Module A M] (s : Set A) (hs : Ideal.span s = ⊤)
    (h : ∀ i : s,
      Module.Finite (Localization.Away i.val) (LocalizedModule.Away i.val M) ∧
      Module.Projective (Localization.Away i.val) (LocalizedModule.Away i.val M)) :
    Module.Finite A M ∧ Module.Projective A M := by
  have hfp (i : s) : Module.FinitePresentation (Localization.Away i.val)
      (LocalizedModule.Away i.val M) := by
    let := (h i).1
    let := (h i).2
    exact Module.finitePresentation_of_projective _ _
  let : Module.FinitePresentation A M := Module.FinitePresentation.of_localizationSpan s hs hfp
  refine ⟨inferInstance, Module.freeLocus_eq_univ_iff.mp (Set.eq_univ_of_forall fun p ↦ ?_)⟩
  have hp : ∃ i : s, i.val ∉ p.asIdeal := by
    by_contra! hn
    have hle : Ideal.span s ≤ p.asIdeal := Ideal.span_le.mpr fun r hr ↦ hn ⟨r, hr⟩
    exact p.isPrime.ne_top (top_le_iff.mp (hs ▸ hle))
  obtain ⟨i, hi⟩ := hp
  have hm : p ∈ (PrimeSpectrum.basicOpen i.val : Set (PrimeSpectrum A)) := hi
  obtain ⟨q, hq⟩ :=
    (PrimeSpectrum.localization_away_comap_range (Localization.Away i.val) i.val).ge hm
  let := (h i).1
  let := (h i).2
  have hq' : q ∈ Module.freeLocus (Localization.Away i.val) (LocalizedModule.Away i.val M) := by
    rw [Module.freeLocus_eq_univ]
    trivial
  rw [Module.freeLocus_localization] at hq'
  exact hq ▸ hq'

private def awayQuotientEquiv (P : Submodule R (R ⊗[k] V)) (r : R) :
    LocalizedModule.Away r ((R ⊗[k] V) ⧸ P) ≃ₗ[awayAlgebra R r]
      ((awayAlgebra R r) ⊗[k] V) ⧸
        P.localized' (awayAlgebra R r) (Submonoid.powers r) (tensorExtension (S := awayAlgebra R r)) := by
  let S := awayAlgebra R r
  let x := Submonoid.powers r
  let f := tensorExtension (R := R) (S := S) (V := V)
  let g := P.toLocalizedQuotient' S x f
  have h : IsLocalizedModule x g := IsLocalizedModule.toLocalizedQuotient' S x f P
  exact (LocalizedModule.equivTensorProduct x ((R ⊗[k] V) ⧸ P)).trans
    (IsLocalizedModule.isBaseChange x S g).equiv

set_option maxHeartbeats 2600000 in
private theorem plane_descent (ht : Ideal.span (t : Set R) = ⊤)
    (h : ∀ i j : (t : Set R),
      Module.Grassmannian.map (doubleAwayLeft i.val j.val).hom (L i) =
        Module.Grassmannian.map (doubleAwayRight i.val j.val).hom (L j)) :
    ∃ P : Plane k V d R, ∀ i : (t : Set R),
      Module.Grassmannian.map (awayMap R i.val).hom P = L i := by
  let P := intersectPlanes t L
  let Q := (R ⊗[k] V) ⧸ P
  let S (i : (t : Set R)) := awayAlgebra R i.val
  let U (i : (t : Set R)) :=
    P.localized' (S i) (Submonoid.powers i.val) (tensorExtension (S := S i))
  let Q' (i : (t : Set R)) := ((S i) ⊗[k] V) ⧸ U i
  have hu (i : (t : Set R)) : U i = (L i).toSubmodule := intersectPlanes_localized t L h i
  let E' (i : (t : Set R)) := (awayQuotientEquiv P i.val).trans
    (Submodule.quotEquivOfEq _ _ (hu i))
  have hfin (i : (t : Set R)) : Module.Finite (S i) (LocalizedModule.Away i.val Q) :=
    Module.Finite.equiv (E' i).symm
  have hproj (i : (t : Set R)) : Module.Projective (S i) (LocalizedModule.Away i.val Q) :=
    Module.Projective.of_equiv (E' i).symm
  obtain ⟨hfinQ, hprojQ⟩ := finiteProjective_of_away (t : Set R) ht
    (fun i ↦ ⟨hfin i, hproj i⟩)
  let := hfinQ
  let := hprojQ
  let G : Plane k V d R :=
    { toSubmodule := P
      finite_quotient := inferInstanceAs (Module.Finite R Q)
      projective_quotient := inferInstanceAs (Module.Projective R Q)
      rankAtStalk_eq := by
        intro q
        obtain ⟨i, q', hq'⟩ := exists_away_above t ht q
        have hbc := Module.rankAtStalk_isBaseChange (M := Q)
          (LocalizedModule.isBaseChange (Submonoid.powers i.val) Q) q'
        rw [hq'] at hbc
        exact hbc.symm.trans ((congrFun (Module.rankAtStalk_eq_of_equiv
          (E' i)) q').trans ((L i).rankAtStalk_eq q')) }
  refine ⟨G, fun i ↦ Module.Grassmannian.ext ?_⟩
  rw [planeMap_eq_localized]
  exact hu i

end PlaneDescent

section AffineCover

variable {k : Type u} [Field k] {R S : TestAlgebra k}
  {X : SchemeOver k}

private theorem exists_principalCover (P : R → Prop)
    (h : ∀ p : PrimeSpectrum R, ∃ r ∉ p.asIdeal, P r) :
    ∃ t : Finset R, Ideal.span (t : Set R) = ⊤ ∧ ∀ r ∈ t, P r := by
  have ht : Ideal.span {r | P r} = ⊤ := by
    by_contra hnt
    obtain ⟨m, hm, hle⟩ := (Ideal.span {r | P r}).exists_le_maximal hnt
    obtain ⟨r, hr, hpr⟩ := h ⟨m, hm.isPrime⟩
    exact hr (hle (Ideal.subset_span hpr))
  obtain ⟨t, hsub, htop⟩ := (Ideal.span_eq_top_iff_finite _).mp ht
  exact ⟨t, htop, fun _ hr ↦ hsub hr⟩

private abbrev awayCover (t : Finset R) (ht : Ideal.span (t : Set R) = ⊤) :
    ((testSpec k).obj (op R)).left.OpenCover :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop
    (fun i : (t : Set R) ↦ i.val)
    ((congrArg Ideal.span (Subtype.range_val (s := (t : Set R)))).trans ht)).openCover

private theorem points_eq_of_awayCover (t : Finset R) (ht : Ideal.span (t : Set R) = ⊤)
    {p q : Points X R} (h : ∀ i : (t : Set R), mapPoints (awayMap R i.val) p =
      mapPoints (awayMap R i.val) q) : p = q := by
  apply Over.OverMorphism.ext
  apply (awayCover t ht).hom_ext
  intro i
  exact congrArg Over.Hom.left (h i)

private theorem mapPoints_comp {T : TestAlgebra k} (a : R ⟶ S) (c : S ⟶ T)
    (f : Points X R) :
    mapPoints c (mapPoints a f) = mapPoints (a ≫ c) f := by
  change (testSpec k).map c.op ≫ (testSpec k).map a.op ≫ f =
    (testSpec k).map (c.op ≫ a.op) ≫ f
  rw [Functor.map_comp, Category.assoc]

private theorem awayMap_left_range (r : R) :
    Set.range ((testSpec k).map (awayMap R r).op).left =
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) :=
  PrimeSpectrum.localization_away_comap_range (awayAlgebra R r) r

private def awayMapOfHom (a : R ⟶ S) (r : R) :
    awayAlgebra R r ⟶ awayAlgebra S (a.hom r) :=
  CommAlgCat.ofHom (Localization.awayMapₐ a.hom r)

private theorem awayMap_naturality (a : R ⟶ S) (r : R) :
    awayMap R r ≫ awayMapOfHom a r = a ≫ awayMap S (a.hom r) := by
  apply CommAlgCat.hom_ext
  ext x
  change IsLocalization.Away.map (Localization.Away r) (Localization.Away (a.hom r))
    a.hom.toRingHom r (algebraMap R (Localization.Away r) x) =
      algebraMap S (Localization.Away (a.hom r)) (a.hom x)
  simp [IsLocalization.Away.map]

private theorem span_finset_image (t : Finset R) (h : Ideal.span (t : Set R) = ⊤)
    [DecidableEq S] (a : R ⟶ S) :
    Ideal.span (t.image a.hom : Set S) = ⊤ := by
  rw [Finset.coe_image, ← Ideal.map_span, h, Ideal.map_top]

private def algHomOfPoint (p : Points ((testSpec k).obj (op R)) S) : R ⟶ S :=
  ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage p).unop

@[simp] private theorem map_algHomOfPoint (p : Points ((testSpec k).obj (op R)) S) :
    (testSpec k).map (algHomOfPoint p).op = p :=
  (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage p

end AffineCover

section AffinePointComparison

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V)
  {d : ℕ} {R S : TestAlgebra k}

private abbrev chartPlane (I : Pivot ι d) (f : Points (chartScheme (k := k) I) R) :
    Plane k V d R :=
  (graphChartMap b I).app R f

private theorem chartPlane_map (I : Pivot ι d) (a : R ⟶ S)
    (f : Points (chartScheme (k := k) I) R) :
    chartPlane b I (mapPoints a f) = Module.Grassmannian.map a.hom (chartPlane b I f) :=
  congrArg (fun g : Points (chartScheme (k := k) I) R ⟶ Plane k V d S ↦ g f)
    ((graphChartMap b I).naturality a)

private theorem plane_map_comp {T : TestAlgebra k} (a : R ⟶ S) (c : S ⟶ T)
    (L : Plane k V d R) :
    Module.Grassmannian.map (a ≫ c).hom L =
      Module.Grassmannian.map c.hom (Module.Grassmannian.map a.hom L) :=
  Module.Grassmannian.map_comp (Module.finrank k V - d) a.hom c.hom L

set_option backward.isDefEq.respectTransparency false in
private theorem gluedPoint_eq_iff_chartPlane_eq {I J : Pivot ι d}
    (f : Points (chartScheme (k := k) I) R) (g : Points (chartScheme (k := k) J) R) :
    f ≫ gluedChart b I = g ≫ gluedChart b J ↔ chartPlane b I f = chartPlane b J g := by
  rw [gluedChart_comp_eq_iff]
  constructor
  · intro h
    have h' := congrArg (fun α : Family k V d ((testSpec k).obj (op R)) ↦
      α.app R (𝟙 _)) h
    rw [chartFamily_apply, chartFamily_apply, Category.id_comp, Category.id_comp] at h'
    exact h'
  · intro h
    ext1
    funext T
    apply ConcreteCategory.hom_ext
    intro q
    let a := algHomOfPoint q
    have ha := map_algHomOfPoint q
    rw [chartFamily_apply, chartFamily_apply, ← ha]
    change chartPlane b I (mapPoints a f) = chartPlane b J (mapPoints a g)
    rw [chartPlane_map, chartPlane_map, h]

set_option backward.isDefEq.respectTransparency false in
private theorem locally_chart_point (p : Points (gluedGrassmannian b d) R) :
    ∃ t : Finset R, Ideal.span (t : Set R) = ⊤ ∧
      ∀ i : (t : Set R), ∃ (I : Pivot ι d) (f : Points (chartScheme (k := k) I) (awayAlgebra R i.val)),
        f ≫ gluedChart b I = mapPoints (awayMap R i.val) p := by
  let P (r : R) := ∃ (I : Pivot ι d)
    (f : Points (chartScheme (k := k) I) (awayAlgebra R r)),
      f ≫ gluedChart b I = mapPoints (awayMap R r) p
  have hloc (x : PrimeSpectrum R) : ∃ r ∉ x.asIdeal, P r := by
    obtain ⟨I, y, hy⟩ := gluedChart_cover b (p.left x)
    let U : TopologicalSpace.Opens (PrimeSpectrum R) :=
      p.left ⁻¹ᵁ (gluedChart b I).left.opensRange
    have hu : x ∈ U := ⟨y, hy⟩
    obtain ⟨_, ⟨r, rfl⟩, hr, hru⟩ :=
      (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open hu U.isOpen
    refine ⟨r, hr, I, ?_⟩
    let q := mapPoints (awayMap R r) p
    have hq : Set.range q.left ⊆ Set.range (gluedChart b I).left := by
      rintro _ ⟨z, rfl⟩
      apply hru
      have hz : ((testSpec k).map (awayMap R r).op).left z ∈
          Set.range ((testSpec k).map (awayMap R r).op).left := ⟨z, rfl⟩
      have hh : ((testSpec k).map (awayMap R r).op).left z ∈
          (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
        rw [← awayMap_left_range r]
        exact hz
      exact hh
    let f := IsOpenImmersion.lift (gluedChart b I).left q.left hq
    have hf : f ≫ (gluedChart b I).left = q.left := IsOpenImmersion.lift_fac _ _ _
    let F : Points (chartScheme (k := k) I) (awayAlgebra R r) :=
      Over.homMk f (by
        rw [← Over.w (gluedChart b I), ← Category.assoc, hf, Over.w q])
    exact ⟨F, Over.OverMorphism.ext hf⟩
  obtain ⟨t, ht, h⟩ := exists_principalCover P hloc
  exact ⟨t, ht, fun i ↦ h _ i.property⟩


/-- A matching plane has the indicated graph on every affine probe through a chart. -/
private def PointMatchesPlane (p : Points (gluedGrassmannian b d) R)
    (L : Plane k V d R) : Prop :=
  ∀ (S : TestAlgebra k) (a : R ⟶ S) (I : Pivot ι d)
    (f : Points (chartScheme (k := k) I) S), f ≫ gluedChart b I = mapPoints a p →
      chartPlane b I f = Module.Grassmannian.map a.hom L

set_option maxHeartbeats 650000 in
private theorem pointMatchesPlane_of_cover (p : Points (gluedGrassmannian b d) R)
    (L : Plane k V d R) (t : Finset R) (ht : Ideal.span (t : Set R) = ⊤)
    (I : ↥(t : Set R) → Pivot ι d)
    (f : ∀ i : (t : Set R), Points (chartScheme (k := k) (I i)) (awayAlgebra R i.val))
    (hf : ∀ i, f i ≫ gluedChart b (I i) = mapPoints (awayMap R i.val) p)
    (hL : ∀ i, chartPlane b (I i) (f i) = Module.Grassmannian.map (awayMap R i.val).hom L) :
    PointMatchesPlane b p L := by
  classical
  intro S a J g hg
  apply plane_eq_of_localizations (t.image a.hom) (span_finset_image t ht a)
  intro ⟨y, hy⟩
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
  let j : (t : Set R) := ⟨r, hr⟩
  have hh : mapPoints (awayMapOfHom a r) (f j) ≫ gluedChart b (I j) =
      mapPoints (awayMap S (a.hom r)) g ≫ gluedChart b J := by
    change (testSpec k).map (awayMapOfHom a r).op ≫ f j ≫ gluedChart b (I j) =
      (testSpec k).map (awayMap S (a.hom r)).op ≫ g ≫ gluedChart b J
    rw [hf j, hg]
    change mapPoints (awayMapOfHom a r) (mapPoints (awayMap R r) p) =
      mapPoints (awayMap S (a.hom r)) (mapPoints a p)
    rw [mapPoints_comp, mapPoints_comp, awayMap_naturality]
  have h := (gluedPoint_eq_iff_chartPlane_eq b _ _).mp hh
  rw [chartPlane_map, chartPlane_map, hL j,
    ← plane_map_comp (awayMap R r) (awayMapOfHom a r),
    awayMap_naturality, plane_map_comp] at h
  exact h.symm

private theorem exists_plane_of_point (p : Points (gluedGrassmannian b d) R) :
    ∃ L, PointMatchesPlane b p L := by
  obtain ⟨t, ht, hloc⟩ := locally_chart_point b p
  choose I f hf using hloc
  let L (i : (t : Set R)) := chartPlane b (I i) (f i)
  have hL (i j : (t : Set R)) :
      Module.Grassmannian.map (doubleAwayLeft i.val j.val).hom (L i) =
        Module.Grassmannian.map (doubleAwayRight i.val j.val).hom (L j) := by
    let a := doubleAwayLeft i.val j.val
    let c := doubleAwayRight i.val j.val
    rw [← chartPlane_map b (I i), ← chartPlane_map b (I j)]
    apply (gluedPoint_eq_iff_chartPlane_eq b _ _).mp
    change (testSpec k).map a.op ≫ f i ≫ gluedChart b (I i) =
      (testSpec k).map c.op ≫ f j ≫ gluedChart b (I j)
    rw [hf i, hf j]
    change mapPoints a (mapPoints (awayMap R i.val) p) =
      mapPoints c (mapPoints (awayMap R j.val) p)
    rw [mapPoints_comp, mapPoints_comp]
    exact congrArg (fun z ↦ mapPoints z p) (doubleAway_comp i.val j.val)
  obtain ⟨P, hP⟩ := plane_descent t L ht hL
  exact ⟨P, pointMatchesPlane_of_cover b p P t ht I f hf (fun i ↦ (hP i).symm)⟩

private theorem matchesPlane_unique (p : Points (gluedGrassmannian b d) R)
    {L M : Plane k V d R} (hL : PointMatchesPlane b p L) (hM : PointMatchesPlane b p M) :
    L = M := by
  obtain ⟨t, ht, hloc⟩ := locally_chart_point b p
  apply plane_eq_of_localizations t ht
  intro i
  obtain ⟨I, f, hf⟩ := hloc i
  exact (hL _ _ _ _ hf).symm.trans (hM _ _ _ _ hf)

private theorem point_matches_chart (I : Pivot ι d)
    (f : Points (chartScheme (k := k) I) R) :
    PointMatchesPlane b (f ≫ gluedChart b I) (chartPlane b I f) := by
  intro S a J g hg
  have h : g ≫ gluedChart b J = mapPoints a f ≫ gluedChart b I :=
    hg.trans (Category.assoc _ _ _).symm
  exact ((gluedPoint_eq_iff_chartPlane_eq b _ _).mp h).trans (chartPlane_map b I a f)

private theorem matchesPoint_unique
    (p q : Points (gluedGrassmannian b d) R) (L : Plane k V d R)
    (hp : PointMatchesPlane b p L) (hq : PointMatchesPlane b q L) :
    p = q := by
  obtain ⟨t, ht, hloc⟩ := locally_chart_point b p
  apply points_eq_of_awayCover t ht
  intro i
  obtain ⟨I, f, hf⟩ := hloc i
  let S := awayAlgebra R i.val
  let a := awayMap R i.val
  obtain ⟨t', ht', hloc'⟩ := locally_chart_point b (mapPoints a q)
  apply points_eq_of_awayCover t' ht'
  intro j
  obtain ⟨J, g, hg⟩ := hloc' j
  let c := awayMap S j.val
  have hp' : mapPoints c f ≫ gluedChart b I = mapPoints (a ≫ c) p := by
    change ((testSpec k).map c.op ≫ f) ≫ gluedChart b I = _
    rw [Category.assoc, hf]
    exact mapPoints_comp a c p
  have hq' : g ≫ gluedChart b J = mapPoints (a ≫ c) q := hg.trans (mapPoints_comp a c q)
  have h := (gluedPoint_eq_iff_chartPlane_eq b _ _).mpr
    ((hp _ _ _ _ hp').trans (hq _ _ _ _ hq').symm)
  calc
    mapPoints c (mapPoints a p) = mapPoints c f ≫ gluedChart b I :=
      (mapPoints_comp a c p).trans hp'.symm
    _ = g ≫ gluedChart b J := h
    _ = mapPoints c (mapPoints a q) := hg

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_point_of_plane (hd : d ≤ Module.finrank k V)
    (L : Plane k V d R) :
    ∃ p : Points (gluedGrassmannian b d) R, PointMatchesPlane b p L := by
  obtain ⟨t, ht, hloc⟩ := exists_principalCover
    (fun r : R ↦ ∃ I : Pivot ι d,
      IsPivot b I (awayAlgebra R r) (Module.Grassmannian.map (awayMap R r).hom L))
    (plane_exists_pivot_away b hd R L)
  choose I hI using fun i : (t : Set R) ↦ hloc i.val i.property
  let A (i : (t : Set R)) := awayAlgebra R i.val
  let f (i : (t : Set R)) : Points (chartScheme (k := k) (I i)) (A i) :=
    (graphChartEquiv b (I i) (A i)).symm ⟨Module.Grassmannian.map (awayMap R i.val).hom L, hI i⟩
  have hL (i : (t : Set R)) :
      chartPlane b (I i) (f i) = Module.Grassmannian.map (awayMap R i.val).hom L :=
    congrArg Subtype.val ((graphChartEquiv b (I i) (A i)).apply_symm_apply _)
  let U := awayCover t ht
  let g (i : U.I₀) := f i ≫ gluedChart b (I i)
  have hglue (i j : U.I₀) :
      pullback.fst (U.f i) (U.f j) ≫ (g i).left =
      pullback.snd (U.f i) (U.f j) ≫ (g j).left := by
    let a := (testSpec k).map (awayMap R i.val).op
    let c := (testSpec k).map (awayMap R j.val).op
    let B := Over.mk ((pullback.fst a.left c.left ≫ a.left) ≫ ((testSpec k).obj (op R)).hom)
    let l : B ⟶ (testSpec k).obj (op (A i)) := Over.homMk (pullback.fst a.left c.left) (by
      change pullback.fst a.left c.left ≫ ((testSpec k).obj (op (A i))).hom = _
      rw [← Over.w a, ← Category.assoc]
      rfl)
    let r : B ⟶ (testSpec k).obj (op (A j)) := Over.homMk (pullback.snd a.left c.left) (by
      change pullback.snd a.left c.left ≫ ((testSpec k).obj (op (A j))).hom = _
      rw [← Over.w c, ← Category.assoc, ← pullback.condition]
      rfl)
    have hlr : l ≫ a = r ≫ c := Over.OverMorphism.ext pullback.condition
    have he : l ≫ g i = r ≫ g j := by
      apply hom_ext_on_affines
      intro T x
      let α := algHomOfPoint (x ≫ l)
      let β := algHomOfPoint (x ≫ r)
      have hα : (testSpec k).map α.op = x ≫ l := map_algHomOfPoint _
      have hβ : (testSpec k).map β.op = x ≫ r := map_algHomOfPoint _
      have hab : awayMap R i.val ≫ α = awayMap R j.val ≫ β := by
        have H : (awayMap R i.val ≫ α).op = (awayMap R j.val ≫ β).op :=
          (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective (by
            change (testSpec k).map (α.op ≫ (awayMap R i.val).op) =
              (testSpec k).map (β.op ≫ (awayMap R j.val).op)
            simp only [Functor.map_comp, hα, hβ]
            rw [Category.assoc, Category.assoc, hlr])
        exact congrArg Quiver.Hom.unop H
      rw [← Category.assoc x, ← Category.assoc x, ← hα, ← hβ]
      change (testSpec k).map α.op ≫ f i ≫ gluedChart b (I i) =
        (testSpec k).map β.op ≫ f j ≫ gluedChart b (I j)
      rw [← Category.assoc, ← Category.assoc]
      apply (gluedPoint_eq_iff_chartPlane_eq b _ _).mpr
      change chartPlane b (I i) (mapPoints α (f i)) =
        chartPlane b (I j) (mapPoints β (f j))
      rw [chartPlane_map, chartPlane_map, hL i, hL j, ← plane_map_comp, ← plane_map_comp, hab]
    exact congrArg Over.Hom.left he
  let p := U.glueMorphisms (fun i ↦ (g i).left) hglue
  have hp : p ≫ (gluedGrassmannian b d).hom = ((testSpec k).obj (op R)).hom := by
    apply U.hom_ext
    intro i
    have hi : U.f i ≫ p = (g i).left := U.ι_glueMorphisms (fun j ↦ (g j).left) hglue i
    rw [← Category.assoc, hi]
    exact (Over.w (g i)).trans (Over.w ((testSpec k).map (awayMap R i.val).op)).symm
  let P : Points (gluedGrassmannian b d) R := Over.homMk p hp
  refine ⟨P, pointMatchesPlane_of_cover b P L t ht I f ?_ hL⟩
  intro i
  apply Over.OverMorphism.ext
  change (g i).left = U.f i ≫ p
  exact (U.ι_glueMorphisms (fun j ↦ (g j).left) hglue i).symm

private def planeOfPoint (p : Points (gluedGrassmannian b d) R) : Plane k V d R :=
  (exists_plane_of_point b p).choose

private theorem planeOfPoint_matches (p : Points (gluedGrassmannian b d) R) :
    PointMatchesPlane b p (planeOfPoint b p) :=
  (exists_plane_of_point b p).choose_spec

private theorem planeOfPoint_chart (I : Pivot ι d)
    (f : Points (chartScheme (k := k) I) R) :
    planeOfPoint b (f ≫ gluedChart b I) = chartPlane b I f :=
  matchesPlane_unique b _ (planeOfPoint_matches b _) (point_matches_chart b I f)

private theorem planeOfPoint_natural (a : R ⟶ S) (p : Points (gluedGrassmannian b d) R) :
    planeOfPoint b (mapPoints a p) = Module.Grassmannian.map a.hom (planeOfPoint b p) := by
  apply matchesPlane_unique b _ (planeOfPoint_matches b _)
  intro T c J f hf
  rw [mapPoints_comp] at hf
  exact (planeOfPoint_matches b p T (a ≫ c) J f hf).trans (plane_map_comp a c _)

set_option maxHeartbeats 600000 in
private def gluedAffinePoints (hd : d ≤ Module.finrank k V) :
    pointsFunctor (gluedGrassmannian b d) ≅ planeFunctor k V d :=
  NatIso.ofComponents
    (fun R ↦ (Equiv.ofBijective (planeOfPoint (R := R) b)
      ⟨fun p q h ↦ matchesPoint_unique b p q _ (planeOfPoint_matches b p)
          (h ▸ planeOfPoint_matches b q),
        fun L ↦ by
          obtain ⟨p, hp⟩ := exists_point_of_plane b hd L
          exact ⟨p, matchesPlane_unique b p (planeOfPoint_matches b p) hp⟩⟩).toIso)
    (fun a ↦ by
      apply ConcreteCategory.hom_ext
      intro p
      exact planeOfPoint_natural b a p)

private def chartSystem (hd : d ≤ Module.finrank k V) : ChartSystem (k := k) (V := V) b d where
  scheme := gluedGrassmannian b d
  affinePoints := gluedAffinePoints b hd
  chart := gluedChart b
  openChart := fun _ ↦ inferInstance
  cover := gluedChart_cover b
  coordinates_eq I R f := by
    change (planeOfPoint b (f ≫ gluedChart b I)).toSubmodule = _
    rw [planeOfPoint_chart]
    exact graphPlane_toSubmodule b I R _
  factor_iff I R p := by
    change (∃ f, f ≫ gluedChart b I = p) ↔ IsPivot b I R (planeOfPoint b p)
    constructor
    · rintro ⟨f, rfl⟩
      rw [planeOfPoint_chart]
      exact (graphChartEquiv b I R f).property
    · intro h
      let f := (graphChartEquiv b I R).symm ⟨planeOfPoint b p, h⟩
      have he : chartPlane b I f = planeOfPoint b p :=
        congrArg Subtype.val ((graphChartEquiv b I R).apply_symm_apply _)
      exact ⟨f, matchesPoint_unique b _ p _ (he ▸ point_matches_chart b I f)
        (planeOfPoint_matches b p)⟩
  overlap := gluedChart_overlap b
  transition I J R f g h :=
    graphTransition k V ι b I J R _ _
      (congrArg (fun L : Plane k V d R ↦ L.toSubmodule)
        ((gluedPoint_eq_iff_chartPlane_eq b _ _).mp h))

theorem affineConstruction : AffineConstruction.{u} := by
  intro k V ι _ _ _ _ _ b d hd
  exact ⟨chartSystem b hd⟩


end AffinePointComparison

end AffineRepresentability

section IntrinsicAffineSubbundles

open TensorProduct
open scoped AlgebraicGeometry

section PullbackTilde

variable {A B : CommRingCat.{u}} (a : A ⟶ B)

set_option backward.isDefEq.respectTransparency false in
private def sectionsPushforwardIsoApp (M : (Spec B).Modules) :
    (Scheme.Modules.pushforward (Spec.map a) ⋙ moduleSpecΓFunctor (R := A)).obj M ≅
      (moduleSpecΓFunctor (R := B) ⋙ ModuleCat.restrictScalars a.hom).obj M := by
  let e : ((Scheme.Modules.pushforward (Spec.map a) ⋙ moduleSpecΓFunctor (R := A)).obj M) ≃ₗ[A]
      (moduleSpecΓFunctor (R := B) ⋙ ModuleCat.restrictScalars a.hom).obj M :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        let y : Γ(M, ⊤) := x
        change (Spec.map a).appTop ((Scheme.ΓSpecIso A).inv r) • y =
          (Scheme.ΓSpecIso B).inv (a r) • y
        rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_inv_naturality] }
  exact e.toModuleIso

set_option backward.isDefEq.respectTransparency false in
private def sectionsPushforwardIso :
    Scheme.Modules.pushforward (Spec.map a) ⋙ moduleSpecΓFunctor (R := A) ≅
      moduleSpecΓFunctor (R := B) ⋙ ModuleCat.restrictScalars a.hom :=
  NatIso.ofComponents (sectionsPushforwardIsoApp a) fun f ↦ by
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun _ ↦ rfl

/-- Pullback along a morphism of affine schemes sheafifies extension of scalars. -/
def affinePullbackTilde :
    tilde.functor A ⋙ Scheme.Modules.pullback (Spec.map a) ≅
      ModuleCat.extendScalars a.hom ⋙ tilde.functor B :=
  (((tilde.adjunction (R := A)).comp (Scheme.Modules.pullbackPushforwardAdjunction
    (Spec.map a))).ofNatIsoRight
      (sectionsPushforwardIso a)).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj a.hom).comp (tilde.adjunction (R := B)))

end PullbackTilde

section TensorExtension
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

private def moduleTensorFunctor (i : Algebra A B) : ModuleCat.{u} A ⥤ ModuleCat.{u} B := by
  letI : Algebra A B := i
  exact {
    obj := fun M ↦ ModuleCat.of B (B ⊗[A] M)
    map := fun f ↦ ModuleCat.ofHom (f.hom.baseChange B)
    map_id := by
      intro M
      apply ModuleCat.hom_ext
      exact LinearMap.baseChange_id
    map_comp := by
      intro M N P f g
      apply ModuleCat.hom_ext
      exact LinearMap.baseChange_comp (A := B) f.hom g.hom }

private theorem extendScalars_eq_moduleTensorFunctor :
    ModuleCat.extendScalars (algebraMap A B) = moduleTensorFunctor ‹Algebra A B› := by
  have ha : (algebraMap A B).toAlgebra = ‹Algebra A B› :=
    Algebra.algebra_ext _ _ (fun _ ↦ rfl)
  exact congrArg moduleTensorFunctor ha

/-- The tensor product comparison is natural in the module on the source affine scheme. -/
def affinePullbackTensorNat :
    tilde.functor (CommRingCat.of A) ⋙
      Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≅
        moduleTensorFunctor ‹Algebra A B› ⋙ tilde.functor (CommRingCat.of B) :=
  affinePullbackTilde (CommRingCat.ofHom (algebraMap A B)) ≪≫
    Functor.isoWhiskerRight (eqToIso extendScalars_eq_moduleTensorFunctor) _

set_option backward.isDefEq.respectTransparency false in
private def restrictTildeOfFreeAway (r : A) (M : ModuleCat.{u} A) {I : Type u}
    (e : Localization.Away r ⊗[A] M ≃ₗ[Localization.Away r] (I →₀ Localization.Away r)) :
    (Scheme.Modules.restrictFunctor
      (Scheme.Opens.ι (X := Spec (CommRingCat.of A)) (PrimeSpectrum.basicOpen r))).obj (tilde M)
        ≅ SheafOfModules.free I := by
  let U : (Spec (CommRingCat.of A)).Opens := PrimeSpectrum.basicOpen r
  let h := basicOpenIsoSpecAway (R := CommRingCat.of A) r
  let j := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r)))
  let F := Scheme.Modules.pullback h.hom
  have hj : U.ι = h.hom ≫ j := (basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of A) r).symm
  let e' := (affinePullbackTensorNat (A := A) (B := Localization.Away r)).app M ≪≫
    (tilde.functor (CommRingCat.of (Localization.Away r))).mapIso e.toModuleIso ≪≫ tildeFinsupp I
  letI : (SheafOfModules.pushforward h.hom.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward h.hom).IsRightAdjoint
  exact (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫
    (Scheme.Modules.pullbackCongr hj).app _ ≪≫
    (Scheme.Modules.pullbackComp h.hom j).symm.app _ ≪≫ F.mapIso e' ≪≫
    SheafOfModules.pullbackObjFreeIso h.hom.toRingCatSheafHom I

end TensorExtension

section AffineSubbundle

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V)
  {d : ℕ} (hd : d ≤ Module.finrank k V) (R : TestAlgebra k)

private def sheafPlaneArrow (L : Plane k V d R) :
    tilde (ModuleCat.of R L.toSubmodule) ⟶ ambient k V ((testSpec k).obj (op R)) :=
  (tilde.functor (CommRingCat.of R)).map (ModuleCat.ofHom L.toSubmodule.subtype) ≫
    (affineAmbientOfBasis (k := k) (V := V) b R).inv

omit [DecidableEq ι] in
include hd in
set_option backward.isDefEq.respectTransparency false in
private theorem sheafPlaneArrow_split (L : Plane k V d R) :
    IsSplitMono (sheafPlaneArrow b R L) := by
  let : Module.Finite k V := Module.Finite.of_basis b
  obtain ⟨C, hC⟩ := (planeSplitAndRank k V d hd R L).1
  let p := L.toSubmodule.projectionOnto C hC
  let i : ModuleCat.of R L.toSubmodule ⟶ ModuleCat.of R (R ⊗[k] V) :=
    ModuleCat.ofHom L.toSubmodule.subtype
  let q : ModuleCat.of R (R ⊗[k] V) ⟶ ModuleCat.of R L.toSubmodule :=
    ModuleCat.ofHom p
  have h : i ≫ q = 𝟙 _ := ModuleCat.hom_ext
    (LinearMap.ext (Submodule.projectionOnto_apply_left hC))
  refine IsSplitMono.mk' ⟨(affineAmbientOfBasis (k := k) (V := V) b R).hom ≫
    (tilde.functor (CommRingCat.of R)).map q, ?_⟩
  rw [sheafPlaneArrow, Category.assoc]
  change (tilde.functor (CommRingCat.of R)).map i ≫
    (affineAmbientOfBasis (k := k) (V := V) b R).inv ≫ _ = _
  simp only [Iso.inv_hom_id_assoc, ← Functor.map_comp, h]
  exact (tilde.functor (CommRingCat.of R)).map_id (ModuleCat.of R L.toSubmodule)

private lemma isSplitMono_map {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} (i : X ⟶ Y) [IsSplitMono i] : IsSplitMono (F.map i) :=
  IsSplitMono.mk' ⟨F.map (retraction i), by rw [← F.map_comp, IsSplitMono.id, F.map_id]⟩

include b hd in
private theorem sheafPlane_locallyFree (L : Plane k V d R)
    (x : ((testSpec k).obj (op R)).left) :
    ∃ U : ((testSpec k).obj (op R)).left.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj (tilde (ModuleCat.of R L.toSubmodule)) ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin d))) := by
  obtain ⟨r, hr, I, hI⟩ := plane_exists_pivot_away b hd R L x
  let U : ((testSpec k).obj (op R)).left.Opens := PrimeSpectrum.basicOpen r
  let S := awayAlgebra R r
  let : Algebra R S := inferInstanceAs (Algebra R (Localization.Away r))
  let : IsScalarTower k R S := inferInstanceAs (IsScalarTower k R (Localization.Away r))
  let P := Module.Grassmannian.map (awayMap R r).hom L
  let e : S ⊗[R] L.toSubmodule ≃ₗ[S] P.toSubmodule := planePullbackEquiv b hd L
  let ep : P.toSubmodule ≃ₗ[S] (Inside I → S) :=
    LinearEquiv.ofBijective _ hI
  let eI : Inside I ≃ ULift.{u} (Fin d) := (pivotOrder I).trans Equiv.ulift.symm
  let E := e ≪≫ₗ ep ≪≫ₗ LinearEquiv.funCongrLeft S S eI.symm ≪≫ₗ
    (Finsupp.linearEquivFunOnFinite S S (ULift.{u} (Fin d))).symm
  exact ⟨U, hr, ⟨restrictTildeOfFreeAway r (ModuleCat.of R L.toSubmodule) E⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The tilde sheaf of an affine plane is a locally split subbundle of the constant bundle. -/
def affinePlaneSubbundle (L : Plane k V d R) :
    Subbundles k V d ((testSpec k).obj (op R)) := by
  let a := sheafPlaneArrow b R L
  let : IsSplitMono a := sheafPlaneArrow_split b hd R L
  let P := Subobject.mk a
  let e := Subobject.underlyingIso a
  refine ⟨P, fun x ↦ ?_⟩
  obtain ⟨U, hU, ⟨eU⟩⟩ := sheafPlane_locallyFree b hd R L x
  let F := Scheme.Modules.restrictFunctor U.ι
  refine ⟨U, hU, ⟨F.mapIso e ≪≫ eU⟩, ?_⟩
  have hP : P.arrow = e.hom ≫ a := (Subobject.underlyingIso_hom_comp_eq_mk a).symm
  have : IsSplitMono P.arrow := IsSplitMono.mk' ⟨retraction a ≫ e.inv, by simp [hP]⟩
  exact isSplitMono_map F P.arrow

set_option backward.isDefEq.respectTransparency false in
theorem affinePlaneSubbundle_isTilde (L : Plane k V d R) :
    IsTildePlane (k := k) (V := V) b R L (affinePlaneSubbundle b hd R L) := by
  let a := sheafPlaneArrow b R L
  let : IsSplitMono a := sheafPlaneArrow_split b hd R L
  refine ⟨(Subobject.underlyingIso a).symm, ?_⟩
  change (Subobject.underlyingIso a).inv ≫ (Subobject.mk a).arrow ≫ _ = _
  simp [a, sheafPlaneArrow]

omit [Fintype ι] [DecidableEq ι] in
theorem isTildePlane_uniqueSubbundle (L : Plane k V d R)
    (P Q : Subbundles k V d ((testSpec k).obj (op R)))
    (hP : IsTildePlane (k := k) (V := V) b R L P) (hQ : IsTildePlane (k := k) (V := V) b R L Q) : P = Q := by
  obtain ⟨eP, hP⟩ := hP
  obtain ⟨eQ, hQ⟩ := hQ
  apply Subtype.ext
  apply Subobject.eq_of_comm (eP.symm ≪≫ eQ)
  rw [← cancel_mono (affineAmbientOfBasis (k := k) (V := V) b R).hom]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hQ, ← hP,
    Iso.inv_hom_id_assoc]

end AffineSubbundle

section LocallyFree

set_option backward.isDefEq.respectTransparency false in
private theorem isQuasicoherent_of_localFree {X : Scheme.{u}} (M : X.Modules) (I : Type u)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj M ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)) : M.IsQuasicoherent := by
  choose U hmem he using h
  have hcov : (Opens.grothendieckTopology X).CoversTop U := by
    apply (Opens.coversTop_iff X U).mpr
    rw [TopologicalSpace.IsOpenCover]
    exact top_unique (fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hmem x⟩)
  have hqc (x : X) : (SheafOfModules.over M (U x)).IsQuasicoherent := by
    let Ux := U x
    let E := Scheme.Modules.overEquiv Ux
    let F := E.inverse
    let e0 := (Scheme.Modules.overFunctorEquiv Ux).app M ≪≫ (he x).some
    let u := TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit Ux X.ringCatSheaf
    let e : SheafOfModules.over M Ux ≅
        SheafOfModules.free (R := X.ringCatSheaf.over Ux) I :=
      E.unitIso.app _ ≪≫ F.mapIso e0 ≪≫ (SheafOfModules.mapFreeIso F I u.symm).symm
    exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over Ux)).prop_of_iso e.symm inferInstance
  exact SheafOfModules.IsQuasicoherent.of_coversTop M U hcov

end LocallyFree

section TildeSubmodule

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
  (b : Module.Basis ι k V) {d : ℕ} (R : TestAlgebra k)

set_option backward.isDefEq.respectTransparency false in
/-- An affine subbundle is the tilde of a submodule of the scalar extension, with
the inclusion itself identified by the tilde functor. -/
private theorem subbundle_is_tildeSubmodule (L : Subbundles k V d ((testSpec k).obj (op R))) :
    ∃ (P : Submodule R (R ⊗[k] V))
      (e : tilde (ModuleCat.of R P) ≅ (L.val : ((testSpec k).obj (op R)).left.Modules)),
      e.hom ≫ L.val.arrow ≫ (affineAmbientOfBasis (k := k) (V := V) b R).hom =
        (tilde.functor (CommRingCat.of R)).map (ModuleCat.ofHom P.subtype) := by
  let N : (Spec (CommRingCat.of R)).Modules :=
    (L.val : ((testSpec k).obj (op R)).left.Modules)
  have hqc : N.IsQuasicoherent :=
    isQuasicoherent_of_localFree N (ULift.{u} (Fin d)) fun x ↦ by
      obtain ⟨U, hx, hU, _⟩ := L.property x
      exact ⟨U, hx, hU⟩
  let F := tilde.functor (CommRingCat.of R)
  let e := asIso N.fromTildeΓ
  let j := (affineAmbientOfBasis (k := k) (V := V) b R).hom
  let ff := tilde.fullyFaithfulFunctor (R := CommRingCat.of R)
  let a := e.hom ≫ L.val.arrow ≫ j
  let f := ff.preimage a
  have hf : F.map f = a := ff.map_preimage a
  have hmono : Mono (F.map f) := by
    rw [hf]
    dsimp only [a]
    infer_instance
  have hmonof : Mono f := by
    constructor
    intro Z g h hgh
    apply ff.map_injective
    have hh := congrArg F.map hgh
    rw [F.map_comp, F.map_comp] at hh
    exact (cancel_mono (F.map f)).mp hh
  let P := f.hom.range
  let eLin := LinearEquiv.ofInjective f.hom ((ModuleCat.mono_iff_injective f).mp hmonof)
  let u := eLin.symm.toModuleIso
  have hcomp : u.hom ≫ f = ModuleCat.ofHom P.subtype :=
    ModuleCat.hom_ext (LinearMap.ext fun x ↦ congrArg Subtype.val (eLin.apply_symm_apply x))
  refine ⟨P, F.mapIso u ≪≫ e, ?_⟩
  change (F.map u.hom ≫ e.hom) ≫ L.val.arrow ≫ j = _
  rw [Category.assoc]
  change F.map u.hom ≫ a = F.map (ModuleCat.ofHom P.subtype)
  calc
    _ = F.map u.hom ≫ F.map f := congrArg (F.map u.hom ≫ ·) hf.symm
    _ = F.map (u.hom ≫ f) := (F.map_comp _ _).symm
    _ = _ := congrArg F.map hcomp

end TildeSubmodule

section LocalFreeSplit

private theorem isSplitMono_of_commuting_isos {C : Type*} [Category C]
    {X Y X' Y' : C} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : X ≅ X') (j : Y ≅ Y') (h : f ≫ j.hom = e.hom ≫ g)
    (hf : IsSplitMono f) : IsSplitMono g := by
  let := hf
  have hg : g = e.inv ≫ f ≫ j.hom := by rw [h, Iso.inv_hom_id_assoc]
  refine IsSplitMono.mk' ⟨j.inv ≫ retraction f ≫ e.hom, ?_⟩
  rw [hg]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, IsSplitMono.id_assoc, Iso.inv_hom_id]

private def pullbackCompRestriction {X Y Z : Scheme.{u}} (h : X ⟶ Z)
    (f : X ⟶ Y) (j : Y ⟶ Z) [IsOpenImmersion j]
    (heq : f ≫ j = h) :
    Scheme.Modules.pullback h ≅ Scheme.Modules.restrictFunctor j ⋙ Scheme.Modules.pullback f :=
  Scheme.Modules.pullbackCongr heq.symm ≪≫ (Scheme.Modules.pullbackComp f j).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback j).symm _

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
  (b : Module.Basis ι k V) {d : ℕ} (R : TestAlgebra k)

set_option maxHeartbeats 1100000 in
set_option backward.isDefEq.respectTransparency false in
private theorem subbundle_away_free_split
    (L : Subbundles k V d ((testSpec k).obj (op R))) (P : Submodule R (R ⊗[k] V))
    (e : tilde (ModuleCat.of R P) ≅ (L.val : ((testSpec k).obj (op R)).left.Modules))
    (he : e.hom ≫ L.val.arrow ≫ (affineAmbientOfBasis (k := k) (V := V) b R).hom =
      (tilde.functor (CommRingCat.of R)).map (ModuleCat.ofHom P.subtype))
    (x : PrimeSpectrum R) :
    ∃ r ∉ x.asIdeal, Nonempty
      (Localization.Away r ⊗[R] P ≃ₗ[Localization.Away r]
        (ULift.{u} (Fin d) →₀ Localization.Away r)) ∧
      ∃ q : (Localization.Away r ⊗[R] (R ⊗[k] V)) →ₗ[Localization.Away r]
          (Localization.Away r ⊗[R] P), q.comp (P.subtype.baseChange _) = LinearMap.id := by
  obtain ⟨U, hU, ⟨u⟩, hs⟩ := L.property x
  let W : TopologicalSpace.Opens (PrimeSpectrum R) := U
  have hx : x ∈ W := hU
  obtain ⟨_, ⟨r, rfl⟩, hr, hle⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open hx W.isOpen
  refine ⟨r, hr, ?_⟩
  let S := Localization.Away r
  let j := Spec.map (CommRingCat.ofHom (algebraMap R S))
  have hj : Set.range j ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    change Set.range (PrimeSpectrum.comap (algebraMap R S)) ⊆ (W : Set (PrimeSpectrum R))
    rw [PrimeSpectrum.localization_away_comap_range S r]
    exact hle
  let f := IsOpenImmersion.lift U.ι j hj
  let H := pullbackCompRestriction j f U.ι (IsOpenImmersion.lift_fac _ _ _)
  let F := Scheme.Modules.pullback j
  let G := Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback f
  let T := tilde.functor (CommRingCat.of R)
  let T' := tilde.functor (CommRingCat.of S)
  let N := ModuleCat.of R (R ⊗[k] V)
  let P' := ModuleCat.of R P
  let i : P' ⟶ N := ModuleCat.ofHom P.subtype
  let i' : ModuleCat.of S (S ⊗[R] P) ⟶ ModuleCat.of S (S ⊗[R] (R ⊗[k] V)) :=
    ModuleCat.ofHom (P.subtype.baseChange S)
  let M : (Spec (CommRingCat.of R)).Modules :=
    (L.val : ((testSpec k).obj (op R)).left.Modules)
  let A := affineAmbientOfBasis (k := k) (V := V) b R
  let B := affinePullbackTensorNat (A := R) (B := S)
  have hG : IsSplitMono (G.map L.val.arrow) :=
    isSplitMono_map (Scheme.Modules.pullback f) ((Scheme.Modules.restrictFunctor U.ι).map L.val.arrow)
  have hF : IsSplitMono (F.map L.val.arrow) :=
    isSplitMono_of_commuting_isos (H.symm.app M) (H.symm.app _) (H.inv.naturality L.val.arrow) hG
  have hi : L.val.arrow ≫ A.hom = e.inv ≫ T.map i := by
    rw [← he, Iso.inv_hom_id_assoc]
  have hsF : IsSplitMono (F.map (T.map i)) := by
    refine isSplitMono_of_commuting_isos (f := F.map L.val.arrow)
      (F.mapIso e.symm) (F.mapIso A) ?_ hF
    rw [Functor.mapIso_hom, Functor.mapIso_hom, ← F.map_comp, ← F.map_comp, hi]
    rfl
  have hi' : IsSplitMono (T'.map i') :=
    isSplitMono_of_commuting_isos (B.app P') (B.app N) (B.hom.naturality i) hsF
  let ff := tilde.fullyFaithfulFunctor (R := CommRingCat.of S)
  constructor
  · let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
      inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
    let v := (B.app P').symm ≪≫ F.mapIso e ≪≫ H.app M ≪≫
      (Scheme.Modules.pullback f).mapIso u ≪≫
      SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (ULift.{u} (Fin d)) ≪≫
      (tildeFinsupp (R := CommRingCat.of S) (ULift.{u} (Fin d))).symm
    exact ⟨(ff.preimageIso v).toLinearEquiv⟩
  · let q := ff.preimage (retraction (T'.map i'))
    have hq : i' ≫ q = 𝟙 _ := by
      apply ff.map_injective
      change T'.map (i' ≫ q) = T'.map (𝟙 _)
      rw [T'.map_comp, T'.map_id]
      have heq : T'.map q = retraction (T'.map i') := ff.map_preimage _
      rw [heq]
      exact IsSplitMono.id (T'.map i')
    exact ⟨q.hom, congrArg ModuleCat.Hom.hom hq⟩

end LocalFreeSplit

section RankOfLocalSummands

open TensorProduct.AlgebraTensorModule
variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
  {d : ℕ} (R : TestAlgebra k) (P : Submodule R (R ⊗[k] V))

set_option backward.isDefEq.respectTransparency false in
private theorem localizedQuotient_rank_of_split (r : R)
    (h : Nonempty (Localization.Away r ⊗[R] P ≃ₗ[Localization.Away r]
        (ULift.{u} (Fin d) →₀ Localization.Away r)) ∧
      ∃ q : (Localization.Away r ⊗[R] (R ⊗[k] V)) →ₗ[Localization.Away r]
        (Localization.Away r ⊗[R] P), q.comp (P.subtype.baseChange _) = LinearMap.id) :
    Module.Finite (Localization.Away r) (LocalizedModule.Away r ((R ⊗[k] V) ⧸ P)) ∧
      Module.Projective (Localization.Away r) (LocalizedModule.Away r ((R ⊗[k] V) ⧸ P)) ∧
      ∀ p : PrimeSpectrum (Localization.Away r),
        Module.rankAtStalk (LocalizedModule.Away r ((R ⊗[k] V) ⧸ P)) p = Module.finrank k V - d := by
  obtain ⟨⟨u⟩, q, hq⟩ := h
  let S := Localization.Away r
  let Q := (R ⊗[k] V) ⧸ P
  let f := P.subtype.baseChange S
  let g := P.mkQ.baseChange S
  have hg : Function.Surjective g := LinearMap.baseChange_surjective S P.mkQ_surjective
  have hex : Function.Exact f g := by
    rw [LinearMap.exact_iff]
    exact SetLike.ext (fun x ↦ SetLike.ext_iff.mp (lTensor_mkQ S P) x)
  let e := (hex.splitInjectiveEquiv hg ⟨q, hq⟩).val
  let s := e.symm.toLinearMap.comp (LinearMap.inr S (S ⊗[R] P) (S ⊗[R] Q))
  let p := (LinearMap.snd S (S ⊗[R] P) (S ⊗[R] Q)).comp e.toLinearMap
  have hsp : p.comp s = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (e (e.symm (0, x))).2 = x
    rw [e.apply_symm_apply]
  let : Module.Projective S (S ⊗[R] Q) := Module.Projective.of_split s p hsp
  let : Module.Finite S (S ⊗[R] Q) := inferInstance
  let : Module.Free S (S ⊗[R] P) := Module.Free.of_equiv u.symm
  let : Module.Finite S (S ⊗[R] P) := Module.Finite.equiv u.symm
  let E := LocalizedModule.equivTensorProduct (Submonoid.powers r) Q
  refine ⟨Module.Finite.equiv E.symm, Module.Projective.of_equiv E.symm, fun x ↦ ?_⟩
  have : Nontrivial S := x.nontrivial
  have hp : Module.rankAtStalk (S ⊗[R] P) x = d := by
    rw [Module.rankAtStalk_eq_of_equiv u, Module.rankAtStalk_eq_finrank_of_free]
    simp
  have hV : Module.rankAtStalk (S ⊗[R] (R ⊗[k] V)) x = Module.finrank k V := by
    rw [Module.rankAtStalk_eq_of_equiv (cancelBaseChange k R S S V),
      Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_finrank_of_free]
    rfl
  have hR := congrFun (Module.rankAtStalk_eq_of_equiv e) x
  rw [Module.rankAtStalk_prod, Pi.add_apply, hp, hV] at hR
  rw [Module.rankAtStalk_eq_of_equiv E]
  change Module.finrank k V = d + Module.rankAtStalk (S ⊗[R] Q) x at hR
  change Module.rankAtStalk (S ⊗[R] Q) x = Module.finrank k V - d
  omega

private theorem plane_of_locally_free_split
    (h : ∀ x : PrimeSpectrum R, ∃ r ∉ x.asIdeal,
      Nonempty (Localization.Away r ⊗[R] P ≃ₗ[Localization.Away r]
        (ULift.{u} (Fin d) →₀ Localization.Away r)) ∧
      ∃ q : (Localization.Away r ⊗[R] (R ⊗[k] V)) →ₗ[Localization.Away r]
          (Localization.Away r ⊗[R] P), q.comp (P.subtype.baseChange _) = LinearMap.id) :
    ∃ L : Plane k V d R, L.toSubmodule = P := by
  obtain ⟨t, ht, hT⟩ := exists_principalCover _ h
  let Q := (R ⊗[k] V) ⧸ P
  have hLoc (i : (t : Set R)) :=
    localizedQuotient_rank_of_split R P i.val (hT i.val i.property)
  obtain ⟨hfin, hproj⟩ := finiteProjective_of_away (t : Set R) ht
    (fun i ↦ ⟨(hLoc i).1, (hLoc i).2.1⟩)
  let := hfin
  let := hproj
  refine ⟨⟨P, hfin, hproj, fun p ↦ ?_⟩, rfl⟩
  obtain ⟨i, q, hq⟩ := exists_away_above t ht p
  have he := Module.rankAtStalk_isBaseChange (M := Q)
    (LocalizedModule.isBaseChange (Submonoid.powers i.val) Q) q
  rw [hq] at he
  exact he.symm.trans ((hLoc i).2.2 q)

end RankOfLocalSummands

section AffineSubbundleComparison

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V)
  {d : ℕ} (R : TestAlgebra k)

omit [Fintype ι] [DecidableEq ι] in
set_option backward.isDefEq.respectTransparency false in
private theorem isTildePlane_uniquePlane (P Q : Plane k V d R)
    (L : Subbundles k V d ((testSpec k).obj (op R)))
    (hP : IsTildePlane (k := k) (V := V) b R P L)
    (hQ : IsTildePlane (k := k) (V := V) b R Q L) :
    P = Q := by
  obtain ⟨eP, hP⟩ := hP
  obtain ⟨eQ, hQ⟩ := hQ
  let F := tilde.functor (CommRingCat.of R)
  let ff := tilde.fullyFaithfulFunctor (R := CommRingCat.of R)
  let E := ff.preimageIso (eP ≪≫ eQ.symm)
  let g : ModuleCat.of R Q.toSubmodule ⟶ ModuleCat.of R (R ⊗[k] V) :=
    ModuleCat.ofHom Q.toSubmodule.subtype
  let f : ModuleCat.of R P.toSubmodule ⟶ ModuleCat.of R (R ⊗[k] V) :=
    ModuleCat.ofHom P.toSubmodule.subtype
  have h : E.hom ≫ g = f := by
    apply ff.map_injective
    change F.map (E.hom ≫ g) = F.map f
    rw [F.map_comp]
    have hE : F.map E.hom = eP.hom ≫ eQ.inv := ff.map_preimage _
    rw [hE]
    rw [← hQ, ← hP]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hcomp : g.hom.comp E.hom.hom = f.hom := congrArg ModuleCat.Hom.hom h
  have hRange : f.hom.range = g.hom.range := by
    rw [← hcomp, LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.mpr E.toLinearEquiv.surjective
  exact Module.Grassmannian.ext ((Submodule.range_subtype _).symm.trans
    (hRange.trans (Submodule.range_subtype _)))

set_option backward.isDefEq.respectTransparency false in
/-- The tilde construction classifies all rank-d subbundles over an affine test scheme. -/
def affineSubbundleEquiv (hd : d ≤ Module.finrank k V) :
    Plane k V d R ≃ Subbundles k V d ((testSpec k).obj (op R)) := by
  let : Module.Finite k V := Module.Finite.of_basis b
  refine Equiv.ofBijective (affinePlaneSubbundle b hd R) ⟨?_, ?_⟩
  · intro P Q h
    exact isTildePlane_uniquePlane b R P Q _ (affinePlaneSubbundle_isTilde b hd R P)
      (h.symm ▸ affinePlaneSubbundle_isTilde b hd R Q)
  · intro L
    obtain ⟨P, ep, hep⟩ := subbundle_is_tildeSubmodule b R L
    obtain ⟨L', hL'⟩ := plane_of_locally_free_split R P (subbundle_away_free_split b R L P ep hep)
    refine ⟨L', isTildePlane_uniqueSubbundle b R L' _ _ (affinePlaneSubbundle_isTilde b hd R L') ?_⟩
    have H : ∃ (Q : Submodule R (R ⊗[k] V)), Q = L'.toSubmodule ∧
        ∃ e : tilde (ModuleCat.of R Q) ≅ (L.val : ((testSpec k).obj (op R)).left.Modules),
        e.hom ≫ L.val.arrow ≫ (affineAmbientOfBasis (k := k) (V := V) b R).hom =
          (tilde.functor (CommRingCat.of R)).map (ModuleCat.ofHom Q.subtype) :=
      ⟨P, hL'.symm, ep, hep⟩
    obtain ⟨_, rfl, h⟩ := H
    exact h

theorem affineSubbundleEquiv_isTilde (hd : d ≤ Module.finrank k V) (L : Plane k V d R) :
    IsTildePlane (k := k) (V := V) b R L (affineSubbundleEquiv b R hd L) :=
  affinePlaneSubbundle_isTilde b hd R L

end AffineSubbundleComparison

theorem affineSubbundleComparison : AffineSubbundleComparison.{u} := by
  intro k V ι _ _ _ _ _ b d hd R
  exact ⟨affineSubbundleEquiv b R hd, affineSubbundleEquiv_isTilde b R hd⟩

end IntrinsicAffineSubbundles

section PullbackSubbundle

set_option backward.isDefEq.respectTransparency false in
private theorem mono_of_locallySplit {X : Scheme.{u}} {P M : X.Modules} (a : P ⟶ M)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsSplitMono ((Scheme.Modules.restrictFunctor U.ι).map a)) :
    Mono a := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have hm : Mono (F.map a) := by
    apply (TopCat.Presheaf.mono_iff_stalk_mono (F.map a)).mpr
    intro x
    obtain ⟨U, hU, hs⟩ := h x
    let y : U.toScheme := ⟨x, hU⟩
    let B := Scheme.Modules.restrictStalkNatIso U.ι y
    let G := Scheme.Modules.toPresheaf U.toScheme ⋙ TopCat.Presheaf.stalkFunctor _ y
    have he : IsSplitMono (G.map ((Scheme.Modules.restrictFunctor U.ι).map a)) :=
      isSplitMono_map G ((Scheme.Modules.restrictFunctor U.ι).map a)
    have hb := isSplitMono_of_commuting_isos (B.app P) (B.app M)
      (B.hom.naturality a) he
    change Mono ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor _ (U.ι y)).map a)
    exact inferInstanceAs (Mono ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor _ (U.ι y)).map a))
  constructor
  intro P' g h' hh
  apply F.map_injective
  have H := congrArg F.map hh
  rw [F.map_comp, F.map_comp] at H
  exact (cancel_mono (F.map a)).mp H

private def pullbackRestrictionIso {T S : Scheme.{u}} (f : T ⟶ S) (U : S.Opens) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) :=
  Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι) ≪≫
    Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f ≪≫
    pullbackCompRestriction _ _ U.ι (morphismRestrict_ι f U)

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
  {d : ℕ} {T S : SchemeOver k} (a : T ⟶ S) (L : Subbundles k V d S)

private def pullbackSubbundleArrow :
    (Scheme.Modules.pullback a.left).obj (L.val : S.left.Modules) ⟶ ambient k V T :=
  (Scheme.Modules.pullback a.left).map L.val.arrow ≫ (ambientPullback k V a).hom

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackSubbundleArrow_local (x : T.left) :
    ∃ U : T.left.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj
          ((Scheme.Modules.pullback a.left).obj (L.val : S.left.Modules)) ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin d))) ∧
      IsSplitMono ((Scheme.Modules.restrictFunctor U.ι).map (pullbackSubbundleArrow a L)) := by
  obtain ⟨U, hU, ⟨e⟩, hsplit⟩ := L.property (a.left x)
  let W := a.left ⁻¹ᵁ U
  let f := a.left ∣_ U
  let F := Scheme.Modules.restrictFunctor W.ι
  let B := pullbackRestrictionIso a.left U
  let M := (L.val : S.left.Modules)
  let eM := B.app M
  let eA := B.app (ambient k V S)
  have hs := isSplitMono_map (Scheme.Modules.pullback f)
    ((Scheme.Modules.restrictFunctor U.ι).map L.val.arrow)
  have hsb : IsSplitMono (F.map ((Scheme.Modules.pullback a.left).map L.val.arrow)) :=
    isSplitMono_of_commuting_isos eM.symm eA.symm (B.inv.naturality L.val.arrow) hs
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  refine ⟨W, hU, ⟨eM ≪≫ (Scheme.Modules.pullback f).mapIso e ≪≫
    SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (ULift.{u} (Fin d))⟩, ?_⟩
  let E := F.mapIso (ambientPullback k V a)
  let l := F.map ((Scheme.Modules.pullback a.left).map L.val.arrow)
  have hl : IsSplitMono l := hsb
  refine IsSplitMono.mk' ⟨E.inv ≫ retraction l, ?_⟩
  change F.map (pullbackSubbundleArrow a L) ≫ E.inv ≫ retraction l = 𝟙 _
  rw [pullbackSubbundleArrow, F.map_comp]
  change (l ≫ E.hom) ≫ E.inv ≫ retraction l = 𝟙 _
  simp

private theorem pullbackSubbundleArrow_mono : Mono (pullbackSubbundleArrow a L) :=
  mono_of_locallySplit _ fun x ↦ by
    obtain ⟨U, hx, _, hU⟩ := pullbackSubbundleArrow_local a L x
    exact ⟨U, hx, hU⟩

set_option backward.isDefEq.respectTransparency false in
/-- Pullback of a locally split subbundle along an arbitrary test morphism. -/
def pullbackSubbundle : Subbundles k V d T := by
  let i := pullbackSubbundleArrow a L
  let : Mono i := pullbackSubbundleArrow_mono a L
  let P := Subobject.mk i
  let e := Subobject.underlyingIso i
  refine ⟨P, fun x ↦ ?_⟩
  obtain ⟨U, hU, ⟨eU⟩, hs⟩ := pullbackSubbundleArrow_local a L x
  let F := Scheme.Modules.restrictFunctor U.ι
  refine ⟨U, hU, ⟨F.mapIso e ≪≫ eU⟩, ?_⟩
  have hf : P.arrow = e.hom ≫ i := (Subobject.underlyingIso_hom_comp_eq_mk i).symm
  have hl : IsSplitMono (F.map i) := hs
  refine IsSplitMono.mk' ⟨retraction (F.map i) ≫ (F.mapIso e).inv, ?_⟩
  rw [hf, F.map_comp]
  change ((F.mapIso e).hom ≫ F.map i) ≫ retraction (F.map i) ≫ (F.mapIso e).inv = 𝟙 _
  simp

set_option backward.isDefEq.respectTransparency false in
theorem pullbackSubbundle_spec : IsPullbackSubbundle k V a L (pullbackSubbundle a L) := by
  let i := pullbackSubbundleArrow a L
  let : Mono i := pullbackSubbundleArrow_mono a L
  exact ⟨(Subobject.underlyingIso i).symm, Subobject.underlyingIso_arrow i⟩

theorem pullbackSubbundle_unique (P Q : Subbundles k V d T)
    (hP : IsPullbackSubbundle k V a L P) (hQ : IsPullbackSubbundle k V a L Q) :
    P = Q := by
  obtain ⟨eP, hP⟩ := hP
  obtain ⟨eQ, hQ⟩ := hQ
  apply Subtype.ext
  apply Subobject.eq_of_comm (eP.symm ≪≫ eQ)
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hQ, ← hP, Iso.inv_hom_id_assoc]

end PullbackSubbundle

theorem subbundlePullback : SubbundlePullback.{u} := by
  intro k V _ _ _ d T S f L
  exact ⟨pullbackSubbundle f L, pullbackSubbundle_spec f L,
    fun M h ↦ pullbackSubbundle_unique f L M (pullbackSubbundle f L) h
      (pullbackSubbundle_spec f L)⟩

section OpenSubmoduleGluing

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  (M : SheafOfModules.{u} R) {U : Opens X}

set_option backward.isDefEq.respectTransparency false in
private theorem moduleSections_map_id {W : (Opens X)ᵒᵖ} (s : M.val.obj W) :
    M.val.map (𝟙 W) s = s := by
  change M.val.presheaf.map (𝟙 W) s = s
  simp only [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

set_option backward.isDefEq.respectTransparency false in
private def extendPresheafSubmodule (N : (SheafOfModules.over M U).Submodule) :
    M.val.Submodule where
  obj W :=
    { carrier := { s | ∀ (V : Opens X) (f : V ⟶ W.unop) (g : V ⟶ U),
        M.val.map f.op s ∈ N.toSubmodule.obj (op (Over.mk g)) }
      zero_mem' := fun V f g ↦ by
        rw [map_zero]
        exact Submodule.zero_mem _
      add_mem' := fun hx hy V f g ↦ by
        rw [map_add]
        exact Submodule.add_mem _ (hx V f g) (hy V f g)
      smul_mem' := fun c s hs V f g ↦ by
        rw [PresheafOfModules.map_smul]
        exact Submodule.smul_mem _ _ (hs V f g) }
  map {A B} f := by
    intro s hs
    change ∀ (V : Opens X) (i : V ⟶ B.unop) (g : V ⟶ U),
      M.val.map i.op (M.val.map f s) ∈ N.toSubmodule.obj (op (Over.mk g))
    intro V i g
    have H := hs V (i ≫ f.unop) g
    rwa [op_comp, Quiver.Hom.op_unop, PresheafOfModules.map_comp_apply] at H

set_option backward.isDefEq.respectTransparency false in
private def extendOpenSubmodule (N : (SheafOfModules.over M U).Submodule) :
    M.Submodule where
  toSubmodule := extendPresheafSubmodule M N
  isSheaf := by
    intro W s hs
    change ∀ (V : Opens X) (f : V ⟶ W.unop) (g : V ⟶ U),
      M.val.map f.op s ∈ N.toSubmodule.obj (op (Over.mk g))
    intro V f g
    let J := Opens.grothendieckTopology X
    let V' := Over.mk g
    let t : (M.over U).val.obj (op V') := M.val.map f.op s
    change t ∈ N.obj (op V')
    apply N.isSheaf t
    rw [GrothendieckTopology.mem_over_iff]
    refine J.superset_covering ?_ (J.pullback_stable f hs)
    intro B b hb
    rw [Sieve.overEquiv_iff]
    have h : M.val.map (b ≫ f).op s ∈ (extendPresheafSubmodule M N).obj (op B) := hb
    have hh := h B (𝟙 B) (b ≫ g)
    change M.val.map b.op (M.val.map f.op s) ∈ N.obj (op (Over.mk (b ≫ g)))
    have heq : M.val.map (b ≫ f).op s = M.val.map b.op (M.val.map f.op s) :=
      M.val.map_comp_apply f.op b.op s
    have hx : M.val.map (b ≫ f).op s ∈ N.obj (op (Over.mk (b ≫ g))) := by
      simpa only [op_id, moduleSections_map_id] using hh
    exact heq ▸ hx

variable {I : Type u} (U₀ : I → Opens X)
  (N : ∀ i, (SheafOfModules.over M (U₀ i)).Submodule)

/-- Compatible subsheaves of a fixed module glue by imposing their section
membership conditions on the opens where each subsheaf is defined. -/
def glueOpenSubmodules : M.Submodule :=
  ⨅ i, extendOpenSubmodule M (N i)

set_option backward.isDefEq.respectTransparency false in
theorem glueOpenSubmodules_restrict
    (h : ∀ i j (W : Opens X) (a : W ⟶ U₀ i) (b : W ⟶ U₀ j) (s : M.val.obj (op W)),
      s ∈ (N i).obj (op (Over.mk a)) ↔ s ∈ (N j).obj (op (Over.mk b)))
    (i : I) {W : Opens X} (a : W ⟶ U₀ i) (s : M.val.obj (op W)) :
    s ∈ (glueOpenSubmodules M U₀ N).obj (op W) ↔ s ∈ (N i).obj (op (Over.mk a)) := by
  change s ∈ (⨅ j, extendOpenSubmodule M (N j)).toSubmodule.obj (op W) ↔ _
  rw [SheafOfModules.Submodule.toSubmodule_iInf]
  have heq :
      (⨅ j, (extendOpenSubmodule M (N j)).toSubmodule).obj (op W) =
        ⨅ j, (extendOpenSubmodule M (N j)).obj (op W) := by
    change (sInf (Set.range (fun j ↦ (extendOpenSubmodule M (N j)).toSubmodule))).obj (op W) = _
    rw [PresheafOfModules.Submodule.sInf_obj]
    apply le_antisymm
    · exact le_iInf fun j ↦ iInf₂_le _ ⟨j, rfl⟩
    · refine le_iInf₂ fun Q hQ ↦ ?_
      obtain ⟨j, rfl⟩ := hQ
      exact iInf_le _ j
  rw [heq, Submodule.mem_iInf]
  constructor
  · intro hs
    have hmem := hs i
    change ∀ (V : Opens X) (f : V ⟶ W) (g : V ⟶ U₀ i),
      M.val.map f.op s ∈ (N i).obj (op (Over.mk g)) at hmem
    simpa only [op_id, moduleSections_map_id] using hmem W (𝟙 W) a
  · intro hs j
    change ∀ (V : Opens X) (f : V ⟶ W) (g : V ⟶ U₀ j),
      M.val.map f.op s ∈ (N j).obj (op (Over.mk g))
    intro V f g
    apply (h i j V (f ≫ a) g _).mp
    let k : Over.mk (f ≫ a) ⟶ Over.mk a := Over.homMk f
    exact (N i).toSubmodule.map_mem k.op hs

private theorem submodule_le_of_openCover (hc : IsOpenCover U₀) (P Q : M.Submodule)
    (h : ∀ (i : I) (W : Opens X), W ≤ U₀ i → P.obj (op W) ≤ Q.obj (op W)) : P ≤ Q := by
  intro W s hs
  apply Q.isSheaf s
  intro x hx
  obtain ⟨i, hi⟩ := hc.exists_mem x
  let V := W.unop ⊓ U₀ i
  let f : V ⟶ W.unop := homOfLE inf_le_left
  refine ⟨V, f, ?_, ⟨hx, hi⟩⟩
  exact h i V inf_le_right (P.toSubmodule.map_mem f.op hs)

theorem glueOpenSubmodules_unique (hc : IsOpenCover U₀)
    (h : ∀ i j (W : Opens X) (a : W ⟶ U₀ i) (b : W ⟶ U₀ j) (s : M.val.obj (op W)),
      s ∈ (N i).obj (op (Over.mk a)) ↔ s ∈ (N j).obj (op (Over.mk b)))
    (P : M.Submodule)
    (hP : ∀ i (W : Opens X) (a : W ⟶ U₀ i) (s : M.val.obj (op W)),
      s ∈ P.obj (op W) ↔ s ∈ (N i).obj (op (Over.mk a))) :
    glueOpenSubmodules M U₀ N = P := by
  apply le_antisymm
  · apply submodule_le_of_openCover M U₀ hc
    intro i W hi s hs
    exact (hP i W (homOfLE hi) s).mpr
      ((glueOpenSubmodules_restrict M U₀ N h i (homOfLE hi) s).mp hs)
  · apply submodule_le_of_openCover M U₀ hc
    intro i W hi s hs
    exact (glueOpenSubmodules_restrict M U₀ N h i (homOfLE hi) s).mpr
      ((hP i W (homOfLE hi) s).mp hs)

set_option backward.isDefEq.respectTransparency false in
private def glueOpenSubmodulesOverIsoAux
    (h : ∀ i j (W : Opens X) (a : W ⟶ U₀ i) (b : W ⟶ U₀ j) (s : M.val.obj (op W)),
      s ∈ (N i).obj (op (Over.mk a)) ↔ s ∈ (N j).obj (op (Over.mk b)))
    (i : I) :
    ((glueOpenSubmodules M U₀ N).toSheafOfModules.over (U₀ i)).val ≅
      (N i).toSheafOfModules.val := by
  have he (W : Over (U₀ i)) :
      (glueOpenSubmodules M U₀ N).obj (op W.left) = (N i).obj (op W) := by
    obtain ⟨W, a, rfl⟩ := W.mk_surjective
    exact SetLike.ext (glueOpenSubmodules_restrict M U₀ N h i a)
  refine PresheafOfModules.isoMk
    (fun W ↦ (LinearEquiv.ofEq _ _ (he W.unop)).toModuleIso) ?_
  intro A B f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- On a cover member the glued sheaf is canonically isomorphic to the local sheaf. -/
def glueOpenSubmodulesOverIso
    (h : ∀ i j (W : Opens X) (a : W ⟶ U₀ i) (b : W ⟶ U₀ j) (s : M.val.obj (op W)),
      s ∈ (N i).obj (op (Over.mk a)) ↔ s ∈ (N j).obj (op (Over.mk b)))
    (i : I) :
    (glueOpenSubmodules M U₀ N).toSheafOfModules.over (U₀ i) ≅ (N i).toSheafOfModules :=
  (SheafOfModules.fullyFaithfulForget (R.over (U₀ i))).preimageIso
    (glueOpenSubmodulesOverIsoAux M U₀ N h i)

@[reassoc]
theorem glueOpenSubmodulesOverIso_ι
    (h : ∀ i j (W : Opens X) (a : W ⟶ U₀ i) (b : W ⟶ U₀ j) (s : M.val.obj (op W)),
      s ∈ (N i).obj (op (Over.mk a)) ↔ s ∈ (N j).obj (op (Over.mk b)))
    (i : I) :
    (glueOpenSubmodulesOverIso M U₀ N h i).hom ≫ (N i).ι =
      (glueOpenSubmodules M U₀ N).ι.over (U₀ i) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end OpenSubmoduleGluing

section SheafRange

variable {C : Type u} [Category C] {J : GrothendieckTopology C} {R' : Sheaf J RingCat.{u}}
  {P Q : SheafOfModules.{u} R'} (a : P ⟶ Q) [Mono a]

set_option backward.isDefEq.respectTransparency false in
private def presheafModuleRange : Q.val.Submodule where
  obj W := (a.val.app W).hom.range
  map f := by
    rintro _ ⟨x, rfl⟩
    refine ⟨P.val.map f x, ?_⟩
    exact congrArg (fun g ↦ g x) (a.val.naturality f)

set_option backward.isDefEq.respectTransparency false in
private def presheafModuleRangeIso :
    P.val ≅ (presheafModuleRange a).toPresheafOfModules := by
  letI : PreservesLimitsOfShape WalkingCospan (SheafOfModules.forget.{u} R') :=
    SheafOfModules.forgetPreservesLimitsOfShape.{u} WalkingCospan R'
  letI : (SheafOfModules.forget.{u} R').PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape (SheafOfModules.forget.{u} R')
  let ha : Mono ((SheafOfModules.forget.{u} R').map a) := (SheafOfModules.forget.{u} R').map_mono a
  let : Mono a.val := ha
  refine PresheafOfModules.isoMk (fun W ↦
    (LinearEquiv.ofInjective (a.val.app W).hom
      (PresheafOfModules.injective_of_mono a.val W)).toModuleIso) ?_
  intro W V f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun g ↦ g x) (a.val.naturality f)

/-- A monomorphism of module sheaves identifies its source with its sectionwise range. -/
def moduleSheafRange : Q.Submodule where
  toSubmodule := presheafModuleRange a
  isSheaf := by
    let Q' := (presheafModuleRange a).toSubfunctor
    have hQ : Presieve.IsSheaf J (Q.val.presheaf ⋙ CategoryTheory.forget Ab) := by
      rw [← isSheaf_iff_isSheaf_of_type]
      exact GrothendieckTopology.HasSheafCompose.isSheaf _ Q.isSheaf
    have hP : Presieve.IsSheaf J (P.val.presheaf ⋙ CategoryTheory.forget Ab) := by
      rw [← isSheaf_iff_isSheaf_of_type]
      exact GrothendieckTopology.HasSheafCompose.isSheaf _ P.isSheaf
    let F := PresheafOfModules.toPresheaf R'.obj ⋙
      (Functor.whiskeringRight Cᵒᵖ Ab (Type u)).obj (CategoryTheory.forget Ab)
    let e := F.mapIso (presheafModuleRangeIso a)
    intro W s hs
    exact (Q'.isSheaf_iff hQ).mp (Presieve.isSheaf_iso J e hP) W s hs

def moduleSheafRangeIso : P ≅ (moduleSheafRange a).toSheafOfModules :=
  (SheafOfModules.fullyFaithfulForget R').preimageIso (presheafModuleRangeIso a)

@[reassoc]
theorem moduleSheafRangeIso_ι :
    (moduleSheafRangeIso a).hom ≫ (moduleSheafRange a).ι = a := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end SheafRange


section AmbientTrivialization

open Scheme.Modules

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackAdjunction_comp {P : Z.Modules} {Q : X.Modules}
    (a : ((Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f).obj P) ⟶ Q) :
    (pullbackPushforwardAdjunction (f ≫ g)).homEquiv P Q
      ((pullbackComp f g).inv.app P ≫ a) =
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)).homEquiv P Q a ≫
        (pushforwardComp f g).hom.app Q := by
  let d := (pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)
  let e := pullbackPushforwardAdjunction (f ≫ g)
  let p := (pullbackComp f g).inv
  let q := (pushforwardComp f g).hom
  have h := unit_conjugateEquiv d e p P
  rw [conjugateEquiv_pullbackComp_inv f g] at h
  change e.homEquiv P Q (p.app P ≫ a) = d.homEquiv P Q a ≫ q.app Q
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← h, Category.assoc, ← q.naturality]
  exact (Category.assoc _ _ _).symm

private def schemeUnit (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

set_option backward.isDefEq.respectTransparency false in
private def pullbackUnitMap (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (schemeUnit Y) ⟶ schemeUnit X := by
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (pushforward f).IsRightAdjoint
  exact SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom

private def unitPushforwardMap (f : X ⟶ Y) :
    schemeUnit Y ⟶ (pushforward f).obj (schemeUnit X) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

set_option backward.isDefEq.respectTransparency false in
private theorem unitPushforwardMap_comp :
    unitPushforwardMap (f ≫ g) =
      (unitPushforwardMap g ≫ (pushforward g).map (unitPushforwardMap f)) ≫
        (pushforwardComp f g).hom.app (schemeUnit X) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackUnitMap_transpose (f : X ⟶ Y) :
    (pullbackPushforwardAdjunction f).homEquiv (schemeUnit Y) (schemeUnit X) (pullbackUnitMap f) =
      unitPushforwardMap f :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackUnitMap_comp :
    pullbackUnitMap (f ≫ g) =
      (pullbackComp f g).inv.app (schemeUnit Z) ≫
        (Scheme.Modules.pullback f).map (pullbackUnitMap g) ≫ pullbackUnitMap f := by
  apply ((pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [pullbackUnitMap_transpose, pullbackAdjunction_comp]
  rw [Adjunction.comp_homEquiv]
  change _ = (pullbackPushforwardAdjunction g).homEquiv _ _
    ((pullbackPushforwardAdjunction f).homEquiv _ _
      ((Scheme.Modules.pullback f).map (pullbackUnitMap g) ≫ pullbackUnitMap f)) ≫ _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    pullbackUnitMap_transpose, pullbackUnitMap_transpose]
  exact unitPushforwardMap_comp f g

set_option backward.isDefEq.respectTransparency false in
private def schemeFreePullback (f : X ⟶ Y) (I : Type u) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.free (R := Y.ringCatSheaf) I) ≅
      SheafOfModules.free (R := X.ringCatSheaf) I := by
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (pushforward f).IsRightAdjoint
  exact SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I

set_option backward.isDefEq.respectTransparency false in
private theorem schemeFreePullback_generator (f : X ⟶ Y) {I : Type u} (i : I) :
    (Scheme.Modules.pullback f).map (SheafOfModules.ιFree i) ≫ (schemeFreePullback f I).hom =
      pullbackUnitMap f ≫ SheafOfModules.ιFree i := by
  exact SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom f.toRingCatSheafHom i

set_option backward.isDefEq.respectTransparency false in
private theorem schemeFreePullback_comp (I : Type u) :
    (schemeFreePullback (f ≫ g) I).hom =
      (pullbackComp f g).inv.app (SheafOfModules.free I) ≫
        (Scheme.Modules.pullback f).map (schemeFreePullback g I).hom ≫
        (schemeFreePullback f I).hom := by
  let F := Scheme.Modules.pullback f
  let G := Scheme.Modules.pullback g
  let H := Scheme.Modules.pullback (f ≫ g)
  let k := (pullbackComp f g).inv
  apply Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit H _ _ (SheafOfModules.isColimitFreeCofan (R := Z.ringCatSheaf) I))
  intro i
  let uZ : schemeUnit Z ⟶ SheafOfModules.free I := SheafOfModules.ιFree i
  let uY : schemeUnit Y ⟶ SheafOfModules.free I := SheafOfModules.ιFree i
  let uX : schemeUnit X ⟶ SheafOfModules.free I := SheafOfModules.ιFree i
  change H.map uZ ≫ (schemeFreePullback (f ≫ g) I).hom =
    H.map uZ ≫ k.app _ ≫ F.map (schemeFreePullback g I).hom ≫ (schemeFreePullback f I).hom
  rw [schemeFreePullback_generator (f ≫ g) i, pullbackUnitMap_comp f g]
  change (k.app (schemeUnit Z) ≫ F.map (pullbackUnitMap g) ≫ pullbackUnitMap f) ≫ uX =
    H.map uZ ≫ k.app _ ≫ F.map (schemeFreePullback g I).hom ≫ (schemeFreePullback f I).hom
  rw [Category.assoc, Category.assoc, ← schemeFreePullback_generator f i,
    ← Category.assoc (F.map (pullbackUnitMap g)),
    ← F.map_comp, ← schemeFreePullback_generator g i, F.map_comp,
    Category.assoc]
  have hn := k.naturality_assoc uZ
    (F.map (schemeFreePullback g I).hom ≫ (schemeFreePullback f I).hom)
  exact hn.symm

section AmbientFree

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackTrivialization_comp {I : Type u} {M : Z.Modules}
    (e : M ≅ SheafOfModules.free (R := Z.ringCatSheaf) I) :
    (Scheme.Modules.pullback (f ≫ g)).map e.hom ≫ (schemeFreePullback (f ≫ g) I).hom =
      (pullbackComp f g).inv.app M ≫
        (Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullback g).map e.hom ≫ (schemeFreePullback g I).hom) ≫
        (schemeFreePullback f I).hom := by
  rw [schemeFreePullback_comp, CategoryTheory.Functor.map_comp]
  have hn := (pullbackComp f g).inv.naturality_assoc e.hom
    ((Scheme.Modules.pullback f).map (schemeFreePullback g I).hom ≫ (schemeFreePullback f I).hom)
  exact hn

private def pullbackTrivialization {X Y : Scheme.{u}} (f : X ⟶ Y) {I : Type u}
    {M : Y.Modules} (e : M ≅ SheafOfModules.free (R := Y.ringCatSheaf) I) :
    (Scheme.Modules.pullback f).obj M ≅ SheafOfModules.free (R := X.ringCatSheaf) I :=
  (Scheme.Modules.pullback f).mapIso e ≪≫ schemeFreePullback f I

private theorem pullbackTrivialization_congr {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) {I : Type u} {M : Y.Modules}
    (e : M ≅ SheafOfModules.free (R := Y.ringCatSheaf) I) :
    (pullbackCongr h).hom.app M ≫ (pullbackTrivialization g e).hom =
      (pullbackTrivialization f e).hom := by
  subst g
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
  (b : Module.Basis ι k V)

private def tildeBasisFree {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M]
    [Module A M] (B : Module.Basis ι A M) :
    tilde (R := CommRingCat.of A) (ModuleCat.of A M) ≅ SheafOfModules.free ι :=
  (tilde.functor (CommRingCat.of A)).mapIso B.repr.toModuleIso ≪≫ tildeFinsupp ι

private def ambientFreeIso (S : SchemeOver k) :
    ambient k V S ≅ SheafOfModules.free ι :=
  pullbackTrivialization S.hom (tildeBasisFree b)

set_option backward.isDefEq.respectTransparency false in
theorem ambientFreeIso_naturality {S T : SchemeOver k} (a : T ⟶ S) :
    (Scheme.Modules.pullback a.left).map (ambientFreeIso b S).hom ≫
      (schemeFreePullback a.left ι).hom =
      (ambientPullback k V a).hom ≫ (ambientFreeIso b T).hom := by
  let M := tilde (R := CommRingCat.of k) (ModuleCat.of k V)
  let e := tildeBasisFree b
  let c := pullbackComp a.left S.hom
  change _ = (c.hom.app M ≫ (pullbackCongr (Over.w a)).hom.app M) ≫
    (pullbackTrivialization T.hom e).hom
  rw [Category.assoc, pullbackTrivialization_congr (Over.w a)]
  have h := pullbackTrivialization_comp a.left S.hom e
  change (Scheme.Modules.pullback (a.left ≫ S.hom)).map e.hom ≫
      (schemeFreePullback (a.left ≫ S.hom) ι).hom = c.inv.app M ≫ _ at h
  change _ = c.hom.app M ≫ ((Scheme.Modules.pullback (a.left ≫ S.hom)).map e.hom ≫
      (schemeFreePullback (a.left ≫ S.hom) ι).hom)
  rw [h]
  change _ = (c.app M).hom ≫ (c.app M).inv ≫ _
  rw [Iso.hom_inv_id_assoc]
  rfl

end AmbientFree

end AmbientTrivialization

section SchemeSubbundles

open TopologicalSpace Scheme.Modules TensorProduct
open scoped AlgebraicGeometry

section AffineUnitComparison

set_option backward.isDefEq.respectTransparency false in
private theorem affinePullbackTilde_unit {A B : CommRingCat.{u}} (a : A ⟶ B) :
    letI : Algebra A B := a.hom.toAlgebra
    (affinePullbackTilde a).hom.app (ModuleCat.of A A) ≫
      (tilde.functor B).map (AlgebraTensorModule.rid A B B).toModuleIso.hom =
        pullbackUnitMap (Spec.map a) := by
  letI : Algebra A B := a.hom.toAlgebra
  let P := ModuleCat.of A A
  let Q := ModuleCat.of B B
  let f := Spec.map a
  let m : (ModuleCat.extendScalars a.hom).obj P ⟶ Q :=
    (AlgebraTensorModule.rid A B B).toModuleIso.hom
  let adj := pullbackPushforwardAdjunction f
  let tA := tilde.adjunction (R := A)
  let tB := tilde.adjunction (R := B)
  let e := ModuleCat.extendRestrictScalarsAdj a.hom
  let da := (tA.comp adj).ofNatIsoRight (sectionsPushforwardIso a)
  let ba := e.comp tB
  change (da.leftAdjointUniq ba).hom.app P ≫ (tilde.functor B).map m = pullbackUnitMap f
  apply (da.homEquiv P (schemeUnit (Spec B))).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    ← Adjunction.homEquiv_unit]
  change ba.homEquiv P (schemeUnit (Spec B)) ((tilde.functor B).map m) =
    ((tA.comp adj).ofNatIsoRight (sectionsPushforwardIso a)).homEquiv P
      (schemeUnit (Spec B)) (pullbackUnitMap f)
  simp only [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change e.homEquiv P _
      (tB.homEquiv _ _ ((tilde.functor B).map m)) =
    tA.homEquiv P _ (adj.homEquiv _ _ (pullbackUnitMap f)) ≫ _
  have ht : adj.homEquiv ((tilde.functor A).obj P) (schemeUnit (Spec B))
      (pullbackUnitMap f) = unitPushforwardMap f := pullbackUnitMap_transpose f
  rw [ht]
  have hm : tB.homEquiv _ ((tilde.functor B).obj Q) ((tilde.functor B).map m) =
    m ≫ tB.unit.app Q := by
    rw [Adjunction.homEquiv_unit]
    exact (tB.unit.naturality m).symm
  rw [hm, Adjunction.homEquiv_unit]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change e.homEquiv _ _ (m ≫ tB.unit.app Q) (1 : A) =
    (unitPushforwardMap f).val.app (op ⊤) (tA.unit.app P (1 : A))
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
  change (tB.unit.app Q) ((1 : A) • (1 : B)) =
    f.appTop (tA.unit.app P (1 : A))
  rw [one_smul]
  change (Scheme.ΓSpecIso B).inv (1 : B) = f.appTop ((Scheme.ΓSpecIso A).inv (1 : A))
  simp only [map_one]

end AffineUnitComparison

section BasisGenerators

private def basisGenerator {A M ι : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (B : Module.Basis ι A M) (i : ι) :
    ModuleCat.of A A ⟶ ModuleCat.of A M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton A M (B i))

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem tildeBasisFree_generator {A : CommRingCat.{u}} {M ι : Type u}
    [AddCommGroup M] [Module A M] (B : Module.Basis ι A M) (i : ι) :
    (tilde.functor A).map (basisGenerator B i) ≫ (tildeBasisFree B).hom =
      SheafOfModules.ιFree i := by
  let c := ModuleCat.finsuppCocone A A ι
  let j := c.ι.app (Discrete.mk i)
  have hg : basisGenerator B i ≫ B.repr.toModuleIso.hom = j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change B.repr ((1 : A) • B i) = Finsupp.single i 1
    rw [one_smul, B.repr_self]
  change (tilde.functor A).map (basisGenerator B i) ≫
    (tilde.functor A).map B.repr.toModuleIso.hom ≫ (tildeFinsupp ι).hom = _
  rw [← Functor.map_comp_assoc, hg]
  let H := isColimitOfPreserves (tilde.functor A) (ModuleCat.finsuppCoconeIsColimit A A ι)
  let e : (Discrete.functor fun _ : ι ↦ ModuleCat.of A A) ⋙ tilde.functor A ≅
      Discrete.functor fun _ ↦ SheafOfModules.unit.{u} (Spec A).ringCatSheaf :=
    Discrete.natIso (fun _ ↦ tildeSelf)
  let HF := (IsColimit.precomposeHomEquiv e.symm _).symm H
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom HF
    (coproductIsCoproduct _) (Discrete.mk i)
  change (𝟙 _ ≫ (tilde.functor A).map j) ≫ (tildeFinsupp ι).hom = SheafOfModules.ιFree i at h
  simpa only [Category.id_comp] using h

end BasisGenerators

section AffineNaturality

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
  (b : Module.Basis ι k V) {R S : TestAlgebra k} (a : R ⟶ S)

private abbrev affineRingMap : CommRingCat.of R ⟶ CommRingCat.of S :=
  CommRingCat.ofHom a.hom.toRingHom

private theorem affineTower : letI : Algebra R S := a.hom.toAlgebra; IsScalarTower k R S := by
  letI : Algebra R S := a.hom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq' a.hom.comp_algebraMap.symm

private def ambientTensorIso :
    (ModuleCat.extendScalars (affineRingMap a).hom).obj (ModuleCat.of R (R ⊗[k] V)) ≅
      ModuleCat.of S (S ⊗[k] V) := by
  letI : Algebra R S := a.hom.toAlgebra
  letI : IsScalarTower k R S := affineTower a
  exact (AlgebraTensorModule.cancelBaseChange k R S S V).toModuleIso

set_option backward.isDefEq.respectTransparency false in
private theorem ambientTensorIso_generator (i : ι) :
    letI : Algebra R S := a.hom.toAlgebra
    (ModuleCat.extendScalars (affineRingMap a).hom).map (basisGenerator (b.baseChange R) i) ≫
      (ambientTensorIso (V := V) a).hom =
        (AlgebraTensorModule.rid R S S).toModuleIso.hom ≫
          basisGenerator (b.baseChange S) i := by
  letI : Algebra R S := a.hom.toAlgebra
  letI : IsScalarTower k R S := affineTower a
  apply ModuleCat.ExtendScalars.hom_ext
  intro r
  rw [ModuleCat.comp_apply, ModuleCat.ExtendScalars.map_tmul, ModuleCat.comp_apply]
  change AlgebraTensorModule.cancelBaseChange k R S S V
      ((1 : S) ⊗ₜ[R] (r • (b.baseChange R i))) =
    (r • (1 : S)) • (b.baseChange S i)
  rw [Module.Basis.baseChange_apply, Module.Basis.baseChange_apply,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one, AlgebraTensorModule.cancelBaseChange_tmul]
  rw [TensorProduct.smul_tmul']
  change ((r • (1 : S)) ⊗ₜ[k] b i) = ((r • (1 : S)) * 1) ⊗ₜ[k] b i
  rw [mul_one]

set_option maxHeartbeats 700000 in
set_option backward.isDefEq.respectTransparency false in
private theorem tildeBasisFree_pullback :
    (Scheme.Modules.pullback (Spec.map (affineRingMap a))).map
        (tildeBasisFree (b.baseChange R)).hom ≫ (schemeFreePullback (Spec.map (affineRingMap a)) ι).hom =
      (affinePullbackTilde (affineRingMap a)).hom.app (ModuleCat.of R (R ⊗[k] V)) ≫
        (tilde.functor (CommRingCat.of S)).map (ambientTensorIso (V := V) a).hom ≫
        (tildeBasisFree (b.baseChange S)).hom := by
  let f := Spec.map (affineRingMap a)
  let F := Scheme.Modules.pullback f
  let TR := tilde.functor (CommRingCat.of R)
  let TS := tilde.functor (CommRingCat.of S)
  let JR := tildeBasisFree (b.baseChange R)
  let JS := tildeBasisFree (b.baseChange S)
  let e := affinePullbackTilde (affineRingMap a)
  let q := (ambientTensorIso (V := V) a).hom
  apply (cancel_epi (F.mapIso JR).inv).mp
  apply Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit F _ _
      (SheafOfModules.isColimitFreeCofan (R := (Spec (CommRingCat.of R)).ringCatSheaf) ι))
  intro i
  let gR := basisGenerator (b.baseChange R) i
  let gS := basisGenerator (b.baseChange S) i
  let uR : schemeUnit (Spec (CommRingCat.of R)) ⟶ SheafOfModules.free ι :=
    SheafOfModules.ιFree i
  let uS : schemeUnit (Spec (CommRingCat.of S)) ⟶ SheafOfModules.free ι :=
    SheafOfModules.ιFree i
  change F.map uR ≫ F.map JR.inv ≫ F.map JR.hom ≫ (schemeFreePullback f ι).hom =
    F.map uR ≫ F.map JR.inv ≫ e.hom.app _ ≫ TS.map q ≫ JS.hom
  have hR : uR ≫ JR.inv = TR.map gR := by
    rw [← cancel_mono JR.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (tildeBasisFree_generator (A := CommRingCat.of R) (b.baseChange R) i).symm
  rw [← F.map_comp_assoc, hR, ← F.map_comp_assoc,
    tildeBasisFree_generator, schemeFreePullback_generator]
  have hn := e.hom.naturality_assoc gR (TS.map q ≫ JS.hom)
  change F.map (TR.map gR) ≫ e.hom.app _ ≫ TS.map q ≫ JS.hom =
    e.hom.app _ ≫ TS.map ((ModuleCat.extendScalars (affineRingMap a).hom).map gR) ≫
      TS.map q ≫ JS.hom at hn
  rw [← F.map_comp_assoc, hR, hn, ← TS.map_comp_assoc, ambientTensorIso_generator, TS.map_comp]
  letI : Algebra R S := a.hom.toAlgebra
  have ht : e.hom.app (ModuleCat.of R R) ≫
      TS.map (AlgebraTensorModule.rid R S S).toModuleIso.hom = pullbackUnitMap f :=
    affinePullbackTilde_unit (affineRingMap a)
  have hS : TS.map gS ≫ JS.hom = uS :=
    tildeBasisFree_generator (A := CommRingCat.of S) (b.baseChange S) i
  calc
    _ = pullbackUnitMap f ≫ (TS.map gS ≫ JS.hom) := congrArg (pullbackUnitMap f ≫ ·) hS.symm
    _ = (e.hom.app (ModuleCat.of R R) ≫ TS.map (AlgebraTensorModule.rid R S S).toModuleIso.hom) ≫
        TS.map gS ≫ JS.hom := congrArg (· ≫ TS.map gS ≫ JS.hom) ht.symm
    _ = _ := by simp only [Category.assoc]; rfl

set_option backward.isDefEq.respectTransparency false in
private theorem affineAmbient_naturality :
    (ambientPullback k V ((testSpec k).map a.op)).hom ≫
        (affineAmbientOfBasis (k := k) V b S).hom =
      (Scheme.Modules.pullback (Spec.map (affineRingMap a))).map (affineAmbientOfBasis (k := k) V b R).hom ≫
        (affinePullbackTilde (affineRingMap a)).hom.app (ModuleCat.of R (R ⊗[k] V)) ≫
        (tilde.functor (CommRingCat.of S)).map (ambientTensorIso (V := V) a).hom := by
  let f := Spec.map (affineRingMap a)
  let F := Scheme.Modules.pullback f
  let JR := tildeBasisFree (b.baseChange R)
  let JS := tildeBasisFree (b.baseChange S)
  let AR := ambientFreeIso b ((testSpec k).obj (op R))
  let AS := ambientFreeIso b ((testSpec k).obj (op S))
  let e := affinePullbackTilde (affineRingMap a)
  let c := ambientPullback k V ((testSpec k).map a.op)
  let q := (tilde.functor (CommRingCat.of S)).map (ambientTensorIso (V := V) a).hom
  apply (cancel_mono JS.hom).mp
  change (c.hom ≫ AS.hom ≫ JS.inv) ≫ JS.hom =
    (F.map (AR.hom ≫ JR.inv) ≫ e.hom.app _ ≫ q) ≫ JS.hom
  have h := ambientFreeIso_naturality b ((testSpec k).map a.op)
  change F.map AR.hom ≫ (schemeFreePullback f ι).hom = c.hom ≫ AS.hom at h
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hJR : F.map JR.hom ≫ (schemeFreePullback f ι).hom =
      e.hom.app _ ≫ q ≫ JS.hom := tildeBasisFree_pullback b a
  rw [← h, ← hJR, ← F.map_comp_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable [Fintype ι] [DecidableEq ι] {d : ℕ}
  (hd : d ≤ Module.finrank k V) (P : Plane k V d R)

set_option backward.isDefEq.respectTransparency false in
/-- The affine classification respects scalar extension of the included submodule. -/
theorem affineSubbundleEquiv_pullback :
    IsPullbackSubbundle k V ((testSpec k).map a.op)
      (affineSubbundleEquiv b R hd P)
      (affineSubbundleEquiv b S hd (Module.Grassmannian.map a.hom P)) := by
  letI : Algebra R S := a.hom.toAlgebra
  letI : IsScalarTower k R S := affineTower a
  let Q := Module.Grassmannian.map a.hom P
  obtain ⟨eR, hR⟩ := affineSubbundleEquiv_isTilde b R hd P
  obtain ⟨eS, hS⟩ := affineSubbundleEquiv_isTilde b S hd Q
  let G := ModuleCat.extendScalars (affineRingMap a).hom
  let TR := tilde.functor (CommRingCat.of R)
  let TS := tilde.functor (CommRingCat.of S)
  let F := Scheme.Modules.pullback (Spec.map (affineRingMap a))
  let u := affinePullbackTilde (affineRingMap a)
  let m : ModuleCat.of R P.toSubmodule ⟶ ModuleCat.of R (R ⊗[k] V) :=
    ModuleCat.ofHom P.toSubmodule.subtype
  let n : ModuleCat.of S Q.toSubmodule ⟶ ModuleCat.of S (S ⊗[k] V) :=
    ModuleCat.ofHom Q.toSubmodule.subtype
  let E : G.obj (ModuleCat.of R P.toSubmodule) ≅ ModuleCat.of S Q.toSubmodule :=
    (planePullbackEquiv (S := S) b hd P).toModuleIso
  let e := F.mapIso eR.symm ≪≫ u.app _ ≪≫ TS.mapIso E ≪≫ eS
  have hE : E.hom ≫ n = G.map m ≫ (ambientTensorIso (V := V) a).hom := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.ExtendScalars.map_tmul]
    rfl
  refine ⟨e, (cancel_mono (affineAmbientOfBasis (k := k) V b S).hom).mp ?_⟩
  let lR := (affineSubbundleEquiv b R hd P).val.arrow
  let lS := (affineSubbundleEquiv b S hd Q).val.arrow
  change (F.map eR.inv ≫ u.hom.app _ ≫ TS.map E.hom ≫ eS.hom) ≫ lS ≫
      (affineAmbientOfBasis (k := k) V b S).hom =
    (F.map lR ≫ (ambientPullback k V ((testSpec k).map a.op)).hom) ≫
      (affineAmbientOfBasis (k := k) V b S).hom
  simp only [Category.assoc]
  change eS.hom ≫ lS ≫ (affineAmbientOfBasis (k := k) V b S).hom = TS.map n at hS
  rw [hS, ← TS.map_comp, hE, TS.map_comp, affineAmbient_naturality b a]
  change eR.hom ≫ lR ≫ (affineAmbientOfBasis (k := k) V b R).hom = TR.map m at hR
  have hr : lR ≫ (affineAmbientOfBasis (k := k) V b R).hom = eR.inv ≫ TR.map m := by rw [← hR]; simp
  rw [← F.map_comp_assoc, hr, F.map_comp, Category.assoc]
  exact congrArg (F.map eR.inv ≫ ·)
    (u.hom.naturality_assoc m (TS.map (ambientTensorIso (V := V) a).hom)).symm

end AffineNaturality

section SubbundleFunctoriality

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
  (b : Module.Basis ι k V) {X Y Z : SchemeOver k}

include b in
set_option backward.isDefEq.respectTransparency false in
private theorem ambientPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (ambientPullback k V (f ≫ g)).hom =
      (pullbackComp f.left g.left).inv.app (ambient k V Z) ≫
        (Scheme.Modules.pullback f.left).map (ambientPullback k V g).hom ≫
        (ambientPullback k V f).hom := by
  let eX := ambientFreeIso b X
  let eY := ambientFreeIso b Y
  let eZ := ambientFreeIso b Z
  let F := Scheme.Modules.pullback f.left
  let G := Scheme.Modules.pullback g.left
  let H := Scheme.Modules.pullback (f.left ≫ g.left)
  let c := (pullbackComp f.left g.left).inv.app (ambient k V Z)
  have hf : F.map eY.hom ≫ (schemeFreePullback f.left ι).hom =
      (ambientPullback k V f).hom ≫ eX.hom := ambientFreeIso_naturality b f
  have hg : G.map eZ.hom ≫ (schemeFreePullback g.left ι).hom =
      (ambientPullback k V g).hom ≫ eY.hom := ambientFreeIso_naturality b g
  apply (cancel_mono eX.hom).mp
  rw [← ambientFreeIso_naturality b (f ≫ g)]
  change H.map eZ.hom ≫ (schemeFreePullback (f.left ≫ g.left) ι).hom =
    (c ≫ F.map (ambientPullback k V g).hom ≫ (ambientPullback k V f).hom) ≫ eX.hom
  rw [pullbackTrivialization_comp, hg, F.map_comp]
  simp only [Category.assoc, hf]
  rfl

/-- The pullback equation for an inclusion into the constant bundle. -/
private def IsPullbackInclusion (f : X ⟶ Y) {P : Y.left.Modules} {Q : X.left.Modules}
    (a : P ⟶ ambient k V Y) (c : Q ⟶ ambient k V X) : Prop :=
  ∃ e : (Scheme.Modules.pullback f.left).obj P ≅ Q,
    e.hom ≫ c = (Scheme.Modules.pullback f.left).map a ≫ (ambientPullback k V f).hom

include b in
set_option backward.isDefEq.respectTransparency false in
private theorem pullbackInclusion_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    {P : Z.left.Modules} {Q : Y.left.Modules} {B : X.left.Modules}
    {p : P ⟶ ambient k V Z} {q : Q ⟶ ambient k V Y} {a : B ⟶ ambient k V X}
    (hg : IsPullbackInclusion g p q) (hf : IsPullbackInclusion f q a) :
    IsPullbackInclusion (f ≫ g) p a := by
  obtain ⟨eg, hg⟩ := hg
  obtain ⟨ef, hf⟩ := hf
  let F := Scheme.Modules.pullback f.left
  let G := Scheme.Modules.pullback g.left
  let H := Scheme.Modules.pullback (f.left ≫ g.left)
  let c := (pullbackComp f.left g.left).inv
  refine ⟨((pullbackComp f.left g.left).symm.app P) ≪≫ F.mapIso eg ≪≫ ef, ?_⟩
  change (c.app P ≫ F.map eg.hom ≫ ef.hom) ≫ a =
    H.map p ≫ (ambientPullback k V (f ≫ g)).hom
  simp only [Category.assoc]
  rw [hf, ← F.map_comp_assoc, hg, F.map_comp, ambientPullback_comp b f g]
  simp only [Category.assoc]
  exact (c.naturality_assoc p (F.map (ambientPullback k V g).hom ≫
    (ambientPullback k V f).hom)).symm

variable {d : ℕ}

include b in
set_option backward.isDefEq.respectTransparency false in
theorem pullbackSubbundle_comp (f : X ⟶ Y) (g : Y ⟶ Z) (L : Subbundles k V d Z) :
    pullbackSubbundle f (pullbackSubbundle g L) = pullbackSubbundle (f ≫ g) L :=
  pullbackSubbundle_unique _ _ _ _
    (pullbackInclusion_comp b f g (pullbackSubbundle_spec g L)
      (pullbackSubbundle_spec f (pullbackSubbundle g L))) (pullbackSubbundle_spec (f ≫ g) L)

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackSubbundleId_injective :
    Function.Injective (pullbackSubbundle (k := k) (V := V) (d := d) (𝟙 X)) := by
  intro L M h
  obtain ⟨eL, hL⟩ := pullbackSubbundle_spec (𝟙 X) L
  obtain ⟨eM, hM⟩ := pullbackSubbundle_spec (𝟙 X) M
  let F := Scheme.Modules.pullback (𝟙 X.left)
  letI : F.IsEquivalence := Functor.isEquivalence_of_iso (pullbackId X.left).symm
  let hIso := Subobject.isoOfEq _ _ (congrArg Subtype.val h)
  let e := eL ≪≫ hIso ≪≫ eM.symm
  let ff := F.asEquivalence.fullyFaithfulFunctor
  let E := ff.preimageIso e
  apply Subtype.ext
  apply Subobject.eq_of_comm E
  apply F.map_injective
  have he : F.map E.hom = e.hom := ff.map_preimage _
  rw [F.map_comp, he]
  apply (cancel_mono (ambientPullback k V (𝟙 X)).hom).mp
  simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  change eM.hom ≫ (pullbackSubbundle (𝟙 X) M).val.arrow =
    F.map M.val.arrow ≫ (ambientPullback k V (𝟙 X)).hom at hM
  change eL.hom ≫ (pullbackSubbundle (𝟙 X) L).val.arrow =
    F.map L.val.arrow ≫ (ambientPullback k V (𝟙 X)).hom at hL
  have hIso_arrow : hIso.hom ≫ (pullbackSubbundle (𝟙 X) M).val.arrow =
      (pullbackSubbundle (𝟙 X) L).val.arrow := Subobject.ofLE_arrow (congrArg Subtype.val h).le
  rw [← hM, Iso.inv_hom_id_assoc, hIso_arrow, hL]

include b in
set_option backward.isDefEq.respectTransparency false in
theorem pullbackSubbundle_id (L : Subbundles k V d X) :
    pullbackSubbundle (𝟙 X) L = L := by
  apply pullbackSubbundleId_injective
  simpa only [Iso.refl_hom, Category.id_comp] using pullbackSubbundle_comp b (𝟙 X) (𝟙 X) L

end SubbundleFunctoriality

section OpenSubbundles

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
  {S : SchemeOver k} {d : ℕ}

private abbrev openTest (U : S.left.Opens) : SchemeOver k :=
  Over.mk (U.ι ≫ S.hom)

private abbrev openTestInclusion (U : S.left.Opens) : openTest U ⟶ S :=
  Over.homMk U.ι rfl

private def openTestMap {U W : S.left.Opens} (h : W ≤ U) : openTest W ⟶ openTest U :=
  Over.homMk (S.left.homOfLE h) (by
    change S.left.homOfLE h ≫ U.ι ≫ S.hom = W.ι ≫ S.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])

@[reassoc]
private theorem openTestMap_inclusion {U W : S.left.Opens} (h : W ≤ U) :
    openTestMap h ≫ openTestInclusion U = openTestInclusion W := by
  apply Over.OverMorphism.ext
  exact Scheme.homOfLE_ι S.left h

private def openPullbackComparison (U : S.left.Opens) :
    SheafOfModules.overFunctor S.left.ringCatSheaf U ⋙ (overEquiv U).functor ≅
      Scheme.Modules.pullback U.ι :=
  overFunctorEquiv U ≪≫ restrictFunctorIsoPullback U.ι

private def openAmbientIso (U : S.left.Opens) :
    (overEquiv U).functor.obj ((ambient k V S).over U) ≅ ambient k V (openTest U) :=
  (openPullbackComparison U).app _ ≪≫ ambientPullback k V (openTestInclusion U)

set_option backward.isDefEq.respectTransparency false in
private def openLocalArrow (U : S.left.Opens) (L : Subbundles k V d (openTest U)) :
    (overEquiv U).inverse.obj (L.val : (openTest U).left.Modules) ⟶ (ambient k V S).over U :=
  (overEquiv U).fullyFaithfulFunctor.preimage
    (((overEquiv U).counitIso.app (L.val : (openTest U).left.Modules)).hom ≫ L.val.arrow ≫
      (openAmbientIso U).inv)

set_option backward.isDefEq.respectTransparency false in
private theorem openLocalArrow_map (U : S.left.Opens) (L : Subbundles k V d (openTest U)) :
    (overEquiv U).functor.map (openLocalArrow U L) =
      ((overEquiv U).counitIso.app (L.val : (openTest U).left.Modules)).hom ≫ L.val.arrow ≫
        (openAmbientIso U).inv :=
  (overEquiv U).fullyFaithfulFunctor.map_preimage _

private instance (U : S.left.Opens) (L : Subbundles k V d (openTest U)) : Mono (openLocalArrow U L) := by
  apply (overEquiv U).functor.mono_of_mono_map
  rw [openLocalArrow_map]
  infer_instance

private def openLocalSubmodule (U : S.left.Opens) (L : Subbundles k V d (openTest U)) :
    ((ambient k V S).over U).Submodule :=
  moduleSheafRange (openLocalArrow U L)

set_option backward.isDefEq.respectTransparency false in
private theorem gluedInclusion_pullback {I : Type u} (U : I → S.left.Opens)
    (L : ∀ i, Subbundles k V d (openTest (U i)))
    (h : ∀ i j (W : S.left.Opens) (a : W ⟶ U i) (b : W ⟶ U j)
      (s : (ambient k V S).val.obj (op W)),
      s ∈ (openLocalSubmodule (U i) (L i)).obj (op (Over.mk a)) ↔
      s ∈ (openLocalSubmodule (U j) (L j)).obj (op (Over.mk b)))
    (i : I) :
    IsPullbackInclusion (openTestInclusion (U i))
      (glueOpenSubmodules (ambient k V S) U (fun j ↦ openLocalSubmodule (U j) (L j))).ι
      (L i).val.arrow := by
  let M := ambient k V S
  let P := glueOpenSubmodules M U (fun j ↦ openLocalSubmodule (U j) (L j))
  let Ui := U i
  let N := openLocalSubmodule Ui (L i)
  let F := (overEquiv Ui).functor
  let C := openPullbackComparison Ui
  let u := ambientPullback k V (openTestInclusion Ui)
  let j := openAmbientIso (k := k) (V := V) Ui
  let B := (overEquiv Ui).counitIso.app ((L i).val : (openTest (U i)).left.Modules)
  let q := openLocalArrow Ui (L i)
  let D := glueOpenSubmodulesOverIso M U _ h i
  let E := moduleSheafRangeIso q
  have hD : D.hom ≫ N.ι = P.ι.over Ui := glueOpenSubmodulesOverIso_ι M U _ h i
  have hq : F.map q ≫ j.hom = B.hom ≫ (L i).val.arrow := by
    change (overEquiv Ui).functor.map (openLocalArrow Ui (L i)) ≫ j.hom = _
    rw [openLocalArrow_map]
    change (B.hom ≫ (L i).val.arrow ≫ j.inv) ≫ j.hom = _
    simp
  let e := (C.app P.toSheafOfModules).symm ≪≫ F.mapIso (D ≪≫ E.symm) ≪≫ B
  refine ⟨e, ?_⟩
  change ((C.app P.toSheafOfModules).inv ≫ F.map (D.hom ≫ E.inv) ≫ B.hom) ≫ (L i).val.arrow =
    (Scheme.Modules.pullback Ui.ι).map P.ι ≫ u.hom
  simp only [Category.assoc, ← hq, ← F.map_comp_assoc]
  have hE : E.inv ≫ q = N.ι := E.inv_comp_eq.mpr (moduleSheafRangeIso_ι q).symm
  rw [hE, hD]
  change (C.app _).inv ≫ F.map (P.ι.over Ui) ≫ (C.app M).hom ≫ u.hom = _
  have hn : F.map (P.ι.over Ui) ≫ (C.app M).hom ≫ u.hom =
      (C.app P.toSheafOfModules).hom ≫ (Scheme.Modules.pullback Ui.ι).map P.ι ≫ u.hom :=
    C.hom.naturality_assoc P.ι u.hom
  rw [hn, Iso.inv_hom_id_assoc]

private def extendLocalSubbundle (U : S.left.Opens) (L : Subbundles k V d (openTest U)) :
    (ambient k V S).Submodule :=
  glueOpenSubmodules (ambient k V S) (fun _ : PUnit.{u+1} ↦ U) (fun _ ↦ openLocalSubmodule U L)

private theorem extendLocalSubbundle_pullback (U : S.left.Opens)
    (L : Subbundles k V d (openTest U)) :
    IsPullbackInclusion (openTestInclusion U) (extendLocalSubbundle U L).ι L.val.arrow := by
  apply gluedInclusion_pullback (fun _ : PUnit.{u+1} ↦ U) (fun _ ↦ L) _ PUnit.unit
  intro _ _ _ a b s
  rw [Subsingleton.elim a b]

private theorem extendLocalSubbundle_mem (U : S.left.Opens)
    (L : Subbundles k V d (openTest U)) {W : S.left.Opens} (a : W ⟶ U)
    (s : (ambient k V S).val.obj (op W)) :
    s ∈ (extendLocalSubbundle U L).obj (op W) ↔
      s ∈ (openLocalSubmodule U L).obj (op (Over.mk a)) := by
  apply glueOpenSubmodules_restrict _ (fun _ : PUnit.{u+1} ↦ U)
    (fun _ ↦ openLocalSubmodule U L) _ PUnit.unit a s
  intro _ _ _ a b s
  rw [Subsingleton.elim a b]

set_option backward.isDefEq.respectTransparency false in
private theorem sections_eq_of_pullback (U : S.left.Opens)
    (P Q : (ambient k V S).Submodule) (L : Subbundles k V d (openTest U))
    (hP : IsPullbackInclusion (openTestInclusion U) P.ι L.val.arrow)
    (hQ : IsPullbackInclusion (openTestInclusion U) Q.ι L.val.arrow)
    (s : (ambient k V S).val.obj (op U)) :
    s ∈ P.obj (op U) ↔ s ∈ Q.obj (op U) := by
  obtain ⟨ep, hp⟩ := hP
  obtain ⟨eq, hq⟩ := hQ
  let E := overEquiv U
  let C := openPullbackComparison U
  let A := ambientPullback k V (openTestInclusion U)
  change ep.hom ≫ L.val.arrow = (Scheme.Modules.pullback U.ι).map P.ι ≫ A.hom at hp
  change eq.hom ≫ L.val.arrow = (Scheme.Modules.pullback U.ι).map Q.ι ≫ A.hom at hq
  let e := C.app P.toSheafOfModules ≪≫ ep ≪≫ eq.symm ≪≫ (C.app Q.toSheafOfModules).symm
  have he : e.hom ≫ E.functor.map (Q.ι.over U) = E.functor.map (P.ι.over U) := by
    apply (cancel_mono ((C.app (ambient k V S)).hom ≫ A.hom)).mp
    simp only [Category.assoc]
    have hc (K : (ambient k V S).Submodule) :
        E.functor.map (K.ι.over U) ≫ (C.app (ambient k V S)).hom ≫ A.hom =
          (C.app K.toSheafOfModules).hom ≫ (Scheme.Modules.pullback U.ι).map K.ι ≫ A.hom :=
      C.hom.naturality_assoc K.ι A.hom
    rw [hc P, hc Q]
    change ((C.app P.toSheafOfModules).hom ≫ ep.hom ≫ eq.inv ≫ (C.app Q.toSheafOfModules).inv) ≫
      (C.app Q.toSheafOfModules).hom ≫ (Scheme.Modules.pullback U.ι).map Q.ι ≫ A.hom =
      (C.app P.toSheafOfModules).hom ≫ (Scheme.Modules.pullback U.ι).map P.ι ≫ A.hom
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← hq, ← hp]
  let e' := E.fullyFaithfulFunctor.preimageIso e
  have he' : e'.hom ≫ Q.ι.over U = P.ι.over U := by
    apply E.fullyFaithfulFunctor.map_injective
    have hMap : E.functor.map e'.hom = e.hom := E.fullyFaithfulFunctor.map_preimage _
    rw [Functor.map_comp, hMap]
    exact he
  have hi' : e'.inv ≫ P.ι.over U = Q.ι.over U := by rw [← he']; simp
  let W : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  constructor
  · intro hs
    let t : (P.toSheafOfModules.over U).val.obj W := ⟨s, hs⟩
    let u : Q.obj (op U) := e'.hom.val.app W t
    have hu : (u : (ambient k V S).val.obj (op U)) = s :=
      congrArg (fun g ↦ g.val.app W t) he'
    exact hu ▸ u.property
  · intro hs
    let t : (Q.toSheafOfModules.over U).val.obj W := ⟨s, hs⟩
    let u : P.obj (op U) := e'.inv.val.app W t
    have hu : (u : (ambient k V S).val.obj (op U)) = s :=
      congrArg (fun g ↦ g.val.app W t) hi'
    exact hu ▸ u.property

end OpenSubbundles

section SubbundleDescent

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V] {d : ℕ}
  (b : Module.Basis ι k V) {X Y : SchemeOver k}

include b in
private theorem pullbackSubbundle_injective_of_iso (e : X ≅ Y) :
    Function.Injective (pullbackSubbundle (k := k) (V := V) (d := d) e.hom) := by
  intro L M h
  have he := congrArg (pullbackSubbundle e.inv) h
  rw [pullbackSubbundle_comp b, pullbackSubbundle_comp b,
    e.inv_hom_id, pullbackSubbundle_id b, pullbackSubbundle_id b] at he
  exact he

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackInclusion_precompose (f : X ⟶ Y)
    {P P' : Y.left.Modules} {Q : X.left.Modules}
    {a : P ⟶ ambient k V Y} {a' : P' ⟶ ambient k V Y} {c : Q ⟶ ambient k V X}
    (e : P' ≅ P) (he : e.hom ≫ a = a')
    (h : IsPullbackInclusion f a c) : IsPullbackInclusion f a' c := by
  obtain ⟨E, hE⟩ := h
  let F := Scheme.Modules.pullback f.left
  refine ⟨F.mapIso e ≪≫ E, ?_⟩
  change (F.map e.hom ≫ E.hom) ≫ c = F.map a' ≫ _
  rw [Category.assoc, hE, ← F.map_comp_assoc, he]

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackInclusion_free_split (f : X ⟶ Y)
    {P : Y.left.Modules} {Q : X.left.Modules}
    {a : P ⟶ ambient k V Y} {c : Q ⟶ ambient k V X}
    (h : IsPullbackInclusion f a c)
    (hfree : Nonempty (P ≅ SheafOfModules.free (ULift.{u} (Fin d)))) (hs : IsSplitMono a) :
    Nonempty (Q ≅ SheafOfModules.free (ULift.{u} (Fin d))) ∧ IsSplitMono c := by
  obtain ⟨e, he⟩ := h
  obtain ⟨eP⟩ := hfree
  let F := Scheme.Modules.pullback f.left
  let := hs
  exact ⟨⟨e.symm ≪≫ F.mapIso eP ≪≫ schemeFreePullback f.left _⟩,
    isSplitMono_of_commuting_isos e (ambientPullback k V f) he.symm (isSplitMono_map F a)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem restrictInclusion_free_split (U : X.left.Opens)
    {P : X.left.Modules} {p : P ⟶ ambient k V X}
    (L : Subbundles k V d (openTest U))
    (h : IsPullbackInclusion (openTestInclusion U) p L.val.arrow)
    (hf : Nonempty ((L.val : (openTest U).left.Modules) ≅ SheafOfModules.free (ULift.{u} (Fin d))))
    (hs : IsSplitMono L.val.arrow) :
    Nonempty ((restrictFunctor U.ι).obj P ≅ SheafOfModules.free (ULift.{u} (Fin d))) ∧
      IsSplitMono ((restrictFunctor U.ι).map p) := by
  obtain ⟨e, he⟩ := h
  obtain ⟨E⟩ := hf
  let r := restrictFunctorIsoPullback U.ι
  let c := ambientPullback k V (openTestInclusion U)
  let eP := r.app P ≪≫ e
  let eA := r.app (ambient k V X) ≪≫ c
  refine ⟨⟨eP ≪≫ E⟩, isSplitMono_of_commuting_isos eP.symm eA.symm ?_ hs⟩
  apply (cancel_mono eA.hom).mp
  simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi eP.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  have hn := r.hom.naturality_assoc p c.hom
  change eP.hom ≫ L.val.arrow = (restrictFunctor U.ι).map p ≫ eA.hom
  change (r.app P).hom ≫ e.hom ≫ L.val.arrow =
    (restrictFunctor U.ι).map p ≫ r.hom.app _ ≫ c.hom
  rw [he]
  exact hn.symm

set_option backward.isDefEq.respectTransparency false in
private theorem subbundleRange_pullback (f : X ⟶ Y) (L : Subbundles k V d Y) :
    IsPullbackInclusion f (moduleSheafRange L.val.arrow).ι (pullbackSubbundle f L).val.arrow := by
  let e := moduleSheafRangeIso L.val.arrow
  have he : e.inv ≫ L.val.arrow = (moduleSheafRange L.val.arrow).ι :=
    e.inv_comp_eq.mpr (moduleSheafRangeIso_ι L.val.arrow).symm
  exact pullbackInclusion_precompose f e.symm he (pullbackSubbundle_spec f L)

include b in
set_option backward.isDefEq.respectTransparency false in
private theorem subbundle_ext_locally (L M : Subbundles k V d X)
    (h : ∀ x : X.left, ∃ U : X.left.Opens, x ∈ U ∧
      pullbackSubbundle (openTestInclusion U) L = pullbackSubbundle (openTestInclusion U) M) :
    L = M := by
  let P := moduleSheafRange L.val.arrow
  let Q := moduleSheafRange M.val.arrow
  have hmem (W : X.left.Opens)
      (hw : pullbackSubbundle (openTestInclusion W) L = pullbackSubbundle (openTestInclusion W) M)
      (s : (ambient k V X).val.obj (op W)) : s ∈ P.obj (op W) ↔ s ∈ Q.obj (op W) :=
    sections_eq_of_pullback W P Q (pullbackSubbundle (openTestInclusion W) L)
      (subbundleRange_pullback _ L) (hw.symm ▸ subbundleRange_pullback _ M) s
  have hl (W : X.left.Opens) (x : X.left) (hx : x ∈ W) :
      ∃ T : X.left.Opens, ∃ e : T ⟶ W, x ∈ T ∧
        pullbackSubbundle (openTestInclusion T) L = pullbackSubbundle (openTestInclusion T) M := by
    obtain ⟨U, hU, hEq⟩ := h x
    let T := W ⊓ U
    refine ⟨T, homOfLE inf_le_left, ⟨hx, hU⟩, ?_⟩
    let f : openTest T ⟶ openTest U := openTestMap inf_le_right
    have hf : f ≫ openTestInclusion U = openTestInclusion T := openTestMap_inclusion _
    rw [← hf, ← pullbackSubbundle_comp b, ← pullbackSubbundle_comp b, hEq]
  have hPQ : P = Q := by
    apply le_antisymm
    · intro W s hs
      apply Q.isSheaf s
      intro x hx
      obtain ⟨T, f, hT, hEq⟩ := hl W.unop x hx
      refine ⟨T, f, (hmem T hEq _).mp (P.toSubmodule.map_mem f.op hs), hT⟩
    · intro W s hs
      apply P.isSheaf s
      intro x hx
      obtain ⟨T, f, hT, hEq⟩ := hl W.unop x hx
      refine ⟨T, f, (hmem T hEq _).mpr (Q.toSubmodule.map_mem f.op hs), hT⟩
  apply Subtype.ext
  have hL : L.val = Subobject.mk P.ι :=
    Subobject.eq_mk_of_comm P.ι _ (moduleSheafRangeIso_ι L.val.arrow)
  have hM : M.val = Subobject.mk Q.ι :=
    Subobject.eq_mk_of_comm Q.ι _ (moduleSheafRangeIso_ι M.val.arrow)
  rw [hL, hM, hPQ]

end SubbundleDescent

section Family

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V) {d : ℕ}
  (hd : d ≤ Module.finrank k V) {X Y : SchemeOver k}

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackSubbundle_affine {R S : TestAlgebra k} (a : R ⟶ S) (P : Plane k V d R) :
    pullbackSubbundle ((testSpec k).map a.op) (affineSubbundleEquiv b R hd P) =
      affineSubbundleEquiv b S hd (Module.Grassmannian.map a.hom P) :=
  pullbackSubbundle_unique _ _ _ _ (pullbackSubbundle_spec _ _)
    (affineSubbundleEquiv_pullback b a hd P)

set_option backward.isDefEq.respectTransparency false in
/-- The family of planes obtained by pulling an intrinsic subbundle back to affine test schemes. -/
def subbundleFamily (L : Subbundles k V d X) : Family k V d X where
  app R := ↾fun p ↦ (affineSubbundleEquiv b R hd).symm (pullbackSubbundle p L)
  naturality {R S} a := by
    apply ConcreteCategory.hom_ext
    intro p
    change (affineSubbundleEquiv b S hd).symm (pullbackSubbundle (mapPoints a p) L) =
      Module.Grassmannian.map a.hom ((affineSubbundleEquiv b R hd).symm (pullbackSubbundle p L))
    apply (affineSubbundleEquiv b S hd).injective
    rw [Equiv.apply_symm_apply, ← pullbackSubbundle_affine b hd, Equiv.apply_symm_apply,
      pullbackSubbundle_comp b]

private theorem subbundleFamily_apply (L : Subbundles k V d X) (R : TestAlgebra k) (p : Points X R) :
    (subbundleFamily b hd L).app R p = (affineSubbundleEquiv b R hd).symm (pullbackSubbundle p L) :=
  rfl

private theorem subbundleFamily_pullback (f : Y ⟶ X) (L : Subbundles k V d X)
    (R : TestAlgebra k) (p : Points Y R) :
    (subbundleFamily b hd (pullbackSubbundle f L)).app R p = (subbundleFamily b hd L).app R (p ≫ f) := by
  rw [subbundleFamily_apply, subbundleFamily_apply, pullbackSubbundle_comp b]

private theorem subbundleFamily_injective :
    Function.Injective (subbundleFamily (X := X) b hd) := by
  intro L M h
  apply subbundle_ext_locally b L M
  intro x
  obtain ⟨U, hAff, hx, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.left.Opens) from trivial)
  obtain ⟨R, ⟨e⟩⟩ := (essImage_algSpec (G := openTest U)).mpr hAff
  refine ⟨U, hx, pullbackSubbundle_injective_of_iso b e ?_⟩
  rw [pullbackSubbundle_comp b, pullbackSubbundle_comp b]
  exact (affineSubbundleEquiv b R.unop hd).symm.injective
    (congrArg (fun α : Family k V d X ↦ α.app R.unop (e.hom ≫ openTestInclusion U)) h)

end Family

section UniversalSubbundle

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype ι] [DecidableEq ι] {b : Module.Basis ι k V} {d : ℕ}
  (C : ChartSystem (k := k) (V := V) b d) (hd : d ≤ Module.finrank k V)

private abbrev chartRing (I : Pivot ι d) : TestAlgebra k :=
  CommAlgCat.of k (chartAlgebra (k := k) I)

private def chartOpen (I : Pivot ι d) : C.scheme.left.Opens :=
  letI := C.openChart I
  (C.chart I).left.opensRange

private theorem chartOpen_range (I : Pivot ι d) :
    Set.range (C.chart I).left = Set.range (chartOpen C I).ι := by
  rw [Scheme.Opens.range_ι]
  rfl

set_option backward.isDefEq.respectTransparency false in
private def chartOpenIso (I : Pivot ι d) :
    chartScheme (k := k) I ≅ openTest (chartOpen C I) := by
  letI := C.openChart I
  let e := IsOpenImmersion.isoOfRangeEq (C.chart I).left (chartOpen C I).ι (chartOpen_range C I)
  refine Over.isoMk e ?_
  change e.hom ≫ (chartOpen C I).ι ≫ C.scheme.hom = (chartScheme (k := k) I).hom
  rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, Over.w]

set_option backward.isDefEq.respectTransparency false in
private theorem chartOpenIso_inclusion (I : Pivot ι d) :
    (chartOpenIso C I).hom ≫ openTestInclusion (chartOpen C I) = C.chart I := by
  let := C.openChart I
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ (chartOpen_range C I)

private abbrev chartUniversalPlane (I : Pivot ι d) : Plane k V d (chartRing I) :=
  C.affinePoints.hom.app (chartRing I) (C.chart I)

private abbrev chartAffineSubbundle (I : Pivot ι d) :
    Subbundles k V d (chartScheme (k := k) I) :=
  affineSubbundleEquiv b (chartRing I) hd (chartUniversalPlane C I)

private def chartLocalSubbundle (I : Pivot ι d) : Subbundles k V d (openTest (chartOpen C I)) :=
  pullbackSubbundle (chartOpenIso C I).inv (chartAffineSubbundle C hd I)

set_option backward.isDefEq.respectTransparency false in
private theorem chartAffineSubbundle_free_split (I : Pivot ι d) :
    Nonempty (((chartAffineSubbundle C hd I).val :
      (chartScheme (k := k) I).left.Modules) ≅ SheafOfModules.free (ULift.{u} (Fin d))) ∧
      IsSplitMono (chartAffineSubbundle C hd I).val.arrow := by
  let R : TestAlgebra k := chartRing I
  let P := chartUniversalPlane C I
  let L := chartAffineSubbundle C hd I
  let f : Points (chartScheme (k := k) I) R := 𝟙 _
  let A := matrixOfPoint I R f
  obtain ⟨e, he⟩ := affineSubbundleEquiv_isTilde b R hd P
  have hr : P.toSubmodule = (graphInclusion b I R A).range := by
    have h := C.coordinates_eq I R f
    change (C.affinePoints.hom.app R (f ≫ C.chart I)).toSubmodule =
      (graphInclusion b I R A).range at h
    have hf : f ≫ C.chart I = C.chart I := Category.id_comp _
    rw [hf] at h
    exact h
  let E := LinearEquiv.ofEq _ _ hr ≪≫ₗ (graphRangeEquiv b I R A).symm ≪≫ₗ
    LinearEquiv.funCongrLeft R R ((pivotOrder I).trans Equiv.ulift.symm).symm ≪≫ₗ
    (Finsupp.linearEquivFunOnFinite R R (ULift.{u} (Fin d))).symm
  let F := tilde.functor (CommRingCat.of R)
  refine ⟨⟨e.symm ≪≫ F.mapIso E.toModuleIso ≪≫ tildeFinsupp _⟩, ?_⟩
  have hs : e.hom ≫ L.val.arrow = sheafPlaneArrow b R P := by
    apply (cancel_mono (affineAmbientOfBasis (k := k) V b R).hom).mp
    rw [Category.assoc, he]
    change _ = (_ ≫ (affineAmbientOfBasis (k := k) V b R).inv) ≫
      (affineAmbientOfBasis (k := k) V b R).hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact isSplitMono_of_commuting_isos e (Iso.refl _) (by simpa only [Iso.refl_hom, Category.comp_id] using hs.symm)
    (sheafPlaneArrow_split b hd R P)

private theorem chartLocalSubbundle_free_split (I : Pivot ι d) :
    Nonempty (((chartLocalSubbundle C hd I).val :
      (openTest (chartOpen C I)).left.Modules) ≅ SheafOfModules.free (ULift.{u} (Fin d))) ∧
      IsSplitMono (chartLocalSubbundle C hd I).val.arrow :=
  pullbackInclusion_free_split (chartOpenIso C I).inv (pullbackSubbundle_spec _ _)
    (chartAffineSubbundle_free_split C hd I).1 (chartAffineSubbundle_free_split C hd I).2

set_option backward.isDefEq.respectTransparency false in
private theorem chartLocalSubbundle_probe (I : Pivot ι d) (R : TestAlgebra k)
    (p : Points (openTest (chartOpen C I)) R) :
    pullbackSubbundle p (chartLocalSubbundle C hd I) =
      affineSubbundleEquiv b R hd
        (C.affinePoints.hom.app R (p ≫ openTestInclusion (chartOpen C I))) := by
  let e := chartOpenIso C I
  let a := algHomOfPoint (p ≫ e.inv)
  have ha : (testSpec k).map a.op = p ≫ e.inv := map_algHomOfPoint _
  change pullbackSubbundle p (pullbackSubbundle e.inv (chartAffineSubbundle C hd I)) = _
  rw [pullbackSubbundle_comp b, ← ha, pullbackSubbundle_affine b hd]
  apply congrArg (affineSubbundleEquiv b R hd)
  have h := congrArg (fun g : Points C.scheme (chartRing I) ⟶ Plane k V d R ↦ g (C.chart I))
    (C.affinePoints.hom.naturality a)
  change C.affinePoints.hom.app R ((testSpec k).map a.op ≫ C.chart I) =
    Module.Grassmannian.map a.hom (chartUniversalPlane C I) at h
  rw [← h, ha, Category.assoc, ← chartOpenIso_inclusion C I]
  have he : p ≫ e.inv ≫ (chartOpenIso C I).hom ≫ openTestInclusion (chartOpen C I) =
      p ≫ openTestInclusion (chartOpen C I) := by
    change p ≫ e.inv ≫ e.hom ≫ openTestInclusion (chartOpen C I) = _
    rw [Iso.inv_hom_id_assoc]
  rw [he]

private theorem chartLocalSubbundle_compatible {W : C.scheme.left.Opens} (hW : IsAffineOpen W)
    (I J : Pivot ι d) (hi : W ≤ chartOpen C I) (hj : W ≤ chartOpen C J) :
    pullbackSubbundle (openTestMap hi) (chartLocalSubbundle C hd I) =
      pullbackSubbundle (openTestMap hj) (chartLocalSubbundle C hd J) := by
  obtain ⟨R, ⟨e⟩⟩ := (essImage_algSpec (G := openTest W)).mpr hW
  apply pullbackSubbundle_injective_of_iso b e
  rw [pullbackSubbundle_comp b, pullbackSubbundle_comp b, chartLocalSubbundle_probe,
    chartLocalSubbundle_probe, Category.assoc, openTestMap_inclusion, Category.assoc,
    openTestMap_inclusion]

set_option backward.isDefEq.respectTransparency false in
private theorem chartSubmodule_compatible (I J : Pivot ι d) (W : C.scheme.left.Opens)
    (a : W ⟶ chartOpen C I) (c : W ⟶ chartOpen C J)
    (s : (ambient k V C.scheme).val.obj (op W)) :
    s ∈ (openLocalSubmodule (chartOpen C I) (chartLocalSubbundle C hd I)).obj (op (Over.mk a)) ↔
      s ∈ (openLocalSubmodule (chartOpen C J) (chartLocalSubbundle C hd J)).obj (op (Over.mk c)) := by
  let L := chartLocalSubbundle C hd I
  let M := chartLocalSubbundle C hd J
  let P := extendLocalSubbundle (chartOpen C I) L
  let Q := extendLocalSubbundle (chartOpen C J) M
  rw [← extendLocalSubbundle_mem (chartOpen C I) L a s,
    ← extendLocalSubbundle_mem (chartOpen C J) M c s]
  change s ∈ P.obj (op W) ↔ s ∈ Q.obj (op W)
  have h (T : C.scheme.left.Opens) (hT : IsAffineOpen T) (hl : T ≤ W)
      (v : (ambient k V C.scheme).val.obj (op T)) : v ∈ P.obj (op T) ↔ v ∈ Q.obj (op T) := by
    have hli := hl.trans (leOfHom a)
    have hlj := hl.trans (leOfHom c)
    let l := pullbackSubbundle (openTestMap hli) L
    let m := pullbackSubbundle (openTestMap hlj) M
    have hEq : l = m := chartLocalSubbundle_compatible C hd hT I J hli hlj
    have hP : IsPullbackInclusion (openTestInclusion T) P.ι l.val.arrow := by
      rw [← openTestMap_inclusion hli]
      exact pullbackInclusion_comp b _ _ (extendLocalSubbundle_pullback _ L) (pullbackSubbundle_spec _ L)
    have hQ : IsPullbackInclusion (openTestInclusion T) Q.ι m.val.arrow := by
      rw [← openTestMap_inclusion hlj]
      exact pullbackInclusion_comp b _ _ (extendLocalSubbundle_pullback _ M) (pullbackSubbundle_spec _ M)
    exact sections_eq_of_pullback T P Q l hP (hEq.symm ▸ hQ) v
  constructor
  · intro hs
    apply Q.isSheaf s
    intro x hx
    obtain ⟨T, hT, hxT, hl⟩ := exists_isAffineOpen_mem_and_subset hx
    let j : T ⟶ W := homOfLE hl
    exact ⟨T, j, (h T hT hl _).mp (P.toSubmodule.map_mem j.op hs), hxT⟩
  · intro hs
    apply P.isSheaf s
    intro x hx
    obtain ⟨T, hT, hxT, hl⟩ := exists_isAffineOpen_mem_and_subset hx
    let j : T ⟶ W := homOfLE hl
    exact ⟨T, j, (h T hT hl _).mpr (Q.toSubmodule.map_mem j.op hs), hxT⟩

private def universalSubmodule : (ambient k V C.scheme).Submodule :=
  glueOpenSubmodules (ambient k V C.scheme) (chartOpen C)
    (fun i ↦ openLocalSubmodule (chartOpen C i) (chartLocalSubbundle C hd i))

private theorem universalInclusion_on_chart (I : Pivot ι d) :
    IsPullbackInclusion (openTestInclusion (chartOpen C I))
      (universalSubmodule C hd).ι (chartLocalSubbundle C hd I).val.arrow :=
  gluedInclusion_pullback (chartOpen C) (chartLocalSubbundle C hd) (chartSubmodule_compatible C hd) I

set_option backward.isDefEq.respectTransparency false in
/-- The universal rank-d subbundle glued from the inclusions on the pivot charts. -/
def universalSubbundle : Subbundles k V d C.scheme := by
  let P := universalSubmodule C hd
  letI : Mono P.ι := (SheafOfModules.forget _).mono_of_mono_map
    (inferInstanceAs (Mono P.toSubmodule.ι))
  let e := Subobject.underlyingIso P.ι
  refine ⟨Subobject.mk P.ι, fun x ↦ ?_⟩
  obtain ⟨I, y, rfl⟩ := C.cover x
  let j := openTestInclusion (chartOpen C I)
  let L := chartLocalSubbundle C hd I
  have hP : IsPullbackInclusion j (Subobject.mk P.ι).arrow L.val.arrow :=
    pullbackInclusion_precompose j e (Subobject.underlyingIso_hom_comp_eq_mk P.ι)
      (universalInclusion_on_chart C hd I)
  have h := chartLocalSubbundle_free_split C hd I
  have hmem : (C.chart I).left y ∈ chartOpen C I := ⟨y, rfl⟩
  exact ⟨chartOpen C I, hmem, restrictInclusion_free_split _ L hP h.1 h.2⟩

private theorem universalSubbundle_on_chart (I : Pivot ι d) :
    pullbackSubbundle (openTestInclusion (chartOpen C I)) (universalSubbundle C hd) =
      chartLocalSubbundle C hd I := by
  let P := universalSubmodule C hd
  letI : Mono P.ι := (SheafOfModules.forget _).mono_of_mono_map
    (inferInstanceAs (Mono P.toSubmodule.ι))
  let j := openTestInclusion (chartOpen C I)
  let L := chartLocalSubbundle C hd I
  apply pullbackSubbundle_unique j _ _ _ (pullbackSubbundle_spec j _)
  exact pullbackInclusion_precompose j (Subobject.underlyingIso P.ι)
    (Subobject.underlyingIso_hom_comp_eq_mk P.ι) (universalInclusion_on_chart C hd I)

section

variable {S X : SchemeOver k} (f : S ⟶ X) (U : X.left.Opens)
  (h : ∀ x : S.left, f.left x ∈ U)

private def factorThroughOpen : S ⟶ openTest U := by
  have hRange : Set.range f.left ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact h x
  refine Over.homMk (IsOpenImmersion.lift U.ι f.left hRange) ?_
  change IsOpenImmersion.lift U.ι f.left hRange ≫ U.ι ≫ X.hom = S.hom
  rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.w]

@[reassoc]
private theorem factorThroughOpen_inclusion :
    factorThroughOpen f U h ≫ openTestInclusion U = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

end

set_option maxHeartbeats 700000 in
set_option backward.isDefEq.respectTransparency false in
/-- On an affine probe the universal subsheaf restricts to the tilde of its plane. -/
theorem universalSubbundle_affine (R : TestAlgebra k) (p : Points C.scheme R) :
    pullbackSubbundle p (universalSubbundle C hd) =
      affineSubbundleEquiv b R hd (C.affinePoints.hom.app R p) := by
  let S := (testSpec k).obj (op R)
  let L := universalSubbundle C hd
  let Q := affineSubbundleEquiv b R hd (C.affinePoints.hom.app R p)
  apply subbundle_ext_locally b (pullbackSubbundle p L) Q
  intro x
  obtain ⟨I, y, hy⟩ := C.cover (p.left x)
  let U := chartOpen C I
  have hx : x ∈ p.left ⁻¹ᵁ U := ⟨y, hy⟩
  obtain ⟨W, hW, hxW, hwU⟩ := exists_isAffineOpen_mem_and_subset hx
  let w := openTestInclusion (S := S) W
  let v := factorThroughOpen (w ≫ p) U (fun z ↦ hwU z.property)
  have hv : v ≫ openTestInclusion U = w ≫ p := factorThroughOpen_inclusion _ _ _
  obtain ⟨T, ⟨e⟩⟩ := (essImage_algSpec (G := openTest W)).mpr hW
  refine ⟨W, hxW, pullbackSubbundle_injective_of_iso b e ?_⟩
  change pullbackSubbundle e.hom (pullbackSubbundle w (pullbackSubbundle p L)) =
    pullbackSubbundle e.hom (pullbackSubbundle w Q)
  rw [pullbackSubbundle_comp b w p, ← hv, ← pullbackSubbundle_comp b v,
    universalSubbundle_on_chart, pullbackSubbundle_comp b e.hom v,
    chartLocalSubbundle_probe, pullbackSubbundle_comp b e.hom w]
  let a := algHomOfPoint (e.hom ≫ w)
  have ha : (testSpec k).map a.op = e.hom ≫ w := map_algHomOfPoint _
  rw [← ha, pullbackSubbundle_affine b hd]
  apply congrArg (affineSubbundleEquiv b T.unop hd)
  have h := congrArg (fun g : Points C.scheme R ⟶ Plane k V d T.unop ↦ g p)
    (C.affinePoints.hom.naturality a)
  change C.affinePoints.hom.app T.unop ((testSpec k).map a.op ≫ p) =
    Module.Grassmannian.map a.hom (C.affinePoints.hom.app R p) at h
  rw [← h, ha, Category.assoc, hv, ← Category.assoc]

end UniversalSubbundle

section AllSchemePoints

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V]
  [Fintype ι] [DecidableEq ι] {b : Module.Basis ι k V} {d : ℕ}
  (C : ChartSystem (k := k) (V := V) b d) (hd : d ≤ Module.finrank k V) (S : SchemeOver k)

private theorem subbundleFamily_universal (p : S ⟶ C.scheme) :
    subbundleFamily b hd (pullbackSubbundle p (universalSubbundle C hd)) =
      familyEquiv C.affinePoints S p := by
  ext R a
  let q : Points S R := a
  let L := universalSubbundle C hd
  change (subbundleFamily b hd (pullbackSubbundle p L)).app R q =
    (familyEquiv C.affinePoints S p).app R q
  let E := affineSubbundleEquiv b R hd
  let t : Points C.scheme R := q ≫ p
  let P : Plane k V d R := C.affinePoints.hom.app R t
  have h₁ : ((subbundleFamily b hd (pullbackSubbundle p L)).app R q : Plane k V d R) =
      (subbundleFamily b hd L).app R t := subbundleFamily_pullback b hd p L R q
  have h₂ : ((subbundleFamily b hd L).app R t : Plane k V d R) =
      E.symm (pullbackSubbundle t L) := subbundleFamily_apply b hd L R t
  have h₃ : E.symm (pullbackSubbundle t L) = E.symm (E P) :=
    congrArg E.symm (universalSubbundle_affine C hd R t)
  have h₄ : P = (familyEquiv C.affinePoints S p).app R q :=
    (familyEquiv_apply C.affinePoints p R q).symm
  exact h₁.trans (h₂.trans (h₃.trans ((E.symm_apply_apply P).trans h₄)))

/-- The intrinsic subbundle and affine-probe models of the Grassmannian over any test scheme. -/
def familySubbundleEquiv : Family k V d S ≃ Subbundles k V d S :=
  (Equiv.ofBijective (subbundleFamily b hd) ⟨subbundleFamily_injective b hd, fun α ↦ by
    let p := (familyEquiv C.affinePoints S).symm α
    exact ⟨pullbackSubbundle p (universalSubbundle C hd),
      (subbundleFamily_universal C hd S p).trans ((familyEquiv _ _).apply_symm_apply α)⟩⟩).symm

private theorem familySubbundleEquiv_apply (p : S ⟶ C.scheme) :
    familySubbundleEquiv C hd S (familyEquiv C.affinePoints S p) =
      pullbackSubbundle p (universalSubbundle C hd) := by
  exact (familySubbundleEquiv C hd S).symm_apply_eq.mp (subbundleFamily_universal C hd S p) |>.symm

/-- The basis-indexed pivot gluing represents rank-d locally split subbundles on all schemes. -/
def schemePoints : SchemePoints (k := k) (V := V) d C.scheme C.affinePoints where
  family := familyEquiv C.affinePoints
  family_apply := fun _ ↦ familyEquiv_apply C.affinePoints
  subbundle := familySubbundleEquiv C hd
  pullback := by
    intro T S f p
    rw [familySubbundleEquiv_apply, familySubbundleEquiv_apply, ← pullbackSubbundle_comp b]
    exact pullbackSubbundle_spec f _

/-- Construction of the Grassmannian by pivot charts, including its universal property on schemes. -/
theorem construction : Construction.{u} := by
  intro k V ι _ _ _ _ _ b d hd
  let C := chartSystem b hd
  refine ⟨C, schemePoints C hd, ?_⟩
  intro R p
  change IsTildePlane (k := k) V b R (C.affinePoints.hom.app R p)
    (familySubbundleEquiv C hd ((testSpec k).obj (op R)) (familyEquiv C.affinePoints _ p))
  rw [familySubbundleEquiv_apply, universalSubbundle_affine]
  exact affineSubbundleEquiv_isTilde b R hd _

end AllSchemePoints

end SchemeSubbundles

end

end LinearAlgebraicGroups.GrassmannianCharts
