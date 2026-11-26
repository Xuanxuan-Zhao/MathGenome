import Specs.LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
import LinearAlgebraicGroups.Affine.HopfAlgebras
import LinearAlgebraicGroups.Affine.ClosedSubgroups
import LinearAlgebraicGroups.Unipotent.ExactOperations
import LinearAlgebraicGroups.Reductive.GeometricRadicals
import LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj Matrix TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport

noncomputable section

set_option linter.style.haveILetI false

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme ClosedSubgroup)
open Specs.AdjointRepresentation (GroupPoints)

variable {F E : Type u} [Field F] [Field E]

private theorem fieldSpecMap_isIso (e : F ≃+* E) :
    letI := scalarStructure e
    IsIso (fieldSpecMap F E) := by
  letI := scalarStructure e
  change IsIso (Scheme.Spec.map (e.toCommRingCatIso.hom.op))
  exact (Scheme.Spec : CommRingCatᵒᵖ ⥤ Scheme).map_isIso e.toCommRingCatIso.hom.op

private def fieldTestIso (e : F ≃+* E) :
    letI := scalarStructure e
    (restrictTestAlgebra F E).obj (CommAlgCat.of E E) ≅ CommAlgCat.of F F := by
  letI := scalarStructure e
  let a := (restrictTestAlgebra F E).obj (CommAlgCat.of E E)
  let b := CommAlgCat.of F F
  let i : a ≃ₐ[F] b := AlgEquiv.ofRingEquiv (f := e.symm) e.symm_apply_apply
  exact ⟨CommAlgCat.ofHom i.toAlgHom, CommAlgCat.ofHom i.symm.toAlgHom,
    CommAlgCat.hom_ext (DFunLike.ext _ _ i.symm_apply_apply),
    CommAlgCat.hom_ext (DFunLike.ext _ _ i.apply_symm_apply)⟩

private def projection (e : F ≃+* E) (X : SchemeOver F) :
    letI := scalarStructure e
    ((baseChange F E).obj X).left ⟶ X.left := by
  letI := scalarStructure e
  exact pullback.fst X.hom (fieldSpecMap F E)

private def pullCoordinate (e : F ≃+* E) (X : SchemeOver F) :
    letI := scalarStructure e
    Γ(X.left, ⊤) ≃+* Γ(((baseChange F E).obj X).left, ⊤) := by
  letI := scalarStructure e
  letI := fieldSpecMap_isIso e
  haveI : IsIso (projection e X) :=
    inferInstanceAs (IsIso (pullback.fst X.hom (fieldSpecMap F E)))
  exact (Scheme.Γ.mapIso (asIso (projection e X)).op).commRingCatIsoToRingEquiv

set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_originalPoint (e : F ≃+* E) (X : SchemeOver F) :
    letI := scalarStructure e
    ∀ (p : RationalPoints ((baseChange F E).obj X)) (a : Γ(X.left, ⊤)),
      evaluation (originalPoint e X p) a = e.symm (evaluation p (pullCoordinate e X a)) := by
  letI := scalarStructure e
  intro p a
  let q : Spec (CommRingCat.of E) ⟶ ((baseChange F E).obj X).left := p.left
  change (((Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ q ≫ projection e X).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom) a = _
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Category.assoc, Category.assoc,
    Scheme.ΓSpecIso_naturality]
  rfl

private def originalGroupEquiv (e : F ≃+* E) (G : GroupScheme F) :
    letI := scalarStructure e
    RationalPoints ((groupBaseChange F E).obj G).X ≃* RationalPoints G.X := by
  letI := scalarStructure e
  let R := CommAlgCat.of E E
  let a := fieldTestIso e
  let f := (groupPointsFunctor F).obj G
  let i := f.mapIso a
  let f₁ := baseChangePointGroupEquiv E G R
  exact f₁.trans (MulEquiv.ofBijective i.hom.hom (ConcreteCategory.bijective_of_isIso i.hom))

private theorem originalGroupEquiv_apply (e : F ≃+* E) (G : GroupScheme F) :
    letI := scalarStructure e
    ∀ p, originalGroupEquiv e G p = originalPoint e G.X p := by
  letI := scalarStructure e
  intro p
  rfl

private theorem continuous_evaluation [TopologicalSpace F] (X : SchemeOver F)
    (a : Γ(X.left, ⊤)) :
    letI := pointTopology X
    Continuous (fun p : RationalPoints X ↦ evaluation p a) := by
  letI := pointTopology X
  exact (continuous_apply a).comp continuous_induced_dom

private theorem continuous_originalPoint [TopologicalSpace F] [TopologicalSpace E]
    (e : F ≃+* E) (h : Continuous e.symm) (X : SchemeOver F) :
    letI := scalarStructure e
    letI := pointTopology X
    letI := pointTopology ((baseChange F E).obj X)
    Continuous (originalPoint e X) := by
  letI := scalarStructure e
  letI := pointTopology X
  letI := pointTopology ((baseChange F E).obj X)
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro a
  simp only [Function.comp_def, evaluation_originalPoint]
  exact h.comp (continuous_evaluation ((baseChange F E).obj X) (pullCoordinate e X a))

set_option backward.isDefEq.respectTransparency false in
private theorem continuous_pointMap [TopologicalSpace F] {X Y : SchemeOver F} (f : X ⟶ Y) :
    letI := pointTopology X
    letI := pointTopology Y
    Continuous (fun p : RationalPoints X ↦ p ≫ f) := by
  letI := pointTopology X
  letI := pointTopology Y
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro a
  have h (p : RationalPoints X) : evaluation (p ≫ f) a = evaluation p (f.left.appTop a) := by
    unfold evaluation
    let q : Spec (CommRingCat.of F) ⟶ X.left := p.left
    change ((q ≫ f.left).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom a = _
    rw [Scheme.Hom.comp_appTop]
    rfl
  change Continuous (fun p : RationalPoints X ↦ evaluation (p ≫ f) a)
  simp only [h]
  exact continuous_evaluation X (f.left.appTop a)

theorem rationalMorphismContinuous : RationalMorphismContinuous.{u} :=
  fun f ↦ continuous_pointMap f

section PointGroupTopology

open WithConv
open scoped CategoryTheory.GrpObj TensorProduct

set_option backward.isDefEq.respectTransparency false in
private theorem continuousMul_hopfSpectrum [TopologicalSpace F] [IsTopologicalRing F]
    (A : HopfAlgebraCategory F) :
    let H := (hopfSpec (CommRingCat.of F)).obj (op A)
    letI := pointTopology H.X
    ContinuousMul (RationalPoints H.X) := by
  let H := (hopfSpec (CommRingCat.of F)).obj (op A)
  letI := pointTopology H.X
  let R := CommAlgCat.of F F
  obtain ⟨χ, hχ, _⟩ := hopfSpecPoints F
  let b := ((χ A).app R).groupIsoToMulEquiv
  let i := Scheme.ΓSpecIso (CommRingCat.of A)
  have hEval (z : WithConv (A →ₐ[F] F)) (a : Γ(H.X.left, ⊤)) :
      evaluation (b z) a = z.ofConv (i.hom a) := by
    have hd : ((b z : RationalPoints H.X)).left =
        Spec.map (CommRingCat.ofHom z.ofConv.toRingHom) := hχ A R z
    unfold evaluation
    rw [hd, Scheme.ΓSpecIso_naturality]
    rfl
  have hcont (a : A) : Continuous (fun p : RationalPoints H.X ↦ (b.symm p).ofConv a) := by
    have h (p : RationalPoints H.X) : (b.symm p).ofConv a = evaluation p (i.inv a) := by
      simpa only [b.apply_symm_apply, Iso.inv_hom_id_apply] using (hEval (b.symm p) (i.inv a)).symm
    simp only [h]
    exact continuous_evaluation H.X (i.inv a)
  let Φ (p : RationalPoints H.X × RationalPoints H.X) : A ⊗[F] A →ₐ[F] F :=
    Algebra.TensorProduct.lift (b.symm p.1).ofConv (b.symm p.2).ofConv
      (fun _ _ ↦ Commute.all _ _)
  have ht (z : A ⊗[F] A) :
      Continuous (fun p : RationalPoints H.X × RationalPoints H.X ↦ Φ p z) := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      have h₁ := (hcont x).comp (continuous_fst (X := RationalPoints H.X) (Y := RationalPoints H.X))
      have h₂ := (hcont y).comp (continuous_snd (X := RationalPoints H.X) (Y := RationalPoints H.X))
      convert h₁.mul h₂ using 1
      funext p
      exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
    | add x y hx hy =>
      convert hx.add hy using 1
      funext p
      exact map_add (Φ p) x y
  refine ⟨?_⟩
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro a
  have h (p : RationalPoints H.X × RationalPoints H.X) :
      evaluation (p.1 * p.2) a = Φ p (Bialgebra.comulAlgHom F A (i.hom a)) := by
    have hp : p.1 * p.2 = b (b.symm p.1 * b.symm p.2) := by
      symm
      exact (map_mul b _ _).trans (congrArg₂ (· * ·) (b.apply_symm_apply p.1) (b.apply_symm_apply p.2))
    rw [hp, hEval]
    exact AlgHom.convMul_apply (b.symm p.1) (b.symm p.2) (i.hom a)
  change Continuous (fun p : RationalPoints H.X × RationalPoints H.X ↦ evaluation (p.1 * p.2) a)
  simp only [h]
  exact ht _

private theorem continuousMul_of_mulEquiv {A B : Type*} [Mul A] [Mul B]
    [TopologicalSpace A] [TopologicalSpace B] [ContinuousMul A]
    (r : A ≃* B) (ha : Continuous r) (hb : Continuous r.symm) : ContinuousMul B := by
  have hpair : Continuous (fun p : B × B ↦ (r.symm p.1, r.symm p.2)) :=
    (hb.comp continuous_fst).prodMk (hb.comp continuous_snd)
  refine ⟨(ha.comp (continuous_mul.comp hpair)).congr ?_⟩
  intro p
  change r (r.symm p.1 * r.symm p.2) = p.1 * p.2
  rw [map_mul, r.apply_symm_apply, r.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
theorem rationalPointTopologicalGroup : RationalPointTopologicalGroup.{u} := by
  intro F _ _ _ G
  letI := pointTopology G.val.X
  obtain ⟨A, ⟨a⟩⟩ := essImage_hopfSpec.mpr G.property.1
  let H := (hopfSpec (CommRingCat.of F)).obj A
  letI := pointTopology H.X
  haveI : ContinuousMul (RationalPoints H.X) := continuousMul_hopfSpectrum A.unop
  let r : RationalPoints H.X ≃* RationalPoints G.val.X :=
    (((groupPointsFunctor F).mapIso a).app (CommAlgCat.of F F)).groupIsoToMulEquiv
  have ha : Continuous r := continuous_pointMap a.hom.hom.hom
  have hb : Continuous r.symm := continuous_pointMap a.inv.hom.hom
  exact
    { continuous_mul := (continuousMul_of_mulEquiv r ha hb).continuous_mul
      continuous_inv := continuous_pointMap (ι[G.val.X]) }

end PointGroupTopology

set_option backward.isDefEq.respectTransparency false in
theorem rationalGroupTransport : RationalGroupTransport.{u} := by
  intro F E _ _ _ _ e he he' G
  letI := scalarStructure e
  let G' := Specs.Unipotent.baseChangedAlgebraicGroup E G
  letI := pointTopology G.val.X
  letI := pointTopology G'.val.X
  let f := originalGroupEquiv e G.val
  refine ⟨f.symm, ?_, continuous_originalPoint e he' G.val.X, originalGroupEquiv_apply e G.val⟩
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro b
  obtain ⟨a, rfl⟩ := (pullCoordinate e G.val.X).surjective b
  have eqn (p : RationalPoints G.val.X) :
      evaluation (f.symm p) (pullCoordinate e G.val.X a) = e (evaluation p a) := by
    apply e.symm.injective
    have h := evaluation_originalPoint e G.val.X (f.symm p) a
    change evaluation (f (f.symm p)) a = _ at h
    rw [f.apply_symm_apply] at h
    rw [e.symm_apply_apply]
    exact h.symm
  change Continuous (fun p : RationalPoints G.val.X ↦ evaluation (f.symm p) (pullCoordinate e G.val.X a))
  simp only [eqn]
  exact he.comp (continuous_evaluation G.val.X a)

theorem evaluationTransport : EvaluationTransport.{u} := by
  intro F E _ _ e X
  letI := scalarStructure e
  intro p a
  exact (congrArg e (evaluation_originalPoint e X p a)).trans
    (e.apply_symm_apply _)
    |>.symm

set_option backward.isDefEq.respectTransparency false in
theorem pointNaturality : PointNaturality.{u} := by
  intro F E _ _ e X Y f
  letI := scalarStructure e
  intro p
  unfold originalPoint
  rw [baseChangePointsSchemeNaturality]
  exact Category.assoc _ _ _ |>.symm

set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_algebraMap (X : SchemeOver F) (p : RationalPoints X) (r : F) :
    letI := coordinateAlgebra X
    evaluation p (algebraMap F Γ(X.left, ⊤) r) = r := by
  let h : X.hom.appTop ≫ p.left.appTop = 𝟙 Γ(Spec (CommRingCat.of F), ⊤) := by
    rw [← Scheme.Hom.comp_appTop, Over.w p]
    change (Spec.map (𝟙 (CommRingCat.of F))).appTop = _
    rw [Spec.map_id, Scheme.Hom.id_appTop]
  have h' : (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ X.hom.appTop ≫ p.left.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom = 𝟙 _ := by
    rw [← Category.assoc X.hom.appTop, h, Category.id_comp, Iso.inv_hom_id]
  exact congrArg (fun f : CommRingCat.of F ⟶ CommRingCat.of F ↦ f r) h'

theorem coordinateTopology : CoordinateTopology.{u} := by
  intro F _ _ _ X idx c
  letI := coordinateAlgebra X
  intro hc
  let T : TopologicalSpace (RationalPoints X) :=
    .induced (fun p (i : idx) ↦ evaluation p (c i)) inferInstance
  change pointTopology X = T
  apply le_antisymm
  · apply continuous_iff_le_induced.mp
    letI := pointTopology X
    exact continuous_pi fun i ↦ continuous_evaluation X (c i)
  · apply continuous_iff_le_induced.mp
    letI := T
    apply continuous_pi
    intro a
    have ha : a ∈ Algebra.adjoin F (Set.range c) := hc.symm ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem a h =>
      obtain ⟨i, rfl⟩ := h
      have ht : Continuous (fun p : RationalPoints X ↦ fun j : idx ↦ evaluation p (c j)) :=
        continuous_induced_dom
      exact (continuous_apply i).comp ht
    | algebraMap r =>
      simpa only [evaluation_algebraMap] using
        (continuous_const : Continuous (fun _ : RationalPoints X ↦ r))
    | add x y hx hy h₁ h₂ =>
      convert h₁.add h₂ using 1
      funext p
      exact map_add (evaluation p) x y
    | mul x y hx hy h₁ h₂ =>
      convert h₁.mul h₂ using 1
      funext p
      exact map_mul (evaluation p) x y

theorem matrixTopology : MatrixTopology.{u} := by
  intro F _ _ _ _ X n _ _ c d
  letI := coordinateAlgebra X
  intro m hg hn hd
  let coords : Option (n × n) → Γ(X.left, ⊤)
    | none => d
    | some (i, j) => c i j
  have hr : Set.range coords = insert d (Set.range fun ij : n × n ↦ c ij.1 ij.2) := by
    ext a
    constructor
    · rintro ⟨(_ | ⟨i, j⟩), rfl⟩
      · exact Set.mem_insert d _
      · exact Set.mem_insert_of_mem _ ⟨(i, j), rfl⟩
    · intro ha
      rcases ha with h | ⟨ij, rfl⟩
      · exact ⟨none, h.symm⟩
      · exact ⟨some ij, rfl⟩
  let pcoords := fun p : RationalPoints X ↦ fun i ↦ evaluation p (coords i)
  have htop : pointTopology X = TopologicalSpace.induced pcoords inferInstance :=
    coordinateTopology X coords (hr.symm ▸ hg)
  rw [htop]
  apply le_antisymm
  · apply continuous_iff_le_induced.mp
    letI := TopologicalSpace.induced pcoords inferInstance
    have hp : Continuous pcoords := continuous_induced_dom
    apply continuous_matrix
    intro i j
    change Continuous (fun p ↦ pcoords p (some (i, j)))
    exact (continuous_apply (some (i, j))).comp hp
  · apply continuous_iff_le_induced.mp
    letI := TopologicalSpace.induced m inferInstance
    have hm : Continuous m := continuous_induced_dom
    apply continuous_pi
    intro i
    cases i with
    | none =>
      change Continuous (fun p : RationalPoints X ↦ evaluation p d)
      simp only [hd]
      exact hm.matrix_det.inv₀ hn
    | some ij => exact hm.matrix_elem ij.1 ij.2

open ValuativeRel in
theorem uniformizerGeneratesMaximalIdeal : UniformizerGeneratesMaximalIdeal.{u} := by
  intro F _ _ π O
  let v := valuation F
  have hmem (x : F) : x ∈ O ↔ x ≤ᵥ 1 :=
    (v.mem_valuationSubring_iff x).trans v.vle_one_iff.symm
  have hmax (x : O) : x ∈ IsLocalRing.maximalIdeal O ↔ (x : F) <ᵥ 1 :=
    v.mem_maximalIdeal_iff.trans v.vlt_one_iff.symm
  constructor
  · rintro ⟨hπ, h⟩
    let p : O := ⟨π, (hmem π).mpr hπ.vle⟩
    have hp := (hmax p).mpr hπ
    refine ⟨p, rfl, le_antisymm ?_ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp))⟩
    intro x hx
    apply Ideal.mem_span_singleton'.mpr
    have hd : (x : F) / (π : F) ≤ᵥ 1 :=
      (ValuativeRel.div_vle_one_iff π.ne_zero).mpr (h x ((hmax x).mp hx))
    let y : O := ⟨(x : F) / (π : F), (hmem _).mpr hd⟩
    exact ⟨y, Subtype.ext (div_mul_cancel₀ (x : F) π.ne_zero)⟩
  · rintro ⟨p, hp, hgen⟩
    have hm : p ∈ IsLocalRing.maximalIdeal O := hgen.symm ▸ Ideal.subset_span (Set.mem_singleton p)
    refine ⟨hp ▸ (hmax p).mp hm, ?_⟩
    intro x hx
    let z : O := ⟨x, (hmem x).mpr hx.vle⟩
    have hz : z ∈ Ideal.span {p} := hgen ▸ (hmax z).mpr hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hz
    have heq : (y : F) * (p : F) = x := congrArg Subtype.val hy
    have hle : (y : F) * (p : F) ≤ᵥ 1 * (p : F) :=
      ValuativeRel.mul_vle_mul_left ((hmem _).mp y.property) _
    rw [one_mul, heq, hp] at hle
    exact hle

open ValuativeRel in
theorem uniformizerTransport : UniformizerTransport.{u} := by
  intro F E _ _ _ _ e he s
  have hlt (x y : F) : e x <ᵥ e y ↔ x <ᵥ y := by
    simp only [ValuativeRel.vlt, he]
  have h₁ : e (s : F) <ᵥ (1 : E) ↔ (s : F) <ᵥ (1 : F) := by
    simpa only [map_one] using hlt (s : F) 1
  change (e (s : F) <ᵥ 1 ∧ ∀ x : E, x <ᵥ 1 → x ≤ᵥ e (s : F)) ↔
    ((s : F) <ᵥ 1 ∧ ∀ x : F, x <ᵥ 1 → x ≤ᵥ (s : F))
  rw [h₁]
  apply and_congr_right
  intro _
  constructor
  · intro h x hx
    apply (he x (s : F)).mp
    exact h (e x) (by simpa only [map_one] using (hlt x 1).mpr hx)
  · intro h x hx
    obtain ⟨y, rfl⟩ := e.surjective x
    exact (he y (s : F)).mpr (h y ((hlt y 1).mp (by simpa only [map_one] using hx)))

theorem matrixCoordinateTransport : MatrixCoordinateTransport.{u} := by
  intro F E _ _ e X n c
  letI := scalarStructure e
  intro p
  ext i j
  exact evaluationTransport e X p (c i j)

theorem sesquilinearMatrixTransport : SesquilinearMatrixTransport.{u} := by
  intro A B n _ _ _ _ _ i hi M H
  have h : (Mᴴ).map i = (M.map i)ᴴ := by
    ext a b
    exact hi (M b a)
  rw [← h, ← Matrix.map_mul, ← Matrix.map_mul]
  constructor
  · intro he
    ext a b
    exact i.injective (congrArg (fun C : Matrix n n B ↦ C a b) he)
  · exact congrArg (fun C : Matrix n n A ↦ C.map i)

theorem specialMatrixTransport : SpecialMatrixTransport.{u} := by
  intro A B n _ _ _ _ i M
  change (i.mapMatrix M).det = 1 ↔ M.det = 1
  rw [← i.map_det, ← map_one i, i.injective.eq_iff]

private theorem transportedInvolution_map {A B : Type u} [Ring A] [Ring B] [StarRing A]
    (i : A ≃+* B) :
    letI := transportedInvolution i
    ∀ a, i (star a) = star (i a) := by
  letI := transportedInvolution i
  intro a
  change i (star a) = i (star (i.symm (i a)))
  rw [i.symm_apply_apply]

theorem coefficientAlgebraTransport : CoefficientAlgebraTransport.{u} := by
  intro F E _ _ e A _ _ _ hstar
  letI := scalarStructure e
  let incl : A →ₐ[F] E ⊗[F] A := Algebra.TensorProduct.includeRight
  let i := RingEquiv.ofBijective incl (Algebra.TensorProduct.includeRight_bijective e.bijective)
  have hi (a : A) : i a = (1 : E) ⊗ₜ[F] a := rfl
  have hbal (r : F) (a : A) :
      (1 : E) ⊗ₜ[F] (algebraMap F A r * a) = e r ⊗ₜ[F] a := by
    rw [← Algebra.smul_def, TensorProduct.tmul_smul]
    change ((e r * 1) : E) ⊗ₜ[F] a = e r ⊗ₜ[F] a
    rw [mul_one]
  refine ⟨i, hi, ?_, ?_⟩
  · intro r
    rw [hi, Algebra.TensorProduct.algebraMap_apply]
    change (1 : E) ⊗ₜ[F] algebraMap F A r = e r ⊗ₜ[F] 1
    simpa only [mul_one] using hbal r (1 : A)
  · letI := transportedInvolution i
    intro t a
    obtain ⟨r, rfl⟩ := e.surjective t
    calc
      star (e r ⊗ₜ[F] a) = star (i (algebraMap F A r * a)) := by rw [hi, hbal]
      _ = i (algebraMap F A r * star a) := by
        rw [← transportedInvolution_map i, star_mul, hstar, Algebra.commutes]
      _ = e r ⊗ₜ[F] star a := by rw [hi, hbal]

theorem quaternionicQuadraticFormTransport : QuaternionicQuadraticFormTransport.{u} := by
  intro F E _ _ e A B n _ _ _ _ _ _ _ i hscalar hstar M H L
  have hvec (C : Matrix n n A) (v : n → A) :
      i ∘ (C *ᵥ v) = C.map i *ᵥ (i ∘ v) := by
    funext j
    exact i.toRingHom.map_mulVec C v j
  have hvalue (v : n → A) :
      i (quaternionicValue H L v) = quaternionicValue (H.map i) (L.map i) (i ∘ v) := by
    unfold quaternionicValue
    have hprod := i.toRingHom.map_dotProduct (star ∘ v) (H *ᵥ (L *ᵥ v))
    change i ((star ∘ v) ⬝ᵥ (H *ᵥ (L *ᵥ v))) =
      (i ∘ (star ∘ v)) ⬝ᵥ (i ∘ (H *ᵥ (L *ᵥ v))) at hprod
    rw [hprod, hvec, hvec]
    congr 1
    funext j
    exact hstar (v j)
  have hrange (a : A) :
      i a ∈ Set.range (algebraMap E B) ↔ a ∈ Set.range (algebraMap F A) := by
    constructor
    · rintro ⟨t, ht⟩
      obtain ⟨r, rfl⟩ := e.surjective t
      exact ⟨r, i.injective ((hscalar r).trans ht)⟩
    · rintro ⟨r, rfl⟩
      exact ⟨e r, (hscalar r).symm⟩
  unfold PreservesQuaternionicQuadraticForm
  have h (v : n → A) :
      (quaternionicValue (H.map i) (L.map i) (M.map i *ᵥ (i ∘ v)) -
        quaternionicValue (H.map i) (L.map i) (i ∘ v)) ∈ Set.range (algebraMap E B) ↔
      (quaternionicValue H L (M *ᵥ v) - quaternionicValue H L v) ∈
        Set.range (algebraMap F A) := by
    rw [← hvec, ← hvalue, ← hvalue, ← map_sub, hrange]
  constructor
  · exact fun hp v ↦ (h v).mp (hp (i ∘ v))
  · intro hp v
    have heq : v = i ∘ (i.symm ∘ v) := by
      funext j
      exact (i.apply_symm_apply (v j)).symm
    simpa only [← heq] using (h (i.symm ∘ v)).mpr (hp (i.symm ∘ v))


theorem specialUnitaryMatrixTransport : SpecialUnitaryMatrixTransport.{u} := by
  intro F E _ _ e A _ _ _ hstar
  letI := scalarStructure e
  obtain ⟨i, hi, _, _⟩ := coefficientAlgebraTransport e A hstar
  refine ⟨i, hi, ?_⟩
  letI := transportedInvolution i
  intro n _ _ M H
  exact and_congr (sesquilinearMatrixTransport i (transportedInvolution_map i) M H)
    (specialMatrixTransport i M)

theorem quaternionicMatrixTransport : QuaternionicMatrixTransport.{u} := by
  intro F E _ _ e A _ _ _ hstar
  letI := scalarStructure e
  obtain ⟨i, hi, hscalar, _⟩ := coefficientAlgebraTransport e A hstar
  refine ⟨i, hi, ?_⟩
  letI := transportedInvolution i
  intro n _ M H L
  exact and_congr (sesquilinearMatrixTransport i (transportedInvolution_map i) M H)
    (quaternionicQuadraticFormTransport e i hscalar (transportedInvolution_map i) M H L)

open CocharacterDynamics (cocharacterPoint unitCoordinates unitPoint)
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.RootGroups (AdditiveLine rootPoint)

set_option backward.isDefEq.respectTransparency false in
private theorem mapPoints_rootPoint {G : GroupScheme F} {A : AdditiveLine F}
    (x : A.group ⟶ G) {R S : TestAlgebra F} (f : R ⟶ S) (a : R) :
    mapPoints f (rootPoint x R a) = rootPoint x S (f.hom a) := by
  unfold rootPoint mapPoints
  rw [← Category.assoc, ← Functor.map_comp]
  congr 2
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext
  change f.hom (Polynomial.aeval a Polynomial.X) = Polynomial.aeval (f.hom a) Polynomial.X
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem mapPoints_cocharacterPoint {G : GroupScheme F} (c : Cocharacter G)
    {R S : TestAlgebra F} (f : R ⟶ S) (s : Rˣ) :
    mapPoints f (cocharacterPoint c R s) =
      cocharacterPoint c S (Units.map f.hom.toMonoidHom s) := by
  change (testSpec F).map f.op ≫
      (testSpec F).map (CommAlgCat.ofHom (unitCoordinates R s)).op ≫ c.hom.hom =
    (testSpec F).map (CommAlgCat.ofHom
      (unitCoordinates S (Units.map f.hom.toMonoidHom s))).op ≫ c.hom.hom
  rw [← Category.assoc, ← Functor.map_comp]
  congr 2
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply MonoidAlgebra.algHom_ext
  · intro m
    change f.hom (unitCoordinates R s (MonoidAlgebra.single m 1)) =
      unitCoordinates S (Units.map f.hom.toMonoidHom s) (MonoidAlgebra.single m 1)
    simp only [unitCoordinates, MonoidAlgebra.lift_single, one_smul, MonoidHom.coe_comp,
      Function.comp_apply, Units.coeHom_apply, MulEquiv.coe_toMonoidHom]
    let n : ℤ := (MulEquiv.ulift m).toAdd
    change f.hom (↑(s ^ n) : R) = (↑((Units.map f.hom.toMonoidHom s) ^ n) : S)
    exact congrArg (fun u : Sˣ ↦ (u : S)) (map_zpow (Units.map f.hom.toMonoidHom) s n)
  · exact Subsingleton.elim _ _

private theorem fieldTestIso_points_injective (e : F ≃+* E) (X : SchemeOver F) :
    letI := scalarStructure e
    Function.Injective (fun p : Points X ((restrictTestAlgebra F E).obj (CommAlgCat.of E E)) ↦
      mapPoints (fieldTestIso e).hom p) := by
  letI := scalarStructure e
  let a := fieldTestIso e
  haveI : IsIso ((testSpec F).map a.hom.op) := (testSpec F).map_isIso a.hom.op
  intro p q h
  exact (cancel_epi ((testSpec F).map a.hom.op)).mp h

set_option backward.isDefEq.respectTransparency false in
theorem rootParameterTransport : RootParameterTransport.{u} := by
  intro F E _ _ e G A x
  letI := scalarStructure e
  intro p a
  let R := CommAlgCat.of E E
  let S := (restrictTestAlgebra F E).obj R
  let f := (fieldTestIso e).hom
  have h := mapPoints_rootPoint x f (show S from e a)
  change mapPoints f (rootPoint x S (e a)) = rootPoint x (CommAlgCat.of F F) (e.symm (e a)) at h
  rw [e.symm_apply_apply] at h
  change _ ↔ mapPoints f (baseChangePoint F E G.X R p) = _
  rw [← h, (fieldTestIso_points_injective e G.X).eq_iff]

set_option backward.isDefEq.respectTransparency false in
theorem cocharacterTransport : CocharacterTransport.{u} := by
  intro F E _ _ e G c
  letI := scalarStructure e
  intro p s
  let R := CommAlgCat.of E E
  let S := (restrictTestAlgebra F E).obj R
  let f := (fieldTestIso e).hom
  let t : Sˣ := Units.map e.toMonoidHom s
  have ht : Units.map f.hom.toMonoidHom t = s := by
    apply Units.ext
    exact e.symm_apply_apply (s : F)
  have h := mapPoints_cocharacterPoint c f t
  rw [ht] at h
  change _ ↔ mapPoints f (baseChangePoint F E G.X R p) = _
  rw [← h, (fieldTestIso_points_injective e G.X).eq_iff]

set_option backward.isDefEq.respectTransparency false in
private def additiveParameterEquiv (A : AdditiveLine F) (R : TestAlgebra F) :
    R ≃ GroupPoints A.group R := by
  let P := CommAlgCat.of F (Polynomial F)
  let a : (Polynomial F →ₐ[F] R) ≃ (P ⟶ R) :=
    ⟨CommAlgCat.ofHom, CommAlgCat.Hom.hom, fun _ ↦ rfl, fun _ ↦ rfl⟩
  let eval : R ≃ (Polynomial F →ₐ[F] R) := Polynomial.aevalEquiv F R
  let b : (P ⟶ R) ≃ (op R ⟶ op P) := Quiver.Hom.opEquiv
  exact (eval.trans a).trans (b.trans
    ((AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of F)).homEquiv))

private theorem additiveParameterEquiv_apply (A : AdditiveLine F) (R : TestAlgebra F) (a : R) :
    additiveParameterEquiv A R a = rootPoint (𝟙 A.group) R a := by
  change (testSpec F).map (CommAlgCat.ofHom (Polynomial.aeval a : Polynomial F →ₐ[F] R)).op =
    (testSpec F).map (CommAlgCat.ofHom (Polynomial.aeval a : Polynomial F →ₐ[F] R)).op ≫ 𝟙 _
  rw [Category.comp_id]

private theorem additiveIdentityPoint_add (A : AdditiveLine F) (R : TestAlgebra F) (a b : R) :
    rootPoint (𝟙 A.group) R (a + b) =
      rootPoint (𝟙 A.group) R a * rootPoint (𝟙 A.group) R b := by
  letI := A.operations.hopf
  let f := Spec.mapMulEquiv (R := F) (S := Polynomial F) (T := R)
  simp only [rootPoint]
  change f (WithConv.toConv (Polynomial.aeval (a + b))) =
    f (WithConv.toConv (Polynomial.aeval a)) * f (WithConv.toConv (Polynomial.aeval b))
  rw [← map_mul]
  apply congrArg f
  apply WithConv.ofConv_injective
  apply Polynomial.algHom_ext
  rw [AlgHom.convMul_apply, Polynomial.aeval_X]
  change a + b = Algebra.TensorProduct.lift (Polynomial.aeval a) (Polynomial.aeval b)
    (fun _ _ ↦ Commute.all _ _) (A.operations.delta Polynomial.X)
  rw [A.comultiplication]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem rootMorphismTransport : RootMorphismTransport.{u} := by
  intro F E _ _ e G A x
  letI := scalarStructure e
  let g (R : TestAlgebra E) := baseChangePointGroupEquiv E A.group R
  let c (R : TestAlgebra E) : R ≃ GroupPoints ((groupBaseChange F E).obj A.group) R :=
    (additiveParameterEquiv A ((restrictTestAlgebra F E).obj R)).trans (g R).symm.toEquiv
  have hc (R : TestAlgebra E) (a : R) :
      baseChangePoint F E A.group.X R (c R a) =
        rootPoint (𝟙 A.group) ((restrictTestAlgebra F E).obj R) a := by
    change g R ((g R).symm (additiveParameterEquiv A _ a)) = _
    rw [MulEquiv.apply_symm_apply, additiveParameterEquiv_apply]
  refine ⟨c, ?_, ?_, ?_⟩
  · intro R a
    refine ⟨hc R a, ?_⟩
    change baseChangePoint F E G.X R (c R a ≫ (baseChange F E).map x.hom.hom) = _
    rw [baseChangePointsSchemeNaturality F E x.hom.hom R (c R a), hc R a]
    change (_ ≫ 𝟙 _) ≫ x.hom.hom = _
    rw [Category.comp_id]
    rfl
  · intro R S f a
    apply (baseChangePoints F E A.group.X S).injective
    rw [baseChangePointsNaturality F E A.group.X f (c R a), hc R a, hc S (f.hom a),
      mapPoints_rootPoint]
    rfl
  · intro R a b
    apply (g R).injective
    rw [map_mul]
    change baseChangePoint F E A.group.X R (c R (a + b)) =
      baseChangePoint F E A.group.X R (c R a) * baseChangePoint F E A.group.X R (c R b)
    rw [hc R (a + b), hc R a, hc R b]
    exact additiveIdentityPoint_add A ((restrictTestAlgebra F E).obj R) a b

open private gm_baseChange from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

set_option backward.isDefEq.respectTransparency false in
theorem cocharacterMorphismTransport : CocharacterMorphismTransport.{u} := by
  intro F E _ _ e G c
  letI := scalarStructure e
  obtain ⟨i, hi⟩ := gm_baseChange F E
  refine ⟨i, hi, ?_⟩
  intro c' s
  apply (cocharacterTransport e c _ s).mp
  let R := CommAlgCat.of E E
  let t : Rˣ := Units.map e.toMonoidHom s
  change baseChangePoint F E G.X R
    ((unitPoint R t ≫ i.hom.hom.hom) ≫ ((groupBaseChange F E).map c).hom.hom) = _
  let M := specGroup (groupAlgebra F IntegerCharacters)
  let u : Points ((baseChange F E).obj M.X) R := unitPoint R t ≫ i.hom.hom.hom
  have hu : baseChangePoint F E M.X R u = unitPoint ((restrictTestAlgebra F E).obj R) t :=
    hi R t
  change baseChangePoint F E G.X R (u ≫ (baseChange F E).map c.hom.hom) = _
  rw [baseChangePointsSchemeNaturality F E c.hom.hom R u, hu]
  rfl

section Clifford

open CliffordAlgebra

variable {R S : Type u} [CommRing R] [CommRing S]

variable {V W : Type u} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W]
variable (e : R ≃+* S)
variable (Q : QuadraticForm R V) (P : QuadraticForm S W)

private def cliffordAlgMap (g : V →ₛₗ[e.toRingHom] W) (h : ∀ v, P (g v) = e (Q v)) :
    letI := Algebra.compHom (CliffordAlgebra P) e.toRingHom
    CliffordAlgebra Q →ₐ[R] CliffordAlgebra P := by
  letI : Algebra R (CliffordAlgebra P) :=
    Algebra.compHom (CliffordAlgebra P) e.toRingHom
  let f : V →ₗ[R] CliffordAlgebra P :=
    { toFun := fun v ↦ CliffordAlgebra.ι P (g v)
      map_add' := fun a b ↦ by rw [map_add g, map_add (CliffordAlgebra.ι P)]
      map_smul' := fun r v ↦ by
        change CliffordAlgebra.ι P (g (r • v)) = r • (CliffordAlgebra.ι P (g v))
        rw [map_smulₛₗ, map_smul]
        rfl }
  exact CliffordAlgebra.lift Q ⟨f, fun v ↦ by
    change CliffordAlgebra.ι P (g v) * CliffordAlgebra.ι P (g v) = _
    rw [ι_sq_scalar, h]
    rfl⟩

private abbrev cliffordMap (g : V →ₛₗ[e.toRingHom] W) (h : ∀ v, P (g v) = e (Q v)) :
    CliffordAlgebra Q →+* CliffordAlgebra P := by
  letI : Algebra R (CliffordAlgebra P) := Algebra.compHom (CliffordAlgebra P) e.toRingHom
  exact (cliffordAlgMap e Q P g h).toRingHom

private theorem cliffordMap_ι (g : V →ₛₗ[e.toRingHom] W)
    (h : ∀ v, P (g v) = e (Q v)) (v : V) :
    cliffordMap e Q P g h (CliffordAlgebra.ι Q v) = CliffordAlgebra.ι P (g v) := by
  letI : Algebra R (CliffordAlgebra P) := Algebra.compHom (CliffordAlgebra P) e.toRingHom
  unfold cliffordMap cliffordAlgMap
  exact CliffordAlgebra.lift_ι_apply _ _ _

private theorem cliffordMap_scalar (g : V →ₛₗ[e.toRingHom] W)
    (h : ∀ v, P (g v) = e (Q v)) (r : R) :
    cliffordMap e Q P g h (algebraMap R (CliffordAlgebra Q) r) =
      algebraMap S (CliffordAlgebra P) (e r) := by
  letI : Algebra R (CliffordAlgebra P) := Algebra.compHom (CliffordAlgebra P) e.toRingHom
  change (cliffordAlgMap e Q P g h) (algebraMap R (CliffordAlgebra Q) r) =
    algebraMap R (CliffordAlgebra P) r
  exact (cliffordAlgMap e Q P g h).commutes r

private theorem map_mem_even (f : CliffordAlgebra Q →+* CliffordAlgebra P)
    (g : V → W)
    (hs : ∀ r : R, ∃ t : S, f (algebraMap R (CliffordAlgebra Q) r) = algebraMap S _ t)
    (hg : ∀ v, f (CliffordAlgebra.ι Q v) = CliffordAlgebra.ι P (g v))
    {x : CliffordAlgebra Q} (hx : x ∈ even Q) : f x ∈ even P := by
  change x ∈ evenOdd Q 0 at hx
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
    obtain ⟨t, ht⟩ := hs r
    rw [ht]
    exact (even P).algebraMap_mem t
  | add x y hx hy hx' hy' => rw [map_add]; exact (even P).add_mem hx' hy'
  | ι_mul_ι_mul a b y hy hy' =>
    rw [map_mul, map_mul, hg, hg]
    exact (even P).mul_mem (ι_mul_ι_mem_evenOdd_zero P _ _) hy'

theorem cliffordTransport : CliffordTransport.{u} := by
  intro R S V W _ _ _ _ _ _ e
  letI := RingHomInvPair.of_ringEquiv e
  letI := RingHomInvPair.symm (↑e : R →+* S) (↑e.symm : S →+* R)
  intro g Q P h
  let f := cliffordMap e Q P g.toLinearMap h
  have hg (w : W) : Q (g.symm w) = e.symm (P w) := by
    apply e.injective
    rw [e.apply_symm_apply, ← h, g.apply_symm_apply]
  let f' := cliffordMap e.symm P Q g.symm.toLinearMap hg
  have hf (r : R) : f (algebraMap R (CliffordAlgebra Q) r) =
      algebraMap S (CliffordAlgebra P) (e r) := cliffordMap_scalar e Q P _ h r
  have hf' (r : S) : f' (algebraMap S (CliffordAlgebra P) r) =
      algebraMap R (CliffordAlgebra Q) (e.symm r) := cliffordMap_scalar e.symm P Q _ hg r
  have hι (v : V) : f (CliffordAlgebra.ι Q v) = CliffordAlgebra.ι P (g v) :=
    cliffordMap_ι e Q P _ h v
  have hι' (w : W) : f' (CliffordAlgebra.ι P w) = CliffordAlgebra.ι Q (g.symm w) :=
    cliffordMap_ι e.symm P Q _ hg w
  have h₁ : f'.comp f = RingHom.id _ := by
    ext x : 1
    change f' (f x) = x
    induction x using CliffordAlgebra.induction with
    | algebraMap r => simp only [hf, hf', e.symm_apply_apply]
    | «ι» v => simp only [hι, hι', g.symm_apply_apply]
    | mul x y hx hy => simp only [map_mul, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h₂ : f.comp f' = RingHom.id _ := by
    ext x : 1
    change f (f' x) = x
    induction x using CliffordAlgebra.induction with
    | algebraMap r => simp only [hf, hf', e.apply_symm_apply]
    | «ι» v => simp only [hι, hι', g.apply_symm_apply]
    | mul x y hx hy => simp only [map_mul, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  let b := RingEquiv.ofRingHom f f' h₂ h₁
  have hrev (x : CliffordAlgebra Q) : f (reverse x) = reverse (f x) := by
    induction x using CliffordAlgebra.induction with
    | algebraMap r => simp only [reverse.commutes, hf]
    | «ι» v => simp only [reverse_ι, hι]
    | mul x y hx hy => simp only [reverse.map_mul, map_mul, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hinv (x : CliffordAlgebra Q) : f (involute x) = involute (f x) := by
    induction x using CliffordAlgebra.induction with
    | algebraMap r => simp only [AlgHom.commutes, hf]
    | «ι» v => simp only [involute_ι, map_neg, hι]
    | mul x y hx hy => simp only [map_mul, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  have heven (x : CliffordAlgebra Q) : b x ∈ even P ↔ x ∈ even Q := by
    constructor
    · intro hx
      have hy := map_mem_even P Q f' g.symm (fun r ↦ ⟨e.symm r, hf' r⟩) hι' hx
      change b.symm (b x) ∈ even Q at hy
      simpa only [b.symm_apply_apply] using hy
    · exact map_mem_even Q P f g (fun r ↦ ⟨e r, hf r⟩) hι
  have hvector (z : CliffordAlgebra Q) :
      b z ∈ Set.range (CliffordAlgebra.ι P) ↔ z ∈ Set.range (CliffordAlgebra.ι Q) := by
    constructor
    · rintro ⟨w, hw⟩
      obtain ⟨v, rfl⟩ := g.surjective w
      exact ⟨v, b.injective ((hι v).trans hw)⟩
    · rintro ⟨v, rfl⟩
      exact ⟨g v, (hι v).symm⟩
  refine ⟨b, hf, hι, hrev, hinv, heven, ?_⟩
  intro x
  have hnorm : reverse (b (x : CliffordAlgebra Q)) * b (x : CliffordAlgebra Q) = 1 ↔
      reverse (x : CliffordAlgebra Q) * (x : CliffordAlgebra Q) = 1 := by
    have h : reverse (b (x : CliffordAlgebra Q)) = b (reverse (x : CliffordAlgebra Q)) :=
      (hrev _).symm
    rw [h, ← map_mul, ← map_one b, b.injective.eq_iff]
  unfold IsSpinPoint
  change (b (x : CliffordAlgebra Q) ∈ even P ∧
    reverse (b (x : CliffordAlgebra Q)) * b (x : CliffordAlgebra Q) = 1 ∧ _) ↔ _
  rw [heven, hnorm]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  change (∀ z : CliffordAlgebra P, z ∈ Set.range (CliffordAlgebra.ι P) ↔
    b (x : CliffordAlgebra Q) * z * b (↑x⁻¹ : CliffordAlgebra Q) ∈
      Set.range (CliffordAlgebra.ι P)) ↔ _
  have hc (z : CliffordAlgebra Q) :
      b ((x : CliffordAlgebra Q) * z * (↑x⁻¹ : CliffordAlgebra Q)) =
        b (x : CliffordAlgebra Q) * b z * b (↑x⁻¹ : CliffordAlgebra Q) := by
    rw [map_mul, map_mul]
  constructor
  · intro h' z
    simpa only [← hc, hvector] using h' (b z)
  · intro h' z
    obtain ⟨w, rfl⟩ := b.surjective z
    rw [← hc, hvector, hvector]
    exact h' w


variable {V W : Type u} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W]

private def scalarExtensionLinearEquiv (e : R ≃+* S) (V : Type u) [AddCommGroup V] [Module R V] :
    letI := scalarStructure e
    letI := RingHomInvPair.of_ringEquiv e
    letI := RingHomInvPair.symm (↑e : R →+* S) (↑e.symm : S →+* R)
    V ≃ₛₗ[(↑e : R →+* S)] (S ⊗[R] V) := by
  letI := scalarStructure e
  letI := RingHomInvPair.of_ringEquiv e
  letI := RingHomInvPair.symm (↑e : R →+* S) (↑e.symm : S →+* R)
  let f : V →ₛₗ[(↑e : R →+* S)] S ⊗[R] V :=
    { toFun := fun v ↦ (1 : S) ⊗ₜ[R] v
      map_add' := fun a b ↦ TensorProduct.tmul_add _ _ _
      map_smul' := fun r v ↦ by
        change (1 : S) ⊗ₜ[R] (r • v) = e r • ((1 : S) ⊗ₜ[R] v)
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul' (e r)]
        rfl }
  let b : R ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl
  let p := (TensorProduct.lid R V).symm.trans
    (TensorProduct.congr b.toLinearEquiv (LinearEquiv.refl R V))
  have hp : (p : V → S ⊗[R] V) = f := by
    funext v
    change TensorProduct.congr b.toLinearEquiv (LinearEquiv.refl R V)
      ((TensorProduct.lid R V).symm v) = _
    rw [TensorProduct.lid_symm_apply, TensorProduct.congr_tmul]
    change b 1 ⊗ₜ[R] v = 1 ⊗ₜ[R] v
    rw [map_one]
  exact LinearEquiv.ofBijective f (hp ▸ p.bijective)

private def transportBilinear (e : R ≃+* S)
    [RingHomInvPair (↑e : R →+* S) (↑e.symm : S →+* R)]
    [RingHomInvPair (↑e.symm : S →+* R) (↑e : R →+* S)]
    (g : V ≃ₛₗ[(↑e : R →+* S)] W) (b : LinearMap.BilinForm R V) : LinearMap.BilinForm S W where
  toFun w :=
    { toFun := fun z ↦ e (b (g.symm w) (g.symm z))
      map_add' := fun x y ↦ by rw [map_add, map_add, map_add]
      map_smul' := fun r z ↦ by
        have hg : g.symm (r • z) = e.symm r • g.symm z := g.symm.map_smulₛₗ r z
        rw [hg, LinearMap.map_smul]
        simp only [smul_eq_mul, map_mul, e.apply_symm_apply, RingHom.id_apply] }
  map_add' x y := by
    ext z
    change e (b (g.symm (x + y)) (g.symm z)) =
      e (b (g.symm x) (g.symm z)) + e (b (g.symm y) (g.symm z))
    rw [map_add, map_add, LinearMap.add_apply, map_add]
  map_smul' r x := by
    ext z
    change e (b (g.symm (r • x)) (g.symm z)) = r • e (b (g.symm x) (g.symm z))
    have hg : g.symm (r • x) = e.symm r • g.symm x := g.symm.map_smulₛₗ r x
    rw [hg, LinearMap.map_smul, LinearMap.smul_apply]
    simp only [smul_eq_mul, map_mul, e.apply_symm_apply]

private def transportQuadraticForm (e : R ≃+* S)
    [RingHomInvPair (↑e : R →+* S) (↑e.symm : S →+* R)]
    [RingHomInvPair (↑e.symm : S →+* R) (↑e : R →+* S)]
    (g : V ≃ₛₗ[(↑e : R →+* S)] W) (Q : QuadraticForm R V) : QuadraticForm S W where
  toFun w := e (Q (g.symm w))
  toFun_smul r w := by
    have hg : g.symm (r • w) = e.symm r • g.symm w := g.symm.map_smulₛₗ r w
    rw [hg, Q.map_smul]
    simp only [smul_eq_mul, map_mul, e.apply_symm_apply]
  exists_companion' := by
    obtain ⟨b, hb⟩ := Q.exists_companion
    refine ⟨transportBilinear e g b, fun x y ↦ ?_⟩
    change e (Q (g.symm (x + y))) = e (Q (g.symm x)) + e (Q (g.symm y)) +
      e (b (g.symm x) (g.symm y))
    rw [map_add g.symm, hb, map_add, map_add]


theorem cliffordBaseChangeTransport : CliffordBaseChangeTransport.{u} := by
  intro R S V _ _ _ _ e Q
  letI := scalarStructure e
  letI := RingHomInvPair.of_ringEquiv e
  letI := RingHomInvPair.symm (↑e : R →+* S) (↑e.symm : S →+* R)
  let g := scalarExtensionLinearEquiv e V
  let P := transportQuadraticForm e g Q
  have h (v : V) : P (g v) = e (Q v) := by
    change e (Q (g.symm (g v))) = e (Q v)
    rw [g.symm_apply_apply]
  exact ⟨P, h, cliffordTransport e g Q P h⟩

end Clifford

section EvenClifford

open CliffordAlgebra

private theorem evenCliffordRingHom_ext {R V A : Type u} [CommRing R] [AddCommGroup V]
    [Module R V] [Semiring A] {Q : QuadraticForm R V} {f g : even Q →+* A}
    (hs : ∀ r, f (algebraMap R (even Q) r) = g (algebraMap R (even Q) r))
    (hp : ∀ v w, f ((even.ι Q).bilin v w) = g ((even.ι Q).bilin v w)) : f = g := by
  apply RingHom.ext
  rintro ⟨x, hx⟩
  change x ∈ evenOdd Q 0 at hx
  induction x, hx using even_induction with
  | algebraMap r => exact hs r
  | add x y hx hy ihx ihy =>
    change f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add, map_add, ihx, ihy]
  | ι_mul_ι_mul v w x hx ih =>
    change f ((even.ι Q).bilin v w * ⟨x, hx⟩) = g ((even.ι Q).bilin v w * ⟨x, hx⟩)
    rw [map_mul, map_mul, hp, ih]

private theorem evenCliffordEquiv_scalar {R S V W : Type u} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W]
    {e : R ≃+* S} {g : V → W} {Q : QuadraticForm R V} {P : QuadraticForm S W}
    {b : CliffordAlgebra Q ≃+* CliffordAlgebra P} (hb : IsCliffordTransport e g Q P b) (r : R) :
    evenCliffordEquiv b hb.2.2.2.2.1 (algebraMap R (even Q) r) = algebraMap S (even P) (e r) :=
  Subtype.ext (hb.1 r)

private theorem evenCliffordEquiv_pair {R S V W : Type u} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W]
    {e : R ≃+* S} {g : V → W} {Q : QuadraticForm R V} {P : QuadraticForm S W}
    {b : CliffordAlgebra Q ≃+* CliffordAlgebra P} (hb : IsCliffordTransport e g Q P b) (v w : V) :
    evenCliffordEquiv b hb.2.2.2.2.1 ((even.ι Q).bilin v w) = (even.ι P).bilin (g v) (g w) := by
  apply Subtype.ext
  change b (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w) =
    CliffordAlgebra.ι P (g v) * CliffordAlgebra.ι P (g w)
  rw [map_mul, hb.2.1, hb.2.1]

theorem cliffordDescentTransport : CliffordDescentTransport.{u} := by
  intro R S V W _ _ _ _ _ _ e g Q P b hb d σ s c a ha σ' s' c'
  have hs (r : R) : d (algebraMap R (even Q) r) = algebraMap S (even P) (e r) :=
    evenCliffordEquiv_scalar hb r
  have hp (v w : V) : d ((even.ι Q).bilin v w) = (even.ι P).bilin (g v) (g w) :=
    evenCliffordEquiv_pair hb v w
  let a₀ := d.symm.trans (a.trans d)
  have hs' (r : S) : a₀ (algebraMap S (even P) r) = algebraMap S (even P) (σ' r) := by
    obtain ⟨r, rfl⟩ := e.surjective r
    rw [← hs r]
    change d (a (d.symm (d (algebraMap R (even Q) r)))) =
      algebraMap S (even P) (e (σ (e.symm (e r))))
    rw [d.symm_apply_apply, ha.1, hs, e.symm_apply_apply]
  have hp' (v w : W) : a₀ ((even.ι P).bilin v w) =
      algebraMap S (even P) (↑c'⁻¹ : S) * (even.ι P).bilin (s' v) (s' w) := by
    obtain ⟨v, rfl⟩ := g.surjective v
    obtain ⟨w, rfl⟩ := g.surjective w
    rw [← hp v w]
    change d (a (d.symm (d ((even.ι Q).bilin v w)))) = _
    rw [d.symm_apply_apply, ha.2, map_mul, hs, hp]
    simp only [s', Function.comp_apply, g.symm_apply_apply, c', ← map_inv, Units.coe_map]
    rfl
  refine ⟨⟨hs', hp'⟩, fun a' ha' x ↦ ?_⟩
  have h : a'.toRingHom = a₀.toRingHom :=
    evenCliffordRingHom_ext (fun r ↦ (ha'.1 r).trans (hs' r).symm)
      (fun v w ↦ (ha'.2 v w).trans (hp' v w).symm)
  change a'.toRingHom (d x) = _
  rw [h]
  change d (a (d.symm (d x))) = d (a x)
  rw [d.symm_apply_apply]

theorem cliffordProjectionTransport : CliffordProjectionTransport.{u} := by
  intro R S V W _ _ _ _ _ _ e g Q P b hb d
  constructor
  · intro x T
    have hnorm : reverse (b x.val.val) * b x.val.val = 1 ↔
        reverse (x.val.val : CliffordAlgebra Q) * x.val.val = 1 := by
      rw [← hb.2.2.1, ← map_mul, ← map_one b, b.injective.eq_iff]
    have hcover (v : V) :
        b x.val.val * CliffordAlgebra.ι P (g v) = CliffordAlgebra.ι P (g (T v)) * b x.val.val ↔
          x.val.val * CliffordAlgebra.ι Q v = CliffordAlgebra.ι Q (T v) * x.val.val := by
      rw [← hb.2.1, ← hb.2.1, ← map_mul, ← map_mul, b.injective.eq_iff]
    change ((reverse (b x.val.val) * b x.val.val = 1) ∧
      ∀ w, b x.val.val * CliffordAlgebra.ι P w =
        CliffordAlgebra.ι P ((g ∘ T ∘ g.symm) w) * b x.val.val) ↔ (_ ∧ _)
    rw [hnorm]
    apply and_congr_right
    intro _
    constructor
    · intro h v
      apply (hcover v).1
      simpa only [Function.comp_apply, g.symm_apply_apply] using h (g v)
    · intro h w
      obtain ⟨v, rfl⟩ := g.surjective w
      simpa only [Function.comp_apply, g.symm_apply_apply] using (hcover v).2 (h v)
  · intro r
    apply Units.ext
    exact evenCliffordEquiv_scalar hb (r : R)

end EvenClifford

section QuaternionicSpin

open CliffordAlgebra

theorem quaternionicSpinChartTransport : QuaternionicSpinChartTransport.{u} := by
  intro R A B S T n m J _ _ _ _ _ _ _ _ _ _ _ _ _ i j D
  let e := j.toRingEquiv
  let g₀ := Equiv.piCongrRight fun _ : m ↦ j.toEquiv
  letI := RingHomInvPair.of_ringEquiv e
  letI := RingHomInvPair.symm (↑e : S →+* T) (↑e.symm : T →+* S)
  let g : (m → S) ≃ₛₗ[(↑e : S →+* T)] (m → T) :=
    { g₀ with
      map_add' := fun v w ↦ funext fun k ↦ map_add e (v k) (w k)
      map_smul' := fun s v ↦ funext fun k ↦ map_mul e s (v k) }
  let P := transportQuadraticForm e g D.form
  have hform (v : m → S) : P (g v) = e (D.form v) := by
    change e (D.form (g.symm (g v))) = e (D.form v)
    rw [g.symm_apply_apply]
  obtain ⟨b, hb⟩ := cliffordTransport e g D.form P hform
  let d := evenCliffordEquiv b hb.2.2.2.2.1
  let undo := Algebra.TensorProduct.congr j.symm (i.mapMatrix (m := n)).symm
  let changeSplit : T ⊗[R] Matrix n n B ≃+* Matrix m m T :=
    (undo.toRingEquiv.trans D.splitting.toRingEquiv).trans e.mapMatrix
  have hsplit (s : S) (M : Matrix n n A) :
      changeSplit (j s ⊗ₜ[R] M.map i) = (D.splitting (s ⊗ₜ[R] M)).map j := by
    change (D.splitting (undo (j s ⊗ₜ[R] i.mapMatrix M))).map j = _
    simp only [undo, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      AlgEquiv.coe_toAlgHom, j.symm_apply_apply, (i.mapMatrix (m := n)).symm_apply_apply]
  let splitting' : T ⊗[R] Matrix n n B ≃ₐ[T] Matrix m m T :=
    AlgEquiv.ofRingEquiv (f := changeSplit) (fun t ↦ by
      obtain ⟨s, rfl⟩ := j.surjective t
      change changeSplit (j s ⊗ₜ[R] (1 : Matrix n n B)) = algebraMap T (Matrix m m T) (j s)
      have h1 : (1 : Matrix n n A).map i = 1 := (i.mapMatrix (m := n)).map_one
      rw [← h1, hsplit]
      change (D.splitting (algebraMap S (S ⊗[R] Matrix n n A) s)).map j = _
      rw [AlgEquiv.commutes]
      ext k l
      by_cases h : k = l <;> simp [Matrix.algebraMap_matrix_apply, h])
  let action' (a : J) := d.symm.trans ((D.evenAction a).trans d)
  let D' : QuaternionicSpinChart R B T n m J :=
    { splitting := splitting'
      form := P
      scalarAction := fun a ↦ e.symm.trans ((D.scalarAction a).trans e)
      vectorAction := fun a ↦ g₀.symm.trans ((D.vectorAction a).trans g₀)
      multiplier := fun a ↦ Units.map e.toMonoidHom (D.multiplier a)
      vectorAction_add := fun a v w ↦ by
        change g (D.vectorAction a (g.symm (v + w))) =
          g (D.vectorAction a (g.symm v)) + g (D.vectorAction a (g.symm w))
        rw [map_add g.symm, D.vectorAction_add, map_add g]
      vectorAction_smul := fun a t v ↦ by
        change g (D.vectorAction a (g.symm (t • v))) =
          e (D.scalarAction a (e.symm t)) • g (D.vectorAction a (g.symm v))
        rw [map_smulₛₗ g.symm, D.vectorAction_smul, map_smulₛₗ g]
        rfl
      similitude := fun a w ↦ by
        obtain ⟨v, rfl⟩ := g.surjective w
        change P (g (D.vectorAction a (g.symm (g v)))) =
          e (D.multiplier a : S) * e (D.scalarAction a (e.symm (P (g v))))
        rw [g.symm_apply_apply, hform, hform, e.symm_apply_apply, D.similitude, map_mul]
      evenAction := action'
      evenAction_formula := fun a ↦ (cliffordDescentTransport e g₀ D.form P b hb
        (D.scalarAction a) (D.vectorAction a) (D.multiplier a) (D.evenAction a)
        (D.evenAction_formula a)).1 }
  have haction (a : J) (x : even D.form) : D'.evenAction a (d x) = d (D.evenAction a x) := by
    change d (D.evenAction a (d.symm (d x))) = _
    rw [d.symm_apply_apply]
  have hmatrix (M : Matrix n n A) : D'.splitMatrix (M.map i) = (D.splitMatrix M).map j := by
    change changeSplit ((1 : T) ⊗ₜ[R] M.map i) = (D.splitting ((1 : S) ⊗ₜ[R] M)).map j
    simpa only [map_one j] using hsplit 1 M
  have hvec (M : Matrix n n A) (w : m → T) :
      D'.splitMatrix (M.map i) *ᵥ w = (g₀ ∘ (D.splitMatrix M *ᵥ ·) ∘ g₀.symm) w := by
    rw [hmatrix]
    obtain ⟨v, rfl⟩ := g₀.surjective w
    simp only [Function.comp_apply, g₀.symm_apply_apply]
    funext k
    exact (e.toRingHom.map_mulVec (D.splitMatrix M) v k).symm
  let p := (Units.mapEquiv (i.toRingEquiv.mapMatrix (m := n)).toMulEquiv).toEquiv.prodCongr
    (Units.mapEquiv d.toMulEquiv).toEquiv
  have hpoints (x : (Matrix n n A)ˣ × (even D.form)ˣ) :
      (∀ a, D'.evenAction a (d x.2.val) = d x.2.val) ↔
        (∀ a, D.evenAction a x.2.val = x.2.val) := by
    simp only [haction, d.injective.eq_iff]
  have hlift (x : (Matrix n n A)ˣ × (even D.form)ˣ) :
      IsCliffordLift D'.form (p x).2 (fun v ↦ D'.splitMatrix (p x).1.val *ᵥ v) ↔
        IsCliffordLift D.form x.2 (fun v ↦ D.splitMatrix x.1.val *ᵥ v) := by
    change IsCliffordLift P (Units.map d.toMonoidHom x.2)
      (fun v ↦ D'.splitMatrix (x.1.val.map i) *ᵥ v) ↔ _
    simp only [hvec]
    exact (cliffordProjectionTransport e g₀ D.form P b hb).1 _ _
  let f : D.CoverPoints ≃ D'.CoverPoints := p.subtypeEquiv
    (fun x ↦ (and_congr (hlift x) (hpoints x)).symm)
  refine ⟨⟨D', hsplit, hform, fun a ↦ ⟨rfl, rfl, rfl⟩, b, hb, haction, f,
    fun _ ↦ ⟨rfl, rfl⟩, ?_, ?_, ?_⟩⟩
  · intro M
    rw [hmatrix]
    exact (e.map_det _).symm
  · intro M
    rw [hmatrix]
    exact (AddMonoidHom.map_trace j _).symm
  · intro x z
    have hz : Units.map d.toMonoidHom
        (Units.map ((algebraMap S (even D.form)).comp (algebraMap R S)) z) =
        Units.map ((algebraMap T (even D'.form)).comp (algebraMap R T)) z := by
      apply Units.ext
      change d (algebraMap S (even D.form) (algebraMap R S (z : R))) =
        algebraMap T (even P) (algebraMap R T (z : R))
      rw [evenCliffordEquiv_scalar hb]
      exact congrArg (algebraMap T (even P)) (j.commutes (z : R))
    change Units.map d.toMonoidHom x.val.2 = _ ↔ _
    rw [← hz]
    exact (Units.mapEquiv d.toMulEquiv).injective.eq_iff

theorem quaternionicSpinDescentAlgebraTransport : QuaternionicSpinDescentAlgebraTransport.{u} := by
  intro R A B S T n m J _ _ _ _ _ _ _ _ _ _ _ _ _ i j D C
  let g := Equiv.piCongrRight fun _ : m ↦ j.toEquiv
  have hscalar (a : J) (s : S) : C.chart.scalarAction a (j s) = j (D.scalarAction a s) := by
    rw [(C.descent_eq a).1]
    change j (D.scalarAction a (j.symm (j s))) = _
    rw [j.symm_apply_apply]
  have hvector (a : J) (v : m → S) : C.chart.vectorAction a (g v) = g (D.vectorAction a v) := by
    rw [(C.descent_eq a).2.1]
    change g (D.vectorAction a (g.symm (g v))) = _
    rw [g.symm_apply_apply]
  have hmulVec (M : Matrix m m S) (v : m → S) : M.map j *ᵥ g v = g (M *ᵥ v) :=
    funext fun k ↦ (j.toRingHom.map_mulVec M v k).symm
  have hfixed (M : Matrix m m S) : C.chart.IsFixedSplitMatrix (M.map j) ↔ D.IsFixedSplitMatrix M := by
    have h (a : J) (v : m → S) :
        (C.chart.vectorAction a (M.map j *ᵥ g v) = M.map j *ᵥ C.chart.vectorAction a (g v)) ↔
        (D.vectorAction a (M *ᵥ v) = M *ᵥ D.vectorAction a v) := by
      rw [hmulVec, hvector, hvector, hmulVec, g.injective.eq_iff]
    constructor
    · intro H a v
      exact (h a v).mp (H a (g v))
    · intro H a w
      obtain ⟨v, rfl⟩ := g.surjective w
      exact (h a v).mpr (H a v)
  have hsplit (X : Matrix n n A) : C.chart.splitMatrix (X.map i) = (D.splitMatrix X).map j := by
    change C.chart.splitting ((1 : T) ⊗ₜ[R] X.map i) = (D.splitting ((1 : S) ⊗ₜ[R] X)).map j
    simpa only [map_one j] using C.splitting_eq 1 X
  have hrange (M : Matrix m m S) :
      M.map j ∈ Set.range C.chart.splitMatrix ↔ M ∈ Set.range D.splitMatrix := by
    constructor
    · rintro ⟨X, hx⟩
      obtain ⟨Y, rfl⟩ := (i.mapMatrix (m := n)).surjective X
      exact ⟨Y, j.toRingEquiv.mapMatrix.injective ((hsplit Y).symm.trans hx)⟩
    · rintro ⟨X, rfl⟩
      exact ⟨X.map i, hsplit X⟩
  have heven (x : even D.form) : C.evenEquiv x ∈ C.chart.fixedEven ↔ x ∈ D.fixedEven := by
    simp only [QuaternionicSpinChart.fixedEven, Subring.mem_iInf, RingHom.mem_eqLocus]
    change (∀ a, C.chart.evenAction a (C.evenEquiv x) = C.evenEquiv x) ↔
      (∀ a, D.evenAction a x = x)
    simp only [C.equivariant, C.evenEquiv.injective.eq_iff]
  refine ⟨?_, hfixed, ?_, ?_⟩
  · intro a M
    have h (v : m → S) :
        (C.chart.vectorAction a (g v) = M.map j *ᵥ (fun k ↦ C.chart.scalarAction a (g v k))) ↔
        (D.vectorAction a v = M *ᵥ (fun k ↦ D.scalarAction a (v k))) := by
      have hs : (fun k ↦ C.chart.scalarAction a (g v k)) = g (fun k ↦ D.scalarAction a (v k)) :=
        funext fun k ↦ hscalar a (v k)
      rw [hs, hvector, hmulVec, g.injective.eq_iff]
    constructor
    · intro H v
      exact (h v).mp (H (g v))
    · intro H w
      obtain ⟨v, rfl⟩ := g.surjective w
      exact (h v).mpr (H v)
  · constructor
    · intro H
      ext M
      rw [← hrange M, H]
      exact hfixed M
    · intro H
      ext N
      obtain ⟨M, rfl⟩ := (j.toRingEquiv.mapMatrix (m := m)).surjective N
      exact (hrange M).trans ((Set.ext_iff.mp H M).trans (hfixed M).symm)
  · let d : D.fixedEven ≃+* C.chart.fixedEven :=
      { toEquiv := C.evenEquiv.toEquiv.subtypeEquiv (fun x ↦ (heven x).symm)
        map_mul' := fun x y ↦ Subtype.ext (map_mul C.evenEquiv x.val y.val)
        map_add' := fun x y ↦ Subtype.ext (map_add C.evenEquiv x.val y.val) }
    exact ⟨d, fun _ ↦ rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem quaternionicSpinGaloisActionTransport : QuaternionicSpinGaloisActionTransport.{u} := by
  intro F E B L n m J _ _ _ _ _ _ _ _ _ _ e G I π D
  letI := scalarStructure e
  intro R R₀ i j C a σ h
  let σ' : R ⊗[E] (E ⊗[F] L) →ₐ[E] R ⊗[E] (E ⊗[F] L) :=
    Algebra.TensorProduct.map (AlgHom.id E R)
      (Algebra.TensorProduct.map (AlgHom.id E E) σ.toAlgHom)
  have hcomm (x : R₀ ⊗[F] L) :
      C.chart.scalarAction a (j x) = j ((D.chart R₀).scalarAction a x) := by
    rw [(C.descent_eq a).1]
    change j ((D.chart R₀).scalarAction a (j.symm (j x))) = _
    rw [j.symm_apply_apply]
  have hcompare (x : R₀ ⊗[F] L) : j ((D.chart R₀).scalarAction a x) = σ' (j x) := by
    induction x using TensorProduct.inductionOn with
    | tmul r t =>
      rw [h r t]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  intro r s t
  obtain ⟨x, hx⟩ := j.surjective (r ⊗ₜ[E] (s ⊗ₜ[F] t))
  have h' := (hcomm x).trans (hcompare x)
  rw [hx] at h'
  exact h'

set_option backward.isDefEq.respectTransparency false in
theorem quaternionicSpinEquationTransport : QuaternionicSpinEquationTransport.{u} := by
  intro R A B S T n m J _ _ _ _ _ _ _ _ _ _ _ _ _ i j D C σ f σ'
  let g := Equiv.piCongrRight fun _ : m ↦ j.toEquiv
  have hform (v : m → S) : C.chart.form (g v) = j (D.form v) := C.form_eq v
  have hsum (v w : m → S) : g (v + w) = g v + g w :=
    funext fun k ↦ j.map_add (v k) (w k)
  have hpolar (v w : m → S) :
      C.chart.form.polarBilin (g v) (g w) = j (D.form.polarBilin v w) := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← hsum, hform, map_sub]
  have hsplit (M : Matrix n n A) :
      C.chart.splitMatrix (f M) = (D.splitMatrix M).map j := by
    change C.chart.splitting ((1 : T) ⊗ₜ[R] M.map i) =
      (D.splitting ((1 : S) ⊗ₜ[R] M)).map j
    simpa only [map_one j] using C.splitting_eq 1 M
  have hmulVec (M : Matrix n n A) (v : m → S) :
      C.chart.splitMatrix (f M) *ᵥ g v = g (D.splitMatrix M *ᵥ v) := by
    rw [hsplit]
    exact funext fun k ↦ (j.toRingHom.map_mulVec (D.splitMatrix M) v k).symm
  have hσ (M : Matrix n n A) : σ' (f M) = f (σ M) := by
    change f (σ (f.symm (f M))) = _
    rw [f.symm_apply_apply]
  have hadj (M : Matrix n n A) (v w : m → S) :
      (C.chart.form.polarBilin (C.chart.splitMatrix (f M) *ᵥ g v) (g w) =
        C.chart.form.polarBilin (g v) (C.chart.splitMatrix (σ' (f M)) *ᵥ g w)) ↔
      (D.form.polarBilin (D.splitMatrix M *ᵥ v) w =
        D.form.polarBilin v (D.splitMatrix (σ M) *ᵥ w)) := by
    rw [hσ, hmulVec, hmulVec, hpolar, hpolar, j.injective.eq_iff]
  have hsemi (ℓ : Matrix n n A) (v : m → S) :
      (C.chart.form (g v) =
        C.chart.form.polarBilin (g v) (C.chart.splitMatrix (f ℓ) *ᵥ g v)) ↔
      (D.form v = D.form.polarBilin v (D.splitMatrix ℓ *ᵥ v)) := by
    rw [hform, hmulVec, hpolar, j.injective.eq_iff]
  have htrace (ℓ X : Matrix n n A) :
      C.chart.semitrace (f ℓ) (f X) = j (D.semitrace ℓ X) := by
    unfold QuaternionicSpinChart.semitrace
    rw [← map_mul]
    exact C.reducedTrace_eq (ℓ * X)
  refine ⟨?_, ?_, htrace, ?_⟩
  · constructor
    · intro h M v w
      exact (hadj M v w).1 (h (f M) (g v) (g w))
    · intro h M v w
      obtain ⟨M, rfl⟩ := f.surjective M
      obtain ⟨v, rfl⟩ := g.surjective v
      obtain ⟨w, rfl⟩ := g.surjective w
      exact (hadj M v w).2 (h M v w)
  · intro ℓ
    constructor
    · intro h v
      exact (hsemi ℓ v).1 (h (g v))
    · intro h v
      obtain ⟨v, rfl⟩ := g.surjective v
      exact (hsemi ℓ v).2 (h v)
  · intro ℓ M
    unfold QuaternionicSpinChart.IsIsometry
    apply and_congr
    · change (σ' (f M.val) * f M.val = 1) ↔ (σ M.val * M.val = 1)
      rw [hσ, ← map_mul, ← map_one f, f.injective.eq_iff]
    · cases ℓ with
      | none =>
        change ((C.chart.splitMatrix (M.val.map i)).det = 1) ↔ (D.splitMatrix M.val).det = 1
        rw [C.reducedNorm_eq, ← map_one j, j.injective.eq_iff]
      | some ℓ =>
        change (∀ Y, σ' Y = Y → C.chart.semitrace (f ℓ) (f M.val * Y * f (M⁻¹).val) =
          C.chart.semitrace (f ℓ) Y) ↔ _
        have hconj (X : Matrix n n A) :
            C.chart.semitrace (f ℓ) (f M.val * f X * f (M⁻¹).val) =
                C.chart.semitrace (f ℓ) (f X) ↔
              D.semitrace ℓ (M.val * X * (M⁻¹).val) = D.semitrace ℓ X := by
          rw [← map_mul, ← map_mul, htrace, htrace, j.injective.eq_iff]
        constructor
        · intro h X hX
          exact (hconj X).1 (h (f X) ((hσ X).trans (congrArg f hX)))
        · intro h Y hY
          obtain ⟨X, rfl⟩ := f.surjective Y
          exact (hconj X).2 (h X (f.injective ((hσ X).symm.trans hY)))

private theorem commute_of_scalar_coordinates {H M R A : Type u} [Mul H] [Monoid M] [CommRing R]
    [Ring A] [Algebra R A] (c : H → M × Aˣ) (hc : Function.Injective c)
    (hmul : ∀ p q, c (p * q) = c p * c q) {p q : H} (hM : (c p).1 = 1) (s : Rˣ)
    (hA : (c p).2 = Units.map (algebraMap R A) s) : Commute p q := by
  change p * q = q * p
  apply hc
  rw [hmul p q, hmul q p]
  apply Prod.ext
  · change (c p).1 * (c q).1 = (c q).1 * (c p).1
    rw [hM, one_mul, mul_one]
  · change (c p).2 * (c q).2 = (c q).2 * (c p).2
    rw [hA]
    exact Units.ext (Algebra.commutes _ _)

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
theorem quaternionicSpinCoverTransport : QuaternionicSpinCoverTransport.{u} := by
  intro F E B L n m J _ _ _ _ _ _ _ _ _ _ e G I π D
  letI := scalarStructure e
  intro G' I' π' R R₀ i j
  obtain ⟨C⟩ := quaternionicSpinChartTransport (S := R₀ ⊗[F] L)
    (T := R ⊗[E] (E ⊗[F] L)) i j (D.chart R₀)
  let g : GroupPoints G' R ≃* GroupPoints G R₀ := baseChangePointGroupEquiv E G R
  let h : GroupPoints I' R ≃* GroupPoints I R₀ := baseChangePointGroupEquiv E I R
  let M := Units.mapEquiv (i.toRingEquiv.mapMatrix (m := n)).toMulEquiv
  let spin := (g.toEquiv.trans (D.spin R₀)).trans C.cover
  let coords := (M.prodCongr (Units.mapEquiv C.evenEquiv.toMulEquiv)).toMonoidHom
  have hcoords (p : GroupPoints G' R) : (spin p).val = coords (D.spin R₀ (g p)).val :=
    Prod.ext (C.cover_eq (D.spin R₀ (g p))).1 (C.cover_eq (D.spin R₀ (g p))).2
  have hmul (p q : GroupPoints G' R) : (spin (p * q)).val = (spin p).val * (spin q).val := by
    rw [hcoords (p * q), map_mul g, D.spin_mul, map_mul coords, hcoords p, hcoords q]
  let vector := M.toMonoidHom.comp ((D.vector R₀).comp h.toMonoidHom)
  have hv : Function.Injective vector := M.injective.comp ((D.vector_injective R₀).comp h.injective)
  have hπ₀ (p : GroupPoints G' R) : h (p ≫ π'.hom.hom) = g p ≫ π.hom.hom :=
    baseChangePointsSchemeNaturality F E π.hom.hom R p
  have hπ (p : GroupPoints G' R) : vector (p ≫ π'.hom.hom) = (spin p).val.1 := by
    calc
      _ = M (D.vector R₀ (g p ≫ π.hom.hom)) := congrArg (fun q ↦ M (D.vector R₀ q)) (hπ₀ p)
      _ = M (D.spin R₀ (g p)).val.1 := congrArg M (D.projection R₀ (g p))
      _ = _ := (C.cover_eq (D.spin R₀ (g p))).1.symm
  have hidentity (p : GroupPoints G' R) : (p ≫ π'.hom.hom : GroupPoints I' R) = 1 ↔
      (spin p).val.1 = 1 := by
    rw [← hπ p, ← map_one vector, hv.eq_iff]
  have hscalar (p : GroupPoints G' R) : (p ≫ π'.hom.hom : GroupPoints I' R) = 1 ↔
      ∃ z : rootsOfUnity 2 R, (spin p).val.2 =
        Units.map ((algebraMap (R ⊗[E] (E ⊗[F] L)) (even C.chart.form)).comp
          (algebraMap R (R ⊗[E] (E ⊗[F] L)))) z.val := by
    have hker : (p ≫ π'.hom.hom : GroupPoints I' R) = 1 ↔
        (g p ≫ π.hom.hom : GroupPoints I R₀) = 1 := by
      rw [← hπ₀ p, ← map_one h, h.injective.eq_iff]
    rw [hker, D.scalarKernel]
    exact exists_congr fun z ↦ (C.scalar_iff (D.spin R₀ (g p)) z.val).symm
  refine ⟨C, spin, fun _ ↦ rfl, hmul, vector, hv, fun _ ↦ rfl, hπ, hidentity, hscalar, ?_, ?_⟩
  · intro p q hp
    obtain ⟨z, hz⟩ := (hscalar p).mp hp
    let T := R ⊗[E] (E ⊗[F] L)
    let s : Tˣ := Units.map (algebraMap R T).toMonoidHom z.val
    have hs : (spin p).val.2 = Units.map (algebraMap T (even C.chart.form)) s :=
      hz.trans (Units.ext rfl)
    have hinj : Function.Injective (fun p : GroupPoints G' R ↦ (spin p).val) :=
      fun _ _ h ↦ spin.injective (Subtype.ext h)
    exact commute_of_scalar_coordinates _ hinj hmul ((hidentity p).mp hp) s hs
  · intro U x p
    change C.cover (D.spin R₀ (baseChangePoint F E G.X R (p ≫ (baseChange F E).map x.hom.hom))) = _
    rw [baseChangePointsSchemeNaturality F E x.hom.hom R p]

set_option backward.isDefEq.respectTransparency false in
theorem quaternionicSpinMarkedLiftTransport : QuaternionicSpinMarkedLiftTransport.{u} := by
  intro F E B L n m J _ _ _ _ _ _ _ _ _ _ e G I π D A x c
  letI := scalarStructure e
  intro K M
  obtain ⟨param, hparam, _, _⟩ := rootMorphismTransport e x
  obtain ⟨torus, htorus, hc⟩ := cocharacterMorphismTransport e c
  refine ⟨param, torus, ?_, hc, ?_⟩
  · intro a
    exact (rootParameterTransport e x _ a).1 (hparam (CommAlgCat.of E E) (e a)).2
  · intro R R₀ i j C spin
    let toCover (p : GroupPoints G R₀) := C.cover (D.spin R₀ p)
    refine ⟨fun a ↦ congrArg toCover (hparam R a).2, ?_⟩
    intro s
    let u : Points ((baseChange F E).obj M.X) R := unitPoint R s ≫ torus.hom.hom.hom
    have hu : baseChangePoint F E M.X R u = unitPoint R₀ s := htorus R s
    apply congrArg toCover
    change baseChangePoint F E G.X R (u ≫ (baseChange F E).map c.hom.hom) = _
    rw [baseChangePointsSchemeNaturality F E c.hom.hom R u, hu]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem testAlgebraRebase_natural {F E B : Type u} [Field F] [Field E]
    [Ring B] [Algebra F B] (e : F ≃+* E) :
    letI := scalarStructure e
    ∀ {R S : TestAlgebra E} (a : R ⟶ S) (x : (restrictTestAlgebra F E).obj R ⊗[F] B),
      testAlgebraRebase e S B (extendTestCoefficients ((restrictTestAlgebra F E).map a) B x) =
        extendTestCoefficients a (E ⊗[F] B) (testAlgebraRebase e R B x) := by
  letI := scalarStructure e
  intro R S a x
  induction x using TensorProduct.inductionOn with
  | tmul r b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
theorem quaternionicSpinCoverNaturality : QuaternionicSpinCoverNaturality.{u} := by
  intro F E B L n m J _ _ _ _ _ _ _ _ _ _ e G I π D
  letI := scalarStructure e
  intro R S a R₀ S₀ a₀ iR iS jR jS CR CS f g b
  have heven (x : even (D.chart R₀).form) :
      f (CR.evenEquiv x) = CS.evenEquiv (D.cliffordMap a₀ x) := by
    change CS.evenEquiv (D.cliffordMap a₀ (CR.evenEquiv.symm (CR.evenEquiv x))) = _
    rw [CR.evenEquiv.symm_apply_apply]
  have hunits (x : (even (D.chart R₀).form)ˣ) :
      Units.map CS.evenEquiv.toMonoidHom (Units.map (D.cliffordMap a₀) x) =
        Units.map f (Units.map CR.evenEquiv.toMonoidHom x) := Units.ext (heven x.val).symm
  let MR := Units.map (iR.toRingEquiv.mapMatrix (m := n)).toMonoidHom
  let MS := Units.map (iS.toRingEquiv.mapMatrix (m := n)).toMonoidHom
  let oldMatrixMap := Units.map ((extendTestCoefficients a₀ B).toRingHom.mapMatrix (m := n)).toMonoidHom
  let matrixMap := Units.map (b.toRingHom.mapMatrix (m := n)).toMonoidHom
  have hmatrix (M : (Matrix n n (R₀ ⊗[F] B))ˣ) :
      MS (oldMatrixMap M) = matrixMap (MR M) := by
    apply Units.ext
    ext k l
    exact testAlgebraRebase_natural e a (M.val k l)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨t, rfl⟩ := jR.surjective t
    have hr : CR.evenEquiv (algebraMap (R₀ ⊗[F] L) (even (D.chart R₀).form) t) =
        algebraMap (R ⊗[E] (E ⊗[F] L)) (even CR.chart.form) (jR t) :=
      evenCliffordEquiv_scalar CR.clifford_formula t
    have hs (s : S₀ ⊗[F] L) :
        CS.evenEquiv (algebraMap (S₀ ⊗[F] L) (even (D.chart S₀).form) s) =
          algebraMap (S ⊗[E] (E ⊗[F] L)) (even CS.chart.form) (jS s) :=
      evenCliffordEquiv_scalar CS.clifford_formula s
    rw [← hr, heven, D.cliffordMap_scalar, hs]
    exact congrArg (algebraMap _ (even CS.chart.form)) (testAlgebraRebase_natural e a t)
  · intro v w
    let v₀ := fun k ↦ jR.symm (v k)
    let w₀ := fun k ↦ jR.symm (w k)
    have hv : (fun k ↦ jR (v₀ k)) = v := funext fun k ↦ jR.apply_symm_apply (v k)
    have hw : (fun k ↦ jR (w₀ k)) = w := funext fun k ↦ jR.apply_symm_apply (w k)
    rw [← hv, ← hw, ← evenCliffordEquiv_pair CR.clifford_formula v₀ w₀, heven,
      D.cliffordMap_pair, evenCliffordEquiv_pair CS.clifford_formula]
    have hvec (x : m → R₀ ⊗[F] L) :
        (fun k ↦ jS ((extendTestCoefficients a₀ L ∘ x) k)) = g ∘ (fun k ↦ jR (x k)) :=
      funext fun k ↦ testAlgebraRebase_natural e a (x k)
    rw [hvec v₀, hvec w₀]
  · intro p
    let p₀ := baseChangePoint F E G.X R p
    let q₀ := mapPoints a₀ p₀
    have hp : baseChangePoint F E G.X S (mapPoints a p) = q₀ :=
      baseChangePointsNaturality F E G.X a p
    have hh := D.spin_natural a₀ p₀
    have hr := CR.cover_eq (D.spin R₀ p₀)
    have hs := CS.cover_eq (D.spin S₀ q₀)
    constructor
    · calc
        _ = (CS.cover (D.spin S₀ q₀)).val.1 := congrArg (fun x ↦ (CS.cover (D.spin S₀ x)).val.1) hp
        _ = MS (D.spin S₀ q₀).val.1 := hs.1
        _ = MS (oldMatrixMap (D.spin R₀ p₀).val.1) := congrArg MS hh.1
        _ = matrixMap (MR (D.spin R₀ p₀).val.1) := hmatrix _
        _ = _ := congrArg matrixMap hr.1.symm
    · calc
        _ = (CS.cover (D.spin S₀ q₀)).val.2 := congrArg (fun x ↦ (CS.cover (D.spin S₀ x)).val.2) hp
        _ = Units.map CS.evenEquiv.toMonoidHom (D.spin S₀ q₀).val.2 := hs.2
        _ = Units.map CS.evenEquiv.toMonoidHom (Units.map (D.cliffordMap a₀) (D.spin R₀ p₀).val.2) :=
          congrArg (Units.map CS.evenEquiv.toMonoidHom) hh.2
        _ = Units.map f (Units.map CR.evenEquiv.toMonoidHom (D.spin R₀ p₀).val.2) := hunits _
        _ = _ := by
          change Units.map f.toMonoidHom (Units.map CR.evenEquiv.toMonoidHom (D.spin R₀ p₀).val.2) =
            Units.map f.toMonoidHom (CR.cover (D.spin R₀ p₀)).val.2
          rw [hr.2]
  · intro p
    let p₀ := baseChangePoint F E I.X R p
    calc
      _ = MS (D.vector S₀ (mapPoints a₀ p₀)) :=
        congrArg (fun x ↦ MS (D.vector S₀ x)) (baseChangePointsNaturality F E I.X a p)
      _ = MS (oldMatrixMap (D.vector R₀ p₀)) := congrArg MS (D.vector_natural a₀ p₀)
      _ = _ := hmatrix _

private theorem quaternionicCliffordMap_leftInverse
    {F B L n m J : Type u} [Field F] [Ring B] [Algebra F B] [Field L] [Algebra F L]
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {G I : GroupScheme F} {π : G ⟶ I} (D : QuaternionicSpinCoverPresentation F B L n m J π)
    {R S : TestAlgebra F} (a : R ≅ S) :
    Function.LeftInverse (D.cliffordMap a.inv) (D.cliffordMap a.hom) := by
  have htest (r : R) : a.inv.hom (a.hom.hom r) = r :=
    DFunLike.congr_fun (congrArg (fun f : R ⟶ R ↦ f.hom) a.hom_inv_id) r
  have hcoeff (s : R ⊗[F] L) :
      extendTestCoefficients a.inv L (extendTestCoefficients a.hom L s) = s := by
    induction s using TensorProduct.inductionOn with
    | tmul r t =>
      change a.inv.hom (a.hom.hom r) ⊗ₜ[F] t = r ⊗ₜ[F] t
      rw [htest]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hvec (v : m → R ⊗[F] L) :
      extendTestCoefficients a.inv L ∘ (extendTestCoefficients a.hom L ∘ v) = v :=
    funext fun k ↦ hcoeff (v k)
  have h : (D.cliffordMap a.inv).comp (D.cliffordMap a.hom) = RingHom.id (even (D.chart R).form) := by
    apply evenCliffordRingHom_ext
    · intro s
      simp only [RingHom.comp_apply, D.cliffordMap_scalar, hcoeff, RingHom.id_apply]
    · intro v w
      simp only [RingHom.comp_apply, D.cliffordMap_pair, hvec, RingHom.id_apply]
  exact DFunLike.congr_fun h

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
theorem quaternionicSpinRationalTransport : QuaternionicSpinRationalTransport.{u} := by
  intro F E B L n m J _ _ _ _ _ _ _ _ _ _ e G I π D
  letI := scalarStructure e
  intro R R₀ R_F a i j C b t d
  let aIso : R_F ≅ R₀ := (fieldTestIso e).symm
  have hbase (X : SchemeOver F) (p : RationalPoints ((baseChange F E).obj X)) :
      mapPoints a (originalPoint e X p) = baseChangePoint F E X R p := by
    change (testSpec F).map aIso.hom.op ≫ (testSpec F).map aIso.inv.op ≫ _ = _
    rw [← Category.assoc, ← Functor.map_comp, ← op_comp, aIso.inv_hom_id, op_id,
      (testSpec F).map_id (op R₀), Category.id_comp]
  have hb (r : F) (z : B) : b (r ⊗ₜ[F] z) = e r ⊗ₜ[F] z := by
    change Algebra.TensorProduct.lid E (E ⊗[F] B) (e r ⊗ₜ[E] ((1 : E) ⊗ₜ[F] z)) = _
    rw [Algebra.TensorProduct.lid_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have ht (r : F) (z : L) : t (r ⊗ₜ[F] z) = e r ⊗ₜ[E] ((1 : E) ⊗ₜ[F] z) := rfl
  have hd : Function.Bijective (D.cliffordMap a) :=
    ⟨(quaternionicCliffordMap_leftInverse D aIso).injective,
      (quaternionicCliffordMap_leftInverse D aIso.symm).surjective⟩
  refine ⟨hb, ht, C.evenEquiv.bijective.comp hd, ?_, ?_, ?_, ?_⟩
  · intro s
    change C.evenEquiv (D.cliffordMap a (algebraMap _ (even (D.chart R_F).form) s)) = _
    rw [D.cliffordMap_scalar, evenCliffordEquiv_scalar C.clifford_formula]
    rfl
  · intro v w
    change C.evenEquiv (D.cliffordMap a ((even.ι (D.chart R_F).form).bilin v w)) = _
    rw [D.cliffordMap_pair, evenCliffordEquiv_pair C.clifford_formula]
    rfl
  · intro p x y
    have h := D.spin_natural a (originalPoint e G.X p)
    rw [hbase G.X p] at h
    constructor
    · rw [(C.cover_eq (D.spin R₀ (baseChangePoint F E G.X R p))).1, h.1]
      apply Units.ext
      ext k l
      rfl
    · rw [(C.cover_eq (D.spin R₀ (baseChangePoint F E G.X R p))).2, h.2]
      exact Units.ext rfl
  · intro p
    have h := D.vector_natural a (originalPoint e I.X p)
    rw [hbase I.X p] at h
    rw [h]
    apply Units.ext
    ext k l
    rfl

end QuaternionicSpin

section Subgroups

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open _root_.LinearAlgebraicGroups.Specs (IsNormalSubgroup subgroupConjugation)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.GeometricRadicals (IsSmoothConnectedNormal IsUnipotentRadical)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup IsUnipotent)

variable [Algebra F E] [IsIso (fieldSpecMap F E)]

private theorem schemeBaseChange_isEquivalence : (baseChange F E).IsEquivalence :=
  (Over.mapPullbackAdj (fieldSpecMap F E)).isEquivalence_right_of_isEquivalence_left

private theorem groupBaseChange_isEquivalence : (groupBaseChange F E).IsEquivalence := by
  letI : (baseChange F E).IsEquivalence := schemeBaseChange_isEquivalence
  exact { essSurj := ⟨fun G ↦ ((baseChange F E).essImage_mapGrp).mpr
    (Functor.EssSurj.mem_essImage (baseChange F E) G.X)⟩ }

private theorem property_baseChange_iff (Q : MorphismProperty Scheme.{u})
    [Q.IsStableUnderBaseChange] (X : SchemeOver F) :
    Q ((baseChange F E).obj X).hom ↔ Q X.hom := by
  let b := fieldSpecMap F E
  let p := pullback.fst X.hom b
  let q := pullback.snd X.hom b
  change Q q ↔ Q X.hom
  haveI : IsIso p := inferInstanceAs (IsIso (pullback.fst X.hom b))
  have h : p ≫ X.hom = q ≫ b := pullback.condition
  have hr : inv p ≫ q = X.hom ≫ inv b := by
    calc
      inv p ≫ q = inv p ≫ (q ≫ b) ≫ inv b := by simp
      _ = X.hom ≫ inv b := by rw [← h]; simp
  exact ⟨MorphismProperty.of_isPullback (IsPullback.of_horiz_isIso ⟨hr⟩),
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback X.hom b)⟩

private theorem property_of_overIso {k : Type u} [Field k]
    (Q : MorphismProperty Scheme.{u}) [Q.IsStableUnderBaseChange]
    {X Y : SchemeOver k} (a : X ≅ Y) (h : Q Y.hom) : Q X.hom := by
  letI : IsIso a.hom.left := (Over.forget _).map_isIso a.hom
  have hc : CommSq a.hom.left X.hom Y.hom (𝟙 _) := ⟨by rw [Over.w, Category.comp_id]⟩
  exact MorphismProperty.of_isPullback (IsPullback.of_horiz_isIso hc) h

private theorem connected_baseChange_iff (X : SchemeOver F) :
    ConnectedSpace ((baseChange F E).obj X).left ↔ ConnectedSpace X.left :=
  (pullback.fst X.hom (fieldSpecMap F E)).homeomorph.connectedSpace_iff

private theorem closedImmersion_baseChange_reflects {X Y : SchemeOver F} (j : X ⟶ Y)
    (hj : IsClosedImmersion ((baseChange F E).map j).left) : IsClosedImmersion j.left := by
  let b := fieldSpecMap F E
  let h : ((baseChange F E).map j).left ≫ pullback.fst Y.hom b =
      pullback.fst X.hom b ≫ j.left := pullback.lift_fst _ _ _
  haveI := hj
  have hc : IsClosedImmersion (((baseChange F E).map j).left ≫ pullback.fst Y.hom b) :=
    IsClosedImmersion.comp _ _
  exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
    (pullback.fst X.hom b) j.left).mp (h ▸ hc)

private theorem subgroup_baseChange_iff {G : GroupScheme F} (U V : ClosedSubgroup G) :
    IsSubgroupOf (transportedSubgroup F E U) (transportedSubgroup F E V) ↔
      IsSubgroupOf U V := by
  let H := groupBaseChange F E
  letI : H.IsEquivalence := groupBaseChange_isEquivalence
  constructor
  · rintro ⟨a, ha⟩
    change H.obj U.group ⟶ H.obj V.group at a
    change a ≫ H.map V.inclusion = H.map U.inclusion at ha
    refine ⟨H.preimage a, H.map_injective ?_⟩
    rw [H.map_comp, H.map_preimage, ha]
  · rintro ⟨a, ha⟩
    exact ⟨H.map a, (H.map_comp _ _).symm.trans (congrArg H.map ha)⟩

private theorem subgroup_lift {G : GroupScheme F}
    (V : ClosedSubgroup ((groupBaseChange F E).obj G)) :
    ∃ U : ClosedSubgroup G, ∃ a : (transportedSubgroup F E U).group ≅ V.group,
      a.hom ≫ V.inclusion = (transportedSubgroup F E U).inclusion := by
  let H := groupBaseChange F E
  letI : H.IsEquivalence := groupBaseChange_isEquivalence
  let U := H.objPreimage V.group
  let a : H.obj U ≅ V.group := H.objObjPreimageIso V.group
  let j : U ⟶ G := H.preimage (a.hom ≫ V.inclusion)
  have hj : H.map j = a.hom ≫ V.inclusion := H.map_preimage _
  have hc : IsClosedImmersion j.hom.hom.left := by
    apply closedImmersion_baseChange_reflects (F := F) (E := E) j.hom.hom
    change IsClosedImmersion (H.map j).hom.hom.left
    rw [hj]
    letI := V.isClosedImmersion
    letI : IsIso a.hom.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso a.hom
    exact IsClosedImmersion.comp _ _
  exact ⟨⟨U, j, hc⟩, a, hj.symm⟩

set_option backward.isDefEq.respectTransparency false in
private theorem normal_precomp_iso {G H J : GroupScheme F} (a : H ≅ J) (j : J ⟶ G)
    (hj : IsNormalSubgroup j) : IsNormalSubgroup (a.hom ≫ j) := by
  obtain ⟨d, hd⟩ := hj
  let f := G.X ◁ a.hom.hom.hom
  refine ⟨f ≫ d ≫ a.inv.hom.hom, ?_⟩
  have ha : a.inv.hom.hom ≫ (a.hom ≫ j).hom.hom = j.hom.hom := by
    change (a.inv ≫ a.hom ≫ j).hom.hom = _
    rw [a.inv_hom_id_assoc]
  rw [Category.assoc, Category.assoc, ha, hd]
  simp only [subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv, f,
    whiskerLeft_fst, whiskerLeft_snd_assoc]
  rfl

private theorem subgroup_smoothConnectedNormal_baseChange_iff {G : AffineAlgebraicGroup F}
    (U : ClosedSubgroup G.val) :
    IsSmoothConnectedNormal (G := baseChangedAlgebraicGroup E G) (transportedSubgroup F E U) ↔
      IsSmoothConnectedNormal U :=
  and_congr (property_baseChange_iff @Smooth U.group.X)
    (and_congr (connected_baseChange_iff U.group.X)
      (baseChangeNormalSubgroupIff F E U.inclusion U.isClosedImmersion))

omit [IsIso (fieldSpecMap F E)] in
private theorem subgroup_unipotent_baseChange_iff {G : AffineAlgebraicGroup F}
    (U : ClosedSubgroup G.val) :
    IsUnipotent (closedSubgroupAlgebraicGroup (G := baseChangedAlgebraicGroup E G)
      (transportedSubgroup F E U)) ↔ IsUnipotent (closedSubgroupAlgebraicGroup U) :=
  Unipotent.unipotenceFieldExtension (K := E) (closedSubgroupAlgebraicGroup U)

private theorem subgroup_smoothConnectedNormal_of_iso {G : AffineAlgebraicGroup F}
    {U V : ClosedSubgroup G.val} (a : U.group ≅ V.group)
    (ha : a.hom ≫ V.inclusion = U.inclusion) (hv : IsSmoothConnectedNormal V) :
    IsSmoothConnectedNormal U := by
  let z := (Grp.forget (SchemeOver F) ⋙ Over.forget _).mapIso a
  refine ⟨?_, z.hom.homeomorph.connectedSpace_iff.mpr hv.2.1, ?_⟩
  · exact property_of_overIso @Smooth ((Grp.forget (SchemeOver F)).mapIso a) hv.1
  · rw [← ha]
    exact normal_precomp_iso a _ hv.2.2

private theorem unipotent_of_groupIso {G H : AffineAlgebraicGroup F}
    (a : G.val ≅ H.val) : IsUnipotent G → IsUnipotent H := by
  rintro ⟨A, ⟨i⟩, h⟩
  exact ⟨A, ⟨i ≪≫ a⟩, h⟩

private theorem radical_baseChange_iff (G : AffineAlgebraicGroup F) (U : ClosedSubgroup G.val) :
    IsUnipotentRadical (baseChangedAlgebraicGroup E G) (transportedSubgroup F E U) ↔
      IsUnipotentRadical G U := by
  let U' := transportedSubgroup F E U
  let G' := baseChangedAlgebraicGroup E G
  constructor
  · rintro ⟨hn, hu, hm⟩
    refine ⟨(subgroup_smoothConnectedNormal_baseChange_iff U).mp hn,
      (subgroup_unipotent_baseChange_iff U).mp hu, ?_⟩
    intro V hv hv'
    exact (subgroup_baseChange_iff V U).mp (hm (transportedSubgroup F E V)
      ((subgroup_smoothConnectedNormal_baseChange_iff V).mpr hv)
      ((subgroup_unipotent_baseChange_iff V).mpr hv'))
  · rintro ⟨hn, hu, hm⟩
    refine ⟨(subgroup_smoothConnectedNormal_baseChange_iff U).mpr hn,
      (subgroup_unipotent_baseChange_iff U).mpr hu, ?_⟩
    intro V hv hv'
    change ClosedSubgroup ((groupBaseChange F E).obj G.val) at V
    obtain ⟨W, a, ha⟩ := subgroup_lift V
    let W' := transportedSubgroup F E W
    have hw : IsSmoothConnectedNormal (G := G') W' :=
      subgroup_smoothConnectedNormal_of_iso a ha hv
    have hw' : IsUnipotent (closedSubgroupAlgebraicGroup (G := G') W') :=
      unipotent_of_groupIso a.symm hv'
    obtain ⟨j, hj⟩ := (subgroup_baseChange_iff (E := E) W U).mpr
      (hm W ((subgroup_smoothConnectedNormal_baseChange_iff (E := E) W).mp hw)
        ((subgroup_unipotent_baseChange_iff (E := E) W).mp hw'))
    change IsSubgroupOf V U'
    refine ⟨a.inv ≫ j, ?_⟩
    calc
      (a.inv ≫ j) ≫ U'.inclusion = a.inv ≫ (j ≫ U'.inclusion) := Category.assoc _ _ _
      _ = a.inv ≫ W'.inclusion := congrArg (a.inv ≫ ·) hj
      _ = a.inv ≫ (a.hom ≫ V.inclusion) := congrArg (a.inv ≫ ·) ha.symm
      _ = V.inclusion := a.inv_hom_id_assoc _

set_option backward.isDefEq.respectTransparency false in
private theorem normal_postcomp_iso {H G J : GroupScheme F}
    (a : G ≅ J) (j : H ⟶ G) (hj : IsNormalSubgroup j) :
    IsNormalSubgroup (j ≫ a.hom) := by
  obtain ⟨d, hd⟩ := hj
  let f : J.X ⊗ H.X ⟶ G.X ⊗ H.X := a.inv.hom.hom ⊗ₘ 𝟙 H.X
  refine ⟨f ≫ d, ?_⟩
  change (f ≫ d) ≫ j.hom.hom ≫ a.hom.hom.hom = _
  rw [← Category.assoc, Category.assoc f, hd]
  have ha : a.inv.hom.hom ≫ a.hom.hom.hom = 𝟙 _ :=
    ((Grp.forget (SchemeOver F)).mapIso a).inv_hom_id
  simp only [subgroupConjugation, MonObj.mul_comp, GrpObj.inv_comp, MonObj.comp_mul,
    GrpObj.comp_inv, ← Category.assoc, show f ≫ fst G.X H.X =
      fst J.X H.X ≫ a.inv.hom.hom from tensorHom_fst _ _,
    show f ≫ snd G.X H.X = snd J.X H.X from by simp [f]]
  simp only [Category.assoc, ha, Category.comp_id]
  rfl

private abbrev pushSubgroup {G J : GroupScheme F} (a : G ≅ J) (U : ClosedSubgroup G) :
    ClosedSubgroup J := by
  refine ⟨U.group, U.inclusion ≫ a.hom, ?_⟩
  letI := U.isClosedImmersion
  haveI : IsIso a.hom.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso a.hom
  exact IsClosedImmersion.comp U.inclusion.hom.hom.left a.hom.hom.hom.left

private def HasOnlyTrivialUnipotentNormals (G : AffineAlgebraicGroup F) : Prop :=
  ∀ U : ClosedSubgroup G.val, IsSmoothConnectedNormal U →
    IsUnipotent (closedSubgroupAlgebraicGroup U) → Nonempty (IsTerminal U.group)

private theorem hasOnlyTrivialUnipotentNormals_of_iso
    {G H : AffineAlgebraicGroup F} (a : G.val ≅ H.val)
    (h : HasOnlyTrivialUnipotentNormals G) : HasOnlyTrivialUnipotentNormals H := by
  intro U hU hu
  exact h (pushSubgroup a.symm U)
    ⟨hU.1, hU.2.1, normal_postcomp_iso a.symm U.inclusion hU.2.2⟩ hu

private theorem hasOnlyTrivialUnipotentNormals_baseChange (G : AffineAlgebraicGroup F) :
    HasOnlyTrivialUnipotentNormals (baseChangedAlgebraicGroup E G) ↔
      HasOnlyTrivialUnipotentNormals G := by
  let H := groupBaseChange F E
  letI : H.IsEquivalence := groupBaseChange_isEquivalence
  constructor
  · intro h U hU hu
    obtain ⟨t⟩ := h (transportedSubgroup F E U)
      ((subgroup_smoothConnectedNormal_baseChange_iff U).mpr hU)
      ((subgroup_unipotent_baseChange_iff U).mpr hu)
    exact ⟨IsTerminal.isTerminalOfObj H _ t⟩
  · intro h V hv hv'
    obtain ⟨U, a, ha⟩ := subgroup_lift V
    obtain ⟨t⟩ := h U
      ((subgroup_smoothConnectedNormal_baseChange_iff U).mp
        (subgroup_smoothConnectedNormal_of_iso a ha hv))
      ((subgroup_unipotent_baseChange_iff U).mp (unipotent_of_groupIso a.symm hv'))
    exact ⟨(t.isTerminalObj H _).ofIso a⟩

open Specs.GeometricBorelConjugacy (IsSmoothConnectedSolvable IsBorel)
open private solvable_iff_sections from LinearAlgebraicGroups.Reductive.GeometricRadicals

open scoped CategoryTheory.Obj in
private def sectionsBaseChangeEquiv (G : GroupScheme F) :
    (𝟙_ (SchemeOver F) ⟶ G.X) ≃* (𝟙_ (SchemeOver E) ⟶ ((groupBaseChange F E).obj G).X) := by
  let H := baseChange F E
  letI : H.IsEquivalence := schemeBaseChange_isEquivalence
  let e := (Functor.FullyFaithful.ofFullyFaithful H).homMulEquiv (X := 𝟙_ (SchemeOver F)) (M := G.X)
  let i := asIso (Functor.LaxMonoidal.ε H)
  refine e.trans { toFun := fun p ↦ i.hom ≫ p, invFun := fun p ↦ i.inv ≫ p
                   left_inv := ?_, right_inv := ?_, map_mul' := fun f g ↦ MonObj.comp_mul _ f g }
  · intro p
    exact i.inv_hom_id_assoc p
  · intro p
    exact i.hom_inv_id_assoc p

private theorem solvable_iff_of_mulEquiv {A B : Type*} [Group A] [Group B] (a : A ≃* B) :
    Group.IsSolvable B ↔ Group.IsSolvable A := by
  constructor
  · intro h
    letI := h
    exact Group.isSolvable_of_surjective (f := a.symm.toMonoidHom) a.symm.surjective
  · intro h
    letI := h
    exact Group.isSolvable_of_surjective (f := a.toMonoidHom) a.surjective

private theorem smoothConnectedSolvable_baseChange_iff [IsAlgClosed F] [IsAlgClosed E]
    {G : AffineAlgebraicGroup F} (U : ClosedSubgroup G.val) :
    IsSmoothConnectedSolvable (transportedSubgroup F E U) ↔ IsSmoothConnectedSolvable U := by
  let D := closedSubgroupAlgebraicGroup U
  let D' := baseChangedAlgebraicGroup E D
  let a := sectionsBaseChangeEquiv (F := F) (E := E) U.group
  have hs := property_baseChange_iff (F := F) (E := E) @Smooth U.group.X
  have hc := connected_baseChange_iff (F := F) (E := E) U.group.X
  let X := (baseChange F E).obj U.group.X
  change (Smooth X.hom ∧ ConnectedSpace X.left ∧ Specs.SchemeDerivedGroup.IsSolvable D'.val) ↔
    (Smooth U.group.X.hom ∧ ConnectedSpace U.group.X.left ∧ Specs.SchemeDerivedGroup.IsSolvable D.val)
  change Smooth X.hom ↔ Smooth U.group.X.hom at hs
  change ConnectedSpace X.left ↔ ConnectedSpace U.group.X.left at hc
  rw [hs, hc]
  apply and_congr_right
  intro hsm
  apply and_congr_right
  intro hcon
  exact (solvable_iff_sections D' (hs.mpr hsm) (hc.mpr hcon)).trans
    ((solvable_iff_of_mulEquiv a).trans (solvable_iff_sections D hsm hcon).symm)

private theorem smoothConnectedSolvable_of_groupIso [IsAlgClosed F]
    {G H : AffineAlgebraicGroup F} {U : ClosedSubgroup G.val} {V : ClosedSubgroup H.val}
    (a : U.group ≅ V.group) (hv : IsSmoothConnectedSolvable V) :
    IsSmoothConnectedSolvable U := by
  let z := (Grp.forget (SchemeOver F) ⋙ Over.forget _).mapIso a
  have hs : Smooth U.group.X.hom :=
    property_of_overIso @Smooth ((Grp.forget (SchemeOver F)).mapIso a) hv.1
  have hc : ConnectedSpace U.group.X.left := z.hom.homeomorph.connectedSpace_iff.mpr hv.2.1
  let r := ((yonedaGrp.mapIso a).app (op (𝟙_ (SchemeOver F)))).groupIsoToMulEquiv
  exact ⟨hs, hc, (solvable_iff_sections (closedSubgroupAlgebraicGroup U) hs hc).mpr
    ((solvable_iff_of_mulEquiv r).mp
      ((solvable_iff_sections (closedSubgroupAlgebraicGroup V) hv.1 hv.2.1).mp hv.2.2))⟩

private theorem subgroupOf_trans {G : GroupScheme F} {U V W : ClosedSubgroup G}
    (h : IsSubgroupOf U V) (h' : IsSubgroupOf V W) : IsSubgroupOf U W := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h'
  exact ⟨a ≫ b, by rw [Category.assoc, hb, ha]⟩

private theorem borel_of_inclusionIso [IsAlgClosed F] {G : AffineAlgebraicGroup F}
    {U V : ClosedSubgroup G.val} (a : U.group ≅ V.group)
    (ha : a.hom ≫ V.inclusion = U.inclusion) (hV : IsBorel V) : IsBorel U := by
  have hvu : IsSubgroupOf V U := ⟨a.inv, by rw [← ha, a.inv_hom_id_assoc]⟩
  exact ⟨smoothConnectedSolvable_of_groupIso a hV.1, fun W hW hUW ↦
    subgroupOf_trans (hV.2 W hW (subgroupOf_trans hvu hUW)) hvu⟩

private theorem borel_baseChange_iff [IsAlgClosed F] [IsAlgClosed E]
    {G : AffineAlgebraicGroup F} (U : ClosedSubgroup G.val) :
    IsBorel (transportedSubgroup F E U) ↔ IsBorel U := by
  let U' := transportedSubgroup F E U
  constructor
  · intro hU
    refine ⟨(smoothConnectedSolvable_baseChange_iff U).mp hU.1, ?_⟩
    intro V hV hUV
    exact (subgroup_baseChange_iff V U).mp (hU.2 _
      ((smoothConnectedSolvable_baseChange_iff V).mpr hV)
      ((subgroup_baseChange_iff U V).mpr hUV))
  · intro hU
    refine ⟨(smoothConnectedSolvable_baseChange_iff U).mpr hU.1, ?_⟩
    intro V hV hUV
    obtain ⟨W, a, ha⟩ := subgroup_lift V
    let W' := transportedSubgroup F E W
    have hvw : IsSubgroupOf V W' := ⟨a.inv, by rw [← ha, a.inv_hom_id_assoc]⟩
    have hs : IsSmoothConnectedSolvable W' :=
      smoothConnectedSolvable_of_groupIso (G := baseChangedAlgebraicGroup E G)
        (H := baseChangedAlgebraicGroup E G) a hV
    have hWU := hU.2 W ((smoothConnectedSolvable_baseChange_iff W).mp hs)
      ((subgroup_baseChange_iff U W).mp (subgroupOf_trans hUV hvw))
    exact subgroupOf_trans hvw ((subgroup_baseChange_iff W U).mpr hWU)

private theorem borel_push [IsAlgClosed F] {G H : AffineAlgebraicGroup F} (a : G.val ≅ H.val)
    {U : ClosedSubgroup G.val} (hU : IsBorel U) : IsBorel (pushSubgroup a U) := by
  refine ⟨hU.1, ?_⟩
  intro W hW hUW
  obtain ⟨f, hf⟩ := hUW
  change f ≫ W.inclusion = U.inclusion ≫ a.hom at hf
  have hu : IsSubgroupOf U (pushSubgroup a.symm W) := ⟨f, by
    change f ≫ W.inclusion ≫ a.inv = U.inclusion
    rw [← Category.assoc, hf, Category.assoc, a.hom_inv_id, Category.comp_id]⟩
  obtain ⟨g, hg⟩ := hU.2 _ hW hu
  change g ≫ U.inclusion = W.inclusion ≫ a.inv at hg
  exact ⟨g, by
    change g ≫ U.inclusion ≫ a.hom = W.inclusion
    rw [← Category.assoc, hg, Category.assoc, a.inv_hom_id, Category.comp_id]⟩

private def HasBorelBelow {G : GroupScheme F} (P : ClosedSubgroup G) : Prop :=
  ∃ B : ClosedSubgroup G, IsBorel B ∧ IsSubgroupOf B P

private theorem hasBorelBelow_baseChange_iff [IsAlgClosed F] [IsAlgClosed E]
    {G : AffineAlgebraicGroup F} (P : ClosedSubgroup G.val) :
    HasBorelBelow (transportedSubgroup F E P) ↔ HasBorelBelow P := by
  constructor
  · rintro ⟨C, hC, hCP⟩
    obtain ⟨B, a, ha⟩ := subgroup_lift (F := F) (E := E) (G := G.val) C
    let G' := baseChangedAlgebraicGroup E G
    let B' := transportedSubgroup F E B
    have hB : IsBorel B' := borel_of_inclusionIso (G := G') (U := B') (V := C) a ha hC
    have hs : IsSubgroupOf B' C := ⟨a.hom, ha⟩
    exact ⟨B, (borel_baseChange_iff (E := E) B).mp hB,
      (subgroup_baseChange_iff (E := E) B P).mp (subgroupOf_trans hs hCP)⟩
  · rintro ⟨B, hB, hBP⟩
    exact ⟨transportedSubgroup F E B, (borel_baseChange_iff (E := E) B).mpr hB,
      (subgroup_baseChange_iff (E := E) B P).mpr hBP⟩

private theorem hasBorelBelow_of_iso [IsAlgClosed F]
    {G H : AffineAlgebraicGroup F} (a : G.val ≅ H.val)
    {P : ClosedSubgroup G.val} {Q : ClosedSubgroup H.val}
    (d : P.group ≅ Q.group) (hd : d.hom ≫ Q.inclusion = P.inclusion ≫ a.hom)
    (hP : HasBorelBelow P) : HasBorelBelow Q := by
  obtain ⟨B, hB, f, hf⟩ := hP
  refine ⟨pushSubgroup a B, borel_push a hB, f ≫ d.hom, ?_⟩
  change (f ≫ d.hom) ≫ Q.inclusion = B.inclusion ≫ a.hom
  rw [Category.assoc, hd, ← Category.assoc, hf]

end Subgroups

theorem groupSchemeTransport : GroupSchemeTransport.{u} := by
  intro F E _ _ e
  letI := scalarStructure e
  letI := fieldSpecMap_isIso e
  refine ⟨groupBaseChange_isEquivalence, ?_⟩
  intro G H f
  exact ⟨closedImmersion_baseChange_reflects f.hom.hom,
    fun h ↦ (transportedSubgroup F E (⟨G, f, h⟩ : ClosedSubgroup H)).isClosedImmersion⟩

private theorem morphismPropertyTransport (e : F ≃+* E)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] {X Y : SchemeOver F} (f : X ⟶ Y) :
    letI := scalarStructure e
    P ((baseChange F E).map f).left ↔ P f.left := by
  letI := scalarStructure e
  letI := fieldSpecMap_isIso e
  haveI : IsIso (projection e X) :=
    inferInstanceAs (IsIso (pullback.fst X.hom (fieldSpecMap F E)))
  haveI : IsIso (projection e Y) :=
    inferInstanceAs (IsIso (pullback.fst Y.hom (fieldSpecMap F E)))
  have h : ((baseChange F E).map f).left ≫ projection e Y = projection e X ≫ f.left :=
    pullback.lift_fst _ _ _
  calc
    _ ↔ P (((baseChange F E).map f).left ≫ projection e Y) :=
      (MorphismProperty.cancel_right_of_respectsIso (P := P) _ _).symm
    _ ↔ P (projection e X ≫ f.left) := by rw [h]
    _ ↔ _ := MorphismProperty.cancel_left_of_respectsIso (P := P) _ _

set_option backward.isDefEq.respectTransparency false in
theorem identityComponentTransport : IdentityComponentTransport.{u} := by
  intro F E _ _ e H G i
  letI := scalarStructure e
  intro G' i'
  letI := fieldSpecMap_isIso e
  haveI : IsIso (projection e G.X) :=
    inferInstanceAs (IsIso (pullback.fst G.X.hom (fieldSpecMap F E)))
  haveI : IsIso (projection e H.X) :=
    inferInstanceAs (IsIso (pullback.fst H.X.hom (fieldSpecMap F E)))
  let v := (projection e G.X).homeomorph
  let w := (projection e H.X).homeomorph
  have hsq : i'.hom.hom.left ≫ projection e G.X = projection e H.X ≫ i.hom.hom.left :=
    pullback.lift_fst _ _ _
  have hopp : IsOpenImmersion i'.hom.hom.left ↔ IsOpenImmersion i.hom.hom.left := by
    exact morphismPropertyTransport e @IsOpenImmersion i.hom.hom
  have hpoint (x : ((baseChange F E).obj H.X).left) :
      v (i'.hom.hom.left x) = i.hom.hom.left (w x) :=
    congrArg (fun f : ((baseChange F E).obj H.X).left ⟶ G.X.left ↦ f x) hsq
  have hrange : v '' Set.range i'.hom.hom.left = Set.range i.hom.hom.left := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨w x, (hpoint x).symm⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨q, rfl⟩ := w.surjective x
      exact ⟨i'.hom.hom.left q, ⟨q, rfl⟩, hpoint q⟩
  have ho : originalPoint e G.X (1 : RationalPoints G'.X) = 1 :=
    (originalGroupEquiv_apply e G 1).symm.trans (map_one (originalGroupEquiv e G))
  have hunit : v (identitySchemePoint G') = identitySchemePoint G := by
    have h := congrArg (fun p : RationalPoints G.X ↦ p.left (default : PrimeSpectrum F)) ho
    change v ((1 : RationalPoints G'.X).left
      (Spec.map (CommRingCat.ofHom e.symm.toRingHom) (default : PrimeSpectrum F))) = _ at h
    have hp : Spec.map (CommRingCat.ofHom e.symm.toRingHom) (default : PrimeSpectrum F) =
        (default : PrimeSpectrum E) := Subsingleton.elim _ _
    rw [hp] at h
    exact h
  have hcc : v '' connectedComponent (identitySchemePoint G') =
      connectedComponent (identitySchemePoint G) := by
    simpa only [Set.image_univ_of_surjective v.surjective, connectedComponentIn_univ, hunit] using
      v.image_connectedComponentIn (Set.mem_univ (identitySchemePoint G'))
  refine and_congr hopp ?_
  rw [← hrange, ← hcc]
  exact Set.image_injective.mpr v.injective |>.eq_iff.symm

set_option backward.isDefEq.respectTransparency false in
theorem quaternionicSpinIsometryTransport : QuaternionicSpinIsometryTransport.{u} := by
  intro F E B L n m J _ _ _ _ _ _ _ _ _ _ e G I O π incl D V
  letI := scalarStructure e
  intro K incl' π'
  have hcover : (IsFinite π' ∧ Flat π' ∧ Surjective π') ↔
      (IsFinite π.hom.hom.left ∧ Flat π.hom.hom.left ∧ Surjective π.hom.hom.left) :=
    and_congr (morphismPropertyTransport e @IsFinite π.hom.hom)
      (and_congr (morphismPropertyTransport e @Flat π.hom.hom)
        (morphismPropertyTransport e @Surjective π.hom.hom))
  refine ⟨hcover, identityComponentTransport e incl, ?_⟩
  intro R R₀ i j C f σ' ℓ'
  let oldPoints : GroupPoints (K.obj O) R ≃* GroupPoints O R₀ :=
    baseChangePointGroupEquiv E O R
  let matrix := Units.mapEquiv f.toRingEquiv.toMulEquiv
  let coordinates := matrix.toMonoidHom.comp ((V.coordinates R₀).comp oldPoints.toMonoidHom)
  obtain ⟨hadj, hsemi, _, hisometry⟩ := quaternionicSpinEquationTransport C (V.adjoint R₀)
  have hrange (M : (Matrix n n (R₀ ⊗[F] B))ˣ) :
      matrix M ∈ Set.range coordinates ↔ M ∈ Set.range (V.coordinates R₀) := by
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨oldPoints p, matrix.injective hp⟩
    · rintro ⟨p, hp⟩
      obtain ⟨q, rfl⟩ := oldPoints.surjective p
      exact ⟨q, congrArg matrix hp⟩
  refine ⟨coordinates, matrix.injective.comp ((V.coordinates_injective R₀).comp oldPoints.injective),
    fun _ ↦ rfl, hadj.2 (V.adjoint_eq R₀), ?_, ?_, ?_⟩
  · intro ℓ hℓ
    cases h : V.semitrace R₀ with
    | none =>
      change (V.semitrace R₀).map f = some ℓ at hℓ
      rw [h] at hℓ
      contradiction
    | some L =>
      change (V.semitrace R₀).map f = some ℓ at hℓ
      rw [h] at hℓ
      have hL : f L = ℓ := Option.some.inj hℓ
      rw [← hL]
      exact (hsemi L).2 (V.semitrace_eq R₀ L h)
  · intro M
    obtain ⟨M, rfl⟩ := matrix.surjective M
    exact (hrange M).trans ((V.coordinates_range R₀ M).trans (hisometry _ M).symm)
  · intro p
    let p₀ := baseChangePoint F E G.X R p
    let q := p ≫ (K.map π).hom.hom
    let q₀ := baseChangePoint F E I.X R q
    have hπ : q₀ = p₀ ≫ π.hom.hom := baseChangePointsSchemeNaturality F E π.hom.hom R p
    have hIncl : baseChangePoint F E O.X R (q ≫ incl'.hom.hom) = q₀ ≫ incl.hom.hom :=
      baseChangePointsSchemeNaturality F E incl.hom.hom R q
    calc
      _ = matrix (V.coordinates R₀ (q₀ ≫ incl.hom.hom)) :=
        congrArg (fun x : GroupPoints O R₀ ↦ matrix (V.coordinates R₀ x)) hIncl
      _ = matrix (V.coordinates R₀ ((p₀ ≫ π.hom.hom) ≫ incl.hom.hom)) :=
        congrArg (fun x : GroupPoints I R₀ ↦ matrix (V.coordinates R₀ (x ≫ incl.hom.hom))) hπ
      _ = matrix (D.vector R₀ (p₀ ≫ π.hom.hom)) := congrArg matrix (V.inclusion R₀ _)
      _ = matrix (D.spin R₀ p₀).val.1 := congrArg matrix (D.projection R₀ p₀)
      _ = _ := (C.cover_eq (D.spin R₀ p₀)).1.symm

open Specs.DiagonalizableGroups (rootsOfUnityPoints)

set_option backward.isDefEq.respectTransparency false in
theorem quaternionicSpinKernelTransport : QuaternionicSpinKernelTransport.{u} := by
  intro F E _ _ e G I Z U π z p unitInclusion hU hker h
  letI := scalarStructure e
  intro K
  letI : K.IsEquivalence := (groupSchemeTransport e).1
  refine ⟨K.map_isPullback hker, ⟨hU.isTerminalObj K U⟩, ?_⟩
  let v (R : TestAlgebra E) := (restrictTestAlgebra F E).obj R
  let component (R : TestAlgebra E) : ((groupPointsFunctor E).obj (K.obj Z)).obj R ≅
      (rootsOfUnityPoints E 2).obj R :=
    (baseChangePointGroupEquiv E Z R).toGrpIso ≪≫ h.app (v R)
  let h' : (groupPointsFunctor E).obj (K.obj Z) ≅ rootsOfUnityPoints E 2 :=
    NatIso.ofComponents component (by
      intro R S a
      apply GrpCat.ext
      intro q
      change h.hom.app (v S) (baseChangePoint F E Z.X S (mapPoints a q)) =
        (rootsOfUnityPoints E 2).map a (h.hom.app (v R) (baseChangePoint F E Z.X R q))
      rw [baseChangePointsNaturality F E Z.X a q]
      exact ConcreteCategory.congr_hom (h.hom.naturality ((restrictTestAlgebra F E).map a))
        (baseChangePoint F E Z.X R q))
  exact ⟨h', fun _ _ ↦ rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem quaternionicSpinScalarKernelTransport : QuaternionicSpinScalarKernelTransport.{u} := by
  intro F E B L n m J _ _ _ _ _ _ _ _ _ _ e G I Z U π D z p unitInclusion hU hker h hscalar
  letI := scalarStructure e
  intro K
  obtain ⟨pullback, terminal, h', hh'⟩ := quaternionicSpinKernelTransport e π z p unitInclusion hU hker h
  refine ⟨pullback, terminal, h', ?_⟩
  intro R R₀ i j C q q₀ x
  have hq : baseChangePoint F E G.X R (q ≫ (K.map z).hom.hom) = q₀ ≫ z.hom.hom :=
    baseChangePointsSchemeNaturality F E z.hom.hom R q
  have hscalar₀ := hscalar R₀ q₀
  have ht := hh' R q
  let y := D.spin R₀ (q₀ ≫ z.hom.hom)
  have hx : x = C.cover y := congrArg (fun a : GroupPoints G R₀ ↦ C.cover (D.spin R₀ a)) hq
  refine ⟨ht, ?_, ?_⟩
  · rw [hx, (C.cover_eq y).1]
    exact (congrArg _ hscalar₀.1).trans (map_one _)
  · rw [hx, ht]
    exact (C.scalar_iff y (h.hom.app R₀ q₀).val).2 hscalar₀.2

set_option backward.isDefEq.respectTransparency false in
theorem rationalSubgroupTransport : RationalSubgroupTransport.{u} := by
  intro F E _ _ e G U
  letI := scalarStructure e
  intro U' p
  let f := originalGroupEquiv e U.group
  let g := originalGroupEquiv e G
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨f q, ?_⟩
    exact (pointNaturality e U.inclusion.hom.hom q).symm
  · rintro ⟨q, hq⟩
    refine ⟨f.symm q, ?_⟩
    apply g.injective
    let j := U.inclusion.hom.hom
    let q' := f.symm q
    change g (q' ≫ (baseChange F E).map j) = g p
    calc
      g (q' ≫ (baseChange F E).map j) = originalPoint e G.X (q' ≫ (baseChange F E).map j) :=
        originalGroupEquiv_apply e G _
      _ = f q' ≫ j := pointNaturality e j q'
      _ = q ≫ j := congrArg (· ≫ j) (f.apply_symm_apply q)
      _ = g p := hq

theorem radicalTransport : RadicalTransport.{u} := by
  intro F E _ _ e G U
  letI := scalarStructure e
  haveI := fieldSpecMap_isIso e
  exact radical_baseChange_iff G U

section AlgebraicClosures

open Specs.GeometricRadicals
  (GeometricGroup IsReductive IsTrivialSubgroup geometricUnipotentRadical)
open Specs.Unipotent (baseChangedAlgebraicGroup)

/-- The isomorphism of algebraic closures extends the original isomorphism of ground fields. -/
private def closureEquiv (e : F ≃+* E) : AlgebraicClosure F ≃+* AlgebraicClosure E :=
  IsAlgClosure.equivOfEquiv (AlgebraicClosure F) (AlgebraicClosure E) e

private def geometricBaseChangeIso (e : F ≃+* E) :
    letI := scalarStructure e
    letI := scalarStructure (closureEquiv e)
    groupBaseChange F (AlgebraicClosure F) ⋙ groupBaseChange (AlgebraicClosure F) (AlgebraicClosure E) ≅
      groupBaseChange F E ⋙ groupBaseChange E (AlgebraicClosure E) := by
  letI := scalarStructure e
  letI := scalarStructure (closureEquiv e)
  let a := fieldSpecMap F (AlgebraicClosure F)
  let b := fieldSpecMap (AlgebraicClosure F) (AlgebraicClosure E)
  let c := fieldSpecMap F E
  let d := fieldSpecMap E (AlgebraicClosure E)
  have h : b ≫ a = d ≫ c := by
    dsimp only [a, b, c, d, fieldSpecMap]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext x
    exact IsAlgClosure.equivOfEquiv_algebraMap _ _ e x
  let i : Over.pullback (b ≫ a) ≅ Over.pullback (d ≫ c) := by rw [h]
  let j := (Over.pullbackComp b a).symm ≪≫ i ≪≫ Over.pullbackComp d c
  exact Functor.mapGrpCompIso.symm ≪≫ Functor.mapGrpNatIso j ≪≫ Functor.mapGrpCompIso

private theorem trivialGeometricRadical_iff (G : AffineAlgebraicGroup F) :
    IsTrivialSubgroup (geometricUnipotentRadical G) ↔
      HasOnlyTrivialUnipotentNormals (GeometricGroup G) := by
  have hr := LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest G
  constructor
  · rintro ⟨a⟩ U hU hu
    obtain ⟨j, hj⟩ := hr.2.2 U hU hu
    let R := geometricUnipotentRadical G
    have hz : IsZero R.group := (Grp.isZero_trivial _).of_iso a
    have hi : U.inclusion = 0 := by rw [← hj, hz.eq_of_tgt j 0, zero_comp]
    letI := U.isClosedImmersion
    haveI : Mono U.inclusion.hom.hom :=
      (Over.forget _).mono_of_mono_map
        (inferInstanceAs (Mono U.inclusion.hom.hom.left))
    haveI : Mono U.inclusion :=
      (Grp.forget (SchemeOver (AlgebraicClosure F))).mono_of_mono_map
        (inferInstanceAs (Mono U.inclusion.hom.hom))
    exact ⟨(IsZero.of_mono_eq_zero U.inclusion hi).isTerminal⟩
  · intro h
    obtain ⟨t⟩ := h (geometricUnipotentRadical G) hr.1 hr.2.1
    exact ⟨t.uniqueUpToIso (Grp.isZero_trivial _).isTerminal⟩

private theorem reductive_baseChange_iff (e : F ≃+* E) (G : AffineAlgebraicGroup F) :
    letI := scalarStructure e
    IsReductive (baseChangedAlgebraicGroup E G) ↔ IsReductive G := by
  letI := scalarStructure e
  letI := scalarStructure (closureEquiv e)
  haveI := fieldSpecMap_isIso e
  haveI := fieldSpecMap_isIso (closureEquiv e)
  let G' := baseChangedAlgebraicGroup E G
  let H := baseChangedAlgebraicGroup (AlgebraicClosure E) (GeometricGroup G)
  let i : H.val ≅ (GeometricGroup G').val := (geometricBaseChangeIso e).app G.val
  apply and_congr (property_baseChange_iff @Smooth G.val.X)
  apply and_congr (property_baseChange_iff @GeometricallyConnected G.val.X)
  rw [trivialGeometricRadical_iff, trivialGeometricRadical_iff]
  exact (⟨hasOnlyTrivialUnipotentNormals_of_iso i.symm,
    hasOnlyTrivialUnipotentNormals_of_iso i⟩ :
      HasOnlyTrivialUnipotentNormals (GeometricGroup G') ↔ HasOnlyTrivialUnipotentNormals H).trans
    (hasOnlyTrivialUnipotentNormals_baseChange (E := AlgebraicClosure E) (GeometricGroup G))

set_option maxHeartbeats 450000 in
private theorem containsGeometricBorel_iff (e : F ≃+* E) (G : AffineAlgebraicGroup F)
    (P : ClosedSubgroup G.val) :
    letI := scalarStructure e
    Specs.BorelProper.ContainsGeometricBorel (transportedSubgroup F E P) ↔
      Specs.BorelProper.ContainsGeometricBorel P := by
  letI := scalarStructure e
  letI := scalarStructure (closureEquiv e)
  haveI := fieldSpecMap_isIso (closureEquiv e)
  let G' := baseChangedAlgebraicGroup E G
  let H := baseChangedAlgebraicGroup (AlgebraicClosure E) (GeometricGroup G)
  let P' : ClosedSubgroup G'.val := transportedSubgroup F E P
  let L : ClosedSubgroup (GeometricGroup G).val := transportedSubgroup F (AlgebraicClosure F) P
  let M : ClosedSubgroup (GeometricGroup G').val := transportedSubgroup E (AlgebraicClosure E) P'
  let N : ClosedSubgroup H.val := transportedSubgroup (AlgebraicClosure F) (AlgebraicClosure E) L
  let α := geometricBaseChangeIso e
  let i : H.val ≅ (GeometricGroup G').val := α.app G.val
  let j : N.group ≅ M.group := α.app P.group
  have hj : j.hom ≫ M.inclusion = N.inclusion ≫ i.hom :=
    (α.hom.naturality P.inclusion).symm
  have hj' : j.inv ≫ N.inclusion = M.inclusion ≫ i.inv :=
    (α.inv.naturality P.inclusion).symm
  have left : Specs.BorelProper.ContainsGeometricBorel P' ↔ HasBorelBelow M := by
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      exact ⟨M.isClosedImmersion, h⟩
  have right : Specs.BorelProper.ContainsGeometricBorel P ↔ HasBorelBelow L := by
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      exact ⟨L.isClosedImmersion, h⟩
  have step₁ : HasBorelBelow M ↔ HasBorelBelow N :=
    ⟨hasBorelBelow_of_iso (G := GeometricGroup G') (H := H) (P := M) (Q := N) i.symm j.symm hj',
     hasBorelBelow_of_iso (G := H) (H := GeometricGroup G') (P := N) (Q := M) i j hj⟩
  have step₂ : HasBorelBelow N ↔ HasBorelBelow L :=
    hasBorelBelow_baseChange_iff (E := AlgebraicClosure E) (G := GeometricGroup G) L
  exact left.trans (step₁.trans (step₂.trans right.symm))

end AlgebraicClosures

theorem parabolicTransport : ParabolicTransport.{u} := by
  intro F E _ _ e G P
  letI := scalarStructure e
  haveI := fieldSpecMap_isIso e
  exact and_congr (reductive_baseChange_iff e G)
    (and_congr (property_baseChange_iff @Smooth P.group.X) (containsGeometricBorel_iff e G P))

end

end LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
