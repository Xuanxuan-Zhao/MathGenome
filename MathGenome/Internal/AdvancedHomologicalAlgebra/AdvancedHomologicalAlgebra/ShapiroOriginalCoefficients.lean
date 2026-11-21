import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ShapiroOriginalCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.Shapiro
import Batteries.Tactic.OpenPrivate

/-! Carrier transport for Shapiro's lemma. -/
noncomputable section
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor
open scoped MonoidAlgebra ModuleCat.Algebra

namespace AdvancedHomologicalAlgebra.ShapiroOriginalCoefficients

open Specs.AdvancedHomologicalAlgebra
open Specs.AdvancedHomologicalAlgebra.ShapiroOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
open private barTermEquiv barTermEquiv_vertex barTermEquiv_boundary
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients

universe u v w
variable (k : Type u) (G : Type v) [CommRing k] [Group G]
variable (H : Subgroup G)

private lemma inclusion_scalar (r : k) :
    ringInclusion k G H (algebraMap k k[H] r) = algebraMap k k[G] r :=
  DFunLike.congr_fun (MonoidAlgebra.mapDomainRingHom_comp_algebraMap (R := k) (A := k) H.subtype) r

private lemma inclusion_single (h : H) :
    ringInclusion k G H (MonoidAlgebra.single h 1) = MonoidAlgebra.single (h : G) 1 :=
  MonoidAlgebra.mapDomain_single

theorem coinduction_formulas : OriginalCoinductionFormulas.{u,v,w} k G H :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-- The two original Hom modules are identified by lifting the values
of each linear map on the very same restricted group ring. -/
def homLift : homLiftType.{u,v,w} k G H := by
  refine NatIso.ofComponents (fun L => LinearEquiv.toModuleIso ?_) ?_
  · exact
      { toFun f := pointwiseHom k G H L f.down
        invFun f := ULift.up (ULift.moduleEquiv.toLinearMap.comp f)
        left_inv f := ULift.ext (LinearMap.ext fun _ => rfl)
        right_inv f := LinearMap.ext fun _ => rfl
        map_add' f g := LinearMap.ext fun _ => rfl
        map_smul' r f := LinearMap.ext fun _ => rfl }
  · intro L L' b
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    rfl

theorem homLift_pointwise : PointwiseHomLift k G H (homLift.{u,v,w} k G H) :=
  fun _ _ => rfl

private lemma coindHom_scalar (L : Coeff.{u,v,w} k H) (r : k)
    (f : CoindHom k G H L) (x : k[G]) :
    f (r • x) = r • f x := by
  have h : (show restrictedRing k G H from (r • x : k[G])) =
      (algebraMap k k[H] r) • (show restrictedRing k G H from x) := by
    change r • x = ringInclusion k G H (algebraMap k k[H] r) * x
    rw [inclusion_scalar, Algebra.smul_def]
  exact (congrArg f h).trans (f.map_smul (algebraMap k k[H] r) x)

private def restrictHomScalars {L : Coeff.{u,v,w} k H} (f : CoindHom k G H L) :
    k[G] →ₗ[k] L where
  toFun x := f x
  map_add' x y := f.map_add x y
  map_smul' r x := coindHom_scalar k G H L r f x

private lemma coindHom_ext {L : Coeff.{u,v,w} k H} {f f' : CoindHom k G H L}
    (h : ∀ g : G, f (MonoidAlgebra.single g 1) = f' (MonoidAlgebra.single g 1)) :
    f = f' := by
  have h' : restrictHomScalars k G H f = restrictHomScalars k G H f' := by
    apply MonoidAlgebra.lhom_ext'
    intro g
    apply LinearMap.ext_ring
    exact h g
  exact LinearMap.ext fun x => LinearMap.congr_fun h' x

private abbrev coefficientRep (L : Coeff.{u,v,w} k H) := (ambientRep k H).obj L
private abbrev coindRep (L : Coeff.{u,v,w} k H) := (ambientRep k G).obj ((coinduction k G H).obj L)

private lemma eval_equivariant (L : Coeff.{u,v,w} k H)
    (f : CoindHom k G H L) (h : H) (g : G) :
    f (MonoidAlgebra.single ((h : G) * g) 1) =
      MonoidAlgebra.single h (1 : k) • f (MonoidAlgebra.single g 1) := by
  rw [← f.map_smul]
  congr 1
  change MonoidAlgebra.single ((h : G) * g) 1 =
    ringInclusion k G H (MonoidAlgebra.single h 1) * MonoidAlgebra.single g 1
  rw [inclusion_single, MonoidAlgebra.single_mul_single, one_mul]

private def extend (L : Coeff.{u,v,w} k H)
    (f : Shapiro.coind.{u,v,w} k G H (coefficientRep k G H L)) : k[G] →ₗ[k] L :=
  Finsupp.linearCombination k (fun g => (f.val g).down) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

private lemma extend_single (L : Coeff.{u,v,w} k H)
    (f : Shapiro.coind.{u,v,w} k G H (coefficientRep k G H L)) (g : G) :
    extend k G H L f (MonoidAlgebra.single g 1) = (f.val g).down := by
  simp [extend]

private def extendHom (L : Coeff.{u,v,w} k H)
    (f : Shapiro.coind.{u,v,w} k G H (coefficientRep k G H L)) : CoindHom k G H L where
  toFun := extend k G H L f
  map_add' := (extend k G H L f).map_add
  map_smul' r x := by
    change k[G] at x
    change extend k G H L f (ringInclusion k G H r * x) = r • extend k G H L f x
    induction r using MonoidAlgebra.induction_on with
    | of h =>
        change extend k G H L f
          (ringInclusion k G H (MonoidAlgebra.single h 1) * x) =
          MonoidAlgebra.single h (1 : k) • extend k G H L f x
        rw [inclusion_single]
        induction x using MonoidAlgebra.induction_on with
        | of g =>
            change extend k G H L f (MonoidAlgebra.single (h : G) 1 *
                MonoidAlgebra.single g 1) =
              MonoidAlgebra.single h (1 : k) • extend k G H L f (MonoidAlgebra.single g 1)
            rw [MonoidAlgebra.single_mul_single, one_mul, extend_single, extend_single]
            exact congrArg ULift.down (f.property h g)
        | add x y hx hy => simp only [mul_add, _root_.map_add, smul_add, hx, hy]
        | smul r x hx => rw [mul_smul_comm, _root_.map_smul, hx, _root_.map_smul, smul_comm]
    | add x y hx hy => simp only [_root_.map_add, add_mul, add_smul, hx, hy]
    | smul r s hs =>
        have hscalar : ringInclusion k G H (r • s) = r • ringInclusion k G H s := by
          rw [Algebra.smul_def, map_mul, inclusion_scalar, ← Algebra.smul_def]
        rw [hscalar, smul_mul_assoc, _root_.map_smul, hs, smul_assoc]

private def coindLiftLinear (L : Coeff.{u,v,w} k H) :
    coindRep k G H L ≃ₗ[k] Shapiro.coind.{u,v,w} k G H (coefficientRep k G H L) where
  toFun f := ⟨fun g => ULift.up ((f.down : CoindHom k G H L) (MonoidAlgebra.single g 1)),
    fun h g => congrArg ULift.up (eval_equivariant k G H L f.down h g)⟩
  invFun f := ULift.up (extendHom k G H L f)
  left_inv f := by
    apply ULift.ext
    apply coindHom_ext k G H
    intro g
    exact extend_single k G H L _ g
  right_inv f := by
    apply Subtype.ext
    funext g
    exact congrArg ULift.up (extend_single k G H L f g)
  map_add' _ _ := rfl
  map_smul' r f := by
    apply Subtype.ext
    funext g
    apply ULift.ext
    change (f.down : CoindHom k G H L) (MonoidAlgebra.single g 1 * algebraMap k k[G] r) =
      r • (f.down : CoindHom k G H L) (MonoidAlgebra.single g 1)
    rw [← Algebra.commutes, ← Algebra.smul_def, coindHom_scalar]

/-- The coefficient comparison lifts the value of each group-algebra map
at the same basis vector. -/
def coindLift : coindLiftType.{u,v,w} k G H :=
  NatIso.ofComponents (fun L => Rep.mkIso (Representation.Equiv.mk (coindLiftLinear k G H L) fun g => by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    apply ULift.ext
    change (f.down : CoindHom k G H L) (MonoidAlgebra.single x 1 * MonoidAlgebra.single g 1) =
      (f.down : CoindHom k G H L) (MonoidAlgebra.single (x * g) 1)
    rw [MonoidAlgebra.single_mul_single, one_mul]))
    (fun b => by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.toLinearMap_injective
      apply LinearMap.ext
      intro f
      rfl)

theorem coindLift_pointwise : PointwiseCoind k G H (homLift.{u,v,w} k G H)
    (coindLift.{u,v,w} k G H) :=
  fun _ _ _ => rfl

theorem coindLift_evaluation : LiftEvaluation k G H (coindLift.{u,v,w} k G H) :=
  fun _ _ => rfl

variable {H}

/-- In each degree the inverse of the pointwise descent lifts the value on
every original bar tuple. -/
private def liftCochain (M : Coeff.{u,v,w} k G) (n : ℕ) :
    Cochain k G M n ≃ₗ[k] (GroupBar.Large.B.{u,v,max u v w} k G n ⟶ (ambientRep k G).obj M) :=
  let e := (barTermEquiv.{u,v,max u v w} k G n).symm
  let i : M ≃ₗ[k[G]] (lift k G).obj M := ULift.moduleEquiv.symm
  let c : Cochain k G M n ≃ₗ[k] _ :=
    { __ := LinearEquiv.arrowCongrAddEquiv e i
      map_smul' _ _ := rfl }
  let h : Cochain k G M n ≃ₗ[k]
      (Rep.toModuleMonoidAlgebra.obj (GroupBar.Large.B.{u,v,max u v w} k G n) ⟶
        (lift k G).obj M) :=
    c.trans ModuleCat.homLinearEquiv.symm
  h.trans
    { (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)).toAdjunction.homEquiv
        (GroupBar.Large.B.{u,v,max u v w} k G n) ((lift k G).obj M) with
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

private lemma liftCochain_apply (M : Coeff.{u,v,w} k G) (n : ℕ)
    (φ : Cochain k G M n) (c : Fin (n+1) → G) :
    ((liftCochain k G M n) φ).hom (GroupBar.Large.single.{u,v,max u v w} k G c 1) =
      ULift.up (φ (basisElement k G n c)) := by
  change ULift.up (φ (barTermEquiv.{u,v,max u v w} k G n
    ((GroupBar.Large.B.{u,v,max u v w} k G n).ρ.asModuleEquiv.symm
      (GroupBar.Large.single.{u,v,max u v w} k G c 1)))) = _
  rw [barTermEquiv_vertex]

/-- The comparison with the ambient cochain complex descends values on the
original bar terms and is natural in the coefficient. -/
def barTransport : originalBarTransport.{u,v,w} k G := by
  refine (NatIso.ofComponents (fun M => HomologicalComplex.Hom.isoOfComponents
    (fun n => (liftCochain k G M n).toModuleIso) ?_) ?_).symm
  · intro i j hij
    have h : j = i+1 := hij.symm
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    let f : Cochain k G M i := φ
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.toLinearMap_injective
    apply LinearMap.ext
    intro x
    symm
    simp only [originalHomogeneous, homogeneousComplex, CochainComplex.of_d]
    change ULift.up (f (((originalBar k G).d (i+1) i).hom
        (barTermEquiv k G (i+1) ((GroupBar.Large.B.{u,v,max u v w} k G (i+1)).ρ.asModuleEquiv.symm x)))) =
      ULift.up (f (barTermEquiv k G i (Rep.toModuleMonoidAlgebra.map
        (GroupBar.Large.boundary.{u,v,max u v w} k G i)
        ((GroupBar.Large.B.{u,v,max u v w} k G (i+1)).ρ.asModuleEquiv.symm x))))
    rw [barTermEquiv_boundary]
  · intro M N b
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    rfl

theorem barTransport_pointwise : PointwiseBar k G (barTransport.{u,v,w} k G) := by
  intro M n φ c
  obtain ⟨ψ, rfl⟩ := (liftCochain k G M n).surjective φ
  change (liftCochain k G M n).symm (liftCochain k G M n ψ) (basisElement k G n c) = _
  rw [LinearEquiv.symm_apply_apply, liftCochain_apply]

section Inhomogeneous

open AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
  (originalBarCoordinates originalBarCoordinates_apply originalBarCoordinates_d
    squareZero rawHomologyLiftIso)

/-- The original Hom complex in the inhomogeneous coordinates of group
cohomology, presented in the same scalar category by the exact carrier lift. -/
def inhomogeneousCoordinates :
    originalHomogeneous.{u,v,w} k G ≅ rawLifted.{u,v,w} k G (squareZero k G) := by
  let term (M : Coeff.{u,v,w} k G) (n : ℕ) :
      Cochain k G M n ≃ₗ[k] ULift.{u} (TupleCochain k G M n) :=
    (originalBarCoordinates k G M n).trans ULift.moduleEquiv.symm
  refine NatIso.ofComponents (fun M => HomologicalComplex.Hom.isoOfComponents
    (fun n => (term M n).toModuleIso) ?_) ?_
  · intro i j hij
    obtain rfl : j = i + 1 := hij.symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    simp only [rawLifted, rawFunctor, Functor.comp_obj, Functor.mapHomologicalComplex_obj_d,
      rawComplex, originalHomogeneous, homogeneousComplex, CochainComplex.of_d]
    change ULift.up (differential k G M i (originalBarCoordinates k G M i f)) =
      ULift.up (originalBarCoordinates k G M (i+1)
        (f.comp ((originalBar k G).d (i+1) i).hom))
    rw [originalBarCoordinates_d]
  · intro M N b
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply ULift.ext
    funext g
    change b.hom (originalBarCoordinates k G M n f g) =
      originalBarCoordinates k G N n (b.hom.comp f) g
    rw [originalBarCoordinates_apply, originalBarCoordinates_apply]
    rfl

lemma inhomogeneousCoordinates_apply (M : Coeff.{u,v,w} k G) (n : ℕ)
    (f : Cochain k G M n) (g : Fin n → G) :
    ((((inhomogeneousCoordinates k G).hom.app M).f n).hom f).down g =
      f (basisElement k G n (Fin.partialProd g)) :=
  originalBarCoordinates_apply k G M n f g

/-- The cohomology of the original Hom complex identifies with the scalar lift
of the cohomology of the original inhomogeneous cochains. -/
def inhomogeneousCohomologyIso (n : ℕ) :
    originalCohomology.{u,v,w} k G n ≅
      rawCohomology k G (squareZero k G) n ⋙ scalarLift.{u,v,w} k :=
  isoWhiskerRight (inhomogeneousCoordinates k G) (homologyAt.{u,v,w} k n) ≪≫
    rawHomologyLiftIso k G n

end Inhomogeneous

variable (H)

variable (A : Specs.AdvancedHomologicalAlgebra.Shapiro.ShapiroData.{u,v,max u v w} k G H)

/-- Restrict and evaluate on the original homogeneous cochains. -/
def comparison : coinduction.{u,v,w} k G H ⋙ originalHomogeneous k G ⟶
    originalHomogeneous k H :=
  (isoWhiskerLeft (coinduction k G H) (barTransport k G).symm).hom ≫
    (associator _ _ _).inv ≫
    (isoWhiskerRight (coindLift.{u,v,w} k G H) _).hom ≫
    (associator _ _ _).hom ≫
    whiskerLeft (ambientRep k H) A.cochain ≫
    (barTransport k H).hom

theorem comparison_formula : RestrictEvaluate k G H (comparison.{u,v,w} k G H A) := by
  intro L n φ c
  let ψ := liftCochain k G ((coinduction k G H).obj L) n φ
  let b := (coindLift.{u,v,w} k G H).hom.app L
  let χ := ψ ≫ b
  let η := A.cochain.app (coefficientRep k G H L)
  change (show Cochain k H L n from (((barTransport k H).hom.app L).f n).hom ((η.f n).hom χ))
      (basisElement k H n c) = _
  rw [barTransport_pointwise]
  have hη : η.f n = ((Shapiro.comparison.{u,v,max u v w} k G H).app
      (coefficientRep k G H L)).f n :=
    (A.component _ n).trans (Shapiro.comparison_component k G H _ n).symm
  rw [hη]
  change (((((Shapiro.comparison.{u,v,max u v w} k G H).app
    (coefficientRep k G H L)).f n).hom χ).hom
      (GroupBar.Large.single k H c 1)).down = _
  rw [Shapiro.comparison_formula]
  change (((b.hom (ψ.hom (GroupBar.Large.single k G (fun i => (c i : G)) 1))).val 1).down) = _
  change ((ψ.hom (GroupBar.Large.single k G (fun i => (c i : G)) 1)).down :
    CoindHom k G H L) (MonoidAlgebra.single 1 1) = _
  dsimp only [ψ]
  rw [liftCochain_apply, ← MonoidAlgebra.one_def]

private theorem transported_comparison (n : ℕ) :
    (transportedDerived k G H A (coindLift.{u,v,w} k G H) n).hom ≫
      (transportedBar k A.targetBar (barTransport k H) n).hom =
    whiskerLeft (coinduction k G H)
      (transportedBar k A.sourceBar (barTransport k G) n).hom ≫
      whiskerRight (comparison.{u,v,w} k G H A) (homologyAt.{u,v,w} k n) := by
  apply NatTrans.ext
  funext L
  let Y := (ambientRep k H).obj L
  let X := (ambientRep k G).obj ((coinduction k G H).obj L)
  let e : X ⟶ (Shapiro.coindFunctor k G H).obj Y := (coindLift k G H).hom.app L
  let a := (A.sourceBar.iso n).hom
  let F := homologyAt.{u,v,w} k n
  let D := Shapiro.derivedCohomology.{u,v,max u v w} k G n
  let η := F.map (A.cochain.app Y)
  let p := F.map ((barTransport k H).hom.app L)
  have h := NatTrans.congr_app (A.comparison n) Y
  change (A.derivedIso n).hom.app Y ≫ (A.targetBar.iso n).hom.app Y =
    a.app _ ≫ η at h
  have h₁ := congrArg (fun f => D.map e ≫ f ≫ p) h
  have h₂ := a.naturality_assoc e (η ≫ p)
  have h₃ : D.map e ≫ (A.derivedIso n).hom.app Y ≫ (A.targetBar.iso n).hom.app Y ≫ p =
      a.app X ≫ (Shapiro.homogeneousCohomology.{u,v,max u v w} k G n).map e ≫ η ≫ p := by
    simpa only [Category.assoc] using h₁.trans (by simpa only [Category.assoc] using h₂)
  simp [transportedDerived, transportedBar, comparison, Category.assoc]
  exact h₃

theorem comparison_quasiIso (L : Coeff.{u,v,w} k H) :
    QuasiIso ((comparison.{u,v,w} k G H A).app L) := by
  constructor
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let e := transportedDerived k G H A (coindLift.{u,v,w} k G H) n
  let a := transportedBar.{u,v,max u v w} k A.sourceBar (barTransport k G) n
  let b := transportedBar.{u,v,w} k A.targetBar (barTransport k H) n
  let f := HomologicalComplex.homologyMap ((comparison.{u,v,w} k G H A).app L) n
  have h : e.hom.app L ≫ b.hom.app L =
      a.hom.app ((coinduction k G H).obj L) ≫ f :=
    NatTrans.congr_app (transported_comparison k G H A n) L
  have : IsIso (a.hom.app ((coinduction k G H).obj L) ≫ f) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_left (a.hom.app ((coinduction k G H).obj L)) f

/-- Natural Shapiro isomorphisms with the original homogeneous comparison
and the transported, augmentation-normalized bar comparisons. -/
def transportShapiroData : OriginalShapiroData.{u,v,w} k G H A where
  coind_formulas := coinduction_formulas k G H
  homLift := homLift k G H
  hom_pointwise := homLift_pointwise k G H
  coindLift := coindLift k G H
  coind_pointwise := coindLift_pointwise k G H
  evaluation := coindLift_evaluation k G H
  sourceCochains := barTransport k G
  source_pointwise := barTransport_pointwise k G
  targetCochains := barTransport k H
  target_pointwise := barTransport_pointwise k H
  cochain := comparison k G H A
  cochain_formula := comparison_formula k G H A
  cochain_quasiIso := comparison_quasiIso k G H A
  comparison := transported_comparison k G H A

/-- Specialization to the very same normalized Shapiro data fixed by HA-A04. -/
def originalShapiroData :
    OriginalShapiroData.{u,v,w} k G H (Shapiro.shapiroData.{u,v,max u v w} k G H) :=
  transportShapiroData k G H (Shapiro.shapiroData.{u,v,max u v w} k G H)

theorem originalShapiro : originalShapiroExpected.{u,v,w} :=
  fun k G _ _ H =>
    ⟨⟨⟨Shapiro.shapiroData k G H, originalShapiroData k G H⟩⟩,
      fun A => ⟨transportShapiroData k G H A⟩⟩

namespace Mixed

open Specs.AdvancedHomologicalAlgebra.ShapiroOriginalCoefficients.Mixed
open AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients

universe a b s

private lemma cochain_ext (M : Coeff.{u,v,a} k G) (n : ℕ) {z z' : Cochain k G M n}
    (h : ∀ c, z (basisElement k G n c) = z' (basisElement k G n c)) : z = z' := by
  apply (originalBarCoordinates k G M n).injective
  funext g
  rw [originalBarCoordinates_apply, originalBarCoordinates_apply]
  exact h _

/-- Postcomposition by a coefficient equivalence gives the comparison with
the scalar lift of the original bar Hom complex. -/
private def cochainLift (M : Coeff.{u,v,a} k G) (N : Coeff.{u,v,max u v a s} k G)
    (e : M ≃ₗ[k[G]] N) : CochainLift.{u,v,a,s} k G M N e := by
  let term (n : ℕ) : ULift.{s} (Cochain k G M n) ≃ₗ[k] Cochain k G N n :=
    { toFun z := e.toLinearMap.comp z.down
      invFun z := ULift.up (e.symm.toLinearMap.comp z)
      left_inv z := ULift.ext (LinearMap.ext fun x => e.symm_apply_apply (z.down x))
      right_inv z := LinearMap.ext fun x => e.apply_symm_apply (z x)
      map_add' _ _ := LinearMap.comp_add _ _ _
      map_smul' _ _ := LinearMap.comp_smul e.toLinearMap _ _ }
  refine ⟨HomologicalComplex.Hom.isoOfComponents (fun n => (term n).toModuleIso) ?_, ?_⟩
  · intro i j hij
    obtain rfl : j = i + 1 := hij.symm
    simp only [liftedComplex, Functor.mapHomologicalComplex_obj_d, homogeneousComplex,
      CochainComplex.of_d]
    rfl
  · intros
    rfl

private def coindCoefficientLift (L : Coeff.{u,v,a} k H) :
    (coinduction k G H).obj L ≃ₗ[k[G]]
      (coinduction k G H).obj (largerCoefficient.{u,v,a,max u v a s} k H L) where
  toFun z := ULift.moduleEquiv.symm.toLinearMap.comp (show CoindHom k G H L from z)
  invFun z := ULift.moduleEquiv.toLinearMap.comp
    (show CoindHom k G H (largerCoefficient.{u,v,a,max u v a s} k H L) from z)
  left_inv _ := LinearMap.ext fun _ => rfl
  right_inv _ := LinearMap.ext fun _ => rfl
  map_add' _ _ := LinearMap.comp_add _ _ _
  map_smul' _ _ := rfl

private def comparisonLift (L : Coeff.{u,v,a} k H) : CoindLift.{u,v,a,s} k G H L where
  coeff := coindCoefficientLift.{u,v,a,s} k G H L
  pointwise _ _ := rfl
  source := cochainLift.{u,v,max u v a,s} k G _ _ _
  target := cochainLift.{u,v,a,s} k H L
    (largerCoefficient.{u,v,a,max u v a s} k H L) ULift.moduleEquiv.symm

private lemma scalarMap_homology
    {M N : CochainComplex (ModuleCat.{max u v a} k) ℕ} (f : M ⟶ N)
    (n : ℕ) (x : M.homology n) :
    (((N.sc n).mapHomologyIso (Mixed.scalarLift.{u,v,a,s} k)).inv).hom
        (ULift.up ((HomologicalComplex.homologyMap f n).hom x)) =
      (HomologicalComplex.homologyMap (scalarMap.{u,v,a,s} k f) n).hom
        ((((M.sc n).mapHomologyIso (Mixed.scalarLift.{u,v,a,s} k)).inv).hom (ULift.up x)) := by
  let F := Mixed.scalarLift.{u,v,a,s} k
  have h := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) n).map f) F
  exact congrArg (fun g => g.hom (ULift.up x)) h

private lemma lift_comparison (L : Coeff.{u,v,a} k H)
    {A : Shapiro.ShapiroData.{u,v,max u v a} k G H}
    (D : OriginalShapiroData.{u,v,a} k G H A)
    {B : Shapiro.ShapiroData.{u,v,max u v a s} k G H}
    (E : OriginalShapiroData.{u,v,max u v a s} k G H B) :
    scalarMap.{u,v,a,s} k (D.cochain.app L) ≫ (comparisonLift.{u,v,a,s} k G H L).target.iso.hom =
      (comparisonLift.{u,v,a,s} k G H L).source.iso.hom ≫ E.cochain.app _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨z⟩
  apply cochain_ext k H _ n
  intro t
  let z' := (coindCoefficientLift.{u,v,a,s} k G H L).toLinearMap.comp z
  change ULift.up ((show Cochain k H L n from ((D.cochain.app L).f n).hom z)
      (basisElement k H n t)) =
    (show Cochain k H _ n from ((E.cochain.app _).f n).hom z') (basisElement k H n t)
  rw [D.cochain_formula L n z t, E.cochain_formula _ n z' t]
  rfl

theorem naturality : naturalityExpected.{u,v,a,b,s} := by
  intro k G _ _ H L L' f A A' D D'
  let S := scalarMap.{u,v,a,max u v a b s} k (D.cochain.app L)
  let T := scalarMap.{u,v,b,max u v a b s} k (D'.cochain.app L')
  let c := coindPost k G H f
  let p := postChain.{u,v,max u v a,max u v b,s} k G c
  let q := postChain.{u,v,a,b,max u v s} k H f
  have h : S ≫ q = p ≫ T := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨z⟩
    apply ULift.ext
    apply cochain_ext k H L' n
    intro t
    change f ((show Cochain k H L n from ((D.cochain.app L).f n).hom z)
        (basisElement k H n t)) =
      (show Cochain k H L' n from ((D'.cochain.app L').f n).hom (c.comp z))
        (basisElement k H n t)
    rw [D.cochain_formula L n z t, D'.cochain_formula L' n (c.comp z) t]
    rfl
  refine ⟨h, ?_, ?_⟩
  · intro n x
    let i := homologyLift.{u,v,max u v a,max u v a b s} k G ((coinduction k G H).obj L) n
    let i' := homologyLift.{u,v,max u v b,max u v a b s} k G ((coinduction k G H).obj L') n
    let j := homologyLift.{u,v,a,max u v a b s} k H L n
    let j' := homologyLift.{u,v,b,max u v a b s} k H L' n
    let pH := (HomologicalComplex.homologyMap p n).hom
    let qH := (HomologicalComplex.homologyMap q n).hom
    let d := (HomologicalComplex.homologyMap (D.cochain.app L) n).hom
    let d' := (HomologicalComplex.homologyMap (D'.cochain.app L') n).hom
    change j'.symm (qH (j (d x))) = d' (i'.symm (pH (i x)))
    apply j'.injective
    rw [LinearEquiv.apply_symm_apply]
    have hj := scalarMap_homology.{u,v,b,max u v a b s} k (D'.cochain.app L') n
      (i'.symm (pH (i x)))
    change j' (d' _) = (HomologicalComplex.homologyMap T n).hom (i' _) at hj
    rw [LinearEquiv.apply_symm_apply] at hj
    have hi := scalarMap_homology.{u,v,a,max u v a b s} k (D.cochain.app L) n x
    change j (d x) = (HomologicalComplex.homologyMap S n).hom (i x) at hi
    rw [hj, hi]
    have hh := congrArg (fun m => HomologicalComplex.homologyMap m n) h
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hh
    exact congrArg (fun m => m.hom (i x)) hh
  · intro B E
    refine ⟨comparisonLift.{u,v,a,max u v a b s} k G H L,
      comparisonLift.{u,v,b,max u v a b s} k G H L',
      lift_comparison.{u,v,a,max u v a b s} k G H L D E,
      lift_comparison.{u,v,b,max u v a b s} k G H L' D' E, ?_, ?_⟩
    · apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨z⟩
      rfl
    · apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨z⟩
      rfl

end Mixed

end AdvancedHomologicalAlgebra.ShapiroOriginalCoefficients
