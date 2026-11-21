import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupExtensionOriginalCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupHochschildSerre
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
import Batteries.Tactic.OpenPrivate

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large
open Specs.AdvancedHomologicalAlgebra.GroupExtensionOriginalCoefficients
open scoped MonoidAlgebra

namespace AdvancedHomologicalAlgebra.GroupExtensionOriginalCoefficients

universe u v w s x
variable {k : Type u} [CommRing k] {G : Type v} [Group G]

private def extendLinear {L : Rep.{max u v w} k G} (n : ℕ) (f : cochains L n) :
    GroupBar.Large.B.{u,v,w} k G n →ₗ[k] L :=
  (Finsupp.linearCombination k (fun c : ULift.{w} (Fin (n+1) → G) => f.val c.down)).comp
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

private lemma extendLinear_single {L : Rep.{max u v w} k G} (n : ℕ) (f : cochains L n)
    (c : Fin (n+1) → G) (r : k) :
    extendLinear n f (GroupBar.Large.single.{u,v,w} k G c r) = r • f.val c :=
  Finsupp.linearCombination_single _ _ _

private def extend {L : Rep.{max u v w} k G} (n : ℕ) (f : cochains L n) :
    GroupBar.Large.B.{u,v,w} k G n ⟶ L :=
  Rep.ofHom ⟨extendLinear n f, fun g => by
    apply MonoidAlgebra.lhom_ext'
    rintro ⟨c⟩
    apply LinearMap.ext_ring
    change extendLinear n f ((GroupBar.Large.B.{u,v,w} k G n).ρ g
      (GroupBar.Large.single k G c 1)) = L.ρ g (extendLinear n f (GroupBar.Large.single k G c 1))
    rw [GroupBar.Large.diagonal_action, extendLinear_single, extendLinear_single,
      one_smul, one_smul, equivariant]⟩

/-- Evaluation on all homogeneous vertices, with inverse given by linear extension. -/
def barEvaluation (L : Rep.{max u v w} k G) (n : ℕ) :
    ((repHomogeneousFunctor.{u,v,w} k G).obj L).X n ≃ₗ[k] cochains L n where
  toFun φ :=
    let ψ : GroupBar.Large.B.{u,v,w} k G n ⟶ L := φ
    ⟨fun c => ψ.hom (GroupBar.Large.single.{u,v,w} k G c 1), fun g c => by
      change ψ.hom (GroupBar.Large.single.{u,v,w} k G (fun i => g * c i) 1) =
        L.ρ g (ψ.hom (GroupBar.Large.single.{u,v,w} k G c 1))
      exact (congrArg ψ.hom (GroupBar.Large.diagonal_action k G n g c 1)).symm.trans
        (Rep.hom_comm_apply ψ g (GroupBar.Large.single.{u,v,w} k G c 1))⟩
  invFun := extend n
  left_inv φ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.toLinearMap_injective
    apply MonoidAlgebra.lhom_ext'
    rintro ⟨c⟩
    apply LinearMap.ext_ring
    change extendLinear n _ (GroupBar.Large.single.{u,v,w} k G c 1) =
      φ.hom (GroupBar.Large.single.{u,v,w} k G c 1)
    rw [extendLinear_single, one_smul]
    rfl
  right_inv f := by
    apply Subtype.ext
    funext c
    change extendLinear n f (GroupBar.Large.single.{u,v,w} k G c 1) = f.val c
    rw [extendLinear_single, one_smul]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma barEvaluation_apply (L : Rep.{max u v w} k G) (n : ℕ)
    (φ : ((repHomogeneousFunctor.{u,v,w} k G).obj L).X n) (c : Fin (n+1) → G) :
    (barEvaluation L n φ).val c = φ.hom (GroupBar.Large.single k G c 1) :=
  rfl

lemma barEvaluation_d (L : Rep.{max u v w} k G) (n : ℕ)
    (φ : ((repHomogeneousFunctor.{u,v,w} k G).obj L).X n) :
    barEvaluation L (n+1) ((((repHomogeneousFunctor k G).obj L).d n (n+1)).hom φ) =
      differential L n (barEvaluation L n φ) := by
  apply Subtype.ext
  funext c
  change φ.hom ((GroupBar.Large.d.{u,v,w} k G n) (GroupBar.Large.single k G c 1)) = _
  rw [GroupBar.Large.boundary_single]
  simp only [one_mul, _root_.map_sum, differential_apply, barEvaluation_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← _root_.map_smul]
  congr 1
  rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]

private lemma liftCoeffEquiv_naturality {M L : Rep.{w} k G} (f : M ⟶ L) (m : M) :
    liftCoeffEquiv.{u,v,w,s} L (f.hom m) = ((coefficientLift.{u,v,w,s} k G).map f).hom (liftCoeffEquiv.{u,v,w,s} M m) :=
  rfl

/-- A coefficient equivalence intertwining the actions transports cochains
pointwise. The two representations may live in different universes. -/
def changeCoefficient {M : Rep.{w} k G} {L : Rep.{x} k G}
    (e : M ≃ₗ[k] L) (he : ∀ g m, e (M.ρ g m) = L.ρ g (e m)) (n : ℕ) :
    cochains M n ≃ₗ[k] cochains L n where
  toLinearMap := pullbackDegree (MonoidHom.id G) e.toLinearMap he n
  invFun := pullbackDegree (MonoidHom.id G) e.symm.toLinearMap (fun g m =>
    e.injective (by simp only [LinearEquiv.coe_toLinearMap, MonoidHom.id_apply,
      LinearEquiv.apply_symm_apply, he])) n
  left_inv f := by
    apply Subtype.ext
    funext c
    exact e.symm_apply_apply (f.val c)
  right_inv f := by
    apply Subtype.ext
    funext c
    exact e.apply_symm_apply (f.val c)

lemma changeCoefficient_apply {M : Rep.{w} k G} {L : Rep.{x} k G}
    (e : M ≃ₗ[k] L) (he : ∀ g m, e (M.ρ g m) = L.ρ g (e m)) (n : ℕ)
    (f : cochains M n) (c : Fin (n+1) → G) :
    (changeCoefficient e he n f).val c = e (f.val c) :=
  rfl

lemma changeCoefficient_d {M : Rep.{w} k G} {L : Rep.{x} k G}
    (e : M ≃ₗ[k] L) (he : ∀ g m, e (M.ρ g m) = L.ρ g (e m)) (n : ℕ)
    (f : cochains M n) :
    changeCoefficient e he (n+1) (differential M n f) =
      differential L n (changeCoefficient e he n f) := by
  apply Subtype.ext
  funext c
  simp only [changeCoefficient_apply, differential_apply, _root_.map_sum, _root_.map_smul]

private def intoBar {M : Rep.{w} k G} {L : Rep.{max u v w s} k G} (e : M ≃ₗ[k] L)
    (he : ∀ g m, e (M.ρ g m) = L.ρ g (e m)) (n : ℕ) :
    cochains M n ≃ₗ[k] ((repHomogeneousFunctor.{u,v,max w s} k G).obj L).X n :=
  (changeCoefficient e he n).trans (barEvaluation.{u,v,max w s} L n).symm

private lemma intoBar_apply {M : Rep.{w} k G} {L : Rep.{max u v w s} k G} (e : M ≃ₗ[k] L)
    (he : ∀ g m, e (M.ρ g m) = L.ρ g (e m)) (n : ℕ) (f : cochains M n) (c : Fin (n+1) → G) :
    (intoBar.{u,v,w,s} e he n f).hom (GroupBar.Large.single k G c 1) = e (f.val c) := by
  change (barEvaluation.{u,v,max w s} L n ((barEvaluation.{u,v,max w s} L n).symm _)).val c = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

private lemma intoBar_d {M : Rep.{w} k G} {L : Rep.{max u v w s} k G} (e : M ≃ₗ[k] L)
    (he : ∀ g m, e (M.ρ g m) = L.ρ g (e m)) (n : ℕ) (f : cochains M n) :
    intoBar.{u,v,w,s} e he (n+1) (differential M n f) =
      (((repHomogeneousFunctor.{u,v,max w s} k G).obj L).d n (n+1)).hom (intoBar.{u,v,w,s} e he n f) := by
  apply (barEvaluation.{u,v,max w s} L (n+1)).injective
  rw [barEvaluation_d.{u,v,max w s}, show barEvaluation.{u,v,max w s} L (n+1) (intoBar.{u,v,w,s} e he (n+1) _) =
    changeCoefficient e he (n+1) (differential M n f) from LinearEquiv.apply_symm_apply _ _,
    show barEvaluation.{u,v,max w s} L n (intoBar.{u,v,w,s} e he n f) = changeCoefficient e he n f from
      LinearEquiv.apply_symm_apply _ _, changeCoefficient_d]

theorem squareZero : squareZeroExpected.{u,v,w} := by
  intro k G _ _ M n
  let e := liftCoeffEquiv.{u,v,w,0} M
  let h := liftCoeffEquiv_action.{u,v,w,0} M
  apply LinearMap.ext
  intro f
  apply (intoBar.{u,v,w,0} e h (n+2)).injective
  change intoBar.{u,v,w,0} e h (n+2) (differential M (n+1) (differential M n f)) =
    intoBar.{u,v,w,0} e h (n+2) 0
  rw [intoBar_d.{u,v,w,0}, intoBar_d.{u,v,w,0}, map_zero]
  exact congrArg (fun t => t.hom (intoBar.{u,v,w,0} e h n f))
    (((repHomogeneousFunctor.{u,v,w} k G).obj ((coefficientLift.{u,v,w,0} k G).obj M)).d_comp_d n (n+1) (n+2))

/-- The comparison chain isomorphism for an equivariant coefficient equivalence. -/
def compareComplex (h : SquareZero.{u,v,w} k G)
    {M : Rep.{w} k G} {L : Rep.{max u v w s} k G} (e : M ≃ₗ[k] L)
    (he : ∀ g m, e (M.ρ g m) = L.ρ g (e m)) :
    ((scalarLift.{u,v,w,s} k).mapHomologicalComplex (.up ℕ)).obj (complex h M) ≅
      (repHomogeneousFunctor.{u,v,max w s} k G).obj L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (ULift.moduleEquiv.trans (intoBar.{u,v,w,s} e he n)).toModuleIso)
    (by
      intro i j hij
      have hji : j = i+1 := hij.symm
      subst j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨f⟩
      change _ = intoBar.{u,v,w,s} e he (i+1) (((complex h M).d i (i+1)).hom f)
      have hd : ((complex h M).d i (i+1)).hom f = differential M i f := by
        simp only [complex, CochainComplex.of_d]
        rfl
      rw [hd]
      exact (intoBar_d.{u,v,w,s} e he i f).symm)

lemma compareComplex_apply (h : SquareZero.{u,v,w} k G)
    {M : Rep.{w} k G} {L : Rep.{max u v w s} k G} (e : M ≃ₗ[k] L)
    (he : ∀ g m, e (M.ρ g m) = L.ρ g (e m)) (n : ℕ) (f : cochains M n)
    (c : Fin (n+1) → G) :
    ((((compareComplex.{u,v,w,s} h e he).hom.f n).hom (ULift.up f)).hom
      (GroupBar.Large.single k G c 1)) = e (f.val c) :=
  intoBar_apply.{u,v,w,s} e he n f c

/-- Naturality holds on the original cochains by equality on every tuple. -/
def pointwiseIso (h : SquareZero.{u,v,w} k G) :
    liftedFunctor.{u,v,w,s} h ≅ coefficientLift.{u,v,w,s} k G ⋙ repHomogeneousFunctor.{u,v,max w s} k G :=
  NatIso.ofComponents (fun M => compareComplex.{u,v,w,s} h (liftCoeffEquiv.{u,v,w,s} M) (liftCoeffEquiv_action.{u,v,w,s} M))
    (by
      intro M L f
      apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨φ⟩
      apply (barEvaluation.{u,v,max w s} ((coefficientLift.{u,v,w,s} k G).obj L) n).injective
      apply Subtype.ext
      funext c
      change (((compareComplex.{u,v,w,s} h (liftCoeffEquiv.{u,v,w,s} L) (liftCoeffEquiv_action.{u,v,w,s} L)).hom.f n).hom
        (ULift.up ((pullbackDegree (MonoidHom.id G) f.hom.toLinearMap
          (fun g m => Rep.hom_comm_apply f g m) n) φ))).hom
          (GroupBar.Large.single k G c 1) =
        ((coefficientLift.{u,v,w,s} k G).map f).hom
          ((((compareComplex.{u,v,w,s} h (liftCoeffEquiv.{u,v,w,s} M) (liftCoeffEquiv_action.{u,v,w,s} M)).hom.f n).hom
            (ULift.up φ)).hom (GroupBar.Large.single k G c 1))
      rw [compareComplex_apply.{u,v,w,s}, compareComplex_apply.{u,v,w,s}]
      exact liftCoeffEquiv_naturality.{u,v,w,s} f (φ.val c))

theorem pointwiseComparison : pointwiseComparisonExpected.{u,v,w} := by
  intro k G _ _ h
  refine ⟨pointwiseIso.{u,v,w,0} h, ?_⟩
  intro M n f c
  change ((((compareComplex.{u,v,w,0} h (liftCoeffEquiv.{u,v,w,0} M) (liftCoeffEquiv_action.{u,v,w,0} M)).hom.f n).hom
    (ULift.up f)).hom (GroupBar.Large.single k G c 1)).down = _
  rw [compareComplex_apply.{u,v,w,0}]
  rfl

/-- Package the comparison together with its values on the bar basis. -/
def barComparison (h : SquareZero.{u,v,w} k G)
    {M : Rep.{w} k G} {L : Rep.{max u v w s} k G} (e : M ≃ₗ[k] L)
    (he : ∀ g m, e (M.ρ g m) = L.ρ g (e m)) : BarComparison.{u,v,w,s} h M L e :=
  ⟨compareComplex.{u,v,w,s} h e he, compareComplex_apply.{u,v,w,s} h e he⟩

/-- A commuting square of compatible coefficient maps gives a commuting
square of cochain maps, tested on every homogeneous tuple. -/
lemma barComparison_pullback {H : Type v} [Group H]
    {hG : SquareZero.{u,v,w} k G} {hH : SquareZero.{u,v,w} k H}
    {M : Rep.{w} k G} {M' : Rep.{w} k H}
    {L : Rep.{max u v w s} k G} {L' : Rep.{max u v w s} k H}
    {e : M ≃ₗ[k] L} {e' : M' ≃ₗ[k] L'}
    (a : BarComparison.{u,v,w,s} hG M L e) (a' : BarComparison.{u,v,w,s} hH M' L' e')
    (t : H →* G) (b : M →ₗ[k] M') (b' : L →ₗ[k] L')
    (hb : ∀ g m, b (M.ρ (t g) m) = M'.ρ g (b m))
    (he : ∀ m, e' (b m) = b' (e m))
    (ψ : (repHomogeneousFunctor.{u,v,max w s} k G).obj L ⟶
      (repHomogeneousFunctor.{u,v,max w s} k H).obj L')
    (hψ : ∀ n (φ : ((repHomogeneousFunctor.{u,v,max w s} k G).obj L).X n)
      (c : Fin (n+1) → H), (((ψ.f n).hom φ).hom (GroupBar.Large.single k H c 1)) =
        b' (φ.hom (GroupBar.Large.single k G (t ∘ c) 1))) :
    ((scalarLift.{u,v,w,s} k).mapHomologicalComplex (.up ℕ)).map (cochainPullback t b hb) ≫
      a'.cochain.hom = a.cochain.hom ≫ ψ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨φ⟩
  apply (barEvaluation.{u,v,max w s} L' n).injective
  apply Subtype.ext
  funext c
  change ((a'.cochain.hom.f n).hom (ULift.up (pullbackDegree t b hb n φ))).hom
    (GroupBar.Large.single k H c 1) =
      ((ψ.f n).hom ((a.cochain.hom.f n).hom (ULift.up φ))).hom
        (GroupBar.Large.single k H c 1)
  rw [a'.formula, hψ, a.formula]
  exact he (φ.val (t ∘ c))

theorem actionComparison : actionComparisonExpected.{u,v,w,s} := by
  intro k G _ _ N _ h M L e he a ha
  let b := barComparison.{u,v,w,s} h (M := Rep.res N.subtype M) (L := Rep.res N.subtype L)
    e (fun g m => he g m)
  refine ⟨b, ?_⟩
  intro g
  unfold conjugation
  exact barComparison_pullback.{u,v,w,s} b b (MulAut.conjNormal g⁻¹).toMonoidHom
    (M.ρ g) (L.ρ g) _ (he g) (a g).asHom (fun n φ c => ha g n φ c)

lemma barComparison_onHomology_naturality {H : Type v} [Group H]
    {hG : SquareZero.{u,v,w} k G} {hH : SquareZero.{u,v,w} k H}
    {M : Rep.{w} k G} {M' : Rep.{w} k H}
    {L : Rep.{max u v w s} k G} {L' : Rep.{max u v w s} k H}
    {e : M ≃ₗ[k] L} {e' : M' ≃ₗ[k] L'}
    (a : BarComparison.{u,v,w,s} hG M L e) (a' : BarComparison.{u,v,w,s} hH M' L' e')
    (φ : complex hG M ⟶ complex hH M')
    (ψ : (repHomogeneousFunctor.{u,v,max w s} k G).obj L ⟶
      (repHomogeneousFunctor.{u,v,max w s} k H).obj L')
    (eq : ((scalarLift.{u,v,w,s} k).mapHomologicalComplex (.up ℕ)).map φ ≫
      a'.cochain.hom = a.cochain.hom ≫ ψ) (n : ℕ) :
    (scalarLift.{u,v,w,s} k).map (HomologicalComplex.homologyMap φ n) ≫
        (a'.onHomology n).hom =
      (a.onHomology n).hom ≫ HomologicalComplex.homologyMap ψ n := by
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) n).map φ) (scalarLift.{u,v,w,s} k)
  let U := scalarLift.{u,v,w,s} k
  change U.map (HomologicalComplex.homologyMap φ n) ≫
      (((complex hH M').sc n).mapHomologyIso U).inv =
    (((complex hG M).sc n).mapHomologyIso U).inv ≫
      HomologicalComplex.homologyMap ((U.mapHomologicalComplex (.up ℕ)).map φ) n at hn
  have heq := congrArg (fun f => HomologicalComplex.homologyMap f n) eq
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at heq
  simp only [BarComparison.onHomology, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc]
  change U.map (HomologicalComplex.homologyMap φ n) ≫
      _ ≫ HomologicalComplex.homologyMap a'.cochain.hom n =
    _ ≫ HomologicalComplex.homologyMap a.cochain.hom n ≫ HomologicalComplex.homologyMap ψ n
  rw [reassoc_of% hn, ← heq]

lemma barComparison_linearEquiv_naturality {H : Type v} [Group H]
    {hG : SquareZero.{u,v,w} k G} {hH : SquareZero.{u,v,w} k H}
    {M : Rep.{w} k G} {M' : Rep.{w} k H}
    {L : Rep.{max u v w s} k G} {L' : Rep.{max u v w s} k H}
    {e : M ≃ₗ[k] L} {e' : M' ≃ₗ[k] L'}
    (a : BarComparison.{u,v,w,s} hG M L e) (a' : BarComparison.{u,v,w,s} hH M' L' e')
    (φ : complex hG M ⟶ complex hH M')
    (ψ : (repHomogeneousFunctor.{u,v,max w s} k G).obj L ⟶
      (repHomogeneousFunctor.{u,v,max w s} k H).obj L')
    (eq : ((scalarLift.{u,v,w,s} k).mapHomologicalComplex (.up ℕ)).map φ ≫
      a'.cochain.hom = a.cochain.hom ≫ ψ) (n : ℕ)
    (x : (complex hG M).homology n) :
    a'.linearEquiv n ((HomologicalComplex.homologyMap φ n).hom x) =
      (HomologicalComplex.homologyMap ψ n).hom (a.linearEquiv n x) :=
  congrArg (fun f => f.hom (ULift.up x))
    (barComparison_onHomology_naturality.{u,v,w,s} a a' φ ψ eq n)

section InjectiveResolution
variable (N : Subgroup G) [N.Normal]

open AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction

private def subgroupBarComparison (h : SquareZero.{u,v,w} k N) (M : Rep.{w} k G) :
    BarComparison.{u,v,w,s} h (Rep.res N.subtype M)
      (Rep.res N.subtype ((coefficientLift.{u,v,w,s} k G).obj M)) (liftCoeffEquiv.{u,v,w,s} M) :=
  barComparison.{u,v,w,s} h (M := Rep.res N.subtype M) (L := Rep.res N.subtype ((coefficientLift.{u,v,w,s} k G).obj M))
    (liftCoeffEquiv.{u,v,w,s} M) (fun a m => liftCoeffEquiv_action.{u,v,w,s} M a m)

private lemma subgroupBarComparison_action (h : SquareZero.{u,v,w} k N)
    (M : Rep.{w} k G) (g : G) (j : ℕ) (x : (complex h (Rep.res N.subtype M)).homology j) :
    let c := subgroupBarComparison.{u,v,w,s} N h M
    let L := (coefficientLift.{u,v,w,s} k G).obj M
    c.linearEquiv j ((HomologicalComplex.homologyMap (conjugation N h M g) j).hom x) =
      quotientCohomologyRepresentation.{u,v,max w s} k G N L j (QuotientGroup.mk' N g)
        (c.linearEquiv j x) := by
  dsimp only
  let c := subgroupBarComparison.{u,v,w,s} N h M
  let L := (coefficientLift.{u,v,w,s} k G).obj M
  let a := homogeneousAction.{u,v,max w s} k G N L
  let ψ := (a g).asHom
  change c.linearEquiv j ((HomologicalComplex.homologyMap (conjugation N h M g) j).hom x) =
    (HomologicalComplex.homologyMap ψ j).hom (c.linearEquiv j x)
  apply barComparison_linearEquiv_naturality.{u,v,w,s} c c
  unfold conjugation
  exact barComparison_pullback.{u,v,w,s} c c (MulAut.conjNormal g⁻¹).toMonoidHom
    (M.ρ g) (L.ρ g) _ (liftCoeffEquiv_action.{u,v,w,s} M g) ψ
      (fun i φ t => homogeneousAction_formula.{u,v,max w s} k G N L g i φ t)

omit [N.Normal] in
private lemma subgroupBarComparison_natural (h : SquareZero.{u,v,w} k N)
    {M L : Rep.{w} k G} (f : M ⟶ L) (j : ℕ) (x : (complex h (Rep.res N.subtype M)).homology j) :
    (subgroupBarComparison.{u,v,w,s} N h L).linearEquiv j
      ((HomologicalComplex.homologyMap ((homogeneousFunctor h).map (Rep.resMap N.subtype f)) j).hom x) =
      (HomologicalComplex.homologyMap
        (Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction.coefficientCochainMap
          k G N ((coefficientLift.{u,v,w,s} k G).map f)) j).hom
        ((subgroupBarComparison.{u,v,w,s} N h M).linearEquiv j x) := by
  apply barComparison_linearEquiv_naturality.{u,v,w,s}
  exact barComparison_pullback.{u,v,w,s} (subgroupBarComparison.{u,v,w,s} N h M) (subgroupBarComparison.{u,v,w,s} N h L)
    (MonoidHom.id N) f.hom.toLinearMap ((coefficientLift.{u,v,w,s} k G).map f).hom.toLinearMap
    (fun a m => Rep.hom_comm_apply f (a : G) m) (liftCoeffEquiv_naturality.{u,v,w,s} f) _ (fun _ _ _ => rfl)

theorem injectiveActionComparison : injectiveActionComparisonExpected.{u,v,w,s} := by
  intro k G _ _ N _ h
  let A := coefficientLift.{u,v,w,s} k G
  let c (M : Rep.{w} k G) (j : ℕ) := (subgroupBarComparison.{u,v,w,s} N h M).linearEquiv j
  let σ (M : Rep.{w} k G) (j : ℕ) := quotientCohomologyRepresentation.{u,v,max w s} k G N (A.obj M) j
  let ρ (M : Rep.{w} k G) (j : ℕ) := (c M j).symm.conjRingEquiv.toMonoidHom.comp (σ M j)
  let e (M : Rep.{w} k G) (j : ℕ) (I : InjectiveResolution (A.obj M)) :=
    (c M j).trans (comparisonModuleIso.{u,v,max w s} k G N (A.obj M) j I).toLinearEquiv
  have he (M : Rep.{w} k G) (j : ℕ) (q : G ⧸ N) (x : (complex h (Rep.res N.subtype M)).homology j) :
      c M j (ρ M j q x) = σ M j q (c M j x) := by
    change c M j ((c M j).symm (σ M j q (c M j x))) = _
    exact (c M j).apply_symm_apply _
  refine ⟨ρ, e, ?_, ?_, ?_⟩
  · intro M j g
    apply LinearMap.ext
    intro x
    apply (c M j).injective
    rw [he]
    exact (subgroupBarComparison_action.{u,v,w,s} N h M g j x).symm
  · intro M j I q x
    change (comparisonRepIso.{u,v,max w s} k G N (A.obj M) j I).hom.hom (c M j (ρ M j q x)) = _
    rw [he]
    exact Rep.hom_comm_apply (comparisonRepIso.{u,v,max w s} k G N (A.obj M) j I).hom q (c M j x)
  · intro M L f j I J φ x
    change (comparisonModuleIso.{u,v,max w s} k G N (A.obj L) j J).hom.hom
      (c L j ((HomologicalComplex.homologyMap
        ((homogeneousFunctor h).map (Rep.resMap N.subtype f)) j).hom x)) = _
    have hn := subgroupBarComparison_natural.{u,v,w,s} N h f j x
    change c L j _ = _ at hn
    rw [hn]
    exact congrArg (fun t => t.hom (c M j x))
      (comparisonModuleIso_natural.{u,v,max w s} k G N (A.map f) j I J φ)

end InjectiveResolution

section Edges
variable (N : Subgroup G) [N.Normal]

/-- Restrict an equivariant linear equivalence to the actual fixed submodules. -/
def fixedEquiv {M : Rep.{w} k G} {L : Rep.{x} k G}
    (e : M ≃ₗ[k] L) (he : ∀ g m, e (M.ρ g m) = L.ρ g (e m)) :
    fixed N M ≃ₗ[k] fixed N L where
  toFun m := ⟨e m.val, fun a => by
    change L.ρ (a : G) (e m.val) = e m.val
    rw [← he]
    exact congrArg e (m.property a)⟩
  invFun l := ⟨e.symm l.val, fun a => e.injective (by
    change e (M.ρ (a : G) (e.symm l.val)) = e (e.symm l.val)
    rw [he, e.apply_symm_apply]
    exact l.property a)⟩
  left_inv m := Subtype.ext (e.symm_apply_apply m.val)
  right_inv l := Subtype.ext (e.apply_symm_apply l.val)
  map_add' m n := Subtype.ext (_root_.map_add e m.val n.val)
  map_smul' a m := Subtype.ext (_root_.map_smul e a m.val)

lemma fixedEquiv_action {M : Rep.{w} k G} {L : Rep.{x} k G}
    (e : M ≃ₗ[k] L) (he : ∀ g m, e (M.ρ g m) = L.ρ g (e m))
    (q : G ⧸ N) (m : fixed N M) :
    fixedEquiv N e he ((fixed N M).ρ q m) = (fixed N L).ρ q (fixedEquiv N e he m) := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    apply Subtype.ext
    exact he g m.val

theorem edgeCochainComparison : edgeCochainComparisonExpected.{u,v,w} := by
  intro k G _ _ N _ hG hN hQ M L e he i r hi hr
  let e₀ := fixedEquiv N e he
  let cG := barComparison.{u,v,w,0} hG e he
  let cN := barComparison.{u,v,w,0} hN (M := Rep.res N.subtype M) (L := Rep.res N.subtype L)
    e (fun a m => he (a : G) m)
  let cQ := barComparison.{u,v,w,0} hQ e₀ (fixedEquiv_action N e he)
  refine ⟨e₀, cG, cN, cQ, fun _ => rfl, ?_, ?_⟩
  · unfold inflation
    exact barComparison_pullback.{u,v,w,0} cQ cG (QuotientGroup.mk' N)
      (Representation.invariants (M.ρ.comp N.subtype)).subtype
      (Representation.invariants (L.ρ.comp N.subtype)).subtype _ (fun _ => rfl) i hi
  · unfold restriction
    exact barComparison_pullback.{u,v,w,0} cG cN N.subtype LinearMap.id LinearMap.id _
      (fun _ => rfl) r hr

end Edges

section DegreeZero

private def constantCochain (M : Rep.{w} k G) (m : M.ρ.invariants) :
    cochains M 0 := ⟨fun _ => m.val, fun g _ => (m.property g).symm⟩

private lemma differential_zero_apply (M : Rep.{w} k G) (f : cochains M 0)
    (c : Fin 2 → G) :
    (differential M 0 f).val c = f.val (fun _ => c 1) - f.val (fun _ => c 0) := by
  change (∑ i : Fin 2, (-1 : k) ^ i.val • f.val (c ∘ i.succAbove)) = _
  rw [Fin.sum_univ_two]
  have h₀ : c ∘ (0 : Fin 2).succAbove = fun _ : Fin 1 => c 1 := by
    funext i
    fin_cases i
    rfl
  have h₁ : c ∘ (1 : Fin 2).succAbove = fun _ : Fin 1 => c 0 := by
    funext i
    fin_cases i
    rfl
  rw [h₀, h₁]
  simp [sub_eq_add_neg]

private def constantCycle (h : SquareZero.{u,v,w} k G) (M : Rep.{w} k G)
    (m : M.ρ.invariants) : (complex h M).cycles 0 :=
  (complex h M).cyclesMk (constantCochain M m) 1 (by simp) (by
    change differential M 0 (constantCochain M m) = 0
    apply Subtype.ext
    funext c
    change (differential M 0 (constantCochain M m)).val c = 0
    rw [differential_zero_apply]
    exact sub_self m.val)

private lemma constantCycle_i (h : SquareZero.{u,v,w} k G) (M : Rep.{w} k G)
    (m : M.ρ.invariants) :
    ((complex h M).iCycles 0).hom (constantCycle h M m) = constantCochain M m :=
  (complex h M).i_cyclesMk _ _ _ _

private def constantCycleEquiv (h : SquareZero.{u,v,w} k G) (M : Rep.{w} k G) :
    M.ρ.invariants ≃ₗ[k] (complex h M).cycles 0 :=
  LinearEquiv.ofBijective
    { toFun := constantCycle h M
      map_add' m m' := by
        apply (ModuleCat.mono_iff_injective ((complex h M).iCycles 0)).mp inferInstance
        rw [_root_.map_add, constantCycle_i, constantCycle_i, constantCycle_i]
        rfl
      map_smul' r m := by
        apply (ModuleCat.mono_iff_injective ((complex h M).iCycles 0)).mp inferInstance
        rw [_root_.map_smul, constantCycle_i, constantCycle_i]
        rfl }
    (by
      constructor
      · intro m m' eq
        apply Subtype.ext
        have eq' := congrArg (fun z => (((complex h M).iCycles 0).hom z).val (fun _ => 1)) eq
        change (((complex h M).iCycles 0).hom (constantCycle h M m)).val (fun _ => 1) =
          (((complex h M).iCycles 0).hom (constantCycle h M m')).val (fun _ => 1) at eq'
        rw [constantCycle_i, constantCycle_i] at eq'
        exact eq'
      · intro z
        let f := ((complex h M).iCycles 0).hom z
        have hz : differential M 0 f = 0 := by
          have eq := congrArg (fun t => t.hom z) ((complex h M).iCycles_d 0 1)
          change ((complex h M).d 0 1).hom f = 0 at eq
          exact eq
        have hc (c : Fin 1 → G) : f.val c = f.val (fun _ => 1) := by
          let t : Fin 2 → G := Fin.cons 1 c
          have eq := congrArg (fun f : cochains M 1 => f.val t) hz
          change (differential M 0 f).val t = 0 at eq
          rw [differential_zero_apply, sub_eq_zero] at eq
          have ht : (fun _ : Fin 1 => t 1) = c := by funext i; fin_cases i; rfl
          exact ht ▸ eq
        let m : M.ρ.invariants := ⟨f.val (fun _ => 1), fun g => by
          rw [← equivariant f g]
          exact hc _⟩
        refine ⟨m, (ModuleCat.mono_iff_injective ((complex h M).iCycles 0)).mp inferInstance ?_⟩
        change ((complex h M).iCycles 0).hom (constantCycle h M m) = f
        rw [constantCycle_i]
        exact Subtype.ext (funext fun c => (hc c).symm))

/-- The augmented degree-zero comparison, natural in the original module. -/
def degreeZeroIso (h : SquareZero.{u,v,w} k G) :
    Rep.invariantsFunctor k G ⋙ ModuleCat.uliftFunctor.{v,w} k ≅ cohomology h 0 :=
  NatIso.ofComponents
    (fun M => (ULift.moduleEquiv.trans (constantCycleEquiv h M)).toModuleIso ≪≫
      (complex h M).isoHomologyπ₀)
    (by
      intro M L f
      change _ ≫ (_ ≫ (complex h L).homologyπ 0) =
        (_ ≫ (complex h M).homologyπ 0) ≫ HomologicalComplex.homologyMap _ 0
      rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc, ← Category.assoc]
      apply congrArg (fun t => t ≫ (complex h L).homologyπ 0)
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨m⟩
      apply (ModuleCat.mono_iff_injective ((complex h L).iCycles 0)).mp inferInstance
      change ((complex h L).iCycles 0).hom (constantCycle h L _) =
        ((complex h L).iCycles 0).hom
          ((HomologicalComplex.cyclesMap ((homogeneousFunctor h).map f) 0).hom (constantCycle h M m))
      have eq := congrArg (fun t => t.hom (constantCycle h M m))
        (HomologicalComplex.cyclesMap_i ((homogeneousFunctor h).map f) 0)
      change ((complex h L).iCycles 0).hom
        ((HomologicalComplex.cyclesMap ((homogeneousFunctor h).map f) 0).hom (constantCycle h M m)) =
        ((((homogeneousFunctor h).map f).f 0).hom (((complex h M).iCycles 0).hom (constantCycle h M m))) at eq
      rw [eq, constantCycle_i, constantCycle_i]
      rfl)

theorem degreeZero : degreeZeroExpected.{u,v,w} := by
  intro k G _ _ h
  refine ⟨degreeZeroIso h, fun M m => ⟨constantCycle h M m, ?_, rfl⟩⟩
  intro c
  rw [constantCycle_i]
  rfl

open private uliftHomology_class from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients in
/-- Pointwise carrier comparison sends the class of a constant homogeneous
cocycle to the class given by the same vertex augmentation. -/
lemma barComparison_constantClass
    {h : SquareZero.{u,v,w} k G} {M : Rep.{w} k G} {L : Rep.{max u v w s} k G}
    {e : M ≃ₗ[k] L} (b : BarComparison.{u,v,w,s} h M L e) (m : M.ρ.invariants)
    (z : ((repHomogeneousFunctor.{u,v,max w s} k G).obj L).cycles 0)
    (hz : ∀ c : Fin 1 → G,
      ((((repHomogeneousFunctor.{u,v,max w s} k G).obj L).iCycles 0).hom z).hom
        (GroupBar.Large.single k G c 1) = e m.val) :
    b.linearEquiv 0 (((degreeZeroIso h).hom.app M).hom (ULift.up m)) =
      (((repHomogeneousFunctor.{u,v,max w s} k G).obj L).homologyπ 0).hom z := by
  let K := complex h M
  let U := scalarLift.{u,v,w,s} k
  let KL := (U.mapHomologicalComplex (.up ℕ)).obj K
  let S := (repHomogeneousFunctor.{u,v,max w s} k G).obj L
  let x := constantCycle h M m
  have hx : (KL.d 0 1).hom (ULift.up (constantCochain M m)) = 0 := by
    change ULift.up ((K.d 0 1).hom (constantCochain M m)) = ULift.up 0
    congr 1
    rw [← constantCycle_i h M m]
    exact congrArg (fun f => f.hom x) (K.iCycles_d 0 1)
  let y := KL.cyclesMk (ULift.up (constantCochain M m)) 1 (by simp) hx
  have hy : (KL.iCycles 0).hom y = ULift.up ((K.iCycles 0).hom x) := by
    rw [constantCycle_i]
    exact KL.i_cyclesMk _ _ _ _
  have hclass : (((K.sc 0).mapHomologyIso U).inv).hom (ULift.up ((K.homologyπ 0).hom x)) =
      (KL.homologyπ 0).hom y := by
    apply (((K.sc 0).mapHomologyIso U).toLinearEquiv).injective
    change (((K.sc 0).mapHomologyIso U).toLinearEquiv) (((K.sc 0).mapHomologyIso U).toLinearEquiv.symm _) = _
    rw [LinearEquiv.apply_symm_apply]
    exact (uliftHomology_class (K.sc 0) x y hy).symm
  have hcycle : (HomologicalComplex.cyclesMap b.cochain.hom 0).hom y = z := by
    apply (ModuleCat.mono_iff_injective (S.iCycles 0)).mp inferInstance
    apply (barEvaluation.{u,v,max w s} L 0).injective
    apply Subtype.ext
    funext c
    have eq := congrArg (fun f => f.hom y) (HomologicalComplex.cyclesMap_i b.cochain.hom 0)
    change (S.iCycles 0).hom ((HomologicalComplex.cyclesMap b.cochain.hom 0).hom y) =
      (b.cochain.hom.f 0).hom ((KL.iCycles 0).hom y) at eq
    change ((S.iCycles 0).hom ((HomologicalComplex.cyclesMap b.cochain.hom 0).hom y)).hom
      (GroupBar.Large.single k G c 1) = ((S.iCycles 0).hom z).hom (GroupBar.Large.single k G c 1)
    rw [eq, hy, constantCycle_i, b.formula]
    exact (hz c).symm
  change (HomologicalComplex.homologyMap b.cochain.hom 0).hom
    ((((K.sc 0).mapHomologyIso U).inv).hom (ULift.up ((K.homologyπ 0).hom x))) = _
  rw [hclass]
  have eq := congrArg (fun f => f.hom y) (HomologicalComplex.homologyπ_naturality b.cochain.hom 0)
  change (HomologicalComplex.homologyMap b.cochain.hom 0).hom ((KL.homologyπ 0).hom y) =
    (S.homologyπ 0).hom ((HomologicalComplex.cyclesMap b.cochain.hom 0).hom y) at eq
  rw [hcycle] at eq
  exact eq

end DegreeZero

def moduleLiftIso (k : Type u) (G : Type v) [CommRing k] [Group G] :
    (Rep.ofModuleMonoidAlgebra : ModuleCat.{w} k[G] ⥤ Rep.{w} k G) ⋙
      coefficientLift.{u,v,w,0} k G ≅
      Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients.lift.{u,v,w} k G ⋙
        Rep.ofModuleMonoidAlgebra := by
  let U := ModuleCat.uliftFunctor.{max u v,w} k[G] ⋙
    (Rep.ofModuleMonoidAlgebra : ModuleCat.{max u v w} k[G] ⥤ Rep.{max u v w} k G)
  exact isoWhiskerRight (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)).counitIso U

theorem moduleLiftComparison : moduleLiftComparisonExpected.{u,v,w} := by
  intro k G _ _
  exact ⟨moduleLiftIso k G⟩

section Inhomogeneous

open Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients (rawFunctor rawLifted)
open AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients (barIso)

private def liftedInhomogeneousIso (h : SquareZero.{u,v,w} k G) :
    Rep.ofModuleMonoidAlgebra ⋙ liftedFunctor.{u,v,w,0} h ≅
      rawLifted k G (GroupCohomologyOriginalCoefficients.squareZero k G) :=
  isoWhiskerLeft Rep.ofModuleMonoidAlgebra (pointwiseIso.{u,v,w,0} h) ≪≫
    isoWhiskerRight (moduleLiftIso k G) (repHomogeneousFunctor.{u,v,w} k G) ≪≫ barIso k G

/-- Descend the comparison through the fully faithful scalar lift. -/
def inhomogeneousIso (h : SquareZero.{u,v,w} k G) :
    Rep.ofModuleMonoidAlgebra ⋙ homogeneousFunctor h ≅
      rawFunctor k G (GroupCohomologyOriginalCoefficients.squareZero k G) :=
  let U := (scalarLift.{u,v,w,0} k).mapHomologicalComplex (.up ℕ)
  NatIso.ofComponents (fun M => U.preimageIso ((liftedInhomogeneousIso h).app M))
    (by
      intro M L f
      apply U.map_injective
      simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact (liftedInhomogeneousIso h).hom.naturality f)

theorem inhomogeneousComparison : inhomogeneousComparisonExpected.{u,v,w} := by
  intro k G _ _ h h'
  let U := (scalarLift.{u,v,w,0} k).mapHomologicalComplex (.up ℕ)
  refine ⟨inhomogeneousIso h, ?_⟩
  intro M n φ g
  have hmap : U.map ((inhomogeneousIso h).hom.app M) = (liftedInhomogeneousIso h).hom.app M :=
    U.map_preimage _
  have hval := congrArg (fun ψ => (((ψ.f n).hom (ULift.up φ)).down) g) hmap
  refine hval.trans ?_
  let A : Rep.{w} k G := Rep.ofModuleMonoidAlgebra.obj M
  change (((moduleLiftIso k G).hom.app M).hom
    ((((compareComplex.{u,v,w,0} h (liftCoeffEquiv.{u,v,w,0} A) (liftCoeffEquiv_action.{u,v,w,0} A)).hom.f n).hom
      (ULift.up φ)).hom (GroupBar.Large.single k G (Fin.partialProd g) 1))).down = _
  rw [compareComplex_apply.{u,v,w,0}]
  rfl

end Inhomogeneous

open private uliftHomology_class from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients in
theorem scalarConnectors : scalarConnectorsExpected.{u,v,w} := by
  intro k _ S hS n
  dsimp only
  let U := ModuleCat.uliftFunctor.{v,w} k
  let T := S.map (U.mapHomologicalComplex (.up ℕ))
  intro hT
  let π := T.X₃.homologyπ n
  apply (cancel_epi π).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let z := ((T.X₃.iCycles n).hom s).down
  have hzu : (T.X₃.d n (n+1)).hom (ULift.up z) = 0 :=
    congrArg (fun f => f.hom s) (T.X₃.iCycles_d n (n+1))
  have hz : (S.X₃.d n (n+1)).hom z = 0 := congrArg ULift.down hzu
  have hsN := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n
  obtain ⟨y, hy⟩ := hsN.moduleCat_surjective_g z
  let b := (S.X₂.d n (n+1)).hom y
  let S' := S.map (HomologicalComplex.eval (ModuleCat.{w} k) (.up ℕ) (n+1))
  have hb : S'.g.hom b = 0 := by
    change ((S.X₂.d n (n+1) ≫ S.g.f (n+1))).hom y = 0
    rw [← S.g.comm]
    change (S.X₃.d n (n+1)).hom ((S.g.f n).hom y) = 0
    exact (congrArg (fun x => (S.X₃.d n (n+1)).hom x) hy).trans hz
  have hsN' := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS (n+1)
  obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff S').mp hsN'.exact b hb
  have hyu : (T.g.f n).hom (ULift.up y) = ULift.up z := congrArg ULift.up hy
  have hxu : (T.f.f (n+1)).hom (ULift.up x) = (T.X₂.d n (n+1)).hom (ULift.up y) :=
    congrArg ULift.up hx
  have hδ := hS.δ_apply n (n+1) rfl z hz y hy x hx (n+2) (by simp)
  have hδu := hT.δ_apply n (n+1) rfl (ULift.up z) hzu (ULift.up y) hyu (ULift.up x) hxu (n+2) (by simp)
  let sz := S.X₃.cyclesMk z (n+1) (by simp) hz
  let tz := T.X₃.cyclesMk (ULift.up z) (n+1) (by simp) hzu
  have htz : tz = s := by
    apply (ModuleCat.mono_iff_injective (T.X₃.iCycles n)).mp inferInstance
    exact T.X₃.i_cyclesMk _ _ _ _
  let sx := S.X₁.cyclesMk x (n+2) (by simp)
    (hS.d_eq_zero_of_f_eq_d_apply n (n+1) y x hx (n+2))
  let tx := T.X₁.cyclesMk (ULift.up x) (n+2) (by simp)
    (hT.d_eq_zero_of_f_eq_d_apply n (n+1) (ULift.up y) (ULift.up x) hxu (n+2))
  have hzclass := uliftHomology_class (S.X₃.sc n) sz tz
    ((T.X₃.i_cyclesMk _ _ _ _).trans (congrArg ULift.up (S.X₃.i_cyclesMk _ _ _ _).symm))
  have hxclass := uliftHomology_class (S.X₁.sc (n+1)) sx tx
    ((T.X₁.i_cyclesMk _ _ _ _).trans (congrArg ULift.up (S.X₁.i_cyclesMk _ _ _ _).symm))
  change (hT.δ n (n+1) rfl).hom ((T.X₃.homologyπ n).hom tz) = (T.X₁.homologyπ (n+1)).hom tx at hδu
  change (hS.δ n (n+1) rfl).hom ((S.X₃.homologyπ n).hom sz) = (S.X₁.homologyπ (n+1)).hom sx at hδ
  change (((S.X₁.sc (n+1)).mapHomologyIso U).hom).hom
      ((hT.δ n (n+1) rfl).hom ((T.X₃.homologyπ n).hom s)) =
    (U.map (hS.δ n (n+1) rfl)).hom
      ((((S.X₃.sc n).mapHomologyIso U).hom).hom ((T.X₃.homologyπ n).hom s))
  change (((S.X₁.sc (n+1)).mapHomologyIso U).hom).hom ((T.X₁.homologyπ (n+1)).hom tx) =
    ULift.up ((S.X₁.homologyπ (n+1)).hom sx) at hxclass
  change (((S.X₃.sc n).mapHomologyIso U).hom).hom ((T.X₃.homologyπ n).hom tz) =
    ULift.up ((S.X₃.homologyπ n).hom sz) at hzclass
  rw [← htz, hδu, hxclass, hzclass]
  exact congrArg ULift.up hδ.symm

private theorem shortExact_of_scalarLift (k : Type u) [CommRing k]
    (S : ShortComplex (CochainComplex (ModuleCat.{w} k) ℕ))
    (h : (S.map ((ModuleCat.uliftFunctor.{v,w} k).mapHomologicalComplex (.up ℕ))).ShortExact) :
    S.ShortExact := by
  let U := ModuleCat.uliftFunctor.{v,w} k
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let T := S.map (HomologicalComplex.eval (ModuleCat.{w} k) (.up ℕ) n)
  have hT : (T.map U).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp h n
  change T.ShortExact
  exact { exact := (T.exact_map_iff_of_faithful U).mp hT.exact
          mono_f := mono_of_mono_map U hT.mono_f
          epi_g := epi_of_epi_map U hT.epi_g }

theorem originalConnectors : originalConnectorsExpected.{u,w,s} := by
  intro k _ A _ _ K _ L _ b V δ e he
  obtain ⟨hex, hn⟩ := he
  let U := ModuleCat.uliftFunctor.{max u s,w} k
  let J := U.mapHomologicalComplex (.up ℕ)
  have hLift {S : ShortComplex A} (hS : S.ShortExact) : (S.map (K ⋙ J)).ShortExact :=
    ShortComplex.shortExact_of_iso (S.mapNatIso b.symm) (hex hS)
  have hRaw {S : ShortComplex A} (hS : S.ShortExact) : (S.map K).ShortExact :=
    shortExact_of_scalarLift.{u,max u s,w} k (S.map K) (hLift hS)
  refine ⟨hRaw, ?_⟩
  dsimp only
  intro S hS n
  let H (n : ℕ) (X : A) := HomologicalComplex.homologyMap (b.inv.app X) n
  let S₀ := S.map K
  let Z (n : ℕ) (X : A) := (((K.obj X).sc n).mapHomologyIso U).hom
  change δ hS n ≫ ((e (n+1)).hom.app S.X₁ ≫ H (n+1) S.X₁ ≫ Z (n+1) S.X₁) =
    ((e n).hom.app S.X₃ ≫ H n S.X₃ ≫ Z n S.X₃) ≫ U.map ((hRaw hS).δ n (n+1) rfl)
  have hc : (hex hS).δ n (n+1) rfl ≫ H (n+1) S.X₁ =
      H n S.X₃ ≫ (hLift hS).δ n (n+1) rfl :=
    GroupHochschildSerre.cochainTransformation_connectors b.inv (hex hS) (hLift hS) n
  have hd : (hLift hS).δ n (n+1) rfl ≫ Z (n+1) S.X₁ =
      Z n S.X₃ ≫ U.map ((hRaw hS).δ n (n+1) rfl) :=
    scalarConnectors.{u,max u s,w} k S₀ (hRaw hS) n (hLift hS)
  rw [reassoc_of% (hn hS n), reassoc_of% hc, hd]
  simp only [Category.assoc]

section Pages

open AdvancedHomologicalAlgebra.GrothendieckSpectralSequence
open AdvancedHomologicalAlgebra.GrothendieckEdges
open Specs.AdvancedHomologicalAlgebra.GroupHochschildSerre
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

/-- Change the universe of the lifted tuple indices, fixing every original tuple. -/
def sameTuples (k : Type u) (G : Type v) [CommRing k] [Group G] :
    repHomogeneousFunctor.{u,v,w} k G ≅ repHomogeneousFunctor.{u,v,max v w} k G :=
  NatIso.ofComponents
    (fun L => HomologicalComplex.Hom.isoOfComponents
      (fun n => ((barEvaluation.{u,v,w} L n).trans
        (barEvaluation.{u,v,max v w} L n).symm).toModuleIso)
      (by
        intro i j hij
        have hji : j = i+1 := hij.symm
        subst j
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        apply (barEvaluation.{u,v,max v w} L (i+1)).injective
        change barEvaluation.{u,v,max v w} L _ ((((repHomogeneousFunctor.{u,v,max v w} k G).obj L).d
          i (i+1)).hom ((barEvaluation.{u,v,max v w} L i).symm (barEvaluation.{u,v,w} L i φ))) =
          barEvaluation.{u,v,max v w} L _ ((barEvaluation.{u,v,max v w} L (i+1)).symm
            (barEvaluation.{u,v,w} L (i+1)
              ((((repHomogeneousFunctor.{u,v,w} k G).obj L).d i (i+1)).hom φ)))
        rw [barEvaluation_d, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
          barEvaluation_d]))
    (by
      intro L L' f
      apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      apply (barEvaluation.{u,v,max v w} L' n).injective
      change barEvaluation.{u,v,max v w} L' n
          ((barEvaluation.{u,v,max v w} L' n).symm (barEvaluation.{u,v,w} L' n (φ ≫ f))) =
        barEvaluation.{u,v,max v w} L' n
          (((barEvaluation.{u,v,max v w} L n).symm (barEvaluation.{u,v,w} L n φ)) ≫ f)
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      funext c
      change f.hom ((barEvaluation.{u,v,w} L n φ).val c) =
        f.hom ((barEvaluation.{u,v,max v w} L n
          ((barEvaluation.{u,v,max v w} L n).symm (barEvaluation.{u,v,w} L n φ))).val c)
      rw [LinearEquiv.apply_symm_apply])

lemma sameTuples_formula (L : Rep.{max u v w} k G) (n : ℕ)
    (φ : ((repHomogeneousFunctor.{u,v,w} k G).obj L).X n) (c : Fin (n+1) → G) :
    (((((sameTuples.{u,v,w} k G).hom.app L).f n).hom φ).hom
      (GroupBar.Large.single.{u,v,max v w} k G c 1)) =
    φ.hom (GroupBar.Large.single.{u,v,w} k G c 1) := by
  change (barEvaluation.{u,v,max v w} L n
    ((barEvaluation.{u,v,max v w} L n).symm (barEvaluation.{u,v,w} L n φ))).val c = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

variable (N : Subgroup G) [N.Normal]

private def subgroupPageEquiv (hN : SquareZero.{u,v,w} k N)
    (C : CohomologyModels.{u,v,max w s} k G N) (M : Rep.{w} k G) (q : ℕ) :
    (complex hN (Rep.res N.subtype M)).homology q ≃ₗ[k]
      (C.subgroup q).obj ((coefficientLift.{u,v,w,s} k G).obj M) :=
  ((subgroupBarComparison.{u,v,w,s} N hN M).linearEquiv q).trans
    ((C.underlying q).app ((coefficientLift.{u,v,w,s} k G).obj M)).symm.toLinearEquiv

private lemma subgroupPageEquiv_coordinates (hN : SquareZero.{u,v,w} k N)
    (C : CohomologyModels.{u,v,max w s} k G N) (M : Rep.{w} k G) (q : ℕ)
    (x : (complex hN (Rep.res N.subtype M)).homology q) :
    ((C.underlying q).app ((coefficientLift.{u,v,w,s} k G).obj M)).toLinearEquiv
      (subgroupPageEquiv.{u,v,w,s} N hN C M q x) = (subgroupBarComparison.{u,v,w,s} N hN M).linearEquiv q x :=
  (((C.underlying q).app ((coefficientLift.{u,v,w,s} k G).obj M)).toLinearEquiv).apply_symm_apply _

private def subgroupPageAction (hN : SquareZero.{u,v,w} k N)
    (C : CohomologyModels.{u,v,max w s} k G N) (M : Rep.{w} k G) (q : ℕ) :
    Representation k (G ⧸ N) ((complex hN (Rep.res N.subtype M)).homology q) :=
  (subgroupPageEquiv.{u,v,w,s} N hN C M q).symm.conjRingEquiv.toMonoidHom.comp
    ((C.subgroup q).obj ((coefficientLift.{u,v,w,s} k G).obj M)).ρ

private lemma subgroupPageEquiv_action (hN : SquareZero.{u,v,w} k N)
    (C : CohomologyModels.{u,v,max w s} k G N) (M : Rep.{w} k G) (q : ℕ)
    (g : G ⧸ N) (x : (complex hN (Rep.res N.subtype M)).homology q) :
    subgroupPageEquiv.{u,v,w,s} N hN C M q (subgroupPageAction.{u,v,w,s} N hN C M q g x) =
      ((C.subgroup q).obj ((coefficientLift.{u,v,w,s} k G).obj M)).ρ g
        (subgroupPageEquiv.{u,v,w,s} N hN C M q x) :=
  (subgroupPageEquiv.{u,v,w,s} N hN C M q).apply_symm_apply _

private lemma subgroupPageAction_formula (hN : SquareZero.{u,v,w} k N)
    (C : CohomologyModels.{u,v,max w s} k G N) (M : Rep.{w} k G) (q : ℕ) (g : G) :
    subgroupPageAction.{u,v,w,s} N hN C M q (QuotientGroup.mk' N g) =
      (HomologicalComplex.homologyMap (conjugation N hN M g) q).hom := by
  let L := (coefficientLift.{u,v,w,s} k G).obj M
  let c := subgroupBarComparison.{u,v,w,s} N hN M
  obtain ⟨a, ha, hc⟩ := C.conjugation L
  have eq : ((scalarLift.{u,v,w,s} k).mapHomologicalComplex (.up ℕ)).map
      (conjugation N hN M g) ≫ c.cochain.hom = c.cochain.hom ≫ (a g).asHom := by
    unfold conjugation
    exact barComparison_pullback.{u,v,w,s} c c (MulAut.conjNormal g⁻¹).toMonoidHom
      (M.ρ g) (L.ρ g) _ (liftCoeffEquiv_action.{u,v,w,s} M g) (a g).asHom (fun n φ t => ha g n φ t)
  apply LinearMap.ext
  intro x
  apply (subgroupPageEquiv.{u,v,w,s} N hN C M q).injective
  rw [subgroupPageEquiv_action.{u,v,w,s}]
  apply ((C.underlying q).app L).toLinearEquiv.injective
  have heq := barComparison_linearEquiv_naturality.{u,v,w,s} c c (conjugation N hN M g)
    (a g).asHom eq q x
  change (c.linearEquiv q) ((HomologicalComplex.homologyMap (conjugation N hN M g) q).hom x) =
    (HomologicalComplex.homologyMap (a g).asHom q).hom ((c.linearEquiv q) x) at heq
  have hc' := hc q g ((c.linearEquiv q) x)
  change (((C.underlying q).app L).toLinearEquiv)
    (((C.subgroup q).obj L).ρ (QuotientGroup.mk' N g) (subgroupPageEquiv.{u,v,w,s} N hN C M q x)) =
    (((C.underlying q).app L).toLinearEquiv)
      (subgroupPageEquiv.{u,v,w,s} N hN C M q ((HomologicalComplex.homologyMap (conjugation N hN M g) q).hom x))
  exact hc'.trans (heq.symm.trans (subgroupPageEquiv_coordinates.{u,v,w,s} N hN C M q _).symm)

private lemma subgroupPageEquiv_natural (hN : SquareZero.{u,v,w} k N)
    (C : CohomologyModels.{u,v,max w s} k G N) {M L : Rep.{w} k G} (f : M ⟶ L)
    (j : ℕ) (x : (complex hN (Rep.res N.subtype M)).homology j) :
    subgroupPageEquiv.{u,v,w,s} N hN C L j
      ((HomologicalComplex.homologyMap ((homogeneousFunctor hN).map (Rep.resMap N.subtype f)) j).hom x) =
      ((C.subgroup j).map ((coefficientLift.{u,v,w,s} k G).map f)).hom
        (subgroupPageEquiv.{u,v,w,s} N hN C M j x) := by
  let U := coefficientLift.{u,v,w,s} k G
  let a := (C.underlying j).app (U.obj M)
  let b := (C.underlying j).app (U.obj L)
  apply b.toLinearEquiv.injective
  have hn := congrArg (fun t => t.hom (subgroupPageEquiv.{u,v,w,s} N hN C M j x))
    ((C.underlying j).hom.naturality (U.map f))
  have eq := subgroupBarComparison_natural.{u,v,w,s} N hN f j x
  change b.toLinearEquiv
    (((C.subgroup j).map (U.map f)).hom (subgroupPageEquiv.{u,v,w,s} N hN C M j x)) =
    (HomologicalComplex.homologyMap
      (Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction.coefficientCochainMap
        k G N (U.map f)) j).hom (a.toLinearEquiv (subgroupPageEquiv.{u,v,w,s} N hN C M j x)) at hn
  rw [hn]
  exact (subgroupPageEquiv_coordinates.{u,v,w,s} N hN C L j _).trans (eq.trans
    (congrArg _ (subgroupPageEquiv_coordinates.{u,v,w,s} N hN C M j x).symm))

def makePageComparisons (hG : SquareZero.{u,v,w} k G) (hN : SquareZero.{u,v,w} k N)
    (hQ : SquareZero.{u,v,max v w} k (G ⧸ N)) (C : CohomologyModels.{u,v,max w s} k G N) :
    PageComparisons.{u,v,w,s} N hG hN hQ C := by
  refine {
    action := subgroupPageAction.{u,v,w,s} N hN C
    formula := subgroupPageAction_formula.{u,v,w,s} N hN C
    subgroup := subgroupPageEquiv.{u,v,w,s} N hN C
    subgroup_action := subgroupPageEquiv_action.{u,v,w,s} N hN C
    subgroup_naturality := subgroupPageEquiv_natural.{u,v,w,s} N hN C
    coefficient := liftCoeffEquiv.{u,v,w,s}
    coefficient_action := liftCoeffEquiv_action.{u,v,w,s}
    coefficient_formula := fun _ _ => rfl
    subgroupBar := subgroupBarComparison.{u,v,w,s} N hN
    subgroup_coordinates := ?_
    groupBar := fun M => barComparison.{u,v,w,s} hG (liftCoeffEquiv.{u,v,w,s} M) (liftCoeffEquiv_action.{u,v,w,s} M)
    quotientPresentation := sameTuples.{u,v,max w s} k (G ⧸ N)
    quotientPresentation_formula := sameTuples_formula.{u,v,max w s}
    quotientBar := ?_ }
  · intro M q x
    exact (((C.underlying q).app ((coefficientLift.{u,v,w,s} k G).obj M)).toLinearEquiv).apply_symm_apply _
  · intro M q
    exact barComparison.{u,v,max v w,s} hQ (M := Rep.of (subgroupPageAction.{u,v,w,s} N hN C M q))
      (L := (C.subgroup q).obj ((coefficientLift.{u,v,w,s} k G).obj M))
      (subgroupPageEquiv.{u,v,w,s} N hN C M q) (subgroupPageEquiv_action.{u,v,w,s} N hN C M q)

theorem pageComparisons : pageComparisonsExpected.{u,v,w,s} := by
  intro k G _ _ N _ hG hN hQ C
  exact ⟨makePageComparisons.{u,v,w,s} N hG hN hQ C⟩

/-- Restrict an equivariant equivalence of representations to invariants. -/
def invariantsEquiv {H : Type v} [Group H] {X : Rep k H} {Y : Rep k H}
    (e : X ≃ₗ[k] Y) (he : ∀ g m, e (X.ρ g m) = Y.ρ g (e m)) :
    X.ρ.invariants ≃ₗ[k] Y.ρ.invariants where
  toFun m := ⟨e m.val, fun g => (he g m.val).symm.trans (congrArg e (m.property g))⟩
  invFun y := ⟨e.symm y.val, fun g => e.injective (by rw [he, e.apply_symm_apply, y.property g])⟩
  left_inv m := Subtype.ext (e.symm_apply_apply m.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' m n := Subtype.ext (_root_.map_add e m.val n.val)
  map_smul' r m := Subtype.ext (_root_.map_smul e r m.val)

local instance standardDerived (B : Type*) [Category B] [Abelian B] :
    HasDerivedCategory B := HasDerivedCategory.standard B

local instance repInjectives (R : Type u) (H : Type v) [CommRing R] [Group H]
    [Small.{w} R[H]] : EnoughInjectives (Rep.{w} R H) :=
  Rep.equivalenceModuleMonoidAlgebra.enoughInjectives_iff.mpr inferInstance

def makeOriginalEdges (hG : SquareZero.{u,v,w} k G) (hN : SquareZero.{u,v,w} k N)
    (hQ : SquareZero.{u,v,max v w} k (G ⧸ N)) (hQ₀ : SquareZero.{u,v,w} k (G ⧸ N))
    {C : CohomologyModels.{u,v,max w s} k G N}
    {P : Package (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N)}
    {E : ObjectEdges (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N) P}
    (e : EdgeIdentifications C P E) (M : Rep.{w} k G) :
    OriginalEdges.{u,v,w,s} (makePageComparisons.{u,v,w,s} N hG hN hQ C) e hQ₀ M := by
  let A := makePageComparisons.{u,v,w,s} N hG hN hQ C
  let L := (coefficientLift.{u,v,w,s} k G).obj M
  let c₀ := fixedEquiv N (liftCoeffEquiv.{u,v,w,s} M) (liftCoeffEquiv_action.{u,v,w,s} M)
  let cQ := barComparison.{u,v,w,s} hQ₀ c₀ (fixedEquiv_action N (liftCoeffEquiv.{u,v,w,s} M) (liftCoeffEquiv_action.{u,v,w,s} M))
  let cG := A.groupBar M
  let cN := A.subgroupBar M
  let col (n : ℕ) := invariantsEquiv (X := Rep.of (A.action M n)) (Y := (C.subgroup n).obj L)
    (A.subgroup M n) (A.subgroup_action M n)
  let r (n : ℕ) : (complex hG M).homology n ⟶ ModuleCat.of k (A.action M n).invariants :=
    ModuleCat.ofHom (((col n).symm.toLinearMap.comp ((e.restriction.map n).app L).hom).comp
      (cG.linearEquiv n).toLinearMap)
  refine {
    fixedCompare := c₀
    fixed_formula := fun _ => rfl
    rowBar := cQ
    column := col
    column_formula := fun _ _ => rfl
    restrict := r
    restrict_formula := ?_
    inflation_compare := ?_
    restriction_compare := ?_ }
  · intro n x
    let ψ := e.restriction.cochain.app L
    have hψ : ((scalarLift.{u,v,w,s} k).mapHomologicalComplex (.up ℕ)).map
        (restriction N hG hN M) ≫ cN.cochain.hom = cG.cochain.hom ≫ ψ := by
      unfold restriction
      exact barComparison_pullback.{u,v,w,s} cG cN N.subtype LinearMap.id LinearMap.id _
        (fun _ => rfl) ψ (e.restriction.formula L)
    apply (cN.linearEquiv n).injective
    have eq := barComparison_linearEquiv_naturality.{u,v,w,s} cG cN (restriction N hG hN M) ψ hψ n x
    rw [eq]
    rw [← A.subgroup_coordinates]
    have hc := congrArg Subtype.val ((col n).apply_symm_apply
      (((e.restriction.map n).app L).hom (cG.linearEquiv n x)))
    exact (congrArg (((C.underlying n).hom.app L).hom) hc).trans
      (e.restriction.ordinary n L (cG.linearEquiv n x))
  · intro n x
    let ψ := e.inflationCochain.app L
    have hψ : ((scalarLift.{u,v,w,s} k).mapHomologicalComplex (.up ℕ)).map
        (inflation N hG hQ₀ M) ≫ cG.cochain.hom = cQ.cochain.hom ≫ ψ := by
      unfold inflation
      exact barComparison_pullback.{u,v,w,s} cQ cG (QuotientGroup.mk' N)
        (Representation.invariants (M.ρ.comp N.subtype)).subtype
        (Representation.invariants (L.ρ.comp N.subtype)).subtype _ (fun _ => rfl)
        ψ (e.inflationFormula L)
    exact barComparison_linearEquiv_naturality.{u,v,w,s} cQ cG (inflation N hG hQ₀ M) ψ hψ n x
  · intro n x
    exact (col n).apply_symm_apply _

private theorem classicalFiveTerms_of_lift
    {X₁ X₂ X₃ X₄ X₅ : ModuleCat.{w} k}
    {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} {d : X₃ ⟶ X₄} {h : X₄ ⟶ X₅}
    (H : ClassicalFiveTerms ((ModuleCat.uliftFunctor.{s,w} k).map f) ((ModuleCat.uliftFunctor.{s,w} k).map g)
      ((ModuleCat.uliftFunctor.{s,w} k).map d) ((ModuleCat.uliftFunctor.{s,w} k).map h)) :
    ClassicalFiveTerms f g d h := by
  let U := ModuleCat.uliftFunctor.{s,w} k
  have eq {X Y Z : ModuleCat.{w} k} {a : X ⟶ Y} {b : Y ⟶ Z}
      (z : U.map a ≫ U.map b = 0) : a ≫ b = 0 :=
    U.map_injective (by rw [Functor.map_comp, Functor.map_zero, z])
  have exact_pair {X Y Z : ModuleCat.{w} k} {a : X ⟶ Y} {b : Y ⟶ Z}
      {z : U.map a ≫ U.map b = 0} (hex : (ShortComplex.mk _ _ z).Exact) :
      (ShortComplex.mk a b (eq z)).Exact :=
    ((ShortComplex.mk a b (eq z)).exact_map_iff_of_faithful U).mp hex
  exact ⟨mono_of_mono_map U H.mono, eq H.fg, eq H.gd, eq H.dh, exact_pair H.exact_f_g,
    exact_pair H.exact_g_d, exact_pair H.exact_d_h⟩

open private conjugateFiveTerms from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupHochschildSerre in
private theorem originalFiveTerms
    {hG : SquareZero.{u,v,w} k G} {hN : SquareZero.{u,v,w} k N}
    {hQ : SquareZero.{u,v,max v w} k (G ⧸ N)} {hQ₀ : SquareZero.{u,v,w} k (G ⧸ N)}
    {C : CohomologyModels.{u,v,max w s} k G N}
    {P : Package (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N)}
    {E : ObjectEdges (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N) P}
    {A : PageComparisons.{u,v,w,s} N hG hN hQ C} {e : EdgeIdentifications C P E}
    {M : Rep.{w} k G} (o : OriginalEdges.{u,v,w,s} A e hQ₀ M)
    (H : let L := (coefficientLift.{u,v,w,s} k G).obj M
      ClassicalFiveTerms (HomologicalComplex.homologyMap (e.inflationCochain.app L) 1)
        ((e.restriction.map 1).app L) (ordinaryTransgression C E L)
        (HomologicalComplex.homologyMap (e.inflationCochain.app L) 2)) :
    ClassicalFiveTerms (HomologicalComplex.homologyMap (inflation N hG hQ₀ M) 1)
      (o.restrict 1) o.transgression (HomologicalComplex.homologyMap (inflation N hG hQ₀ M) 2) := by
  let U := scalarLift.{u,v,w,s} k
  let L := (coefficientLift.{u,v,w,s} k G).obj M
  let i (n : ℕ) := HomologicalComplex.homologyMap (inflation N hG hQ₀ M) n
  let i' (n : ℕ) := HomologicalComplex.homologyMap (e.inflationCochain.app L) n
  let r' := (e.restriction.map 1).app L
  let t' := ordinaryTransgression C E L
  let er (n : ℕ) := (o.rowBar.onHomology n)
  let et (n : ℕ) := ((A.groupBar M).onHomology n)
  let ec : U.obj (ModuleCat.of k (A.action M 1).invariants) ≅ _ :=
    (ULift.moduleEquiv.trans (o.column 1)).toModuleIso
  have hi (n : ℕ) : (er n).hom ≫ i' n ≫ (et n).inv = U.map (i n) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x⟩
    change (et n).toLinearEquiv.symm ((i' n).hom (o.rowBar.linearEquiv n x)) = _
    rw [← o.inflation_compare n x]
    exact (et n).toLinearEquiv.symm_apply_apply _
  have hr : (et 1).hom ≫ r' ≫ ec.inv = U.map (o.restrict 1) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x⟩
    change ec.toLinearEquiv.symm (r'.hom ((A.groupBar M).linearEquiv 1 x)) = _
    rw [← o.restriction_compare 1 x]
    exact ec.toLinearEquiv.symm_apply_apply _
  have hd : ec.hom ≫ t' ≫ (er 2).inv = U.map o.transgression := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x⟩
    rfl
  have h := conjugateFiveTerms (er 1) (et 1) ec (er 2) (et 2) H
  change ClassicalFiveTerms ((er 1).hom ≫ i' 1 ≫ (et 1).inv)
    ((et 1).hom ≫ r' ≫ ec.inv) (ec.hom ≫ t' ≫ (er 2).inv)
    ((er 2).hom ≫ i' 2 ≫ (et 2).inv) at h
  rw [hi 1, hi 2, hr, hd] at h
  exact classicalFiveTerms_of_lift.{u,max v w,max u s} h

open AdvancedHomologicalAlgebra.G05FilteredEdges in
private theorem originalFilteredCompatibility
    {hG : SquareZero.{u,v,w} k G} {hN : SquareZero.{u,v,w} k N}
    {hQ : SquareZero.{u,v,max v w} k (G ⧸ N)} {hQ₀ : SquareZero.{u,v,w} k (G ⧸ N)}
    {C : CohomologyModels.{u,v,max w s} k G N}
    {P : Package (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N)}
    {E : ObjectEdges (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N) P}
    {A : PageComparisons.{u,v,w,s} N hG hN hQ C} {e : EdgeIdentifications C P E}
    {M : Rep.{w} k G} (o : OriginalEdges.{u,v,w,s} A e hQ₀ M) : o.FilteredCompatibility := by
  let U := scalarLift.{u,v,w,s} k
  let L := (coefficientLift.{u,v,w,s} k G).obj M
  let er (n : ℕ) := o.rowBar.onHomology n
  let et (n : ℕ) := (A.groupBar M).onHomology n
  let ec (n : ℕ) := o.invariantIso n
  have hi (n : ℕ) : (er n).inv ≫ U.map (HomologicalComplex.homologyMap (inflation N hG hQ₀ M) n) =
      HomologicalComplex.homologyMap (e.inflationCochain.app L) n ≫ (et n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x⟩
    exact o.inflation_compare n x
  have hr (n : ℕ) : (et n).inv ≫ U.map (o.restrict n) =
      (e.restriction.map n).app L ≫ (ec n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x⟩
    exact o.restriction_compare n x
  have hd : (ec 1).inv ≫ U.map o.transgression = ordinaryTransgression C E L ≫ (er 2).inv := by
    rw [Iso.inv_comp_eq]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x⟩
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro n
    change ((rowCoordinates C E n).hom.app L ≫ (er n).inv) ≫ _ =
      (E.filtered L).row n ≫ ((displayedTarget C E n).hom.app L ≫ (et n).inv)
    rw [Category.assoc, hi, ← Category.assoc, e.inflation_filtered, Category.assoc]
  · intro n
    change ((displayedTarget C E n).hom.app L ≫ (et n).inv) ≫ _ =
      (E.filtered L).column n ≫ ((columnCoordinates C E n).hom.app L ≫ (ec n).inv)
    rw [Category.assoc, hr, ← Category.assoc, e.restriction_filtered, Category.assoc]
  · change ((columnCoordinates C E 1).hom.app L ≫ (ec 1).inv) ≫ _ =
      _ ≫ ((rowCoordinates C E 2).hom.app L ≫ (er 2).inv)
    rw [Category.assoc, hd]
    simp [ordinaryTransgression]
    rfl

private theorem originalPageCoordinatesCompatibility
    {hG : SquareZero.{u,v,w} k G} {hN : SquareZero.{u,v,w} k N}
    {hQ : SquareZero.{u,v,max v w} k (G ⧸ N)} {hQ₀ : SquareZero.{u,v,w} k (G ⧸ N)}
    {C : CohomologyModels.{u,v,max w s} k G N}
    {P : Package (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N)}
    {E : ObjectEdges (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N) P}
    {A : PageComparisons.{u,v,w,s} N hG hN hQ C} {e : EdgeIdentifications C P E}
    {M : Rep.{w} k G} (o : OriginalEdges.{u,v,w,s} A e hQ₀ M) : o.PageCoordinatesCompatibility := by
  refine ⟨?_, ?_⟩
  · intro n
    simp only [PageComparisons.second, OriginalEdges.row, OriginalEdges.rowReduction,
      e.row_identification, NatIso.trans_app, Iso.trans_assoc, Iso.symm_self_id_assoc]
  · intro n
    simp only [PageComparisons.second, OriginalEdges.columnPage, OriginalEdges.columnReduction,
      e.column_identification, NatIso.trans_app, Iso.trans_assoc, Iso.symm_self_id_assoc]

private theorem originalZeroCoordinates
    {hG : SquareZero.{u,v,w} k G} {hN : SquareZero.{u,v,w} k N}
    {hQ : SquareZero.{u,v,max v w} k (G ⧸ N)} {hQ₀ : SquareZero.{u,v,w} k (G ⧸ N)}
    {C : CohomologyModels.{u,v,max w s} k G N}
    {P : Package (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N)}
    {E : ObjectEdges (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N) P}
    {A : PageComparisons.{u,v,w,s} N hG hN hQ C} {e : EdgeIdentifications C P E}
    {M : Rep.{w} k G} (o : OriginalEdges.{u,v,w,s} A e hQ₀ M) : o.ZeroCoordinates := by
  let L := (coefficientLift.{u,v,w,s} k G).obj M
  refine ⟨?_, ?_, ?_⟩
  · intro m
    let z := constantCycle hG M m
    let l : (totalInvariants.{u,v,max w s} k G N).obj L :=
      ⟨⟨A.coefficient M m.val, fun g =>
        (A.coefficient_action M g m.val).symm.trans (congrArg (A.coefficient M) (m.property g))⟩,
        fun q => by
          induction q using QuotientGroup.induction_on with
          | H g =>
            apply Subtype.ext
            exact (A.coefficient_action M g m.val).symm.trans
              (congrArg (A.coefficient M) (m.property g))⟩
    refine ⟨l, z, rfl, fun c => ?_, ?_⟩
    · change (((complex hG M).iCycles 0).hom (constantCycle hG M m)).val c = _
      rw [constantCycle_i]
      rfl
    obtain ⟨z', hz', he⟩ := C.total_augmentation L l
    exact (barComparison_constantClass.{u,v,w,s} (A.groupBar M) m z' hz').trans he.symm
  · intro m
    let z := constantCycle hN (Rep.res N.subtype M) m
    refine ⟨z, fun c => ?_, ?_⟩
    · change (((complex hN (Rep.res N.subtype M)).iCycles 0).hom
        (constantCycle hN (Rep.res N.subtype M) m)).val c = _
      rw [constantCycle_i]
      rfl
    let j := (C.underlying 0).app L
    obtain ⟨z', hz', he⟩ := C.subgroup_augmentation L (o.fixedCompare m)
    apply j.toLinearEquiv.injective
    have hclass := barComparison_constantClass.{u,v,w,s} (A.subgroupBar M) m z' (fun c =>
      (hz' c).trans (o.fixed_formula m))
    simp only [Iso.trans_hom, NatTrans.comp_app, E.degreeZeroF_hom]
    exact (A.subgroup_coordinates M 0 _).trans (hclass.trans he.symm)
  · intro n m
    let V := (C.subgroup n).obj L
    let X : Rep.{max v w} k (G ⧸ N) := Rep.of (A.action M n)
    let z := constantCycle hQ X m
    refine ⟨z, fun c => ?_, ?_⟩
    · change (((complex hQ X).iCycles 0).hom (constantCycle hQ X m)).val c = _
      rw [constantCycle_i]
      rfl
    obtain ⟨z', hz', he⟩ := C.quotient_augmentation V (o.column n m)
    let φ := A.quotientPresentation.hom.app V
    let z'' := (HomologicalComplex.cyclesMap φ 0).hom z'
    have hz'' (c : Fin 1 → G ⧸ N) :
        ((((repHomogeneousFunctor.{u,v,max v w s} k (G ⧸ N)).obj V).iCycles 0).hom z'').hom
          (GroupBar.Large.single.{u,v,max v w s} k (G ⧸ N) c 1) = A.subgroup M n m.val := by
      have hi := congrArg (fun f => f.hom z') (HomologicalComplex.cyclesMap_i φ 0)
      change _ = (φ.f 0).hom ((((repHomogeneousFunctor.{u,v,max w s} k (G ⧸ N)).obj V).iCycles 0).hom z') at hi
      change ((((repHomogeneousFunctor.{u,v,max v w s} k (G ⧸ N)).obj V).iCycles 0).hom z'').hom _ = _
      rw [show (((repHomogeneousFunctor.{u,v,max v w s} k (G ⧸ N)).obj V).iCycles 0).hom z'' =
        (φ.f 0).hom _ from hi]
      exact (A.quotientPresentation_formula V 0 _ c).trans ((hz' c).trans (o.column_formula n m))
    have hclass := barComparison_constantClass.{u,v,max v w,s} (A.quotientBar M n) m z'' hz''
    have hp := congrArg (fun f => f.hom z') (HomologicalComplex.homologyπ_naturality φ 0)
    simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, E.degreeZero_hom]
    exact hclass.trans (hp.symm.trans (congrArg _ he.symm))

private theorem originalPagesNatural
    (hG : SquareZero.{u,v,w} k G) (hN : SquareZero.{u,v,w} k N)
    (hQ : SquareZero.{u,v,max v w} k (G ⧸ N))
    {C : CohomologyModels.{u,v,max w s} k G N}
    {P : Package (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N)}
    (E : ObjectEdges (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N) P) :
    PageComparisons.Natural E (makePageComparisons.{u,v,w,s} N hG hN hQ C) := by
  intro M L f
  let A := makePageComparisons.{u,v,w,s} N hG hN hQ C
  let I := coefficientLift.{u,v,w,s} k G
  let U := scalarLift.{u,v,w,s} k
  let b := I.map f
  refine ⟨?_, ?_⟩
  · intro p q
    let X := (C.subgroup q).obj (I.obj M)
    let Y := (C.subgroup q).obj (I.obj L)
    let c := (C.subgroup q).map b
    let F := HomologicalComplex.homologyFunctor (ModuleCat.{max u v w s} k) (.up ℕ) p
    let a := A.subgroupMap f q
    let bar (V : Rep.{max u v w s} k (G ⧸ N)) := A.quotientPresentation.hom.app V
    let f₀ := (repHomogeneousFunctor.{u,v,max w s} k (G ⧸ N)).map c
    let f₁ := (repHomogeneousFunctor.{u,v,max v w s} k (G ⧸ N)).map c
    have hn : F.map f₀ ≫ F.map (bar Y) = F.map (bar X) ≫ F.map f₁ := by
      rw [← F.map_comp, ← F.map_comp]
      exact congrArg F.map (A.quotientPresentation.hom.naturality c)
    have hbar : ((U.mapHomologicalComplex (.up ℕ)).map ((homogeneousFunctor hQ).map a)) ≫
        (A.quotientBar L q).cochain.hom = (A.quotientBar M q).cochain.hom ≫ f₁ := by
      exact barComparison_pullback.{u,v,max v w,s} (A.quotientBar M q) (A.quotientBar L q)
        (MonoidHom.id (G ⧸ N)) a.hom.toLinearMap c.hom.toLinearMap
        (fun g m => Rep.hom_comm_apply a g m) (fun m => A.subgroup_naturality f q m)
        f₁ (fun _ _ _ => rfl)
    have h := barComparison_onHomology_naturality.{u,v,max v w,s} (A.quotientBar M q) (A.quotientBar L q)
      ((homogeneousFunctor hQ).map a) f₁ hbar p
    have h' : F.map f₁ ≫ ((A.quotientBar L q).onHomology p).inv =
        ((A.quotientBar M q).onHomology p).inv ≫
          U.map (HomologicalComplex.homologyMap ((homogeneousFunctor hQ).map a) p) := by
      apply (cancel_mono ((A.quotientBar L q).onHomology p).hom).mp
      apply (cancel_epi ((A.quotientBar M q).onHomology p).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id_assoc, Category.comp_id]
      exact h.symm
    have hs := (displayedSecond C E p q).hom.naturality b
    change ((objectSequence _ _ P).map b).page 0 p ((p : ℤ)+q) ≫
        (displayedSecond C E p q).hom.app (I.obj L) =
      (displayedSecond C E p q).hom.app (I.obj M) ≫ F.map f₀ at hs
    change ((objectSequence _ _ P).map b).page 0 p ((p : ℤ)+q) ≫
        ((displayedSecond C E p q).hom.app (I.obj L) ≫ F.map (bar Y) ≫
          ((A.quotientBar L q).onHomology p).inv) =
      ((displayedSecond C E p q).hom.app (I.obj M) ≫ F.map (bar X) ≫
          ((A.quotientBar M q).onHomology p).inv) ≫
        U.map (HomologicalComplex.homologyMap ((homogeneousFunctor hQ).map a) p)
    calc
      _ = (((objectSequence _ _ P).map b).page 0 p ((p : ℤ)+q) ≫
          (displayedSecond C E p q).hom.app (I.obj L)) ≫
          (F.map (bar Y) ≫ ((A.quotientBar L q).onHomology p).inv) := by simp only [Category.assoc]
      _ = ((displayedSecond C E p q).hom.app (I.obj M) ≫ F.map f₀) ≫
          (F.map (bar Y) ≫ ((A.quotientBar L q).onHomology p).inv) := congrArg (· ≫ _) hs
      _ = (displayedSecond C E p q).hom.app (I.obj M) ≫ (F.map f₀ ≫ F.map (bar Y)) ≫
          ((A.quotientBar L q).onHomology p).inv := by simp only [Category.assoc]
      _ = (displayedSecond C E p q).hom.app (I.obj M) ≫ (F.map (bar X) ≫ F.map f₁) ≫
          ((A.quotientBar L q).onHomology p).inv := congrArg (fun t => _ ≫ t ≫ _) hn
      _ = (displayedSecond C E p q).hom.app (I.obj M) ≫ F.map (bar X) ≫
          (F.map f₁ ≫ ((A.quotientBar L q).onHomology p).inv) := by simp only [Category.assoc]
      _ = (displayedSecond C E p q).hom.app (I.obj M) ≫ F.map (bar X) ≫
          (((A.quotientBar M q).onHomology p).inv ≫ U.map
            (HomologicalComplex.homologyMap ((homogeneousFunctor hQ).map a) p)) :=
        congrArg (fun t => _ ≫ _ ≫ t) h'
      _ = _ := by simp only [Category.assoc]
  · intro n
    let ψ := (repHomogeneousFunctor.{u,v,max w s} k G).map b
    have hbar : (U.mapHomologicalComplex (.up ℕ)).map ((homogeneousFunctor hG).map f) ≫
        (A.groupBar L).cochain.hom = (A.groupBar M).cochain.hom ≫ ψ := by
      exact barComparison_pullback.{u,v,w,s} (A.groupBar M) (A.groupBar L) (MonoidHom.id G)
        f.hom.toLinearMap b.hom.toLinearMap (fun g m => Rep.hom_comm_apply f g m)
        (liftCoeffEquiv_naturality.{u,v,w,s} f) ψ (fun _ _ _ => rfl)
    have h := barComparison_onHomology_naturality.{u,v,w,s} (A.groupBar M) (A.groupBar L)
      ((homogeneousFunctor hG).map f) ψ hbar n
    have h' : HomologicalComplex.homologyMap ψ n ≫ ((A.groupBar L).onHomology n).inv =
        ((A.groupBar M).onHomology n).inv ≫
          U.map (HomologicalComplex.homologyMap ((homogeneousFunctor hG).map f) n) := by
      apply (cancel_mono ((A.groupBar L).onHomology n).hom).mp
      apply (cancel_epi ((A.groupBar M).onHomology n).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id_assoc, Category.comp_id]
      exact h.symm
    have hs := (displayedTarget C E n).hom.naturality b
    change ((objectSequence _ _ P).map b).target n ≫ (displayedTarget C E n).hom.app (I.obj L) =
      (displayedTarget C E n).hom.app (I.obj M) ≫ HomologicalComplex.homologyMap ψ n at hs
    change ((objectSequence _ _ P).map b).target n ≫ ((displayedTarget C E n).hom.app (I.obj L) ≫
      ((A.groupBar L).onHomology n).inv) = ((displayedTarget C E n).hom.app (I.obj M) ≫
      ((A.groupBar M).onHomology n).inv) ≫
        U.map (HomologicalComplex.homologyMap ((homogeneousFunctor hG).map f) n)
    calc
      _ = (((objectSequence _ _ P).map b).target n ≫
          (displayedTarget C E n).hom.app (I.obj L)) ≫
          ((A.groupBar L).onHomology n).inv := by simp only [Category.assoc]
      _ = ((displayedTarget C E n).hom.app (I.obj M) ≫ HomologicalComplex.homologyMap ψ n) ≫
          ((A.groupBar L).onHomology n).inv := congrArg (· ≫ _) hs
      _ = (displayedTarget C E n).hom.app (I.obj M) ≫
          (HomologicalComplex.homologyMap ψ n ≫ ((A.groupBar L).onHomology n).inv) :=
        Category.assoc _ _ _
      _ = (displayedTarget C E n).hom.app (I.obj M) ≫ (((A.groupBar M).onHomology n).inv ≫
          U.map (HomologicalComplex.homologyMap ((homogeneousFunctor hG).map f) n)) :=
        congrArg (_ ≫ ·) h'
      _ = _ := (Category.assoc _ _ _).symm

private def subgroupPointwiseIso (h : SquareZero.{u,v,w} k N) :
    (Rep.resFunctor.{w} N.subtype ⋙ homogeneousFunctor h) ⋙
        (scalarLift.{u,v,w,s} k).mapHomologicalComplex (.up ℕ) ≅
      coefficientLift.{u,v,w,s} k G ⋙
        (Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction.restriction.{u,v,max w s} k G N ⋙
          repHomogeneousFunctor.{u,v,max w s} k N) :=
  NatIso.ofComponents (fun M => (subgroupBarComparison.{u,v,w,s} N h M).cochain)
    (by
      intro M L f
      exact barComparison_pullback.{u,v,w,s} (subgroupBarComparison.{u,v,w,s} N h M) (subgroupBarComparison.{u,v,w,s} N h L)
        (MonoidHom.id N) f.hom.toLinearMap ((coefficientLift.{u,v,w,s} k G).map f).hom.toLinearMap
        (fun a m => Rep.hom_comm_apply f (a : G) m) (liftCoeffEquiv_naturality.{u,v,w,s} f) _ (fun _ _ _ => rfl))

private theorem liftedOriginalConnectors
    {H : Type v} [Group H]
    (K : Rep.{w} k H ⥤ CochainComplex (ModuleCat.{max v w} k) ℕ) [K.PreservesZeroMorphisms]
    (L : Rep.{max u v w s} k H ⥤ CochainComplex (ModuleCat.{max u v w s} k) ℕ)
      [L.PreservesZeroMorphisms]
    (a : K ⋙ (scalarLift.{u,v,w,s} k).mapHomologicalComplex (.up ℕ) ≅ coefficientLift.{u,v,w,s} k H ⋙ L)
    (V : ℕ → Rep.{max u v w s} k H ⥤ ModuleCat.{max u v w s} k)
    (δ : ∀ {S : ShortComplex (Rep.{max u v w s} k H)}, S.ShortExact → ∀ n : ℕ,
      (V n).obj S.X₃ ⟶ (V (n+1)).obj S.X₁)
    (e : ∀ n, V n ≅ L ⋙ HomologicalComplex.homologyFunctor _ (.up ℕ) n)
    (he : PreservesCochainConnectors.{u,v,max w s} k L V δ e) :
    OriginalConnectors.{u,max v w,s} k K _ a
      (fun n => coefficientLift.{u,v,w,s} k H ⋙ V n)
      (fun h n => δ (liftShortExact.{u,v,w,s} h) n) (fun n => isoWhiskerLeft _ (e n)) := by
  apply originalConnectors
  obtain ⟨hex, hn⟩ := he
  exact ⟨fun h => hex (liftShortExact.{u,v,w,s} h), fun h n => hn (liftShortExact.{u,v,w,s} h) n⟩

set_option maxHeartbeats 1400000 in
theorem originalNormalization : originalNormalizationExpected.{u,v,w,s} := by
  intro k G _ _ N _ hG hN hQ C
  refine ⟨pointwiseIso.{u,v,w,s} hG, subgroupPointwiseIso.{u,v,w,s} N hN, pointwiseIso.{u,v,w,s} hQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M n f t
    exact congrArg ULift.down (compareComplex_apply.{u,v,w,s} hG (liftCoeffEquiv.{u,v,w,s} M)
      (liftCoeffEquiv_action.{u,v,w,s} M) n f t)
  · intro M n f t
    exact congrArg ULift.down ((subgroupBarComparison.{u,v,w,s} N hN M).formula n f t)
  · intro M n f t
    exact congrArg ULift.down (compareComplex_apply.{u,v,w,s} hQ (liftCoeffEquiv.{u,v,w,s} M)
      (liftCoeffEquiv_action.{u,v,w,s} M) n f t)
  · exact liftedOriginalConnectors.{u,v,w,s} (k := k) (H := G) (homogeneousFunctor hG)
      (repHomogeneousFunctor.{u,v,max w s} k G) (pointwiseIso.{u,v,w,s} hG)
      (rightValue (totalInvariants.{u,v,max w s} k G N))
      (fun h n => rightBoundary (totalInvariants.{u,v,max w s} k G N) h n)
      C.totalDerived C.total_connectors
  · exact liftedOriginalConnectors.{u,v,w,s} (k := k) (H := G)
      (Rep.resFunctor.{w} N.subtype ⋙ homogeneousFunctor hN)
      (Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction.restriction.{u,v,max w s} k G N ⋙
        repHomogeneousFunctor.{u,v,max w s} k N) (subgroupPointwiseIso.{u,v,w,s} N hN)
      (fun n => rightValue (subgroupInvariants.{u,v,max w s} k G N) n ⋙ forgetQuotient.{u,v,max w s} k G N)
      (fun h n => (forgetQuotient.{u,v,max w s} k G N).map
        (rightBoundary (subgroupInvariants.{u,v,max w s} k G N) h n))
      (fun n => isoWhiskerRight (C.subgroupDerived n) _ ≪≫ C.underlying n) C.subgroup_connectors
  · exact liftedOriginalConnectors.{u,v,w,s} (k := k) (H := G ⧸ N) (homogeneousFunctor hQ)
      (repHomogeneousFunctor.{u,v,max w s} k (G ⧸ N)) (pointwiseIso.{u,v,w,s} hQ)
      (rightValue (quotientInvariants.{u,v,max w s} k G N))
      (fun h n => rightBoundary (quotientInvariants.{u,v,max w s} k G N) h n)
      C.quotientDerived C.quotient_connectors

set_option maxHeartbeats 1000000 in
theorem spectralSequenceEdges : spectralSequenceEdgesExpected.{u,v,w,s} := by
  intro k G _ _ N _
  obtain ⟨P, E, C, e, quadrant, five⟩ :=
    GroupHochschildSerre.lyndonHochschildSerre.{u,v,max w s} k G N
  let hG := squareZero.{u,v,w} k G
  let hN := squareZero.{u,v,w} k N
  let hQ := squareZero.{u,v,max v w} k (G ⧸ N)
  let hQ₀ := squareZero.{u,v,w} k (G ⧸ N)
  refine ⟨P, E, C, e, hG, hN, hQ, hQ₀, makePageComparisons.{u,v,w,s} N hG hN hQ C,
    originalNormalization.{u,v,w,s} k G N hG hN hQ₀ C, originalPagesNatural.{u,v,w,s} N hG hN hQ E,
    fun M => quadrant ((coefficientLift.{u,v,w,s} k G).obj M), ?_⟩
  intro M
  let o := makeOriginalEdges.{u,v,w,s} N hG hN hQ hQ₀ e M
  exact ⟨o, originalFilteredCompatibility.{u,v,w,s} N o, originalPageCoordinatesCompatibility.{u,v,w,s} N o,
    originalZeroCoordinates.{u,v,w,s} N o,
    originalFiveTerms.{u,v,w,s} N o (five _)⟩

section Mixed

open Specs.AdvancedHomologicalAlgebra.GroupExtensionOriginalCoefficients.Mixed

universe a b t

open private uliftHomology_class from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients in
private lemma homologyIso_inv_class
    (K : CochainComplex (ModuleCat.{a} k) ℕ) (n : ℕ) (z : K.cycles n) :
    let U := ModuleCat.uliftFunctor.{t,a} k
    let K' := (U.mapHomologicalComplex (.up ℕ)).obj K
    ∃ y : K'.cycles n,
      (K'.iCycles n).hom y = ULift.up ((K.iCycles n).hom z) ∧
      (((K.sc n).mapHomologyIso U).inv).hom (ULift.up ((K.homologyπ n).hom z)) =
        (K'.homologyπ n).hom y := by
  let U := ModuleCat.uliftFunctor.{t,a} k
  let K' := (U.mapHomologicalComplex (.up ℕ)).obj K
  have h : (K'.d n (n+1)).hom (ULift.up ((K.iCycles n).hom z)) = 0 := by
    change ULift.up ((K.d n (n+1)).hom ((K.iCycles n).hom z)) = ULift.up 0
    exact congrArg ULift.up (congrArg (fun f => f.hom z) (K.iCycles_d n (n+1)))
  let y := K'.cyclesMk (ULift.up ((K.iCycles n).hom z)) (n+1) (by simp) h
  have hy : (K'.iCycles n).hom y = ULift.up ((K.iCycles n).hom z) :=
    K'.i_cyclesMk _ _ _ _
  refine ⟨y, hy, ?_⟩
  let i := ((K.sc n).mapHomologyIso U).toLinearEquiv
  apply i.injective
  change i (i.symm _) = _
  rw [i.apply_symm_apply]
  exact (uliftHomology_class (K.sc n) z y hy).symm

open private uliftHomology_class from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients in
set_option maxHeartbeats 700000 in
theorem mixedCohomologyOnClasses : cohomologyMapOnClassesExpected.{u,v,a,b,t} := by
  intro k G H _ _ _ hG hH M L r f hf n z
  let K := complex hG M
  let Lc := complex hH L
  let U := scalarLift.{u,v,a,max v b t} k
  let V := scalarLift.{u,v,b,max v a t} k
  let K' := (U.mapHomologicalComplex (.up ℕ)).obj K
  let L' := (V.mapHomologicalComplex (.up ℕ)).obj Lc
  let φ : K' ⟶ L' := commonPullback.{u,v,a,b,t} (hG := hG) (hH := hH) r f hf
  obtain ⟨y, hy, hz⟩ := homologyIso_inv_class.{u,max v a,max u v b t} K n z
  let y' := (HomologicalComplex.cyclesMap φ n).hom y
  let fz := pullbackDegree r f hf n ((K.iCycles n).hom z)
  have hy' : (L'.iCycles n).hom y' = ULift.up fz := by
    have e := congrArg (fun g => g.hom y) (HomologicalComplex.cyclesMap_i φ n)
    change (L'.iCycles n).hom y' = (φ.f n).hom ((K'.iCycles n).hom y) at e
    exact e.trans (congrArg (φ.f n).hom hy)
  have hfz : (Lc.d n (n+1)).hom fz = 0 := by
    apply ULift.up_injective
    change (L'.d n (n+1)).hom (ULift.up fz) = 0
    rw [← hy']
    exact congrArg (fun g => g.hom y') (L'.iCycles_d n (n+1))
  let z' := Lc.cyclesMk fz (n+1) (by simp) hfz
  have hz' : (Lc.iCycles n).hom z' = fz := Lc.i_cyclesMk _ _ _ _
  refine ⟨z', fun c => congrArg (fun φ => φ.val c) hz', ?_⟩
  let i := (K.sc n).mapHomologyIso U
  let j := (Lc.sc n).mapHomologyIso V
  have hn := congrArg (fun g => g.hom y) (HomologicalComplex.homologyπ_naturality φ n)
  change (HomologicalComplex.homologyMap φ n).hom ((K'.homologyπ n).hom y) =
    (L'.homologyπ n).hom y' at hn
  have hj : j.hom.hom ((L'.homologyπ n).hom y') = ULift.up ((Lc.homologyπ n).hom z') := by
    exact uliftHomology_class (Lc.sc n) z' y' (hy'.trans (congrArg ULift.up hz').symm)
  change (j.hom.hom ((HomologicalComplex.homologyMap φ n).hom
    (i.inv.hom (ULift.up ((K.homologyπ n).hom z))))).down = _
  exact congrArg ULift.down ((congrArg (fun x => j.hom.hom
    ((HomologicalComplex.homologyMap φ n).hom x)) hz).trans ((congrArg j.hom.hom hn).trans hj))

private lemma commonBar_pullback {H : Type v} [Group H]
    {hG : SquareZero.{u,v,a} k G} {hH : SquareZero.{u,v,b} k H}
    {M : Rep.{a} k G} {L : Rep.{b} k H}
    {X : Rep.{max u v a b t} k G} {Y : Rep.{max u v a b t} k H}
    {e : M ≃ₗ[k] X} {e' : L ≃ₗ[k] Y}
    (c : BarComparison.{u,v,a,max v b t} hG M X e)
    (c' : BarComparison.{u,v,b,max v a t} hH L Y e')
    (r : H →* G) (f : M →ₗ[k] L) (f' : X →ₗ[k] Y)
    (hf : ∀ g m, f (M.ρ (r g) m) = L.ρ g (f m))
    (he : ∀ m, e' (f m) = f' (e m))
    (ψ : (repHomogeneousFunctor.{u,v,max v a b t} k G).obj X ⟶
      (repHomogeneousFunctor.{u,v,max v a b t} k H).obj Y)
    (hψ : ∀ n (φ : ((repHomogeneousFunctor.{u,v,max v a b t} k G).obj X).X n)
      (z : Fin (n+1) → H), (((ψ.f n).hom φ).hom (GroupBar.Large.single k H z 1)) =
        f' (φ.hom (GroupBar.Large.single k G (r ∘ z) 1))) :
    commonPullback.{u,v,a,b,t} (hG := hG) (hH := hH) r f hf ≫ c'.cochain.hom =
      c.cochain.hom ≫ ψ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨φ⟩
  apply (barEvaluation.{u,v,max v a b t} Y n).injective
  apply Subtype.ext
  funext z
  change ((c'.cochain.hom.f n).hom (ULift.up (pullbackDegree r f hf n φ))).hom
      (GroupBar.Large.single k H z 1) =
    ((ψ.f n).hom ((c.cochain.hom.f n).hom (ULift.up φ))).hom
      (GroupBar.Large.single k H z 1)
  rw [c'.formula, hψ, c.formula]
  exact he (φ.val (r ∘ z))

private lemma commonBar_homology {H : Type v} [Group H]
    {hG : SquareZero.{u,v,a} k G} {hH : SquareZero.{u,v,b} k H}
    {M : Rep.{a} k G} {L : Rep.{b} k H}
    {X : Rep.{max u v a b t} k G} {Y : Rep.{max u v a b t} k H}
    {e : M ≃ₗ[k] X} {e' : L ≃ₗ[k] Y}
    (c : BarComparison.{u,v,a,max v b t} hG M X e)
    (c' : BarComparison.{u,v,b,max v a t} hH L Y e')
    (φ : (liftedFunctor.{u,v,a,max v b t} hG).obj M ⟶
      (liftedFunctor.{u,v,b,max v a t} hH).obj L)
    {ψ : (repHomogeneousFunctor.{u,v,max v a b t} k G).obj X ⟶
      (repHomogeneousFunctor.{u,v,max v a b t} k H).obj Y}
    (h : φ ≫ c'.cochain.hom = c.cochain.hom ≫ ψ) (n : ℕ) :
    commonHomologyMap.{u,max v a,max v b,t} φ n ≫ (c'.onHomology n).hom =
      (c.onHomology n).hom ≫ HomologicalComplex.homologyMap ψ n := by
  have hn := congrArg (fun f => HomologicalComplex.homologyMap f n) h
  simp only [HomologicalComplex.homologyMap_comp] at hn
  let i := ((complex hG M).sc n).mapHomologyIso (scalarLift.{u,v,a,max v b t} k)
  let j := ((complex hH L).sc n).mapHomologyIso (scalarLift.{u,v,b,max v a t} k)
  simp only [commonHomologyMap, BarComparison.onHomology, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  change i.inv ≫ HomologicalComplex.homologyMap φ n ≫ j.hom ≫ j.inv ≫
      HomologicalComplex.homologyMap c'.cochain.hom n =
    i.inv ≫ HomologicalComplex.homologyMap c.cochain.hom n ≫ HomologicalComplex.homologyMap ψ n
  rw [Iso.hom_inv_id_assoc, hn]

private lemma commonBar_onOriginal {H : Type v} [Group H]
    {hG : SquareZero.{u,v,a} k G} {hH : SquareZero.{u,v,b} k H}
    {M : Rep.{a} k G} {L : Rep.{b} k H}
    {X : Rep.{max u v a b t} k G} {Y : Rep.{max u v a b t} k H}
    {e : M ≃ₗ[k] X} {e' : L ≃ₗ[k] Y}
    (c : BarComparison.{u,v,a,max v b t} hG M X e)
    (c' : BarComparison.{u,v,b,max v a t} hH L Y e')
    (φ : (liftedFunctor.{u,v,a,max v b t} hG).obj M ⟶
      (liftedFunctor.{u,v,b,max v a t} hH).obj L)
    {ψ : (repHomogeneousFunctor.{u,v,max v a b t} k G).obj X ⟶
      (repHomogeneousFunctor.{u,v,max v a b t} k H).obj Y}
    (h : φ ≫ c'.cochain.hom = c.cochain.hom ≫ ψ) (n : ℕ)
    (z : (complex hG M).homology n) :
    c'.linearEquiv n (originalHomologyMap.{u,max v a,max v b,t} φ n z) =
      (HomologicalComplex.homologyMap ψ n).hom (c.linearEquiv n z) :=
  congrArg (fun f => f.hom (ULift.up z)) (commonBar_homology.{u,v,a,b,t} c c' φ h n)

private lemma iso_inv_naturality {D : Type*} [Category D] {X Y X' Y' : D}
    (i : X ≅ Y) (j : X' ≅ Y') {f : X ⟶ X'} {g : Y ⟶ Y'}
    (h : f ≫ j.hom = i.hom ≫ g) : g ≫ j.inv = i.inv ≫ f := by
  apply (cancel_mono j.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, h, Iso.inv_hom_id_assoc]

variable {hG : SquareZero.{u,v,a} k G} {hN : SquareZero.{u,v,a} k N}
  {hQ : SquareZero.{u,v,max v a} k (G ⧸ N)}
  {hG' : SquareZero.{u,v,b} k G} {hN' : SquareZero.{u,v,b} k N}
  {hQ' : SquareZero.{u,v,max v b} k (G ⧸ N)}
  {C : CohomologyModels.{u,v,max v a b t} k G N}
  {P : Package (subgroupInvariants.{u,v,max v a b t} k G N)
    (quotientInvariants.{u,v,max v a b t} k G N)}
  (E : ObjectEdges (subgroupInvariants.{u,v,max v a b t} k G N)
    (quotientInvariants.{u,v,max v a b t} k G N) P)

open Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction (coefficientCochainMap) in
omit [N.Normal] in
private lemma commonSubgroup_natural {M : Rep.{a} k G} {L : Rep.{b} k G}
    (f : M.ρ.IntertwiningMap L.ρ) (j : ℕ) (z : (complex hN (Rep.res N.subtype M)).homology j) :
    (subgroupBarComparison.{u,v,b,max v a t} N hN' L).linearEquiv j
      (cohomologyMap.{u,v,a,b,t} (hG := hN) (hH := hN')
        (M := Rep.res N.subtype M) (L := Rep.res N.subtype L)
        (MonoidHom.id N) f.toLinearMap (fun g x => Representation.IntertwiningMap.isIntertwining M.ρ L.ρ f (g : G) x) j z) =
    (HomologicalComplex.homologyMap
      (coefficientCochainMap.{u,v,max v a b t} k G N (commonCoefficientMap.{u,v,a,b,t} f)) j).hom
      ((subgroupBarComparison.{u,v,a,max v b t} N hN M).linearEquiv j z) := by
  let c := subgroupBarComparison.{u,v,a,max v b t} N hN M
  let c' := subgroupBarComparison.{u,v,b,max v a t} N hN' L
  let f' := commonCoefficientMap.{u,v,a,b,t} f
  let ψ := coefficientCochainMap.{u,v,max v a b t} k G N f'
  apply commonBar_onOriginal.{u,v,a,b,t} c c' _ (ψ := ψ)
  exact commonBar_pullback.{u,v,a,b,t} c c' (MonoidHom.id N)
    f.toLinearMap f'.hom.toLinearMap (fun g x => Representation.IntertwiningMap.isIntertwining M.ρ L.ρ f (g : G) x)
    (fun x => (commonCoefficientMap_apply.{u,v,a,b,t} f x).symm) ψ (fun _ _ _ => rfl)

private lemma commonSubgroupPage_natural {M : Rep.{a} k G} {L : Rep.{b} k G}
    (f : M.ρ.IntertwiningMap L.ρ) (j : ℕ) (z : (complex hN (Rep.res N.subtype M)).homology j) :
    subgroupPageEquiv.{u,v,b,max v a t} N hN' C L j
      (cohomologyMap.{u,v,a,b,t} (hG := hN) (hH := hN')
        (M := Rep.res N.subtype M) (L := Rep.res N.subtype L)
        (MonoidHom.id N) f.toLinearMap (fun g x => Representation.IntertwiningMap.isIntertwining M.ρ L.ρ f (g : G) x) j z) =
    ((C.subgroup j).map (commonCoefficientMap.{u,v,a,b,t} f)).hom
      (subgroupPageEquiv.{u,v,a,max v b t} N hN C M j z) := by
  let f' := commonCoefficientMap.{u,v,a,b,t} f
  let U := C.underlying j
  apply (U.app ((coefficientLift.{u,v,b,max v a t} k G).obj L)).toLinearEquiv.injective
  rw [subgroupPageEquiv_coordinates.{u,v,b,max v a t}]
  have hn := congrArg (fun g => g.hom (subgroupPageEquiv.{u,v,a,max v b t} N hN C M j z))
    (U.hom.naturality f')
  change ((U.app ((coefficientLift.{u,v,b,max v a t} k G).obj L)).toLinearEquiv)
      (((C.subgroup j).map f').hom (subgroupPageEquiv.{u,v,a,max v b t} N hN C M j z)) =
    (HomologicalComplex.homologyMap
      (Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction.coefficientCochainMap.{u,v,max v a b t} k G N f') j).hom
      ((U.app ((coefficientLift.{u,v,a,max v b t} k G).obj M)).toLinearEquiv
        (subgroupPageEquiv.{u,v,a,max v b t} N hN C M j z)) at hn
  rw [hn, subgroupPageEquiv_coordinates.{u,v,a,max v b t}]
  exact commonSubgroup_natural.{u,v,a,b,t} N f j z

set_option maxHeartbeats 1800000 in
private theorem commonPagesNatural :
    PageNaturality.{u,v,a,b,t} E (makePageComparisons.{u,v,a,max v b t} N hG hN hQ C)
      (makePageComparisons.{u,v,b,max v a t} N hG' hN' hQ' C) := by
  intro M L f
  let A := makePageComparisons.{u,v,a,max v b t} N hG hN hQ C
  let B := makePageComparisons.{u,v,b,max v a t} N hG' hN' hQ' C
  let X := (coefficientLift.{u,v,a,max v b t} k G).obj M
  let Y := (coefficientLift.{u,v,b,max v a t} k G).obj L
  let b := commonCoefficientMap.{u,v,a,b,t} f
  let D := (objectSequence _ _ P).map b
  let c (q : ℕ) := (C.subgroup q).map b
  let eA (q : ℕ) : (A.action M q).Equiv ((C.subgroup q).obj X).ρ :=
    Representation.Equiv.mk (A.subgroup M q) (fun g => LinearMap.ext (A.subgroup_action M q g))
  let eB (q : ℕ) : (B.action L q).Equiv ((C.subgroup q).obj Y).ρ :=
    Representation.Equiv.mk (B.subgroup L q) (fun g => LinearMap.ext (B.subgroup_action L q g))
  let fQ (q : ℕ) : (A.action M q).IntertwiningMap (B.action L q) :=
    (eB q).symm.toIntertwiningMap.comp ((c q).hom.comp (eA q).toIntertwiningMap)
  have he (q : ℕ) (z : (complex hN (Rep.res N.subtype M)).homology q) :
      B.subgroup L q (fQ q z) = (c q).hom (A.subgroup M q z) :=
    (B.subgroup L q).apply_symm_apply _
  dsimp only
  refine ⟨fQ, ?_, ?_, ?_⟩
  · intro q z
    apply (B.subgroup L q).injective
    exact (he q z).trans (commonSubgroupPage_natural.{u,v,a,b,t} (C := C)
      (hN' := hN') N f q z).symm
  · intro p q
    let F := HomologicalComplex.homologyFunctor (ModuleCat.{max u v a b t} k) (.up ℕ) p
    let S := displayedSecond C E p q ≪≫
      isoWhiskerLeft (C.subgroup q) (isoWhiskerRight (sameTuples.{u,v,max v a b t} k (G ⧸ N)) F)
    let ψ := (repHomogeneousFunctor.{u,v,max v a b t} k (G ⧸ N)).map (c q)
    let φ := commonPullback.{u,v,max v a,max v b,t} (hG := hQ) (hH := hQ')
      (M := Rep.of (A.action M q)) (L := Rep.of (B.action L q))
      (MonoidHom.id (G ⧸ N)) (fQ q).toLinearMap
      (Representation.IntertwiningMap.isIntertwining _ _ (fQ q))
    have hbar : φ ≫ (B.quotientBar L q).cochain.hom =
        (A.quotientBar M q).cochain.hom ≫ ψ :=
      commonBar_pullback.{u,v,max v a,max v b,t} (A.quotientBar M q) (B.quotientBar L q)
        (MonoidHom.id (G ⧸ N)) (fQ q).toLinearMap (c q).hom.toLinearMap
        (Representation.IntertwiningMap.isIntertwining _ _ (fQ q))
        (he q) ψ (fun _ _ _ => rfl)
    have hi := iso_inv_naturality ((A.quotientBar M q).onHomology p) ((B.quotientBar L q).onHomology p)
      (commonBar_homology.{u,v,max v a,max v b,t}
        (A.quotientBar M q) (B.quotientBar L q) φ hbar p)
    have hs := S.hom.naturality b
    change D.page 0 p ((p : ℤ) + q) ≫ (S.app Y).hom =
      (S.app X).hom ≫ HomologicalComplex.homologyMap ψ p at hs
    change D.page 0 p ((p : ℤ) + q) ≫ (S.app Y).hom ≫ ((B.quotientBar L q).onHomology p).inv =
      (S.app X).hom ≫ ((A.quotientBar M q).onHomology p).inv ≫
        commonHomologyMap.{u,max v a,max v b,t} φ p
    rw [← Category.assoc, hs, Category.assoc, hi]
  · intro n
    let S := displayedTarget C E n
    let ψ := (repHomogeneousFunctor.{u,v,max v a b t} k G).map b
    let φ := commonPullback.{u,v,a,b,t} (hG := hG) (hH := hG')
      (MonoidHom.id G) f.toLinearMap (Representation.IntertwiningMap.isIntertwining M.ρ L.ρ f)
    have hbar : φ ≫ (B.groupBar L).cochain.hom = (A.groupBar M).cochain.hom ≫ ψ :=
      commonBar_pullback.{u,v,a,b,t} (A.groupBar M) (B.groupBar L) (MonoidHom.id G)
        f.toLinearMap b.hom.toLinearMap (Representation.IntertwiningMap.isIntertwining M.ρ L.ρ f)
        (fun z => (commonCoefficientMap_apply.{u,v,a,b,t} f z).symm) ψ (fun _ _ _ => rfl)
    have hi := iso_inv_naturality ((A.groupBar M).onHomology n) ((B.groupBar L).onHomology n)
      (commonBar_homology.{u,v,a,b,t} (A.groupBar M) (B.groupBar L) φ hbar n)
    have hs := S.hom.naturality b
    change D.target n ≫ (S.app Y).hom = (S.app X).hom ≫ HomologicalComplex.homologyMap ψ n at hs
    change D.target n ≫ (S.app Y).hom ≫ ((B.groupBar L).onHomology n).inv =
      (S.app X).hom ≫ ((A.groupBar M).onHomology n).inv ≫
        commonHomologyMap.{u,max v a,max v b,t} φ n
    rw [← Category.assoc, hs, Category.assoc, hi]

open AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction in
private def injectiveComparison (h : SquareZero.{u,v,w} k N) (M : Rep.{w} k G) (j : ℕ)
    (I : InjectiveResolution ((coefficientLift.{u,v,w,s} k G).obj M)) :
    (complex h (Rep.res N.subtype M)).homology j ≃ₗ[k]
      (Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction.invariantResolutionComplex.{u,v,max w s} k G N ((coefficientLift.{u,v,w,s} k G).obj M) I).homology j :=
  ((subgroupBarComparison.{u,v,w,s} N h M).linearEquiv j).trans
    (comparisonModuleIso.{u,v,max w s} k G N ((coefficientLift.{u,v,w,s} k G).obj M) j I).toLinearEquiv

open AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction in
private lemma injectiveComparison_action (h : SquareZero.{u,v,w} k N)
    (C : CohomologyModels.{u,v,max w s} k G N) (M : Rep.{w} k G) (j : ℕ)
    (I : InjectiveResolution ((coefficientLift.{u,v,w,s} k G).obj M))
    (q : G ⧸ N) (z : (complex h (Rep.res N.subtype M)).homology j) :
    let K := Specs.AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction.invariantResolutionComplex.{u,v,max w s} k G N ((coefficientLift.{u,v,w,s} k G).obj M) I
    injectiveComparison.{u,v,w,s} N h M j I (subgroupPageAction.{u,v,w,s} N h C M j q z) =
      (K.homology j).ρ q (injectiveComparison.{u,v,w,s} N h M j I z) := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    let L := (coefficientLift.{u,v,w,s} k G).obj M
    let c := (subgroupBarComparison.{u,v,w,s} N h M).linearEquiv j
    let e := comparisonRepIso.{u,v,max w s} k G N L j I
    have hact := congrArg (fun f => f z) (subgroupPageAction_formula.{u,v,w,s} N h C M j g)
    change e.hom.hom (c (subgroupPageAction.{u,v,w,s} N h C M j (QuotientGroup.mk' N g) z)) =
      _
    exact (congrArg (fun x => e.hom.hom (c x)) hact).trans
      ((congrArg e.hom.hom (subgroupBarComparison_action.{u,v,w,s} N h M g j z)).trans
        (Rep.hom_comm_apply e.hom (QuotientGroup.mk' N g) (c z)))

set_option maxHeartbeats 1000000 in
open AdvancedHomologicalAlgebra.GroupQuotientCohomologyAction in
private theorem commonInjectiveNatural :
    InjectiveNaturality.{u,v,a,b,t} (makePageComparisons.{u,v,a,max v b t} N hG hN hQ C)
      (makePageComparisons.{u,v,b,max v a t} N hG' hN' hQ' C) := by
  refine ⟨injectiveComparison.{u,v,a,max v b t} N hN, injectiveComparison.{u,v,b,max v a t} N hN',
    injectiveComparison_action.{u,v,a,max v b t} N hN C,
    injectiveComparison_action.{u,v,b,max v a t} N hN' C, ?_⟩
  intro M L f j I J φ z
  let b := commonCoefficientMap.{u,v,a,b,t} f
  let c := (subgroupBarComparison.{u,v,a,max v b t} N hN M).linearEquiv j
  let Y := (coefficientLift.{u,v,b,max v a t} k G).obj L
  have h := commonSubgroup_natural.{u,v,a,b,t} (hN' := hN') N f j z
  exact (congrArg (comparisonModuleIso.{u,v,max v a b t} k G N Y j J).hom.hom h).trans
    (congrArg (fun g => g.hom (c z)) (comparisonModuleIso_natural.{u,v,max v a b t} k G N b j I J φ))

private lemma square_of_comparisons {D : Type*} [Category D] {X Y X₁ Y₁ X' Y' X₁' Y₁' : D}
    (i : X ≅ X') (j : Y ≅ Y') (i₁ : X₁ ≅ X₁') (j₁ : Y₁ ≅ Y₁')
    {f : X ⟶ Y} {f₁ : X₁ ⟶ Y₁} {g : X ⟶ X₁} {g₁ : Y ⟶ Y₁}
    {f' : X' ⟶ Y'} {f₁' : X₁' ⟶ Y₁'} {g' : X' ⟶ X₁'} {g₁' : Y' ⟶ Y₁'}
    (hf : f ≫ j.hom = i.hom ≫ f') (h₁ : f₁ ≫ j₁.hom = i₁.hom ≫ f₁')
    (hg : g ≫ i₁.hom = i.hom ≫ g') (hg₁ : g₁ ≫ j₁.hom = j.hom ≫ g₁')
    (h : f' ≫ g₁' = g' ≫ f₁') : f ≫ g₁ = g ≫ f₁ := by
  apply (cancel_mono j₁.hom).mp
  calc
    (f ≫ g₁) ≫ j₁.hom = (f ≫ j.hom) ≫ g₁' := by rw [Category.assoc, hg₁, Category.assoc]
    _ = i.hom ≫ (f' ≫ g₁') := by rw [hf, Category.assoc]
    _ = (g ≫ i₁.hom) ≫ f₁' := by rw [h, hg, Category.assoc]
    _ = (g ≫ f₁) ≫ j₁.hom := by rw [Category.assoc, Category.assoc, h₁]

private lemma edgeBarCoordinates
    {hG : SquareZero.{u,v,w} k G} {hN : SquareZero.{u,v,w} k N}
    {hQ : SquareZero.{u,v,max v w} k (G ⧸ N)} {hQ₀ : SquareZero.{u,v,w} k (G ⧸ N)}
    {C : CohomologyModels.{u,v,max w s} k G N}
    {P : Package (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N)}
    {E : ObjectEdges (subgroupInvariants.{u,v,max w s} k G N) (quotientInvariants.{u,v,max w s} k G N) P}
    {A : PageComparisons.{u,v,w,s} N hG hN hQ C} {e : EdgeIdentifications C P E}
    {M : Rep.{w} k G} (o : OriginalEdges.{u,v,w,s} A e hQ₀ M) :
    let U := scalarLift.{u,v,w,s} k
    let X := (coefficientLift.{u,v,w,s} k G).obj M
    (∀ n, U.map (HomologicalComplex.homologyMap (inflation N hG hQ₀ M) n) ≫
        ((A.groupBar M).onHomology n).hom =
      (o.rowBar.onHomology n).hom ≫ HomologicalComplex.homologyMap (e.inflationCochain.app X) n) ∧
    (∀ n, U.map (o.restrict n) ≫ (o.invariantIso n).hom =
      ((A.groupBar M).onHomology n).hom ≫ (e.restriction.map n).app X) ∧
    U.map o.transgression ≫ (o.rowBar.onHomology 2).hom =
      (o.invariantIso 1).hom ≫ ordinaryTransgression C E X := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨z⟩
    exact o.inflation_compare n z
  · intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨z⟩
    exact o.restriction_compare n z
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨z⟩
    exact (o.rowBar.linearEquiv 2).apply_symm_apply _

private lemma ordinaryTransgression_natural {X Y : Rep.{max u v a b t} k G}
    (f : X ⟶ Y) :
    (C.subgroup 1 ⋙ quotientInvariants.{u,v,max v a b t} k G N).map f ≫ ordinaryTransgression C E Y =
      ordinaryTransgression C E X ≫ (subgroupInvariants.{u,v,max v a b t} k G N ⋙
        repHomogeneousCohomology.{u,v,max v a b t} k (G ⧸ N) 2).map f := by
  let D := (objectSequence _ _ P).map f
  let d X := AdvancedHomologicalAlgebra.G05FilteredEdges.transgression ((objectSequence _ _ P).obj X)
  let c := columnCoordinates C E 1
  let r := rowCoordinates C E 2
  have hc := c.inv.naturality f
  have hr := r.hom.naturality f
  have hd : D.page 0 0 1 ≫ d Y = d X ≫ D.page 0 2 2 := D.differential_comm 0 0 1
  change _ ≫ (c.inv.app Y ≫ d Y ≫ r.hom.app Y) = (c.inv.app X ≫ d X ≫ r.hom.app X) ≫ _
  calc
    _ = (_ ≫ c.inv.app Y) ≫ (d Y ≫ r.hom.app Y) := (Category.assoc _ _ _).symm
    _ = (c.inv.app X ≫ D.page 0 0 1) ≫ (d Y ≫ r.hom.app Y) :=
      congrArg (· ≫ (d Y ≫ r.hom.app Y)) hc
    _ = c.inv.app X ≫ (D.page 0 0 1 ≫ d Y) ≫ r.hom.app Y := by simp only [Category.assoc]
    _ = c.inv.app X ≫ (d X ≫ D.page 0 2 2) ≫ r.hom.app Y :=
      congrArg (fun g => c.inv.app X ≫ g ≫ r.hom.app Y) hd
    _ = c.inv.app X ≫ d X ≫ (D.page 0 2 2 ≫ r.hom.app Y) := by simp only [Category.assoc]
    _ = c.inv.app X ≫ d X ≫ (r.hom.app X ≫ _) :=
      congrArg (fun g => c.inv.app X ≫ d X ≫ g) hr
    _ = _ := by simp only [Category.assoc]

set_option maxHeartbeats 2200000 in
private theorem commonEdgesNatural
    {hQ₀ : SquareZero.{u,v,a} k (G ⧸ N)} {hQ₀' : SquareZero.{u,v,b} k (G ⧸ N)}
    (e : EdgeIdentifications C P E) :
    EdgesNatural.{u,v,a,b,t} E (makePageComparisons.{u,v,a,max v b t} N hG hN hQ C)
      (makePageComparisons.{u,v,b,max v a t} N hG' hN' hQ' C) (hQ₀ := hQ₀) (hQ₀' := hQ₀') e := by
  intro M L f o o'
  let A := makePageComparisons.{u,v,a,max v b t} N hG hN hQ C
  let B := makePageComparisons.{u,v,b,max v a t} N hG' hN' hQ' C
  let U := scalarLift.{u,v,a,max v b t} k
  let V := scalarLift.{u,v,b,max v a t} k
  let X := (coefficientLift.{u,v,a,max v b t} k G).obj M
  let Y := (coefficientLift.{u,v,b,max v a t} k G).obj L
  let b' := commonCoefficientMap.{u,v,a,b,t} f
  let bN := (subgroupInvariants.{u,v,max v a b t} k G N).map b'
  obtain ⟨fQ, hfQ, _, _⟩ := commonPagesNatural.{u,v,a,b,t} (hG := hG) (hN := hN)
    (hQ := hQ) (hG' := hG') (hN' := hN') (hQ' := hQ') N E M L f
  refine ⟨fQ, hfQ, ?_⟩
  let φ := commonPullback.{u,v,a,b,t} (hG := hG) (hH := hG') (MonoidHom.id G) f.toLinearMap
    (Representation.IntertwiningMap.isIntertwining M.ρ L.ρ f)
  let T := commonHomologyMap.{u,max v a,max v b,t} φ
  let f₀ := fixedMap N f
  let φ₀ := commonPullback.{u,v,a,b,t} (hG := hQ₀) (hH := hQ₀') (MonoidHom.id (G ⧸ N)) f₀.toLinearMap
    (Representation.IntertwiningMap.isIntertwining _ _ f₀)
  let R := commonHomologyMap.{u,max v a,max v b,t} φ₀
  let K (n : ℕ) : U.obj (ModuleCat.of k (A.action M n).invariants) ⟶
      V.obj (ModuleCat.of k (B.action L n).invariants) :=
    ModuleCat.ofHom (show ULift.{max u v b t} (A.action M n).invariants →ₗ[k]
        ULift.{max u v a t} (B.action L n).invariants from
      ULift.moduleEquiv.symm.toLinearMap.comp
        ((onInvariants _ _ (fQ n)).comp ULift.moduleEquiv.toLinearMap))
  let ψ := (repHomogeneousFunctor.{u,v,max v a b t} k G).map b'
  let ψ₀ := (repHomogeneousFunctor.{u,v,max v a b t} k (G ⧸ N)).map bN
  have ht (n : ℕ) : T n ≫ ((B.groupBar L).onHomology n).hom =
      ((A.groupBar M).onHomology n).hom ≫ HomologicalComplex.homologyMap ψ n :=
    commonBar_homology.{u,v,a,b,t} (A.groupBar M) (B.groupBar L) φ
      (commonBar_pullback.{u,v,a,b,t} (A.groupBar M) (B.groupBar L) (MonoidHom.id G)
        f.toLinearMap b'.hom.toLinearMap (Representation.IntertwiningMap.isIntertwining M.ρ L.ρ f)
        (fun z => (commonCoefficientMap_apply.{u,v,a,b,t} f z).symm) ψ (fun _ _ _ => rfl)) n
  have he (z : fixed N M) : o'.fixedCompare (f₀ z) = bN.hom (o.fixedCompare z) := by
    apply Subtype.ext
    change (o'.fixedCompare (f₀ z)).val = b'.hom (o.fixedCompare z).val
    rw [o'.fixed_formula, o.fixed_formula]
    exact (commonCoefficientMap_apply.{u,v,a,b,t} f z.val).symm
  have hr (n : ℕ) : R n ≫ (o'.rowBar.onHomology n).hom =
      (o.rowBar.onHomology n).hom ≫ HomologicalComplex.homologyMap ψ₀ n :=
    commonBar_homology.{u,v,a,b,t} o.rowBar o'.rowBar φ₀
      (commonBar_pullback.{u,v,a,b,t} o.rowBar o'.rowBar (MonoidHom.id (G ⧸ N))
        f₀.toLinearMap bN.hom.toLinearMap (Representation.IntertwiningMap.isIntertwining _ _ f₀)
        he ψ₀ (fun _ _ _ => rfl)) n
  have hc (n : ℕ) : K n ≫ (o'.invariantIso n).hom =
      (o.invariantIso n).hom ≫ (C.subgroup n ⋙ quotientInvariants.{u,v,max v a b t} k G N).map b' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨z⟩
    apply Subtype.ext
    change (o'.column n (onInvariants _ _ (fQ n) z)).val =
      ((C.subgroup n).map b').hom (o.column n z).val
    rw [o'.column_formula, o.column_formula]
    exact (congrArg (B.subgroup L n) (hfQ n z.val)).trans
      (commonSubgroupPage_natural.{u,v,a,b,t} (C := C) (hN' := hN') N f n z.val)
  obtain ⟨hi, hj, hd⟩ := edgeBarCoordinates.{u,v,a,max v b t} N o
  obtain ⟨hi', hj', hd'⟩ := edgeBarCoordinates.{u,v,b,max v a t} N o'
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact square_of_comparisons (o.rowBar.onHomology n) (o'.rowBar.onHomology n)
      ((A.groupBar M).onHomology n) ((B.groupBar L).onHomology n)
      (hr n) (ht n) (hi n) (hi' n)
      ((whiskerRight e.inflationCochain (HomologicalComplex.homologyFunctor _ (.up ℕ) n)).naturality b')
  · intro n
    exact square_of_comparisons ((A.groupBar M).onHomology n) ((B.groupBar L).onHomology n)
      (o.invariantIso n) (o'.invariantIso n) (ht n) (hc n) (hj n) (hj' n)
      ((e.restriction.map n).naturality b')
  · exact square_of_comparisons (o.invariantIso 1) (o'.invariantIso 1)
      (o.rowBar.onHomology 2) (o'.rowBar.onHomology 2) (hc 1) (hr 2) hd hd'
      (ordinaryTransgression_natural.{u,v,a,b,t} N E b')

set_option maxHeartbeats 1400000 in
theorem mixedSpectralSequence : spectralSequenceExpected.{u,v,a,b,t} := by
  intro k G _ _ N _
  obtain ⟨P, E, C, e, quadrant, five⟩ :=
    GroupHochschildSerre.lyndonHochschildSerre.{u,v,max v a b t} k G N
  let hG := squareZero.{u,v,a} k G
  let hN := squareZero.{u,v,a} k N
  let hQ := squareZero.{u,v,max v a} k (G ⧸ N)
  let hQ₀ := squareZero.{u,v,a} k (G ⧸ N)
  let hG' := squareZero.{u,v,b} k G
  let hN' := squareZero.{u,v,b} k N
  let hQ' := squareZero.{u,v,max v b} k (G ⧸ N)
  let hQ₀' := squareZero.{u,v,b} k (G ⧸ N)
  let A := makePageComparisons.{u,v,a,max v b t} N hG hN hQ C
  let B := makePageComparisons.{u,v,b,max v a t} N hG' hN' hQ' C
  refine ⟨P, E, C, e, hG, hN, hQ, hQ₀, hG', hN', hQ', hQ₀', A, B,
    originalNormalization.{u,v,a,max v b t} k G N hG hN hQ₀ C,
    originalNormalization.{u,v,b,max v a t} k G N hG' hN' hQ₀' C,
    commonPagesNatural.{u,v,a,b,t} N E, commonInjectiveNatural.{u,v,a,b,t} N,
    commonEdgesNatural.{u,v,a,b,t} N E (hQ₀ := hQ₀) (hQ₀' := hQ₀') e, quadrant, ?_, ?_⟩
  · intro M
    let o := makeOriginalEdges.{u,v,a,max v b t} N hG hN hQ hQ₀ e M
    exact ⟨o, originalFilteredCompatibility.{u,v,a,max v b t} N o,
      originalPageCoordinatesCompatibility.{u,v,a,max v b t} N o,
      originalZeroCoordinates.{u,v,a,max v b t} N o, originalFiveTerms.{u,v,a,max v b t} N o (five _)⟩
  · intro L
    let o := makeOriginalEdges.{u,v,b,max v a t} N hG' hN' hQ' hQ₀' e L
    exact ⟨o, originalFilteredCompatibility.{u,v,b,max v a t} N o,
      originalPageCoordinatesCompatibility.{u,v,b,max v a t} N o,
      originalZeroCoordinates.{u,v,b,max v a t} N o, originalFiveTerms.{u,v,b,max v a t} N o (five _)⟩

end Mixed

end Pages

end AdvancedHomologicalAlgebra.GroupExtensionOriginalCoefficients
