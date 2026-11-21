import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.Shapiro
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupCohomologyOriginalCoefficients
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! Shapiro's lemma for the original left group-algebra modules (HA-A04-Carrier).
The scalar and group rings remain fixed when lifting the coefficient carriers. -/
noncomputable section
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor
open scoped MonoidAlgebra ModuleCat.Algebra

namespace Specs.AdvancedHomologicalAlgebra.ShapiroOriginalCoefficients

universe u v w
variable (k : Type u) (G : Type v) [CommRing k] [Group G]
variable (H : Subgroup G)

open GroupCohomologyOriginalCoefficients
open Shapiro (derivedCohomology homogeneousFunctor)

abbrev ringInclusion : k[H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype

abbrev restrict := ModuleCat.restrictScalars (ringInclusion k G H)

abbrev restrictedRing := (restrict k G H).obj (ModuleCat.of k[G] k[G])

/-- Coinduction is literally the group-algebra-linear Hom with right translation
on the argument, including when its carrier is larger than that of the input module. -/
abbrev coinduction : Coeff.{u,v,w} k H ⥤ Coeff.{u,v,max u v w} k G :=
  ModuleCat.coextendScalars (ringInclusion k G H)

abbrev CoindHom (L : Coeff.{u,v,w} k H) := restrictedRing k G H →ₗ[k[H]] L

abbrev ambientRep : Coeff.{u,v,w} k G ⥤ Rep.{max u v w} k G :=
  lift.{u,v,w} k G ⋙ Rep.ofModuleMonoidAlgebra

/-- Evaluation at the identity, with the original restricted scalar action. -/
def evaluationLinear (L : Coeff.{u,v,w} k H) :
    ((coinduction k G H ⋙ restrict k G H).obj L) →ₗ[k[H]] L where
  toFun f := (show CoindHom k G H L from f) (1 : k[G])
  map_add' _ _ := rfl
  map_smul' r f := by
    change (show CoindHom k G H L from f) (1 * ringInclusion k G H r) =
      r • (show CoindHom k G H L from f) (1 : k[G])
    rw [one_mul, ← (show CoindHom k G H L from f).map_smul]
    congr 1
    change ringInclusion k G H r = ringInclusion k G H r * 1
    rw [mul_one]

/-- Both the original action and the coefficient maps use the unchanged group rings. -/
def OriginalCoinductionFormulas : Prop :=
  (∀ (L : Coeff.{u,v,w} k H) (g : G) (f : (coinduction k G H).obj L) (x : k[G]),
    (show CoindHom k G H L from MonoidAlgebra.single g (1 : k) • f) x =
      (show CoindHom k G H L from f) (x * MonoidAlgebra.single g 1)) ∧
  (∀ (L L' : Coeff.{u,v,w} k H) (b : L ⟶ L') (f : (coinduction k G H).obj L) (x : k[G]),
    (show CoindHom k G H L' from (coinduction k G H).map b f) x =
      b.hom ((show CoindHom k G H L from f) x))

abbrev Cochain (M : Coeff.{u,v,w} k G) (n : ℕ) :=
  (originalBar k G).X n →ₗ[k[G]] M

/-- Unsigned precomposition with the alternating-deletion boundary. -/
def homogeneousComplex (M : Coeff.{u,v,w} k G) :
    CochainComplex (ModuleCat.{max u v w} k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (Cochain k G M n))
    (fun n => ModuleCat.ofHom
      { toFun φ := φ.comp ((originalBar k G).d (n+1) n).hom
        map_add' _ _ := rfl
        map_smul' _ _ := rfl })
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro x
      have h := congrArg (fun f => ModuleCat.Hom.hom f x)
        ((originalBar k G).d_comp_d (n+2) (n+1) n)
      change φ (((originalBar k G).d (n+1) n).hom
        (((originalBar k G).d (n+2) (n+1)).hom x)) = 0
      rw [show ((originalBar k G).d (n+1) n).hom
        (((originalBar k G).d (n+2) (n+1)).hom x) = 0 from h, map_zero])

/-- Coefficients act on the bar Hom complex by postcomposition. -/
def originalHomogeneous : Coeff.{u,v,w} k G ⥤
    CochainComplex (ModuleCat.{max u v w} k) ℕ where
  obj := homogeneousComplex k G
  map b :=
    { f n := ModuleCat.ofHom
        { toFun φ := b.hom.comp φ
          map_add' _ _ := LinearMap.comp_add _ _ _
          map_smul' _ _ := LinearMap.comp_smul b.hom _ _ }
      comm' i j hij := by
        have h : j = i+1 := hij.symm
        subst j
        simp only [homogeneousComplex, CochainComplex.of_d]
        rfl }
  map_id _ := by ext n φ; rfl
  map_comp _ _ := by ext n φ; rfl

abbrev homologyAt (n : ℕ) :=
  HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} k) (.up ℕ) n

abbrev originalCohomology (n : ℕ) :=
  originalHomogeneous.{u,v,w} k G ⋙ homologyAt.{u,v,w} k n

/-- The comparison with the derived invariants on representations uses the
counit of the group-algebra module equivalence on the *given* carrier lift. -/
def derivedIdentify (n : ℕ) :
    derived.{u,v,w} k G n ≅ ambientRep.{u,v,w} k G ⋙ derivedCohomology.{u,v,max u v w} k G n :=
  isoWhiskerLeft (lift k G)
    ((leftUnitor _).symm ≪≫ isoWhiskerRight (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)).counitIso.symm _ ≪≫
      associator _ _ _) ≪≫ (associator _ _ _).symm

abbrev originalBarTransport (G : Type v) [Group G] :=
  ambientRep.{u,v,w} k G ⋙ homogeneousFunctor.{u,v,max u v w} k G ≅ originalHomogeneous.{u,v,w} k G

/-- The cochain carrier isomorphism is pointwise descent on every original tuple. -/
def PointwiseBar (e : originalBarTransport.{u,v,w} k G) : Prop :=
  ∀ (M : Coeff.{u,v,w} k G) n
    (φ : GroupBar.Large.B.{u,v,max u v w} k G n ⟶ (ambientRep k G).obj M)
    (c : Fin (n+1) → G),
    (show Cochain k G M n from ((e.hom.app M).f n).hom φ) (basisElement k G n c) =
      (φ.hom (GroupBar.Large.single.{u,v,max u v w} k G c 1)).down

abbrev coindLiftType :=
  coinduction.{u,v,w} k G H ⋙ ambientRep.{u,v,max u v w} k G ≅
    ambientRep.{u,v,w} k H ⋙ Shapiro.coindFunctor.{u,v,w} k G H

abbrev homLiftType :=
  coinduction.{u,v,w} k G H ⋙ lift.{u,v,max u v w} k G ≅
    lift.{u,v,w} k H ⋙ coinduction.{u,v,max u v w} k G H

/-- The pointwise map on the original Hom uses the same k[H]-action and
the same domain, even for the lifted coefficient. -/
def pointwiseHom (L : Coeff.{u,v,w} k H) (f : CoindHom k G H L) :
    CoindHom k G H ((lift.{u,v,w} k H).obj L) :=
  ULift.moduleEquiv.symm.toLinearMap.comp f

def PointwiseHomLift (e : homLiftType.{u,v,w} k G H) : Prop :=
  ∀ (L : Coeff.{u,v,w} k H) (f : (coinduction k G H ⋙ lift k G).obj L),
    (show CoindHom k G H ((lift k H).obj L) from (e.hom.app L).hom f) =
      pointwiseHom k G H L f.down

def PointwiseCoind (e : homLiftType.{u,v,w} k G H) (b : coindLiftType.{u,v,w} k G H) : Prop :=
  ∀ (L : Coeff.{u,v,w} k H) (f : (ambientRep k G).obj ((coinduction k G H).obj L)) (g : G),
    ((b.hom.app L).hom f).val g =
      (show CoindHom k G H ((lift k H).obj L) from (e.hom.app L).hom f)
        (MonoidAlgebra.single g 1)

/-- Restricting the coefficient isomorphism commutes with the coinduction
counit's evaluation at the group identity. -/
def LiftEvaluation (e : coindLiftType.{u,v,w} k G H) : Prop :=
  let res := Rep.resFunctor.{max u v w} (k := k) H.subtype
  let adj : res ⊣ Shapiro.coindFunctor.{u,v,w} k G H := Rep.resCoindAdjunction.{max u w,u,v,v} k H.subtype
  ∀ (L : Coeff.{u,v,w} k H) (f : (ambientRep k G).obj ((coinduction k G H).obj L)),
    ((res.map (e.hom.app L) ≫
      adj.counit.app ((ambientRep k H).obj L)).hom f).down =
      evaluationLinear k G H L f.down

/-- The original homogeneous formula, on the original Hom into coinduction. -/
def RestrictEvaluate (η : coinduction.{u,v,w} k G H ⋙ originalHomogeneous k G ⟶
    originalHomogeneous k H) : Prop :=
  ∀ (L : Coeff.{u,v,w} k H) n
    (φ : Cochain k G ((coinduction k G H).obj L) n) (c : Fin (n+1) → H),
    (show Cochain k H L n from ((η.app L).f n).hom φ) (basisElement k H n c) =
      (φ (basisElement k G n (fun i => (c i : G))) : CoindHom k G H L) (1 : k[G])

/-- A normalized ambient derived-to-bar comparison followed by pointwise descent. -/
def transportedBar {J : Type v} [Group J] (A : Shapiro.AugmentedBarComparison.{u,v,max u v w} k J)
    (e : originalBarTransport.{u,v,w} k J) (n : ℕ) :
    derived.{u,v,w} k J n ≅ originalCohomology.{u,v,w} k J n :=
  derivedIdentify k J n ≪≫ isoWhiskerLeft (ambientRep k J) (A.iso n) ≪≫
    (associator _ _ _).symm ≪≫ isoWhiskerRight e (homologyAt.{u,v,w} k n)

/-- Transport the accepted Shapiro isomorphism through the actual lift of coinduction. -/
def transportedDerived (A : Shapiro.ShapiroData.{u,v,max u v w} k G H)
    (e : coindLiftType.{u,v,w} k G H) (n : ℕ) :
    coinduction.{u,v,w} k G H ⋙ derived.{u,v,max u v w} k G n ≅ derived.{u,v,w} k H n :=
  isoWhiskerLeft (coinduction k G H) (derivedIdentify k G n) ≪≫
    (associator _ _ _).symm ≪≫ isoWhiskerRight e _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft (ambientRep k H) (A.derivedIso n) ≪≫
    (derivedIdentify k H n).symm

structure OriginalShapiroData (A : Shapiro.ShapiroData.{u,v,max u v w} k G H) where
  coind_formulas : OriginalCoinductionFormulas.{u,v,w} k G H
  homLift : homLiftType.{u,v,w} k G H
  hom_pointwise : PointwiseHomLift k G H homLift
  coindLift : coindLiftType.{u,v,w} k G H
  coind_pointwise : PointwiseCoind k G H homLift coindLift
  evaluation : LiftEvaluation k G H coindLift
  sourceCochains : originalBarTransport.{u,v,max u v w} k G
  source_pointwise : PointwiseBar k G sourceCochains
  targetCochains : originalBarTransport.{u,v,w} k H
  target_pointwise : PointwiseBar k H targetCochains
  cochain : coinduction.{u,v,w} k G H ⋙ originalHomogeneous k G ⟶ originalHomogeneous k H
  cochain_formula : RestrictEvaluate k G H cochain
  cochain_quasiIso : ∀ L, QuasiIso (cochain.app L)
  comparison : ∀ n,
    (transportedDerived k G H A coindLift n).hom ≫
      (transportedBar k A.targetBar targetCochains n).hom =
    whiskerLeft (coinduction k G H) (transportedBar k A.sourceBar sourceCochains n).hom ≫
      whiskerRight cochain (homologyAt.{u,v,w} k n)

/-- Existence on the original coefficients, together with transport for each
given normalized ambient comparison. -/
def originalShapiroExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (H : Subgroup G),
    Nonempty (Σ A : Shapiro.ShapiroData.{u,v,max u v w} k G H,
      OriginalShapiroData.{u,v,w} k G H A) ∧
      ∀ A : Shapiro.ShapiroData.{u,v,max u v w} k G H,
        Nonempty (OriginalShapiroData.{u,v,w} k G H A)

namespace Mixed

universe a b s

/-- Postcomposition of the original Hom defining coinduction, for an original
coefficient homomorphism whose domain and codomain can have different sizes. -/
def coindPost {L : Coeff.{u,v,a} k H} {L' : Coeff.{u,v,b} k H}
    (f : L →ₗ[k[H]] L') :
    (coinduction k G H).obj L →ₗ[k[G]] (coinduction k G H).obj L' where
  toFun z := f.comp (show CoindHom k G H L from z)
  map_add' _ _ := LinearMap.comp_add _ _ _
  map_smul' _ _ := rfl

abbrev scalarLift := ModuleCat.uliftFunctor.{s,max u v a} k

abbrev liftedComplex (M : Coeff.{u,v,a} k G) :
    CochainComplex (ModuleCat.{max u v a s} k) ℕ :=
  ((scalarLift.{u,v,a,s} k).mapHomologicalComplex (.up ℕ)).obj (homogeneousComplex k G M)

/-- The isomorphism on homology through the exact scalar lift of the
specified original cochain complex. -/
def homologyLift (M : Coeff.{u,v,a} k G) (n : ℕ) :
    (homogeneousComplex k G M).homology n ≃ₗ[k]
      (liftedComplex.{u,v,a,s} k G M).homology n :=
  ULift.moduleEquiv.symm.trans
    (((homogeneousComplex k G M).sc n).mapHomologyIso (scalarLift.{u,v,a,s} k)).symm.toLinearEquiv

/-- The two complexes use the same bar differential, and the cochain map
postcomposes with the given coefficient map in the original coordinates. -/
def postChain {M : Coeff.{u,v,a} k G} {N : Coeff.{u,v,b} k G} (f : M →ₗ[k[G]] N) :
    liftedComplex.{u,v,a,max a b s} k G M ⟶ liftedComplex.{u,v,b,max a b s} k G N where
  f n := ModuleCat.ofHom
    { toFun z := ULift.up (f.comp z.down)
      map_add' _ _ := congrArg ULift.up (LinearMap.comp_add _ _ _)
      map_smul' _ _ := congrArg ULift.up (LinearMap.comp_smul f _ _) }
  comm' i j hij := by
    obtain rfl : j = i+1 := hij.symm
    simp only [liftedComplex, Functor.mapHomologicalComplex_obj_d, homogeneousComplex,
      CochainComplex.of_d]
    rfl

def postHomology {M : Coeff.{u,v,a} k G} {N : Coeff.{u,v,b} k G}
    (f : M →ₗ[k[G]] N) (n : ℕ) :
    (homogeneousComplex k G M).homology n →ₗ[k] (homogeneousComplex k G N).homology n :=
  (homologyLift.{u,v,b,max a b s} k G N n).symm.toLinearMap.comp
    ((HomologicalComplex.homologyMap (postChain.{u,v,a,b,s} k G f) n).hom.comp
      (homologyLift.{u,v,a,max a b s} k G M n).toLinearMap)

abbrev largerCoefficient (M : Coeff.{u,v,a} k G) : Coeff.{u,v,max a s} k G :=
  (ModuleCat.uliftFunctor.{s,a} k[G]).obj M

/-- The common coefficient map is conjugation of the given map by the
pointwise carrier equivalences over the same group algebra. -/
def largerMap {M : Coeff.{u,v,a} k G} {N : Coeff.{u,v,b} k G} (f : M →ₗ[k[G]] N) :
    largerCoefficient.{u,v,a,max a b s} k G M ⟶ largerCoefficient.{u,v,b,max a b s} k G N :=
  ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp
    (f.comp ULift.moduleEquiv.toLinearMap))

/-- Compare the original cochains with those over a larger coefficient
carrier, using the same tuple domain and the given coefficient equivalence. -/
structure CochainLift (M : Coeff.{u,v,a} k G) (N : Coeff.{u,v,max u v a s} k G)
    (e : M ≃ₗ[k[G]] N) where
  iso : liftedComplex.{u,v,a,s} k G M ≅ homogeneousComplex k G N
  pointwise : ∀ n (z : Cochain k G M n),
    (show Cochain k G N n from (iso.hom.f n).hom (ULift.up z)) = e.toLinearMap.comp z

/-- The comparison on coinduction is the pointwise lift of the original
group-algebra Hom, with domain and right-translation action unchanged. -/
structure CoindLift (L : Coeff.{u,v,a} k H) where
  coeff : (coinduction k G H).obj L ≃ₗ[k[G]]
    (coinduction k G H).obj (largerCoefficient.{u,v,a,max u v a s} k H L)
  pointwise : ∀ (z : (coinduction k G H).obj L) (x : k[G]),
    (show CoindHom k G H _ from coeff z) x =
      ULift.up ((show CoindHom k G H L from z) x)
  source : CochainLift.{u,v,max u v a,s} k G _ _ coeff
  target : CochainLift.{u,v,a,s} k H L
    (largerCoefficient.{u,v,a,max u v a s} k H L) ULift.moduleEquiv.symm

abbrev scalarMap {M N : CochainComplex (ModuleCat.{max u v a} k) ℕ} (f : M ⟶ N) :=
  ((scalarLift.{u,v,a,s} k).mapHomologicalComplex (.up ℕ)).map f

/-- Mixed coefficient postcomposition commutes with each original Shapiro
map on cochains and homology. Both maps are compared with the same Shapiro
comparison on the lifted coefficients. -/
def naturalityType (L : Coeff.{u,v,a} k H) (L' : Coeff.{u,v,b} k H)
    (f : L →ₗ[k[H]] L')
    {A : Shapiro.ShapiroData.{u,v,max u v a} k G H}
    {A' : Shapiro.ShapiroData.{u,v,max u v b} k G H}
    (D : OriginalShapiroData.{u,v,a} k G H A)
    (D' : OriginalShapiroData.{u,v,b} k G H A') : Prop :=
  let S := scalarMap.{u,v,a,max u v a b s} k (D.cochain.app L)
  let T := scalarMap.{u,v,b,max u v a b s} k (D'.cochain.app L')
  let c := coindPost k G H f
  let p := postChain.{u,v,max u v a,max u v b,s} k G c
  let q := postChain.{u,v,a,b,max u v s} k H f
  (S ≫ q = p ≫ T) ∧
  (∀ n x, postHomology.{u,v,a,b,max u v s} k H f n
      ((HomologicalComplex.homologyMap (D.cochain.app L) n).hom x) =
    (HomologicalComplex.homologyMap (D'.cochain.app L') n).hom
      (postHomology.{u,v,max u v a,max u v b,s} k G c n x)) ∧
  ∀ (B : Shapiro.ShapiroData.{u,v,max u v a b s} k G H)
    (E : OriginalShapiroData.{u,v,max u v a b s} k G H B),
    ∃ (I : CoindLift.{u,v,a,max u v a b s} k G H L)
      (J : CoindLift.{u,v,b,max u v a b s} k G H L'),
      let g := largerMap.{u,v,a,b,max u v s} k H f
      (S ≫ I.target.iso.hom = I.source.iso.hom ≫ E.cochain.app _) ∧
      (T ≫ J.target.iso.hom = J.source.iso.hom ≫ E.cochain.app _) ∧
      (p ≫ J.source.iso.hom = I.source.iso.hom ≫
        (coinduction k G H ⋙ originalHomogeneous k G).map g) ∧
      (q ≫ J.target.iso.hom = I.target.iso.hom ≫ (originalHomogeneous k H).map g)

def naturalityExpected : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G] (H : Subgroup G)
    {L : Coeff.{u,v,a} k H} {L' : Coeff.{u,v,b} k H} (f : L →ₗ[k[H]] L')
    {A : Shapiro.ShapiroData.{u,v,max u v a} k G H}
    {A' : Shapiro.ShapiroData.{u,v,max u v b} k G H}
    (D : OriginalShapiroData.{u,v,a} k G H A)
    (D' : OriginalShapiroData.{u,v,b} k G H A'),
    naturalityType.{u,v,a,b,s} k G H L L' f D D'

end Mixed

end Specs.AdvancedHomologicalAlgebra.ShapiroOriginalCoefficients
