import Specs.LinearAlgebraicGroups.Descent.RelativeBasedAction
import LinearAlgebraicGroups.Classification.Pinning
import LinearAlgebraicGroups.RootData.DatumAndWeyl
import LinearAlgebraicGroups.Affine.AdjointRepresentation
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Dual.Lemmas

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj BigOperators TensorProduct Matrix

universe u

namespace LinearAlgebraicGroups.Descent.RelativeBasedAction

open _root_.LinearAlgebraicGroups.Specs
open Specs.RelativeBasedAction
open Specs.Pinning (SplitBorelPair AttachedDatum BasedIso transportCharacter)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.AbstractPairing (Root)
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors adjointWeightSpace characterValue)
open Specs.AdjointRepresentation (GroupPoints RelativeTangent TangentCoordinates dualMap reduction constants scale conjugate)

open private charactersOfIso cocharactersOfIso extendCoordinates canonicalZero_eq
  from LinearAlgebraicGroups.RootData.CharacterPairing
open private coroot_functional_of_reflection from LinearAlgebraicGroups.Classification.Pinning
open private tangent_coordinates map_comp_apply conjugationLinear conjugationLinear_spec
  conjugationLinear_naturality constants_dualMap constants_scale
  from LinearAlgebraicGroups.Affine.AdjointRepresentation

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k] {G H : GroupScheme k} {S : SchemeOver k}

private abbrev eval (f : sections G S ⟶ sections H S) (U : Over S) :
    (U.left ⟶ G.X) →* (U.left ⟶ H.X) := (f.app (op U)).hom

private theorem eval_naturality (f : sections G S ⟶ sections H S) {U V : Over S}
    (a : U ⟶ V) (p : V.left ⟶ G.X) :
    eval f U (a.left ≫ p) = a.left ≫ eval f V p :=
  congrArg (fun m => m.hom p) (f.naturality a.op)

private def Preserves {T G : GroupScheme k} (i : T ⟶ G)
    (f : RelativeAut G S) (e : RelativeAut T S) : Prop :=
  sectionMap i S ≫ f.asIso.hom = e.asIso.hom ≫ sectionMap i S

private theorem Preserves.eval_eq {T G : GroupScheme k} {i : T ⟶ G}
    {f : RelativeAut G S} {e : RelativeAut T S} (h : Preserves i f e) (U : Over S)
    (t : U.left ⟶ T.X) :
    eval f.asIso.hom U (t ≫ i.hom.hom) = eval e.asIso.hom U t ≫ i.hom.hom :=
  congrArg (fun a => eval a U t) h

private theorem Preserves.symm {T G : GroupScheme k} {i : T ⟶ G}
    {f : RelativeAut G S} {e : RelativeAut T S} (h : Preserves i f e) :
    Preserves i (Aut.of f.asIso.symm) (Aut.of e.asIso.symm) := by
  change sectionMap i S ≫ f.asIso.inv = e.asIso.inv ≫ sectionMap i S
  rw [← Category.id_comp (sectionMap i S ≫ f.asIso.inv), ← e.asIso.inv_hom_id,
    Category.assoc, ← Category.assoc e.asIso.hom, ← h, Category.assoc,
    f.asIso.hom_inv_id, Category.comp_id]

private abbrev testOver {R A : TestAlgebra k} (a : R ⟶ A) :
    Over ((testSpec k).obj (op R)) :=
  Over.mk ((testSpec k).map a.op)

private def testOverMap {R A B : TestAlgebra k} (a : R ⟶ A) (m : A ⟶ B) :
    testOver (a ≫ m) ⟶ testOver a :=
  Over.homMk ((testSpec k).map m.op) (by
    change (testSpec k).map m.op ≫ (testSpec k).map a.op = (testSpec k).map (a ≫ m).op
    rw [op_comp, Functor.map_comp])

private theorem eval_mapPoints {R A B : TestAlgebra k}
    (f : sections G ((testSpec k).obj (op R)) ⟶ sections H ((testSpec k).obj (op R)))
    (a : R ⟶ A) (m : A ⟶ B) (p : GroupPoints G A) :
    eval f (testOver (a ≫ m)) (mapPoints m p) = mapPoints m (eval f (testOver a) p) :=
  eval_naturality f (testOverMap a m) p

private theorem scalar_eval {T : GroupScheme k} (e : T ≅ T) (U : Over S)
    (t : U.left ⟶ T.X) :
    eval (scalarAut e S).asIso.hom U t = t ≫ e.hom.hom.hom := rfl

private theorem scalarAut_symm {T : GroupScheme k} (e : T ≅ T) :
    Aut.of (scalarAut e S).asIso.symm = scalarAut e.symm S := by
  apply Aut.ext
  apply Iso.ext
  rfl

private theorem characterValue_map {T : GroupScheme k} (χ : Character T)
    {A B : TestAlgebra k} (a : A ⟶ B) (t : GroupPoints T A) :
    characterValue χ B (mapPoints a t) = a.hom (characterValue χ A t) := by
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  unfold characterValue
  change (F.preimage ((testSpec k).map a.op ≫ t ≫ χ.hom.hom)).unop.hom _ = _
  rw [← Category.assoc (g := t)] at ⊢
  rw [Category.assoc (f := (testSpec k).map a.op)]
  rw [F.preimage_comp, show (testSpec k).map a.op = (algSpec (CommRingCat.of k)).map
    a.op from rfl, F.preimage_map]
  rfl

private theorem dualMap_comp {A B C : TestAlgebra k} (a : A ⟶ B) (b : B ⟶ C) :
    dualMap a ≫ dualMap b = dualMap (a ≫ b) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  exact TrivSqZeroExt.ext rfl rfl

private def relativeTangentMap {R : TestAlgebra k}
    (f : sections G ((testSpec k).obj (op R)) ⟶ sections H ((testSpec k).obj (op R)))
    (p : RelativeTangent G R) : RelativeTangent H R :=
  ⟨eval f (testOver (constants R)) p.toMul.val, by
    change mapPoints (reduction R) (eval f (testOver (constants R)) p.toMul.val) = 1
    rw [← eval_mapPoints, show mapPoints (reduction R) p.toMul.val = 1 from p.toMul.property,
      map_one]⟩

private theorem relativeTangentMap_ne_zero {R : TestAlgebra k}
    (f : RelativeAut G ((testSpec k).obj (op R))) (p : RelativeTangent G R) (hp : p ≠ 0) :
    relativeTangentMap f.asIso.hom p ≠ 0 := by
  intro h
  apply hp
  apply Subtype.ext
  have he := congrArg (fun x : RelativeTangent G R => x.toMul.val) h
  change eval f.asIso.hom (testOver (constants R)) p.toMul.val = 1 at he
  rw [← (eval f.asIso.hom (testOver (constants R))).map_one] at he
  exact (ConcreteCategory.bijective_of_isIso (f.asIso.hom.app
    (op (testOver (constants R))))).1 he

private theorem transport_relative_tangent (T : ClosedSubgroup G) {R A : TestAlgebra k}
    (f : RelativeAut G ((testSpec k).obj (op R))) (e : T.group ≅ T.group)
    (h : Preserves T.inclusion f (scalarAut e _)) (a : R ⟶ A)
    {χ : Character T.group} {v : Lie k G} (hv : v ∈ adjointWeightVectors T χ)
    (p : RelativeTangent G R)
    (hp : p.toMul.val = mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) v.toMul.val)
    (t : GroupPoints T.group A) :
    let q := (relativeTangentMap f.asIso.hom p).toMul.val
    let g := mapPoints (constants A) (t ≫ T.inclusion.hom.hom)
    g * mapPoints (dualMap a) q * g⁻¹ =
      mapPoints (scale A (characterValue (transportCharacter e χ) A t)) (mapPoints (dualMap a) q) := by
  dsimp only
  let s : GroupPoints T.group A := t ≫ e.inv.hom.hom
  let w : GroupPoints G (CommAlgCat.of k (DualNumber A)) :=
    mapPoints (dualMap a) p.toMul.val
  let gs : GroupPoints G (CommAlgCat.of k (DualNumber A)) :=
    mapPoints (constants A) (s ≫ T.inclusion.hom.hom)
  let c := characterValue χ A s
  have hw : w = mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k A))) v.toMul.val := by
    dsimp only [w]
    rw [hp, ← map_comp_apply, dualMap_comp]
    have he : (CommAlgCat.ofHom (Algebra.ofId k R)) ≫ a =
        CommAlgCat.ofHom (Algebra.ofId k A) := by ext
    rw [he]
  have hwt : gs * w * gs⁻¹ = mapPoints (scale A c) w := by
    rw [hw]
    exact hv A s
  let U := testOver (a ≫ constants A)
  let F := eval f.asIso.hom U
  let q := (relativeTangentMap f.asIso.hom p).toMul.val
  have hq : F w = mapPoints (dualMap a) q := by
    dsimp only [F, U, w, q, relativeTangentMap]
    rw [← constants_dualMap]
    exact eval_mapPoints _ _ _ _
  have hg : F gs = mapPoints (constants A) (t ≫ T.inclusion.hom.hom) := by
    have hf := h.eval_eq U (mapPoints (constants A) s)
    change F (mapPoints (constants A) s ≫ T.inclusion.hom.hom) =
      eval (scalarAut e _).asIso.hom U (mapPoints (constants A) s) ≫ T.inclusion.hom.hom at hf
    rw [scalar_eval] at hf
    have hs : s ≫ e.hom.hom.hom = t := by
      dsimp only [s]
      rw [Category.assoc, show e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ from
        ((Grp.forget (SchemeOver k)).mapIso e).inv_hom_id, Category.comp_id]
    simpa only [gs, mapPoints, Category.assoc, hs] using hf
  have hscale : F (mapPoints (scale A c) w) = mapPoints (scale A c) (F w) := by
    have hn := eval_mapPoints f.asIso.hom (a ≫ constants A) (scale A c) w
    rw [Category.assoc, constants_scale] at hn
    exact hn
  have hχ : characterValue (transportCharacter e χ) A t = c := rfl
  have hh := congrArg F hwt
  rw [map_mul, map_mul, map_inv, hscale, hg, hq] at hh
  simpa only [hχ] using hh

private theorem conjugation_weight_iff {J : Type u} [Fintype J] [DecidableEq J]
    [AddCommGroup (Lie k G)] [Module k (Lie k G)]
    {b : Module.Basis J k (Lie k G)} (C : TangentCoordinates G J b)
    (T : ClosedSubgroup G) (χ : Character T.group) (v : Lie k G) :
    v ∈ adjointWeightVectors T χ ↔ ∀ (A : TestAlgebra k) (t : GroupPoints T.group A),
      conjugationLinear C (t ≫ T.inclusion.hom.hom) (extendCoordinates b A v) =
        characterValue χ A t • extendCoordinates b A v := by
  unfold adjointWeightVectors
  change (∀ A t, _) ↔ _
  apply forall_congr'
  intro A
  apply forall_congr'
  intro t
  have hbase : (C.equiv A (extendCoordinates b A v)).toMul.val =
      mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k A))) v.toMul.val := by
    exact (C.naturality (CommAlgCat.ofHom (Algebra.ofId k A)) (b.equivFun v)).trans
      (congrArg (mapPoints _) (C.at_base v))
  change (mapPoints (constants A) (t ≫ T.inclusion.hom.hom) *
    mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k A))) v.toMul.val *
    (mapPoints (constants A) (t ≫ T.inclusion.hom.hom))⁻¹ =
    mapPoints (scale A (characterValue χ A t))
      (mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k A))) v.toMul.val)) ↔ _
  rw [← hbase, ← C.smul]
  change conjugate (t ≫ T.inclusion.hom.hom) (C.equiv A (extendCoordinates b A v)) = _ ↔ _
  rw [← conjugationLinear_spec C]
  exact ((Subtype.val_injective.comp (C.equiv A).injective).eq_iff)

private def tensorProjection {A R : TestAlgebra k} (φ : R →ₗ[k] k) :
    A ⊗[k] R →ₗ[k] A :=
  (TensorProduct.rid k A).toLinearMap.comp (TensorProduct.map LinearMap.id φ)

private theorem tensorProjection_tmul {A R : TestAlgebra k} (φ : R →ₗ[k] k) (x : A) (y : R) :
    tensorProjection φ (x ⊗ₜ[k] y) = algebraMap k A (φ y) * x := by
  simp only [tensorProjection, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul,
    LinearMap.id_apply, TensorProduct.rid_tmul, Algebra.smul_def]

private theorem includeLeft_mul_includeRight {A R : TestAlgebra k} (x : A) (y : R) :
    Algebra.TensorProduct.includeLeft (S := k) x * Algebra.TensorProduct.includeRight (R := k) y =
      x ⊗ₜ[k] y := by
  simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- Pairing the scalar coefficients with a ground-field linear form intertwines
conjugation by a point defined over the other tensor factor. -/
private theorem conjugation_tensor_projection {J : Type u} [Fintype J] [DecidableEq J]
    [AddCommGroup (Lie k G)] [Module k (Lie k G)]
    {b : Module.Basis J k (Lie k G)} (C : TangentCoordinates G J b)
    {A R : TestAlgebra k} (g : GroupPoints G A) (φ : R →ₗ[k] k) (z : J → R)
    (c : A) :
    let B := CommAlgCat.of k (A ⊗[k] R)
    let l : A ⟶ B := CommAlgCat.ofHom Algebra.TensorProduct.includeLeft
    let r : R ⟶ B := CommAlgCat.ofHom Algebra.TensorProduct.includeRight
    let w := fun j => r.hom (z j)
    conjugationLinear C (mapPoints l g) w = l.hom c • w →
      conjugationLinear C g (fun j => algebraMap k A (φ (z j))) =
        c • (fun j => algebraMap k A (φ (z j))) := by
  dsimp only
  let B := CommAlgCat.of k (A ⊗[k] R)
  let l : A ⟶ B := CommAlgCat.ofHom Algebra.TensorProduct.includeLeft
  let r : R ⟶ B := CommAlgCat.ofHom Algebra.TensorProduct.includeRight
  let F := conjugationLinear C (mapPoints l g)
  let E := conjugationLinear C g
  let p : B →ₗ[k] A := tensorProjection φ
  let w : J → B := fun j => r.hom (z j)
  let v : J → A := fun j => algebraMap k A (φ (z j))
  intro h
  change F w = l.hom c • w at h
  change E v = c • v
  have expand (K : Type u) [CommRing K] (s : J → K) :
      (∑ j, s j • Pi.single (M := fun _ : J => K) j 1) = s := by
    funext j
    simp [Pi.single_apply, mul_ite]
  have natural (j : J) :
      F (Pi.single j (1 : B)) = fun i => l.hom (E (Pi.single j (1 : A)) i) := by
    have h₁ := conjugationLinear_naturality C l g (Pi.single j (1 : A))
    have h₂ : (fun i => l.hom (Pi.single (M := fun _ : J => A) j 1 i)) =
        Pi.single j (1 : B) := by
      funext i
      by_cases he : i = j <;> simp [he]
    rwa [h₂] at h₁
  have pe (x : A) (y : R) : p (r.hom y * l.hom x) = algebraMap k A (φ y) * x := by
    rw [mul_comm]
    change tensorProjection φ
      (Algebra.TensorProduct.includeLeft x * Algebra.TensorProduct.includeRight y) = _
    rw [includeLeft_mul_includeRight, tensorProjection_tmul]
  have expandMap (K : Type u) [CommRing K] (D : (J → K) →ₗ[K] (J → K)) (s : J → K)
      (i : J) : D s i = ∑ j, s j * D (Pi.single j 1) i := by
    conv_lhs => rw [← expand K s]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  funext i
  have hi := congrArg (fun f : J → B => p (f i)) h
  change p (F w i) = p (l.hom c * r.hom (z i)) at hi
  rw [expandMap B F w, map_sum, mul_comm (l.hom c), pe] at hi
  simp only [natural, w, pe] at hi
  rw [expandMap A E v]
  exact hi.trans (mul_comm _ _)

/-- A nonzero tangent eigenvector after the relative action yields a nonzero
ground-field eigenvector by applying a linear form to its scalar coefficients. -/
private theorem transports_roots (G₀ : AffineAlgebraicGroup k) (T : ClosedSubgroup G₀.val)
    {R : TestAlgebra k} [Nontrivial R]
    (f : RelativeAut G₀.val ((testSpec k).obj (op R))) (e : T.group ≅ T.group)
    (h : Preserves T.inclusion f (scalarAut e _)) :
    Set.MapsTo (transportCharacter e) (absoluteRoots T) (absoluteRoots T) := by
  classical
  rintro χ ⟨hχ, v, hv, hv₀⟩
  let s := identityLieStructure G₀
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨n, b, ⟨C⟩⟩ := tangent_coordinates G₀ s
  let I := ULift.{u} (Fin n)
  let p := C.equiv R (extendCoordinates b R v)
  have hp : p.toMul.val =
      mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) v.toMul.val :=
    (C.naturality (CommAlgCat.ofHom (Algebra.ofId k R)) (b.equivFun v)).trans
      (congrArg (mapPoints _) (C.at_base v))
  have hp₀ : p ≠ 0 := by
    intro hp₀
    apply hv₀
    refine Eq.trans ?_ (canonicalZero_eq s).symm
    apply b.equivFun.injective
    refine Eq.trans ?_ b.equivFun.map_zero.symm
    have hzero : extendCoordinates b R v = 0 :=
      (C.equiv R).injective (hp₀.trans (C.equiv R).map_zero.symm)
    funext j
    change b.equivFun v j = 0
    apply (FaithfulSMul.algebraMap_injective k R)
    exact (congrFun hzero j).trans (map_zero (algebraMap k R)).symm
  let q := relativeTangentMap f.asIso.hom p
  have hq₀ : q ≠ 0 := relativeTangentMap_ne_zero f p hp₀
  let z : I → R := (C.equiv R).symm q
  have hz : C.equiv R z = q := (C.equiv R).apply_symm_apply _
  obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
    by_contra! hh
    apply hq₀
    rw [← hz, show z = 0 from funext hh, map_zero]
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero k hj
  let v' := b.equivFun.symm (fun i => φ (z i))
  have hne : v' ≠ 0 := by
    intro hzero
    apply hφ
    have hzero' := congrArg (fun v => b.equivFun v j) hzero
    simpa only [v', LinearEquiv.apply_symm_apply, map_zero, Pi.zero_apply] using hzero'
  refine ⟨?_, v', ?_, ?_⟩
  · intro hh
    exact hχ ((charactersOfIso e).injective (hh.trans (map_one (charactersOfIso e)).symm))
  · apply (conjugation_weight_iff C T _ v').mpr
    intro A t
    let B := CommAlgCat.of k (A ⊗[k] R)
    let l : A ⟶ B := CommAlgCat.ofHom Algebra.TensorProduct.includeLeft
    let r : R ⟶ B := CommAlgCat.ofHom Algebra.TensorProduct.includeRight
    let t' : GroupPoints T.group B := mapPoints l t
    let w : I → B := fun i => r.hom (z i)
    let g : GroupPoints G₀.val A := t ≫ T.inclusion.hom.hom
    let c := characterValue (transportCharacter e χ) A t
    have he := transport_relative_tangent T f e h r hv p hp t'
    change mapPoints (constants B) (mapPoints l g) * mapPoints (dualMap r) q.toMul.val *
      (mapPoints (constants B) (mapPoints l g))⁻¹ =
        mapPoints (scale B (characterValue (transportCharacter e χ) B t'))
          (mapPoints (dualMap r) q.toMul.val) at he
    have hq : (C.equiv B w).toMul.val = mapPoints (dualMap r) q.toMul.val := by
      rw [C.naturality r z, hz]
    rw [← hq, show characterValue (transportCharacter e χ) B t' = l.hom c from
      characterValue_map _ l t, ← C.smul] at he
    change conjugate (mapPoints l g) (C.equiv B w) = _ at he
    rw [← conjugationLinear_spec C] at he
    have hE := (Subtype.val_injective.comp (C.equiv B).injective) he
    have hdesc := conjugation_tensor_projection C g φ z c hE
    have hval : extendCoordinates b A v' = fun i => algebraMap k A (φ (z i)) := by
      ext i
      change algebraMap k A (b.equivFun v' i) = _
      rw [show b.equivFun v' = _ from b.equivFun.apply_symm_apply _]
    simpa only [hval] using hdesc
  · simpa only [canonicalZero_eq s] using hne

private def torusInBorel (P : SplitBorelPair k) {j : P.T.group ⟶ P.B.group}
    (hj : j ≫ P.B.inclusion = P.T.inclusion) : ClosedSubgroup P.B.group := by
  letI : IsClosedImmersion P.B.inclusion.hom.hom.left := P.B.isClosedImmersion
  haveI : IsClosedImmersion (j.hom.hom.left ≫ P.B.inclusion.hom.hom.left) := by
    change IsClosedImmersion (j ≫ P.B.inclusion).hom.hom.left
    rw [hj]
    exact P.T.isClosedImmersion
  exact ⟨P.T.group, j, IsClosedImmersion.of_comp_isClosedImmersion _ P.B.inclusion.hom.hom.left⟩

private theorem Preserves.factor {T B G : GroupScheme k} {i : T ⟶ G} {j : T ⟶ B}
    {l : B ⟶ G} [Mono l.hom.hom] (hj : j ≫ l = i)
    {f : RelativeAut G S} {b : RelativeAut B S} {e : RelativeAut T S}
    (ht : Preserves i f e) (hb : Preserves l f b) : Preserves j b e := by
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro t
  apply (cancel_mono l.hom.hom).mp
  change eval b.asIso.hom U.unop (t ≫ j.hom.hom) ≫ l.hom.hom =
      (eval e.asIso.hom U.unop t ≫ j.hom.hom) ≫ l.hom.hom
  rw [← hb.eval_eq, Category.assoc (f := t), ← Grp.comp_hom_hom, hj, ht.eval_eq,
    Category.assoc, ← Grp.comp_hom_hom, hj]

private theorem borel_weight_iff (P : SplitBorelPair k) {j : P.T.group ⟶ P.B.group}
    (hj : j ≫ P.B.inclusion = P.T.inclusion) (χ : Character P.T.group)
    (v : Lie k P.B.group) :
    v ∈ adjointWeightVectors (torusInBorel P hj) χ ↔
      mapPointKernel P.B.inclusion v ∈ adjointWeightVectors P.T χ := by
  letI : IsClosedImmersion P.B.inclusion.hom.hom.left := P.B.isClosedImmersion
  letI : Mono P.B.inclusion.hom.hom := Over.mono_of_mono_left _
  unfold adjointWeightVectors
  change (∀ R t, _) ↔ (∀ R t, _)
  apply forall_congr'
  intro R
  apply forall_congr'
  intro t
  dsimp only
  refine (cancel_mono P.B.inclusion.hom.hom).symm.trans ?_
  have htorus : t ≫ j.hom.hom ≫ P.B.inclusion.hom.hom = t ≫ P.T.inclusion.hom.hom :=
    congrArg (fun a : P.T.group ⟶ P.G.val => t ≫ a.hom.hom) hj
  simp only [MonObj.mul_comp, GrpObj.inv_comp, mapPoints, Category.assoc, torusInBorel, htorus]
  rfl

/-- The ambient root line lies in the Borel Lie algebra exactly when the Borel
has a nonzero vector with that weight. -/
private theorem subgroupRoots_iff (P : SplitBorelPair k) {j : P.T.group ⟶ P.B.group}
    (hj : j ≫ P.B.inclusion = P.T.inclusion) (α : Root P.T) :
    α ∈ BorelsAndChambers.subgroupRoots P.T P.B ↔
      α.val ∈ absoluteRoots (torusInBorel P hj) := by
  letI : IsClosedImmersion P.B.inclusion.hom.hom.left := P.B.isClosedImmersion
  letI : Mono P.B.inclusion.hom.hom := Over.mono_of_mono_left _
  have hinj : Function.Injective (mapPointKernel P.B.inclusion) := by
    intro v w h
    apply Subtype.ext
    exact (cancel_mono P.B.inclusion.hom.hom).mp
      (congrArg (fun x : Lie k P.G.val => x.toMul.val) h)
  have hzero : mapPointKernel P.B.inclusion (0 : Lie k P.B.group) = (0 : Lie k P.G.val) := by
    apply Subtype.ext
    change (1 : (testSpec k).obj (op (CommAlgCat.of k (DualNumber k))) ⟶ P.B.group.X) ≫
      P.B.inclusion.hom.hom = 1
    exact MonObj.one_comp _
  constructor
  · intro h
    obtain ⟨hn, v, hv, hv₀⟩ := α.property
    obtain ⟨w, rfl⟩ := h hv
    exact ⟨hn, w, (borel_weight_iff P hj _ _).mpr hv, fun hw => hv₀ (hw ▸ hzero)⟩
  · rintro ⟨_, v, hv, hv₀⟩
    let w := mapPointKernel P.B.inclusion v
    have hw := (borel_weight_iff P hj α.val v).mp hv
    have hw₀ : w ≠ 0 := fun he => hv₀ (hinj (he.trans hzero.symm))
    let s := identityLieStructure P.G
    letI := s.lieRing
    letI := s.lieAlgebra
    let W := adjointWeightSpace P.T α.val s
    have hW : (W : Set (Lie k P.G.val)) = adjointWeightVectors P.T α.val :=
      LinearAlgebraicGroups.RootData.CharacterPairing.adjointWeightSpaceVectors P.G P.T s α.val
    have hdim : Module.finrank k W = 1 :=
      ((LinearAlgebraicGroups.RootData.RootGroups.rootSubgroups P.G P.reductive P.T
        P.split P.maximal).2 α.val α.property).1 s
    have hspan : W = k ∙ w := eq_span_singleton_of_mem_of_finrank_eq_one hdim
      (by change w ∈ (W : Set _); rwa [hW])
      (by simpa only [canonicalZero_eq s] using hw₀)
    intro x hx
    have hx' : x ∈ W := by change x ∈ (W : Set _); rwa [hW]
    rw [hspan] at hx'
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx'
    let sB := identityLieStructure (Unipotent.closedSubgroupAlgebraicGroup P.B)
    letI := sB.lieRing
    letI := sB.lieAlgebra
    letI : IsAffine P.B.group.X.left :=
      (Unipotent.closedSubgroupAlgebraicGroup P.B).property.1
    letI : IsAffine P.G.val.X.left := P.G.property.1
    have hm := identityDifferentialLieHom k P.B.group P.G.val P.B.inclusion sB s
    obtain ⟨d, hd⟩ := hm
    refine ⟨c • v, ?_⟩
    change mapPointKernel P.B.inclusion (c • v) = x
    rw [← hd, map_smul, hd]
    exact hc

private theorem transports_simple (P : SplitBorelPair k)
    (r : Root P.T ≃ Root P.T) {e : P.T.group ≅ P.T.group}
    (hr : ∀ α, (r α).val = transportCharacter e α.val)
    (hp : ∀ α, r α ∈ BorelsAndChambers.subgroupRoots P.T P.B ↔
      α ∈ BorelsAndChambers.subgroupRoots P.T P.B) :
    ∀ α, Pinning.IsSimple P (r α) ↔ Pinning.IsSimple P α := by
  let L := charactersOfIso e
  intro α
  constructor
  · rintro ⟨hpos, hsimple⟩
    refine ⟨(hp α).mp hpos, fun β hβ δ hδ he => ?_⟩
    apply hsimple (r β) ((hp β).mpr hβ) (r δ) ((hp δ).mpr hδ)
    rw [hr, hr, hr]
    change L α.val = L β.val * L δ.val
    rw [← L.map_mul, he]
  · rintro ⟨hpos, hsimple⟩
    refine ⟨(hp α).mpr hpos, ?_⟩
    intro β hβ δ hδ he
    obtain ⟨β', rfl⟩ := r.surjective β
    obtain ⟨δ', rfl⟩ := r.surjective δ
    apply hsimple β' ((hp β').mp hβ) δ' ((hp δ').mp hδ)
    apply L.injective
    rw [hr, hr, hr] at he
    change L α.val = L β'.val * L δ'.val at he
    rwa [L.map_mul]

private def characterLinearEquiv {T : GroupScheme k} (e : T ≅ T) :
    Additive (Character T) ≃ₗ[ℤ] Additive (Character T) :=
  (charactersOfIso e).toAdditive.toIntLinearEquiv

private def cocharacterLinearEquiv {P : SplitBorelPair k}
    (D : AttachedDatum P) (e : P.T.group ≅ P.T.group) :
    letI := D.comm
    Additive (Cocharacter P.T.group) ≃ₗ[ℤ] Additive (Cocharacter P.T.group) := by
  letI := D.comm
  exact (cocharactersOfIso e.symm).toAdditive.toIntLinearEquiv

variable {P : SplitBorelPair k}

/-- A torus action preserving simple roots and carrying each rank-one
reflection to a root-datum automorphism preserves the attached coroots on
the full lattice. -/
private theorem basedAction_of_root_and_reflection_transport (D : AttachedDatum P)
    (e : P.T.group ≅ P.T.group) (r : Root P.T ≃ Root P.T)
    (hroot : ∀ α, (r α).val = transportCharacter e α.val)
    (hSimple : ∀ α, Pinning.IsSimple P (r α) ↔ Pinning.IsSimple P α)
    (hReflect : ∀ α, ∃ s : D.toBased.datum.Aut, ∀ v,
      s.weightEquiv v = characterLinearEquiv e
        (D.toBased.datum.reflection α ((characterLinearEquiv e).symm v))) :
    ∃ d : Aut D.toBased,
      (∀ χ : Character P.T.group, d.asIso.hom.val.weightEquiv (Additive.ofMul χ) =
        Additive.ofMul (transportCharacter e χ)) ∧
      (∀ c : Cocharacter P.T.group, d.asIso.hom.val.coweightEquiv (Additive.ofMul c) =
        Additive.ofMul (c ≫ e.inv)) := by
  let := D.comm
  let R := D.datum.rootDatum
  let L := characterLinearEquiv e
  let M := cocharacterLinearEquiv D e
  have hr (α : Root P.T) : L (R.root α) = R.root (r α) := by
    rw [D.datum.root_eq, D.datum.root_eq, hroot]
    rfl
  have hp (x : Additive (Character P.T.group)) (y : Additive (Cocharacter P.T.group)) :
      R.toLinearMap (L x) y = R.toLinearMap x (M y) := by
    change R.toLinearMap (Additive.ofMul (e.inv ≫ Additive.toMul x)) (Additive.ofMul (Additive.toMul y)) =
      R.toLinearMap (Additive.ofMul (Additive.toMul x)) (Additive.ofMul (Additive.toMul y ≫ e.inv))
    rw [D.datum.pairing_eq, D.datum.pairing_eq]
    unfold Specs.CharacterPairing.pairing Specs.CharacterDescent.compositionPairing
    rw [Category.assoc]
  have hc (α : Root P.T) : M (R.coroot (r α)) = R.coroot α := by
    let p := (R.toLinearMap.flip (R.coroot α)).comp L.symm.toLinearMap
    have hp₂ : p (R.root (r α)) = 2 := by
      change R.toLinearMap (L.symm (R.root (r α))) (R.coroot α) = 2
      rw [← hr, L.symm_apply_apply, R.root_coroot_two]
    obtain ⟨s, hs⟩ := hReflect α
    have hs' (x : Additive (Character P.T.group)) : s.weightEquiv x = x - p x • R.root (r α) := by
      rw [hs]
      change L (R.reflection α (L.symm x)) = _
      rw [RootPairing.reflection_apply]
      let v : Additive (Character P.T.group) := L.symm x
      let w : Additive (Character P.T.group) := p x • R.root α
      change L (v - w) = x - p x • R.root (r α)
      refine (L.map_sub v w).trans (congrArg₂ (· - ·) (L.apply_symm_apply x) ?_)
      exact (L.map_smul (p x) (R.root α)).trans (congrArg (p x • ·) (hr α))
    have hfun := coroot_functional_of_reflection R (r α) s p hp₂ hs'
    apply R.flip.toPerfPair.injective
    ext x
    change R.toLinearMap x (M (R.coroot (r α))) = R.toLinearMap x (R.coroot α)
    rw [← hp]
    have he := DFunLike.congr_fun hfun (L x)
    change R.toLinearMap (L x) (R.coroot (r α)) = R.toLinearMap (L.symm (L x)) (R.coroot α) at he
    rw [L.symm_apply_apply] at he
    exact he
  let b : BasedIso D.toBased D.toBased := ⟨{
    weightMap := L.toLinearMap
    coweightMap := M.toLinearMap
    indexEquiv := r
    bijective_weightMap := L.bijective
    bijective_coweightMap := M.bijective
    weight_coweight_transpose := by ext y x; exact hp x y
    root_weightMap := funext hr
    coroot_coweightMap := by
      funext j
      obtain ⟨i, rfl⟩ := r.surjective j
      change M (R.coroot (r i)) = R.coroot (r.symm (r i))
      rw [r.symm_apply_apply]
      exact hc i }, by
    ext j
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact (D.simple_iff _).mpr ((hSimple i).mpr ((D.simple_iff _).mp hi))
    · intro hj
      obtain ⟨i, rfl⟩ := r.surjective j
      exact ⟨i, (D.simple_iff _).mpr ((hSimple i).mp ((D.simple_iff _).mp hj)), rfl⟩⟩
  exact ⟨Aut.of (asIso (b : D.toBased ⟶ D.toBased)), fun _ => rfl, fun _ => rfl⟩

open Specs.BorelNormalizer (InducesTorusConjugation)
open Specs.NormalizerLatticeAction (ConstantGroup)
open Specs.GeometricRadicals (IsSplitTorus)
open CategoryTheory.Limits
open private reflectionConjugation actionOnDatum
  from LinearAlgebraicGroups.RootData.DatumAndWeyl
open private normalizes_iff_sections from LinearAlgebraicGroups.RootData.BorelNormalizer
open private isTorus_of_split from LinearAlgebraicGroups.RootData.CharacterPairing

private theorem transported_conjugation (T : ClosedSubgroup G)
    (f : RelativeAut G S) (e : T.group ≅ T.group)
    (ht : Preserves T.inclusion f (scalarAut e S))
    (n : 𝟙_ (SchemeOver k) ⟶ G.X) {c : T.group ≅ T.group}
    (hc : InducesTorusConjugation T n c)
    {Y : SchemeOver k} (a : Y ⟶ S)
    {Z : SchemeOver k} (z : Z ⟶ Y) (t : Z ⟶ T.group.X) :
    let g := eval f.asIso.hom (Over.mk a) (toUnit Y ≫ n)
    let d := e.symm ≪≫ c ≪≫ e
    (z ≫ g) * (t ≫ T.inclusion.hom.hom) * (z ≫ g)⁻¹ =
      t ≫ (d.hom ≫ T.inclusion).hom.hom := by
  dsimp only
  let U : Over S := Over.mk (z ≫ a)
  let z' : U ⟶ Over.mk a := Over.homMk z
  let F := eval f.asIso.hom U
  let s := t ≫ e.inv.hom.hom
  let nZ := toUnit Z ≫ n
  have hn : F nZ = z ≫ eval f.asIso.hom (Over.mk a) (toUnit Y ≫ n) := by
    have hh := eval_naturality f.asIso.hom z' (toUnit Y ≫ n)
    change F (z ≫ toUnit Y ≫ n) = _ at hh
    rw [← Category.assoc, comp_toUnit] at hh
    exact hh
  have hs : s ≫ e.hom.hom.hom = t := by
    dsimp only [s]
    rw [Category.assoc, show e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ from
      ((Grp.forget (SchemeOver k)).mapIso e).inv_hom_id, Category.comp_id]
  have htorus (x : Z ⟶ T.group.X) : F (x ≫ T.inclusion.hom.hom) =
      x ≫ e.hom.hom.hom ≫ T.inclusion.hom.hom := by
    rw [show F (x ≫ T.inclusion.hom.hom) = _ from ht.eval_eq U x, scalar_eval, Category.assoc]
  have hh : nZ * (s ≫ T.inclusion.hom.hom) * nZ⁻¹ =
      (s ≫ c.hom.hom.hom) ≫ T.inclusion.hom.hom := by
    have he := congrArg (s ≫ ·) hc.symm
    change s ≫ ((toUnit T.group.X ≫ n) * T.inclusion.hom.hom *
      (toUnit T.group.X ≫ n)⁻¹) = s ≫ (c.hom ≫ T.inclusion).hom.hom at he
    simpa only [nZ, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc s (toUnit _),
      comp_toUnit, Grp.comp_hom_hom, Category.assoc] using he
  have he := congrArg F hh
  rw [map_mul, map_mul, map_inv, htorus, ← Category.assoc s, hs, hn, htorus] at he
  simpa only [Iso.trans_hom, Iso.symm_hom, Grp.comp_hom_hom, Category.assoc, s] using he

private theorem scalar_cancellation {X Y Z : SchemeOver k} [Nonempty Y.left] {f g : X ⟶ Z}
    (h : fst X Y ≫ f = fst X Y ≫ g) : f = g := by
  let W := (Over.pullback Y.hom).obj X
  let U := (Over.map Y.hom).obj W
  let x : U ⟶ X := Over.homMk (pullback.fst X.hom Y.hom) pullback.condition
  let y : U ⟶ Y := Over.homMk W.hom
  have he := congrArg (lift x y ≫ ·) h
  simp only [lift_fst_assoc] at he
  have hs : Surjective Y.hom := ⟨Function.surjective_to_subsingleton Y.hom⟩
  have hp := IsPullback.of_hasPullback X.hom Y.hom
  let : Flat x.left := MorphismProperty.of_isPullback hp.flip (inferInstance : Flat Y.hom)
  let : Surjective x.left := MorphismProperty.of_isPullback hp.flip hs
  let : Epi x.left := Flat.epi_of_flat_of_surjective x.left
  apply Over.OverMorphism.ext
  exact (cancel_epi x.left).mp (congrArg (fun j => j.left) he)

private theorem family_constant_of_subsingleton {Q : GroupScheme k} {L : Type u} [Group L]
    (C : ConstantGroup Q L) {Y : SchemeOver k} [Subsingleton Y.left]
    (p : Y.left) (q : Y ⟶ Q.X) :
    ∃ w : L, q = toUnit Y ≫ C.sectionPoint w := by
  refine ⟨C.families Y q p, (C.families Y).injective ?_⟩
  rw [C.constant]
  apply LocallyConstant.ext
  intro x
  exact congrArg (C.families Y q) (Subsingleton.elim x p)

/-- Over a residue field the transported normalizer point lies over a single
Weyl label. The conjugation identity descends to the entire ground-field torus. -/
private theorem conjugated_reflection_action {P : SplitBorelPair k} (D : AttachedDatum P)
    (f : RelativeAut P.G.val S) (e : P.T.group ≅ P.T.group)
    (ht : Preserves P.T.inclusion f (scalarAut e S)) (x : S.left) (α : Root P.T) :
    ∃ s : D.toBased.datum.Aut, ∀ v,
      s.weightEquiv v = characterLinearEquiv e
        (D.toBased.datum.reflection α ((characterLinearEquiv e).symm v)) := by
  letI := D.comm
  let T := P.T
  let i := T.inclusion
  obtain ⟨n, _, c, hc, hw⟩ := reflectionConjugation D.datum α
  let d := e.symm ≪≫ c ≪≫ e
  let a₀ := S.left.fromSpecResidueField x
  let Y : SchemeOver k := Over.mk (a₀ ≫ S.hom)
  let a : Y ⟶ S := Over.homMk a₀
  let g := eval f.asIso.hom (Over.mk a) (toUnit Y ≫ n)
  haveI : Subsingleton Y.left := by
    change Subsingleton (Spec (S.left.residueField x))
    infer_instance
  let p : Y.left := (IsLocalRing.closedPoint (S.left.residueField x))
  haveI : Nonempty Y.left := ⟨p⟩
  have he {Z : SchemeOver k} (z : Z ⟶ Y) (t : Z ⟶ T.group.X) :
      (z ≫ g) * (t ≫ i.hom.hom) * (z ≫ g)⁻¹ = t ≫ (d.hom ≫ i).hom.hom :=
    transported_conjugation T f e ht n hc a z t
  have hg : Normalizes i g := by
    apply (normalizes_iff_sections T g).mpr
    intro Z z t
    refine ⟨⟨t ≫ d.hom.hom.hom, ?_⟩, t ≫ d.inv.hom.hom, ?_⟩
    · simpa only [Grp.comp_hom_hom, Category.assoc] using (he z t).symm
    · let t' := t ≫ d.inv.hom.hom
      have hd := he z t'
      have hh : t' ≫ (d.hom ≫ i).hom.hom = t ≫ i.hom.hom := by
        simp only [t', Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id_assoc]
      rw [hh] at hd
      change t' ≫ i.hom.hom = _
      rw [← hd]
      group
  obtain ⟨N, j, hj, W, q, hN, _, _, _, _, _, hsplit⟩ :=
    LinearAlgebraicGroups.Reductive.WeylScheme.weylScheme P.G P.reductive T
      (isTorus_of_split P.split) P.maximal
  obtain ⟨⟨I⟩, hlift⟩ := hsplit P.split
  obtain ⟨m, hm⟩ := (hN Y g).mp hg
  obtain ⟨w, hlabel⟩ := family_constant_of_subsingleton I.constantGroup p (m ≫ q.hom.hom)
  have hf := I.conjugates Y m w hlabel
  rw [hm] at hf
  have hc' : d = I.conjugation w := by
    apply Iso.ext
    apply Grp.hom_ext
    letI : IsClosedImmersion i.hom.hom.left := T.isClosedImmersion
    letI : Mono i.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono i.hom.hom).mp
    apply scalar_cancellation (Y := Y)
    have hcomp := (he (snd T.group.X Y) (fst T.group.X Y)).symm.trans hf
    simpa only [Grp.comp_hom_hom, Category.assoc, conjugateFamily] using hcomp
  obtain ⟨A, _, hA, _⟩ := actionOnDatum D.datum I hN (fun w => (hlift _).2)
  refine ⟨A w, fun v => ?_⟩
  let χ := Additive.toMul v
  change (A w).weightEquiv (Additive.ofMul χ) =
    characterLinearEquiv e
      ((RootPairing.Equiv.reflection D.datum.rootDatum α).weightEquiv
        (characterLinearEquiv e.symm (Additive.ofMul χ)))
  rw [hA, I.characterAction, ← hc']
  change Additive.ofMul (d.inv ≫ χ) =
    characterLinearEquiv e
      ((RootPairing.Equiv.reflection D.datum.rootDatum α).weightEquiv
        (Additive.ofMul (e.hom ≫ χ)))
  rw [hw]
  change Additive.ofMul (d.inv ≫ χ) = Additive.ofMul (e.inv ≫ c.inv ≫ e.hom ≫ χ)
  simp only [d, Iso.trans_inv, Iso.symm_inv, Category.assoc]

/-- Recognize the based action of an aligned automorphism over a nonempty affine test. -/
theorem relativeBasedAction : Specs.RelativeBasedAction.Statement.{u} := by
  intro k _ P D R S hS f b e ht hb
  letI : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp hS
  have ht' : Preserves P.T.inclusion (Aut.of f.asIso.symm) (scalarAut e.symm S) := by
    rw [← scalarAut_symm]
    exact (show Preserves P.T.inclusion f (scalarAut e S) from ht).symm
  have h := transports_roots P.G P.T f e ht
  have h' := transports_roots P.G P.T (Aut.of f.asIso.symm) e.symm ht'
  let r : Root P.T ≃ Root P.T :=
    { toFun := fun α => ⟨transportCharacter e α.val, h α.property⟩
      invFun := fun α => ⟨transportCharacter e.symm α.val, h' α.property⟩
      left_inv := fun α => Subtype.ext (by simp [transportCharacter])
      right_inv := fun α => Subtype.ext (by simp [transportCharacter]) }
  obtain ⟨j, hj⟩ := P.containsTorus
  let T' := torusInBorel P hj
  let B := Unipotent.closedSubgroupAlgebraicGroup P.B
  letI : IsClosedImmersion P.B.inclusion.hom.hom.left := P.B.isClosedImmersion
  letI : Mono P.B.inclusion.hom.hom := Over.mono_of_mono_left _
  have hjf : Preserves j b (scalarAut e S) := Preserves.factor hj ht hb
  have hjf' : Preserves j (Aut.of b.asIso.symm) (scalarAut e.symm S) := by
    rw [← scalarAut_symm]
    exact hjf.symm
  have hp (α : Root P.T) : r α ∈ BorelsAndChambers.subgroupRoots P.T P.B ↔
      α ∈ BorelsAndChambers.subgroupRoots P.T P.B := by
    rw [subgroupRoots_iff P hj, subgroupRoots_iff P hj]
    constructor
    · intro hα
      have hh := transports_roots B T' (Aut.of b.asIso.symm) e.symm hjf' hα
      change (e.hom ≫ e.inv ≫ α.val) ∈ absoluteRoots T' at hh
      simpa only [Iso.hom_inv_id_assoc] using hh
    · exact fun hα => transports_roots B T' b e hjf hα
  obtain ⟨x⟩ := hS
  exact basedAction_of_root_and_reflection_transport D e r (fun _ => rfl)
    (transports_simple P r (fun _ => rfl) hp)
    (conjugated_reflection_action D f e ht x)

end

end LinearAlgebraicGroups.Descent.RelativeBasedAction
