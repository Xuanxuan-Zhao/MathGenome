import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalLeviRadicalGeneration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.InnerTypeALocalGeneration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.InnerTypeASplitRank
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedCongruencePointTopology
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct WithZero

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalLeviRadicalGeneration

open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.ExceptionalLeviRadicalGeneration
open LinearAlgebraicGroups.Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open LinearAlgebraicGroups.Specs.CharacterDescent (Cocharacter)
open LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.Specs.AdjointCocharacters (coordinateHopfIso)

private noncomputable abbrev groupCoordinates := @LinearAlgebraicGroups.Specs.AdjointCocharacters.coordinateHopf
open LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent (coordinatePointEquiv)
open LinearAlgebraicGroups.Specs.InnerTypeARelativeContraction
open LinearAlgebraicGroups.Specs.InnerTypeASplitRank (RelativeBlockDescription)
open LinearAlgebraicGroups.Specs.Unipotent (Index closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics
open LocalNormOneCommutators.Spec (coordinateTopology elementary elementaryGroup normOne)
open _root_.Specs.RM03.CSA (isCentralSimple isCentralDivision reducedNorm)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {F : Type u} [Field F]

private abbrev ground (F : Type u) [Field F] : TestAlgebra F := CommAlgCat.of F F
private abbrev RationalPoints (G : GroupScheme F) := 𝟙_ (SchemeOver F) ⟶ G.X

private def rationalEquiv (G : GroupScheme F) : RationalPoints G ≃* GroupPoints G (ground F) where
  toFun p := (groundPointIso F).inv ≫ p
  invFun p := (groundPointIso F).hom ≫ p
  left_inv _ := Iso.hom_inv_id_assoc _ _
  right_inv _ := Iso.inv_hom_id_assoc _ _
  map_mul' _ _ := MonObj.comp_mul _ _ _

private abbrev onPoints {A B : GroupScheme F} (f : A ⟶ B) (R : TestAlgebra F) :
    GroupPoints A R →* GroupPoints B R :=
  ((groupPointsFunctor F).map f |>.app R).hom

private def onRational {A B : GroupScheme F} (f : A ⟶ B) :
    RationalPoints A →* RationalPoints B where
  toFun x := x ≫ f.hom.hom
  map_one' := MonObj.one_comp _
  map_mul' _ _ := MonObj.mul_comp _ _ _

private theorem rationalEquiv_post {A B : GroupScheme F} (f : A ⟶ B)
    (y : RationalPoints A) :
    (rationalEquiv B).symm (onPoints f (ground F) (rationalEquiv A y)) =
      onRational f y := by
  apply (rationalEquiv B).injective
  rw [MulEquiv.apply_symm_apply]
  exact (Category.assoc (groundPointIso F).inv y f.hom.hom).symm

private def rationalCoordinates (G : AffineAlgebraicGroup F) :
    RationalPoints G.val ≃* WithConv (groupCoordinates G →ₐ[F] F) :=
  (rationalEquiv G.val).trans (coordinatePointEquiv G (ground F)).symm

private theorem continuous_localPoints_iff [TopologicalSpace F] {P : Type*} [TopologicalSpace P]
    (G : AffineAlgebraicGroup F) (f : P → RationalPoints G.val) :
    letI := localPointTopology G
    Continuous f ↔ ∀ a : groupCoordinates G, Continuous fun p => rationalCoordinates G (f p) a := by
  change @Continuous _ _ _ (TopologicalSpace.induced _ (TopologicalSpace.induced _ _)) f ↔ _
  rw [continuous_induced_rng, continuous_induced_rng, continuous_pi_iff]
  rfl

private theorem continuous_rationalEvaluation [TopologicalSpace F] (G : AffineAlgebraicGroup F)
    (a : groupCoordinates G) :
    letI := localPointTopology G
    Continuous (fun p => rationalCoordinates G p a) :=
by
  letI := localPointTopology G
  exact (continuous_localPoints_iff G id).mp continuous_id a

open private continuous_convolutionEvaluation from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedCongruencePointTopology

private theorem localPointGroup [TopologicalSpace F] [IsTopologicalRing F]
    (G : AffineAlgebraicGroup F) :
    letI := localPointTopology G
    IsTopologicalGroup (RationalPoints G.val) := by
  letI := localPointTopology G
  refine { continuous_mul := (continuous_localPoints_iff G _).mpr ?_
           continuous_inv := (continuous_localPoints_iff G _).mpr ?_ }
  · intro a
    simp only [map_mul]
    exact continuous_convolutionEvaluation (rationalCoordinates G ∘ Prod.fst)
      (rationalCoordinates G ∘ Prod.snd)
      (fun b => (continuous_rationalEvaluation G b).comp continuous_fst)
      (fun b => (continuous_rationalEvaluation G b).comp continuous_snd) a
  · intro a
    simp only [map_inv]
    change Continuous fun p => rationalCoordinates G p (HopfAlgebra.antipodeAlgHom F (groupCoordinates G) a)
    exact continuous_rationalEvaluation G _

open private map_hasLimit from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility

open LinearAlgebraicGroups.Specs.GeometricRadicals (IsReductive)

private theorem mem_generated_of_limit [Infinite F] {G : AffineAlgebraicGroup F}
    (hG : IsReductive G) {A : GroupScheme F} (f : A ⟶ G.val) (c : Cocharacter A)
    (x : GroupPoints A (ground F)) (hx : HasLimit c x 1) :
    (rationalEquiv G.val).symm (onPoints f (ground F) x) ∈ unipotentGenerated G := by
  let d := c ≫ f
  obtain ⟨D⟩ := CocharacterDynamics.existsLimitDecomposition G d
  obtain ⟨E⟩ := CocharacterDynamics.existsLimitDecomposition G (oppositeCocharacter d)
  have h : HasLimit d (onPoints f (ground F) x) 1 := by
    have hh := map_hasLimit f c hx
    change HasLimit d (onPoints f (ground F) x) (onPoints f (ground F) 1) at hh
    rwa [map_one] at hh
  obtain ⟨p, hp⟩ := (D.contracting_points _ _).mp h
  apply (le_sup_left.trans (RelativeRayGeneration.twoRadicals_le_unipotentGenerated hG D E) :
    SubgroupSections D.contracting (𝟙_ (SchemeOver F)) ≤ unipotentGenerated G)
  refine ⟨(rationalEquiv D.contracting.group).symm p, ?_⟩
  change ((groundPointIso F).hom ≫ p) ≫ D.contracting.inclusion.hom.hom =
    (groundPointIso F).hom ≫ onPoints f (ground F) x
  exact (Category.assoc _ _ _).trans (congrArg ((groundPointIso F).hom ≫ ·) hp)

private theorem quotient_section_mem {A Q G : GroupScheme F}
    (f : A ⟶ G) (q : A ⟶ Q) (s : Q ⟶ A)
    (H : ClosedSubgroup A) (hker : IsSchemeKernel q H) (hsection : s ≫ q = 𝟙 Q)
    (C : Subgroup (RationalPoints G))
    (hH : ∀ x, onRational (H.inclusion ≫ f) x ∈ C)
    (hs : ∀ t, onRational (s ≫ f) t ∈ C)
    (x : RationalPoints A) : onRational f x ∈ C := by
  let y := onRational q x
  let z := onRational s y
  have hz : onRational q z = y := by
    change (y ≫ s.hom.hom) ≫ q.hom.hom = y
    rw [Category.assoc, ← Grp.comp_hom_hom, hsection, Grp.id_hom_hom, Category.comp_id]
  let w := x * z⁻¹
  have hw : onRational q w = 1 := by simp [w, hz, y]
  have hk : w ≫ q.hom.hom = 𝟙 _ ≫ η[Q.X] := by
    rw [Category.id_comp]
    exact hw
  let p := hker.lift w (𝟙 _) hk
  have hp : onRational H.inclusion p = w := hker.lift_fst _ _ _
  have hwz : w * z = x := by simp [w]
  rw [← hwz, map_mul]
  apply C.mul_mem
  · rw [← hp]
    exact hH p
  · exact hs y

section MatrixModel

open LinearAlgebraicGroups.Descent.InnerTypeA.Specification (NormOneCoordinates normOneIdeal)
open LinearAlgebraicGroups.Specs.StandardGroups (HopfOperations spectrum)
open _root_.Specs.RM03.CSA (genericReducedNorm)

variable {B : Type u} [DivisionRing B] [Algebra F B] {m : ℕ}
variable {hA : isCentralSimple F (Matrix (Fin m) (Fin m) B)}
variable {I : Type u} [Fintype I] {b : Module.Basis I F (Matrix (Fin m) (Fin m) B)}

private theorem normAt_ground (x : Matrix (Fin m) (Fin m) B) :
    normAt hA b ((1 : F) ⊗ₜ[F] x) = reducedNorm hA x := by
  obtain ⟨e⟩ := RM03.CSA.algEquiv_matrix_algebraicClosure hA
  exact (LinearAlgebraicGroups.Descent.InnerTypeA.reducedNormComparison hA b e).2.2.2.1 x

private def normOneSubgroup (hA : isCentralSimple F (Matrix (Fin m) (Fin m) B)) :
    Subgroup (Matrix (Fin m) (Fin m) B)ˣ where
  carrier := normOne hA
  one_mem' := RM03.CSA.reducedNorm_one hA
  mul_mem' := by
    intro x y hx hy
    change reducedNorm hA (x : Matrix (Fin m) (Fin m) B) = 1 at hx
    change reducedNorm hA (y : Matrix (Fin m) (Fin m) B) = 1 at hy
    change reducedNorm hA ((x : Matrix (Fin m) (Fin m) B) * y) = 1
    change RM03.CSA.reducedNorm hA _ = 1
    exact (RM03.CSA.reducedNorm_mul hA _ _).trans (by rw [show RM03.CSA.reducedNorm hA _ = 1 from hx,
      show RM03.CSA.reducedNorm hA _ = 1 from hy, one_mul])
  inv_mem' := by
    intro x hx
    change reducedNorm hA (x : Matrix (Fin m) (Fin m) B) = 1 at hx
    have h := RM03.CSA.reducedNorm_mul hA (↑x : Matrix (Fin m) (Fin m) B) (↑x⁻¹)
    change RM03.CSA.reducedNorm hA (x : Matrix (Fin m) (Fin m) B) = 1 at hx
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, RM03.CSA.reducedNorm_one,
      hx, one_mul] at h
    exact h.symm

private def ofNormOne {H : AffineAlgebraicGroup F} (P : NormOnePoints hA b H) :
    normOneSubgroup hA →* GroupPoints H.val (ground F) where
  toFun x := (P.point (ground F)).symm
    ⟨1 ⊗ₜ[F] (x.val : Matrix (Fin m) (Fin m) B), (normAt_ground _).trans x.prop⟩
  map_one' := by
    apply (P.point (ground F)).injective
    apply Subtype.ext
    rw [Equiv.apply_symm_apply, P.one]
    rfl
  map_mul' x y := by
    apply (P.point (ground F)).injective
    apply Subtype.ext
    rw [Equiv.apply_symm_apply, P.mul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl

private theorem ofNormOne_coordinates {H : AffineAlgebraicGroup F} (P : NormOnePoints hA b H)
    (x : normOneSubgroup hA) :
    (P.point (ground F) (ofNormOne P x)).val =
      1 ⊗ₜ[F] (x.val : Matrix (Fin m) (Fin m) B) :=
  congrArg Subtype.val ((P.point (ground F)).apply_symm_apply _)

private theorem ofNormOne_surjective {H : AffineAlgebraicGroup F} (P : NormOnePoints hA b H) :
    Function.Surjective (ofNormOne P) := by
  intro g
  obtain ⟨x, hx⟩ := (Algebra.TensorProduct.lid F (Matrix (Fin m) (Fin m) B)).symm.surjective
    (P.point (ground F) g).val
  change 1 ⊗ₜ[F] x = _ at hx
  have hn : reducedNorm hA x = 1 := by
    rw [← normAt_ground (b := b), hx]
    exact (P.point (ground F) g).prop
  obtain ⟨v, rfl⟩ := (RM03.CSA.reducedNorm_ne_zero_iff_isUnit hA x).mp (by have he : RM03.CSA.reducedNorm hA x = 1 := hn; rw [he]; exact one_ne_zero)
  refine ⟨⟨v, hn⟩, ?_⟩
  apply (P.point (ground F)).injective
  exact Subtype.ext ((ofNormOne_coordinates P ⟨v, hn⟩).trans hx)

private theorem compareNormModels {A H : AffineAlgebraicGroup F}
    (P : NormOnePoints hA b A) (Q : NormOnePoints hA b H) :
    ∃ f : A.val ⟶ H.val, ∀ (R : TestAlgebra F) (x : GroupPoints A.val R),
      Q.point R (onPoints f R x) = P.point R x := by
  let e (R : TestAlgebra F) := (P.point R).trans (Q.point R).symm
  have he (R : TestAlgebra F) (x : GroupPoints A.val R) : Q.point R (e R x) = P.point R x :=
    (Q.point R).apply_symm_apply _
  let n : (groupPointsFunctor F).obj A.val ⟶ (groupPointsFunctor F).obj H.val :=
    { app := fun R => GrpCat.ofHom
        { toFun := e R
          map_one' := by
            apply (Q.point R).injective
            exact Subtype.ext (by rw [he, P.one, Q.one])
          map_mul' := fun x y => by
            apply (Q.point R).injective
            apply Subtype.ext
            rw [he, P.mul, Q.mul, he, he] }
      naturality := by
        intro R T f
        apply GrpCat.ext
        intro x
        change e T (mapPoints f x) = mapPoints f (e R x)
        apply (Q.point T).injective
        apply Subtype.ext
        rw [he, Q.natural, P.natural, he] }
  obtain ⟨f, hf⟩ := (groupHomComparison F A.val H.val A.property.1).2 n
  exact ⟨f, fun R x => by
    change (groupPointsFunctor F).map f = n at hf
    change Q.point R (((groupPointsFunctor F).map f).app R x) = _
    rw [hf]
    exact he R x⟩

omit [Fintype I] in
private theorem continuous_polynomialEvaluation [TopologicalSpace F] [IsTopologicalRing F]
    {P : Type*} [TopologicalSpace P] (x : P → I → F)
    (hx : ∀ i, Continuous fun z => x z i) (p : MvPolynomial I F) :
    Continuous fun z => MvPolynomial.aeval (x z) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa only [MvPolynomial.aeval_C] using continuous_const (y := algebraMap F F a)
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul (hx i)

private theorem continuous_normComparison [TopologicalSpace F] [IsTopologicalRing F]
    (h : HopfOperations F (NormOneCoordinates hA b))
    (P : NormOnePoints hA b (@spectrum F _ _ _ h.hopf inferInstance))
    (heval : ∀ (R : TestAlgebra F) (a : NormOneCoordinates hA b →ₐ[F] R)
      (g : GroupPoints (@spectrum F _ _ _ h.hopf inferInstance).val R),
      (show Points _ R from g).left = Spec.map (CommRingCat.ofHom a.toRingHom) →
      ∀ i, (b.baseChange R).repr (P.point R g).val i =
        a (Ideal.Quotient.mk (normOneIdeal hA b) (MvPolynomial.X i)))
    {G : AffineAlgebraicGroup F} (f : (@spectrum F _ _ _ h.hopf inferInstance).val ⟶ G.val) :
    letI := coordinateTopology b
    letI := localPointTopology G
    Continuous (fun x : normOneSubgroup hA =>
      (rationalEquiv G.val).symm (onPoints f (ground F) (ofNormOne P x))) := by
  letI := coordinateTopology b
  letI := localPointTopology G
  let A := NormOneCoordinates hA b
  let C := groupCoordinates G
  let H := @spectrum F _ A _ h.hopf inferInstance
  let FF := (algSpec.fullyFaithful (R := CommRingCat.of F))
  let q := FF.preimage (f.hom.hom ≫ (coordinateHopfIso G).inv.hom.hom)
  let g (x : normOneSubgroup hA) : GroupPoints H.val (ground F) := ofNormOne P x
  let a (x : normOneSubgroup hA) := (FF.preimage (g x)).unop.hom
  have ha (x : normOneSubgroup hA) :
      (testSpec F).map (CommAlgCat.ofHom (a x)).op = g x :=
    FF.map_preimage _
  have hq : (testSpec F).map q = f.hom.hom ≫ (coordinateHopfIso G).inv.hom.hom :=
    FF.map_preimage _
  have hcoeff (x : normOneSubgroup hA) (i : I) :
      a x (Ideal.Quotient.mk (normOneIdeal hA b) (MvPolynomial.X i)) =
        b.repr (x.val : Matrix (Fin m) (Fin m) B) i := by
    have hx := heval (ground F) (a x) (g x)
      (congrArg (fun z => z.left) (ha x)).symm i
    rw [ofNormOne_coordinates] at hx
    simp only [Module.Basis.baseChange_repr_tmul, smul_eq_mul, mul_one] at hx
    exact hx.symm
  have hpoly (x : normOneSubgroup hA) :
      (a x).comp (Ideal.Quotient.mkₐ F (normOneIdeal hA b)) =
        MvPolynomial.aeval (fun i => b.repr (x.val : Matrix (Fin m) (Fin m) B) i) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [MvPolynomial.aeval_X]
    exact hcoeff x i
  have he (x : normOneSubgroup hA) :
      (coordinatePointEquiv G (ground F)).symm (onPoints f (ground F) (g x)) =
        toConv ((a x).comp q.unop.hom) := by
    apply (coordinatePointEquiv G (ground F)).injective
    rw [MulEquiv.apply_symm_apply]
    change g x ≫ f.hom.hom = (testSpec F).map
      (CommAlgCat.ofHom ((a x).comp q.unop.hom)).op ≫ (coordinateHopfIso G).hom.hom.hom
    have hcomp : (CommAlgCat.ofHom ((a x).comp q.unop.hom)).op =
        (CommAlgCat.ofHom (a x)).op ≫ q := by
      apply Quiver.Hom.unop_inj
      apply CommAlgCat.hom_ext
      rfl
    rw [hcomp, Functor.map_comp, ha, hq, Category.assoc, Category.assoc,
      ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  apply (continuous_localPoints_iff G _).mpr
  intro v
  obtain ⟨p, hp⟩ := Ideal.Quotient.mkₐ_surjective F (normOneIdeal hA b) (q.unop.hom v)
  have heval' (x : normOneSubgroup hA) :
      rationalCoordinates G ((rationalEquiv G.val).symm (onPoints f (ground F) (g x))) v =
        MvPolynomial.aeval (fun i => b.repr (x.val : Matrix (Fin m) (Fin m) B) i) p := by
    change ((coordinatePointEquiv G (ground F)).symm
      (rationalEquiv G.val ((rationalEquiv G.val).symm (onPoints f (ground F) (g x))))).ofConv v = _
    rw [MulEquiv.apply_symm_apply, he]
    change a x (q.unop.hom v) = _
    rw [← hp, ← hpoly]
    rfl
  have hcont : Continuous fun x : normOneSubgroup hA =>
      MvPolynomial.aeval (fun i => b.repr (x.val : Matrix (Fin m) (Fin m) B) i) p := by
    apply continuous_polynomialEvaluation
    intro i
    let E := Matrix (Fin m) (Fin m) B
    have hc : Continuous (fun y : E => (b.repr y i : F)) :=
      (continuous_apply i).comp (continuous_induced_dom (f := fun y : E => fun j : I => b.repr y j))
    exact hc.comp (Units.continuous_val.comp continuous_subtype_val)
  convert hcont using 1
  exact funext heval'

private theorem elementary_mem_generated [Infinite F] {A G : AffineAlgebraicGroup F}
    (P : NormOnePoints hA b A) {S : ClosedSubgroup A.val} (D : ScalarDiagonalModel P S)
    (hD : RelativeBlockDescription D)
    (hB : isCentralSimple F B) (hG : IsReductive G) (f : A.val ⟶ G.val) (x : normOneSubgroup hA)
    (hx : x.val ∈ elementaryGroup (B := B) (Fin m)) :
    (rationalEquiv G.val).symm (onPoints f (ground F) (ofNormOne P x)) ∈ unipotentGenerated G := by
  rcases hD with ⟨α, hα, hchar, hroots, hchoose, hcomponent, hlim⟩
  let e : normOneSubgroup hA →* RationalPoints G.val :=
    (rationalEquiv G.val).symm.toMonoidHom.comp ((onPoints f (ground F)).comp (ofNormOne P))
  have he : elementaryGroup (B := B) (Fin m) ≤
      ((unipotentGenerated G).comap e).map (normOneSubgroup hA).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, j, hij, a, rfl⟩
    have hn : (elementary i j hij a) ∈ normOne hA := by
      have h := (InnerTypeARelativeContraction.blockTransvections (R := F)
        hB hA b i j hij).2.1
        ((1 : F) ⊗ₜ[F] a)
      change reducedNorm hA (1 + Matrix.single i j a) = 1
      rw [← normAt_ground (b := b), TensorProduct.tmul_add, ← Algebra.TensorProduct.one_def]
      simpa [blockEntry, TensorProduct.map_tmul] using h
    let z : normOneSubgroup hA := ⟨elementary i j hij a, hn⟩
    refine ⟨z, ?_, rfl⟩
    show e z ∈ unipotentGenerated G
    obtain ⟨c, hc⟩ := hchoose i j hij
    have hpos : 0 < CharacterPairing.pairing S.group (α i j) c := by rw [hc]; decide
    apply mem_generated_of_limit hG f (c ≫ S.inclusion)
    apply ((hlim i j hij c hpos (ground F) (ofNormOne P z)).1.mpr ?_).2
    let a₀ : F ⊗[F] B := 1 ⊗ₜ[F] a
    have ha : (P.point (ground F) (ofNormOne P z)).val = 1 + blockEntry i j a₀ := by
      rw [ofNormOne_coordinates]
      change (1 : F) ⊗ₜ[F] (1 + Matrix.single i j a) = _
      rw [TensorProduct.tmul_add, ← Algebra.TensorProduct.one_def]
      simp [a₀, blockEntry, TensorProduct.map_tmul]
    refine ⟨a₀, ha, fun y hy => ?_⟩
    have hj := (InnerTypeARelativeContraction.blockTransvections (R := F)
      hB hA b i j hij).1
    exact hj (hy.symm.trans ha)
  obtain ⟨y, hy, hyx⟩ := he hx
  have hyx' : y = x := Subtype.ext hyx
  exact hyx' ▸ hy


private theorem reindex_coordinateTopology [TopologicalSpace F] {J : Type*} [Finite J]
    (e : I ≃ J) :
    coordinateTopology (b.reindex e) = coordinateTopology b := by
  let M := Matrix (Fin m) (Fin m) B
  let f : M → I → F := fun x i => b.repr x i
  let g : M → J → F := fun x j => (b.reindex e).repr x j
  change TopologicalSpace.induced g _ = TopologicalSpace.induced f _
  apply le_antisymm
  · letI : TopologicalSpace M := TopologicalSpace.induced g inferInstance
    apply continuous_iff_le_induced.mp (show Continuous f from ?_)
    apply continuous_pi_iff.mpr
    intro i
    have hc := (continuous_apply (e i)).comp (continuous_induced_dom (f := g))
    simpa only [f, g, Function.comp_def, Module.Basis.repr_reindex_apply,
      Equiv.symm_apply_apply] using hc
  · letI : TopologicalSpace M := TopologicalSpace.induced f inferInstance
    apply continuous_iff_le_induced.mp (show Continuous g from ?_)
    apply continuous_pi_iff.mpr
    intro j
    have hc := (continuous_apply (e.symm j)).comp (continuous_induced_dom (f := f))
    simpa only [f, g, Function.comp_def, Module.Basis.repr_reindex_apply] using hc

private theorem normModelGeneration [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Infinite F]
    {H G : AffineAlgebraicGroup F} (hG : IsReductive G) (f : H.val ⟶ G.val)
    (P : NormOnePoints hA b H) (hB : isCentralSimple F B) (hm : 2 ≤ m) :
    letI := localPointTopology G
    let image (x : normOneSubgroup hA) :=
      (rationalEquiv G.val).symm (onPoints f (ground F) (ofNormOne P x))
    (∀ x : normOneSubgroup hA, x.val ∈ elementaryGroup (B := B) (Fin m) →
      image x ∈ unipotentGenerated G) ∧
    (∀ y : RationalPoints H.val, onRational f y ∈
      closure (unipotentGenerated G : Set (RationalPoints G.val))) := by
  classical
  cases m with
  | zero => omega
  | succ n =>
    letI := localPointTopology G
    obtain ⟨h, Q, S, heval, _, _, ⟨D, hD⟩, _⟩ :=
      InnerTypeASplitRank.splitRank n (show isCentralDivision F B from ⟨hB.2.1, hB.2.2⟩) hA b
    let A := @spectrum F _ (NormOneCoordinates hA b) _ h.hopf inferInstance
    obtain ⟨e, he⟩ := compareNormModels (A := A) Q P
    let f₀ := e ≫ f
    let image (x : normOneSubgroup hA) :=
      (rationalEquiv G.val).symm (onPoints f₀ (ground F) (ofNormOne Q x))
    have himage (x : normOneSubgroup hA) :
        image x = (rationalEquiv G.val).symm (onPoints f (ground F) (ofNormOne P x)) := by
      have hxe : onPoints e (ground F) (ofNormOne Q x) = ofNormOne P x := by
        apply (P.point (ground F)).injective
        apply Subtype.ext
        rw [he, ofNormOne_coordinates, ofNormOne_coordinates]
      have hcomp : onPoints f₀ (ground F) (ofNormOne Q x) =
          onPoints f (ground F) (onPoints e (ground F) (ofNormOne Q x)) :=
        (Category.assoc (show Points A.val.X (ground F) from ofNormOne Q x)
          e.hom.hom f.hom.hom).symm
      exact congrArg (rationalEquiv G.val).symm (hcomp.trans (congrArg (onPoints f _) hxe))
    have hgen (x : normOneSubgroup hA) (hx : x.val ∈ elementaryGroup (B := B) (Fin (n + 1))) :
        image x ∈ unipotentGenerated G :=
      elementary_mem_generated Q D hD hB hG f₀ x hx
    refine ⟨?_, ?_⟩
    · intro x hx
      change (rationalEquiv G.val).symm (onPoints f (ground F) (ofNormOne P x)) ∈
        unipotentGenerated G
      rw [← himage]
      exact hgen x hx
    · intro y
      obtain ⟨x, hx⟩ := ofNormOne_surjective P (rationalEquiv H.val y)
      have hy : image x = onRational f y := by
        rw [himage, hx]
        exact rationalEquiv_post f y
      rw [← hy]
      let r : I ≃ Fin (Module.finrank F (Matrix (Fin (n + 1)) (Fin (n + 1)) B)) :=
        Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
      let b' := b.reindex r
      letI := coordinateTopology b'
      have htop : coordinateTopology b' = coordinateTopology b := reindex_coordinateTopology r
      have hdense := InnerTypeALocalGeneration.localBlockGeneration.1 hB (n + 1) hm
      have hcont : Continuous image := by
        have hc := continuous_normComparison h Q heval f₀
        rw [← htop] at hc
        exact hc
      let E : Set (normOneSubgroup hA) := {z | z.val ∈ elementaryGroup (B := B) (Fin (n + 1))}
      have hxE : x ∈ closure E := by
        apply closure_subtype.mpr
        have hsubset :
            (elementaryGroup (B := B) (Fin (n + 1)) : Set _) ⊆ Subtype.val '' E := by
          intro z hz
          exact ⟨⟨z, hdense.1 hz⟩, hz, rfl⟩
        exact closure_mono hsubset (hdense.2 b' x.prop)
      exact map_mem_closure hcont hxE (fun x hx => hgen x hx)

end MatrixModel

open LinearAlgebraicGroups.Specs.GeneralLinearStructure (SpecialMatrixPoints)

open private normOneMatrixModel splitMatrixCoordinates_tmul
  normAt_eq_splitDet reindexedSplitMatrixCoordinates reindexedSplitMatrixCoordinates_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.InnerTypeARelativeContraction

private theorem splitSL2_mem_generated [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Infinite F] {H G : AffineAlgebraicGroup F}
    (hG : IsReductive G) (f : H.val ⟶ G.val) (J : SpecialMatrixPoints H 2)
    (y : RationalPoints H.val) : onRational f y ∈ unipotentGenerated G := by
  classical
  let M := Matrix (Fin 2) (Fin 2) F
  have hF : isCentralSimple F F := ⟨inferInstance, inferInstance, inferInstance⟩
  have hM : isCentralSimple F M :=
    InnerTypeALocalGeneration.Spec.matrixCentralSimple hF (by decide : 0 < 2)
  let b := Module.Free.chooseBasis F M
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex F M)
  let r : Index.{u} 2 ≃ Fin 2 := Equiv.ulift
  let E := reindexedSplitMatrixCoordinates (k := F) r
  have hnorm (R : TestAlgebra F) (x : R ⊗[F] M) :
      normAt hM b x = (E R x).det := by
    exact (normAt_eq_splitDet (R := R) hM b x).trans
      (Matrix.det_reindexAlgEquiv R R r.symm _).symm
  obtain ⟨P, _⟩ := normOneMatrixModel J E hnorm (reindexedSplitMatrixCoordinates_natural r)
  obtain ⟨x, hx⟩ := ofNormOne_surjective P (rationalEquiv H.val y)
  have hn : reducedNorm hM (x.val : M) = 1 := x.prop
  have hd : Matrix.det (x.val : M) = 1 := by
    have hh := normAt_eq_splitDet (R := ground F) hM b ((1 : F) ⊗ₜ[F] (x.val : M))
    rw [splitMatrixCoordinates_tmul] at hh
    change normAt hM b ((1 : F) ⊗ₜ[F] (x.val : M)) =
      (1 • (x.val : M).map (algebraMap F F)).det at hh
    have hbase : (x.val : M).map (algebraMap F F) = (x.val : M) := by
      ext i j
      exact Algebra.algebraMap_self_apply _
    rw [one_smul, hbase, normAt_ground, hn] at hh
    exact hh.symm
  have hxE : x.val ∈ elementaryGroup (B := F) (Fin 2) := by
    change x.val ∈ (elementaryGroup (B := F) (Fin 2) : Set _)
    rw [InnerTypeALocalGeneration.splitElementaryGeneration (F := F) 2 le_rfl]
    exact hd
  have hy := (normModelGeneration hG f P hF le_rfl).1 x hxE
  change (rationalEquiv G.val).symm (onPoints f (ground F) (ofNormOne P x)) ∈
    unipotentGenerated G at hy
  rw [hx, rationalEquiv_post] at hy
  exact hy

private theorem onRational_comp {A B C : GroupScheme F}
    (f : A ⟶ B) (g : B ⟶ C) (x : RationalPoints A) :
    onRational (f ≫ g) x = onRational g (onRational f x) :=
  (Category.assoc x f.hom.hom g.hom.hom).symm

@[simp]
private theorem onRational_id {A : GroupScheme F} (x : RationalPoints A) :
    onRational (𝟙 A) x = x := Category.comp_id x

@[simp]
private theorem onRational_zero {A B : GroupScheme F} (x : RationalPoints A) :
    onRational (0 : A ⟶ B) x = 1 := by
  change (x ≫ toUnit _) ≫ η[B.X] = 1
  rw [show x ≫ toUnit _ = 𝟙 _ from Subsingleton.elim _ _]
  exact Category.id_comp _

private theorem mem_of_product {A B H G : GroupScheme F}
    (e : H ≅ Limits.prod A B) (f : H ⟶ G) (C : Subgroup (RationalPoints G))
    (hA : ∀ x, onRational (Limits.prod.inl A B ≫ e.inv ≫ f) x ∈ C)
    (hB : ∀ x, onRational (Limits.prod.inr A B ≫ e.inv ≫ f) x ∈ C)
    (x : RationalPoints H) : onRational f x ∈ C := by
  let z := onRational e.hom x
  let a := onRational Limits.prod.fst z
  let b := onRational Limits.prod.snd z
  have he : onRational (Limits.prod.inl A B) a * onRational (Limits.prod.inr A B) b = z := by
    let U := Grp.forget (SchemeOver F)
    apply (isLimitOfPreserves U (prodIsProd A B)).hom_ext
    rintro (_ | _)
    · change onRational Limits.prod.fst (_ * _) = a
      rw [map_mul, ← onRational_comp (Limits.prod.inl A B),
        ← onRational_comp (Limits.prod.inr A B), prod.inl_fst, prod.inr_fst,
        onRational_id, onRational_zero, mul_one]
    · change onRational Limits.prod.snd (_ * _) = b
      rw [map_mul, ← onRational_comp (Limits.prod.inl A B),
        ← onRational_comp (Limits.prod.inr A B), prod.inl_snd, prod.inr_snd,
        onRational_zero, onRational_id, one_mul]
  have hx : onRational (e.inv ≫ f) z = onRational f x := by
    rw [show z = onRational e.hom x from rfl, ← onRational_comp, Iso.hom_inv_id_assoc]
  rw [← hx, ← he, map_mul, ← onRational_comp, ← onRational_comp]
  exact C.mul_mem (hA a) (hB b)

private theorem divisionMatrix_mem_closure [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Infinite F] {H G : AffineAlgebraicGroup F}
    {m d : ℕ} (hG : IsReductive G) (f : H.val ⟶ G.val)
    (hH : IsDivisionMatrixGroup H m d) (hm : 2 ≤ m) :
    letI := localPointTopology G
    ∀ y : RationalPoints H.val, onRational f y ∈
      closure (unipotentGenerated G : Set (RationalPoints G.val)) := by
  obtain ⟨B, _, _, hB, _, hM, b, ⟨P⟩⟩ := hH
  exact (normModelGeneration hG f P hB hm).2

theorem leviRadicalGeneration : LeviRadicalGeneration.{u} := by
  intro F _ _ _ _ G hG _ c D H q s A _ hker _ hsection hs hmodel
  letI : Infinite ℤᵐ⁰ := Infinite.of_injective WithZero.exp WithZero.exp_injective
  letI : Infinite F := Infinite.of_surjective _
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).surjective.comp
      (ValuativeRel.valuation_surjective (K := F)))
  letI := localPointTopology G
  letI := localPointGroup G
  let C := (unipotentGenerated G).topologicalClosure
  have hred := reductive_of_semisimple G hG.1
  have hgen : unipotentGenerated G ≤ C := Subgroup.le_topologicalClosure _
  have hH : ∀ x, onRational (H.inclusion ≫ D.centralizer.inclusion) x ∈ C := by
    rcases hmodel with h₂ | ⟨H₁, H₂, ⟨J⟩, h₃, ⟨e⟩⟩
    · exact divisionMatrix_mem_closure hred _ h₂ (by decide)
    · apply mem_of_product e _ C
      · intro x
        exact hgen (splitSL2_mem_generated hred _ J x)
      · exact divisionMatrix_mem_closure hred _ h₃ (by decide)
  have hs' : ∀ t, onRational (s ≫ D.centralizer.inclusion) t ∈ C := by
    intro t
    rw [hs, onRational_comp]
    exact hgen (splitSL2_mem_generated hred _ A.matrix (onRational A.diagonal t))
  have hZ : SubgroupSections D.centralizer (𝟙_ (SchemeOver F)) ≤ C := by
    rintro _ ⟨x, rfl⟩
    exact quotient_section_mem D.centralizer.inclusion q s H hker hsection C hH hs' x
  obtain ⟨E⟩ := CocharacterDynamics.existsLimitDecomposition G (oppositeCocharacter c)
  have hle := sup_le ((RelativeRayGeneration.twoRadicals_le_unipotentGenerated hred D E).trans hgen) hZ
  rw [RelativeRayGeneration.twoRadicals_sup_centralizer hred D E] at hle
  exact fun x => hle (show x ∈ (⊤ : Subgroup (RationalPoints G.val)) from trivial)

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalLeviRadicalGeneration
