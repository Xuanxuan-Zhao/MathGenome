import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.SquareZeroMaps
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison
import Batteries.Tactic.OpenPrivate

open CategoryTheory CochainComplex.HomComplex

universe u v

namespace DerivedFormalization.Affine.SquareZeroMaps

open Specs.DerivedFormalization.Affine.SquareZeroMaps
open Specs.DerivedFormalization.Affine.CotangentComplex (Model)
open Specs.DerivedFormalization.Affine.Tensor
  (ModuleTensor act act_assoc_at regular restrict term signedLeft signedLeft_apply
    signedLeft_assoc signedLeft_d signedLeft_right)
open Specs.DerivedFormalization.Affine.PolynomialPath (ModulePathModel)
open Specs.DerivedFormalization.DG.HomComplex (component ofStrict)
open Kahler (IsDerivation value)
open RightDGModule (strictCycle strictMap strictCycle_strictMap)

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {A B : NonpositiveCDGA.{u,v} k} {b : A ⟶ B}

private theorem algebraHom_ext {C E : CommDGAlgebra.{u,v} k} {f g : C ⟶ E}
    (e : ∀ i (x : C.complex.X i), f.chainMap.f i x = g.chainMap.f i x) : f = g := by
  apply CommDGAlgebra.Hom.ext_chainMap
  apply HomologicalComplex.hom_ext
  intro i
  exact ModuleCat.hom_ext (LinearMap.ext (e i))

section Product

variable (M : B.Module)

private abbrev productDegree (i : ℤ) := ModuleCat.of k (B.complex.X i × term M i)

@[reducible] private def productComplex : ModuleCochain.{u,v} k where
  X := productDegree M
  d i j := ModuleCat.ofHom (LinearMap.prodMap (B.complex.d i j).hom ((M.complex ()).d i j).hom)
  shape i j h := by
    rw [B.complex.shape i j h, (M.complex ()).shape i j h]
    exact ModuleCat.hom_ext rfl
  d_comp_d' i j l _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x, m⟩
    exact Prod.ext (CategoryTheory.congr_fun (B.complex.d_comp_d i j l) x)
      (CategoryTheory.congr_fun ((M.complex ()).d_comp_d i j l) m)

private def productMul (i j n : ℤ) (h : i+j=n) :
    productDegree M i →ₗ[k] productDegree M j →ₗ[k] productDegree M n :=
  (((B.mul i j n h).comp (LinearMap.fst k _ _)).compl₂
    (LinearMap.fst k _ _)).compr₂ (LinearMap.inl k _ _) +
  ((((act M i j n h).comp (LinearMap.snd k _ _)).compl₂ (LinearMap.fst k _ _)) +
    (((signedLeft M i j n h).comp (LinearMap.fst k _ _)).compl₂
      (LinearMap.snd k _ _))).compr₂ (LinearMap.inr k _ _)

private theorem productMul_apply (i j n : ℤ) (h : i+j=n)
    (x : productDegree M i) (y : productDegree M j) :
    productMul M i j n h x y =
      (B.mul i j n h x.1 y.1, act M i j n h x.2 y.1 + signedLeft M i j n h x.1 y.2) :=
  Prod.ext (add_zero _) (zero_add _)

private theorem left_unit (i : ℤ) (m : term M i) :
    signedLeft M 0 i i (zero_add i) B.one m = m := by
  rw [signedLeft_apply, zero_mul, Int.negOnePow_zero, one_smul, M.act_id]

private theorem productMul_assoc (i j l : ℤ) (x : productDegree M i)
    (y : productDegree M j) (z : productDegree M l) :
    productMul M (i+j) l (i+j+l) rfl (productMul M i j (i+j) rfl x y) z =
      productMul M i (j+l) (i+j+l) (add_assoc i j l).symm x (productMul M j l (j+l) rfl y z) := by
  rw [productMul_apply M i j (i+j) rfl, productMul_apply M j l (j+l) rfl,
    productMul_apply M (i+j) l (i+j+l) rfl, productMul_apply M i (j+l) (i+j+l) (by omega)]
  apply Prod.ext
  · exact B.toDGAlgebra.assoc (a := ()) (b := ()) (c := ()) (e := ()) i j l x.1 y.1 z.1
  · rw [LinearMap.map_add₂, map_add]
    rw [act_assoc_at M i j l (i+j) (j+l) (i+j+l) rfl rfl rfl,
      ← signedLeft_right M i j l (i+j) (j+l) (i+j+l) rfl rfl rfl,
      signedLeft_assoc M i j l (i+j+l) rfl]
    abel_nf

private theorem productMul_leibniz (i j n : ℤ) (h : i+j=n)
    (x : productDegree M i) (y : productDegree M j) :
    (productComplex M).d n (n+1) (productMul M i j n h x y) =
      productMul M (i+1) j (n+1) (by omega) ((productComplex M).d i (i+1) x) y +
        i.negOnePow • productMul M i (j+1) (n+1) (by omega) x ((productComplex M).d j (j+1) y) := by
  rw [productMul_apply M i j n h, productMul_apply M (i+1) j (n+1) (by omega),
    productMul_apply M i (j+1) (n+1) (by omega)]
  apply Prod.ext
  · exact B.toDGAlgebra.leibniz (a := ()) (b := ()) (c := ()) i j n h x.1 y.1
  · change (M.complex ()).d n (n+1)
        (act M i j n h x.2 y.1 + signedLeft M i j n h x.1 y.2) =
      (act M (i+1) j (n+1) (by omega) ((M.complex ()).d i (i+1) x.2) y.1 +
        signedLeft M (i+1) j (n+1) (by omega) (B.complex.d i (i+1) x.1) y.2) +
      i.negOnePow • (act M i (j+1) (n+1) (by omega) x.2 (B.complex.d j (j+1) y.1) +
        signedLeft M i (j+1) (n+1) (by omega) x.1 ((M.complex ()).d j (j+1) y.2))
    rw [map_add, M.leibniz (a := ()) (b := ()), signedLeft_d]
    rw [smul_add]
    abel

private theorem productMul_comm (i j n : ℤ) (h : i+j=n)
    (x : productDegree M i) (y : productDegree M j) :
    productMul M i j n h x y = (i*j).negOnePow • productMul M j i n (by omega) y x := by
  rw [productMul_apply M i j n h, productMul_apply M j i n (by omega)]
  apply Prod.ext
  · exact B.toCommDGAlgebra.graded_comm i j n h x.1 y.1
  · change act M i j n h x.2 y.1 + signedLeft M i j n h x.1 y.2 =
      (i*j).negOnePow • (act M j i n (by omega) y.2 x.1 +
        signedLeft M j i n (by omega) y.1 x.2)
    rw [signedLeft_apply, signedLeft_apply, mul_comm j i, smul_add, smul_smul]
    simp only [← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul, one_smul]
    exact add_comm _ _

@[reducible] private def productAlgebra : CommDGAlgebra.{u,v} k where
  toDGAlgebra :=
    { hom := fun _ _ => productComplex M
      comp := productMul M
      id := fun _ => (B.one, 0)
      d_id := fun _ => Prod.ext (B.toDGAlgebra.d_id ())
        (show (M.complex ()).d 0 1 0 = 0 from map_zero _)
      id_comp := fun i x => by
        rw [productMul_apply]
        exact Prod.ext (B.toDGAlgebra.id_comp (a := ()) (b := ()) i x.1)
          (by change act M 0 i i _ 0 x.1 + signedLeft M 0 i i _ B.one x.2 = x.2
              rw [map_zero, LinearMap.zero_apply, zero_add]
              exact left_unit M i x.2)
      comp_id := fun i x => by
        rw [productMul_apply]
        exact Prod.ext (B.toDGAlgebra.comp_id (a := ()) (b := ()) i x.1)
          (by change act M i 0 i _ x.2 B.one + signedLeft M i 0 i _ x.1 0 = x.2
              rw [map_zero, add_zero]
              exact M.act_id () i x.2)
      assoc := productMul_assoc M
      leibniz := productMul_leibniz M }
  graded_comm := productMul_comm M

private def productProjection : productAlgebra M ⟶ B.toCommDGAlgebra where
  chainMap := ⟨fun _ => ModuleCat.ofHom (LinearMap.fst k _ _), fun _ _ _ => rfl⟩
  map_one := rfl
  map_mul i j n h x y := congrArg Prod.fst (productMul_apply M i j n h x y)

private def productSection : B.toCommDGAlgebra ⟶ productAlgebra M where
  chainMap := Tensor.chainOfDegrees (fun _ => LinearMap.inl k _ _)
    (fun i x => Prod.ext rfl
      (show (M.complex ()).d i (i+1) 0 = 0 from map_zero _))
  map_one := rfl
  map_mul i j n h x y := by
    change (_, 0) = productMul M i j n h (x, 0) (y, 0)
    rw [productMul_apply]
    simp

private def squareZeroExtension : Extension M where
  algebra := productAlgebra M
  coord _ := LinearEquiv.refl _ _
  projection := productProjection M
  zeroSection := productSection M
  section_projection := algebraHom_ext (fun _ _ => rfl)
  projection_coord _ _ := rfl
  section_coord _ _ := rfl
  unit_coord := rfl
  differential _ _ _ := rfl
  multiplication i j n h x y := productMul_apply M i j n h x y

end Product

private theorem extensionConstructionProof : ExtensionConstruction.{u,v} := by
  intro k _ _ B
  refine ⟨squareZeroExtension, fun M h i hi => ⟨fun x y => ?_⟩⟩
  exact Prod.ext ((B.nonpositive i hi).elim x.1 y.1) ((h i hi).elim x.2 y.2)

section Coordinates

variable {C : CommDGAlgebra.{u,v} k} {M N : B.Module}

private theorem hom_apply_eq {D E : CommDGAlgebra.{u,v} k} {f g : D ⟶ E}
    (h : f = g) (i : ℤ) (x : D.complex.X i) :
    f.chainMap.f i x = g.chainMap.f i x := by
  subst g
  rfl

private def coefficientProjection (S : Extension M) : S.algebra.complex ⟶ M.complex () :=
  Tensor.chainOfDegrees (fun i => (LinearMap.snd k _ _).comp (S.coord i).toLinearMap)
    (fun i x => (congrArg Prod.snd (S.differential i (i+1) x)).symm)

private def algebraFromComponents (S : Extension M)
    (p : C ⟶ B.toCommDGAlgebra) (d : C.complex ⟶ M.complex ())
    (hu : d.f 0 C.one = 0)
    (hm : ∀ (i j n : ℤ) (h : i+j=n) (x : C.complex.X i) (y : C.complex.X j),
      d.f n (C.mul i j n h x y) =
        act M i j n h (d.f i x) (p.chainMap.f j y) +
          (i*j).negOnePow • act M j i n (by omega) (d.f j y) (p.chainMap.f i x)) :
    C ⟶ S.algebra where
  chainMap := Tensor.chainOfDegrees
    (fun i => (S.coord i).symm.toLinearMap.comp ((p.chainMap.f i).hom.prod (d.f i).hom)) (by
      intro i x
      apply (S.coord (i+1)).injective
      rw [S.differential]
      change (B.complex.d i (i+1) ((S.coord i) ((S.coord i).symm _)).1,
        (M.complex ()).d i (i+1) ((S.coord i) ((S.coord i).symm _)).2) =
          (S.coord (i+1)) ((S.coord (i+1)).symm _)
      simp only [LinearEquiv.apply_symm_apply]
      exact Prod.ext
        (CategoryTheory.congr_fun (p.chainMap.comm i (i+1)) x)
        (CategoryTheory.congr_fun (d.comm i (i+1)) x))
  map_one := by
    apply (S.coord 0).injective
    change (S.coord 0) ((S.coord 0).symm _) = _
    rw [LinearEquiv.apply_symm_apply, S.unit_coord]
    exact Prod.ext p.map_one hu
  map_mul i j n h x y := by
    apply (S.coord n).injective
    rw [S.multiplication]
    have coord (l : ℤ) (z : C.complex.X l) :
        S.coord l ((S.coord l).symm ((p.chainMap.f l).hom.prod (d.f l).hom z)) =
          (p.chainMap.f l z, d.f l z) := (S.coord l).apply_symm_apply _
    change S.coord n ((S.coord n).symm _) =
      (B.mul i j n h (S.coord i ((S.coord i).symm _)).1
        (S.coord j ((S.coord j).symm _)).1,
        act M i j n h (S.coord i ((S.coord i).symm _)).2
          (S.coord j ((S.coord j).symm _)).1 +
          (i*j).negOnePow • act M j i n (by omega)
            (S.coord j ((S.coord j).symm _)).2 (S.coord i ((S.coord i).symm _)).1)
    rw [coord n, coord i, coord j]
    exact Prod.ext (p.map_mul i j n h x y) (hm i j n h x y)

private theorem algebraFromComponents_coord (S : Extension M)
    (p : C ⟶ B.toCommDGAlgebra) (d : C.complex ⟶ M.complex ()) (hu hm)
    (i : ℤ) (x : C.complex.X i) :
    S.coord i ((algebraFromComponents S p d hu hm).chainMap.f i x) =
      (p.chainMap.f i x, d.f i x) :=
  (S.coord i).apply_symm_apply _

private def mapCoefficients (S : Extension M) (U : Extension N) (g : M ⟶ N) :
    CoefficientMap S U g := by
  let d := coefficientProjection S ≫ g.app ()
  have hd (i : ℤ) (x : S.algebra.complex.X i) :
      d.f i x = (g.app ()).f i (S.coord i x).2 := rfl
  have hu : d.f 0 S.algebra.one = 0 := by rw [hd, S.unit_coord]; exact map_zero _
  have hm (i j n : ℤ) (h : i+j=n) (x : S.algebra.complex.X i) (y : S.algebra.complex.X j) :
      d.f n (S.algebra.mul i j n h x y) =
        act N i j n h (d.f i x) (S.projection.chainMap.f j y) +
          (i*j).negOnePow • act N j i n (by omega) (d.f j y) (S.projection.chainMap.f i x) := by
    rw [hd, S.multiplication, S.projection_coord, S.projection_coord, hd, hd]
    simp only [Units.smul_def, map_add, map_zsmul, g.comm_act]
  let f := algebraFromComponents U S.projection d hu hm
  have hf (i : ℤ) (x : S.algebra.complex.X i) :
      U.coord i (f.chainMap.f i x) = (S.projection.chainMap.f i x, d.f i x) :=
    algebraFromComponents_coord U S.projection d hu hm i x
  refine ⟨f, algebraHom_ext ?_, algebraHom_ext ?_, fun i x => congrArg Prod.snd (hf i x)⟩
  · intro i x
    change U.projection.chainMap.f i (f.chainMap.f i x) = _
    rw [U.projection_coord, hf]
  · intro i x
    apply (U.coord i).injective
    change U.coord i (f.chainMap.f i (S.zeroSection.chainMap.f i x)) = _
    rw [hf, U.section_coord, hd, S.projection_coord, S.section_coord]
    exact Prod.ext rfl (map_zero _)

end Coordinates

private theorem coefficientNaturalityProof : CoefficientNaturality.{u,v} := by
  intro k _ _ A B b R T M N S U E E' g
  let G := mapCoefficients S U g
  refine ⟨G, fun f i x => ?_⟩
  rw [E'.read_equiv, E.read_equiv]
  exact G.coefficients i (f.val.chainMap.f i x)

section Derivations

variable (R : Model b) {M : B.Module} (S : Extension M)

local notation "P" => R.algebra.toCommDGAlgebra
local notation "p" => underlying R.augmentation
local notation "baseMap" => underlying R.base

private abbrev RelativeDerivation (d : (P).complex ⟶ M.complex ()) : Prop :=
  IsDerivation baseMap (M := restrict p M) (Cochain.ofHom d)

private abbrev mapComponent (f : Maps R S.projection S.zeroSection) :
    (P).complex ⟶ M.complex () :=
  f.val.chainMap ≫ coefficientProjection S

private theorem map_first (f : Maps R S.projection S.zeroSection) (i : ℤ)
    (x : (P).complex.X i) :
    (S.coord i (f.val.chainMap.f i x)).1 = (p).chainMap.f i x :=
  (S.projection_coord i _).symm.trans (hom_apply_eq f.property.1 i x)

private theorem mapComponent_derivation (f : Maps R S.projection S.zeroSection) :
    RelativeDerivation R (mapComponent R S f) := by
  constructor
  · intro i q e x
    have eq : q = i := by omega
    revert e
    rw [eq]
    intro e
    rw [Cochain.ofHom_v]
    change (S.coord i (f.val.chainMap.f i ((baseMap).chainMap.f i x))).2 = 0
    have h := hom_apply_eq f.property.2 i x
    change f.val.chainMap.f i ((baseMap).chainMap.f i x) =
      S.zeroSection.chainMap.f i ((underlying b).chainMap.f i x) at h
    rw [h, S.section_coord]
  · intro i j n ir jr nr h hi hj hn x y
    have ei : ir = i := by omega
    have ej : jr = j := by omega
    have en : nr = n := by omega
    revert hi hj hn
    rw [ei, ej, en]
    intro hi hj hn
    rw [Cochain.ofHom_v, Cochain.ofHom_v, Cochain.ofHom_v]
    change (S.coord n (f.val.chainMap.f n ((P).mul i j n h x y))).2 =
      act M i j n h (S.coord i (f.val.chainMap.f i x)).2 ((p).chainMap.f j y) +
        (i*j).negOnePow • act M j i n (by omega)
          (S.coord j (f.val.chainMap.f j y)).2 ((p).chainMap.f i x)
    rw [f.val.map_mul, S.multiplication, map_first R S f, map_first R S f]

private theorem derivation_zero_on_base (d : (P).complex ⟶ M.complex ())
    (h : RelativeDerivation R d) (i : ℤ) (x : A.complex.X i) :
    d.f i ((baseMap).chainMap.f i x) = 0 := by
  simpa only [Cochain.ofHom_v] using h.relative i i (add_zero i) x

private def mapOfDerivation (d : (P).complex ⟶ M.complex ()) (hd : RelativeDerivation R d) :
    Maps R S.projection S.zeroSection := by
  have hu : d.f 0 (P).one = 0 := by
    rw [← (baseMap).map_one]
    exact derivation_zero_on_base R d hd 0 A.one
  have hm (i j n : ℤ) (h : i+j=n) (x : (P).complex.X i) (y : (P).complex.X j) :
      d.f n ((P).mul i j n h x y) =
        act M i j n h (d.f i x) ((p).chainMap.f j y) +
          (i*j).negOnePow • act M j i n (by omega) (d.f j y) ((p).chainMap.f i x) := by
    have e := hd.leibniz i j n i j n h (add_zero i) (add_zero j) (add_zero n) x y
    rw [Cochain.ofHom_v, Cochain.ofHom_v, Cochain.ofHom_v] at e
    exact e
  let f := algebraFromComponents S p d hu hm
  have hf (i : ℤ) (x : (P).complex.X i) :
      S.coord i (f.chainMap.f i x) = ((p).chainMap.f i x, d.f i x) :=
    algebraFromComponents_coord S p d hu hm i x
  refine ⟨f, algebraHom_ext ?_, algebraHom_ext ?_⟩
  · intro i x
    change S.projection.chainMap.f i (f.chainMap.f i x) = _
    rw [S.projection_coord, hf]
  · intro i x
    apply (S.coord i).injective
    change S.coord i (f.chainMap.f i ((baseMap).chainMap.f i x)) =
      S.coord i (S.zeroSection.chainMap.f i ((underlying b).chainMap.f i x))
    rw [hf, S.section_coord, derivation_zero_on_base R d hd]
    exact Prod.ext (hom_apply_eq (show baseMap ≫ p = underlying b from R.triangle) i x) rfl

private theorem mapOfDerivation_coord (d : (P).complex ⟶ M.complex ())
    (hd : RelativeDerivation R d) (i : ℤ) (x : (P).complex.X i) :
    S.coord i ((mapOfDerivation R S d hd).val.chainMap.f i x) =
      ((p).chainMap.f i x, d.f i x) :=
  (S.coord i).apply_symm_apply _

end Derivations

section CotangentCycles

open private tensor_ext scalarExtend scalarExtend_pure unit_tensor_action
  baseChangedSymbol_d baseChangedSymbol_mul representStrict
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison
open Specs.DerivedFormalization.Affine.Tensor (restrictFunctor)

variable (R : Model b) (T : ModuleTensor.{u,v} k) {M : B.Module}

local notation "P" => R.algebra.toCommDGAlgebra
local notation "p" => underlying R.augmentation
local notation "baseMap" => underlying R.base
local notation "O" => R.differentials
local notation "L" => R.module T

variable (ht : T.Formulas (underlying R.augmentation) (regular B.toCommDGAlgebra))

private def cycleComponent (z : Cycles R T M) : (P).complex ⟶ M.complex () :=
  Tensor.chainOfDegrees
    (fun i => (((strictMap z).app ()).f i).hom.comp (symbol R T i)) (by
      intro i x
      change (M.complex ()).d i (i+1) (((strictMap z).app ()).f i (symbol R T i x)) =
        ((strictMap z).app ()).f (i+1) (symbol R T (i+1) ((P).complex.d i (i+1) x))
      rw [← baseChangedSymbol_d T O ht]
      exact CategoryTheory.congr_fun (((strictMap z).app ()).comm i (i+1)) (symbol R T i x))

private theorem cycleComponent_derivation (z : Cycles R T M) :
    RelativeDerivation R (cycleComponent R T ht z) := by
  constructor
  · intro i q h x
    have eq : q = i := by omega
    revert h
    rw [eq]
    intro h
    rw [Cochain.ofHom_v]
    change ((strictMap z).app ()).f i
      (T.tmul p (N := regular B.toCommDGAlgebra) i 0 i (add_zero i)
        (value (O).symbol i i (add_zero i) ((baseMap).chainMap.f i x)) B.one) = 0
    rw [(O).symbol.property.relative i i (add_zero i) x]
    change ((strictMap z).app ()).f i
      (T.degree p (O).module (regular B.toCommDGAlgebra) i
        (Tensor.pair p (N := regular B.toCommDGAlgebra) i 0 i (add_zero i) 0 B.one)) = 0
    rw [map_zero, LinearMap.zero_apply, map_zero, map_zero]
  · intro i j n ir jr nr h hi hj hn x y
    have ei : ir = i := by omega
    have ej : jr = j := by omega
    have en : nr = n := by omega
    revert hi hj hn
    rw [ei, ej, en]
    intro hi hj hn
    rw [Cochain.ofHom_v, Cochain.ofHom_v, Cochain.ofHom_v]
    let F := strictMap z
    change (F.app ()).f n (symbol R T n ((P).mul i j n h x y)) =
      act M i j n h ((F.app ()).f i (symbol R T i x)) ((p).chainMap.f j y) +
        (i*j).negOnePow • act M j i n (by omega)
          ((F.app ()).f j (symbol R T j y)) ((p).chainMap.f i x)
    rw [baseChangedSymbol_mul T O ht]
    simp only [Units.smul_def, map_add, map_zsmul, F.comm_act]

/-- Tensor with the unit before restricting the scalar-extended module to (P). -/
private def tensorUnitDegree (i : ℤ) : term (O).module i →ₗ[k] term L i :=
  (T.degree p (O).module (regular B.toCommDGAlgebra) i).toLinearMap.comp
    ((Tensor.pair p (N := regular B.toCommDGAlgebra) i 0 i (add_zero i)).flip B.one)

private theorem tensorUnitDegree_apply (i : ℤ) (x : term (O).module i) :
    tensorUnitDegree R T i x =
      T.tmul p (N := regular B.toCommDGAlgebra) i 0 i (add_zero i) x B.one := rfl

private def tensorUnit : (O).module ⟶ restrict p L :=
  Tensor.homOfDegrees (tensorUnitDegree R T) (by
    intro i x
    change ((L).complex ()).d i (i+1) (tensorUnitDegree R T i x) =
      tensorUnitDegree R T (i+1) (((O).module.complex ()).d i (i+1) x)
    rw [tensorUnitDegree_apply, tensorUnitDegree_apply, ht.differential]
    change _ + i.negOnePow • T.tmul p (N := regular B.toCommDGAlgebra)
      i 1 (i+1) rfl x (B.complex.d 0 1 B.one) = _
    rw [B.toDGAlgebra.d_id]
    change _ + i.negOnePow • T.degree p (O).module (regular B.toCommDGAlgebra) (i+1)
      (Tensor.pair p (N := regular B.toCommDGAlgebra) i 1 (i+1) rfl x 0) = _
    rw [map_zero, map_zero, smul_zero, add_zero]) (by
    intro i j n h x y
    change tensorUnitDegree R T n (act (O).module i j n h x y) =
      act L i j n h (tensorUnitDegree R T i x) ((p).chainMap.f j y)
    rw [tensorUnitDegree_apply, tensorUnitDegree_apply, unit_tensor_action T ht]
    have e := Tensor.pure_balance p (N := regular B.toCommDGAlgebra)
      i j 0 n j n h (add_zero j) (add_zero n) x y B.one
    rw [show signedLeft (regular B.toCommDGAlgebra) j 0 j (add_zero j)
        ((p).chainMap.f j y) B.one = (p).chainMap.f j y from by
      rw [signedLeft_apply, mul_zero, Int.negOnePow_zero, one_smul]
      exact B.toDGAlgebra.id_comp (a := ()) (b := ()) j _] at e
    exact congrArg (T.degree p (O).module (regular B.toCommDGAlgebra) n) e)

include ht in
private theorem strictMap_ext_on_symbols {F G : L ⟶ M}
    (h : ∀ (i : ℤ) (x : (P).complex.X i),
      (F.app ()).f i (symbol R T i x) = (G.app ()).f i (symbol R T i x))
    (d : (P).complex ⟶ M.complex ()) (hd : RelativeDerivation R d)
    (hF : ∀ (i : ℤ) (x : (P).complex.X i), (F.app ()).f i (symbol R T i x) = d.f i x) :
    F = G := by
  let f := tensorUnit R T ht ≫ (restrictFunctor p).map F
  let g := tensorUnit R T ht ≫ (restrictFunctor p).map G
  obtain ⟨H, _, hH⟩ := (O).represents (restrict p M) 0 ⟨Cochain.ofHom d, hd⟩
  have hf : ofStrict f = H := hH _ (by
    intro i q e x
    have eq : q = i := by omega
    revert e
    rw [eq]
    intro e
    change (Cochain.ofHom (f.app ())).v i i (add_zero i)
      (value (O).symbol i i (add_zero i) x) = (Cochain.ofHom d).v i i (add_zero i) x
    rw [Cochain.ofHom_v, Cochain.ofHom_v]
    exact hF i x)
  have hg : ofStrict g = H := hH _ (by
    intro i q e x
    have eq : q = i := by omega
    revert e
    rw [eq]
    intro e
    change (Cochain.ofHom (g.app ())).v i i (add_zero i)
      (value (O).symbol i i (add_zero i) x) = (Cochain.ofHom d).v i i (add_zero i) x
    rw [Cochain.ofHom_v, Cochain.ofHom_v]
    exact (h i x).symm.trans (hF i x))
  have eqUnit (i : ℤ) (x : term (O).module i) :
      (F.app ()).f i (tensorUnitDegree R T i x) =
        (G.app ()).f i (tensorUnitDegree R T i x) := by
    have eq := CategoryTheory.congr_fun
      (congrArg (fun z => component z () i i (add_zero i)) (hf.trans hg.symm)) x
    change (Cochain.ofHom (f.app ())).v i i (add_zero i) x =
      (Cochain.ofHom (g.app ())).v i i (add_zero i) x at eq
    rw [Cochain.ofHom_v, Cochain.ofHom_v] at eq
    exact eq
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply tensor_ext T
  intro i j e x y
  rw [← unit_tensor_action T ht i j n e x y, F.comm_act, G.comm_act]
  exact congrArg (fun w => act M i j n e w y) (eqUnit i x)

include ht in
private theorem cycle_ext_on_symbols {z z' : Cycles R T M}
    (h : ∀ (i : ℤ) (x : (P).complex.X i), read z i x = read z' i x) : z = z' := by
  have e := strictMap_ext_on_symbols R T ht (F := strictMap z) (G := strictMap z')
    (fun i x => h i x) _ (cycleComponent_derivation R T ht z) (fun _ _ => rfl)
  rw [← strictCycle_strictMap z, ← strictCycle_strictMap z', e]

variable (S : Extension M)

include ht in
private theorem exists_cycle_for_map (f : Maps R S.projection S.zeroSection) :
    ∃ z : Cycles R T M, ∀ (i : ℤ) (x : (P).complex.X i),
      read z i x = (S.coord i (f.val.chainMap.f i x)).2 := by
  obtain ⟨g, hg⟩ := representStrict (O) (restrict p M) (mapComponent R S f)
    (mapComponent_derivation R S f)
  refine ⟨strictCycle (scalarExtend T ht g), fun i x => ?_⟩
  change (Cochain.ofHom ((scalarExtend T ht g).app ())).v i i (add_zero i) (symbol R T i x) = _
  rw [Cochain.ofHom_v]
  change ((scalarExtend T ht g).app ()).f i
    (T.tmul p (N := regular B.toCommDGAlgebra) i 0 i (add_zero i)
      (value (O).symbol i i (add_zero i) x) B.one) = _
  rw [scalarExtend_pure, M.act_id, hg]
  rfl

private def cycleComparison : CycleComparison R T S := by
  let forward := fun f : Maps R S.projection S.zeroSection => (exists_cycle_for_map R T ht S f).choose
  have hforward (f : Maps R S.projection S.zeroSection) (i : ℤ) (x : (P).complex.X i) :
      read (forward f) i x = (S.coord i (f.val.chainMap.f i x)).2 :=
    (exists_cycle_for_map R T ht S f).choose_spec i x
  let backward := fun z : Cycles R T M =>
    mapOfDerivation R S (cycleComponent R T ht z) (cycleComponent_derivation R T ht z)
  have hbackward (z : Cycles R T M) (i : ℤ) (x : (P).complex.X i) :
      S.coord i ((backward z).val.chainMap.f i x) = ((p).chainMap.f i x, read z i x) :=
    mapOfDerivation_coord R S (cycleComponent R T ht z) (cycleComponent_derivation R T ht z) i x
  refine ⟨⟨forward, backward, ?_, ?_⟩, hforward, ?_, cycle_ext_on_symbols R T ht⟩
  · intro f
    apply Subtype.ext
    apply algebraHom_ext
    intro i x
    apply (S.coord i).injective
    rw [hbackward, hforward]
    exact Prod.ext (map_first R S f i x).symm rfl
  · intro z
    apply cycle_ext_on_symbols R T ht
    intro i x
    rw [hforward, hbackward]
  · intro f
    exact ⟨mapComponent R S f, fun _ _ => rfl, mapComponent_derivation R S f⟩

end CotangentCycles

private theorem mapsAreCyclesProof : MapsAreCycles.{u,v} := by
  intro k _ _ A B b R T ht M S
  exact ⟨cycleComparison R T ht S⟩

section PathTargets

open PolynomialPath
  (truncationDegree mem_truncationDegree truncationTerms truncation truncationInclusion
    ClosedAlgebraTerms)

private theorem maps_to_truncation {D : NonpositiveCDGA.{u,v} k}
    {E : CommDGAlgebra.{u,v} k} (f : D.toCommDGAlgebra ⟶ E) (i : ℤ) (x : D.complex.X i) :
    f.chainMap.f i x ∈ truncationDegree E i := by
  rw [mem_truncationDegree]
  constructor
  · intro h
    rw [(D.nonpositive i h).elim x 0, map_zero]
  · rintro rfl
    change E.complex.d 0 1 (f.chainMap.f 0 x) = 0
    have h := CategoryTheory.congr_fun (f.chainMap.comm 0 1) x
    simp only [ModuleCat.comp_apply] at h
    rw [h, D.d_zero_apply, map_zero]

private abbrev factorTruncation {D : NonpositiveCDGA.{u,v} k}
    {E : CommDGAlgebra.{u,v} k} (f : D.toCommDGAlgebra ⟶ E) :
    D.toCommDGAlgebra ⟶ (truncation E).toCommDGAlgebra :=
  (truncationTerms E).factor f (maps_to_truncation f)

private theorem factorTruncation_inclusion {D : NonpositiveCDGA.{u,v} k}
    {E : CommDGAlgebra.{u,v} k} (f : D.toCommDGAlgebra ⟶ E) :
    factorTruncation f ≫ truncationInclusion E = f :=
  (truncationTerms E).factor_inclusion f _

variable {M : B.Module} (S : Extension M) (W : ModulePathModel M) (U : Extension W.obj)

private def pathTarget : PathTarget S W U where
  algebra := truncation U.algebra
  inclusion := truncationInclusion U.algebra
  inclusion_injective _ := Subtype.val_injective
  inclusion_range i x := by
    rw [← mem_truncationDegree]
    change (∃ y : truncationDegree U.algebra i, y.val = x) ↔ _
    exact ⟨fun ⟨y, h⟩ => h ▸ y.property, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  zeroSection := factorTruncation U.zeroSection
  section_inclusion := factorTruncation_inclusion U.zeroSection
  evaluation c := truncationInclusion U.algebra ≫ (mapCoefficients U S (W.evaluation c)).hom
  evaluation_projection c := by
    rw [Category.assoc, (mapCoefficients U S (W.evaluation c)).projection_comm]
  section_evaluation c := by
    rw [← Category.assoc, factorTruncation_inclusion,
      (mapCoefficients U S (W.evaluation c)).section_comm]
  evaluation_coefficients c i x :=
    (mapCoefficients U S (W.evaluation c)).coefficients i _

private def pathMapsEquiv (R : Model b) :
    Maps R (pathTarget S W U).augmentation (pathTarget S W U).zeroSection ≃
      Maps R U.projection U.zeroSection := by
  let H := pathTarget S W U
  have cancel {D : CommDGAlgebra.{u,v} k} {f g : D ⟶ H.algebra.toCommDGAlgebra}
      (e : f ≫ H.inclusion = g ≫ H.inclusion) : f = g :=
    (truncationTerms U.algebra).inclusion_cancel e
  refine
    { toFun := fun f => ⟨f.val ≫ H.inclusion, ?_, ?_⟩
      invFun := fun g => ⟨factorTruncation g.val, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [Category.assoc]
    exact f.property.1
  · rw [← Category.assoc, f.property.2, Category.assoc, H.section_inclusion]
  · change factorTruncation g.val ≫ truncationInclusion U.algebra ≫ U.projection = _
    rw [← Category.assoc, factorTruncation_inclusion]
    exact g.property.1
  · apply cancel
    change (underlying R.base ≫ factorTruncation g.val) ≫ truncationInclusion U.algebra =
      (underlying b ≫ factorTruncation U.zeroSection) ≫ truncationInclusion U.algebra
    rw [Category.assoc, Category.assoc, factorTruncation_inclusion, factorTruncation_inclusion]
    exact g.property.2
  · intro f
    apply Subtype.ext
    apply cancel
    exact factorTruncation_inclusion (f.val ≫ H.inclusion)
  · intro g
    apply Subtype.ext
    exact factorTruncation_inclusion g.val

end PathTargets

private theorem polynomialPathsAreCyclesProof : PolynomialPathsAreCycles.{u,v} := by
  intro k _ _ A B b R T ht M _ S W U
  let H := pathTarget S W U
  let E := cycleComparison R T ht S
  let F := cycleComparison R T ht U
  let e := (pathMapsEquiv S W U R).trans F.equiv
  have he (f : Maps R H.augmentation H.zeroSection) (i : ℤ) (x : R.algebra.complex.X i) :
      read (e f) i x = (U.coord i ((f.val ≫ H.inclusion).chainMap.f i x)).2 :=
    F.read_equiv (pathMapsEquiv S W U R f) i x
  refine ⟨H, E, e, he, ?_⟩
  intro f c i x
  rw [E.read_equiv, he]
  exact H.evaluation_coefficients c i (f.val.chainMap.f i x)

theorem extensionConstruction : ExtensionConstruction.{u,v} :=
  extensionConstructionProof

theorem mapsAreCycles : MapsAreCycles.{u,v} :=
  mapsAreCyclesProof

theorem coefficientNaturality : CoefficientNaturality.{u,v} :=
  coefficientNaturalityProof

theorem polynomialPathsAreCycles : PolynomialPathsAreCycles.{u,v} :=
  polynomialPathsAreCyclesProof

end
end DerivedFormalization.Affine.SquareZeroMaps
