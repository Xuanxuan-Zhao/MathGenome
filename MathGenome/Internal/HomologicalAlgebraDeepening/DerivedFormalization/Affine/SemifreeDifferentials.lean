import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.SemifreeDifferentials
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.KahlerDifferentials
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeAlgebras
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFree
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CellReindex

open CategoryTheory HomologicalComplex
open scoped DirectSum Classical
open CochainComplex.HomComplex (Cochain δ δ_v)

universe u v

namespace DerivedFormalization.Affine.SemifreeDifferentials

open Specs.DerivedFormalization.DG.HomComplex (gradedHom component)
open Specs.DerivedFormalization.Affine.Tensor (term)
open Semifree (Variables StagedPresentation variableTerm Polynomial polynomialMul coefficient)
open Specs.DerivedFormalization.Affine.Tensor
  (act signedLeft signedLeft_apply signedLeft_right signedLeft_assoc act_assoc_at)
open Kahler (Derivation value)

noncomputable section

variable {k : Type u} [Field k] [CharZero k]

private def homComparison {A P : NonpositiveCDGA.{u,v} k} (f : A ⟶ P) (M : P.Module) :
    HomDerivationComparison (Kahler.model (f : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra)) M where
  cochains := Kahler.derivationComplex f M
  derivations _ := LinearEquiv.refl k _
  identification := Kahler.homComplexIso f M
  commutator r D := congrArg Subtype.val (Kahler.derivationComplex_d f M r D)
  evaluation r i p h D x := by
    change component (Kahler.homEquiv f M r D) () i p h
      (Kahler.value (Kahler.universalDerivation f) i i (add_zero i) x) = _
    rw [Kahler.homEquiv_apply, Kahler.descend_partial]
    rfl

private theorem readout_evaluation {Q P : CommDGAlgebra.{u,v} k} {g : Q ⟶ P}
    {O : Kahler.DifferentialModel g} {M : P.Module} (C : HomDerivationComparison O M)
    {r : ℤ} (F : gradedHom O.module M r) (i p : ℤ) (h : i+r=p) (x : P.complex.X i) :
    Kahler.value (C.readout F) i p h x =
      component F () i p h (Kahler.value O.symbol i i (add_zero i) x) := by
  rw [← C.evaluation r i p h (C.identification.inv.f r F) x]
  have eq := congrArg (fun t => t.f r) C.identification.inv_hom_id
  change C.identification.inv.f r ≫ C.identification.hom.f r = 𝟙 _ at eq
  have apply_eq := CategoryTheory.congr_fun eq F
  change C.identification.hom.f r (C.identification.inv.f r F) = F at apply_eq
  rw [apply_eq]

theorem homDerivations : HomDerivations.{u,v} := by
  intro k _ _ A P f
  refine ⟨Kahler.model f, fun n => LinearEquiv.refl k _, homComparison f, fun _ _ => rfl, ?_⟩
  intro M N b r F i p h x
  rw [readout_evaluation, readout_evaluation]
  change (((F.val ()).comp (Cochain.ofHom (b.app ())) (add_zero r)).v i p h)
      (Kahler.value (Kahler.universalDerivation f) i i (add_zero i) x) = _
  rw [Cochain.comp_v _ _ _ i p p h (add_zero p), Cochain.ofHom_v]
  rfl

/-- The closed universal symbol commutes with the cochain differential. -/
theorem differential_symbol {A P : CommDGAlgebra.{u,v} k} {f : A ⟶ P}
    (O : Kahler.DifferentialModel f) (i : ℤ) (x : P.complex.X i) :
    (O.module.complex ()).d i (i+1) (Kahler.value O.symbol i i (add_zero i) x) =
      Kahler.value O.symbol (i+1) (i+1) (add_zero (i+1)) (P.complex.d i (i+1) x) := by
  have h : (δ 0 1 O.symbol.val).v i (i+1) (by omega) x = 0 := by
    rw [O.closed, Cochain.zero_v]
    rfl
  rw [δ_v 0 1 (by decide) _ i (i+1) (by omega) i (i+1) (by omega) rfl] at h
  change (O.module.complex ()).d i (i+1) (Kahler.value O.symbol i i (add_zero i) x) +
    (1 : ℤ).negOnePow • Kahler.value O.symbol (i+1) (i+1) (add_zero (i+1))
      (P.complex.d i (i+1) x) = 0 at h
  simpa only [Int.negOnePow_one, Units.neg_smul, one_smul, ← sub_eq_add_neg, sub_eq_zero] using h

/-- Positive coefficient degrees cannot occur in a differential over the
nonpositive source algebra. -/
theorem differential_coefficient_level {P : NonpositiveCDGA.{u,v} k} {V : Variables.{v}}
    {M : P.Module} {e : ∀ x, term M (V.degree x)} (basis : IsGradedBasis e)
    (x y : V.Index)
    (hy : (LinearEquiv.ofBijective _ (basis (V.degree x+1))).symm
      ((M.complex ()).d (V.degree x) (V.degree x+1) (e x)) y ≠ 0) :
    level V y < level V x := by
  have hd : V.degree x + 1 + -V.degree y ≤ 0 := by
    by_contra! hp
    exact hy ((P.nonpositive _ hp).allEq _ _)
  have hx := V.nonpositive x
  have hy' := V.nonpositive y
  unfold level
  omega

section SquareZero

variable {P : CommDGAlgebra.{u,v} k} (N : P.Module)

private abbrev SquareTerm (i : ℤ) := P.complex.X i × term N i

private def squareMul (i j n : ℤ) (h : i+j=n) :
    SquareTerm N i →ₗ[k] SquareTerm N j →ₗ[k] SquareTerm N n :=
  let fst (r : ℤ) := LinearMap.fst k (P.complex.X r) (term N r)
  let snd (r : ℤ) := LinearMap.snd k (P.complex.X r) (term N r)
  let first := ((P.mul i j n h).compl₂ (fst j)).comp (fst i)
  let second := ((act N i j n h).compl₂ (fst j)).comp (snd i) +
    ((signedLeft N i j n h).compl₂ (snd j)).comp (fst i)
  { toFun := fun a => (first a).prod (second a)
    map_add' := fun a b => LinearMap.ext fun c => by
      simp only [LinearMap.prod_apply, Function.prod_apply, map_add, LinearMap.add_apply,
        Prod.mk_add_mk]
    map_smul' := fun r a => LinearMap.ext fun b => by
      simp only [LinearMap.prod_apply, Function.prod_apply, map_smul, LinearMap.smul_apply,
        Prod.smul_mk, RingHom.id_apply] }

private theorem squareMul_apply (i j n : ℤ) (h : i+j=n) (a : SquareTerm N i) (b : SquareTerm N j) :
    squareMul N i j n h a b =
      (P.mul i j n h a.1 b.1, act N i j n h a.2 b.1 + signedLeft N i j n h a.1 b.2) := rfl

/-- The graded square-zero extension, viewed with zero differential for the
graded universal property of the polynomial algebra. -/
@[reducible] private def squareAlgebra : CommDGAlgebra.{u,v} k where
  toDGAlgebra :=
    { hom := fun _ _ => { X := fun i => ModuleCat.of k (SquareTerm N i), d := fun _ _ => 0 }
      comp := fun i j n h => squareMul N i j n h
      id := fun _ => (P.one, 0)
      d_id := by intros; rfl
      id_comp := by
        intro _ _ i a
        rw [squareMul_apply]
        apply Prod.ext
        · exact P.toDGAlgebra.id_comp i a.1
        · change act N 0 i i _ 0 a.1 + signedLeft N 0 i i _ P.one a.2 = a.2
          simp only [map_zero, LinearMap.zero_apply, zero_add, signedLeft_apply, zero_mul,
            Int.negOnePow_zero, one_smul]
          exact N.act_id () i a.2
      comp_id := by
        intro _ _ i a
        rw [squareMul_apply]
        apply Prod.ext
        · exact P.toDGAlgebra.comp_id i a.1
        · change act N i 0 i _ a.2 P.one + signedLeft N i 0 i _ a.1 0 = a.2
          rw [map_zero, add_zero]
          exact N.act_id () i a.2
      assoc := by
        intro _ _ _ _ i j l a b c
        simp only [squareMul_apply]
        apply Prod.ext
        · exact P.toDGAlgebra.assoc i j l a.1 b.1 c.1
        · change act N (i+j) l _ _ (_ + _) c.1 + signedLeft N (i+j) l _ _ _ c.2 =
            act N i (j+l) _ _ a.2 _ + signedLeft N i (j+l) _ _ a.1 (_ + _)
          simp only [map_add, LinearMap.add_apply]
          rw [act_assoc_at N i j l (i+j) (j+l) (i+j+l) rfl rfl rfl,
            ← signedLeft_right N i j l (i+j) (j+l) (i+j+l) rfl rfl rfl,
            signedLeft_assoc]
          exact add_assoc _ _ _
      leibniz := by
        intros
        simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero, smul_zero, add_zero] }
  graded_comm := by
    intro i j n h a b
    simp only [squareMul_apply, Prod.smul_mk]
    apply Prod.ext
    · exact P.graded_comm i j n h a.1 b.1
    · change act N i j n h a.2 b.1 + signedLeft N i j n h a.1 b.2 =
        (i*j).negOnePow • (act N j i n _ b.2 a.1 + signedLeft N j i n _ b.1 a.2)
      simp only [signedLeft_apply, smul_add, smul_smul, mul_comm j i,
        Int.units_mul_self, one_smul]
      exact add_comm _ _

end SquareZero

section PolynomialDerivations

variable {A P : NonpositiveCDGA.{u,v} k} {V : Variables.{v}} {f : A ⟶ P}
variable (E : StagedPresentation A V f) (N : P.Module)

private abbrev variableImage (x : V.Index) := E.component _ (variableTerm A V x)

private def diagonal {X Y : ModuleCochain.{u,v} k}
    (L : ∀ n : ℤ, X.X n ⟶ Y.X n) : Cochain X Y 0 :=
  Cochain.mk fun i p h => L i ≫ (Y.XIsoOfEq (by omega : i = p)).hom

omit [CharZero k] in
@[simp] private theorem diagonal_v {X Y : ModuleCochain.{u,v} k}
    (L : ∀ n : ℤ, X.X n ⟶ Y.X n) (n : ℤ) :
    (diagonal L).v n n (add_zero n) = L n := by
  rw [diagonal, Cochain.mk_v]
  simp

private def derivationFromValues (z : ∀ x, term N (V.degree x)) :
    {D : Derivation (f : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra) N 0 //
      ∀ x, value D (V.degree x) (V.degree x) (add_zero _) (variableImage E x) = z x} := by
  let g (i : ℤ) : A.complex.X i →ₗ[k] (squareAlgebra N).complex.X i :=
    (f.chainMap.f i).hom.prod 0
  have g_one : g 0 A.one = (squareAlgebra N).one := by
    apply Prod.ext
    · exact f.map_one
    · rfl
  have g_mul (i j n : ℤ) (h : i+j=n) (a : A.complex.X i) (b : A.complex.X j) :
      g n (A.mul i j n h a b) = (squareAlgebra N).mul i j n h (g i a) (g j b) := by
    change g n (A.mul i j n h a b) = squareMul N i j n h (g i a) (g j b)
    rw [squareMul_apply]
    apply Prod.ext
    · exact f.map_mul i j n h a b
    · change 0 = act N i j n h 0 (f.chainMap.f j b) + signedLeft N i j n h (f.chainMap.f i a) 0
      simp
  let lift := (Classical.choice (Semifree.gradedUniversalProperty A V (squareAlgebra N)
    g g_one g_mul (fun x => (variableImage E x, z x)))).default
  let projection : Semifree.GradedLift A V P.toCommDGAlgebra
      (fun i => (f.chainMap.f i).hom) (variableImage E) :=
    { component := fun i => (LinearMap.fst k _ _).comp (lift.component i)
      map_mul := by
        intro i j n h a b
        exact congrArg Prod.fst (lift.map_mul i j n h a b)
      map_base := fun i a => congrArg Prod.fst (lift.map_base i a)
      map_var := fun x => congrArg Prod.fst (lift.map_var x) }
  let presented : Semifree.GradedLift A V P.toCommDGAlgebra
      (fun i => (f.chainMap.f i).hom) (variableImage E) :=
    ⟨fun i => (E.component i).toLinearMap, E.map_mul, E.map_base, fun _ => rfl⟩
  have proj_eq : projection = presented :=
    (Semifree.gradedLift_unique A V P.toCommDGAlgebra _ _).elim _ _
  have first (i : ℤ) (a : Polynomial A V i) : (lift.component i a).1 = E.component i a :=
    congrArg (fun q : Semifree.GradedLift A V P.toCommDGAlgebra
      (fun i => (f.chainMap.f i).hom) (variableImage E) => q.component i a) proj_eq
  let D (i : ℤ) : P.complex.X i ⟶ (N.complex ()).X i :=
    ModuleCat.ofHom (((LinearMap.snd k _ _).comp (lift.component i)).comp
      (E.component i).symm.toLinearMap)
  have on_poly (i : ℤ) (p : Polynomial A V i) : D i (E.component i p) = (lift.component i p).2 := by
    change (lift.component i ((E.component i).symm (E.component i p))).2 = _
    rw [LinearEquiv.symm_apply_apply]
  refine ⟨⟨diagonal D, ?_⟩, ?_⟩
  · constructor
    · intro i p h a
      have pp : i=p := by omega
      cases pp
      rw [diagonal_v, ← E.map_base, on_poly, lift.map_base]
      rfl
    · intro i j n ir jr nr h hi hj hn x y
      have ir_eq : i=ir := by omega
      cases ir_eq
      have jr_eq : j=jr := by omega
      cases jr_eq
      have nr_eq : n=nr := by omega
      cases nr_eq
      obtain ⟨a, rfl⟩ := (E.component i).surjective x
      obtain ⟨b, rfl⟩ := (E.component j).surjective y
      rw [diagonal_v, diagonal_v, diagonal_v, ← E.map_mul, on_poly, on_poly, on_poly, lift.map_mul]
      change (squareMul N i j n h (lift.component i a) (lift.component j b)).2 = _
      rw [squareMul_apply]
      change act N i j n h (lift.component i a).2 (lift.component j b).1 +
        signedLeft N i j n h (lift.component i a).1 (lift.component j b).2 = _
      rw [first, first, signedLeft_apply]
  · intro x
    change (diagonal D).v _ _ _ (E.component _ (variableTerm A V x)) = _
    rw [diagonal_v, on_poly, lift.map_var]

end PolynomialDerivations

section GradedBasis

open Specs.DerivedFormalization.DG
open Specs.DerivedFormalization.Affine.Tensor (dgCat)
variable {B : CommDGAlgebra.{u,v} k} {V : Variables.{v}}

private abbrev basisCells (B : CommDGAlgebra.{u,v} k) (V : Variables.{v}) (x : V.Index) :=
  SemiFree.cell (A := dgCat B) () (V.degree x)

private abbrev freeModule (B : CommDGAlgebra.{u,v} k) (V : Variables.{v}) : B.Module :=
  SemiFree.directSum (basisCells B V)

private abbrev single (B : CommDGAlgebra.{u,v} k) (V : Variables.{v}) (n : ℤ)
    (x : V.Index) : B.complex.X (n + -V.degree x) →ₗ[k] Coefficients B V n :=
  SemiFree.summand (basisCells B V) () n x

private theorem multiples_single {M : B.Module} (e : ∀ x, term M (V.degree x))
    (n : ℤ) (x : V.Index) (a : B.complex.X (n + -V.degree x)) :
    multiples e n (single B V n x a) = act M (V.degree x) (n + -V.degree x) n (by omega) (e x) a := by
  apply DirectSum.toModule_lof (R := k)

private abbrev freeGenerator (B : CommDGAlgebra.{u,v} k) (V : Variables.{v}) (x : V.Index) :
    term (freeModule B V) (V.degree x) :=
  single B V (V.degree x) x (SemiFree.generator (A := dgCat B) () (V.degree x))

private theorem freeGenerator_act (n : ℤ) (x : V.Index) (a : B.complex.X (n + -V.degree x)) :
    act (freeModule B V) (V.degree x) (n + -V.degree x) n (by omega) (freeGenerator B V x) a =
      single B V n x a := by
  have cell_act (d j n : ℤ) (h : d+j=n) (b : B.complex.X j) :
      act (SemiFree.cell (A := dgCat B) () d) d j n h
        (SemiFree.generator (A := dgCat B) () d) b =
        (B.complex.XIsoOfEq (by omega : j = n + -d)).hom b := by
    subst n
    exact RightDGModule.cellGenerator_mul (A := dgCat B) () d () j b
  change SemiFree.sumAct (basisCells B V) (V.degree x) (n + -V.degree x) n _ _ a = _
  rw [SemiFree.sumAct_summand, cell_act]
  simp [HomologicalComplex.XIsoOfEq]

private theorem multiples_freeGenerator {M : B.Module} (e : ∀ x, term M (V.degree x))
    (x : V.Index) : multiples e (V.degree x) (freeGenerator B V x) = e x := by
  rw [multiples_single]
  have act_unit (i j : ℤ) (h : (0 : ℤ) = j) (z : term M i) :
      act M i j i (by omega) z ((B.complex.XIsoOfEq h).hom B.one) = z := by
    subst j
    exact M.act_id () i z
  exact act_unit _ _ (by omega) (e x)

private theorem multiples_act {M : B.Module} (e : ∀ x, term M (V.degree x))
    (i j n : ℤ) (h : i+j=n) (z : Coefficients B V i) (a : B.complex.X j) :
    multiples e n (act (freeModule B V) i j n h z a) =
      act M i j n h (multiples e i z) a := by
  suffices hlin : (multiples e n).comp ((act (freeModule B V) i j n h).flip a) =
      ((act M i j n h).flip a).comp (multiples e i) from LinearMap.congr_fun hlin z
  apply DirectSum.linearMap_ext
  intro x
  apply LinearMap.ext
  intro b
  change multiples e n (SemiFree.sumAct (basisCells B V) i j n h (single B V i x b) a) =
    act M i j n h (multiples e i (single B V i x b)) a
  rw [SemiFree.sumAct_summand, multiples_single, multiples_single]
  exact (act_assoc_at M (V.degree x) (i + -V.degree x) j i (n + -V.degree x) n
    (by omega) (by omega) h (e x) b a).symm

private abbrev degreeMap {M N : B.Module} (F : gradedHom M N 0) (i : ℤ) :
    term M i →ₗ[k] term N i := (component F () i i (add_zero i)).hom

private theorem degreeMap_act {M N : B.Module} (F : gradedHom M N 0)
    (i j n : ℤ) (h : i+j=n) (z : term M i) (a : B.complex.X j) :
    degreeMap F n (act M i j n h z a) = act N i j n h (degreeMap F i z) a :=
  F.property (a := ()) (b := ()) i j n i n h (add_zero i) (add_zero n) z a

private def gradedOfDegrees {M N : B.Module} (L : ∀ i, term M i →ₗ[k] term N i)
    (hL : ∀ (i j n : ℤ) (h : i+j=n) z a, L n (act M i j n h z a) = act N i j n h (L i z) a) :
    gradedHom M N 0 :=
  ⟨fun a => by
    cases a
    exact diagonal fun i => ModuleCat.ofHom (L i), by
      rintro ⟨⟩ ⟨⟩ i j n ir nr h hi hn z a
      have ir_eq : i=ir := by omega
      cases ir_eq
      have nr_eq : n=nr := by omega
      cases nr_eq
      rw [diagonal_v, diagonal_v]
      exact hL i j n h z a⟩

@[simp] private theorem gradedOfDegrees_apply {M N : B.Module}
    (L : ∀ i, term M i →ₗ[k] term N i) (hL) (i : ℤ) (z : term M i) :
    degreeMap (gradedOfDegrees L hL) i z = L i z := by
  change (diagonal (fun i => ModuleCat.ofHom (L i))).v i i (add_zero i) z = _
  rw [diagonal_v]
  rfl

private def postDerivation {A : CommDGAlgebra.{u,v} k} {f : A ⟶ B} {M N : B.Module}
    (F : gradedHom M N 0) (D : Derivation f M 0) : Derivation f N 0 :=
  ⟨diagonal (fun i => ModuleCat.ofHom ((degreeMap F i).comp (value D i i (add_zero i)).hom)), by
    constructor
    · intro i p h a
      have pp : i=p := by omega
      cases pp
      rw [diagonal_v]
      change degreeMap F i (value D i i (add_zero i) (f.chainMap.f i a)) = _
      rw [D.property.relative, map_zero]
    · intro i j n ir jr nr h hi hj hn x y
      have ir_eq : i=ir := by omega
      cases ir_eq
      have jr_eq : j=jr := by omega
      cases jr_eq
      have nr_eq : n=nr := by omega
      cases nr_eq
      rw [diagonal_v, diagonal_v, diagonal_v]
      change degreeMap F n (value D n n (add_zero n) (B.mul i j n h x y)) = _
      rw [D.property.leibniz i j n i j n h (add_zero i) (add_zero j) (add_zero n),
        map_add, LinearMap.map_smul_of_tower, degreeMap_act, degreeMap_act]
      rfl⟩

@[simp] private theorem postDerivation_apply {A : CommDGAlgebra.{u,v} k} {f : A ⟶ B}
    {M N : B.Module} (F : gradedHom M N 0) (D : Derivation f M 0) (i : ℤ) (x : B.complex.X i) :
    value (postDerivation F D) i i (add_zero i) x = degreeMap F i (value D i i (add_zero i) x) := by
  change (diagonal (fun i => ModuleCat.ofHom ((degreeMap F i).comp
    (value D i i (add_zero i)).hom))).v i i (add_zero i) x = _
  rw [diagonal_v]
  rfl

variable {A P : NonpositiveCDGA.{u,v} k} {f : A ⟶ P}
variable (E : StagedPresentation A V f)

private theorem derivation_eq_on_polynomials {N : P.Module}
    {D D' : Derivation (f : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra) N 0}
    (h : ∀ x, value D (V.degree x) (V.degree x) (add_zero _) (variableImage E x) =
      value D' (V.degree x) (V.degree x) (add_zero _) (variableImage E x))
    (i : ℤ) (p : P.complex.X i) : value D i i (add_zero i) p = value D' i i (add_zero i) p := by
  obtain ⟨q, rfl⟩ := (E.component i).surjective p
  apply Semifree.polynomial_generated A V
    (fun n a => value D n n (add_zero n) (E.component n a) =
      value D' n n (add_zero n) (E.component n a))
  · intro n
    simp only [map_zero]
  · intro n a b ha hb
    simp only [map_add, ha, hb]
  · intro n s a ha
    simp only [Units.smul_def, map_zsmul, ha]
  · intro n a
    rw [E.map_base, D.property.relative, D'.property.relative]
  · exact h
  · intro i j n hij a b ha hb
    rw [E.map_mul, D.property.leibniz i j n i j n hij (add_zero i) (add_zero j) (add_zero n),
      D'.property.leibniz i j n i j n hij (add_zero i) (add_zero j) (add_zero n), ha, hb]

/-- The universal symbols of the polynomial variables form the right graded basis. -/
theorem graded_basis (O : Kahler.DifferentialModel (f : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra)) :
    IsGradedBasis (generator E O) := by
  let L := freeModule P.toCommDGAlgebra V
  let D := derivationFromValues E L (freeGenerator P.toCommDGAlgebra V)
  obtain ⟨F, hF, _⟩ := O.represents L 0 D.val
  have on_generator (x : V.Index) :
      degreeMap F (V.degree x) (generator E O x) = freeGenerator P.toCommDGAlgebra V x :=
    (hF _ _ (add_zero _) (variableImage E x)).trans (D.property x)
  intro n
  have left : (degreeMap F n).comp (multiples (generator E O) n) = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro x
    apply LinearMap.ext
    intro a
    change degreeMap F n (multiples (generator E O) n (single P.toCommDGAlgebra V n x a)) =
      single P.toCommDGAlgebra V n x a
    rw [multiples_single, degreeMap_act, on_generator, freeGenerator_act]
  let H := gradedOfDegrees (fun i => (multiples (generator E O) i).comp (degreeMap F i))
    (by
      intro i j n h z a
      change multiples (generator E O) n (degreeMap F n (act O.module i j n h z a)) = _
      rw [degreeMap_act]
      exact multiples_act (generator E O) i j n h (degreeMap F i z) a)
  have H_generator (x : V.Index) :
      degreeMap H (V.degree x) (generator E O x) = generator E O x := by
    rw [gradedOfDegrees_apply, LinearMap.comp_apply, on_generator, multiples_freeGenerator]
  have H_symbol (i : ℤ) (p : P.complex.X i) :
      degreeMap H i (value O.symbol i i (add_zero i) p) = value O.symbol i i (add_zero i) p := by
    rw [← postDerivation_apply]
    exact derivation_eq_on_polynomials E (fun x => by
      rw [postDerivation_apply]
      exact H_generator x) i p
  obtain ⟨K, _, hK⟩ := O.represents O.module 0 O.symbol
  have eqH : H = K := hK _ (by
    intro i p h z
    have pp : i=p := by omega
    cases pp
    exact H_symbol i z)
  have eqI : Specs.DerivedFormalization.DG.HomComplex.ofStrict (𝟙 O.module) = K :=
    hK _ (by
      intro i p h z
      have pp : i=p := by omega
      cases pp
      change (Cochain.ofHom (𝟙 (O.module.complex ()))).v i i (add_zero i)
        (value O.symbol i i (add_zero i) z) = _
      rw [Cochain.ofHom_v]
      rfl)
  have right (z : term O.module n) : multiples (generator E O) n (degreeMap F n z) = z := by
    change ((multiples (generator E O) n).comp (degreeMap F n)) z = _
    have hHz : degreeMap H n z = ((multiples (generator E O) n).comp (degreeMap F n)) z :=
      gradedOfDegrees_apply _ _ n z
    rw [← hHz, eqH, ← eqI]
    change ((Cochain.ofHom (𝟙 (O.module.complex ()))).v n n (add_zero n)) z = _
    rw [Cochain.ofHom_v]
    rfl
  have leftInv : Function.LeftInverse (degreeMap F n) (multiples (generator E O) n) :=
    fun z => LinearMap.congr_fun left z
  exact ⟨leftInv.injective, fun z => ⟨degreeMap F n z, right z⟩⟩

end GradedBasis

section CellPresentation

open Specs.DerivedFormalization.DG
open Specs.DerivedFormalization.Affine.Tensor (dgCat)
variable {B : CommDGAlgebra.{u,v} k} {V : Variables.{v}} {M : B.Module}
variable {e : ∀ x, term M (V.degree x)} (basis : IsGradedBasis e)

private abbrev coordinates (n : ℤ) : term M n ≃ₗ[k] Coefficients B V n :=
  (LinearEquiv.ofBijective (multiples e n) (basis n)).symm

private theorem coordinates_single (n : ℤ) (x : V.Index) (a : B.complex.X (n + -V.degree x)) :
    coordinates basis n (act M (V.degree x) (n + -V.degree x) n (by omega) (e x) a) =
      single B V n x a := by
  rw [← multiples_single]
  exact (coordinates basis n).apply_symm_apply _

private theorem coordinates_action (i j n : ℤ) (h : i+j=n) (z : term M i) (a : B.complex.X j)
    (x : V.Index) :
    coordinates basis n (act M i j n h z a) x =
      B.mul (i + -V.degree x) j (n + -V.degree x) (by omega) (coordinates basis i z x) a := by
  have hz : z = multiples e i (coordinates basis i z) :=
    ((coordinates basis i).symm_apply_apply z).symm
  nth_rw 1 [hz]
  rw [← multiples_act]
  change (coordinates basis n ((coordinates basis n).symm (act (freeModule B V) i j n h
    (coordinates basis i z) a))) x = _
  rw [(coordinates basis n).apply_symm_apply]
  rfl

private def stageSubmodule (l : ℕ) (n : ℤ) : Submodule k (term M n) where
  carrier := {z | ∀ x, l ≤ level V x → coordinates basis n z x = 0}
  zero_mem' := by intro x _; simp
  add_mem' := by
    intro z w hz hw x hx
    rw [map_add, DFinsupp.add_apply, hz x hx, hw x hx, add_zero]
  smul_mem' := by
    intro c z hz x hx
    rw [map_smul, DFinsupp.smul_apply, hz x hx, smul_zero]

private theorem stage_mono {l s : ℕ} (h : l ≤ s) (n : ℤ) :
    stageSubmodule basis l n ≤ stageSubmodule basis s n :=
  fun _ hz x hx => hz x (h.trans hx)

private theorem stage_action (l : ℕ) (i j n : ℤ) (h : i+j=n)
    (z : term M i) (hz : z ∈ stageSubmodule basis l i) (a : B.complex.X j) :
    act M i j n h z a ∈ stageSubmodule basis l n := by
  intro x hx
  rw [coordinates_action, hz x hx, map_zero, LinearMap.zero_apply]

private theorem stage_multiple (l : ℕ) (n : ℤ) (x : V.Index) (hx : level V x < l)
    (a : B.complex.X (n + -V.degree x)) :
    act M (V.degree x) (n + -V.degree x) n (by omega) (e x) a ∈ stageSubmodule basis l n := by
  intro y hy
  have neq : x ≠ y := by rintro rfl; omega
  rw [coordinates_single]
  change (DirectSum.lof k V.Index (fun t => B.complex.X (n + -V.degree t)) x a) y = _
  exact DFinsupp.single_eq_of_ne (Ne.symm neq)

private theorem stage_differential
    (triangular : ∀ x y, coordinates basis (V.degree x+1)
      ((M.complex ()).d (V.degree x) (V.degree x+1) (e x)) y ≠ 0 → level V y < level V x)
    (l : ℕ) (n : ℤ) (z : term M n) (hz : z ∈ stageSubmodule basis l n) :
    (M.complex ()).d n (n+1) z ∈ stageSubmodule basis l (n+1) := by
  let c := coordinates basis n z
  let F := ((M.complex ()).d n (n+1)).hom.comp (multiples e n)
  have eq : F c = (M.complex ()).d n (n+1) z := by
    change (M.complex ()).d n (n+1) ((coordinates basis n).symm (coordinates basis n z)) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [← eq, ← DirectSum.sum_support_of c, map_sum]
  apply Submodule.sum_mem
  intro x hx
  have hx' : level V x < l := by
    by_contra! hh
    exact (DFinsupp.mem_support_iff.mp hx) (hz x hh)
  change (M.complex ()).d n (n+1) (multiples e n (single B V n x (c x))) ∈ _
  rw [multiples_single, M.leibniz (a := ()) (b := ())]
  apply Submodule.add_mem
  · apply stage_action
    intro y hy
    by_contra hh
    have := triangular x y hh
    omega
  · rw [Units.smul_def]
    apply zsmul_mem
    have ha : V.degree x + (n + -V.degree x + 1) = n+1 := by omega
    have hb : n + -V.degree x + 1 = n+1 + -V.degree x := by omega
    let a : B.complex.X (n+1 + -V.degree x) :=
      (B.complex.XIsoOfEq hb).hom (B.complex.d (n + -V.degree x) (n + -V.degree x + 1) (c x))
    have reindexed (d j n : ℤ) (h : d+j=n) (w : term M d) (b : B.complex.X j) :
        act M d j n h w b =
          act M d (n + -d) n (by omega) w ((B.complex.XIsoOfEq (by omega : j = n + -d)).hom b) := by
      have q : j=n + -d := by omega
      cases q
      simp [HomologicalComplex.XIsoOfEq]
    rw [reindexed (V.degree x) _ (n+1) ha]
    exact stage_multiple basis l (n+1) x hx' a

variable (triangular : ∀ x y, coordinates basis (V.degree x+1)
  ((M.complex ()).d (V.degree x) (V.degree x+1) (e x)) y ≠ 0 → level V y < level V x)

private def stageDifferential (l : ℕ) (n : ℤ) :
    ModuleCat.of k (stageSubmodule basis l n) ⟶ ModuleCat.of k (stageSubmodule basis l (n+1)) :=
  ModuleCat.ofHom ((((M.complex ()).d n (n+1)).hom.comp (stageSubmodule basis l n).subtype).codRestrict
    (stageSubmodule basis l (n+1)) fun z => stage_differential basis triangular l n z z.property)

@[reducible] private def stageComplex (l : ℕ) : ModuleCochain.{u,v} k :=
  CochainComplex.of (fun n => ModuleCat.of k (stageSubmodule basis l n))
    (stageDifferential basis triangular l) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      change (M.complex ()).d (n+1) (n+1+1) ((M.complex ()).d n (n+1) z.val) = 0
      rw [← ModuleCat.comp_apply, d_comp_d]
      rfl)

@[simp] private theorem stageComplex_d (l : ℕ) (n : ℤ) (z : stageSubmodule basis l n) :
    ((stageComplex basis triangular l).d n (n+1) z).val = (M.complex ()).d n (n+1) z.val := by
  simp only [stageComplex, CochainComplex.of_d]
  rfl

private def stageAct (l : ℕ) (i j n : ℤ) (h : i+j=n) :
    stageSubmodule basis l i →ₗ[k] B.complex.X j →ₗ[k] stageSubmodule basis l n where
  toFun z := (act M i j n h z.val).codRestrict _ (stage_action basis l i j n h z z.property)
  map_add' x y := LinearMap.ext fun a => Subtype.ext (by
    exact LinearMap.congr_fun (map_add (act M i j n h) x.val y.val) a)
  map_smul' c x := LinearMap.ext fun a => Subtype.ext (by
    exact LinearMap.congr_fun (map_smul (act M i j n h) c x.val) a)

@[reducible] private def cellStage (l : ℕ) : B.Module where
  complex _ := stageComplex basis triangular l
  act i j n h := stageAct basis l i j n h
  act_id := by
    rintro ⟨⟩ i z
    exact Subtype.ext (M.act_id () i z.val)
  act_assoc := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩ i j l z a b
    exact Subtype.ext (M.act_assoc (a := ()) (b := ()) (c := ()) i j l z.val a b)
  leibniz := by
    rintro ⟨⟩ ⟨⟩ i j n h z a
    apply Subtype.ext
    change ((stageComplex basis triangular l).d n (n+1)
      (stageAct basis l i j n h z a)).val =
      act M (i+1) j (n+1) _ (((stageComplex basis triangular l).d i (i+1) z).val) a +
        i.negOnePow • act M i (j+1) (n+1) _ z.val (B.complex.d j (j+1) a)
    rw [stageComplex_d, stageComplex_d]
    exact M.leibniz (a := ()) (b := ()) i j n h z.val a

private def stageInto (l : ℕ) : cellStage basis triangular l ⟶ M :=
  Tensor.homOfDegrees (fun n => (stageSubmodule basis l n).subtype)
    (fun n z => (stageComplex_d basis triangular l n z).symm) (fun _ _ _ _ _ _ => rfl)

private abbrev Fresh (V : Variables.{v}) (l : ℕ) := {x : V.Index // level V x = l}

@[reducible] private def freshCells (l : ℕ) : SemiFree.CellFamily (cellStage basis triangular l) (Fresh V l) where
  object _ := ()
  degree x := V.degree x.val
  boundary x := ⟨(M.complex ()).d (V.degree x.val) (V.degree x.val+1) (e x.val), fun y hy => by
    by_contra hh
    have h := triangular x.val y hh
    rw [x.property] at h
    omega⟩
  closed x := by
    apply Subtype.ext
    rw [stageComplex_d]
    change (M.complex ()).d (V.degree x.val+1) (V.degree x.val+1+1)
      ((M.complex ()).d (V.degree x.val) (V.degree x.val+1) (e x.val)) = 0
    rw [← ModuleCat.comp_apply, d_comp_d]
    rfl

private abbrev FreshCoefficients (B : CommDGAlgebra.{u,v} k) (V : Variables.{v}) (l : ℕ) (n : ℤ) :=
  ⨁ x : Fresh V l, B.complex.X (n + -V.degree x.val)

private def includeFresh (B : CommDGAlgebra.{u,v} k) (V : Variables.{v}) (l : ℕ) (n : ℤ) :
    FreshCoefficients B V l n →ₗ[k] Coefficients B V n :=
  DirectSum.toModule k _ _ fun x => single B V n x.val

private theorem includeFresh_single (l : ℕ) (n : ℤ) [dec : DecidableEq (Fresh V l)] (x : Fresh V l)
    (a : B.complex.X (n + -V.degree x.val)) :
    includeFresh B V l n (DirectSum.lof k (Fresh V l)
      (fun t => B.complex.X (n + -V.degree t.val)) x a) = single B V n x.val a := by
  exact DirectSum.toModule_lof (R := k) (M := fun t : Fresh V l => B.complex.X (n + -V.degree t.val))
    (φ := fun t => single B V n t.val) x a

private theorem includeFresh_cell (l : ℕ) (n : ℤ) (x : Fresh V l)
    (a : B.complex.X (n + -V.degree x.val)) :
    includeFresh B V l n (SemiFree.summand (SemiFree.cells (freshCells basis triangular l)) () n x a) =
      single B V n x.val a := by
  unfold SemiFree.summand
  exact includeFresh_single (B := B) l n (dec := fun i j => Classical.propDecidable (i=j)) x a

private theorem includeFresh_apply (l : ℕ) (n : ℤ) (z : FreshCoefficients B V l n) (x : V.Index) :
    includeFresh B V l n z x = if hx : level V x = l then z ⟨x, hx⟩ else 0 := by
  by_cases hx : level V x = l
  · rw [dite_eq_left hx]
    let first := (DFinsupp.lapply (R := k) x).comp (includeFresh B V l n)
    let second : FreshCoefficients B V l n →ₗ[k] B.complex.X (n + -V.degree x) :=
      DFinsupp.lapply (⟨x, hx⟩ : Fresh V l)
    suffices eq : first = second from LinearMap.congr_fun eq z
    apply DirectSum.linearMap_ext
    intro y
    apply LinearMap.ext
    intro a
    change (includeFresh B V l n (DirectSum.lof k (Fresh V l)
      (fun t => B.complex.X (n + -V.degree t.val)) y a)) x =
      (DirectSum.lof k (Fresh V l) (fun t => B.complex.X (n + -V.degree t.val)) y a) ⟨x, hx⟩
    rw [includeFresh_single]
    by_cases hy : y.val = x
    · have eq : y = ⟨x, hx⟩ := Subtype.ext hy
      subst y
      change (DirectSum.lof k V.Index (fun t => B.complex.X (n + -V.degree t)) x a) x =
        (DirectSum.lof k (Fresh V l) (fun t => B.complex.X (n + -V.degree t.val))
          (⟨x, hx⟩ : Fresh V l) a) (⟨x, hx⟩ : Fresh V l)
      rw [DirectSum.lof_apply, DirectSum.lof_apply]
    · have hne : (⟨x, hx⟩ : Fresh V l) ≠ y := fun h => hy (congrArg Subtype.val h).symm
      change (DFinsupp.single (β := fun t : V.Index => B.complex.X (n + -V.degree t)) y.val a) x =
        (DFinsupp.single (β := fun t : Fresh V l => B.complex.X (n + -V.degree t.val)) y a)
          (⟨x, hx⟩ : Fresh V l)
      rw [DFinsupp.single_eq_of_ne (Ne.symm hy), DFinsupp.single_eq_of_ne hne]
  · rw [dite_eq_right hx]
    let first := (DFinsupp.lapply (R := k) x).comp (includeFresh B V l n)
    suffices eq : first = 0 from LinearMap.congr_fun eq z
    apply DirectSum.linearMap_ext
    intro y
    apply LinearMap.ext
    intro a
    change (includeFresh B V l n (DirectSum.lof k (Fresh V l)
      (fun t => B.complex.X (n + -V.degree t.val)) y a)) x = 0
    rw [includeFresh_single]
    have hne : x ≠ y.val := fun h => hx (h ▸ y.property)
    exact DFinsupp.single_eq_of_ne hne

private def attachDegree (l : ℕ) (n : ℤ) :
    stageSubmodule basis l n × FreshCoefficients B V l n →ₗ[k] stageSubmodule basis (l+1) n :=
  ((stageSubmodule basis l n).subtype.coprod ((multiples e n).comp (includeFresh B V l n))).codRestrict
    _ (fun z => by
      change (z.1.val + multiples e n (includeFresh B V l n z.2)) ∈ stageSubmodule basis (l+1) n
      apply Submodule.add_mem
      · exact stage_mono basis (Nat.le_succ l) n z.1.property
      · intro x hx
        change coordinates basis n ((coordinates basis n).symm (includeFresh B V l n z.2)) x = 0
        rw [LinearEquiv.apply_symm_apply, includeFresh_apply, dite_eq_right (by omega)])

private theorem attachDegree_coordinates (l : ℕ) (n : ℤ)
    (z : stageSubmodule basis l n × FreshCoefficients B V l n) :
    coordinates basis n (attachDegree basis l n z).val =
      coordinates basis n z.1.val + includeFresh B V l n z.2 := by
  change coordinates basis n (z.1.val + (coordinates basis n).symm (includeFresh B V l n z.2)) = _
  rw [map_add, LinearEquiv.apply_symm_apply]

private theorem attachDegree_bijective (l : ℕ) (n : ℤ) :
    Function.Bijective (attachDegree basis l n) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    have allzero (x : V.Index) : coordinates basis n z.1.val x +
        (if hx : level V x = l then z.2 ⟨x, hx⟩ else 0) = 0 := by
      have h := congrArg (fun w : stageSubmodule basis (l+1) n => coordinates basis n w.val x) hz
      rw [attachDegree_coordinates, DFinsupp.add_apply, includeFresh_apply] at h
      simpa only [Submodule.coe_zero, map_zero, DFinsupp.zero_apply] using h
    apply Prod.ext
    · apply Subtype.ext
      apply (coordinates basis n).injective
      apply DFinsupp.ext
      intro x
      by_cases hx : level V x = l
      · exact (z.1.property x (by omega)).trans (by simp)
      · simpa [hx] using allzero x
    · apply DFinsupp.ext
      intro x
      have h := allzero x.val
      rwa [dite_eq_left x.property, z.1.property x.val (by omega), zero_add] at h
  · intro z
    let c := coordinates basis n z.val
    let old := c.filter (fun x => level V x < l)
    let fresh : FreshCoefficients B V l n := c.subtypeDomain (fun x => level V x = l)
    let w : stageSubmodule basis l n :=
      ⟨(coordinates basis n).symm old, fun x hx => by
        rw [LinearEquiv.apply_symm_apply]
        exact DFinsupp.filter_apply_neg c (by omega)⟩
    refine ⟨(w, fresh), Subtype.ext ?_⟩
    apply (coordinates basis n).injective
    rw [attachDegree_coordinates]
    change coordinates basis n ((coordinates basis n).symm old) + includeFresh B V l n fresh = c
    rw [LinearEquiv.apply_symm_apply]
    apply DFinsupp.ext
    intro x
    rw [DFinsupp.add_apply, includeFresh_apply, DFinsupp.filter_apply]
    by_cases small : level V x < l
    · rw [ite_eq_left small, dite_eq_right (by omega), add_zero]
    · rw [ite_eq_right small, zero_add]
      by_cases freshHere : level V x = l
      · rw [dite_eq_left freshHere]
        rfl
      · rw [dite_eq_right freshHere]
        exact (z.property x (by omega)).symm

private theorem attachDegree_val (l : ℕ) (n : ℤ)
    (z : stageSubmodule basis l n × FreshCoefficients B V l n) :
    (attachDegree basis l n z).val = z.1.val + multiples e n (includeFresh B V l n z.2) := rfl

private theorem attachDegree_old (l : ℕ) (n : ℤ) (z : stageSubmodule basis l n) :
    (attachDegree basis l n (z, 0)).val = z.val := by
  rw [attachDegree_val, map_zero, map_zero, add_zero]

private theorem attachDegree_fresh (l : ℕ) (n : ℤ) (z : stageSubmodule basis l n)
    (x : Fresh V l) (a : B.complex.X (n + -V.degree x.val)) :
    (attachDegree basis l n
      (z, SemiFree.summand (SemiFree.cells (freshCells basis triangular l)) () n x a)).val =
      z.val + act M (V.degree x.val) (n + -V.degree x.val) n (by omega) (e x.val) a := by
  rw [attachDegree_val]
  change z.val + multiples e n (includeFresh B V l n
    (SemiFree.summand (SemiFree.cells (freshCells basis triangular l)) () n x a)) = _
  rw [includeFresh_cell, multiples_single]

omit [CharZero k] in
private theorem prodSumExt {ι : Type v} {X : Type v} {Y : ι → Type v} {Z : Type v}
    [AddCommGroup X] [Module k X] [∀ i, AddCommGroup (Y i)] [∀ i, Module k (Y i)]
    [AddCommGroup Z] [Module k Z]
    {L R : X × (⨁ i, Y i) →ₗ[k] Z}
    (old : ∀ z, L (z, 0) = R (z, 0))
    (fresh : ∀ i z, L (0, DirectSum.lof k ι Y i z) = R (0, DirectSum.lof k ι Y i z)) :
    L = R := by
  apply LinearMap.prod_ext
  · exact LinearMap.ext old
  · apply DirectSum.linearMap_ext
    intro i
    exact LinearMap.ext (fresh i)

private theorem attachDegree_d (l : ℕ) (n : ℤ)
    (z : term (SemiFree.attach (freshCells basis triangular l)) n) :
    attachDegree basis l (n+1)
        (((SemiFree.attach (freshCells basis triangular l)).complex ()).d n (n+1) z) =
      ((cellStage basis triangular (l+1)).complex ()).d n (n+1) (attachDegree basis l n z) := by
  apply Subtype.ext
  let C := freshCells basis triangular l
  let lhs := ((stageSubmodule basis (l+1) (n+1)).subtype.comp (attachDegree basis l (n+1))).comp
    (((SemiFree.attach C).complex ()).d n (n+1)).hom
  let rhs := ((stageSubmodule basis (l+1) (n+1)).subtype.comp
    (((cellStage basis triangular (l+1)).complex ()).d n (n+1)).hom).comp (attachDegree basis l n)
  suffices eq : lhs = rhs from LinearMap.congr_fun eq z
  apply prodSumExt
  · intro y
    change (attachDegree basis l (n+1) ((SemiFree.attachComplex C ()).d n (n+1) (y, 0))).val =
      ((stageComplex basis triangular (l+1)).d n (n+1) (attachDegree basis l n (y, 0))).val
    rw [SemiFree.attachComplex_d, map_zero, map_zero, add_zero, attachDegree_old]
    rw [stageComplex_d, stageComplex_d, attachDegree_old]
  · intro x a
    let S := SemiFree.cells C
    let y := SemiFree.summand S () n x a
    change (attachDegree basis l (n+1) ((SemiFree.attachComplex C ()).d n (n+1) (0, y))).val =
      ((stageComplex basis triangular (l+1)).d n (n+1) (attachDegree basis l n (0, y))).val
    rw [SemiFree.attachComplex_d, map_zero, zero_add, SemiFree.attachingMap_summand,
      SemiFree.directSum_d_summand, attachDegree_fresh basis triangular, stageComplex_d,
      attachDegree_fresh basis triangular]
    let p := V.degree x.val
    change act M (p+1) (n + -p) (n+1) _ ((M.complex ()).d p (p+1) (e x.val)) a +
      act M p (n+1 + -p) (n+1) _ (e x.val)
        (((-p).negOnePow • B.complex.d (n + -p) (n+1 + -p)) a) =
      (M.complex ()).d n (n+1) (0 + act M p (n + -p) n _ (e x.val) a)
    rw [zero_add, M.leibniz (a := ()) (b := ())]
    simp only [Int.negOnePow_neg, ModuleCat.hom_smul, LinearMap.smul_apply,
      LinearMap.map_smul_of_tower]
    have reindex (j t : ℤ) (h : j=t) (hj : p+j=n+1) (c : B.complex.X j) :
        act M p t (n+1) (by omega) (e x.val) ((B.complex.XIsoOfEq h).hom c) =
          act M p j (n+1) hj (e x.val) c := by
      cases h
      simp [HomologicalComplex.XIsoOfEq]
    -- The shifted coefficient differential uses a propositionally equal target index.
    have hp : n + -p + 1 = n+1 + -p := by omega
    have hd := CategoryTheory.congr_fun (B.complex.d_comp_XIsoOfEq_hom hp (n + -p)) a
    change (B.complex.XIsoOfEq hp).hom (B.complex.d (n + -p) (n + -p + 1) a) =
      B.complex.d (n + -p) (n+1 + -p) a at hd
    rw [← hd]
    congr 2
    exact reindex _ _ hp (by omega) _

private theorem attachDegree_act (l : ℕ) (i j n : ℤ) (h : i+j=n)
    (z : term (SemiFree.attach (freshCells basis triangular l)) i) (a : B.complex.X j) :
    attachDegree basis l n (act (SemiFree.attach (freshCells basis triangular l)) i j n h z a) =
      act (cellStage basis triangular (l+1)) i j n h (attachDegree basis l i z) a := by
  apply Subtype.ext
  let C := freshCells basis triangular l
  let lhs := ((stageSubmodule basis (l+1) n).subtype.comp (attachDegree basis l n)).comp
    ((act (SemiFree.attach C) i j n h).flip a)
  let rhs := ((stageSubmodule basis (l+1) n).subtype.comp
    ((act (cellStage basis triangular (l+1)) i j n h).flip a)).comp (attachDegree basis l i)
  suffices eq : lhs = rhs from LinearMap.congr_fun eq z
  apply prodSumExt
  · intro y
    change (attachDegree basis l n (act (cellStage basis triangular l) i j n h y a,
      SemiFree.sumAct (SemiFree.cells C) i j n h 0 a)).val =
      act M i j n h (attachDegree basis l i (y, 0)).val a
    rw [map_zero, LinearMap.zero_apply, attachDegree_old, attachDegree_old]
    rfl
  · intro x b
    let S := SemiFree.cells C
    let y := SemiFree.summand S () i x b
    change (attachDegree basis l n (act (cellStage basis triangular l) i j n h 0 a,
      SemiFree.sumAct S i j n h y a)).val =
      act M i j n h (attachDegree basis l i (0, y)).val a
    rw [map_zero, LinearMap.zero_apply, SemiFree.sumAct_summand, attachDegree_fresh basis triangular,
      attachDegree_fresh basis triangular]
    simp only [Submodule.coe_zero, zero_add]
    exact (act_assoc_at M (V.degree x.val) (i + -V.degree x.val) j i (n + -V.degree x.val) n
      (by omega) (by omega) h (e x.val) b a).symm

private def stageSuccessor (l : ℕ) :
    SemiFree.attach (freshCells basis triangular l) ≅ cellStage basis triangular (l+1) :=
  _root_.DerivedFormalization.DG.CoefficientLift.isoOfComponents
    (fun a n => by
      cases a
      exact LinearEquiv.ofBijective (attachDegree basis l n) (attachDegree_bijective basis l n))
    (by rintro ⟨⟩ n z; exact attachDegree_d basis triangular l n z)
    (by rintro ⟨⟩ ⟨⟩ i j n h z a; exact attachDegree_act basis triangular l i j n h z a)

private theorem stageSuccessor_apply (l : ℕ) (n : ℤ)
    (z : term (SemiFree.attach (freshCells basis triangular l)) n) :
    ((stageSuccessor basis triangular l).hom.app ()).f n z = attachDegree basis l n z := rfl

private def smallPresentation : SemiFree.Presentation M where
  stage := cellStage basis triangular
  bottom := by
    rintro ⟨⟩ n z
    apply Subtype.ext
    apply (coordinates basis n).injective
    apply DFinsupp.ext
    intro x
    exact (z.property x (Nat.zero_le _)).trans (by simp)
  index := Fresh V
  family := freshCells basis triangular
  successor := stageSuccessor basis triangular
  into := stageInto basis triangular
  compatible l := by
    apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change ((stageSuccessor basis triangular l).hom.app () |>.f n (z, 0)).val = z.val
    rw [stageSuccessor_apply, attachDegree_old]
  injective l := by
    rintro ⟨⟩ n
    exact Subtype.val_injective
  exhaustive := by
    rintro ⟨⟩ n z
    let c := coordinates basis n z
    refine ⟨c.support.sup (level V) + 1, ⟨z, ?_⟩, rfl⟩
    intro x hx
    by_contra hn
    have he : x ∈ c.support := DFinsupp.mem_support_iff.mpr hn
    have h := Finset.le_sup (f := level V) he
    omega

include basis triangular in
/-- A triangular right graded basis gives the countable cell presentation of
the given module with its original differential. -/
theorem cellPresentation_of_basis : HasCellPresentation e := by
  let F := smallPresentation basis triangular
  obtain ⟨extensions, he, hc⟩ := _root_.DerivedFormalization.DG.CellReindex.fromSmall F
  let G := CellReindex.indexedPresentation F extensions he
  refine ⟨G, fun _ => Equiv.refl _, fun _ _ => rfl, ?_⟩
  intro l x
  change Fresh V l at x
  let n := V.degree x.val
  let z : term (SemiFree.attach (freshCells basis triangular l)) n :=
    SemiFree.attachedGenerator (freshCells basis triangular l) x
  have hz : (extensions l).generator x = ((F.successor l).hom.app ()).f n z := by
    apply ((extensions l).coordinates () n).injective
    change (extensions l).coordinates () n (((extensions l).coordinates () n).symm
      (0, IndexedSemiFree.summand (IndexedSemiFree.cells (CellReindex.indexedFamily (F.family l)))
        () n x (SemiFree.generator (A := dgCat B) () n))) = _
    rw [LinearEquiv.apply_symm_apply, hc]
    have h := congrArg (fun b : SemiFree.attach (F.family l) ⟶ SemiFree.attach (F.family l) =>
      (b.app ()).f n z) (F.successor l).hom_inv_id
    exact h.symm
  apply heq_of_eq
  change ((F.into (l+1)).app ()).f n ((extensions l).generator x) = e x.val
  rw [hz]
  change (((stageSuccessor basis triangular l).hom.app ()).f n z).val = e x.val
  rw [stageSuccessor_apply, attachDegree_val]
  change 0 + multiples e n (includeFresh B V l n
    (SemiFree.summand (SemiFree.cells (freshCells basis triangular l)) () n x
      (SemiFree.generator (A := dgCat B) () n))) = _
  rw [zero_add, includeFresh_cell]
  exact multiples_freeGenerator e x.val

end CellPresentation

theorem semifreeBasis : SemifreeBasis.{u,v} := by
  intro k _ _ A P V f E O
  let basis := graded_basis E O
  have triangular := differential_coefficient_level basis
  exact ⟨basis, fun x => differential_symbol O _ _, triangular,
    cellPresentation_of_basis basis triangular⟩

section BaseChange

open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor regular)
variable {P B : CommDGAlgebra.{u,v} k} {V : Variables.{v}} {M : P.Module}
variable {e : ∀ x, term M (V.degree x)} (basis : IsGradedBasis e)
variable (g : P ⟶ B) (T : ModuleTensor.{u,v} k)

private abbrev changedGenerator (x : V.Index) : term (T.obj g M (regular B)) (V.degree x) :=
  T.tmul g (N := regular B) (V.degree x) 0 (V.degree x) (add_zero _) (e x) B.one

private theorem left_regular (i j n : ℤ) (h : i+j=n) (a : B.complex.X i) (b : B.complex.X j) :
    signedLeft (regular B) i j n h a b = B.mul i j n h a b :=
  (B.graded_comm i j n h a b).symm

private def scalarProduct (i j n : ℤ) (h : i+j=n) (b : B.complex.X j) :
    Coefficients P V i →ₗ[k] Coefficients B V n :=
  DirectSum.lmap fun x => ((B.mul (i + -V.degree x) j (n + -V.degree x) (by omega)).flip b).comp
    (g.chainMap.f (i + -V.degree x)).hom

@[reducible] private def tensorCoordinatesPair (i j n : ℤ) (h : i+j=n) :
    term M i →ₗ[k] B.complex.X j →ₗ[k] Coefficients B V n :=
  LinearMap.flip
    { toFun := fun b => (scalarProduct (V := V) g i j n h b).comp (coordinates basis i).toLinearMap
      map_add' := fun b b' => LinearMap.ext fun z => DFinsupp.ext fun x => by
        change B.mul _ j _ _ (g.chainMap.f _ (coordinates basis i z x)) (b+b') = _
        exact map_add _ _ _
      map_smul' := fun c b => LinearMap.ext fun z => DFinsupp.ext fun x => by
        change B.mul _ j _ _ (g.chainMap.f _ (coordinates basis i z x)) (c • b) = _
        exact map_smul _ _ _ }

private theorem tensorCoordinatesPair_apply (i j n : ℤ) (h : i+j=n) (z : term M i)
    (b : B.complex.X j) (x : V.Index) :
    tensorCoordinatesPair basis g i j n h z b x =
      B.mul (i + -V.degree x) j (n + -V.degree x) (by omega)
        (g.chainMap.f _ (coordinates basis i z x)) b := rfl

private theorem tensorCoordinatesPair_balanced (i l j n : ℤ) (h : i+l+j=n)
    (z : term M i) (a : P.complex.X l) (b : B.complex.X j) :
    tensorCoordinatesPair basis g (i+l) j n h (act M i l (i+l) rfl z a) b =
      tensorCoordinatesPair basis g i (l+j) n (by omega) z
        (signedLeft (regular B) l j (l+j) rfl (g.chainMap.f l a) b) := by
  apply DFinsupp.ext
  intro x
  rw [tensorCoordinatesPair_apply, tensorCoordinatesPair_apply, coordinates_action, g.map_mul, left_regular]
  exact act_assoc_at (regular B) (i + -V.degree x) l j ((i+l) + -V.degree x) (l+j)
    (n + -V.degree x) (by omega) rfl (by omega) _ _ _

private def tensorCoordinates (n : ℤ) :
    term (T.obj g M (regular B)) n →ₗ[k] Coefficients B V n :=
  (Tensor.liftDegree (f := g) (M := M) (N := regular B) (tensorCoordinatesPair basis g · · n ·)
    (fun i l j h z a b => tensorCoordinatesPair_balanced basis g i l j n h z a b)).comp
    (T.degree g M (regular B) n).symm.toLinearMap

private theorem tensorCoordinates_tmul (i j n : ℤ) (h : i+j=n) (z : term M i) (b : B.complex.X j) :
    tensorCoordinates basis g T n (T.tmul g (N := regular B) i j n h z b) =
      tensorCoordinatesPair basis g i j n h z b := by
  unfold tensorCoordinates
  simp only [LinearMap.comp_apply, ModuleTensor.tmul, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [Tensor.liftDegree_pure]

private theorem moduleTensor_linear_ext {Y : Type v} [AddCommGroup Y] [Module k Y]
    {n : ℤ} {L R : term (T.obj g M (regular B)) n →ₗ[k] Y}
    (h : ∀ (i j : ℤ) (h : i+j=n) (z : term M i) (b : B.complex.X j),
      L (T.tmul g (N := regular B) i j n h z b) = R (T.tmul g (N := regular B) i j n h z b)) : L = R := by
  have eq : L.comp (T.degree g M (regular B) n).toLinearMap =
      R.comp (T.degree g M (regular B) n).toLinearMap := by
    apply Tensor.pure_ext (f := g) (M := M) (N := regular B)
    exact h
  apply LinearMap.ext
  intro z
  obtain ⟨w, rfl⟩ := (T.degree g M (regular B) n).surjective z
  exact LinearMap.congr_fun eq w

private def tensorPair (i j n : ℤ) (h : i+j=n) :
    term M i →ₗ[k] B.complex.X j →ₗ[k] term (T.obj g M (regular B)) n :=
  (Tensor.pair (N := regular B) g i j n h).compr₂ (T.degree g M _ n).toLinearMap

variable (formulas : T.Formulas g (regular B))

include formulas in
private theorem tensor_unit_action (i j n : ℤ) (h : i+j=n) (z : term M i) (b : B.complex.X j) :
    act (T.obj g M (regular B)) i j n h (T.tmul g (N := regular B) i 0 i (add_zero _) z B.one) b =
      T.tmul g (N := regular B) i j n h z b := by
  rw [formulas.action M i 0 i j n (add_zero i) h z B.one b]
  have unit_mul (l : ℤ) (eq : 0+j=l) :
      T.tmul g (N := regular B) i l n (by omega) z (B.mul 0 j l eq B.one b) = T.tmul g (N := regular B) i j n h z b := by
    have hl : j=l := by omega
    cases hl
    rw [B.toDGAlgebra.id_comp (a := ()) (b := ()) j b]
  exact unit_mul (0+j) rfl

private theorem tensor_balance (i l j il lj n : ℤ) (hi : i+l=il) (hj : l+j=lj) (h : il+j=n)
    (z : term M i) (a : P.complex.X l) (b : B.complex.X j) :
    T.tmul g (N := regular B) il j n h (act M i l il hi z a) b =
      T.tmul g (N := regular B) i lj n (by omega) z (B.mul l j lj hj (g.chainMap.f l a) b) := by
  have eq := congrArg (T.degree g M (regular B) n)
    (Tensor.pure_balance (N := regular B) g i l j il lj n hi hj h z a b)
  rw [← left_regular]
  exact eq

private theorem scalarProduct_single (i j n : ℤ) (h : i+j=n) (b : B.complex.X j)
    (x : V.Index) (a : P.complex.X (i + -V.degree x)) :
    scalarProduct (V := V) g i j n h b (single P V i x a) =
      single B V n x (B.mul (i + -V.degree x) j (n + -V.degree x) (by omega) (g.chainMap.f _ a) b) := by
  unfold scalarProduct
  exact DirectSum.lmap_lof (R := k)
    (M := fun t : V.Index => P.complex.X (i + -V.degree t))
    (N := fun t : V.Index => B.complex.X (n + -V.degree t))
    (fun t => ((B.mul (i + -V.degree t) j (n + -V.degree t) (by omega)).flip b).comp
      (g.chainMap.f (i + -V.degree t)).hom) x a

include formulas in
private theorem multiples_scalarProduct (i j n : ℤ) (h : i+j=n) (z : Coefficients P V i) (b : B.complex.X j) :
    multiples (changedGenerator (e := e) g T) n (scalarProduct g i j n h b z) =
      T.tmul g (N := regular B) i j n h (multiples e i z) b := by
  suffices eq : (multiples (changedGenerator (e := e) g T) n).comp (scalarProduct g i j n h b) =
      ((tensorPair g T i j n h).flip b).comp (multiples e i) from LinearMap.congr_fun eq z
  apply DirectSum.linearMap_ext
  intro x
  apply LinearMap.ext
  intro a
  change multiples (changedGenerator (e := e) g T) n
      (scalarProduct g i j n h b (single P V i x a)) =
    T.tmul g (N := regular B) i j n h (multiples e i (single P V i x a)) b
  rw [scalarProduct_single, multiples_single, multiples_single]
  rw [tensor_unit_action g T formulas, tensor_balance g T]

private theorem tensorCoordinates_on_generator (n : ℤ) (x : V.Index) (b : B.complex.X (n + -V.degree x)) :
    tensorCoordinates basis g T n (T.tmul g (N := regular B) (V.degree x) (n + -V.degree x) n (by omega) (e x) b) =
      single B V n x b := by
  rw [tensorCoordinates_tmul]
  have coords : coordinates basis (V.degree x) (e x) = freeGenerator P V x := by
    rw [← multiples_freeGenerator e x]
    change coordinates basis (V.degree x) ((coordinates basis (V.degree x)).symm _) = _
    rw [LinearEquiv.apply_symm_apply]
  change scalarProduct g (V.degree x) (n + -V.degree x) n (by omega) b (coordinates basis (V.degree x) (e x)) = _
  rw [coords]
  unfold freeGenerator
  rw [scalarProduct_single]
  congr 1
  have unital (q j : ℤ) (hq : (0 : ℤ)=q) (b : B.complex.X j) :
      B.mul q j j (by omega) (g.chainMap.f q ((P.complex.XIsoOfEq hq).hom P.one)) b = b := by
    cases hq
    change B.mul 0 j j (zero_add j) (g.chainMap.f 0 P.one) b = b
    rw [g.map_one]
    exact B.toDGAlgebra.id_comp j b
  exact unital _ _ (by omega) b

include basis formulas in
private theorem changed_basis : IsGradedBasis (changedGenerator (e := e) g T) := by
  intro n
  let forward := multiples (changedGenerator (e := e) g T) n
  let backward := tensorCoordinates basis g T n
  have left : backward.comp forward = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro x
    apply LinearMap.ext
    intro b
    change tensorCoordinates basis g T n (multiples (changedGenerator (e := e) g T) n (single B V n x b)) =
      single B V n x b
    rw [multiples_single, tensor_unit_action g T formulas, tensorCoordinates_on_generator]
  have right : forward.comp backward = LinearMap.id := by
    apply moduleTensor_linear_ext (M := M) g T
    intro i j h z b
    change forward (tensorCoordinates basis g T n (T.tmul g (N := regular B) i j n h z b)) = _
    rw [tensorCoordinates_tmul]
    change multiples (changedGenerator (e := e) g T) n
        (scalarProduct g i j n h b (coordinates basis i z)) = _
    rw [multiples_scalarProduct g T formulas]
    change T.tmul g (N := regular B) i j n h ((coordinates basis i).symm (coordinates basis i z)) b = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have li : Function.LeftInverse backward forward := fun z => LinearMap.congr_fun left z
  have ri : Function.RightInverse backward forward := fun z => LinearMap.congr_fun right z
  exact ⟨li.injective, ri.surjective⟩

include formulas in
private theorem changed_multiples (n : ℤ) (a : Coefficients P V n) :
    multiples (changedGenerator (e := e) g T) n (changeCoefficients g V n a) =
      T.tmul g (N := regular B) n 0 n (add_zero n) (multiples e n a) B.one := by
  have eq : scalarProduct (V := V) g n 0 n (add_zero n) B.one = changeCoefficients g V n := by
    apply LinearMap.ext
    intro z
    apply DFinsupp.ext
    intro x
    change B.mul (n + -V.degree x) 0 (n + -V.degree x) (add_zero _) (g.chainMap.f _ (z x)) B.one =
      g.chainMap.f _ (z x)
    exact B.toDGAlgebra.comp_id _ _
  rw [← eq, multiples_scalarProduct g T formulas]

include formulas in
private theorem changed_differential (basis' : IsGradedBasis (changedGenerator (e := e) g T))
    (x : V.Index) :
    coordinates basis' (V.degree x+1) (((T.obj g M (regular B)).complex ()).d (V.degree x) (V.degree x+1)
      (changedGenerator (e := e) g T x)) =
      changeCoefficients g V (V.degree x+1) (coordinates basis (V.degree x+1)
        ((M.complex ()).d (V.degree x) (V.degree x+1) (e x))) := by
  apply (coordinates basis' (V.degree x+1)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change _ = multiples (changedGenerator (e := e) g T) (V.degree x+1) _
  rw [changed_multiples g T formulas]
  change _ = T.tmul g (N := regular B) (V.degree x+1) 0 (V.degree x+1) (add_zero _)
    ((coordinates basis (V.degree x+1)).symm (coordinates basis (V.degree x+1) _)) B.one
  rw [LinearEquiv.symm_apply_apply]
  rw [formulas.differential]
  have closed : B.complex.d 0 1 B.one = 0 := B.toDGAlgebra.d_id ()
  change _ + (V.degree x).negOnePow • T.tmul g (N := regular B) (V.degree x) 1 (V.degree x+1) rfl (e x)
    (B.complex.d 0 1 B.one) = _
  rw [closed]
  change _ + (V.degree x).negOnePow • tensorPair g T (V.degree x) 1 (V.degree x+1) rfl (e x) 0 = _
  simp only [map_zero, smul_zero, add_zero]

end BaseChange

theorem semifreeAfterBaseChange : SemifreeAfterBaseChange.{u,v} := by
  intro k _ _ T A P V f E O B g formulas
  dsimp only
  let basis := graded_basis E O
  let basis' := changed_basis basis g T formulas
  have differential := changed_differential basis g T formulas basis'
  have triangular (x y : V.Index) (h : coordinates basis' (V.degree x+1)
      (((T.obj g O.module (Specs.DerivedFormalization.Affine.Tensor.regular B)).complex ()).d
        (V.degree x) (V.degree x+1) (changedGenerator (e := generator E O) g T x)) y ≠ 0) :
      level V y < level V x := by
    apply differential_coefficient_level basis x y
    intro zero
    apply h
    rw [differential]
    change g.chainMap.f _ (coordinates basis (V.degree x+1)
      ((O.module.complex ()).d (V.degree x) (V.degree x+1) (generator E O x)) y) = 0
    rw [zero, map_zero]
  exact ⟨basis, basis', cellPresentation_of_basis basis' triangular,
    changed_multiples (e := generator E O) g T formulas, differential⟩


section CanonicalModels

variable {A P : NonpositiveCDGA.{u,v} k} {f : A ⟶ P}

/-- The concrete module of relative differentials is semifree. -/
theorem omega_isSemiFree (h : Semifree.IsSemifree A f) :
    RightDGModule.IsSemiFree (Kahler.omega (f : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra)) := by
  obtain ⟨_, ⟨E⟩⟩ := h
  obtain ⟨_, _, _, F, _⟩ := semifreeBasis E (Kahler.model f)
  exact ⟨F⟩

/-- The concrete balanced extension of the relative differentials is semifree
over the target algebra. -/
theorem baseChange_omega_isSemiFree (h : Semifree.IsSemifree A f)
    {B : CommDGAlgebra.{u,v} k} (g : P.toCommDGAlgebra ⟶ B) :
    RightDGModule.IsSemiFree
      ((Tensor.baseChange g).obj (Kahler.omega (f : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra))) := by
  obtain ⟨_, ⟨E⟩⟩ := h
  obtain ⟨_, _, ⟨F, _⟩, _, _⟩ :=
    semifreeAfterBaseChange (Tensor.moduleTensorModel k) E (Kahler.model f) g
      (Tensor.moduleTensor_formulas g (Specs.DerivedFormalization.Affine.Tensor.regular B))
  exact ⟨F⟩

end CanonicalModels

end
end DerivedFormalization.Affine.SemifreeDifferentials
