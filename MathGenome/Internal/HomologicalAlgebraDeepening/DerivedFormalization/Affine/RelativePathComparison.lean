import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.KahlerDifferentials
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.PolynomialPath
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeLifting
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.RelativePathComparison
import Batteries.Tactic.OpenPrivate

open CategoryTheory
open CochainComplex.HomComplex

universe u v

noncomputable section

namespace DerivedFormalization.Affine.RelativePathComparison

open Specs.DerivedFormalization.Affine.RelativePathComparison
open Specs.DerivedFormalization.Affine.PolynomialPath
  (AlgebraPathModel RelativePathModel ModulePathModel Coefficients mapCoefficients)
open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor act regular term restrict signedLeft)
open Specs.DerivedFormalization.DG.HomComplex
  (gradedHom component HomotopyEquation)
open Kahler

/-- Lift a pair of maps with the same augmentation to one relative polynomial path. -/
theorem relativePathLifting : RelativePathLifting.{u,v} := by
  intro k _ _ A P Q B aP aQ p q U V R f₀ f₁ hf hs hq h₀ h₁ hp₀ hp₁
  obtain ⟨g, ⟨g₀, g₁⟩, _⟩ := R.target_pullback P f₀ f₁ (hp₀.trans hp₁.symm)
  obtain ⟨b, _, hb⟩ := R.target_pullback A aQ aQ rfl
  have e₁ : aP ≫ g = b :=
    hb _ ⟨by rw [Category.assoc, g₀, h₀], by rw [Category.assoc, g₁, h₁]⟩
  have e₂ : (aQ ≫ R.constants) ≫ R.endpoints = b :=
    hb _ ⟨by simp only [Category.assoc, R.constant_first, Category.comp_id],
      by simp only [Category.assoc, R.constant_second, Category.comp_id]⟩
  obtain ⟨H, hH, hg⟩ := Semifree.exists_lift_of_surjective_quasiIso aP
    (aQ ≫ R.constants) b g R.endpoints hf e₁ e₂
    (R.trivial_fibration hs hq).1 (R.trivial_fibration hs hq).2
  have e₀ : H ≫ R.endpoints ≫ R.first = f₀ := by rw [← Category.assoc, hg, g₀]
  have e₁' : H ≫ R.endpoints ≫ R.second = f₁ := by rw [← Category.assoc, hg, g₁]
  refine ⟨H, hH, e₀, e₁', ?_⟩
  calc
    _ = (H ≫ R.endpoints ≫ R.first) ≫ q := by simp only [Category.assoc]
    _ = p := by rw [e₀, hp₀]

section Scalars

open Specs.DerivedFormalization.Affine.Tensor (act_assoc_at)

variable {k : Type u} [Field k] [CharZero k]
variable {A B C : CommDGAlgebra.{u,v} k} {f : A ⟶ B}
variable (T : ModuleTensor.{u,v} k)

private theorem signedLeft_regular (i j n : ℤ) (e : i+j=n)
    (a : B.complex.X i) (b : B.complex.X j) :
    signedLeft (regular B) i j n e a b = B.mul i j n e a b :=
  (B.graded_comm i j n e a b).symm

private theorem tensor_ext {M : A.Module} {n : ℤ} {V : Type*}
    [AddCommGroup V] [Module k V] {F G : term ((T.baseChange f).obj M) n →ₗ[k] V}
    (h : ∀ (i j : ℤ) (e : i+j=n) (x : term M i) (b : B.complex.X j),
      F (T.tmul f (N := regular B) i j n e x b) =
        G (T.tmul f (N := regular B) i j n e x b)) : F = G := by
  let E := T.degree f M (regular B) n
  have eq : F.comp E.toLinearMap = G.comp E.toLinearMap := Tensor.pure_ext h
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := E.surjective x
  exact LinearMap.congr_fun eq y

private def scalarExtendDegree {M : A.Module} {N : B.Module}
    (L : M ⟶ restrict f N) (n : ℤ) :
    term ((T.baseChange f).obj M) n →ₗ[k] term N n :=
  (Tensor.liftDegree (f := f) (M := M) (N := regular B)
    (fun i j h => (act N i j n h).comp ((L.app ()).f i).hom)
    (by
      intro i l j h x a b
      change act N (i+l) j n h ((L.app ()).f (i+l) (act M i l (i+l) rfl x a)) b =
        act N i (l+j) n (by omega) ((L.app ()).f i x)
          (signedLeft (regular B) l j (l+j) rfl (f.chainMap.f l a) b)
      rw [L.comm_act, signedLeft_regular]
      exact act_assoc_at N i l j (i+l) (l+j) n rfl rfl h _ _ _)).comp
    (T.degree f M (regular B) n).symm.toLinearMap

private theorem scalarExtendDegree_pure {M : A.Module} {N : B.Module}
    (L : M ⟶ restrict f N) (i j n : ℤ) (e : i+j=n) (x : term M i) (b : B.complex.X j) :
    scalarExtendDegree T L n (T.tmul f (N := regular B) i j n e x b) =
      act N i j n e ((L.app ()).f i x) b := by
  simp only [scalarExtendDegree, LinearMap.comp_apply, ModuleTensor.tmul,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [Tensor.liftDegree_pure]
  rfl

private def scalarExtend {M : A.Module} {N : B.Module}
    (formulas : T.Formulas f (regular B)) (L : M ⟶ restrict f N) :
    (T.baseChange f).obj M ⟶ N :=
  Tensor.homOfDegrees (scalarExtendDegree T L) (by
    intro n z
    suffices e : ((N.complex ()).d n (n+1)).hom.comp (scalarExtendDegree T L n) =
        (scalarExtendDegree T L (n+1)).comp
          ((((T.baseChange f).obj M).complex ()).d n (n+1)).hom by
      exact LinearMap.congr_fun e z
    apply tensor_ext T
    intro i j e x b
    simp only [LinearMap.comp_apply, scalarExtendDegree_pure,
      formulas.differential, map_add, Units.smul_def, map_zsmul]
    change (N.complex ()).d n (n+1) _ = _
    rw [N.leibniz (a := ()) (b := ())]
    have hx := CategoryTheory.congr_fun ((L.app ()).comm i (i+1)) x
    simp only [ModuleCat.comp_apply] at hx
    rw [← hx]
    rfl) (by
      intro n l q h z b
      suffices e : (scalarExtendDegree T L q).comp
          ((act ((T.baseChange f).obj M) n l q h).flip b) =
          ((act N n l q h).flip b).comp (scalarExtendDegree T L n) by
        exact LinearMap.congr_fun e z
      apply tensor_ext T
      intro i j e x y
      simp only [LinearMap.comp_apply, LinearMap.flip_apply, formulas.action,
        scalarExtendDegree_pure]
      exact (act_assoc_at N i j l n (j+l) q e rfl h _ y b).symm)

private theorem scalarExtend_pure {M : A.Module} {N : B.Module}
    (formulas : T.Formulas f (regular B)) (L : M ⟶ restrict f N)
    (i j n : ℤ) (e : i+j=n) (x : term M i) (b : B.complex.X j) :
    ((scalarExtend T formulas L).app ()).f n (T.tmul f (N := regular B) i j n e x b) =
      act N i j n e ((L.app ()).f i x) b :=
  scalarExtendDegree_pure T L i j n e x b

variable {M : A.Module}

private theorem unit_tensor_action (formulas : T.Formulas f (regular B))
    (i j n : ℤ) (e : i+j=n) (x : term M i) (b : B.complex.X j) :
    act ((T.baseChange f).obj M) i j n e
      (T.tmul f (N := regular B) i 0 i (add_zero i) x B.one) b =
      T.tmul f (N := regular B) i j n e x b := by
  rw [formulas.action]
  have h (l : ℤ) (el : 0+j=l) :
      T.tmul f (N := regular B) i l n (by omega) x (B.mul 0 j l el B.one b) =
        T.tmul f (N := regular B) i j n e x b := by
    obtain rfl : l = j := by omega
    rw [B.toDGAlgebra.id_comp]
  exact h (0+j) rfl

omit [CharZero k] in
private theorem symbol_commutes {X W : ModuleCochain.{u,v} k}
    (s : Cochain X W 0) (closed : δ 0 1 s = 0) (i : ℤ) (x : X.X i) :
    W.d i (i+1) (s.v i i (add_zero i) x) =
      s.v (i+1) (i+1) (add_zero (i+1)) (X.d i (i+1) x) := by
  have e := CategoryTheory.congr_fun
    (congrArg (fun D : Cochain X W 1 => D.v i (i+1) rfl) closed) x
  rw [δ_zero_cochain_v, Cochain.zero_v] at e
  change (((s.v i i (add_zero i) ≫ W.d i (i+1)) -
    (X.d i (i+1) ≫ s.v (i+1) (i+1) (add_zero (i+1)))).hom) x = 0 at e
  simpa only [ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, sub_eq_zero] using e

private theorem baseChangedSymbol_d {a : C ⟶ A} (O : DifferentialModel a)
    (formulas : T.Formulas f (regular B)) (i : ℤ) (x : A.complex.X i) :
    (((T.baseChange f).obj O.module).complex ()).d i (i+1) (baseChangedSymbol T f O i x) =
      baseChangedSymbol T f O (i+1) (A.complex.d i (i+1) x) := by
  change (((T.baseChange f).obj O.module).complex ()).d i (i+1)
    (T.tmul f (N := regular B) i 0 i (add_zero i) (value O.symbol i i (add_zero i) x) B.one) =
    T.tmul f (N := regular B) (i+1) 0 (i+1) _ _ B.one
  rw [formulas.differential,
    symbol_commutes _ O.closed, show ((regular B).complex ()).d 0 (0+1) B.one = 0 from
      B.toDGAlgebra.d_id ()]
  simp only [ModuleTensor.tmul, Specs.DerivedFormalization.Affine.Tensor.pure,
    Specs.DerivedFormalization.DG.BalancedTensor.tmul,
    Specs.DerivedFormalization.DG.BalancedTensor.rawTmul, TensorProduct.tmul_zero,
    map_zero, smul_zero, add_zero]

private theorem act_baseChangedSymbol {a : C ⟶ A} (O : DifferentialModel a)
    (formulas : T.Formulas f (regular B)) (i j n : ℤ) (e : i+j=n)
    (x : A.complex.X i) (b : B.complex.X j) :
    act ((T.baseChange f).obj O.module) i j n e (baseChangedSymbol T f O i x) b =
      T.tmul f (N := regular B) i j n e (value O.symbol i i (add_zero i) x) b :=
  unit_tensor_action T formulas i j n e _ b

private theorem baseChangedSymbol_mul {a : C ⟶ A} (O : DifferentialModel a)
    (formulas : T.Formulas f (regular B)) (i j n : ℤ) (e : i+j=n)
    (x : A.complex.X i) (y : A.complex.X j) :
    baseChangedSymbol T f O n (A.mul i j n e x y) =
      act ((T.baseChange f).obj O.module) i j n e
        (baseChangedSymbol T f O i x) (f.chainMap.f j y) +
      (i*j).negOnePow • act ((T.baseChange f).obj O.module) j i n (by omega)
        (baseChangedSymbol T f O j y) (f.chainMap.f i x) := by
  let E := T.degree f O.module (regular B) n
  rw [act_baseChangedSymbol T O formulas, act_baseChangedSymbol T O formulas]
  change E (Specs.DerivedFormalization.Affine.Tensor.pure f n 0 n (add_zero n)
      (value O.symbol n n (add_zero n) (A.mul i j n e x y)) B.one) =
    E (Specs.DerivedFormalization.Affine.Tensor.pure f i j n e
      (value O.symbol i i (add_zero i) x) (f.chainMap.f j y)) +
    (i*j).negOnePow • E (Specs.DerivedFormalization.Affine.Tensor.pure f j i n (by omega)
      (value O.symbol j j (add_zero j) y) (f.chainMap.f i x))
  rw [O.symbol.property.leibniz i j n i j n e (add_zero i) (add_zero j) (add_zero n),
    Tensor.pure_add_left, Units.smul_def, Tensor.pure_zsmul_left, map_add, map_zsmul]
  congr 2
  · have h := Tensor.pure_balance f (N := regular B) i j 0 n j n e (add_zero j) (add_zero n)
          (value O.symbol i i (add_zero i) x) y B.one
    rw [signedLeft_regular, B.toDGAlgebra.comp_id] at h
    exact h
  · have h := Tensor.pure_balance f (N := regular B) j i 0 n i n (by omega) (add_zero i)
        (add_zero n) (value O.symbol j j (add_zero j) y) x B.one
    rw [signedLeft_regular, B.toDGAlgebra.comp_id] at h
    exact congrArg E h

end Scalars

section Representation

open Specs.DerivedFormalization.DG.HomComplex (restrictedDifferential)

variable {k : Type u} [Field k] [CharZero k]
variable {A P : CommDGAlgebra.{u,v} k} {a : A ⟶ P}

private theorem representStrict (O : DifferentialModel a) (N : P.Module)
    (D : P.complex ⟶ N.complex ()) (dDeriv : IsDerivation a (Cochain.ofHom D)) :
    ∃ L : O.module ⟶ N, ∀ (i : ℤ) (x : P.complex.X i),
      (L.app ()).f i (value O.symbol i i (add_zero i) x) = D.f i x := by
  obtain ⟨G, hG, _⟩ := O.represents N 0 ⟨Cochain.ofHom D, dDeriv⟩
  have h₀ (i : ℤ) (x : P.complex.X i) :
      component G () i i (add_zero i) (value O.symbol i i (add_zero i) x) = D.f i x := by
    simpa only [value, Cochain.ofHom_v] using hG i i (add_zero i) x
  let E := restrictedDifferential O.module N 0 1 G
  have hE (i : ℤ) (x : P.complex.X i) :
      component E () i (i+1) rfl (value O.symbol i i (add_zero i) x) = 0 := by
    change (δ 0 1 (G.val ())).v i (i+1) rfl (value O.symbol i i (add_zero i) x) = 0
    rw [δ_zero_cochain_v]
    change (N.complex ()).d i (i+1)
        (component G () i i (add_zero i) (value O.symbol i i (add_zero i) x)) -
      component G () (i+1) (i+1) (add_zero (i+1))
        ((O.module.complex ()).d i (i+1) (value O.symbol i i (add_zero i) x)) = 0
    rw [symbol_commutes _ O.closed, h₀, h₀, sub_eq_zero]
    exact CategoryTheory.congr_fun (D.comm i (i+1)) x
  have hz : E = 0 := by
    obtain ⟨F, _, hF⟩ := O.represents N 1 0
    have eF : E = F := hF E (by
      intro i p h x
      subst p
      exact hE i x)
    have zF : (0 : gradedHom O.module N 1) = F := hF 0 (by
      dsimp only
      intro i p h x
      rfl)
    exact eF.trans zF.symm
  have hclosed : δ 0 1 (G.val ()) = 0 :=
    congrArg (fun H : gradedHom O.module N 1 => H.val ()) hz
  refine ⟨Tensor.homOfDegrees (fun i => (component G () i i (add_zero i)).hom)
    (symbol_commutes (G.val ()) hclosed)
    (fun i j n h x b => G.property (a := ()) (b := ()) i j n i n h
      (add_zero i) (add_zero n) x b), ?_⟩
  exact h₀

end Representation

section Coefficients

open Specs.DerivedFormalization.Affine.PolynomialPath (evaluate endpoint differential)
open PolynomialPath (convolve convolve_map_left convolve_map_right map_convolve convolve_add
  convolve_zsmul convolve_flip evaluate_mapCoefficients pathComplex pathComplex_d)

variable {k : Type u} [Field k] [CharZero k]

private theorem derivative_of_convolution {A Q B : CommDGAlgebra.{u,v} k}
    {aQ : A ⟶ Q} (q : Q ⟶ B) (T : ModuleTensor.{u,v} k) (O : DifferentialModel aQ)
    (F : T.Formulas q (regular B)) (i j n : ℤ) (h : i+j=n)
    (x : Coefficients (Q.complex.X i)) (y : Coefficients (Q.complex.X j)) :
    let M := (T.baseChange q).obj O.module
    mapCoefficients (baseChangedSymbol T q O n) (convolve (Q.mul i j n h) x y) =
      convolve (act M i j n h) (mapCoefficients (baseChangedSymbol T q O i) x)
        (mapCoefficients (q.chainMap.f j).hom y) +
      (i*j).negOnePow • convolve (act M j i n (by omega))
        (mapCoefficients (baseChangedSymbol T q O j) y) (mapCoefficients (q.chainMap.f i).hom x) := by
  dsimp only
  let M := (T.baseChange q).obj O.module
  let m₁ := ((act M i j n h).comp (baseChangedSymbol T q O i)).compl₂ (q.chainMap.f j).hom
  let m₂ := ((act M j i n (by omega)).comp (baseChangedSymbol T q O j)).compl₂
    (q.chainMap.f i).hom
  have hm : (Q.mul i j n h).compr₂ (baseChangedSymbol T q O n) =
      m₁ + ((i*j).negOnePow : ℤ) • m₂.flip := by
    ext x y
    exact baseChangedSymbol_mul T O F i j n h x y
  rw [map_convolve, hm, convolve_add, convolve_zsmul, convolve_flip]
  simp only [m₁, m₂, ← convolve_map_right, ← convolve_map_left, Units.smul_def]
  rfl

private def asPathCoordinates {X Y : ModuleCochain.{u,v} k}
    (e : ∀ i : ℤ, X.X i ≃ₗ[k] Specs.DerivedFormalization.Affine.PolynomialPath.term Y i)
    (h : ∀ (i : ℤ) (x : X.X i), e (i+1) (X.d i (i+1) x) =
      differential Y i (i+1) rfl (e i x)) :
    X ⟶ pathComplex Y :=
  CochainComplex.ofHom (fun i => ModuleCat.ofHom (e i).toLinearMap) (by
    intro i
    rw [pathComplex_d Y i (i+1) rfl]
    exact ModuleCat.hom_ext (LinearMap.ext fun x => (h i x).symm))

private def fromPathCoordinates {X Y : ModuleCochain.{u,v} k}
    (e : ∀ i : ℤ, X.X i ≃ₗ[k] Specs.DerivedFormalization.Affine.PolynomialPath.term Y i)
    (h : ∀ (i : ℤ) (x : X.X i), e (i+1) (X.d i (i+1) x) =
      differential Y i (i+1) rfl (e i x)) :
    pathComplex Y ⟶ X :=
  CochainComplex.ofHom (fun i => ModuleCat.ofHom (e i).symm.toLinearMap) (by
    intro i
    rw [pathComplex_d Y i (i+1) rfl]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change ↑(Specs.DerivedFormalization.Affine.PolynomialPath.term Y i) at z
    change X.d i (i+1) ((e i).symm z) = (e (i+1)).symm (differential Y i (i+1) rfl z)
    apply (e (i+1)).injective
    rw [h, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])

variable {A A' P Q B : NonpositiveCDGA.{u,v} k}
variable (a : A ⟶ A') (aP : A ⟶ P) (aQ : A' ⟶ Q) (p : P ⟶ B) (q : Q ⟶ B)
variable {U : AlgebraPathModel Q.toCommDGAlgebra} {V : AlgebraPathModel B.toCommDGAlgebra}
variable (R : RelativePathModel q U V) (H : P ⟶ R.truncated)

private abbrev includedPath : P.toCommDGAlgebra ⟶ U.obj :=
  (H : P.toCommDGAlgebra ⟶ R.truncated.toCommDGAlgebra) ≫
    R.includeTruncation ≫ R.includeRelative

private theorem includedPath_endpoint (i : ℤ) (x : P.complex.X i)
    (f : P ⟶ Q) (c : k)
    (hf : (f = H ≫ R.endpoints ≫ R.first ∧ c = 0) ∨
      (f = H ≫ R.endpoints ≫ R.second ∧ c = 1)) :
    evaluate c (U.coordinates i ((includedPath q R H).chainMap.f i x)).1 = f.chainMap.f i x := by
  change endpoint Q.complex c i (U.coordinates i ((includedPath q R H).chainMap.f i x)) = _
  rw [← U.evaluation_coordinates]
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have e := CategoryTheory.congr_fun
      (congrArg (fun f : R.truncated.complex ⟶ Q.complex => f.f i) R.first_eval)
      (H.chainMap.f i x)
    exact e.symm
  · have e := CategoryTheory.congr_fun
      (congrArg (fun f : R.truncated.complex ⟶ Q.complex => f.f i) R.second_eval)
      (H.chainMap.f i x)
    exact e.symm

private theorem includedPath_augmentation
    (hAug : H ≫ R.endpoints ≫ R.first ≫ q = p) (i : ℤ) (x : P.complex.X i) :
    let z := U.coordinates i ((includedPath q R H).chainMap.f i x)
    (mapCoefficients (q.chainMap.f i).hom z.1,
      mapCoefficients (q.chainMap.f (i-1)).hom z.2) =
        (Finsupp.single 0 (p.chainMap.f i x), 0) := by
  dsimp only
  let H' : P.toCommDGAlgebra ⟶ R.relative :=
    (H : P.toCommDGAlgebra ⟶ R.truncated.toCommDGAlgebra) ≫ R.includeTruncation
  let y := R.augmentRelative.chainMap.f i (H'.chainMap.f i x)
  have e := CategoryTheory.congr_fun
    (congrArg (fun g : R.relative ⟶ V.obj => g.chainMap.f i) R.relative_square)
    (H'.chainMap.f i x)
  have ez := congrArg (V.coordinates i) e
  change V.coordinates i (R.coefficientMap.chainMap.f i ((includedPath q R H).chainMap.f i x)) =
    V.coordinates i (V.constantMap.chainMap.f i y) at ez
  rw [R.map_coordinates, V.constant_coordinates] at ez
  change (_, _) = (Finsupp.single 0 y, 0) at ez
  have ey := congrArg (fun z : Specs.DerivedFormalization.Affine.PolynomialPath.term B.complex i =>
    evaluate (0 : k) z.1) ez
  change evaluate (0 : k) (mapCoefficients (q.chainMap.f i).hom
    (U.coordinates i ((includedPath q R H).chainMap.f i x)).1) =
      evaluate (0 : k) (Finsupp.single 0 y) at ey
  rw [evaluate_mapCoefficients, includedPath_endpoint q R H i x _ 0 (Or.inl ⟨rfl, rfl⟩),
    PolynomialPath.evaluate_single, pow_zero, one_smul] at ey
  have hp := CategoryTheory.congr_fun
    (congrArg (fun f : P ⟶ B => f.chainMap.f i) hAug) x
  change q.chainMap.f i ((H ≫ R.endpoints ≫ R.first).chainMap.f i x) = p.chainMap.f i x at hp
  have hy : y = p.chainMap.f i x := ey.symm.trans hp
  simpa only [hy] using ez

private theorem includedPath_relative (hBase : aP ≫ H = a ≫ aQ ≫ R.constants)
    (i : ℤ) (x : A.complex.X i) :
    U.coordinates i ((includedPath q R H).chainMap.f i (aP.chainMap.f i x)) =
      (Finsupp.single 0 (aQ.chainMap.f i (a.chainMap.f i x)), 0) := by
  let a' : A.toCommDGAlgebra ⟶ A'.toCommDGAlgebra := a
  let aQ' : A'.toCommDGAlgebra ⟶ Q.toCommDGAlgebra := aQ
  let c : Q.toCommDGAlgebra ⟶ R.truncated.toCommDGAlgebra := R.constants
  let H' : P.toCommDGAlgebra ⟶ R.truncated.toCommDGAlgebra := H
  let aP' : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra := aP
  have eq : aP' ≫ includedPath q R H = a' ≫ aQ' ≫ U.constantMap := by
    have e : c ≫ R.includeTruncation ≫ R.includeRelative = U.constantMap := by
      rw [← Category.assoc, R.constants_truncate, R.relative_constant]
    have base : aP' ≫ H' = a' ≫ aQ' ≫ c := hBase
    calc
      _ = (aP' ≫ H') ≫ (R.includeTruncation ≫ R.includeRelative) := by
        simp only [includedPath, Category.assoc, aP', H']
      _ = _ := by rw [base]; simp only [Category.assoc, e, a', aQ']
  have e := CategoryTheory.congr_fun (congrArg (fun f : A.toCommDGAlgebra ⟶ U.obj =>
    f.chainMap.f i) eq) x
  change (includedPath q R H).chainMap.f i (aP.chainMap.f i x) =
    U.constantMap.chainMap.f i (aQ.chainMap.f i (a.chainMap.f i x)) at e
  rw [e, U.constant_coordinates]
  rfl

end Coefficients

section PathDerivative

open private snd_zsmul from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.PolynomialPath

open PolynomialPath (pathMap convolve convolve_single_right mapCoefficients_single)

variable {k : Type u} [Field k] [CharZero k]
variable {A A' P Q B : NonpositiveCDGA.{u,v} k}
variable (a : A ⟶ A') (aP : A ⟶ P) {aQ : A' ⟶ Q} (p : P ⟶ B) (q : Q ⟶ B)
variable {U : AlgebraPathModel Q.toCommDGAlgebra} {V : AlgebraPathModel B.toCommDGAlgebra}
variable (R : RelativePathModel q U V) (H : P ⟶ R.truncated)
variable (T : ModuleTensor.{u,v} k)
variable (OQ : DifferentialModel (aQ : A'.toCommDGAlgebra ⟶ Q.toCommDGAlgebra))

local notation "p₀" => (p : P.toCommDGAlgebra ⟶ B.toCommDGAlgebra)
local notation "q₀" => (q : Q.toCommDGAlgebra ⟶ B.toCommDGAlgebra)

variable (fq : ModuleTensor.Formulas T
  (show Q.toCommDGAlgebra ⟶ B.toCommDGAlgebra from q) (regular B.toCommDGAlgebra))
variable (W : ModulePathModel (A := B.toCommDGAlgebra)
  ((ModuleTensor.baseChange T (show Q.toCommDGAlgebra ⟶ B.toCommDGAlgebra from q)).obj OQ.module))

private def coefficientSymbol : Q.complex ⟶ (((T.baseChange q₀).obj OQ.module).complex ()) :=
  CochainComplex.ofHom (fun i => ModuleCat.ofHom (baseChangedSymbol T q₀ OQ i))
    (fun i => ModuleCat.hom_ext (LinearMap.ext (baseChangedSymbol_d T OQ fq i)))

private def pathDerivative : P.complex ⟶ W.obj.complex () :=
  (includedPath q R H).chainMap ≫
    asPathCoordinates U.coordinates (fun i => U.d_coordinates i (i+1) rfl) ≫
    pathMap (coefficientSymbol q T OQ fq) ≫
    fromPathCoordinates W.coordinates (fun i => W.d_coordinates i (i+1) rfl)

private theorem pathDerivative_coordinates (i : ℤ) (x : P.complex.X i) :
    let z := U.coordinates i ((includedPath q R H).chainMap.f i x)
    W.coordinates i ((pathDerivative q R H T OQ fq W).f i x) =
      (mapCoefficients (baseChangedSymbol T q₀ OQ i) z.1,
        mapCoefficients (baseChangedSymbol T q₀ OQ (i-1)) z.2) := by
  dsimp only
  let z := U.coordinates i ((includedPath q R H).chainMap.f i x)
  change W.coordinates i ((W.coordinates i).symm
    (mapCoefficients (baseChangedSymbol T q₀ OQ i) z.1,
      mapCoefficients (baseChangedSymbol T q₀ OQ (i-1)) z.2)) = _
  exact (W.coordinates i).apply_symm_apply _

private theorem pathDerivative_leibniz
    (hAug : H ≫ R.endpoints ≫ R.first ≫ q = p)
    (i j n : ℤ) (e : i+j=n) (x : P.complex.X i) (y : P.complex.X j) :
    (pathDerivative q R H T OQ fq W).f n (P.mul i j n e x y) =
      act W.obj i j n e ((pathDerivative q R H T OQ fq W).f i x) (p.chainMap.f j y) +
      (i*j).negOnePow • act W.obj j i n (by omega)
        ((pathDerivative q R H T OQ fq W).f j y) (p.chainMap.f i x) := by
  let D := pathDerivative q R H T OQ fq W
  let hx := U.coordinates i ((includedPath q R H).chainMap.f i x)
  let hy := U.coordinates j ((includedPath q R H).chainMap.f j y)
  have ex := includedPath_augmentation p q R H hAug i x
  have ey := includedPath_augmentation p q R H hAug j y
  have ex₀ : mapCoefficients (q.chainMap.f i).hom hx.1 = Finsupp.single 0 (p.chainMap.f i x) :=
    congrArg Prod.fst ex
  have ex₁ : mapCoefficients (q.chainMap.f (i-1)).hom hx.2 = 0 := congrArg Prod.snd ex
  have ey₀ : mapCoefficients (q.chainMap.f j).hom hy.1 = Finsupp.single 0 (p.chainMap.f j y) :=
    congrArg Prod.fst ey
  have ey₁ : mapCoefficients (q.chainMap.f (j-1)).hom hy.2 = 0 := congrArg Prod.snd ey
  have hmul :
      U.coordinates n ((includedPath q R H).chainMap.f n (P.mul i j n e x y)) =
        (convolve (Q.mul i j n e) hx.1 hy.1,
          convolve (Q.mul i (j-1) (n-1) (by omega)) hx.1 hy.2 +
            j.negOnePow • convolve (Q.mul (i-1) j (n-1) (by omega)) hx.2 hy.1) := by
    rw [(includedPath q R H).map_mul, U.multiplication]
  have hdx : W.coordinates i (D.f i x) =
      (mapCoefficients (baseChangedSymbol T q₀ OQ i) hx.1,
       mapCoefficients (baseChangedSymbol T q₀ OQ (i-1)) hx.2) :=
    pathDerivative_coordinates q R H T OQ fq W i x
  have hdy : W.coordinates j (D.f j y) =
      (mapCoefficients (baseChangedSymbol T q₀ OQ j) hy.1,
       mapCoefficients (baseChangedSymbol T q₀ OQ (j-1)) hy.2) :=
    pathDerivative_coordinates q R H T OQ fq W j y
  apply (W.coordinates n).injective
  rw [pathDerivative_coordinates, hmul]
  simp only [map_add, Units.smul_def, map_zsmul]
  rw [W.action_coordinates, W.action_coordinates, hdx, hdy]
  dsimp only [Prod.fst, Prod.snd]
  apply Prod.ext
  · change mapCoefficients (baseChangedSymbol T q₀ OQ n) (convolve (Q.mul i j n e) hx.1 hy.1) = _
    rw [derivative_of_convolution q₀ T OQ fq, ex₀, ey₀,
      convolve_single_right, convolve_single_right]
    rfl
  · -- The image of each form coefficient under q is zero.
    change mapCoefficients (baseChangedSymbol T q₀ OQ (n-1))
        (convolve (Q.mul i (j-1) (n-1) (by omega)) hx.1 hy.2) +
      (j.negOnePow : ℤ) • mapCoefficients (baseChangedSymbol T q₀ OQ (n-1))
        (convolve (Q.mul (i-1) j (n-1) (by omega)) hx.2 hy.1) = _
    rw [derivative_of_convolution q₀ T OQ fq, derivative_of_convolution q₀ T OQ fq,
      ex₀, ex₁, ey₀, ey₁, convolve_single_right, convolve_single_right]
    simp only [map_zero, smul_zero, zero_add, add_zero, Units.smul_def]
    have sign : (i*(j-1)).negOnePow = (i*j).negOnePow * i.negOnePow := by
      rw [show i*(j-1) = i*j-i by ring, Int.negOnePow_sub]
    simp only [sign, Units.val_mul, Prod.snd_add, snd_zsmul, smul_smul]
    abel

private theorem pathDerivative_isDerivation
    (hBase : aP ≫ H = a ≫ aQ ≫ R.constants)
    (hAug : H ≫ R.endpoints ≫ R.first ≫ q = p) :
    IsDerivation (aP : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra)
      (M := restrict p₀ W.obj) (Cochain.ofHom (pathDerivative q R H T OQ fq W)) := by
  constructor
  · intro i j e x
    have ej : i=j := by omega
    cases ej
    rw [Cochain.ofHom_v]
    apply (W.coordinates i).injective
    rw [pathDerivative_coordinates, includedPath_relative a aP aQ q R H hBase,
      mapCoefficients_single, map_zero, map_zero]
    have hz : baseChangedSymbol T q₀ OQ i (aQ.chainMap.f i (a.chainMap.f i x)) = 0 := by
      change T.tmul q₀ (N := regular B.toCommDGAlgebra) i 0 i (add_zero i)
        (value OQ.symbol i i (add_zero i) (aQ.chainMap.f i (a.chainMap.f i x))) _ = 0
      rw [OQ.symbol.property.relative]
      simp only [ModuleTensor.tmul, Specs.DerivedFormalization.Affine.Tensor.pure,
        Specs.DerivedFormalization.DG.BalancedTensor.tmul,
        Specs.DerivedFormalization.DG.BalancedTensor.rawTmul, TensorProduct.zero_tmul, map_zero]
    rw [hz, Finsupp.single_zero]
    rfl
  · intro i j n ir jr nr e ei ej en x y
    have hi : i=ir := by omega
    have hj : j=jr := by omega
    have hn : n=nr := by omega
    cases hi
    cases hj
    cases hn
    simp only [Cochain.ofHom_v]
    exact pathDerivative_leibniz p q R H T OQ fq W hAug i j n e x y

end PathDerivative

section Integration

variable {k : Type u} [Field k] [CharZero k] {B : CommDGAlgebra.{u,v} k}
variable {M N L : B.Module}

private def precomposeHomotopy (F : M ⟶ N) (h : gradedHom N L (-1)) :
    gradedHom M L (-1) :=
  ⟨fun a => Cochain.mk fun i j e => (F.app a).f i ≫ component h a i j e, by
    rintro ⟨⟩ ⟨⟩ i j n ir nr e hi hn x b
    change component h () n nr hn ((F.app ()).f n (act M i j n e x b)) =
      act L ir j nr (by omega) (component h () i ir hi ((F.app ()).f i x)) b
    rw [F.comm_act]
    exact h.property (a := ()) (b := ()) i j n ir nr e hi hn _ b⟩

private theorem precomposeHomotopy_equation (F : M ⟶ N) (g₁ g₀ : N ⟶ L)
    (h : gradedHom N L (-1)) (hh : HomotopyEquation g₁ g₀ h) :
    HomotopyEquation (F ≫ g₁) (F ≫ g₀) (precomposeHomotopy F h) := by
  intro a i x
  change _ = (L.complex a).d (i-1) i (component h a i (i-1) (by omega) ((F.app a).f i x)) +
    component h a (i+1) i (by omega) ((F.app a).f (i+1) ((M.complex a).d i (i+1) x))
  have e := CategoryTheory.congr_fun ((F.app a).comm i (i+1)) x
  simp only [ModuleCat.comp_apply] at e
  rw [← e]
  exact hh a i ((F.app a).f i x)

end Integration

/-- Differentiate a relative path coefficientwise, then integrate the resulting
path of scalar-extended differential maps. -/
theorem pathToCotangentHomotopy : PathToCotangentHomotopy.{u,v} := by
  intro k _ _ A A' P Q B a aP aQ p q U V R H hBase hAug T OP OQ
  dsimp only
  intro fp fq W
  let p₀ : P.toCommDGAlgebra ⟶ B.toCommDGAlgebra := p
  let q₀ : Q.toCommDGAlgebra ⟶ B.toCommDGAlgebra := q
  let D := pathDerivative q R H T OQ fq W
  obtain ⟨L, hL⟩ := representStrict OP (restrict p₀ W.obj) D
    (pathDerivative_isDerivation a aP (aQ := aQ) p q R H T OQ fq W hBase hAug)
  let F := scalarExtend T fp L
  refine ⟨F, ?_, ?_, ?_⟩
  · intro i x
    change W.coordinates i ((F.app ()).f i
      (T.tmul p₀ (N := regular B.toCommDGAlgebra) i 0 i (add_zero i)
        (value OP.symbol i i (add_zero i) x) B.one)) = _
    rw [scalarExtend_pure, W.obj.act_id, hL]
    exact pathDerivative_coordinates q R H T OQ fq W i x
  · intro f c hf i j n e x b
    change ((W.evaluation c).app ()).f n ((F.app ()).f n
      (T.tmul p₀ (N := regular B.toCommDGAlgebra) i j n e
        (value OP.symbol i i (add_zero i) x) b)) = _
    rw [scalarExtend_pure, (W.evaluation c).comm_act, hL,
      W.evaluation_coordinates, pathDerivative_coordinates]
    change act _ i j n e
      (Specs.DerivedFormalization.Affine.PolynomialPath.evaluate c
        (mapCoefficients (baseChangedSymbol T q₀ OQ i)
          (U.coordinates i ((includedPath q R H).chainMap.f i x)).1)) b = _
    rw [PolynomialPath.evaluate_mapCoefficients, includedPath_endpoint q R H i x f c hf,
      act_baseChangedSymbol T OQ fq]
  · exact ⟨precomposeHomotopy F W.homotopy,
      precomposeHomotopy_equation F _ _ _ W.endpoints_homotopic, fun _ _ _ _ => rfl⟩

end DerivedFormalization.Affine.RelativePathComparison
