import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CotangentBaseChange
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.DerivedAffineBaseChange
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CotangentComplex
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits
open Specs.DerivedFormalization.Affine.CotangentBaseChange
open Specs.DerivedFormalization.Affine.Tensor (term act regular restrict restrictFunctor)
open DerivedFormalization.Affine.SemifreeDifferentials (generator)

universe u v

namespace DerivedFormalization.Affine.CotangentBaseChange

open private polynomial_induction from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeAlgebras
open private unit_tensor_action from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison
open private shuffle from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.Tensor

open private unitTensor unitTensor_apply bijective_of_basis
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CotangentComplex
open private isoOfDegreewiseBijective isoOfDegreewiseBijective_hom
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CellLift
open private tensorIsPushout from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.DerivedAffineBaseChange
open private coproductModel
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.TensorResolutionComparison

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {A P C Q B D A' P' D' : NonpositiveCDGA.{u,v} k}

private abbrev tensorModel (k : Type u) [Field k] [CharZero k] :
    Specs.DerivedFormalization.Affine.Tensor.ModuleTensor.{u,v} k := Tensor.moduleTensorModel k

local notation "T" => tensorModel k
local notation "Ω" => (fun {A P} (f : A ⟶ P) => Kahler.model f)
local notation "ι" => NonpositiveCDGA.toCommDGAlgebra
local notation "pure" => Specs.DerivedFormalization.Affine.Tensor.pure

private theorem identityModels : IdentityCotangentModels T Ω := by
  intro C Q q h
  exact ⟨Tensor.baseChangeId (Kahler.omega q), fun i j n h x y =>
    Tensor.baseChangeId_pure (Kahler.omega q) i j n h (symbol (Ω q) i x) y⟩

private theorem component_eq {X Y : NonpositiveCDGA.{u,v} k} {f g : X ⟶ Y}
    (e : f = g) (i : ℤ) (x : X.complex.X i) :
    f.chainMap.f i x = g.chainMap.f i x :=
  CategoryTheory.congr_fun (congrArg (fun t : X ⟶ Y => t.chainMap.f i) e) x

private def partialMap {f : A ⟶ P} {f' : A' ⟶ P'}
    (a : A ⟶ A') (p : P ⟶ P') (h : f ≫ p = a ≫ f') :
    (Ω f).module ⟶ restrict (p : ι P ⟶ ι P') (Ω f').module :=
  Kahler.descendStrict (Kahler.squareDerivation p a f' h) (Kahler.squareDerivation_closed p a f' h)

private theorem partialMap_symbol {f : A ⟶ P} {f' : A' ⟶ P'}
    (a : A ⟶ A') (p : P ⟶ P') (h : f ≫ p = a ≫ f') (i : ℤ) (x : P.complex.X i) :
    ((partialMap a p h).app ()).f i (symbol (Ω f) i x) =
      symbol (Ω f') i (p.chainMap.f i x) := by
  exact (Kahler.descendStrict_symbol (Kahler.squareDerivation p a f' h)
    (Kahler.squareDerivation_closed p a f' h) i x).trans
    (Kahler.squareDerivation_apply p a f' h i x)

set_option backward.isDefEq.respectTransparency false in
private theorem symbolMaps : SymbolMaps T Ω := by
  intro A P D A' P' D' f f' a p g g' d hp hg
  let N := (extend T g').obj (Ω f').module
  let U := unitTensor g' (Ω f').module (Tensor.moduleTensor_formulas g' (regular (ι D')))
  let L := partialMap a p hp ≫ (restrictFunctor (p : ι P ⟶ ι P')).map U
  let hL : (Ω f).module ⟶ restrict (g : ι P ⟶ ι D) (restrict (d : ι D ⟶ ι D') N) :=
    { app := L.app
      comm_act := by
        rintro ⟨⟩ ⟨⟩ i j n e x z
        change (L.app ()).f n (act (Ω f).module i j n e x z) =
          act N i j n e ((L.app ()).f i x) (d.chainMap.f j (g.chainMap.f j z))
        have eq : d.chainMap.f j (g.chainMap.f j z) = g'.chainMap.f j (p.chainMap.f j z) :=
          component_eq hg j z
        rw [eq]
        exact L.comm_act (a := ()) (b := ()) i j n e x z }
  let m := Kahler.extend (g : ι P ⟶ ι D) hL
  have hm : IsSymbolMap T (Ω f) (Ω f') g g' p d m := by
    intro i j n e x z
    refine (Kahler.extend_pure (g : ι P ⟶ ι D) hL i j n e (symbol (Ω f) i x) z).trans ?_
    change act N i j n e ((U.app ()).f i (((partialMap a p hp).app ()).f i
      (symbol (Ω f) i x))) (d.chainMap.f j z) = _
    rw [partialMap_symbol, unitTensor_apply]
    exact unit_tensor_action T (Tensor.moduleTensor_formulas g' (regular (ι D'))) i j n e
      (symbol (Ω f') i (p.chainMap.f i x)) (d.chainMap.f j z)
  refine ⟨m, hm, fun m' hm' => ?_⟩
  exact Kahler.comparison_ext (g : ι P ⟶ ι D) (fun i j n e x z =>
    (hm' i j n e x z).trans (hm i j n e x z).symm)

private theorem differentialNaturality : DifferentialNaturality T Ω := by
  intro A P C Q A' P' C' Q' f a p q f' a' p' q' _ _ α β γ d hf ha hp hq e e' he he' l hl
  let r := partialMap γ d hq
  refine ⟨r, partialMap_symbol γ d hq, ?_⟩
  apply Kahler.comparison_ext (p : ι P ⟶ ι Q)
  intro i j n h x y
  change (r.app ()).f n ((e.hom.app ()).f n (symbolTensor T (Ω f) p i j n h x y)) =
    (e'.hom.app ()).f n ((l.app ()).f n (symbolTensor T (Ω f) p i j n h x y))
  rw [he, hl, he', r.comm_act, partialMap_symbol]
  exact congrArg (fun w => act (Ω q').module i j n h (symbol (Ω q') i w) (d.chainMap.f j y))
    (component_eq hp i x)

private theorem differentialComparisons
    (presentation : ∀ {A P C Q : NonpositiveCDGA.{u,v} k} {f : A ⟶ P} {a : A ⟶ C}
      {p : P ⟶ Q} {q : C ⟶ Q}, PresentationBaseChange (f := f) (a := a) (p := p) (q := q)) :
    DifferentialComparisons (tensorModel.{u,v} k) Ω := by
  intro A P C Q f a p q H hs
  obtain ⟨V, ⟨E⟩⟩ := hs
  obtain ⟨E', _, hvar⟩ := presentation H V E
  let c := Kahler.comparison p a q H.w
  have hc : IsDifferentialComparison T (Ω f) (Ω q) p c :=
    Kahler.comparison_symbol p a q H.w
  obtain ⟨_, h₁, _, _, _⟩ := SemifreeDifferentials.semifreeAfterBaseChange T E (Ω f) p
    (Tensor.moduleTensor_formulas p (regular (ι Q)))
  have h₂ := SemifreeDifferentials.graded_basis E' (Ω q)
  have hgen (x : V.Index) : (c.app ()).f (V.degree x)
      (symbolTensor T (Ω f) p (V.degree x) 0 (V.degree x) (add_zero _)
        (E.component _ (Semifree.variableTerm A V x)) Q.one) = generator E' (Ω q) x := by
    change (c.app ()).f (V.degree x)
      (symbolTensor T (Ω f) p (V.degree x) 0 (V.degree x) (add_zero _)
        (E.component _ (Semifree.variableTerm A V x)) Q.one) =
      symbol (Ω q) (V.degree x) (E'.component _ (Semifree.variableTerm C V x))
    refine (hc (V.degree x) 0 (V.degree x) (add_zero _) _ Q.one).trans ?_
    exact ((Ω q).module.act_id (a := ()) (V.degree x) _).trans
      (congrArg (symbol (Ω q) (V.degree x)) (hvar x).symm)
  have hb (a : Unit) (n : ℤ) : Function.Bijective ((c.app a).f n) := by
    cases a
    exact bijective_of_basis h₁ h₂ c hgen n
  let e := isoOfDegreewiseBijective c hb
  have he : e.hom = c := isoOfDegreewiseBijective_hom c hb
  refine ⟨e, ?_, fun e' hc' => Iso.ext ?_⟩
  · intro i j n h x y
    exact (congrArg (fun m : (Tensor.baseChange (p : ι P ⟶ ι Q)).obj (Kahler.omega f) ⟶
      Kahler.omega q => (m.app ()).f n (symbolTensor T (Ω f) p i j n h x y)) he).trans
      (hc i j n h x y)
  rw [he]
  exact Kahler.comparison_ext (p : ι P ⟶ ι Q)
    (fun i j n h x y => (hc' i j n h x y).trans (hc i j n h x y).symm)

section Presentation

open Semifree

variable {f : A ⟶ P} {a : A ⟶ C} {V : Variables.{v}}

private def changePolynomial (a : A ⟶ C) (V : Variables.{v}) (n : ℤ) :
    Polynomial A V n →ₗ[k] Polynomial C V n :=
  DirectSum.lmap fun m => (a.chainMap.f (n - V.weight m.val)).hom

private theorem changePolynomial_term (n : ℤ) (m : V.Monomial)
    (x : A.complex.X (n - V.weight m.val)) :
    changePolynomial a V n (Semifree.term A V n m x) =
      Semifree.term C V n m (a.chainMap.f _ x) := by
  classical
  unfold changePolynomial Semifree.term
  rw [DirectSum.lmap_lof]

private theorem changePolynomial_homogeneousTerm (n : ℤ) (m : V.Monomial) {i : ℤ}
    (h : i + V.weight m.val = n) (x : A.complex.X i) :
    changePolynomial a V n (homogeneousTerm A V n m h x) =
      homogeneousTerm C V n m h (a.chainMap.f i x) := by
  unfold homogeneousTerm
  simp only [LinearMap.comp_apply, changePolynomial_term]
  have natural (j : ℤ) (e : i = j) :
      a.chainMap.f j (castDegree A.complex.X e x) =
        castDegree C.complex.X e (a.chainMap.f i x) := by cases e; rfl
  rw [natural]

private theorem changePolynomial_coefficient (n : ℤ) (x : A.complex.X n) :
    changePolynomial a V n (coefficient A V n x) =
      coefficient C V n (a.chainMap.f n x) :=
  changePolynomial_homogeneousTerm n V.constant (by simp) x

private theorem changePolynomial_variable (x : V.Index) :
    changePolynomial a V (V.degree x) (variableTerm A V x) = variableTerm C V x := by
  change changePolynomial a V _ (homogeneousTerm A V _ (V.singleton x) (r := 0)
      (by simp) A.one) = _
  rw [changePolynomial_homogeneousTerm, a.map_one]
  rfl

private theorem changePolynomial_mul (i j n : ℤ) (h : i+j=n)
    (x : Polynomial A V i) (y : Polynomial A V j) :
    changePolynomial a V n (polynomialMul A V i j n h x y) =
      polynomialMul C V i j n h (changePolynomial a V i x) (changePolynomial a V j y) := by
  classical
  induction x using polynomial_induction A V with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | single m x =>
    induction y using polynomial_induction A V with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | single p y =>
      rw [← homogeneousTerm_self A V i m, ← homogeneousTerm_self A V j p]
      rw [changePolynomial_homogeneousTerm, changePolynomial_homogeneousTerm]
      rw [polynomialMul_homogeneousTerm, polynomialMul_homogeneousTerm]
      split_ifs with hp
      · rw [LinearMap.map_smul_of_tower, changePolynomial_homogeneousTerm, a.map_mul]
      · exact map_zero _

private theorem changePolynomial_usesOnly {n : ℤ} {S : Set V.Index}
    {x : Polynomial A V n} (h : UsesOnly A V S x) :
    UsesOnly C V S (changePolynomial a V n x) := by
  intro m hm
  apply h m
  intro hz
  exact hm (by change a.chainMap.f _ (x m) = 0; rw [hz, map_zero])

private theorem algebraPure_ext {f : A ⟶ P} {a : A ⟶ C} {n : ℤ} {W : Type*}
    [AddCommGroup W] [Module k W] {F G : (Tensor.algebraTensor f a).complex.X n →ₗ[k] W}
    (h : ∀ i j (e : i+j=n) x y, F (Tensor.algebraPure f a i j n e x y) =
      G (Tensor.algebraPure f a i j n e x y)) : F = G :=
  Tensor.pure_ext (f := a) (M := restrict (f : ι A ⟶ ι P) (regular (ι P)))
    (N := regular (ι C)) h

set_option maxHeartbeats 1200000 in
private theorem tensorPresentation (E : StagedPresentation A V f) :
    ∃ E' : StagedPresentation C V ((coproductModel (k := k)).inr f a),
      E'.stages = E.stages ∧ ∀ x : V.Index,
        E'.component (V.degree x) (variableTerm C V x) =
          ((coproductModel (k := k)).inl f a).chainMap.f (V.degree x)
            (E.component (V.degree x) (variableTerm A V x)) := by
  classical
  let S := coproductModel (k := k)
  let Q := S.tensor f a
  let p : P ⟶ Q := S.inl f a
  let q : C ⟶ Q := S.inr f a
  let x (z : V.Index) := p.chainMap.f (V.degree z) (E.component _ (variableTerm A V z))
  obtain ⟨gl⟩ := gradedUniversalProperty C V (ι Q) (fun n => (q.chainMap.f n).hom)
    q.map_one q.map_mul x
  let G := gl.default
  let F (n : ℤ) : Polynomial C V n →ₗ[k] Q.complex.X n := G.component n
  have coeF (n : ℤ) (z : C.complex.X n) : F n (coefficient C V n z) = q.chainMap.f n z :=
    G.map_base n z
  have varF (z : V.Index) : F (V.degree z) (variableTerm C V z) = x z := G.map_var z
  have mulF (i j n : ℤ) (h : i+j=n) (y : Polynomial C V i) (z : Polynomial C V j) :
      F n (polynomialMul C V i j n h y z) = Q.mul i j n h (F i y) (F j z) :=
    G.map_mul i j n h y z
  have pF (n : ℤ) (z : Polynomial A V n) :
      F n (changePolynomial a V n z) = p.chainMap.f n (E.component n z) := by
    induction n, z using polynomial_generated A V with
    | zero n => simp
    | add n y z hy hz => simp only [map_add, hy, hz]
    | sign n s y hy => simp only [Units.smul_def, map_zsmul, hy]
    | base n y =>
      rw [changePolynomial_coefficient, coeF, E.map_base]
      have hbase : f ≫ p = a ≫ q := (S.formulas f a).base
      exact (component_eq hbase n y).symm
    | var y => rw [changePolynomial_variable, varF]
    | mul i j n h y z hy hz =>
      rw [changePolynomial_mul, mulF, E.map_mul, p.map_mul, hy, hz]
  let L (n : ℤ) : P.complex.X n →ₗ[k] Polynomial C V n :=
    (changePolynomial a V n).comp (E.component n).symm.toLinearMap
  have FL (n : ℤ) (z : P.complex.X n) : F n (L n z) = p.chainMap.f n z := by
    change F n (changePolynomial a V n ((E.component n).symm z)) = _
    rw [pF, LinearEquiv.apply_symm_apply]
  have Lb (n : ℤ) (z : A.complex.X n) :
      L n (f.chainMap.f n z) = coefficient C V n (a.chainMap.f n z) := by
    change changePolynomial a V n ((E.component n).symm (f.chainMap.f n z)) = _
    rw [← E.map_base, LinearEquiv.symm_apply_apply, changePolynomial_coefficient]
  have Lm (i j n : ℤ) (h : i+j=n) (y : P.complex.X i) (z : P.complex.X j) :
      L n (P.mul i j n h y z) = polynomialMul C V i j n h (L i y) (L j z) := by
    obtain ⟨y, rfl⟩ := (E.component i).surjective y
    obtain ⟨z, rfl⟩ := (E.component j).surjective z
    change changePolynomial a V n ((E.component n).symm (P.mul i j n h _ _)) = _
    rw [← E.map_mul, LinearEquiv.symm_apply_apply, changePolynomial_mul]
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  let R (n : ℤ) : Q.complex.X n →ₗ[k] Polynomial C V n :=
    Tensor.liftDegree (f := a) (M := restrict (f : ι A ⟶ ι P) (regular (ι P)))
      (N := regular (ι C))
      (fun i j h => ((polynomialMul C V i j n h).compl₂ (coefficient C V j)).comp (L i))
      (by
        intro i l j h y b z
        change polynomialMul C V (i+l) j n h (L (i+l) (P.mul i l (i+l) rfl y
          (f.chainMap.f l b))) (coefficient C V j z) =
          polynomialMul C V i (l+j) n (by omega) (L i y)
            (coefficient C V (l+j) (Specs.DerivedFormalization.Affine.Tensor.signedLeft
              (regular (ι C)) l j (l+j) rfl (a.chainMap.f l b) z))
        rw [Lm, Lb]
        have hs := (ι C).graded_comm l j (l+j) rfl (a.chainMap.f l b) z
        rw [show Specs.DerivedFormalization.Affine.Tensor.signedLeft (regular (ι C)) l j (l+j) rfl
          (a.chainMap.f l b) z = C.mul l j (l+j) rfl (a.chainMap.f l b) z from hs.symm,
          ← polynomialMul_coefficient]
        have hn : i+l+j = n := h
        subst n
        exact polynomialMul_assoc C V i l j _ _ _)
  have Rp (i j n : ℤ) (h : i+j=n) (y : P.complex.X i) (z : C.complex.X j) :
      R n (Tensor.algebraPure f a i j n h y z) =
        polynomialMul C V i j n h (L i y) (coefficient C V j z) := by
    unfold R
    exact Tensor.liftDegree_pure (f := (a : ι A ⟶ ι C))
      (M := restrict (f : ι A ⟶ ι P) (regular (ι P))) (N := regular (ι C)) _ _ i j h y z
  have FR (n : ℤ) : (F n).comp (R n) = LinearMap.id := by
    apply algebraPure_ext (f := f) (a := a)
    intro i j h y z
    change F n (R n (Tensor.algebraPure f a i j n h y z)) = _
    rw [Rp, mulF, FL, coeF]
    exact Tensor.algebraPure_factor f a i j n h y z
  have Rm (i j n : ℤ) (h : i+j=n) (y : Q.complex.X i) (z : Q.complex.X j) :
      R n (Q.mul i j n h y z) = polynomialMul C V i j n h (R i y) (R j z) := by
    have eq : (Q.mul i j n h).compr₂ (R n) =
        ((polynomialMul C V i j n h).comp (R i)).compl₂ (R j) := by
      apply algebraPure_ext (f := f) (a := a)
      intro b c hbc u v
      apply algebraPure_ext (f := f) (a := a)
      intro d e hde w v₂
      change R n (Tensor.algebraMul f a i j n h
          (Tensor.algebraPure f a b c i hbc u v) (Tensor.algebraPure f a d e j hde w v₂)) =
        polynomialMul C V i j n h (R i (Tensor.algebraPure f a b c i hbc u v))
          (R j (Tensor.algebraPure f a d e j hde w v₂))
      rw [Tensor.algebraMul_pure f a b c d e i j (b+d) (c+e) n hbc hde h rfl rfl]
      change R n ((c*d).negOnePow.val • Tensor.algebraPure f a (b+d) (c+e) n (by omega)
          (P.mul b d (b+d) rfl u w) (C.mul c e (c+e) rfl v v₂)) = _
      erw [map_zsmul, Rp, Lm, ← polynomialMul_coefficient, Rp, Rp]
      subst i j
      exact (shuffle (D := (polynomialGradedAlgebra C V).toCommDGAlgebra)
        b c d e n h (L b u) (coefficient C V c v) (L d w) (coefficient C V e v₂)).symm
    exact LinearMap.congr_fun (LinearMap.congr_fun eq y) z
  have RF (n : ℤ) (z : Polynomial C V n) : R n (F n z) = z := by
    induction n, z using polynomial_generated C V with
    | zero n => simp
    | add n y z hy hz => simp only [map_add, hy, hz]
    | sign n s y hy => simp only [Units.smul_def, map_zsmul, hy]
    | base n y =>
      rw [coeF]
      change R n (Tensor.algebraPure f a 0 n n (zero_add n) P.one y) = _
      rw [Rp]
      have hL : L 0 P.one = coefficient C V 0 C.one := by
        change L 0 (ι P).one = coefficient C V 0 (ι C).one
        rw [← f.map_one, Lb, a.map_one]
      rw [hL, polynomialMul_one_left]
    | var y =>
      rw [varF]
      change R _ (Tensor.algebraPure f a (V.degree y) 0 (V.degree y) (add_zero _)
        (E.component _ (variableTerm A V y)) C.one) = _
      rw [Rp, polynomialMul_one_right]
      change changePolynomial a V _ ((E.component _).symm (E.component _ (variableTerm A V y))) = _
      rw [LinearEquiv.symm_apply_apply, changePolynomial_variable]
    | mul i j n h y z hy hz => rw [mulF, Rm, hy, hz]
  let e (n : ℤ) : Polynomial C V n ≃ₗ[k] Q.complex.X n :=
    LinearEquiv.ofLinearMap (F n) (R n) (FR n) (LinearMap.ext (RF n))
  refine ⟨{ component := e
            map_one := (coeF 0 C.one).trans q.map_one
            map_mul := mulF
            map_base := coeF
            stages := E.stages
            earlier := ?_ }, rfl, varF⟩
  intro z
  let i := V.degree z
  let y := E.component i (variableTerm A V z)
  have hc : Q.complex.d i (i+1) (p.chainMap.f i y) =
      p.chainMap.f (i+1) (P.complex.d i (i+1) y) :=
    CategoryTheory.congr_fun (p.chainMap.comm i (i+1)) y
  change UsesOnly C V _ ((e (i+1)).symm (Q.complex.d i (i+1) (F i (variableTerm C V z))))
  rw [varF]
  change UsesOnly C V _ ((e (i+1)).symm (Q.complex.d i (i+1) (p.chainMap.f i y)))
  rw [hc, ← FL]
  change UsesOnly C V _ ((e (i+1)).symm (e (i+1) (L (i+1) (P.complex.d i (i+1) y))))
  rw [LinearEquiv.symm_apply_apply]
  exact changePolynomial_usesOnly (E.earlier z)

end Presentation

private theorem presentationBaseChange {f : A ⟶ P} {a : A ⟶ C} {p : P ⟶ Q} {q : C ⟶ Q} :
    PresentationBaseChange (f := f) (a := a) (p := p) (q := q) := by
  intro H V E
  let S := coproductModel (k := k)
  let H₀ := tensorIsPushout S f a
  obtain ⟨E₀, hstage, hvar⟩ := tensorPresentation (a := a) E
  let e := H₀.isoIsPushout _ _ H
  have hl : S.inl f a ≫ e.hom = p := H₀.inl_isoIsPushout_hom _ _ H
  have hr : S.inr f a ≫ e.hom = q := H₀.inr_isoIsPushout_hom _ _ H
  let c (n : ℤ) : (S.tensor f a).complex.X n ≃ₗ[k] Q.complex.X n :=
    ((NonpositiveCDGA.forgetComplex k ⋙
    HomologicalComplex.eval _ _ n).mapIso e).toLinearEquiv
  have hc (n : ℤ) (x : (S.tensor f a).complex.X n) : c n x = e.hom.chainMap.f n x := rfl
  let E' : Semifree.StagedPresentation C V q :=
    { component := fun n => (E₀.component n).trans (c n)
      map_one := by
        change c 0 (E₀.component 0 _) = Q.one
        rw [E₀.map_one, hc, e.hom.map_one]
      map_mul := by
        intro i j n hn x y
        change c n (E₀.component n _) = Q.mul i j n hn (c i _) (c j _)
        rw [E₀.map_mul, hc, hc, hc, e.hom.map_mul]
        rfl
      map_base := by
        intro i x
        change c i (E₀.component i _) = _
        rw [E₀.map_base, hc]
        exact component_eq hr i x
      stages := E₀.stages
      earlier := by
        intro x
        let n := V.degree x
        let z := E₀.component n (Semifree.variableTerm C V x)
        change Semifree.UsesOnly C V _ ((E₀.component (n+1)).symm ((c (n+1)).symm
          (Q.complex.d n (n+1) (c n z))))
        have h : Q.complex.d n (n+1) (c n z) =
            c (n+1) ((S.tensor f a).complex.d n (n+1) z) :=
          CategoryTheory.congr_fun (e.hom.chainMap.comm n (n+1)) z
        rw [h, LinearEquiv.symm_apply_apply]
        exact E₀.earlier x }
  refine ⟨E', hstage, fun x => ?_⟩
  change c (V.degree x) (E₀.component _ (Semifree.variableTerm C V x)) = _
  rw [hvar, hc]
  exact component_eq hl _ _

private theorem nestedSymbol_ext {f : A ⟶ P} (p : P ⟶ Q) (q : Q ⟶ D) {M : D.Module}
    {m m' : (extend T q).obj ((extend T p).obj (Ω f).module) ⟶ M}
    (h : ∀ (i j l n t : ℤ) (hn : i+j=n) (ht : n+l=t) (x : P.complex.X i)
        (b : Q.complex.X j) (c : D.complex.X l),
      (m.app ()).f t (pure q (N := regular (ι D)) n l t ht
        (symbolTensor T (Ω f) p i j n hn x b) c) =
      (m'.app ()).f t (pure q (N := regular (ι D)) n l t ht
        (symbolTensor T (Ω f) p i j n hn x b) c)) :
    m = m' := by
  let e := Tensor.baseChangeComp (p : ι P ⟶ ι Q) (q : ι Q ⟶ ι D) (Ω f).module
  apply (cancel_epi e.inv).mp
  apply Kahler.comparison_ext (p ≫ q : ι P ⟶ ι D)
  intro i j n hn x y
  let w := pure q (N := regular (ι D)) i j n hn
    (symbolTensor T (Ω f) p i 0 i (add_zero i) x Q.one) y
  have fw : (e.hom.app ()).f n w = symbolTensor T (Ω f) (p ≫ q) i j n hn x y := by
    have eq := Tensor.baseChangeComp_pure (p : ι P ⟶ ι Q) (q : ι Q ⟶ ι D) (Ω f).module
      i 0 j i n (add_zero i) hn (symbol (Ω f) i x) Q.one y
    change _ = _ at eq
    rw [q.map_one] at eq
    have u (l : ℤ) (hl : 0+j=l) :
        pure (p ≫ q : ι P ⟶ ι D) (N := regular (ι D)) i l n (by omega)
          (symbol (Ω f) i x) (D.mul 0 j l hl D.one y) =
        symbolTensor T (Ω f) (p ≫ q) i j n hn x y := by
      have h0 : l = j := by omega
      cases h0
      have hm : D.mul 0 j j (zero_add j) D.one y = y := (ι D).toDGAlgebra.id_comp j y
      exact congrArg (pure (p ≫ q : ι P ⟶ ι D) (N := regular (ι D)) i j n hn
        (symbol (Ω f) i x)) hm
    exact eq.trans (u (0+j) rfl)
  let L := (Tensor.baseChange (q : ι Q ⟶ ι D)).obj
    ((Tensor.baseChange (p : ι P ⟶ ι Q)).obj (Ω f).module)
  have bw := DFunLike.congr_fun
    (congrArg (fun g : L ⟶ L => ModuleCat.Hom.hom ((g.app ()).f n)) e.hom_inv_id) w
  change (e.inv.app ()).f n ((e.hom.app ()).f n w) = w at bw
  change (m.app ()).f n ((e.inv.app ()).f n _) = (m'.app ()).f n ((e.inv.app ()).f n _)
  have back := (congrArg (fun z => (e.inv.app ()).f n z) fw.symm).trans bw
  exact (congrArg (fun w => (m.app ()).f n w) back).trans
    ((h i 0 j i n (add_zero i) hn x Q.one y).trans (congrArg (fun w => (m'.app ()).f n w) back.symm))

set_option backward.isDefEq.respectTransparency false in
private theorem iteratedComparisons : IteratedComparisons (tensorModel.{u,v} k) Ω := by
  intro A P C Q D R f a p q b r s _ _ e e' e'' assoc he he' he'' hassoc
  apply nestedSymbol_ext p r
  intro i j l m n hm hn x y z
  change (e'.hom.app ()).f n (((extend T r).map e.hom).app () |>.f n
      (pure r (N := regular (ι R)) m l n hn (symbolTensor T (Ω f) p i j m hm x y) z)) =
    (e''.hom.app ()).f n ((assoc.hom.app ()).f n _)
  have hmap := Tensor.map_first_pure (r : ι Q ⟶ ι R) (N := regular (ι R)) e.hom
    m l n hn (symbolTensor T (Ω f) p i j m hm x y) z
  erw [hmap, he]
  have balance := Tensor.pure_balance (r : ι Q ⟶ ι R) (N := regular (ι R))
    i j l m (j+l) n hm rfl hn (symbol (Ω q) i (p.chainMap.f i x)) y z
  rw [show Specs.DerivedFormalization.Affine.Tensor.signedLeft (regular (ι R)) j l (j+l) rfl
       (r.chainMap.f j y) z = R.mul j l (j+l) rfl (r.chainMap.f j y) z from
       ((ι R).graded_comm j l (j+l) rfl (r.chainMap.f j y) z).symm] at balance
  erw [balance, he', hassoc, he'']
  rfl

private def baseChangeCongr (M : P.Module) {g g' : P ⟶ D} (h : g = g') :
    (extend T g).obj M ≅ (extend T g').obj M := by
  cases h
  exact Iso.refl _

private theorem baseChangeCongr_pure (M : P.Module) {g g' : P ⟶ D} (h : g = g')
    (i j n : ℤ) (e : i+j=n) (x : term M i) (y : D.complex.X j) :
    ((baseChangeCongr M h).hom.app ()).f n
      (pure g (N := regular (ι D)) i j n e x y) =
      pure g' (N := regular (ι D)) i j n e x y := by
  cases h
  rfl


private theorem iso_inv_apply {M N : D.Module} (e : M ≅ N) (n : ℤ) (z : term M n) :
    (e.inv.app ()).f n ((e.hom.app ()).f n z) = z :=
  DFunLike.congr_fun (congrArg (fun g : M ⟶ M => ModuleCat.Hom.hom ((g.app ()).f n)) e.hom_inv_id) z

private theorem baseChangeComp_one (p : P ⟶ Q) (q : Q ⟶ D) (M : P.Module)
    (i j n : ℤ) (hn : i+j=n) (x : term M i) (y : D.complex.X j) :
    ((Tensor.baseChangeComp (p : ι P ⟶ ι Q) (q : ι Q ⟶ ι D) M).hom.app ()).f n
      (pure q (N := regular (ι D)) i j n hn
        (pure p (N := regular (ι Q)) i 0 i (add_zero i) x Q.one) y) =
      pure (p ≫ q : ι P ⟶ ι D) (N := regular (ι D)) i j n hn x y := by
  refine (Tensor.baseChangeComp_pure (p : ι P ⟶ ι Q) (q : ι Q ⟶ ι D) M
    i 0 j i n (add_zero i) hn x Q.one y).trans ?_
  have e (l : ℤ) (h : 0+j=l) :
      pure (p ≫ q : ι P ⟶ ι D) (N := regular (ι D)) i l n (by omega) x
          ((ι D).mul 0 j l h (q.chainMap.f 0 (ι Q).one) y) =
        pure (p ≫ q : ι P ⟶ ι D) (N := regular (ι D)) i j n hn x y := by
    have h' : l = j := by omega
    cases h'
    rw [q.map_one]
    exact congrArg (pure (p ≫ q : ι P ⟶ ι D) (N := regular (ι D)) i j n hn x)
      ((ι D).toDGAlgebra.id_comp j y)
  exact e _ rfl

section FlatAssembly

variable (π : P ⟶ B) (b : B ⟶ D) (p : P ⟶ Q) (u : Q ⟶ D)
variable (w : π ≫ b = p ≫ u)
variable {M : P.Module} {N : Q.Module}
variable (c : (Tensor.baseChange (p : ι P ⟶ ι Q)).obj M ≅ N)

private def cotangentSquareIso :
    (extend T b).obj ((extend T π).obj M) ≅ (extend T u).obj N :=
  Tensor.baseChangeComp (π : ι P ⟶ ι B) (b : ι B ⟶ ι D) M ≪≫
    baseChangeCongr M w ≪≫
    (Tensor.baseChangeComp (p : ι P ⟶ ι Q) (u : ι Q ⟶ ι D) M).symm ≪≫ (extend T u).mapIso c

set_option maxHeartbeats 600000 in
private theorem cotangentSquareIso_pure
    (i j l m n : ℤ) (hm : i+j=m) (hn : m+l=n)
    (x : term M i) (y : B.complex.X j) (z : D.complex.X l) :
    ((cotangentSquareIso π b p u w c).hom.app ()).f n
      (pure b (N := regular (ι D)) m l n hn
        (pure π (N := regular (ι B)) i j m hm x y) z) =
      pure u (N := regular (ι D)) i (j+l) n (by omega)
        ((c.hom.app ()).f i (pure p (N := regular (ι Q)) i 0 i (add_zero i) x Q.one))
        (D.mul j l (j+l) rfl (b.chainMap.f j y) z) := by
  let e := Tensor.baseChangeComp (π : ι P ⟶ ι B) (b : ι B ⟶ ι D) M
  let e' := Tensor.baseChangeComp (p : ι P ⟶ ι Q) (u : ι Q ⟶ ι D) M
  let w' := baseChangeCongr M w
  let j' := (extend T u).map c.hom
  let a := D.mul j l (j+l) rfl (b.chainMap.f j y) z
  let x' := pure p (N := regular (ι Q)) i 0 i (add_zero i) x Q.one
  let z' := pure u (M := (Tensor.baseChange (p : ι P ⟶ ι Q)).obj M)
    (N := regular (ι D)) i (j+l) n (by omega) x' a
  have ehom := Tensor.baseChangeComp_pure (π : ι P ⟶ ι B) (b : ι B ⟶ ι D) M
    i j l m n hm hn x y z
  have wb : (w'.hom.app ()).f n (pure (π ≫ b : ι P ⟶ ι D) (N := regular (ι D)) i (j+l) n
      (by omega) x a) = pure (p ≫ u : ι P ⟶ ι D) (N := regular (ι D)) i (j+l) n
      (by omega) x a := baseChangeCongr_pure M w i (j+l) n (by omega) x a
  have eb := baseChangeComp_one p u M i (j+l) n (by omega) x a
  have einv : (e'.inv.app ()).f n (pure (p ≫ u : ι P ⟶ ι D) (N := regular (ι D))
      i (j+l) n (by omega) x a) = z' :=
    (congrArg (fun z => (e'.inv.app ()).f n z) eb.symm).trans (iso_inv_apply e' n z')
  change (j'.app ()).f n ((e'.inv.app ()).f n ((w'.hom.app ()).f n ((e.hom.app ()).f n _))) = _
  have eq := (congrArg (fun z => (w'.hom.app ()).f n z) ehom).trans wb
  have eq' := (congrArg (fun z => (e'.inv.app ()).f n z) eq).trans einv
  exact (congrArg (fun z => (j'.app ()).f n z) eq').trans
    (Tensor.map_first_pure (u : ι Q ⟶ ι D) (N := regular (ι D)) c.hom i (j+l) n (by omega) x' a)

end FlatAssembly

private theorem flatComparisonOfAugmentation {f : A ⟶ P} {g : A ⟶ B} {a : A ⟶ C}
    (π : P ⟶ B) (X : PushoutCocone f a) (Y : PushoutCocone g a) (u : X.pt ⟶ Y.pt)
    (hl : X.inl ≫ u = π ≫ Y.inl) (hr : X.inr ≫ u = Y.inr)
    (hp : IsPushout f a X.inl X.inr) (hs : Semifree.IsSemifree A f)
    (hsurj : NonpositiveCDGA.DegreewiseSurjective u)
    (hq : NonpositiveCDGA.IsQuasiIso u) :
    Nonempty (FlatComparison T Ω π X Y) := by
  obtain ⟨V, ⟨E⟩⟩ := hs
  obtain ⟨E', _, _⟩ := presentationBaseChange hp V E
  obtain ⟨c, hc, _⟩ := differentialComparisons (k := k)
    (fun {_ _ _ _ _ _ _ _} => presentationBaseChange) hp ⟨V, ⟨E⟩⟩
  refine ⟨{
    augmentation := u
    left := hl
    right := hr
    semifree := ⟨V, ⟨E'⟩⟩
    surjective := hsurj
    quasiIso := hq
    iso := cotangentSquareIso π Y.inl X.inl u hl.symm c
    onSymbols := ?_ }⟩
  intro i j l m n hm hn x y z
  refine (cotangentSquareIso_pure π Y.inl X.inl u hl.symm c
    i j l m n hm hn (symbol (Ω f) i x) y z).trans ?_
  have hsym : (c.hom.app ()).f i (symbolTensor T (Ω f) X.inl i 0 i (add_zero i) x X.pt.one) =
      symbol (Ω X.inr) i (X.inl.chainMap.f i x) :=
    (hc i 0 i (add_zero i) x X.pt.one).trans ((Ω X.inr).module.act_id (a := ()) i _)
  exact congrArg (fun v => pure u (N := regular (ι Y.pt)) i (j+l) n (by omega) v
    (Y.pt.mul j l (j+l) rfl (Y.inl.chainMap.f j y) z)) hsym

section OrdinaryTensor

open scoped TensorProduct
open NonpositiveCDGA (ordinary ordinaryMap)
open private ordinary_eq_zero from MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.NonpositiveAlgebras

variable {R S : CommAlgCat.{v} k}

private theorem ordinary_mul_zero_degree (x y : R) :
    (ordinary R).mul 0 0 0 rfl x y = x * y := rfl

@[instance_reducible] private def degreeModule (M : (ordinary R).Module) (n : ℤ) : Module R (term M n) where
  smul r x := act M n 0 n (add_zero n) x r
  one_smul x := M.act_id () n x
  mul_smul r s x := by
    change act M n 0 n (add_zero n) x (r*s) =
      act M n 0 n (add_zero n) (act M n 0 n (add_zero n) x s) r
    rw [mul_comm r s, ← ordinary_mul_zero_degree]
    exact (Specs.DerivedFormalization.Affine.Tensor.act_assoc_at M n 0 0 n 0 n
      (add_zero n) rfl (add_zero n) x s r).symm
  smul_zero r := by
    change act M n 0 n (add_zero n) 0 r = 0
    exact (LinearMap.congr_fun (map_zero (act M n 0 n (add_zero n))) r).trans
      (LinearMap.zero_apply _)
  smul_add r x y := by
    change act M n 0 n (add_zero n) (x+y) r = _
    simp only [map_add]
    rfl
  add_smul r s x := map_add (act M n 0 n (add_zero n) x) r s
  zero_smul x := map_zero (act M n 0 n (add_zero n) x)

attribute [local instance] degreeModule

private theorem degreeModule_algebraMap (M : (ordinary R).Module) (n : ℤ) (c : k)
    (x : term M n) : (algebraMap k R c) • x = c • x := by
  change act M n 0 n (add_zero n) x (algebraMap k R c) = _
  rw [Algebra.algebraMap_eq_smul_one]
  have eq : act M n 0 n (add_zero n) x (c • (1 : R)) =
      c • act M n 0 n (add_zero n) x (1 : R) :=
    (act M n 0 n (add_zero n) x).map_smul c ((ordinary R).one)
  refine eq.trans ?_
  exact congrArg (fun y : term M n => c • y) (M.act_id () n x)

private def ordinaryDegreeDifferential (M : (ordinary R).Module) (n m : ℤ) :
    term M n →ₗ[R] term M m where
  toFun := (M.complex ()).d n m
  map_add' := ((M.complex ()).d n m).hom.map_add
  map_smul' r x := by
    by_cases h : n+1=m
    swap
    · have hz : (M.complex ()).d n m = 0 := HomologicalComplex.shape _ _ _ h
      change (M.complex ()).d n m (r • x) = r • (M.complex ()).d n m x
      rw [hz]
      simp
    subst m
    change (M.complex ()).d n (n+1) (act M n 0 n (add_zero n) x r) =
      act M (n+1) 0 (n+1) (add_zero (n+1)) ((M.complex ()).d n (n+1) x) r
    refine (M.leibniz (a := ()) (b := ()) n 0 n (add_zero n) x r).trans ?_
    change _ + n.negOnePow • act M n 1 (n+1) rfl x ((ordinary R).complex.d 0 1 r) = _
    have h : (ordinary R).complex.d 0 1 r = 0 := ordinary_eq_zero R 1 (by decide) _
    have hz : act M n 1 (n+1) rfl x ((ordinary R).complex.d 0 1 r) = 0 :=
      (congrArg (act M n 1 (n+1) rfl x) h).trans (map_zero _)
    rw [hz, smul_zero, add_zero]

variable (a : R ⟶ S) [Algebra R S]
variable (ha : ∀ r, algebraMap R S r = a.hom r)

private abbrev flatModule := restrict (NonpositiveCDGA.ordinaryMap a :
    ι (ordinary R) ⟶ ι (ordinary S)) (regular (ι (ordinary S)))

include ha in
private theorem ordinarySignedLeft (r : R) (s : S) :
    Specs.DerivedFormalization.Affine.Tensor.signedLeft (flatModule a) 0 0 0 rfl r s =
      (r • s : S) := by
  change (0 : ℤ).negOnePow • (ordinary S).mul 0 0 0 rfl s (a.hom r) = _
  rw [Int.negOnePow_zero, one_smul, ordinary_mul_zero_degree, mul_comm, Algebra.smul_def, ha]

variable (M : (ordinary R).Module)

private abbrev ordinaryTensorDegree (S : CommAlgCat.{v} k) [Algebra R S] (n : ℤ) := term M n ⊗[R] S

private local instance ordinaryTensorScalars (n : ℤ) : Module k (ordinaryTensorDegree M S n) :=
  Module.compHom _ (algebraMap k R)

private theorem ordinary_tmul_smul_left (n : ℤ) (c : k) (x : term M n) (s : S) :
    (c • x) ⊗ₜ[R] s = c • (x ⊗ₜ[R] s : ordinaryTensorDegree M S n) := by
  change _ = (algebraMap k R c) • (x ⊗ₜ[R] s)
  exact (congrArg (fun z => z ⊗ₜ[R] s) (degreeModule_algebraMap M n c x).symm).trans
    (TensorProduct.smul_tmul' (R := R) (algebraMap k R c) x s).symm

include ha in
private theorem ordinary_tmul_smul_right (n : ℤ) (c : k) (x : term M n) (s : S) :
    x ⊗ₜ[R] (c • s) = c • (x ⊗ₜ[R] s : ordinaryTensorDegree M S n) := by
  have hs : (algebraMap k R c) • s = c • s := by
    rw [Algebra.smul_def, ha, a.hom.commutes]
    exact (Algebra.smul_def c s).symm
  change _ = (algebraMap k R c) • (x ⊗ₜ[R] s)
  exact (congrArg (fun y => x ⊗ₜ[R] y) hs.symm).trans
    (TensorProduct.tmul_smul (R := R) (algebraMap k R c) x s)

include ha

private def ordinaryPairZero (n : ℤ) :
    term M n →ₗ[k] S →ₗ[k] ordinaryTensorDegree M S n where
  toFun x := {
    toFun := fun s => x ⊗ₜ[R] s
    map_add' := TensorProduct.tmul_add x
    map_smul' := fun c s => ordinary_tmul_smul_right a ha M n c x s }
  map_add' x y := LinearMap.ext fun s => TensorProduct.add_tmul x y s
  map_smul' c x := LinearMap.ext fun s => ordinary_tmul_smul_left (S := S) M n c x s

private def ordinaryPair (i j n : ℤ) (h : i+j=n) :
    term M i →ₗ[k] term (flatModule a) j →ₗ[k] ordinaryTensorDegree M S n :=
  if z : j = 0 then by
    subst j
    have hi : i = n := by omega
    cases hi
    exact ordinaryPairZero a ha M i
  else 0

private theorem ordinaryPair_zero_degree (i : ℤ) (x : term M i) (s : S) :
    ordinaryPair a ha M i 0 i (add_zero i) x s = x ⊗ₜ[R] s := by
  simp only [ordinaryPair]
  rfl

private theorem ordinaryPair_off_degree (i j n : ℤ) (h : i+j=n) (hj : j ≠ 0)
    (x : term M i) (s : term (flatModule a) j) : ordinaryPair a ha M i j n h x s = 0 := by
  simp [ordinaryPair, hj]

private def ordinaryForward (n : ℤ) :
    term (Tensor.over M (flatModule a)) n →ₗ[k] ordinaryTensorDegree M S n :=
  Tensor.liftDegree (f := 𝟙 (ι (ordinary R))) (M := M) (N := flatModule a)
    (fun i j h => ordinaryPair a ha M i j n h) (by
      intro i l j h x r s
      by_cases hl : l = 0
      · subst l
        by_cases hj : j = 0
        · subst j
          have hn : n = i := by omega
          cases hn
          let r₀ : R := r
          let s₀ : S := s
          change ordinaryPair a ha M (n+0) 0 n _ (act M n 0 (n+0) rfl x r) s =
            ordinaryPair a ha M n (0+0) n _ x
              (Specs.DerivedFormalization.Affine.Tensor.signedLeft (flatModule a) 0 0 0 rfl r s)
          have e (p : ℤ) (hp : n+0=p) :
              ordinaryPair a ha M p 0 n (by omega) (act M n 0 p hp x r) s =
                (r₀ • x) ⊗ₜ[R] s₀ := by
            have hpi : p = n := by omega
            cases hpi
            exact ordinaryPair_zero_degree a ha M n _ s
          let t : S := Specs.DerivedFormalization.Affine.Tensor.signedLeft (flatModule a)
            0 0 0 rfl r s
          have ht : t = r₀ • s₀ := ordinarySignedLeft a ha r₀ s₀
          calc
            _ = (r₀ • x) ⊗ₜ[R] s₀ := e (n+0) rfl
            _ = x ⊗ₜ[R] (r₀ • s₀) := TensorProduct.smul_tmul r₀ x s₀
            _ = x ⊗ₜ[R] t := congrArg (fun y : S => x ⊗ₜ[R] y) ht.symm
            _ = _ := (ordinaryPair_zero_degree a ha M n x t).symm
        · rw [ordinaryPair_off_degree a ha M _ _ _ _ hj,
            ordinaryPair_off_degree a ha M _ _ _ _ (by omega)]
      · have hr : r = 0 := ordinary_eq_zero R l hl r
        subst r
        change ordinaryPair a ha M _ _ _ _ (act M i l (i+l) rfl x 0) s =
          ordinaryPair a ha M _ _ _ _ x (Specs.DerivedFormalization.Affine.Tensor.signedLeft
            (flatModule a) l j (l+j) rfl ((𝟙 (ι (ordinary R)) : _ ⟶ _).chainMap.f l 0) s)
        simp only [map_zero, LinearMap.zero_apply])

private theorem ordinaryForward_pure (i j n : ℤ) (h : i+j=n) (x : term M i)
    (s : term (flatModule a) j) :
    ordinaryForward a ha M n (pure (𝟙 (ι (ordinary R))) (N := flatModule a) i j n h x s) =
      ordinaryPair a ha M i j n h x s := by
  unfold ordinaryForward
  exact Tensor.liftDegree_pure (f := 𝟙 (ι (ordinary R))) (M := M) (N := flatModule a) _ _ i j h x s

private def ordinaryBackwardAdd (n : ℤ) :
    ordinaryTensorDegree M S n →+ term (Tensor.over M (flatModule a)) n :=
  let b := Tensor.pair (𝟙 (ι (ordinary R))) (M := M) (N := flatModule a) n 0 n (add_zero n)
  TensorProduct.liftAddHom (R := R) (M := term M n) (N := S)
    { toFun := fun x => (b x).toAddMonoidHom
      map_zero' := AddMonoidHom.ext fun s => LinearMap.congr_fun (map_zero b) s
      map_add' := fun x y => AddMonoidHom.ext fun s => LinearMap.congr_fun (map_add b x y) s }
    (by
      intro (r : R) x s
      have h := Tensor.pure_balance (𝟙 (ι (ordinary R))) (M := M) (N := flatModule a)
        n 0 0 n 0 n (add_zero n) rfl (add_zero n) x r s
      change pure (𝟙 (ι (ordinary R))) (N := flatModule a) n 0 n (add_zero n) (r • x) s =
        pure (𝟙 (ι (ordinary R))) (N := flatModule a) n 0 n (add_zero n) x _
      exact h.trans (congrArg (pure (𝟙 (ι (ordinary R))) (N := flatModule a)
        n 0 n (add_zero n) x) (ordinarySignedLeft a ha r s)))

private theorem ordinaryBackwardAdd_tmul (n : ℤ) (x : term M n) (s : S) :
    ordinaryBackwardAdd a ha M n (x ⊗ₜ[R] s) =
      pure (𝟙 (ι (ordinary R))) (N := flatModule a) n 0 n (add_zero n) x s := rfl

private def ordinaryBackward (n : ℤ) :
    ordinaryTensorDegree M S n →ₗ[k] term (Tensor.over M (flatModule a)) n :=
  { ordinaryBackwardAdd a ha M n with
    map_smul' := fun c w => by
      change ordinaryBackwardAdd a ha M n (c • w) = c • ordinaryBackwardAdd a ha M n w
      induction w using TensorProduct.inductionOn with
      | add x y hx hy => simp only [smul_add, map_add, hx, hy]
      | tmul x s =>
        rw [← ordinary_tmul_smul_left (S := S) M n c x s, ordinaryBackwardAdd_tmul,
          ordinaryBackwardAdd_tmul]
        exact LinearMap.congr_fun (map_smul
          (Tensor.pair (𝟙 (ι (ordinary R))) (M := M) (N := flatModule a) n 0 n (add_zero n)) c x) s }

private theorem ordinaryBackward_tmul (n : ℤ) (x : term M n) (s : S) :
    ordinaryBackward a ha M n (x ⊗ₜ[R] s) =
      pure (𝟙 (ι (ordinary R))) (N := flatModule a) n 0 n (add_zero n) x s := rfl

private def ordinaryTensorEquiv (n : ℤ) :
    term (Tensor.over M (flatModule a)) n ≃ₗ[k] ordinaryTensorDegree M S n :=
  LinearEquiv.ofLinearMap (ordinaryForward a ha M n) (ordinaryBackward a ha M n) (by
    apply LinearMap.ext
    intro w
    change ordinaryForward a ha M n (ordinaryBackward a ha M n w) = w
    induction w using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x s =>
      have h := ordinaryBackward_tmul a ha M n x s
      rw [h]
      exact (ordinaryForward_pure a ha M n 0 n (add_zero n) x s).trans
        (ordinaryPair_zero_degree a ha M n x s)) (by
    apply Tensor.pure_ext (f := 𝟙 (ι (ordinary R))) (M := M) (N := flatModule a)
    intro i j h x s
    change ordinaryBackward a ha M n (ordinaryForward a ha M n
      (pure (𝟙 (ι (ordinary R))) (N := flatModule a) i j n h x s)) =
      pure (𝟙 (ι (ordinary R))) (N := flatModule a) i j n h x s
    rw [ordinaryForward_pure]
    by_cases hj : j = 0
    · subst j
      have hn : n = i := by omega
      cases hn
      exact (congrArg (ordinaryBackward a ha M n) (ordinaryPair_zero_degree a ha M n x s)).trans
        (ordinaryBackward_tmul a ha M n x s)
    · erw [ordinaryPair_off_degree a ha M _ _ _ _ hj, ordinary_eq_zero S j hj s, map_zero]
      exact (map_zero (Tensor.pair (𝟙 (ι (ordinary R))) (M := M) (N := flatModule a)
        i j n h x)).symm)

private theorem ordinary_backward_d (n : ℤ) (w : ordinaryTensorDegree M S n) :
    Tensor.differential (Tensor.over M (flatModule a)) n (ordinaryBackward a ha M n w) =
      ordinaryBackward a ha M (n+1) ((ordinaryDegreeDifferential M n (n+1)).rTensor S w) := by
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x s =>
    have hl := ordinaryBackward_tmul a ha M n x s
    have hr := ordinaryBackward_tmul a ha M (n+1) (ordinaryDegreeDifferential M n (n+1) x) s
    rw [hl, LinearMap.rTensor_tmul, hr]
    refine (Tensor.d_pure_at (𝟙 (ι (ordinary R))) (M := M) (N := flatModule a)
      n 0 n (n+1) 1 (n+1) (add_zero n) rfl rfl rfl x s).trans ?_
    have h : ((flatModule a).complex ()).d 0 1 s = 0 := ordinary_eq_zero S 1 (by decide) _
    rw [h]
    change _ + n.negOnePow • Tensor.pair (𝟙 (ι (ordinary R))) (M := M) (N := flatModule a)
      n 1 (n+1) rfl x 0 = _
    simp only [map_zero, smul_zero, add_zero]
    rfl

private theorem ordinary_backward_d_at (n m : ℤ) (h : n+1=m) (w : ordinaryTensorDegree M S n) :
    (Tensor.over M (flatModule a) |>.complex ()).d n m (ordinaryBackward a ha M n w) =
      ordinaryBackward a ha M m ((ordinaryDegreeDifferential M n m).rTensor S w) := by
  subst m
  exact ordinary_backward_d a ha M n w

private theorem ordinary_tensor_kFlat [Module.Flat R S] : Tensor.KFlat (flatModule a) := by
  intro M hM ⟨⟩ n
  have hin (n : ℤ) : Function.Exact (ordinaryDegreeDifferential M (n-1) n)
      (ordinaryDegreeDifferential M n (n+1)) := by
    have h := hM () n
    rw [HomologicalComplex.exactAt_iff' _ (n-1) n (n+1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff] at h
    intro x
    change (M.complex ()).d n (n+1) x = 0 ↔ ∃ y, (M.complex ()).d (n-1) n y = x
    refine ⟨h x, ?_⟩
    rintro ⟨y, rfl⟩
    exact CategoryTheory.congr_fun ((M.complex ()).d_comp_d (n-1) n (n+1)) y
  have hout := Module.Flat.rTensor_exact S (hin n)
  rw [HomologicalComplex.exactAt_iff' _ (n-1) n (n+1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  let e := ordinaryTensorEquiv a ha M n
  have he (z : ordinaryTensorDegree M S n) : e.symm z = ordinaryBackward a ha M n z := rfl
  have eq : ordinaryBackward a ha M n (e x) = x := e.symm_apply_apply x
  have hzero : (ordinaryDegreeDifferential M n (n+1)).rTensor S (e x) = 0 := by
    apply (ordinaryTensorEquiv a ha M (n+1)).symm.injective
    change ordinaryBackward a ha M (n+1) _ = _
    rw [← ordinary_backward_d, eq, map_zero]
    exact hx
  obtain ⟨y, hy⟩ := (hout (e x)).mp hzero
  refine ⟨ordinaryBackward a ha M (n-1) y, ?_⟩
  change (Tensor.over M (flatModule a) |>.complex ()).d (n-1) n
    (ordinaryBackward a ha M (n-1) y) = x
  rw [ordinary_backward_d_at a ha M (n-1) n (by omega), hy, eq]

end OrdinaryTensor

section FlatPushout

open NonpositiveCDGA (ordinary ordinaryMap)
open private tensorMap tensorMap_induced tensorMap_first_quasiIso
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.TensorResolutionComparison

variable {f : A ⟶ P} {g : A ⟶ B} {a : A ⟶ C}

private theorem pushoutTensor_surjective (π : P ⟶ B) (hπ : f ≫ π = g)
    (h : NonpositiveCDGA.DegreewiseSurjective π) :
    NonpositiveCDGA.DegreewiseSurjective (tensorMap π (𝟙 C) hπ (Category.comp_id a)) := by
  intro n
  let d := tensorMap π (𝟙 C) hπ (Category.comp_id a)
  let L := (d.chainMap.f n).hom
  let U := LinearMap.range L
  have hz : U.mkQ = 0 := by
    apply algebraPure_ext (f := g) (a := a)
    intro i j e x y
    obtain ⟨z, hz⟩ := h i x
    change π.chainMap.f i z = x at hz
    have hgen : L (Tensor.algebraPure f a i j n e z y) = Tensor.algebraPure g a i j n e x y := by
      change d.chainMap.f n (Tensor.algebraPure f a i j n e z y) = _
      exact ((tensorMap_induced π (𝟙 C) hπ (Category.comp_id a)).tmul i j n e z y).trans
        (congrArg (fun w => Tensor.algebraPure g a i j n e w y) hz)
    have hm : Tensor.algebraPure g a i j n e x y ∈ U := ⟨_, hgen⟩
    change U.mkQ (Tensor.algebraPure g a i j n e x y) = 0
    exact (Submodule.Quotient.mk_eq_zero (p := U)).mpr hm
  intro x
  change x ∈ U
  exact (Submodule.Quotient.mk_eq_zero (p := U)).mp (DFunLike.congr_fun hz x)

private theorem pushoutFlatAugmentation (π : P ⟶ B) (hπ : f ≫ π = g)
    (hπs : NonpositiveCDGA.DegreewiseSurjective π) (hπq : NonpositiveCDGA.IsQuasiIso π)
    (hflat : OrdinaryFlat a)
    (X : PushoutCocone f a) (Y : PushoutCocone g a)
    (hX : IsPushout f a X.inl X.inr) (hY : IsPushout g a Y.inl Y.inr)
    (u : X.pt ⟶ Y.pt) (hl : X.inl ≫ u = π ≫ Y.inl) (hr : X.inr ≫ u = Y.inr) :
    NonpositiveCDGA.DegreewiseSurjective u ∧ NonpositiveCDGA.IsQuasiIso u := by
  obtain ⟨A₀, C₀, a₀, eA, eC, he, hflat⟩ := hflat
  let : Algebra A₀ C₀ := a₀.hom.toRingHom.toAlgebra
  let : Module.Flat A₀ C₀ := hflat
  let f₀ := eA.inv ≫ f
  let g₀ := eA.inv ≫ g
  let X₀ := tensorIsPushout (coproductModel (k := k)) f₀ (ordinaryMap a₀)
  let Y₀ := tensorIsPushout (coproductModel (k := k)) g₀ (ordinaryMap a₀)
  have he' : eA.inv ≫ a = ordinaryMap a₀ ≫ eC.inv := by
    rw [Iso.eq_comp_inv, Category.assoc, he, Iso.inv_hom_id_assoc]
  have hX' : IsPushout f₀ (ordinaryMap a₀) X.inl (eC.inv ≫ X.inr) := by
    apply hX.of_iso' eA.symm (Iso.refl _) eC.symm (Iso.refl _)
    · simp [f₀]
    · simpa using he'
    · simp
    · simp
  have hY' : IsPushout g₀ (ordinaryMap a₀) Y.inl (eC.inv ≫ Y.inr) := by
    apply hY.of_iso' eA.symm (Iso.refl _) eC.symm (Iso.refl _)
    · simp [g₀]
    · simpa using he'
    · simp
    · simp
  let iX := X₀.isoIsPushout _ _ hX'
  let iY := Y₀.isoIsPushout _ _ hY'
  have hπ₀ : f₀ ≫ π = g₀ := by simp [f₀, g₀, hπ]
  let u₀ := tensorMap π (𝟙 (ordinary C₀)) hπ₀ (Category.comp_id (ordinaryMap a₀))
  have hu₀ := tensorMap_induced π (𝟙 (ordinary C₀)) hπ₀ (Category.comp_id (ordinaryMap a₀))
  have e : iX.hom ≫ u = u₀ ≫ iY.hom := by
    apply X₀.hom_ext
    · rw [← Category.assoc, X₀.inl_isoIsPushout_hom _ _ hX', hl, ← Category.assoc, hu₀.inl,
        Category.assoc, Y₀.inl_isoIsPushout_hom _ _ hY']
    · rw [← Category.assoc, X₀.inr_isoIsPushout_hom _ _ hX', Category.assoc, hr,
        ← Category.assoc, hu₀.inr, Category.id_comp, Y₀.inr_isoIsPushout_hom _ _ hY']
  have hs₀ : NonpositiveCDGA.DegreewiseSurjective u₀ := pushoutTensor_surjective π hπ₀ hπs
  have hq₀ : NonpositiveCDGA.IsQuasiIso u₀ :=
    tensorMap_first_quasiIso π hπ₀ hπq (ordinary_tensor_kFlat a₀ (fun _ => rfl))
  constructor
  · intro n y
    let z := iY.inv.chainMap.f n y
    obtain ⟨w, hw⟩ := hs₀ n z
    change u₀.chainMap.f n w = z at hw
    refine ⟨iX.hom.chainMap.f n w, ?_⟩
    change u.chainMap.f n (iX.hom.chainMap.f n w) = y
    have eq := component_eq e n w
    change u.chainMap.f n (iX.hom.chainMap.f n w) = iY.hom.chainMap.f n (u₀.chainMap.f n w) at eq
    rw [eq, hw]
    exact component_eq iY.inv_hom_id n y
  · let K := NonpositiveCDGA.forgetComplex k
    change QuasiIso (K.map u)
    have he : K.map iX.hom ≫ K.map u = K.map u₀ ≫ K.map iY.hom := by
      simpa only [Functor.map_comp] using congrArg K.map e
    have hq : QuasiIso (K.map u₀) := hq₀
    apply (quasiIso_iff_comp_left (K.map iX.hom) (K.map u)).1
    rw [he]
    exact quasiIso_comp _ _

private theorem flatComparisons : FlatComparisons (tensorModel.{u,v} k) Ω := by
  intro A P B C f g a π hπ hs hπs hπq ha X Y hX hY
  have hx := IsPushout.of_isColimit hX.some
  have hy := IsPushout.of_isColimit hY.some
  have comm : f ≫ (π ≫ Y.inl) = a ≫ Y.inr := by rw [← Category.assoc, hπ, hy.w]
  obtain ⟨u, hl, hr⟩ := hx.exists_desc (π ≫ Y.inl) Y.inr comm
  obtain ⟨hu, hq⟩ := pushoutFlatAugmentation π hπ hπs hπq ha X Y hx hy u hl hr
  exact flatComparisonOfAugmentation π X Y u hl hr hx hs hu hq

end FlatPushout

section Naturality

set_option maxHeartbeats 1200000 in
private theorem flatNormalizedSymbol {f : A ⟶ P} {g : A ⟶ B} {a : A ⟶ C}
    {π : P ⟶ B} {X : PushoutCocone f a} {Y : PushoutCocone g a}
    (F : FlatComparison T Ω π X Y)
    (e : (extend T Y.inl).obj ((extend T π).obj (Ω f).module) ≅
      (extend T (π ≫ Y.inl)).obj (Ω f).module)
    (he : IsAssociator T π Y.inl (Ω f).module e) (i j n : ℤ) (h : i+j=n)
    (x : P.complex.X i) (y : Y.pt.complex.X j) :
    ((e.inv ≫ F.iso.hom).app ()).f n (symbolTensor T (Ω f) (π ≫ Y.inl) i j n h x y) =
      symbolTensor T (Ω X.inr) F.augmentation i j n h (X.inl.chainMap.f i x) y := by
  let w := pure Y.inl (N := regular (ι Y.pt)) i j n h
    (symbolTensor T (Ω f) π i 0 i (add_zero i) x B.one) y
  have mulOne (l : ℤ) (hl : 0+j=l) :
      Y.pt.mul 0 j l hl (Y.inl.chainMap.f 0 B.one) y =
        Semifree.castDegree Y.pt.complex.X (show j = l by omega) y := by
    have eq : l = j := by omega
    cases eq
    change (ι Y.pt).mul 0 j j (zero_add j) (Y.inl.chainMap.f 0 (ι B).one) y = _
    rw [Y.inl.map_one]
    exact (ι Y.pt).toDGAlgebra.id_comp j y
  have fw : (e.hom.app ()).f n w = symbolTensor T (Ω f) (π ≫ Y.inl) i j n h x y := by
    refine (he i 0 j i n (add_zero i) h (symbol (Ω f) i x) B.one y).trans ?_
    have eq (l : ℤ) (hl : 0+j=l) :
        symbolTensor T (Ω f) (π ≫ Y.inl) i l n (by omega) x
            (Y.pt.mul 0 j l hl (Y.inl.chainMap.f 0 B.one) y) =
          symbolTensor T (Ω f) (π ≫ Y.inl) i j n h x y := by
      rw [mulOne]
      have e : l = j := by omega
      cases e
      rfl
    exact eq (0+j) rfl
  have fw' : (F.iso.hom.app ()).f n w =
      symbolTensor T (Ω X.inr) F.augmentation i j n h (X.inl.chainMap.f i x) y := by
    refine (F.onSymbols i 0 j i n (add_zero i) h x B.one y).trans ?_
    have eq (l : ℤ) (hl : 0+j=l) :
        symbolTensor T (Ω X.inr) F.augmentation i l n (by omega) (X.inl.chainMap.f i x)
            (Y.pt.mul 0 j l hl (Y.inl.chainMap.f 0 B.one) y) =
          symbolTensor T (Ω X.inr) F.augmentation i j n h (X.inl.chainMap.f i x) y := by
      rw [mulOne]
      have e : l = j := by omega
      cases e
      rfl
    exact eq (0+j) rfl
  let L := (extend T Y.inl).obj ((extend T π).obj (Ω f).module)
  have bw := DFunLike.congr_fun
    (congrArg (fun g : L ⟶ L => ModuleCat.Hom.hom ((g.app ()).f n)) e.hom_inv_id) w
  change (e.inv.app ()).f n ((e.hom.app ()).f n w) = w at bw
  change (F.iso.hom.app ()).f n ((e.inv.app ()).f n _) = _
  exact (congrArg (fun z => (F.iso.hom.app ()).f n ((e.inv.app ()).f n z)) fw.symm).trans
    ((congrArg (fun z => (F.iso.hom.app ()).f n z) bw).trans fw')

set_option maxHeartbeats 1200000 in
private theorem flatNaturality : FlatNaturality (tensorModel.{u,v} k) Ω := by
  intro A P B C C' f g a a' π X Y X' Y' F F' c p d hp hc hd₁ hd₂ hd e e' he he'
  have l₁ : f ≫ (𝟙 P) = (𝟙 A) ≫ f := by simp
  have l₂ : (π ≫ Y.inl) ≫ d = (𝟙 P) ≫ (π ≫ Y'.inl) := by
    rw [Category.id_comp, Category.assoc, hd₁]
  obtain ⟨l, hl, _⟩ := symbolMaps (𝟙 A) (𝟙 P) (π ≫ Y.inl) (π ≫ Y'.inl) d l₁ l₂
  obtain ⟨r, hr, _⟩ := symbolMaps c p F.augmentation F'.augmentation d hc hd
  refine ⟨l, r, hl, hr, ?_⟩
  apply nestedSymbol_ext π Y.inl
  intro i j l' m n hm hn x b y
  let w := pure Y.inl (N := regular (ι Y.pt)) m l' n hn (symbolTensor T (Ω f) π i j m hm x b) y
  let z := Y.pt.mul j l' (j+l') rfl (Y.inl.chainMap.f j b) y
  change ((e'.inv ≫ F'.iso.hom).app ()).f n ((l.app ()).f n ((e.hom.app ()).f n w)) =
    (r.app ()).f n ((F.iso.hom.app ()).f n w)
  have eq₁ : (e.hom.app ()).f n w =
      symbolTensor T (Ω f) (π ≫ Y.inl) i (j+l') n (by omega) x z :=
    he i j l' m n hm hn (symbol (Ω f) i x) b y
  have eq₂ : (F.iso.hom.app ()).f n w =
      symbolTensor T (Ω X.inr) F.augmentation i (j+l') n (by omega) (X.inl.chainMap.f i x) z :=
    F.onSymbols i j l' m n hm hn x b y
  let J := (e'.inv ≫ F'.iso.hom).app () |>.f n
  have hleft := (congrArg (fun v => (l.app ()).f n v) eq₁).trans
    (hl i (j+l') n (by omega) x z)
  have hright := (congrArg (fun v => (r.app ()).f n v) eq₂).trans
    (hr i (j+l') n (by omega) (X.inl.chainMap.f i x) z)
  refine (congrArg (fun v => J v) hleft).trans ?_
  refine (flatNormalizedSymbol F' e' he' i (j+l') n (by omega) _ _).trans ?_
  have eq : X'.inl.chainMap.f i ((𝟙 P : P ⟶ P).chainMap.f i x) =
      p.chainMap.f i (X.inl.chainMap.f i x) := (component_eq hp i x).symm
  exact (congrArg (fun x' => symbolTensor T (Ω X'.inr) F'.augmentation i (j+l') n (by omega)
    x' (d.chainMap.f (j+l') z)) eq).trans hright.symm

end Naturality

/-- Base change for the cotangent complex on strict semifree representatives. -/
theorem cotangentBaseChange : BaseChange.{u,v} := by
  intro k _ _
  let T₀ := Tensor.moduleTensorModel.{u,v} k
  refine ⟨T₀, coproductModel, (fun {A P} (f : A ⟶ P) => Kahler.model f), Tensor.moduleTensor_comparisons,
    fun {_ _} f N => Tensor.moduleTensor_formulas f N,
    fun {_ _ _} f a => tensorIsPushout coproductModel f a, ?_,
    fun {_ _ _ _ _ _ _ _} => presentationBaseChange,
    differentialComparisons (fun {_ _ _ _ _ _ _ _} => presentationBaseChange),
    identityModels, iteratedComparisons, symbolMaps, differentialNaturality,
    flatComparisons, flatNaturality⟩
  intro A B b
  obtain ⟨P, f, p, h, hs, hp, hq⟩ := _root_.DerivedFormalization.semifreeResolution b
  exact ⟨⟨⟨⟨P, f, p, h, hs, hp, hq⟩, Kahler.model f⟩⟩, fun h =>
    CotangentComplex.nativeComparison b T₀ h Tensor.moduleTensor_formulas⟩

end

end DerivedFormalization.Affine.CotangentBaseChange
