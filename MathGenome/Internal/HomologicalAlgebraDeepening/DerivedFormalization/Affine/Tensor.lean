import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.Tensor
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.BalancedTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ShiftCone

open CategoryTheory
open CochainComplex.HomComplex (Cochain)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom component ofStrict)

universe u v

namespace DerivedFormalization.Affine.Tensor

open Specs.DerivedFormalization.Affine.Tensor
open DGBimodule
open scoped Classical

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {A B C : Affine.CommDGAlgebra.{u,v} k}

/-- The degree of the signed tensor is the balanced quotient of the direct sum. -/
abbrev tensorDegree (f : A ⟶ B) (M : A.Module) (N : B.Module) (n : ℤ) : Type v :=
  Specs.DerivedFormalization.Affine.Tensor.tensorDegree f M N n

abbrev tensor (f : A ⟶ B) (M : A.Module) (N : B.Module) : B.Module :=
  Specs.DerivedFormalization.DG.BalancedTensor.RightModule.toOrdinary.obj
    (mixedTensorModule (signedBimodule f N) M)

/-- Extension with coefficients in a dg module over the target algebra. -/
@[reducible] def extension (f : A ⟶ B) (N : B.Module) : A.Module ⥤ B.Module where
  obj M := tensor f M N
  map g := tensorMap.{u,v,0,0} (signedBimodule f N) g
  map_id M := (tensorFunctor.{u,v,0,0} (signedBimodule f N)).map_id M
  map_comp g g' := (tensorFunctor.{u,v,0,0} (signedBimodule f N)).map_comp g g'

abbrev baseChange (f : A ⟶ B) : A.Module ⥤ B.Module :=
  extension f (regular B)

abbrev over (M N : A.Module) : A.Module := tensor (𝟙 A) M N

abbrev differential (M : A.Module) (i : ℤ) := (M.complex ()).d i (i+1)

local notation "d[" M "," i "]" => differential M i

def pair (f : A ⟶ B) {M : A.Module} {N : B.Module} (i j n : ℤ) (h : i+j=n) :
    term M i →ₗ[k] term N j →ₗ[k] term (tensor f M N) n :=
  tensorPair (signedBimodule f N) M () () i j n h

@[simp] theorem pair_apply (f : A ⟶ B) {M : A.Module} {N : B.Module}
    (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term N j) :
    pair f i j n h x y = pure f i j n h x y := rfl

theorem pure_zsmul_left (f : A ⟶ B) {M : A.Module} {N : B.Module}
    (i j n : ℤ) (h : i+j=n) (t : ℤ) (x : term M i) (y : term N j) :
    pure f i j n h (t • x) y = t • pure f i j n h x y :=
  map_zsmul ((pair f i j n h).flip y) t x

theorem pure_zsmul_right (f : A ⟶ B) {M : A.Module} {N : B.Module}
    (i j n : ℤ) (h : i+j=n) (t : ℤ) (x : term M i) (y : term N j) :
    pure f i j n h x (t • y) = t • pure f i j n h x y :=
  map_zsmul (pair f i j n h x) t y

theorem pure_add_left (f : A ⟶ B) {M : A.Module} {N : B.Module}
    (i j n : ℤ) (h : i+j=n) (x x' : term M i) (y : term N j) :
    pure f i j n h (x+x') y = pure f i j n h x y + pure f i j n h x' y :=
  map_add ((pair f i j n h).flip y) x x'

theorem pure_add_right (f : A ⟶ B) {M : A.Module} {N : B.Module}
    (i j n : ℤ) (h : i+j=n) (x : term M i) (y y' : term N j) :
    pure f i j n h x (y+y') = pure f i j n h x y + pure f i j n h x y' :=
  map_add (pair f i j n h x) y y'

theorem pure_balance (f : A ⟶ B) {M : A.Module} {N : B.Module}
    (i l j il lj n : ℤ) (hi : i+l=il) (hj : l+j=lj) (h : il+j=n)
    (x : term M i) (a : A.complex.X l) (y : term N j) :
    pure f il j n h (act M i l il hi x a) y =
      pure f i lj n (by omega) x (signedLeft N l j lj hj (f.chainMap.f l a) y) :=
  tmul_balance (signedBimodule f N) M () (a := ()) (a' := ())
    i l j il lj n hi hj h x a y

theorem d_pure (f : A ⟶ B) {M : A.Module} {N : B.Module}
    (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term N j) :
    d[tensor f M N,n] (pure f i j n h x y) =
      pure f (i+1) j (n+1) (by omega) (d[M,i] x) y +
        i.negOnePow • pure f i (j+1) (n+1) (by omega) x (d[N,j] y) :=
  tensorComplex_d_tmul.{u,v,0,0} (signedBimodule f N) M () () i j n h x y

theorem d_pure_at (f : A ⟶ B) {M : A.Module} {N : B.Module}
    (i j n i' j' n' : ℤ) (h : i+j=n) (hi : i+1=i') (hj : j+1=j') (hn : n+1=n')
    (x : term M i) (y : term N j) :
    ((tensor f M N).complex ()).d n n' (pure f i j n h x y) =
      pure f i' j n' (by omega) ((M.complex ()).d i i' x) y +
        i.negOnePow • pure f i j' n' (by omega) x ((N.complex ()).d j j' y) := by
  subst i' j' n'
  exact d_pure f i j n h x y

theorem act_pure (f : A ⟶ B) {M : A.Module} {N : B.Module}
    (i j n l q : ℤ) (h : i+j=n) (e : n+l=q)
    (x : term M i) (y : term N j) (b : B.complex.X l) :
    act (tensor f M N) n l q e (pure f i j n h x y) b =
      pure f i (j+l) q (by omega) x (act N j l (j+l) rfl y b) :=
  tensorModule_act_tmul.{u,v,0,0} (signedBimodule f N) M ()
    i j n l (j+l) q h e rfl x y b

theorem map_first_pure (f : A ⟶ B) {M M' : A.Module} {N : B.Module}
    (g : M ⟶ M') (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term N j) :
    (((extension f N).map g).app ()).f n (pure f i j n h x y) =
      pure f i j n h ((g.app ()).f i x) y :=
  tensorMap_tmul.{u,v,0,0} (signedBimodule f N) g () () i j n h x y

section Lift

variable {f : A ⟶ B} {M : A.Module} {N : B.Module}
variable {P : Type*} [AddCommGroup P] [Module k P] {n : ℤ}

theorem pure_ext {F G : term (tensor f M N) n →ₗ[k] P}
    (e : ∀ (i j : ℤ) (h : i+j=n) (x : term M i) (y : term N j),
      F (pure f i j n h x y) = G (pure f i j n h x y)) : F = G :=
  DGBimodule.linearMap_ext (signedBimodule f N) M (fun _ => e)

def liftDegree
    (F : ∀ (i j : ℤ) (_ : i+j=n), term M i →ₗ[k] term N j →ₗ[k] P)
    (e : ∀ (i l j : ℤ) (h : i+l+j=n) (x : term M i) (a : A.complex.X l)
      (y : term N j),
      F (i+l) j h (act M i l (i+l) rfl x a) y =
        F i (l+j) (by omega) x (signedLeft N l j (l+j) rfl (f.chainMap.f l a) y)) :
    term (tensor f M N) n →ₗ[k] P :=
  DGBimodule.lift (signedBimodule f N) M (fun _ => F) (fun _ _ => e)

@[simp] theorem liftDegree_pure (F) (e) (i j : ℤ) (h : i+j=n)
    (x : term M i) (y : term N j) :
    liftDegree (f := f) (M := M) (N := N) (P := P) F e (pure f i j n h x y) = F i j h x y :=
  lift_tmul (signedBimodule f N) M _ _ () i j h x y

end Lift

-- Extensionality is used for the linear maps behind the component morphisms.
local macro "on_pure" : tactic =>
  `(tactic| (apply ModuleCat.hom_ext; apply pure_ext))

private theorem signedLeft_map {N N' : B.Module} (g : N ⟶ N')
    (l j q : ℤ) (h : l+j=q) (a : B.complex.X l) (y : term N j) :
    (g.app ()).f q (signedLeft N l j q h a y) =
      signedLeft N' l j q h a ((g.app ()).f j y) := by
  simp only [signedLeft_apply, Units.smul_def, map_zsmul]
  rw [g.comm_act]

private def secondDegree (f : A ⟶ B) (M : A.Module) {N N' : B.Module} (g : N ⟶ N')
    (n : ℤ) : term (tensor f M N) n →ₗ[k] term (tensor f M N') n :=
    liftDegree (fun i j h => (pair f i j n h).compl₂ ((g.app ()).f j).hom) (by
      intro i l j h x a y
      change pair f (i+l) j n h _ _ = pair f i (l+j) n _ x _
      rw [pair_apply, pair_apply, signedLeft_map]
      exact pure_balance f i l j (i+l) (l+j) n rfl rfl h x a ((g.app ()).f j y))

private theorem secondDegree_pure (f : A ⟶ B) (M : A.Module) {N N' : B.Module} (g : N ⟶ N')
    (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term N j) :
    secondDegree f M g n (pure f i j n h x y) = pure f i j n h x ((g.app ()).f j y) := by
  rw [secondDegree, liftDegree_pure]
  rfl

/-- Tensoring a map in the second module variable. -/
def mapSecond (f : A ⟶ B) (M : A.Module) {N N' : B.Module} (g : N ⟶ N') :
    tensor f M N ⟶ tensor f M N' := by
  let L := secondDegree f M g
  have ev := secondDegree_pure f M g
  refine ⟨?_, ?_⟩
  · rintro ⟨⟩
    refine CochainComplex.ofHom (fun n => ModuleCat.ofHom (L n)) ?_
    intro n
    on_pure
    intro i j h x y
    change d[tensor f M N',n] (L n (pure f i j n h x y)) =
      L (n+1) (d[tensor f M N,n] (pure f i j n h x y))
    rw [ev, d_pure, d_pure, map_add]
    simp only [Units.smul_def, map_zsmul]
    rw [ev, ev]
    have e := CategoryTheory.congr_fun ((g.app ()).comm j (j+1)) y
    simp only [ModuleCat.comp_apply] at e
    rw [e]
  · rintro ⟨⟩ ⟨⟩ n l q e
    intro z b
    change L q (act (tensor f M N) n l q e z b) =
      act (tensor f M N') n l q e (L n z) b
    have eq : (L q).comp ((act (tensor f M N) n l q e).flip b) =
        ((act (tensor f M N') n l q e).flip b).comp (L n) := by
      apply pure_ext
      intro i j h x y
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.flip_apply,
        act_pure, ev, ev, act_pure, g.comm_act]
    exact LinearMap.congr_fun eq z

@[simp] theorem map_second_pure (f : A ⟶ B) (M : A.Module) {N N' : B.Module}
    (g : N ⟶ N') (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term N j) :
    ((mapSecond f M g).app ()).f n (pure f i j n h x y) =
      pure f i j n h x ((g.app ()).f j y) :=
  secondDegree_pure f M g i j n h x y

/-- Extension is functorial in the second argument as well. -/
def secondFunctor (f : A ⟶ B) (M : A.Module) : B.Module ⥤ B.Module where
  obj := tensor f M
  map := mapSecond f M
  map_id N := by
    apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    on_pure
    intro i j h x y
    rw [map_second_pure]
    rfl
  map_comp g g' := by
    apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    on_pure
    intro i j h x y
    change ((mapSecond f M (g ≫ g')).app ()).f n _ =
      ((mapSecond f M g').app ()).f n (((mapSecond f M g).app ()).f n _)
    rw [map_second_pure, map_second_pure, map_second_pure]
    rfl

/-- K-flatness tests acyclicity against all dg modules. -/
def KFlat (N : A.Module) : Prop :=
  ∀ E : A.Module, RightDGModule.Acyclic E → RightDGModule.Acyclic (over E N)

section GradedMap

variable (f : A ⟶ B) (N : B.Module) {M M' : A.Module} {r : ℤ}

private def firstDegree (w : gradedHom M M' r) (n q : ℤ) (e : n+r=q) :
    term (tensor f M N) n →ₗ[k] term (tensor f M' N) q :=
  liftDegree (fun i j h => (pair f (i+r) j q (by omega)).comp (component w () i (i+r) rfl).hom) (by
    intro i l j h x a y
    change pure f (i+l+r) j q (by omega)
        (component w () (i+l) (i+l+r) rfl (act M i l (i+l) rfl x a)) y =
      pure f (i+r) (l+j) q (by omega) (component w () i (i+r) rfl x)
        (signedLeft N l j (l+j) rfl (f.chainMap.f l a) y)
    rw [w.property (a := ()) (b := ()) i l (i+l) (i+r) (i+l+r) rfl rfl rfl x a]
    exact pure_balance f (i+r) l j (i+l+r) (l+j) q (by omega) rfl (by omega)
      (component w () i (i+r) rfl x) a y)

private theorem firstDegree_pure (w : gradedHom M M' r) (i j n ir q : ℤ)
    (h : i+j=n) (hi : i+r=ir) (e : n+r=q) (x : term M i) (y : term N j) :
    firstDegree f N w n q e (pure f i j n h x y) =
      pure f ir j q (by omega) (component w () i ir hi x) y := by
  subst ir
  rw [firstDegree, liftDegree_pure]
  rfl

/-- Tensor a homogeneous right-linear map on the first factor with the identity. -/
def mapFirstGraded (w : gradedHom M M' r) :
    gradedHom (tensor f M N) (tensor f M' N) r :=
  ⟨fun _ => Cochain.mk fun n q e => ModuleCat.ofHom (firstDegree f N w n q e), by
    rintro ⟨⟩ ⟨⟩ n l p nr pr h e hp z a
    have eq : (firstDegree f N w p pr hp).comp ((act (tensor f M N) n l p h).flip a) =
        ((act (tensor f M' N) nr l pr (by omega)).flip a).comp (firstDegree f N w n nr e) := by
      apply pure_ext
      intro i j hij x y
      simp only [LinearMap.comp_apply, LinearMap.flip_apply]
      rw [act_pure, firstDegree_pure f N w i (j+l) p (i+r) pr _ rfl hp,
        firstDegree_pure f N w i j n (i+r) nr hij rfl e, act_pure]
    exact LinearMap.congr_fun eq z⟩

theorem map_first_graded_pure (w : gradedHom M M' r) (i j n ir q : ℤ)
    (h : i+j=n) (hi : i+r=ir) (e : n+r=q) (x : term M i) (y : term N j) :
    component (mapFirstGraded f N w) () n q e (pure f i j n h x y) =
      pure f ir j q (by omega) (component w () i ir hi x) y :=
  firstDegree_pure f N w i j n ir q h hi e x y

end GradedMap

open Specs.DerivedFormalization.DG.HomComplex (HomotopyEquation) in
theorem map_first_homotopy (f : A ⟶ B) (N : B.Module) {M M' : A.Module}
    (g g' : M ⟶ M') (w : gradedHom M M' (-1)) (hw : HomotopyEquation g g' w) :
    HomotopyEquation ((extension f N).map g) ((extension f N).map g')
      (mapFirstGraded f N w) := by
  rintro ⟨⟩ n z
  let L := fun n q e => (component (mapFirstGraded f N w) () n q e).hom
  let G := fun n => (((extension f N).map g).app ()).f n
  let G' := fun n => (((extension f N).map g').app ()).f n
  change G n z - G' n z = ((tensor f M' N).complex ()).d (n-1) n (L n (n-1) (by omega) z) +
    L (n+1) n (by omega) (d[tensor f M N,n] z)
  have e : (G n).hom - (G' n).hom =
      (((tensor f M' N).complex ()).d (n-1) n).hom.comp (L n (n-1) (by omega)) +
        (L (n+1) n (by omega)).comp (d[tensor f M N,n]).hom := by
    apply pure_ext
    intro i j h x y
    change G n (pure f i j n h x y) - G' n (pure f i j n h x y) =
      ((tensor f M' N).complex ()).d (n-1) n
          (component (mapFirstGraded f N w) () n (n-1) (by omega) (pure f i j n h x y)) +
        component (mapFirstGraded f N w) () (n+1) n (by omega)
          (d[tensor f M N,n] (pure f i j n h x y))
    rw [map_first_pure, map_first_pure,
      map_first_graded_pure f N w i j n (i-1) (n-1) h (by omega) (by omega)]
    rw [d_pure_at f (i-1) j (n-1) i (j+1) n _ (by omega) rfl (by omega),
      d_pure f i j n h x y, map_add]
    simp only [Units.smul_def, map_zsmul]
    rw [map_first_graded_pure f N w (i+1) j (n+1) i n (by omega) (by omega) (by omega),
      map_first_graded_pure f N w i (j+1) (n+1) (i-1) n (by omega) (by omega) (by omega)]
    have hi : (i-1).negOnePow = -i.negOnePow := by
      rw [show i-1 = i+(-1) by omega, Int.negOnePow_add]
      simp [Int.negOnePow_neg]
    simp only [hi, Units.val_neg, neg_smul]
    rw [← pair_apply f i j n h ((g.app ()).f i x) y,
      ← pair_apply f i j n h ((g'.app ()).f i x) y,
      ← LinearMap.sub_apply, ← map_sub, hw () i x, map_add, LinearMap.add_apply,
      pair_apply, pair_apply]
    abel
  exact LinearMap.congr_fun e z


/-- Assemble a module morphism from commuting maps of its homogeneous terms. -/
def homOfDegrees {M N : A.Module} (L : ∀ n, term M n →ₗ[k] term N n)
    (hd : ∀ n (x : term M n), d[N,n] (L n x) = L (n+1) (d[M,n] x))
    (ha : ∀ i j n (h : i+j=n) (x : term M i) (a : A.complex.X j),
      L n (act M i j n h x a) = act N i j n h (L i x) a) :
    M ⟶ N where
  app := fun a => by
    cases a
    exact CochainComplex.ofHom (fun n => ModuleCat.ofHom (L n)) (by
      intro n
      apply ModuleCat.hom_ext
      exact LinearMap.ext (hd n))
  comm_act := by
    rintro ⟨⟩ ⟨⟩ i j n h x a
    exact ha i j n h x a

section Cone

open RightDGModule (cone coneGradedRetraction coneInclusion)
open Specs.DerivedFormalization.DG.ShiftCone (coneDiff_succ)

variable {M M' : A.Module} (g : M ⟶ M') (f : A ⟶ B) (N : B.Module)

private def coneSnd : gradedHom (cone g) M 1 :=
  ⟨fun a => Cochain.mk fun i q e => by
    subst q
    exact ModuleCat.ofHom (LinearMap.snd _ _ _), by
    intro a b i j n ir nr h hi hn x z
    subst ir nr
    rfl⟩

private def coneInr : gradedHom M (cone g) (-1) :=
  ⟨fun a => Cochain.mk fun i q e => by
    have t : q+1=i := by omega
    subst i
    exact ModuleCat.ofHom (LinearMap.inr _ _ _), by
    intro a b i j n ir nr h hi hn x z
    have ti : ir+1=i := by omega
    have tn : nr+1=n := by omega
    subst i n
    change (0, M.act (ir+1) j (nr+1) _ x z) = (_, _)
    simp⟩

private theorem coneInr_apply (i p : ℤ) (h : p+1=i) (x : term M i) :
    component (coneInr g) () i p (by omega) x = (0, cast (congrArg (fun a => ↥(term M a)) h.symm) x) := by
  subst i
  rfl

private def coneForward (n : ℤ) :
    term (tensor f (cone g) N) n →ₗ[k] term (cone ((extension f N).map g)) n :=
  (firstDegree f N (coneGradedRetraction g) n n (by omega)).prod
    (firstDegree f N (coneSnd g) n (n+1) rfl)

private theorem coneForward_pure (i j n : ℤ) (h : i+j=n)
    (p : term (cone g) i) (y : term N j) :
    coneForward g f N n (pure f i j n h p y) =
      (pure f i j n h p.1 y, pure f (i+1) j (n+1) (by omega) p.2 y) := by
  unfold coneForward
  apply Prod.ext
  · exact firstDegree_pure f N (coneGradedRetraction g) i j n i n h (by omega) (by omega) p y
  · exact firstDegree_pure f N (coneSnd g) i j n (i+1) (n+1) h rfl rfl p y

private def coneBackward (n : ℤ) :
    term (cone ((extension f N).map g)) n →ₗ[k] term (tensor f (cone g) N) n :=
  (firstDegree f N (ofStrict (coneInclusion g)) n n (by omega)).coprod
    (firstDegree f N (coneInr g) (n+1) n (by omega))

private theorem coneBackward_left (i j n : ℤ) (h : i+j=n) (x : term M' i) (y : term N j) :
    coneBackward g f N n (pure f i j n h x y, 0) = pure f i j n h (x, 0) y := by
  unfold coneBackward
  rw [LinearMap.coprod_apply, map_zero, add_zero]
  exact firstDegree_pure f N (ofStrict (coneInclusion g)) i j n i n h (by omega) (by omega) x y

private theorem coneBackward_right (i j n p : ℤ) (h : i+j=n+1) (hp : p+1=i)
    (x : term M i) (y : term N j) :
    coneBackward g f N n (0, pure f i j (n+1) h x y) =
      pure f p j n (by omega) (0, cast (congrArg (fun a => ↥(term M a)) hp.symm) x) y := by
  unfold coneBackward
  rw [LinearMap.coprod_apply, map_zero, zero_add,
    firstDegree_pure f N (coneInr g) i j (n+1) p n h (by omega) (by omega),
    coneInr_apply g i p hp]

private theorem tensorCone_comm (n : ℤ) (z : term (tensor f (cone g) N) n) :
    d[cone ((extension f N).map g),n] (coneForward g f N n z) =
      coneForward g f N (n+1) (d[tensor f (cone g) N,n] z) := by
  have eq : (d[cone ((extension f N).map g),n]).hom.comp (coneForward g f N n) =
      (coneForward g f N (n+1)).comp (d[tensor f (cone g) N,n]).hom := by
    apply pure_ext
    intro i j h p y
    change d[cone ((extension f N).map g),n] (coneForward g f N n (pure f i j n h p y)) =
      coneForward g f N (n+1) (d[tensor f (cone g) N,n] (pure f i j n h p y))
    rw [coneForward_pure, d_pure, map_add, Units.smul_def, map_zsmul,
      coneForward_pure, coneForward_pure]
    change Specs.DerivedFormalization.DG.ShiftCone.coneDiff ((extension f N).map g) () n (n+1) _ = _
    rw [coneDiff_succ]
    apply Prod.ext
    · change d[tensor f M' N,n] _ + (((extension f N).map g).app ()).f (n+1) _ =
        pure f (i+1) j (n+1) (by omega)
          (Specs.DerivedFormalization.DG.ShiftCone.coneDiff g () i (i+1) p).1 y +
        (i.negOnePow : ℤ) • pure f i (j+1) (n+1) (by omega) p.1 (d[N,j] y)
      rw [coneDiff_succ, d_pure, map_first_pure, ← pair_apply f _ _ _ _ (_ + _) y,
        map_add, LinearMap.add_apply, pair_apply, pair_apply, Units.smul_def]
      abel
    · change -(d[tensor f M N,n+1] _) =
        pure f (i+1+1) j (n+1+1) (by omega)
          (Specs.DerivedFormalization.DG.ShiftCone.coneDiff g () i (i+1) p).2 y +
        (i.negOnePow : ℤ) • pure f (i+1) (j+1) (n+1+1) (by omega) p.2 (d[N,j] y)
      rw [coneDiff_succ, d_pure, Int.negOnePow_succ, Units.neg_smul, Units.smul_def, neg_add, neg_neg,
        ← pair_apply f _ _ _ _ (-_) y, map_neg, LinearMap.neg_apply, pair_apply]
  exact LinearMap.congr_fun eq z

private theorem tensorCone_action (i l n : ℤ) (h : i+l=n)
    (z : term (tensor f (cone g) N) i) (a : B.complex.X l) :
    coneForward g f N n (act (tensor f (cone g) N) i l n h z a) =
      act (cone ((extension f N).map g)) i l n h (coneForward g f N i z) a := by
  have eq : (coneForward g f N n).comp ((act (tensor f (cone g) N) i l n h).flip a) =
      ((act (cone ((extension f N).map g)) i l n h).flip a).comp (coneForward g f N i) := by
    apply pure_ext
    intro p q e x y
    simp only [LinearMap.comp_apply, LinearMap.flip_apply]
    rw [act_pure, coneForward_pure, coneForward_pure]
    apply Prod.ext
    · exact (act_pure f p q i l n e h x.1 y a).symm
    · exact (act_pure f (p+1) q (i+1) l (n+1) (by omega) (by omega) x.2 y a).symm
  exact LinearMap.congr_fun eq z

private theorem coneBackward_forward (n : ℤ) :
    (coneBackward g f N n).comp (coneForward g f N n) = LinearMap.id := by
  apply pure_ext
  intro i j h p y
  rw [LinearMap.comp_apply, coneForward_pure, LinearMap.id_apply]
  have e : (pure f i j n h p.1 y, pure f (i+1) j (n+1) (by omega) p.2 y) =
      (pure f i j n h p.1 y, 0) + (0, pure f (i+1) j (n+1) (by omega) p.2 y) := by
    simp
  rw [e, map_add, coneBackward_left,
    coneBackward_right g f N (i+1) j n i (by omega) rfl]
  change _ + pure f i j n h (M := cone g) (0, p.2) y = _
  have ep : ((p.1, 0) : term (cone g) i) + (0, p.2) = p := by simp
  have eL := map_add ((pair f (M := cone g) i j n h).flip y) (p.1, 0) (0, p.2)
  rw [ep] at eL
  exact eL.symm


private theorem coneForward_backward (n : ℤ) :
    (coneForward g f N n).comp (coneBackward g f N n) = LinearMap.id := by
  apply LinearMap.prod_ext
  · apply pure_ext
    intro i j h x y
    change coneForward g f N n (coneBackward g f N n (pure f i j n h x y, 0)) = _
    rw [coneBackward_left, coneForward_pure, ← pair_apply f (i+1) j (n+1) _ 0 y,
      map_zero, LinearMap.zero_apply]
    rfl
  · apply pure_ext
    intro i j h x y
    change coneForward g f N n (coneBackward g f N n (0, pure f i j (n+1) h x y)) = _
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, p+1=i := ⟨i-1, by omega⟩
    rw [coneBackward_right g f N (p+1) j n p h rfl, coneForward_pure,
      ← pair_apply f p j n _ 0 y, map_zero, LinearMap.zero_apply]
    rfl

/-- Tensor in the first factor commutes with the signed cone. -/
def tensorConeIso : tensor f (cone g) N ≅ cone ((extension f N).map g) where
  hom := homOfDegrees (coneForward g f N) (tensorCone_comm g f N) (tensorCone_action g f N)
  inv := homOfDegrees (coneBackward g f N)
    (by
      intro n z
      have hl := fun m x => LinearMap.congr_fun (coneBackward_forward g f N m) x
      have hr := fun m x => LinearMap.congr_fun (coneForward_backward g f N m) x
      have e := congrArg (coneBackward g f N (n+1))
        (tensorCone_comm g f N n (coneBackward g f N n z))
      change coneBackward g f N (n+1) (d[cone ((extension f N).map g),n]
        (((coneForward g f N n).comp (coneBackward g f N n)) z)) =
        ((coneBackward g f N (n+1)).comp (coneForward g f N (n+1))) _ at e
      rw [hr, hl] at e
      exact e.symm)
    (by
      intro i j n h z a
      have hl := fun m x => LinearMap.congr_fun (coneBackward_forward g f N m) x
      have hr := fun m x => LinearMap.congr_fun (coneForward_backward g f N m) x
      have e := congrArg (coneBackward g f N n)
        (tensorCone_action g f N i j n h (coneBackward g f N i z) a)
      change ((coneBackward g f N n).comp (coneForward g f N n)) _ =
        coneBackward g f N n (act (cone ((extension f N).map g)) i j n h
          (((coneForward g f N i).comp (coneBackward g f N i)) z) a) at e
      rw [hl, hr] at e
      exact e.symm)
  hom_inv_id := by
    apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    exact coneBackward_forward g f N n
  inv_hom_id := by
    apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    exact coneForward_backward g f N n

end Cone

theorem KFlat.map_quasiIso {N M M' : A.Module} (hN : KFlat N)
    (g : M ⟶ M') (h : RightDGModule.IsQuasiIso g) :
    RightDGModule.IsQuasiIso ((extension (𝟙 A) N).map g) := by
  apply (RightDGModule.quasiIso_iff_cone_acyclic _).2
  have h' := hN _ ((RightDGModule.quasiIso_iff_cone_acyclic g).1 h)
  intro a i
  have e := (HomologicalComplex.homologyFunctor _ _ i).mapIso
    ((RightDGModuleModel.eval a).mapIso (tensorConeIso g (𝟙 A) N))
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ i).2
    (((HomologicalComplex.exactAt_iff_isZero_homology _ i).1 (h' a i)).of_iso e.symm)


/-- The functor and degree equivalence for the signed balanced tensor. -/
def moduleTensorModel (k : Type u) [Field k] [CharZero k] : ModuleTensor.{u,v} k where
  extension f N := extension f N
  degree _ _ _ _ := LinearEquiv.refl _ _

section Algebra

set_option maxHeartbeats 800000

variable (f : A ⟶ B) (g : A ⟶ C)

abbrev algebraModule : C.Module := tensor g (restrict f (regular B)) (regular C)

abbrev algebraComplex := (algebraModule f g).complex ()

noncomputable abbrev algebraPure (i j n : ℤ) (h : i+j=n) (x : B.complex.X i)
    (y : C.complex.X j) : (algebraComplex f g).X n :=
  pure g (M := restrict f (regular B)) (N := regular C) i j n h x y

private abbrev algebraPair (i j n : ℤ) (h : i+j=n) :
    B.complex.X i →ₗ[k] C.complex.X j →ₗ[k] (algebraComplex f g).X n :=
  pair g (M := restrict f (regular B)) (N := regular C) i j n h

private theorem mul_assoc_at (D : Affine.CommDGAlgebra.{u,v} k) (i j l ij jl n : ℤ)
    (hij : i+j=ij) (hjl : j+l=jl) (hn : ij+l=n)
    (x : D.complex.X i) (y : D.complex.X j) (z : D.complex.X l) :
    D.mul ij l n hn (D.mul i j ij hij x y) z =
      D.mul i jl n (by omega) x (D.mul j l jl hjl y z) :=
  act_assoc_at (regular D) i j l ij jl n hij hjl hn x y z

private theorem algebraPure_smul_left (i j n : ℤ) (h : i+j=n) (t : ℤ)
    (x : B.complex.X i) (y : C.complex.X j) :
    algebraPure f g i j n h (t • x) y = t • algebraPure f g i j n h x y :=
  map_zsmul ((algebraPair f g i j n h).flip y) t x

private theorem algebraPure_smul_right (i j n : ℤ) (h : i+j=n) (t : ℤ)
    (x : B.complex.X i) (y : C.complex.X j) :
    algebraPure f g i j n h x (t • y) = t • algebraPure f g i j n h x y :=
  map_zsmul (algebraPair f g i j n h x) t y

private theorem algebraPure_balance (i l j il lj n : ℤ) (hi : i+l=il) (hj : l+j=lj)
    (h : il+j=n) (x : B.complex.X i) (a : A.complex.X l) (y : C.complex.X j) :
    algebraPure f g il j n h (B.mul i l il hi x (f.chainMap.f l a)) y =
      (l*j).negOnePow • algebraPure f g i lj n (by omega) x
        (C.mul j l lj (by omega) y (g.chainMap.f l a)) := by
  have e := pure_balance g (M := restrict f (regular B)) (N := regular C)
    i l j il lj n hi hj h x a y
  rw [signedLeft_apply, Units.smul_def] at e
  exact e.trans (algebraPure_smul_right f g i lj n _ _ x _)

private abbrev productOnPure (i j p q ip jq n : ℤ)
    (e : i+p=ip) (e' : j+q=jq) (h : ip+jq=n)
    (x : B.complex.X i) (y : C.complex.X j) (z : B.complex.X p) (w : C.complex.X q) :
    (algebraComplex f g).X n :=
  (j*p).negOnePow • algebraPure f g ip jq n h (B.mul i p ip e x z) (C.mul j q jq e' y w)

private theorem productOnPure_comm (i j p q ip jq n : ℤ)
    (e : i+p=ip) (e' : j+q=jq) (h : ip+jq=n)
    (x : B.complex.X i) (y : C.complex.X j) (z : B.complex.X p) (w : C.complex.X q) :
    productOnPure f g i j p q ip jq n e e' h x y z w =
      ((i+j)*(p+q)).negOnePow •
        productOnPure f g p q i j ip jq n (by omega) (by omega) h z w x y := by
  unfold productOnPure
  rw [B.graded_comm i p ip e x z, C.graded_comm j q jq e' y w]
  simp only [Units.smul_def, algebraPure_smul_left, algebraPure_smul_right,
    smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
  rw [show j*p+(j*q+i*p) = (i+j)*(p+q)+q*i - 2*(i*q) by ring,
    sub_eq_add_neg, Int.negOnePow_add, Int.negOnePow_neg, Int.negOnePow_two_mul, mul_one]

private theorem productOnPure_balance_right
    (i j p l q pl lq ip ipL jq jqL n : ℤ)
    (epl : p+l=pl) (elq : l+q=lq) (eip : i+p=ip) (eipL : i+pl=ipL)
    (ejq : j+q=jq) (ejqL : j+lq=jqL) (h : ipL+jq=n)
    (x : B.complex.X i) (y : C.complex.X j) (z : B.complex.X p)
    (a : A.complex.X l) (w : C.complex.X q) :
    productOnPure f g i j pl q ipL jq n eipL ejq h
        x y (B.mul p l pl epl z (f.chainMap.f l a)) w =
      productOnPure f g i j p lq ip jqL n eip ejqL (by omega)
        x y z (signedLeft (regular C) l q lq elq (g.chainMap.f l a) w) := by
  unfold productOnPure
  rw [← mul_assoc_at B i p l ip pl ipL eip epl (by omega) x z (f.chainMap.f l a),
    algebraPure_balance f g ip l jq ipL jqL n (by omega) (by omega) h,
    signedLeft_apply]
  change _ = (j*p).negOnePow • algebraPure f g ip jqL n _
    (B.mul i p ip eip x z) (C.mul j lq jqL ejqL y ((l*q).negOnePow • C.mul q l lq _ w _))
  simp only [Units.smul_def, map_zsmul, algebraPure_smul_right,
    smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
  rw [← mul_assoc_at C j q l jq lq jqL ejq (by omega) (by omega),
    show j*pl+l*jq = j*p+l*q+2*(j*l) by rw [← epl, ← ejq]; ring,
    Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

private def leftProduct (i j m n : ℤ) (h : i+j+m=n)
    (x : B.complex.X i) (y : C.complex.X j) :
    (algebraComplex f g).X m →ₗ[k] (algebraComplex f g).X n :=
  liftDegree (f := g) (M := restrict f (regular B)) (N := regular C)
    (fun p q e => (j*p).negOnePow •
      (((algebraPair f g (i+p) (j+q) n (by omega)).comp
        (B.mul i p (i+p) rfl x)).compl₂ (C.mul j q (j+q) rfl y)))
    (by
      intro p l q e z a w
      exact productOnPure_balance_right f g i j p l q (p+l) (l+q)
        (i+p) (i+(p+l)) (j+q) (j+(l+q)) n rfl rfl rfl rfl rfl rfl (by omega) x y z a w)

private theorem leftProduct_pure (i j p q ip jq m n : ℤ)
    (ep : p+q=m) (h : i+j+m=n) (e : i+p=ip) (e' : j+q=jq)
    (x : B.complex.X i) (y : C.complex.X j) (z : B.complex.X p) (w : C.complex.X q) :
    leftProduct f g i j m n h x y (algebraPure f g p q m ep z w) =
      productOnPure f g i j p q ip jq n e e' (by omega) x y z w := by
  subst ip jq
  unfold leftProduct
  erw [liftDegree_pure]
  rfl

private abbrev leftProductBilinear (i j m n : ℤ) (h : i+j+m=n) :
    B.complex.X i →ₗ[k] C.complex.X j →ₗ[k]
      (algebraComplex f g).X m →ₗ[k] (algebraComplex f g).X n :=
  LinearMap.mk₂ k (leftProduct f g i j m n h)
    (by
      intro x x' y
      apply pure_ext
      intro p q ep z w
      rw [LinearMap.add_apply, leftProduct_pure f g i j p q (i+p) (j+q) m n ep h rfl rfl,
        leftProduct_pure f g i j p q (i+p) (j+q) m n ep h rfl rfl,
        leftProduct_pure f g i j p q (i+p) (j+q) m n ep h rfl rfl]
      unfold productOnPure
      simp only [← pair_apply, map_add, LinearMap.add_apply, smul_add])
    (by
      intro t x y
      apply pure_ext
      intro p q ep z w
      rw [LinearMap.smul_apply, leftProduct_pure f g i j p q (i+p) (j+q) m n ep h rfl rfl,
        leftProduct_pure f g i j p q (i+p) (j+q) m n ep h rfl rfl]
      unfold productOnPure
      simp only [← pair_apply, map_smul, LinearMap.smul_apply]
      exact smul_comm _ _ _)
    (by
      intro x y y'
      apply pure_ext
      intro p q ep z w
      rw [LinearMap.add_apply, leftProduct_pure f g i j p q (i+p) (j+q) m n ep h rfl rfl,
        leftProduct_pure f g i j p q (i+p) (j+q) m n ep h rfl rfl,
        leftProduct_pure f g i j p q (i+p) (j+q) m n ep h rfl rfl]
      unfold productOnPure
      simp only [← pair_apply, map_add, LinearMap.add_apply, smul_add])
    (by
      intro t x y
      apply pure_ext
      intro p q ep z w
      rw [LinearMap.smul_apply, leftProduct_pure f g i j p q (i+p) (j+q) m n ep h rfl rfl,
        leftProduct_pure f g i j p q (i+p) (j+q) m n ep h rfl rfl]
      unfold productOnPure
      simp only [← pair_apply, map_smul, LinearMap.smul_apply]
      exact smul_comm _ _ _)

private theorem leftProduct_balance (p m n : ℤ) (hp : p+m=n)
    (i l j : ℤ) (h : i+l+j=p) (x : B.complex.X i) (a : A.complex.X l) (y : C.complex.X j) :
    leftProduct f g (i+l) j m n (by omega) (B.mul i l (i+l) rfl x (f.chainMap.f l a)) y =
      leftProduct f g i (l+j) m n (by omega) x
        (signedLeft (regular C) l j (l+j) rfl (g.chainMap.f l a) y) := by
  apply pure_ext
  intro s t e z w
  rw [leftProduct_pure f g (i+l) j s t (s+(i+l)) (t+j) m n e _ (by omega) (by omega),
    leftProduct_pure f g i (l+j) s t (s+i) (t+(l+j)) m n e _ (by omega) (by omega),
    productOnPure_comm f g (i+l) j s t, productOnPure_comm f g i (l+j) s t,
    show (i+l+j)*(s+t)=p*m by rw [h,e],
    show (i+(l+j))*(s+t)=p*m by rw [← add_assoc,h,e]]
  congr 1
  exact productOnPure_balance_right f g s t i l j (i+l) (l+j) (s+i) (s+(i+l))
    (t+j) (t+(l+j)) n rfl rfl rfl rfl rfl rfl (by omega) z w x a y

/-- The Koszul multiplication of the tensor of two commutative dg algebras. -/
def algebraMul (p m n : ℤ) (hp : p+m=n) :
    (algebraComplex f g).X p →ₗ[k] (algebraComplex f g).X m →ₗ[k] (algebraComplex f g).X n :=
  liftDegree (fun i j h => leftProductBilinear f g i j m n (by omega))
    (fun i l j h x a y => leftProduct_balance f g p m n hp i l j h x a y)

theorem algebraMul_pure (i j p q m m' ip jq n : ℤ) (h : i+j=m) (h' : p+q=m')
    (hh : m+m'=n) (e : i+p=ip) (e' : j+q=jq)
    (x : B.complex.X i) (y : C.complex.X j) (z : B.complex.X p) (w : C.complex.X q) :
    algebraMul f g m m' n hh (algebraPure f g i j m h x y) (algebraPure f g p q m' h' z w) =
      (j*p).negOnePow • algebraPure f g ip jq n (by omega) (B.mul i p ip e x z)
        (C.mul j q jq e' y w) := by
  unfold algebraMul
  erw [liftDegree_pure]
  exact leftProduct_pure f g i j p q ip jq m' n h' (by omega) e e' x y z w

private abbrev algebraOne : (algebraComplex f g).X 0 :=
  algebraPure f g 0 0 0 rfl B.one C.one

private theorem d_algebraPure (i j n : ℤ) (h : i+j=n) (x : B.complex.X i) (y : C.complex.X j) :
    (algebraComplex f g).d n (n+1) (algebraPure f g i j n h x y) =
      algebraPure f g (i+1) j (n+1) (by omega) (B.complex.d i (i+1) x) y +
      i.negOnePow • algebraPure f g i (j+1) (n+1) (by omega) x (C.complex.d j (j+1) y) :=
  d_pure g (M := restrict f (regular B)) (N := regular C) i j n h x y

private theorem d_algebraPure_at (i j n i' j' : ℤ) (h : i+j=n) (hi : i+1=i') (hj : j+1=j')
    (x : B.complex.X i) (y : C.complex.X j) :
    (algebraComplex f g).d n (n+1) (algebraPure f g i j n h x y) =
      algebraPure f g i' j (n+1) (by omega) (B.complex.d i i' x) y +
      i.negOnePow • algebraPure f g i j' (n+1) (by omega) x (C.complex.d j j' y) :=
  d_pure_at g (M := restrict f (regular B)) (N := regular C) i j n i' j' (n+1) h hi hj rfl x y

private theorem algebraOne_closed :
    (algebraComplex f g).d 0 1 (algebraOne f g) = 0 := by
  change (algebraComplex f g).d 0 (0+1) (algebraPure f g 0 0 0 rfl B.one C.one) = 0
  rw [d_algebraPure f g 0 0 0 rfl B.one C.one,
    show B.complex.d 0 (0+1) B.one = 0 from B.toDGAlgebra.d_id (),
    show C.complex.d 0 (0+1) C.one = 0 from C.toDGAlgebra.d_id ()]
  change (algebraPair f g (0+1) 0 1 _ 0 C.one) + (0 : ℤ).negOnePow •
    algebraPair f g 0 (0+1) 1 _ B.one 0 = 0
  rw [map_zero, LinearMap.zero_apply, map_zero, smul_zero, add_zero]

private theorem algebraOne_mul (n : ℤ) :
    algebraMul f g 0 n n (zero_add n) (algebraOne f g) = LinearMap.id := by
  apply pure_ext
  intro i j h x y
  rw [algebraOne, algebraMul_pure f g 0 0 i j 0 n i j n rfl h _ (zero_add i) (zero_add j),
    zero_mul, Int.negOnePow_zero, one_smul]
  exact congrArg₂ (algebraPure f g i j n h) (B.toDGAlgebra.id_comp i x) (C.toDGAlgebra.id_comp j y)

private theorem algebraMul_one (n : ℤ) :
    (algebraMul f g n 0 n (add_zero n)).flip (algebraOne f g) = LinearMap.id := by
  apply pure_ext
  intro i j h x y
  rw [LinearMap.flip_apply, algebraOne, algebraMul_pure f g i j 0 0 n 0 i j n h rfl _ (add_zero i) (add_zero j),
    mul_zero, Int.negOnePow_zero, one_smul]
  exact congrArg₂ (algebraPure f g i j n h) (B.toDGAlgebra.comp_id i x) (C.toDGAlgebra.comp_id j y)

private theorem algebraMul_comm (i j n : ℤ) (h : i+j=n) :
    algebraMul f g i j n h = (i*j).negOnePow • (algebraMul f g j i n (by omega)).flip := by
  apply pure_ext
  intro a b hab x y
  apply pure_ext
  intro c d hcd z w
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.flip_apply,
    algebraMul_pure f g a b c d i j (a+c) (b+d) n hab hcd h rfl rfl,
    algebraMul_pure f g c d a b j i (a+c) (b+d) n hcd hab (by omega) (by omega) (by omega)]
  subst i j
  exact productOnPure_comm f g a b c d (a+c) (b+d) n rfl rfl (by omega) x y z w

private theorem algebraMul_assoc (i j l : ℤ)
    (x : (algebraComplex f g).X i) (y : (algebraComplex f g).X j)
    (z : (algebraComplex f g).X l) :
    algebraMul f g (i+j) l (i+j+l) rfl (algebraMul f g i j (i+j) rfl x y) z =
      algebraMul f g i (j+l) (i+j+l) (by omega) x (algebraMul f g j l (j+l) rfl y z) := by
  have e (z : (algebraComplex f g).X l) :
      (algebraMul f g i j (i+j) rfl).compr₂ ((algebraMul f g (i+j) l (i+j+l) rfl).flip z) =
        (algebraMul f g i (j+l) (i+j+l) (by omega)).compl₂
          ((algebraMul f g j l (j+l) rfl).flip z) := by
    apply pure_ext
    intro a b hab x y
    apply pure_ext
    intro c d hcd w t
    have ez :
        algebraMul f g (i+j) l (i+j+l) rfl
          (algebraMul f g i j (i+j) rfl (algebraPure f g a b i hab x y) (algebraPure f g c d j hcd w t)) =
        (algebraMul f g i (j+l) (i+j+l) (by omega) (algebraPure f g a b i hab x y)).comp
          (algebraMul f g j l (j+l) rfl (algebraPure f g c d j hcd w t)) := by
      apply pure_ext
      intro p q hpq u v
      rw [LinearMap.comp_apply, algebraMul_pure f g a b c d i j (a+c) (b+d) (i+j) hab hcd rfl rfl rfl,
        algebraMul_pure f g c d p q j l (c+p) (d+q) (j+l) hcd hpq rfl rfl rfl]
      simp only [Units.smul_def, map_zsmul, LinearMap.smul_apply]
      rw [algebraMul_pure f g (a+c) (b+d) p q (i+j) l (a+c+p) (b+d+q) (i+j+l)
            _ hpq rfl rfl rfl,
        algebraMul_pure f g a b (c+p) (d+q) i (j+l) (a+c+p) (b+d+q) (i+j+l)
            hab _ _ (by omega) (by omega)]
      rw [mul_assoc_at B a c p (a+c) (c+p) (a+c+p) rfl rfl rfl,
        mul_assoc_at C b d q (b+d) (d+q) (b+d+q) rfl rfl rfl]
      simp only [Units.smul_def, smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
      rw [show b*c+(b+d)*p = d*p+b*(c+p) by ring]
    exact LinearMap.congr_fun ez z
  exact LinearMap.congr_fun (LinearMap.congr_fun (e z) x) y

private theorem algebraMul_d (i j n : ℤ) (h : i+j=n) :
    (algebraMul f g i j n h).compr₂ ((algebraComplex f g).d n (n+1)).hom =
      (algebraMul f g (i+1) j (n+1) (by omega)).comp ((algebraComplex f g).d i (i+1)).hom +
        i.negOnePow •
          (algebraMul f g i (j+1) (n+1) (by omega)).compl₂ ((algebraComplex f g).d j (j+1)).hom := by
  apply pure_ext
  intro a b hab x y
  apply pure_ext
  intro c d hcd z w
  change (algebraComplex f g).d n (n+1)
      (algebraMul f g i j n h (algebraPure f g a b i hab x y) (algebraPure f g c d j hcd z w)) =
    algebraMul f g (i+1) j (n+1) (by omega) ((algebraComplex f g).d i (i+1) (algebraPure f g a b i hab x y))
        (algebraPure f g c d j hcd z w) +
      i.negOnePow • algebraMul f g i (j+1) (n+1) (by omega) (algebraPure f g a b i hab x y)
        ((algebraComplex f g).d j (j+1) (algebraPure f g c d j hcd z w))
  rw [algebraMul_pure f g a b c d i j (a+c) (b+d) n hab hcd h rfl rfl]
  rw [Units.smul_def, map_zsmul]
  rw [d_algebraPure f g a b i hab, d_algebraPure f g c d j hcd,
    d_algebraPure_at f g (a+c) (b+d) n (a+1+c) (b+1+d) (by omega) (by omega) (by omega)]
  have b_d := B.toDGAlgebra.leibniz (a := ()) (b := ()) (c := ()) a c (a+c) rfl x z
  have c_d := C.toDGAlgebra.leibniz (a := ()) (b := ()) (c := ()) b d (b+d) rfl y w
  simp only [Units.smul_def, map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [algebraMul_pure f g (a+1) b c d (i+1) j (a+1+c) (b+d) (n+1) _ hcd _ rfl rfl,
    algebraMul_pure f g a (b+1) c d (i+1) j (a+c) (b+1+d) (n+1) _ hcd _ rfl rfl,
    algebraMul_pure f g a b (c+1) d i (j+1) (a+1+c) (b+d) (n+1) hab _ _ (by omega) rfl,
    algebraMul_pure f g a b c (d+1) i (j+1) (a+c) (b+1+d) (n+1) hab _ _ rfl (by omega)]
  -- Distribute the two Leibniz formulas at the chosen output indices.
  have atB (q : ℤ) (hq : a+c+1=q) :
      B.complex.d (a+c) q (B.mul a c (a+c) rfl x z) =
        B.mul (a+1) c q (by omega) (B.complex.d a (a+1) x) z +
          a.negOnePow • B.mul a (c+1) q (by omega) x (B.complex.d c (c+1) z) := by
    subst q
    exact b_d
  have atC (q : ℤ) (hq : b+d+1=q) :
      C.complex.d (b+d) q (C.mul b d (b+d) rfl y w) =
        C.mul (b+1) d q (by omega) (C.complex.d b (b+1) y) w +
          b.negOnePow • C.mul b (d+1) q (by omega) y (C.complex.d d (d+1) w) := by
    subst q
    exact c_d
  rw [atB _ (by omega), atC _ (by omega)]
  simp only [← pair_apply, Units.smul_def, map_add, map_zsmul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_add, smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
  subst i
  rw [show b*c+(a+c) = a+(b+1)*c by ring,
    show b*c+(a+c+b) = a+b+(c+b*c) by ring]
  have ep : (a+b+b*(c+1)).negOnePow = (b*c+a).negOnePow := by
    rw [show a+b+b*(c+1) = b*c+a+2*b by ring, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
  rw [ep]
  abel

/-- The commutative dg algebra on the balanced tensor of the regular modules. -/
@[reducible] def algebraTensor : Affine.CommDGAlgebra.{u,v} k where
  toDGAlgebra :=
    { hom := fun _ _ => algebraComplex f g
      comp := fun i j n h => algebraMul f g i j n h
      id := fun _ => algebraOne f g
      d_id := fun _ => algebraOne_closed f g
      id_comp := fun i x => LinearMap.congr_fun (algebraOne_mul f g i) x
      comp_id := fun i x => LinearMap.congr_fun (algebraMul_one f g i) x
      assoc := fun i j l => algebraMul_assoc f g i j l
      leibniz := fun i j n h x y => LinearMap.congr_fun (LinearMap.congr_fun (algebraMul_d f g i j n h) x) y }
  graded_comm i j n h x y := LinearMap.congr_fun
    (LinearMap.congr_fun (algebraMul_comm f g i j n h) x) y


@[reducible] def chainOfDegrees {X Y : ModuleCochain.{u,v} k}
    (L : ∀ n, X.X n →ₗ[k] Y.X n)
    (h : ∀ n (x : X.X n), Y.d n (n+1) (L n x) = L (n+1) (X.d n (n+1) x)) :
    X ⟶ Y :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (L n)) (fun n =>
    ModuleCat.hom_ext (LinearMap.ext (h n)))

/-- The first algebra map into the tensor product sends `x` to `x ⊗ 1`. -/
def algebraInl : B ⟶ algebraTensor f g where
  chainMap := chainOfDegrees (fun n => (algebraPair f g n 0 n (add_zero n)).flip C.one) (by
    intro i x
    change (algebraComplex f g).d i (i+1) (algebraPure f g i 0 i _ x C.one) =
      algebraPure f g (i+1) 0 (i+1) _ (B.complex.d i (i+1) x) C.one
    rw [d_pure g i 0 i (add_zero i), show d[regular C,0] C.one = 0 from C.toDGAlgebra.d_id (),
      ← pair_apply g (M := restrict f (regular B)) (N := regular C) i (0+1) (i+1) rfl x 0, map_zero, smul_zero, add_zero])
  map_one := rfl
  map_mul i j n h x y := by
    change algebraPure f g n 0 n _ (B.mul i j n h x y) C.one =
      algebraMul f g i j n h (algebraPure f g i 0 i _ x C.one) (algebraPure f g j 0 j _ y C.one)
    rw [algebraMul_pure f g i 0 j 0 i j n 0 n _ _ h h rfl, zero_mul,
      Int.negOnePow_zero, one_smul]
    exact congrArg (algebraPure f g n 0 n (add_zero n) (B.mul i j n h x y))
      (C.toDGAlgebra.comp_id 0 C.one).symm

/-- The second algebra map into the tensor product sends `y` to `1 ⊗ y`. -/
def algebraInr : C ⟶ algebraTensor f g where
  chainMap := chainOfDegrees (fun n => algebraPair f g 0 n n (zero_add n) B.one) (by
    intro j y
    change (algebraComplex f g).d j (j+1) (algebraPure f g 0 j j _ B.one y) =
      algebraPure f g 0 (j+1) (j+1) _ B.one (C.complex.d j (j+1) y)
    rw [d_pure g 0 j j (zero_add j), show d[restrict f (regular B),0] B.one = 0 from B.toDGAlgebra.d_id (),
      ← pair_apply g (M := restrict f (regular B)) (N := regular C) (0+1) j (j+1) (by omega) 0 y, map_zero, LinearMap.zero_apply, Int.negOnePow_zero,
      one_smul, zero_add])
  map_one := rfl
  map_mul i j n h x y := by
    change algebraPure f g 0 n n _ B.one (C.mul i j n h x y) =
      algebraMul f g i j n h (algebraPure f g 0 i i _ B.one x) (algebraPure f g 0 j j _ B.one y)
    rw [algebraMul_pure f g 0 i 0 j i j 0 n n _ _ h rfl h, mul_zero,
      Int.negOnePow_zero, one_smul]
    exact congrArg (fun z => algebraPure f g 0 n n (zero_add n) z (C.mul i j n h x y))
      (B.toDGAlgebra.comp_id 0 B.one).symm

theorem algebraInl_comp : f ≫ algebraInl f g = g ≫ algebraInr f g := by
  apply CommDGAlgebra.Hom.ext_chainMap
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change algebraPure f g n 0 n _ (f.chainMap.f n a) C.one =
    algebraPure f g 0 n n _ B.one (g.chainMap.f n a)
  have e := algebraPure_balance f g 0 n 0 n n n (zero_add n) (add_zero n) (add_zero n) B.one a C.one
  rw [mul_zero, Int.negOnePow_zero, one_smul] at e
  simpa only [B.toDGAlgebra.id_comp, C.toDGAlgebra.id_comp] using e

variable {D : Affine.CommDGAlgebra.{u,v} k} (r : B ⟶ D) (s : C ⟶ D)
variable (e : f ≫ r = g ≫ s)

include e in
private theorem baseMap_eq (i : ℤ) (x : A.complex.X i) :
    r.chainMap.f i (f.chainMap.f i x) = s.chainMap.f i (g.chainMap.f i x) :=
  congrArg (fun t : A ⟶ D => t.chainMap.f i x) e

include e in
private def algebraDescDegree (n : ℤ) : (algebraComplex f g).X n →ₗ[k] D.complex.X n :=
  liftDegree (f := g) (M := restrict f (regular B)) (N := regular C)
    (fun i j h => ((D.mul i j n h).comp (r.chainMap.f i).hom).compl₂ (s.chainMap.f j).hom)
    (by
      intro i l j h x a y
      change D.mul (i+l) j n h (r.chainMap.f (i+l) (B.mul i l (i+l) rfl x (f.chainMap.f l a)))
          (s.chainMap.f j y) =
        D.mul i (l+j) n (by omega) (r.chainMap.f i x)
          (s.chainMap.f (l+j) (signedLeft (regular C) l j (l+j) rfl (g.chainMap.f l a) y))
      rw [r.map_mul, mul_assoc_at D i l j (i+l) (l+j) n rfl rfl h,
        baseMap_eq f g r s e, D.graded_comm l j (l+j) rfl, signedLeft_apply]
      simp only [Units.smul_def, map_zsmul]
      change _ = (l*j).negOnePow.val • D.mul i (l+j) n _
        (r.chainMap.f i x) (s.chainMap.f (l+j) (C.mul j l (l+j) _ y (g.chainMap.f l a)))
      rw [s.map_mul])

theorem algebraDescDegree_pure (i j n : ℤ) (h : i+j=n) (x : B.complex.X i) (y : C.complex.X j) :
    algebraDescDegree f g r s e n (algebraPure f g i j n h x y) =
      D.mul i j n h (r.chainMap.f i x) (s.chainMap.f j y) := by
  unfold algebraDescDegree
  erw [liftDegree_pure]
  rfl

private theorem shuffle
    (a b c d n : ℤ) (h : a+b+(c+d)=n)
    (x : D.complex.X a) (y : D.complex.X b) (z : D.complex.X c) (w : D.complex.X d) :
    D.mul (a+b) (c+d) n h (D.mul a b (a+b) rfl x y) (D.mul c d (c+d) rfl z w) =
      (b*c).negOnePow • D.mul (a+c) (b+d) n (by omega) (D.mul a c (a+c) rfl x z)
        (D.mul b d (b+d) rfl y w) := by
  rw [mul_assoc_at D a b (c+d) (a+b) (b+c+d) n rfl (by omega) h,
    ← mul_assoc_at D b c d (b+c) (c+d) (b+c+d) rfl rfl rfl,
    D.graded_comm b c (b+c) rfl y z]
  simp only [Units.smul_def, map_zsmul, LinearMap.smul_apply]
  rw [mul_assoc_at D c b d (b+c) (b+d) (b+c+d) (by omega) rfl rfl,
    ← mul_assoc_at D a c (b+d) (a+c) (b+c+d) n rfl (by omega) (by omega)]

/-- The common extension of two compatible maps of cdgas. -/
def algebraDesc (r : B ⟶ D) (s : C ⟶ D) (e : f ≫ r = g ≫ s) : algebraTensor f g ⟶ D where
  chainMap := chainOfDegrees (algebraDescDegree f g r s e) (by
    intro n z
    have eq : (D.complex.d n (n+1)).hom.comp (algebraDescDegree f g r s e n) =
        (algebraDescDegree f g r s e (n+1)).comp ((algebraComplex f g).d n (n+1)).hom := by
      apply pure_ext
      intro i j h x y
      change D.complex.d n (n+1) (algebraDescDegree f g r s e n (algebraPure f g i j n h x y)) =
        algebraDescDegree f g r s e (n+1) ((algebraComplex f g).d n (n+1) (algebraPure f g i j n h x y))
      rw [algebraDescDegree_pure, D.toDGAlgebra.leibniz (a := ()) (b := ()) (c := ()),
        d_algebraPure, map_add]
      simp only [Units.smul_def, map_zsmul]
      rw [algebraDescDegree_pure, algebraDescDegree_pure]
      have hr := CategoryTheory.congr_fun (r.chainMap.comm i (i+1)) x
      have hs := CategoryTheory.congr_fun (s.chainMap.comm j (j+1)) y
      simp only [ModuleCat.comp_apply] at hr hs
      rw [hr, hs]
    exact LinearMap.congr_fun eq z)
  map_one := by
    change algebraDescDegree f g r s e 0 (algebraOne f g) = D.one
    rw [algebraOne, algebraDescDegree_pure, r.map_one, s.map_one]
    exact D.toDGAlgebra.id_comp 0 D.one
  map_mul i j n h x y := by
    have eq : (algebraMul f g i j n h).compr₂ (algebraDescDegree f g r s e n) =
        ((D.mul i j n h).comp (algebraDescDegree f g r s e i)).compl₂
          (algebraDescDegree f g r s e j) := by
      apply pure_ext
      intro a b hab x₁ y₁
      apply pure_ext
      intro c d hcd x₂ y₂
      change algebraDescDegree f g r s e n (algebraMul f g i j n h
          (algebraPure f g a b i hab x₁ y₁) (algebraPure f g c d j hcd x₂ y₂)) =
        D.mul i j n h (algebraDescDegree f g r s e i (algebraPure f g a b i hab x₁ y₁))
          (algebraDescDegree f g r s e j (algebraPure f g c d j hcd x₂ y₂))
      rw [algebraMul_pure f g a b c d i j (a+c) (b+d) n hab hcd h rfl rfl]
      simp only [Units.smul_def, map_zsmul]
      rw [algebraDescDegree_pure, algebraDescDegree_pure, algebraDescDegree_pure,
        r.map_mul, s.map_mul]
      subst i j
      exact (shuffle (D := D) a b c d n h (r.chainMap.f a x₁) (s.chainMap.f b y₁)
        (r.chainMap.f c x₂) (s.chainMap.f d y₂)).symm
    exact LinearMap.congr_fun (LinearMap.congr_fun eq x) y

theorem algebraDesc_pure (i j n : ℤ) (h : i+j=n) (x : B.complex.X i) (y : C.complex.X j) :
    (algebraDesc f g r s e).chainMap.f n (algebraPure f g i j n h x y) =
      D.mul i j n h (r.chainMap.f i x) (s.chainMap.f j y) :=
  algebraDescDegree_pure f g r s e i j n h x y

theorem algebraInl_desc : algebraInl f g ≫ algebraDesc f g r s e = r := by
  apply CommDGAlgebra.Hom.ext_chainMap
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change algebraDescDegree f g r s e i (algebraPure f g i 0 i _ x C.one) = _
  rw [algebraDescDegree_pure, s.map_one]
  exact D.toDGAlgebra.comp_id i _

theorem algebraInr_desc : algebraInr f g ≫ algebraDesc f g r s e = s := by
  apply CommDGAlgebra.Hom.ext_chainMap
  apply HomologicalComplex.hom_ext
  intro j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change algebraDescDegree f g r s e j (algebraPure f g 0 j j _ B.one y) = _
  rw [algebraDescDegree_pure, r.map_one]
  exact D.toDGAlgebra.id_comp j _

theorem algebraPure_factor (i j n : ℤ) (h : i+j=n) (x : B.complex.X i) (y : C.complex.X j) :
    (algebraTensor f g).mul i j n h ((algebraInl f g).chainMap.f i x) ((algebraInr f g).chainMap.f j y) =
      algebraPure f g i j n h x y := by
  change algebraMul f g i j n h (algebraPure f g i 0 i _ x C.one) (algebraPure f g 0 j j _ B.one y) = _
  rw [algebraMul_pure f g i 0 0 j i j i j n _ _ h (add_zero i) (zero_add j),
    zero_mul, Int.negOnePow_zero, one_smul]
  exact congrArg₂ (algebraPure f g i j n h) (B.toDGAlgebra.comp_id i x) (C.toDGAlgebra.id_comp j y)

theorem algebraTensor_hom_ext {r s : algebraTensor f g ⟶ D}
    (hl : algebraInl f g ≫ r = algebraInl f g ≫ s)
    (hr : algebraInr f g ≫ r = algebraInr f g ≫ s) : r = s := by
  apply CommDGAlgebra.Hom.ext_chainMap
  apply HomologicalComplex.hom_ext
  intro n
  on_pure
  intro i j h x y
  change r.chainMap.f n (algebraPure f g i j n h x y) = s.chainMap.f n (algebraPure f g i j n h x y)
  rw [← algebraPure_factor f g i j n h x y, r.map_mul, s.map_mul]
  exact congrArg₂ (fun x y => D.mul i j n h x y)
    (congrArg (fun t : B ⟶ D => t.chainMap.f i x) hl)
    (congrArg (fun t : C ⟶ D => t.chainMap.f j y) hr)

/-- A tensor of commutative dg algebras is their coproduct under the base. -/
theorem algebraTensor_coproduct (e : f ≫ r = g ≫ s) :
    ∃! t : algebraTensor f g ⟶ D, algebraInl f g ≫ t = r ∧ algebraInr f g ≫ t = s :=
  ⟨algebraDesc f g r s e, ⟨algebraInl_desc f g r s e, algebraInr_desc f g r s e⟩,
    fun _ ht => algebraTensor_hom_ext f g (ht.1.trans (algebraInl_desc f g r s e).symm)
      (ht.2.trans (algebraInr_desc f g r s e).symm)⟩


end Algebra


section Associativity

set_option maxHeartbeats 800000

variable (f : A ⟶ B) (g : B ⟶ C) (M : A.Module) (N : B.Module) (P : C.Module)

theorem signedLeft_pure (l i j n li q : ℤ) (h : i+j=n) (h' : l+i=li) (e : l+n=q)
    (a : B.complex.X l) (x : term N i) (y : term P j) :
    signedLeft (tensor g N P) l n q e (g.chainMap.f l a) (pure g i j n h x y) =
      pure g li j q (by omega) (signedLeft N l i li h' a x) y := by
  rw [signedLeft_apply, act_pure, signedLeft_apply]
  have hb := pure_balance g i l j li (j+l) q (by omega) (by omega) (by omega) x a y
  rw [signedLeft_apply] at hb
  simp only [Units.smul_def] at hb ⊢
  rw [pure_zsmul_left, hb, pure_zsmul_right, smul_smul, ← Units.val_mul, ← Int.negOnePow_add,
    show l*n=l*i+l*j by rw [← h,mul_add]]

private abbrev associateSource := tensor g (tensor f M N) P
private abbrev associateTarget := tensor (f ≫ g) M (tensor g N P)

private def associateRight (n ij l : ℤ) (h : ij+l=n) :
    term (tensor f M N) ij →ₗ[k] term P l →ₗ[k] term (associateTarget f g M N P) n :=
  liftDegree (f := f) (M := M) (N := N)
    (fun i j hij =>
      ((LinearMap.llcomp k (term P l) (term (tensor g N P) (j+l))
          (term (associateTarget f g M N P) n)).compl₂ (pair g j l (j+l) rfl)).comp
        (pair (f ≫ g) i (j+l) n (by omega)))
    (by
      intro i a j hij x z y
      apply LinearMap.ext
      intro w
      change pure (f ≫ g) (N := tensor g N P) (i+a) (j+l) n _ (act M i a (i+a) rfl x z)
          (pure g j l (j+l) rfl y w) =
        pure (f ≫ g) (N := tensor g N P) i ((a+j)+l) n _ x
          (pure g (a+j) l ((a+j)+l) rfl (signedLeft N a j (a+j) rfl (f.chainMap.f a z) y) w)
      rw [pure_balance (f ≫ g) i a (j+l) (i+a) (a+j+l) n rfl (by omega) (by omega),
        show (f ≫ g).chainMap.f a z = g.chainMap.f a (f.chainMap.f a z) from rfl,
        signedLeft_pure g N P a j l (j+l) (a+j) (a+j+l) rfl rfl (by omega)])

private theorem associateRight_pure (n ij l : ℤ) (h : ij+l=n)
    (i j jl : ℤ) (hij : i+j=ij) (hjl : j+l=jl) (x : term M i) (y : term N j) (z : term P l) :
    associateRight f g M N P n ij l h (pure f i j ij hij x y) z =
      pure (f ≫ g) (N := tensor g N P) i jl n (by omega) x (pure g j l jl hjl y z) := by
  subst jl
  unfold associateRight
  erw [liftDegree_pure]
  rfl

private def associateForward (n : ℤ) :
    term (associateSource f g M N P) n →ₗ[k] term (associateTarget f g M N P) n :=
  liftDegree (f := g) (M := tensor f M N) (N := P) (associateRight f g M N P n)
    (by
      intro ij a l h z b w
      have eq :
          ((associateRight f g M N P n (ij+a) l h).flip w).comp
            ((act (tensor f M N) ij a (ij+a) rfl).flip b) =
          (associateRight f g M N P n ij (a+l) (by omega)).flip
            (signedLeft P a l (a+l) rfl (g.chainMap.f a b) w) := by
        apply pure_ext
        intro i j e x y
        rw [LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.flip_apply, LinearMap.flip_apply,
          act_pure,
          associateRight_pure f g M N P n (ij+a) l h i (j+a) (j+a+l) (by omega) rfl,
          associateRight_pure f g M N P n ij (a+l) (by omega) i j (j+a+l) e (by omega),
          pure_balance g j a l (j+a) (a+l) (j+a+l) rfl rfl rfl]
      exact LinearMap.congr_fun eq z)

private theorem associateForward_pure (i j l ij n : ℤ) (e : i+j=ij) (h : ij+l=n)
    (x : term M i) (y : term N j) (z : term P l) :
    associateForward f g M N P n (pure g ij l n h (pure f i j ij e x y) z) =
      pure (f ≫ g) (N := tensor g N P) i (j+l) n (by omega) x (pure g j l (j+l) rfl y z) := by
  unfold associateForward
  erw [liftDegree_pure]
  exact associateRight_pure f g M N P n ij l h i j (j+l) e rfl x y z

private def associateLeft (n i jl : ℤ) (h : i+jl=n) (x : term M i) :
    term (tensor g N P) jl →ₗ[k] term (associateSource f g M N P) n :=
  liftDegree (f := g) (M := N) (N := P)
    (fun j l hjl => (pair g (i+j) l n (by omega)).comp (pair f i j (i+j) rfl x))
    (by
      intro j a l hij y b z
      change pure g (M := tensor f M N) (i+(j+a)) l n (by omega)
          (pure f i (j+a) (i+(j+a)) rfl x (act N j a (j+a) rfl y b)) z =
        pure g (M := tensor f M N) (i+j) (a+l) n (by omega) (pure f i j (i+j) rfl x y)
          (signedLeft P a l (a+l) rfl (g.chainMap.f a b) z)
      rw [← act_pure f i j (i+j) a (i+(j+a)) rfl (by omega),
        pure_balance g (i+j) a l (i+(j+a)) (a+l) n (by omega) rfl (by omega)])

private theorem associateLeft_pure (n i jl : ℤ) (h : i+jl=n)
    (j l ij : ℤ) (hjl : j+l=jl) (hij : i+j=ij) (x : term M i) (y : term N j) (z : term P l) :
    associateLeft f g M N P n i jl h x (pure g j l jl hjl y z) =
      pure g ij l n (by omega) (pure f i j ij hij x y) z := by
  subst ij
  unfold associateLeft
  rw [liftDegree_pure]
  rfl

private abbrev associateLeftBilinear (n i jl : ℤ) (h : i+jl=n) :
    term M i →ₗ[k] term (tensor g N P) jl →ₗ[k] term (associateSource f g M N P) n :=
  { toFun := associateLeft f g M N P n i jl h
    map_add' := by
      intro x x'
      apply pure_ext
      intro j l e y z
      rw [LinearMap.add_apply,
        associateLeft_pure f g M N P n i jl h j l (i+j) e rfl,
        associateLeft_pure f g M N P n i jl h j l (i+j) e rfl,
        associateLeft_pure f g M N P n i jl h j l (i+j) e rfl]
      simp only [← pair_apply, map_add, LinearMap.add_apply]
    map_smul' := by
      intro t x
      apply pure_ext
      intro j l e y z
      rw [RingHom.id_apply, LinearMap.smul_apply,
        associateLeft_pure f g M N P n i jl h j l (i+j) e rfl,
        associateLeft_pure f g M N P n i jl h j l (i+j) e rfl]
      simp only [← pair_apply, map_smul, LinearMap.smul_apply] }

private def associateBackward (n : ℤ) :
    term (associateTarget f g M N P) n →ₗ[k] term (associateSource f g M N P) n :=
  liftDegree (f := f ≫ g) (M := M) (N := tensor g N P) (associateLeftBilinear f g M N P n)
    (by
      intro i a jl h x b z
      suffices e : associateLeft f g M N P n (i+a) jl h (act M i a (i+a) rfl x b) =
        associateLeft f g M N P n i (a+jl) (by omega) x ∘ₗ
          signedLeft (tensor g N P) a jl (a+jl) rfl ((f ≫ g).chainMap.f a b) from LinearMap.congr_fun e z
      apply pure_ext
      intro j l e y w
      change associateLeft f g M N P n (i+a) jl h (act M i a (i+a) rfl x b)
          (pure g j l jl e y w) =
        associateLeft f g M N P n i (a+jl) (by omega) x
          (signedLeft (tensor g N P) a jl (a+jl) rfl (g.chainMap.f a (f.chainMap.f a b))
            (pure g j l jl e y w))
      rw [signedLeft_pure g N P a j l jl (a+j) (a+jl) e rfl rfl,
        associateLeft_pure f g M N P n (i+a) jl h j l (i+a+j) e rfl,
        associateLeft_pure f g M N P n i (a+jl) (by omega) (a+j) l (i+a+j) (by omega) (by omega),
        pure_balance f i a j (i+a) (a+j) (i+a+j) rfl rfl rfl])

private theorem associateBackward_pure (i j l jl n : ℤ) (e : j+l=jl) (h : i+jl=n)
    (x : term M i) (y : term N j) (z : term P l) :
    associateBackward f g M N P n (pure (f ≫ g) (N := tensor g N P) i jl n h x (pure g j l jl e y z)) =
      pure g (i+j) l n (by omega) (pure f i j (i+j) rfl x y) z := by
  unfold associateBackward
  erw [liftDegree_pure]
  exact associateLeft_pure f g M N P n i jl h j l (i+j) e rfl x y z

private theorem associateForward_backward (n : ℤ) :
    (associateForward f g M N P n).comp (associateBackward f g M N P n) = LinearMap.id := by
  apply pure_ext
  intro i jl h x z
  have e : ((associateForward f g M N P n).comp (associateBackward f g M N P n)).comp
        (pair (f ≫ g) i jl n h x) = pair (f ≫ g) i jl n h x := by
    apply pure_ext
    intro j l hjl y w
    change associateForward f g M N P n
      (associateBackward f g M N P n (pure (f ≫ g) (N := tensor g N P) i jl n h x
        (pure g j l jl hjl y w))) = _
    rw [associateBackward_pure, associateForward_pure]
    subst jl
    rfl
  exact LinearMap.congr_fun e z

private theorem associateBackward_forward (n : ℤ) :
    (associateBackward f g M N P n).comp (associateForward f g M N P n) = LinearMap.id := by
  apply pure_ext
  intro ij l h z w
  have e : ((associateBackward f g M N P n).comp (associateForward f g M N P n)).comp
        ((pair g ij l n h).flip w) = (pair g ij l n h).flip w := by
    apply pure_ext
    intro i j hij x y
    change associateBackward f g M N P n
      (associateForward f g M N P n (pure g (M := tensor f M N) ij l n h
        (pure f i j ij hij x y) w)) = _
    rw [associateForward_pure, associateBackward_pure]
    subst ij
    rfl
  exact LinearMap.congr_fun e z

private theorem nestedPure_degree (i j l n s t : ℤ) (hs : j+l=s) (ht : j+l=t)
    (es : i+s=n) (et : i+t=n) (x : term M i) (y : term N j) (w : term P l) :
    pure (f ≫ g) (N := tensor g N P) i s n es x (pure g j l s hs y w) =
      pure (f ≫ g) (N := tensor g N P) i t n et x (pure g j l t ht y w) := by
  subst s t
  rfl

private theorem associateForward_d (n : ℤ) (z : term (associateSource f g M N P) n) :
    d[associateTarget f g M N P,n] (associateForward f g M N P n z) =
      associateForward f g M N P (n+1) (d[associateSource f g M N P,n] z) := by
  let L := (d[associateTarget f g M N P,n]).hom.comp (associateForward f g M N P n)
  let R := (associateForward f g M N P (n+1)).comp (d[associateSource f g M N P,n]).hom
  have e : L = R := by
    apply pure_ext
    intro ij l h z w
    have ez : L.comp ((pair g ij l n h).flip w) = R.comp ((pair g ij l n h).flip w) := by
      apply pure_ext
      intro i j hij x y
      change d[associateTarget f g M N P,n] (associateForward f g M N P n
          (pure g ij l n h (pure f i j ij hij x y) w)) =
        associateForward f g M N P (n+1) (d[associateSource f g M N P,n]
          (pure g ij l n h (pure f i j ij hij x y) w))
      rw [associateForward_pure,
        d_pure (f ≫ g) (M := M) (N := tensor g N P) i (j+l) n _ x _,
        d_pure g (M := tensor f M N) (N := P) ij l n h _ w,
        d_pure f i j ij hij x y, d_pure g j l (j+l) rfl y w]
      simp only [Units.smul_def]
      rw [pure_add_left g (M := tensor f M N) (N := P) (ij+1) l (n+1) _ _ _ w,
        pure_zsmul_left g (M := tensor f M N) (N := P) (ij+1) l (n+1) _ _ _ w,
        pure_add_right (f ≫ g) (M := M) (N := tensor g N P) i (j+l+1) (n+1) _ x,
        pure_zsmul_right (f ≫ g) (M := M) (N := tensor g N P) i (j+l+1) (n+1) _ _ x]
      simp only [map_add, map_zsmul]
      rw [associateForward_pure, associateForward_pure, associateForward_pure]
      rw [nestedPure_degree f g M N P i (j+1) l (n+1) _ ((j+1)+l)
          (by omega) rfl _ (by omega) x,
        nestedPure_degree f g M N P i j (l+1) (n+1) (j+l+1) (j+(l+1))
          (by omega) rfl _ (by omega) x]
      have hs : ij.negOnePow = i.negOnePow * j.negOnePow := by rw [← hij, Int.negOnePow_add]
      rw [hs, Units.val_mul, smul_add, smul_smul]
      abel
    exact LinearMap.congr_fun ez z
  exact LinearMap.congr_fun e z

private theorem associateForward_act (n a q : ℤ) (h : n+a=q)
    (z : term (associateSource f g M N P) n) (c : C.complex.X a) :
    associateForward f g M N P q (act (associateSource f g M N P) n a q h z c) =
      act (associateTarget f g M N P) n a q h (associateForward f g M N P n z) c := by
  let L := (associateForward f g M N P q).comp ((act (associateSource f g M N P) n a q h).flip c)
  let R := ((act (associateTarget f g M N P) n a q h).flip c).comp (associateForward f g M N P n)
  have e : L = R := by
    apply pure_ext
    intro ij l h' z w
    have ez : L.comp ((pair g ij l n h').flip w) = R.comp ((pair g ij l n h').flip w) := by
      apply pure_ext
      intro i j hij x y
      change associateForward f g M N P q (act (associateSource f g M N P) n a q h
          (pure g ij l n h' (pure f i j ij hij x y) w) c) =
        act (associateTarget f g M N P) n a q h (associateForward f g M N P n
          (pure g ij l n h' (pure f i j ij hij x y) w)) c
      rw [act_pure g, associateForward_pure, associateForward_pure, act_pure (f ≫ g)]
      rw [act_pure g j l (j+l) a (j+l+a) rfl rfl y w c]
      exact nestedPure_degree f g M N P i j (l+a) q (j+(l+a)) (j+l+a)
        rfl (by omega) _ _ x y _
    exact LinearMap.congr_fun ez z
  exact LinearMap.congr_fun e z

/-- Reassociate three balanced tensor factors along composable algebra maps. -/
def associate : associateSource f g M N P ≅ associateTarget f g M N P where
  hom := homOfDegrees (associateForward f g M N P) (associateForward_d f g M N P)
    (associateForward_act f g M N P)
  inv := homOfDegrees (associateBackward f g M N P)
    (by
      intro n z
      have hl := fun m x => LinearMap.congr_fun (associateBackward_forward f g M N P m) x
      have hr := fun m x => LinearMap.congr_fun (associateForward_backward f g M N P m) x
      have e := congrArg (associateBackward f g M N P (n+1))
        (associateForward_d f g M N P n (associateBackward f g M N P n z))
      change associateBackward f g M N P (n+1) (d[associateTarget f g M N P,n]
        (((associateForward f g M N P n).comp (associateBackward f g M N P n)) z)) =
        ((associateBackward f g M N P (n+1)).comp (associateForward f g M N P (n+1))) _ at e
      rw [hr, hl] at e
      exact e.symm)
    (by
      intro i j n h z a
      have hl := fun m x => LinearMap.congr_fun (associateBackward_forward f g M N P m) x
      have hr := fun m x => LinearMap.congr_fun (associateForward_backward f g M N P m) x
      have e := congrArg (associateBackward f g M N P n)
        (associateForward_act f g M N P i j n h (associateBackward f g M N P i z) a)
      change ((associateBackward f g M N P n).comp (associateForward f g M N P n)) _ =
        associateBackward f g M N P n (act (associateTarget f g M N P) i j n h
          (((associateForward f g M N P i).comp (associateBackward f g M N P i)) z) a) at e
      rw [hl, hr] at e
      exact e.symm)
  hom_inv_id := by
    apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    exact associateBackward_forward f g M N P n
  inv_hom_id := by
    apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    exact associateForward_backward f g M N P n

theorem associate_pure (i j l ij n : ℤ) (e : i+j=ij) (h : ij+l=n)
    (x : term M i) (y : term N j) (z : term P l) :
    ((associate f g M N P).hom.app ()).f n (pure g ij l n h (pure f i j ij e x y) z) =
      pure (f ≫ g) (N := tensor g N P) i (j+l) n (by omega) x (pure g j l (j+l) rfl y z) :=
  associateForward_pure f g M N P i j l ij n e h x y z


end Associativity


section SecondGradedMap

variable (f : A ⟶ B) (M : A.Module) {N N' : B.Module} {r : ℤ}

private theorem graded_signedLeft (w : gradedHom N N' r)
    (l j t jr tr : ℤ) (h : l+j=t) (hj : j+r=jr) (ht : t+r=tr)
    (a : B.complex.X l) (y : term N j) :
    component w () t tr ht (signedLeft N l j t h a y) =
      (l*r).negOnePow • signedLeft N' l jr tr (by omega) a (component w () j jr hj y) := by
  simp only [signedLeft_apply, Units.smul_def, map_zsmul, smul_smul, ← Units.val_mul,
    ← Int.negOnePow_add]
  rw [w.property (a := ()) (b := ()) j l t jr tr (by omega) hj ht y a]
  have hs : l*r + l*jr = l*j + 2*(l*r) := by subst jr; ring
  rw [hs, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

private def secondGradedDegree (w : gradedHom N N' r) (n q : ℤ) (e : n+r=q) :
    term (tensor f M N) n →ₗ[k] term (tensor f M N') q :=
  liftDegree (fun i j _ =>
    (i*r).negOnePow • (pair f i (j+r) q (by omega)).compl₂ (component w () j (j+r) rfl).hom) (by
    intro i l j h x a y
    change ((i+l)*r).negOnePow • pure f (i+l) (j+r) q (by omega)
        (act M i l (i+l) rfl x a) (component w () j (j+r) rfl y) =
      (i*r).negOnePow • pure f i (l+j+r) q (by omega) x
        (component w () (l+j) (l+j+r) rfl
          (signedLeft N l j (l+j) rfl (f.chainMap.f l a) y))
    rw [pure_balance f i l (j+r) (i+l) (l+j+r) q rfl (by omega) (by omega) x a,
      graded_signedLeft w l j (l+j) (j+r) (l+j+r) rfl rfl rfl _ y]
    simp only [Units.smul_def, pure_zsmul_right, smul_smul, ← Units.val_mul,
      ← Int.negOnePow_add, add_mul])

private theorem secondGradedDegree_pure (w : gradedHom N N' r) (i j n jr q : ℤ)
    (h : i+j=n) (hj : j+r=jr) (e : n+r=q) (x : term M i) (y : term N j) :
    secondGradedDegree f M w n q e (pure f i j n h x y) =
      (i*r).negOnePow • pure f i jr q (by omega) x (component w () j jr hj y) := by
  subst jr
  rw [secondGradedDegree, liftDegree_pure]
  rfl

/-- Tensoring a homogeneous map in the second variable uses the sign `(-1)^(i*r)`. -/
def mapSecondGraded (w : gradedHom N N' r) : gradedHom (tensor f M N) (tensor f M N') r :=
  ⟨fun _ => Cochain.mk fun n q e => ModuleCat.ofHom (secondGradedDegree f M w n q e), by
    rintro ⟨⟩ ⟨⟩ n l p nr pr h e hp z a
    have eq : (secondGradedDegree f M w p pr hp).comp ((act (tensor f M N) n l p h).flip a) =
        ((act (tensor f M N') nr l pr (by omega)).flip a).comp
          (secondGradedDegree f M w n nr e) := by
      apply pure_ext
      intro i j hij x y
      simp only [LinearMap.comp_apply, LinearMap.flip_apply]
      rw [act_pure, secondGradedDegree_pure f M w i (j+l) p (j+l+r) pr _ rfl hp,
        secondGradedDegree_pure f M w i j n (j+r) nr hij rfl e]
      simp only [Units.smul_def, map_zsmul, LinearMap.smul_apply]
      rw [w.property (a := ()) (b := ()) j l (j+l) (j+r) (j+l+r) rfl rfl rfl y a]
      have ev := act_pure f (M := M) (N := N') i (j+r) nr l pr (by omega) (by omega)
        x (component w () j (j+r) rfl y) a
      rw [ev]
      let y' := component w () j (j+r) rfl y
      have hdeg (t : ℤ) (ht : j+r+l=t) (et : i+t=pr) :
          pure f (N := N') i t pr et x (act N' (j+r) l t ht y' a) =
            pure f (N := N') i (j+r+l) pr (by omega) x (act N' (j+r) l (j+r+l) rfl y' a) := by
        subst t
        rfl
      exact congrArg (fun z : term (tensor f M N') pr => (i*r).negOnePow.val • z)
        (hdeg (j+l+r) (by omega) (by omega))
    exact LinearMap.congr_fun eq z⟩

theorem map_second_graded_pure (w : gradedHom N N' r) (i j n jr q : ℤ)
    (h : i+j=n) (hj : j+r=jr) (e : n+r=q) (x : term M i) (y : term N j) :
    component (mapSecondGraded f M w) () n q e (pure f i j n h x y) =
      (i*r).negOnePow • pure f i jr q (by omega) x (component w () j jr hj y) :=
  secondGradedDegree_pure f M w i j n jr q h hj e x y

end SecondGradedMap

open Specs.DerivedFormalization.DG.HomComplex (HomotopyEquation) in
theorem map_second_homotopy (f : A ⟶ B) (M : A.Module) {N N' : B.Module}
    (g g' : N ⟶ N') (w : gradedHom N N' (-1)) (hw : HomotopyEquation g g' w) :
    HomotopyEquation (mapSecond f M g) (mapSecond f M g') (mapSecondGraded f M w) := by
  rintro ⟨⟩ n z
  let L := fun n q e => (component (mapSecondGraded f M w) () n q e).hom
  let G := fun n => ((mapSecond f M g).app ()).f n
  let G' := fun n => ((mapSecond f M g').app ()).f n
  change G n z - G' n z = ((tensor f M N').complex ()).d (n-1) n (L n (n-1) (by omega) z) +
    L (n+1) n (by omega) (d[tensor f M N,n] z)
  have e : (G n).hom - (G' n).hom =
      (((tensor f M N').complex ()).d (n-1) n).hom.comp (L n (n-1) (by omega)) +
        (L (n+1) n (by omega)).comp (d[tensor f M N,n]).hom := by
    apply pure_ext
    intro i j h x y
    change G n (pure f i j n h x y) - G' n (pure f i j n h x y) =
      ((tensor f M N').complex ()).d (n-1) n
          (component (mapSecondGraded f M w) () n (n-1) (by omega) (pure f i j n h x y)) +
        component (mapSecondGraded f M w) () (n+1) n (by omega)
          (d[tensor f M N,n] (pure f i j n h x y))
    rw [map_second_pure, map_second_pure,
      map_second_graded_pure f M w i j n (j-1) (n-1) h (by omega) (by omega)]
    simp only [Units.smul_def, map_zsmul]
    rw [d_pure_at f i (j-1) (n-1) (i+1) j n _ rfl (by omega) (by omega),
      d_pure f i j n h x y, map_add]
    simp only [Units.smul_def, map_zsmul]
    rw [map_second_graded_pure f M w (i+1) j (n+1) (j-1) n (by omega) (by omega) (by omega),
      map_second_graded_pure f M w i (j+1) (n+1) j n (by omega) (by omega) (by omega)]
    have hs : (i*(-1)).negOnePow = i.negOnePow := by
      rw [show i*(-1) = -i by ring, Int.negOnePow_neg]
    have ht : ((i+1)*(-1)).negOnePow = -i.negOnePow := by
      rw [show (i+1)*(-1) = -(i+1) by ring, Int.negOnePow_neg, Int.negOnePow_succ]
    simp only [hs, ht, Units.smul_def, Units.val_neg, neg_smul, smul_add, smul_smul,
      ← Units.val_mul, ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul,
      Units.val_one, one_zsmul]
    rw [← pair_apply f i j n h x ((g.app ()).f j y),
      ← pair_apply f i j n h x ((g'.app ()).f j y),
      ← map_sub, hw () j y, map_add, pair_apply, pair_apply]
    abel
  exact LinearMap.congr_fun e z

section AlgebraCompatibility

variable (f : A ⟶ B) (g : A ⟶ C)

/-- The right action of the second algebra is multiplication by its image in the coproduct. -/
theorem algebraTensor_action (n l q : ℤ) (h : n+l=q)
    (z : (algebraComplex f g).X n) (c : C.complex.X l) :
    (algebraTensor f g).mul n l q h z ((algebraInr f g).chainMap.f l c) =
      act (algebraModule f g) n l q h z c := by
  have e : ((algebraTensor f g).mul n l q h).flip ((algebraInr f g).chainMap.f l c) =
      (act (algebraModule f g) n l q h).flip c := by
    apply pure_ext (f := g) (M := restrict f (regular B)) (N := regular C)
    intro i j hij x y
    change algebraMul f g n l q h (algebraPure f g i j n hij x y)
        (algebraPure f g 0 l l (zero_add l) B.one c) =
      act (algebraModule f g) n l q h (algebraPure f g i j n hij x y) c
    rw [algebraMul_pure f g i j 0 l n l i (j+l) q hij (zero_add l) h (add_zero i) rfl,
      mul_zero, Int.negOnePow_zero, one_smul, B.toDGAlgebra.comp_id]
    exact (act_pure g i j n l q hij h x y c).symm
  exact LinearMap.congr_fun e z

/-- Restricting the regular module of the coproduct along the second inclusion
recovers the signed module tensor, on the same underlying complex. -/
def algebraModuleIso : algebraModule f g ≅ restrict (algebraInr f g) (regular (algebraTensor f g)) where
  hom := ⟨fun _ => 𝟙 _, by
    rintro ⟨⟩ ⟨⟩ i j n h x a
    exact (algebraTensor_action f g i j n h x a).symm⟩
  inv := ⟨fun _ => 𝟙 _, by
    rintro ⟨⟩ ⟨⟩ i j n h x a
    exact algebraTensor_action f g i j n h x a⟩
  hom_inv_id := RightDGModuleModel.hom_ext fun _ => Category.id_comp _
  inv_hom_id := RightDGModuleModel.hom_ext fun _ => Category.id_comp _

theorem algebraTensor_nonpositive (hB : B.IsNonpositive) (hC : C.IsNonpositive) :
    (algebraTensor f g).IsNonpositive := by
  intro n hn
  have H : (LinearMap.id : (algebraComplex f g).X n →ₗ[k] (algebraComplex f g).X n) = 0 := by
    apply pure_ext (f := g) (M := restrict f (regular B)) (N := regular C)
    intro i j h x y
    change algebraPure f g i j n h x y = 0
    by_cases hi : 0 < i
    · rw [@Subsingleton.elim (B.complex.X i) (hB i hi) x 0]
      change algebraPair f g i j n h 0 y = 0
      rw [map_zero, LinearMap.zero_apply]
    · have hj : 0 < j := by omega
      rw [@Subsingleton.elim (C.complex.X j) (hC j hj) y 0]
      exact map_zero (algebraPair f g i j n h x)
  exact ⟨fun x y => (LinearMap.congr_fun H x).trans (LinearMap.congr_fun H y).symm⟩

/-- The coproduct of nonpositive cdgas is nonpositive. -/
def nonpositiveTensor {A B C : Affine.NonpositiveCDGA.{u,v} k} (f : A ⟶ B) (g : A ⟶ C) :
    Affine.NonpositiveCDGA.{u,v} k :=
  ⟨algebraTensor f g, algebraTensor_nonpositive f g B.nonpositive C.nonpositive⟩

section AlgebraMap

variable {A' B' C' : Affine.CommDGAlgebra.{u,v} k}
variable (f' : A' ⟶ B') (g' : A' ⟶ C') {a : A ⟶ A'} (b : B ⟶ B') (c : C ⟶ C')
variable (hb : f ≫ b = a ≫ f') (hc : g ≫ c = a ≫ g')

/-- The map on tensor coproducts induced by a morphism of spans of dg algebras. -/
def algebraMap : algebraTensor f g ⟶ algebraTensor f' g' :=
  algebraDesc f g (b ≫ algebraInl f' g') (c ≫ algebraInr f' g') (by
    rw [← Category.assoc, ← Category.assoc, hb, hc, Category.assoc, Category.assoc,
      algebraInl_comp])

theorem algebraMap_pure (i j n : ℤ) (h : i+j=n) (x : B.complex.X i) (y : C.complex.X j) :
    (algebraMap f g f' g' b c hb hc).chainMap.f n (algebraPure f g i j n h x y) =
      algebraPure f' g' i j n h (b.chainMap.f i x) (c.chainMap.f j y) := by
  rw [algebraMap, algebraDesc_pure]
  exact algebraPure_factor f' g' i j n h _ _

theorem algebraMap_inl :
    algebraInl f g ≫ algebraMap f g f' g' b c hb hc = b ≫ algebraInl f' g' :=
  algebraInl_desc f g _ _ _

theorem algebraMap_inr :
    algebraInr f g ≫ algebraMap f g f' g' b c hb hc = c ≫ algebraInr f' g' :=
  algebraInr_desc f g _ _ _

end AlgebraMap

end AlgebraCompatibility

section ChangeOfScalars

variable (f : A ⟶ B) (g : B ⟶ C)

abbrev restrictFunctor : B.Module ⥤ A.Module :=
  Specs.DerivedFormalization.Affine.Tensor.restrictFunctor f

/-- Restriction along the composite agrees with successive restrictions. -/
theorem restrict_comp (P : C.Module) : restrict (f ≫ g) P = restrict f (restrict g P) := rfl

variable (N : B.Module)

private def leftUnitDegree (n : ℤ) : term (tensor f (regular A) N) n →ₗ[k] term N n :=
  liftDegree (fun i j h => (signedLeft N i j n h).comp (f.chainMap.f i).hom) (by
    intro i l j h x a y
    change signedLeft N (i+l) j n h (f.chainMap.f (i+l) (A.mul i l (i+l) rfl x a)) y =
      signedLeft N i (l+j) n (by omega) (f.chainMap.f i x)
        (signedLeft N l j (l+j) rfl (f.chainMap.f l a) y)
    rw [f.map_mul]
    exact signedLeft_assoc N i l j n h _ _ y)

private theorem leftUnitDegree_pure (i j n : ℤ) (h : i+j=n)
    (a : A.complex.X i) (y : term N j) :
    leftUnitDegree f N n (pure f (M := regular A) i j n h a y) =
      signedLeft N i j n h (f.chainMap.f i a) y :=
  by
    rw [leftUnitDegree, liftDegree_pure]
    rfl

private theorem signedLeft_one (n : ℤ) (y : term N n) :
    signedLeft N 0 n n (zero_add n) B.one y = y := by
  rw [signedLeft_apply, zero_mul, Int.negOnePow_zero, one_smul]
  exact N.act_id () n y

private def leftUnitHom : tensor f (regular A) N ⟶ N :=
  homOfDegrees (leftUnitDegree f N) (by
    intro n z
    let L := (d[N,n]).hom.comp (leftUnitDegree f N n)
    let R := (leftUnitDegree f N (n+1)).comp (d[tensor f (regular A) N,n]).hom
    have e : L = R := by
      apply pure_ext (f := f) (M := regular A) (N := N)
      intro i j h a y
      change d[N,n] (leftUnitDegree f N n (pure f (M := regular A) i j n h a y)) =
        leftUnitDegree f N (n+1) (d[tensor f (regular A) N,n] (pure f (M := regular A) i j n h a y))
      rw [leftUnitDegree_pure, signedLeft_d, d_pure f (M := regular A) (N := N), map_add]
      simp only [Units.smul_def, map_zsmul]
      rw [leftUnitDegree_pure, leftUnitDegree_pure]
      have e := CategoryTheory.congr_fun (f.chainMap.comm i (i+1)) a
      simp only [ModuleCat.comp_apply] at e
      rw [e]
    -- The component equation follows from the equality of linear maps.
    exact LinearMap.congr_fun e z)
    (by
      intro n l q h z b
      let L := (leftUnitDegree f N q).comp ((act (tensor f (regular A) N) n l q h).flip b)
      let R := ((act N n l q h).flip b).comp (leftUnitDegree f N n)
      have e : L = R := by
        apply pure_ext (f := f) (M := regular A) (N := N)
        intro i j e a y
        change leftUnitDegree f N q (act (tensor f (regular A) N) n l q h
          (pure f (M := regular A) i j n e a y) b) =
          act N n l q h (leftUnitDegree f N n (pure f (M := regular A) i j n e a y)) b
        rw [act_pure f (M := regular A) (N := N), leftUnitDegree_pure, leftUnitDegree_pure]
        exact signedLeft_right N i j l n (j+l) q e rfl h _ y b
      exact LinearMap.congr_fun e z)

private def leftUnitInv : N ⟶ tensor f (regular A) N :=
  homOfDegrees (fun n => pair f (M := regular A) 0 n n (zero_add n) A.one) (by
    intro n y
    change d[tensor f (regular A) N,n] (pure f (M := regular A) (N := N) 0 n n _ A.one y) =
      pure f (M := regular A) (N := N) 0 (n+1) (n+1) _ A.one (d[N,n] y)
    rw [d_pure f (M := regular A) (N := N), show d[regular A,0] A.one = 0 from A.toDGAlgebra.d_id (),
      ← pair_apply f (M := regular A) (N := N) (0+1) n (n+1) (by omega) 0 y,
      map_zero, LinearMap.zero_apply, Int.negOnePow_zero, one_smul, zero_add])
    (by
      intro i j n h y a
      subst n
      exact (act_pure f (M := regular A) (N := N) 0 i i j (i+j) (zero_add i) rfl A.one y a).symm)

/-- Tensoring the regular source module with a coefficient module evaluates the action. -/
def leftUnit : tensor f (regular A) N ≅ N where
  hom := leftUnitHom f N
  inv := leftUnitInv f N
  hom_inv_id := by
    apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    on_pure
    intro i j h a y
    change pure f (M := regular A) 0 n n (zero_add n) A.one
      (leftUnitDegree f N n (pure f (M := regular A) i j n h a y)) =
        pure f (M := regular A) i j n h a y
    rw [leftUnitDegree_pure]
    have e := pure_balance f (M := regular A) (N := N) 0 i j i n n (zero_add i) h h A.one a y
    rw [show act (regular A) 0 i i (zero_add i) A.one a = a from A.toDGAlgebra.id_comp i a] at e
    exact e.symm
  inv_hom_id := by
    apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    change leftUnitDegree f N n (pure f (M := regular A) 0 n n (zero_add n) A.one y) = y
    rw [leftUnitDegree_pure, f.map_one, signedLeft_one]

theorem leftUnit_pure (i j n : ℤ) (h : i+j=n) (a : A.complex.X i) (y : term N j) :
    (((leftUnit f N).hom.app ()).f n) (pure f (M := regular A) i j n h a y) =
      signedLeft N i j n h (f.chainMap.f i a) y :=
  leftUnitDegree_pure f N i j n h a y

theorem leftUnit_inv_pure (n : ℤ) (y : term N n) :
    (((leftUnit f N).inv.app ()).f n) y = pure f (M := regular A) 0 n n (zero_add n) A.one y := rfl

/-- Iterated extension of scalars agrees with extension along the composite. -/
def baseChangeComp (M : A.Module) :
    (baseChange g).obj ((baseChange f).obj M) ≅ (baseChange (f ≫ g)).obj M :=
  associate f g M (regular B) (regular C) ≪≫
    (secondFunctor (f ≫ g) M).mapIso (leftUnit g (regular C))

theorem baseChangeComp_pure (M : A.Module) (i j l m n : ℤ) (hm : i+j=m) (hn : m+l=n)
    (x : term M i) (b : B.complex.X j) (c : C.complex.X l) :
    (((baseChangeComp f g M).hom.app ()).f n)
      (pure g (N := regular C) m l n hn (pure f (N := regular B) i j m hm x b) c) =
      pure (f ≫ g) (N := regular C) i (j+l) n (by omega) x
        (C.mul j l (j+l) rfl (g.chainMap.f j b) c) := by
  change ((mapSecond (f ≫ g) M (leftUnit g (regular C)).hom).app ()).f n
    ((((associate f g M (regular B) (regular C)).hom.app ()).f n) _) = _
  rw [associate_pure, map_second_pure, leftUnit_pure, signedLeft_apply]
  exact congrArg (pure (f ≫ g) (N := regular C) i (j+l) n (by omega) x)
    (C.graded_comm j l (j+l) rfl (g.chainMap.f j b) c).symm

end ChangeOfScalars

section Symmetry

variable (M N : A.Module)

private def swapDegree (n : ℤ) : term (over M N) n →ₗ[k] term (over N M) n :=
  liftDegree (fun i j _ => (i*j).negOnePow • (pair (𝟙 A) j i n (by omega)).flip) (by
    intro i l j h x a y
    change ((i+l)*j).negOnePow • pure (𝟙 A) j (i+l) n (by omega) y (act M i l (i+l) rfl x a) =
      (i*(l+j)).negOnePow • pure (𝟙 A) (l+j) i n (by omega) (signedLeft N l j (l+j) rfl a y) x
    rw [signedLeft_apply]
    simp only [Units.smul_def]
    rw [pure_zsmul_left (𝟙 A) (M := N) (N := M), smul_smul, ← Units.val_mul,
      ← Int.negOnePow_add]
    -- Use the balancing relation in the reversed tensor.
    have e := pure_balance (𝟙 A) (M := N) (N := M) j l i (l+j) (i+l) n
      (by omega) (by omega) (by omega) y a x
    change pure (𝟙 A) (M := N) (N := M) (l+j) i n _ (act N j l (l+j) _ y a) x =
      pure (𝟙 A) j (i+l) n _ y (signedLeft M l i (i+l) _ a x) at e
    rw [e, signedLeft_apply, Units.smul_def, pure_zsmul_right (𝟙 A) (M := N) (N := M),
      smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
    rw [show i*(l+j)+l*j+l*i = (i+l)*j+2*(l*i) by ring,
      Int.negOnePow_add, Int.negOnePow_two_mul, mul_one])

private theorem swapDegree_pure (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term N j) :
    swapDegree M N n (pure (𝟙 A) i j n h x y) =
      (i*j).negOnePow • pure (𝟙 A) j i n (by omega) y x := by
  rw [swapDegree, liftDegree_pure]
  rfl

private def swapHom : over M N ⟶ over N M :=
  homOfDegrees (swapDegree M N) (by
    intro n z
    let L := (d[over N M,n]).hom.comp (swapDegree M N n)
    let R := (swapDegree M N (n+1)).comp (d[over M N,n]).hom
    have e : L = R := by
      apply pure_ext (f := 𝟙 A) (M := M) (N := N)
      intro i j h x y
      change d[over N M,n] (swapDegree M N n (pure (𝟙 A) i j n h x y)) =
        swapDegree M N (n+1) (d[over M N,n] (pure (𝟙 A) i j n h x y))
      rw [swapDegree_pure, Units.smul_def, map_zsmul,
        d_pure (𝟙 A) (M := N) (N := M) j i n _ y x,
        d_pure (𝟙 A) (M := M) (N := N) i j n h x y,
        map_add]
      simp only [Units.smul_def, map_zsmul]
      rw [swapDegree_pure, swapDegree_pure]
      simp only [Units.smul_def, smul_add, smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
      have e₁ : ((i+1)*j).negOnePow = (i*j).negOnePow * j.negOnePow := by
        rw [show (i+1)*j=i*j+j by ring, Int.negOnePow_add]
      have e₂ : (i+i*(j+1)).negOnePow = (i*j).negOnePow := by
        rw [show i+i*(j+1)=i*j+2*i by ring, Int.negOnePow_add (i*j) (2*i),
          Int.negOnePow_two_mul, mul_one]
      rw [e₁, e₂, Int.negOnePow_add (i*j) j]
      abel
    exact LinearMap.congr_fun e z)
    (by
      intro n l q h z a
      let L := (swapDegree M N q).comp ((act (over M N) n l q h).flip a)
      let R := ((act (over N M) n l q h).flip a).comp (swapDegree M N n)
      have e : L = R := by
        apply pure_ext (f := 𝟙 A) (M := M) (N := N)
        intro i j hij x y
        change swapDegree M N q (act (over M N) n l q h (pure (𝟙 A) i j n hij x y) a) =
          act (over N M) n l q h (swapDegree M N n (pure (𝟙 A) i j n hij x y)) a
        rw [act_pure (𝟙 A) (M := M) (N := N), swapDegree_pure, swapDegree_pure]
        simp only [Units.smul_def, map_zsmul, LinearMap.smul_apply]
        rw [act_pure (𝟙 A) (M := N) (N := M)]
        have e := pure_balance (𝟙 A) (M := N) (N := M) j l i (j+l) (i+l) q
          rfl (by omega) (by omega) y a x
        change pure (𝟙 A) (M := N) (N := M) (j+l) i q _ (act N j l (j+l) rfl y a) x =
          pure (𝟙 A) j (i+l) q _ y (signedLeft M l i (i+l) _ a x) at e
        rw [e, signedLeft_apply, Units.smul_def, pure_zsmul_right (𝟙 A) (M := N) (N := M),
          smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
        rw [show i*(j+l)+l*i = i*j+2*(l*i) by ring,
          Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
      exact LinearMap.congr_fun e z)

private theorem swapHom_comp : swapHom M N ≫ swapHom N M = 𝟙 (over M N) := by
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  apply HomologicalComplex.hom_ext
  intro n
  on_pure
  intro i j h x y
  change swapDegree N M n (swapDegree M N n (pure (𝟙 A) i j n h x y)) =
    pure (𝟙 A) i j n h x y
  rw [swapDegree_pure, Units.smul_def, map_zsmul, swapDegree_pure]
  simp only [Units.smul_def, smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
  rw [show i*j+j*i = 2*(i*j) by ring, Int.negOnePow_two_mul, Units.val_one, one_zsmul]

/-- The Koszul symmetry of the tensor over a commutative dg algebra. -/
def swap : over M N ≅ over N M :=
  ⟨swapHom M N, swapHom N M, swapHom_comp M N, swapHom_comp N M⟩

theorem swap_pure (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term N j) :
    ((swap M N).hom.app ()).f n (pure (𝟙 A) i j n h x y) =
      (i*j).negOnePow • pure (𝟙 A) j i n (by omega) y x :=
  swapDegree_pure M N i j n h x y

end Symmetry

section Restriction

variable (f : A ⟶ B) (g : B ⟶ C) (M : A.Module) (P : C.Module)

private theorem restrictTensor_action (i j n : ℤ) (h : i+j=n)
    (x : term (restrict g (tensor (f ≫ g) M P)) i) (a : B.complex.X j) :
    act (restrict g (tensor (f ≫ g) M P)) i j n h x a =
      act (tensor f M (restrict g P)) i j n h x a := by
  have e : (act (restrict g (tensor (f ≫ g) M P)) i j n h).flip a =
      (act (tensor f M (restrict g P)) i j n h).flip a := by
    apply pure_ext (f := f ≫ g) (M := M) (N := P)
    intro s t hs y z
    change act (tensor (f ≫ g) M P) i j n h (pure (f ≫ g) s t i hs y z) (g.chainMap.f j a) =
      act (tensor f M (restrict g P)) i j n h (pure f s t i hs y z) a
    rw [act_pure (f ≫ g) (M := M) (N := P), act_pure f (M := M) (N := restrict g P)]
    rfl
  exact LinearMap.congr_fun e x

/-- Restricting the output of the tensor along a map amounts to restricting the second input. -/
def restrictTensorIso :
    restrict g (tensor (f ≫ g) M P) ≅ tensor f M (restrict g P) where
  hom := ⟨fun a => by cases a; exact 𝟙 _, by
    rintro ⟨⟩ ⟨⟩ i j n h x a
    exact restrictTensor_action f g M P i j n h x a⟩
  inv := ⟨fun a => by cases a; exact 𝟙 _, by
    rintro ⟨⟩ ⟨⟩ i j n h x a
    exact (restrictTensor_action f g M P i j n h x a).symm⟩
  hom_inv_id := RightDGModuleModel.hom_ext (by rintro ⟨⟩; exact Category.id_comp _)
  inv_hom_id := RightDGModuleModel.hom_ext (by rintro ⟨⟩; exact Category.id_comp _)

theorem restrictTensorIso_pure (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term P j) :
    (((restrictTensorIso f g M P).hom.app ()).f n)
      (pure (f ≫ g) (M := M) (N := P) i j n h x y) =
      pure f (M := M) (N := restrict g P) i j n h x y := rfl

theorem restrictTensorIso_inv_pure (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term P j) :
    (((restrictTensorIso f g M P).inv.app ()).f n)
      (pure f (M := M) (N := restrict g P) i j n h x y) =
      pure (f ≫ g) (M := M) (N := P) i j n h x y := rfl

end Restriction

section TensorMaps

variable (f : A ⟶ B) {M M' : A.Module} {N N' : B.Module}

/-- The maps in the two tensor variables commute. -/
theorem map_tensor_comm (a : M ⟶ M') (b : N ⟶ N') :
    (extension f N).map a ≫ mapSecond f M' b =
      mapSecond f M b ≫ (extension f N').map a := by
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  apply HomologicalComplex.hom_ext
  intro n
  on_pure
  intro i j h x y
  change ((mapSecond f M' b).app ()).f n ((((extension f N).map a).app ()).f n (pure f i j n h x y)) =
    (((extension f N').map a).app ()).f n (((mapSecond f M b).app ()).f n (pure f i j n h x y))
  rw [map_first_pure, map_second_pure, map_second_pure, map_first_pure]

end TensorMaps

section SymmetryComparisons

variable (M : A.Module)

theorem map_second_swap {N N' : A.Module} (g : N ⟶ N') :
    mapSecond (𝟙 A) M g ≫ (swap M N').hom = (swap M N).hom ≫ (extension (𝟙 A) M).map g := by
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  apply HomologicalComplex.hom_ext
  intro n
  on_pure
  intro i j h x y
  change ((swap M N').hom.app ()).f n (((mapSecond (𝟙 A) M g).app ()).f n (pure (𝟙 A) i j n h x y)) =
    (((extension (𝟙 A) M).map g).app ()).f n (((swap M N).hom.app ()).f n (pure (𝟙 A) i j n h x y))
  rw [map_second_pure, swap_pure, swap_pure]
  simp only [Units.smul_def, map_zsmul]
  rw [map_first_pure]

theorem KFlat.map_quasiIso_second (hM : KFlat M) {N N' : A.Module} (g : N ⟶ N')
    (hg : RightDGModule.IsQuasiIso g) :
    RightDGModule.IsQuasiIso (mapSecond (𝟙 A) M g) := by
  rintro ⟨⟩
  let e := (RightDGModuleModel.eval ()).mapIso (swap M N)
  let e' := (RightDGModuleModel.eval ()).mapIso (swap M N')
  let q := (extension (𝟙 A) M).map g
  let t := mapSecond (𝟙 A) M g
  have hq : QuasiIso (q.app ()) := KFlat.map_quasiIso hM g hg ()
  have he : QuasiIso e.hom := quasiIso_of_isIso _
  have he' : QuasiIso e'.hom := quasiIso_of_isIso _
  have h : t.app () ≫ e'.hom = e.hom ≫ q.app () :=
    congrArg (fun d : over M N ⟶ over N' M => d.app ()) (map_second_swap M g)
  have hh : QuasiIso (e.hom ≫ q.app ()) :=
    quasiIso_comp _ _ (hφ := he) (hφ' := hq)
  exact (quasiIso_iff_comp_right (t.app ()) e'.hom (hφ' := he')).1 (h.symm ▸ hh)

/-- Extension along the identity algebra map is canonically the identity. -/
def baseChangeId : (baseChange (𝟙 A)).obj M ≅ M :=
  swap M (regular A) ≪≫ leftUnit (𝟙 A) M

theorem baseChangeId_pure (i j n : ℤ) (h : i+j=n) (x : term M i) (a : A.complex.X j) :
    ((baseChangeId M).hom.app ()).f n (pure (𝟙 A) (N := regular A) i j n h x a) =
      act M i j n h x a := by
  change ((leftUnit (𝟙 A) M).hom.app ()).f n
    (((swap M (regular A)).hom.app ()).f n (pure (𝟙 A) (N := regular A) i j n h x a)) = _
  rw [swap_pure, Units.smul_def, map_zsmul, leftUnit_pure, signedLeft_apply]
  change (i*j).negOnePow.val • ((j*i).negOnePow • act M i j n h x a) = _
  simp only [Units.smul_def, smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
  rw [show i*j+j*i = 2*(i*j) by ring, Int.negOnePow_two_mul, Units.val_one, one_zsmul]

theorem regular_kFlat : KFlat (regular A) := by
  intro E hE a i
  have e := (HomologicalComplex.homologyFunctor _ _ i).mapIso
    ((RightDGModuleModel.eval a).mapIso (baseChangeId E))
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ i).2
    (((HomologicalComplex.exactAt_iff_isZero_homology _ i).1 (hE a i)).of_iso e)

end SymmetryComparisons

section BaseChangeSquare

variable (f : A ⟶ B) (g : A ⟶ C) (M : B.Module)

private abbrev squareSource :=
  (baseChange (algebraInl f g)).obj M

private abbrev squareTarget :=
  (baseChange g).obj (restrict f M)

private theorem inl_mul_pure (l p q m n : ℤ) (h : p+q=m) (e : l+m=n)
    (b : B.complex.X l) (x : B.complex.X p) (y : C.complex.X q) :
    (algebraTensor f g).mul l m n e ((algebraInl f g).chainMap.f l b) (algebraPure f g p q m h x y) =
      algebraPure f g (l+p) q n (by omega) (B.mul l p (l+p) rfl b x) y := by
  change algebraMul f g l m n e (algebraPure f g l 0 l (add_zero l) b C.one)
    (algebraPure f g p q m h x y) = _
  rw [algebraMul_pure f g l 0 p q l m (l+p) q n (add_zero l) h e rfl (zero_add q),
    zero_mul, Int.negOnePow_zero, one_smul, C.toDGAlgebra.id_comp]

private theorem signedLeft_regular (D : Affine.CommDGAlgebra.{u,v} k)
    (i j n : ℤ) (h : i+j=n) (x : D.complex.X i) (y : D.complex.X j) :
    signedLeft (regular D) i j n h x y = D.mul i j n h x y :=
  (D.graded_comm i j n h x y).symm

private def squarePairRight (i m n : ℤ) (e : i+m=n) (x : term M i) :
    (algebraTensor f g).complex.X m →ₗ[k] term (squareTarget f g M) n :=
  liftDegree (f := g) (M := restrict f (regular B)) (N := regular C)
    (fun p q _ => (pair g (M := restrict f M) (N := regular C) (i+p) q n (by omega)).comp
      (act M i p (i+p) rfl x)) (by
    intro p l q h b a c
    change pure g (M := restrict f M) (N := regular C) (i+(p+l)) q n _
        (act M i (p+l) (i+(p+l)) rfl x (B.mul p l (p+l) rfl b (f.chainMap.f l a))) c =
      pure g (M := restrict f M) (N := regular C) (i+p) (l+q) n _ (act M i p (i+p) rfl x b)
        (signedLeft (regular C) l q (l+q) rfl (g.chainMap.f l a) c)
    rw [← act_assoc_at M i p l (i+p) (p+l) (i+(p+l)) rfl rfl (by omega) x b (f.chainMap.f l a)]
    exact pure_balance g (M := restrict f M) (N := regular C)
      (i+p) l q (i+(p+l)) (l+q) n (by omega) rfl (by omega) (act M i p (i+p) rfl x b) a c)

private theorem squarePairRight_pure (i p q m n d : ℤ) (e : i+m=n) (h : p+q=m) (hd : i+p=d)
    (x : term M i) (b : B.complex.X p) (c : C.complex.X q) :
    squarePairRight f g M i m n e x (algebraPure f g p q m h b c) =
      pure g (M := restrict f M) (N := regular C) d q n (by omega) (act M i p d hd x b) c := by
  subst d
  unfold squarePairRight algebraPure
  erw [liftDegree_pure]
  rfl

private def squarePair (i m n : ℤ) (e : i+m=n) :
    term M i →ₗ[k] (algebraTensor f g).complex.X m →ₗ[k] term (squareTarget f g M) n where
  toFun := squarePairRight f g M i m n e
  map_add' x y := by
    apply pure_ext (f := g) (M := restrict f (regular B)) (N := regular C)
    intro p q h b c
    change squarePairRight f g M i m n e (x+y) _ =
      squarePairRight f g M i m n e x (algebraPure f g p q m h b c) +
        squarePairRight f g M i m n e y (algebraPure f g p q m h b c)
    rw [squarePairRight_pure f g M i p q m n (i+p) e h rfl,
      squarePairRight_pure f g M i p q m n (i+p) e h rfl,
      squarePairRight_pure f g M i p q m n (i+p) e h rfl]
    exact ((pair g (M := restrict f M) (N := regular C) (i+p) q n (by omega)).flip c
      ∘ₗ (act M i p (i+p) rfl).flip b).map_add x y
  map_smul' t x := by
    apply pure_ext (f := g) (M := restrict f (regular B)) (N := regular C)
    intro p q h b c
    change squarePairRight f g M i m n e (t • x) _ =
      t • squarePairRight f g M i m n e x (algebraPure f g p q m h b c)
    rw [squarePairRight_pure f g M i p q m n (i+p) e h rfl,
      squarePairRight_pure f g M i p q m n (i+p) e h rfl]
    exact ((pair g (M := restrict f M) (N := regular C) (i+p) q n (by omega)).flip c
      ∘ₗ (act M i p (i+p) rfl).flip b).map_smul t x

private def squareForward (n : ℤ) :
    term (squareSource f g M) n →ₗ[k] term (squareTarget f g M) n :=
  liftDegree (f := algebraInl f g) (M := M) (N := regular (algebraTensor f g))
    (fun i m e => squarePair f g M i m n e) (by
      intro i l m h x b z
      change squarePairRight f g M (i+l) m n h (act M i l (i+l) rfl x b) z =
        squarePairRight f g M i (l+m) n (by omega) x
          (signedLeft (regular (algebraTensor f g)) l m (l+m) rfl
            ((algebraInl f g).chainMap.f l b) z)
      rw [signedLeft_regular]
      have e : squarePairRight f g M (i+l) m n h (act M i l (i+l) rfl x b) =
          (squarePairRight f g M i (l+m) n (by omega) x).comp
            ((algebraTensor f g).mul l m (l+m) rfl ((algebraInl f g).chainMap.f l b)) := by
        apply pure_ext (f := g) (M := restrict f (regular B)) (N := regular C)
        intro p q hm u v
        change squarePairRight f g M (i+l) m n h (act M i l (i+l) rfl x b)
            (algebraPure f g p q m hm u v) =
          squarePairRight f g M i (l+m) n (by omega) x
            ((algebraTensor f g).mul l m (l+m) rfl ((algebraInl f g).chainMap.f l b)
              (algebraPure f g p q m hm u v))
        rw [inl_mul_pure, squarePairRight_pure f g M (i+l) p q m n (i+l+p) h hm rfl,
          squarePairRight_pure f g M i (l+p) q (l+m) n (i+l+p) (by omega) (by omega) (by omega),
          act_assoc_at M i l p (i+l) (l+p) (i+l+p) rfl rfl rfl]
      exact LinearMap.congr_fun e z)

private theorem squareForward_pure (i p q m n d : ℤ) (e : i+m=n) (h : p+q=m) (hd : i+p=d)
    (x : term M i) (b : B.complex.X p) (c : C.complex.X q) :
    squareForward f g M n (pure (algebraInl f g) (M := M) (N := regular (algebraTensor f g))
      i m n e x (algebraPure f g p q m h b c)) =
      pure g (M := restrict f M) (N := regular C) d q n (by omega) (act M i p d hd x b) c := by
  rw [squareForward, liftDegree_pure]
  exact squarePairRight_pure f g M i p q m n d e h hd x b c

private def squareBackward (n : ℤ) :
    term (squareTarget f g M) n →ₗ[k] term (squareSource f g M) n :=
  liftDegree (f := g) (M := restrict f M) (N := regular C)
    (fun i j h => (pair (algebraInl f g) (M := M) (N := regular (algebraTensor f g)) i j n h).compl₂
      (((algebraInr f g).chainMap.f j).hom)) (by
      intro i l j h x a c
      let Q := algebraTensor f g
      let P := regular Q
      let b := algebraInl f g
      let d := algebraInr f g
      change pure b (M := M) (N := P) (i+l) j n h
          (act M i l (i+l) rfl x (f.chainMap.f l a)) (d.chainMap.f j c) =
        pure b (M := M) (N := P) i (l+j) n (by omega) x
          (d.chainMap.f (l+j) (signedLeft (regular C) l j (l+j) rfl (g.chainMap.f l a) c))
      rw [pure_balance b (M := M) (N := P) i l j (i+l) (l+j) n rfl rfl h x,
        signedLeft_regular Q, signedLeft_regular C, d.map_mul]
      have e := congrArg (fun q : A ⟶ Q => q.chainMap.f l a) (algebraInl_comp f g)
      change b.chainMap.f l (f.chainMap.f l a) = d.chainMap.f l (g.chainMap.f l a) at e
      rw [e])

private theorem squareBackward_pure (i j n : ℤ) (h : i+j=n)
    (x : term M i) (c : C.complex.X j) :
    squareBackward f g M n (pure g (M := restrict f M) (N := regular C) i j n h x c) =
      pure (algebraInl f g) (M := M) (N := regular (algebraTensor f g)) i j n h x
        ((algebraInr f g).chainMap.f j c) := by
  rw [squareBackward, liftDegree_pure]
  rfl

private theorem squareForward_backward (n : ℤ) :
    (squareForward f g M n).comp (squareBackward f g M n) = LinearMap.id := by
  apply pure_ext (f := g) (M := restrict f M) (N := regular C)
  intro i j h x c
  change squareForward f g M n (squareBackward f g M n
    (pure g (M := restrict f M) (N := regular C) i j n h x c)) = _
  rw [squareBackward_pure]
  change squareForward f g M n (pure (algebraInl f g) (M := M) (N := regular (algebraTensor f g))
    i j n h x (algebraPure f g 0 j j (zero_add j) B.one c)) = _
  rw [squareForward_pure f g M i 0 j j n i h (zero_add j) (add_zero i)]
  exact congrArg (fun z : term M i => pure g (M := restrict f M) (N := regular C) i j n h z c)
    (M.act_id () i x)

private theorem squareBackward_forward (n : ℤ) :
    (squareBackward f g M n).comp (squareForward f g M n) = LinearMap.id := by
  let Q := algebraTensor f g
  let P := regular Q
  let b := algebraInl f g
  let d := algebraInr f g
  apply pure_ext (f := b) (M := M) (N := P)
  intro i j h x z
  let L := (squareBackward f g M n).comp (squareForward f g M n)
  have e : L.comp (pair b (M := M) (N := P) i j n h x) =
      pair b (M := M) (N := P) i j n h x := by
    apply pure_ext (f := g) (M := restrict f (regular B)) (N := regular C)
    intro p q hj y c
    change squareBackward f g M n (squareForward f g M n
        (pure b (M := M) (N := P) i j n h x (algebraPure f g p q j hj y c))) =
      pure b (M := M) (N := P) i j n h x (algebraPure f g p q j hj y c)
    rw [squareForward_pure f g M i p q j n (i+p) h hj rfl, squareBackward_pure,
      pure_balance b (M := M) (N := P) i p q (i+p) j n rfl hj (by omega) x y,
      signedLeft_regular Q, algebraPure_factor]
  exact LinearMap.congr_fun e z

private def squareBackwardHom : squareTarget f g M ⟶ restrict (algebraInr f g) (squareSource f g M) :=
  homOfDegrees (squareBackward f g M) (by
    intro n z
    let b := algebraInl f g
    let d := algebraInr f g
    let P := regular (algebraTensor f g)
    let L := (d[squareSource f g M,n]).hom.comp (squareBackward f g M n)
    let R := (squareBackward f g M (n+1)).comp (d[squareTarget f g M,n]).hom
    have e : L = R := by
      apply pure_ext (f := g) (M := restrict f M) (N := regular C)
      intro i j h x c
      change d[squareSource f g M,n] (squareBackward f g M n
          (pure g (M := restrict f M) (N := regular C) i j n h x c)) =
        squareBackward f g M (n+1) (d[squareTarget f g M,n]
          (pure g (M := restrict f M) (N := regular C) i j n h x c))
      rw [squareBackward_pure, d_pure b (M := M) (N := P),
        d_pure g (M := restrict f M) (N := regular C), map_add]
      simp only [Units.smul_def, map_zsmul]
      rw [squareBackward_pure, squareBackward_pure]
      have e := CategoryTheory.congr_fun (d.chainMap.comm j (j+1)) c
      exact congrArg (fun z : (algebraTensor f g).complex.X (j+1) =>
        pure b (M := M) (N := P) (i+1) j (n+1) (by omega) (d[M,i] x) (d.chainMap.f j c) +
          i.negOnePow.val • pure b (M := M) (N := P) i (j+1) (n+1) (by omega) x z) e
    exact LinearMap.congr_fun e z)
    (by
      intro n l p h z c
      let b := algebraInl f g
      let d := algebraInr f g
      let P := regular (algebraTensor f g)
      let L := (squareBackward f g M p).comp ((act (squareTarget f g M) n l p h).flip c)
      let R := ((act (squareSource f g M) n l p h).flip (d.chainMap.f l c)).comp (squareBackward f g M n)
      have e : L = R := by
        apply pure_ext (f := g) (M := restrict f M) (N := regular C)
        intro i j hij x y
        change squareBackward f g M p (act (squareTarget f g M) n l p h
            (pure g (M := restrict f M) (N := regular C) i j n hij x y) c) =
          act (squareSource f g M) n l p h (squareBackward f g M n
            (pure g (M := restrict f M) (N := regular C) i j n hij x y)) (d.chainMap.f l c)
        rw [act_pure g (M := restrict f M) (N := regular C), squareBackward_pure, squareBackward_pure,
          act_pure b (M := M) (N := P)]
        change pure b (M := M) (N := P) i (j+l) p (by omega) x
          (d.chainMap.f (j+l) (C.mul j l (j+l) rfl y c)) = _
        rw [d.map_mul]
      exact LinearMap.congr_fun e z)

private theorem squareBackward_bijective (n : ℤ) : Function.Bijective (squareBackward f g M n) :=
  ⟨Function.LeftInverse.injective (fun x => LinearMap.congr_fun (squareForward_backward f g M n) x),
    Function.RightInverse.surjective (fun x => LinearMap.congr_fun (squareBackward_forward f g M n) x)⟩

/-- Base change around the tensor pushout of commutative dg algebras. -/
def baseChangeSquare :
    restrict (algebraInr f g) (squareSource f g M) ≅ squareTarget f g M where
  hom := homOfDegrees (squareForward f g M) (by
    intro n x
    apply (squareBackward_bijective f g M (n+1)).1
    have e := CategoryTheory.congr_fun (((squareBackwardHom f g M).app ()).comm n (n+1))
      (squareForward f g M n x)
    change d[squareSource f g M,n] (((squareBackward f g M n).comp (squareForward f g M n)) x) =
      squareBackward f g M (n+1) (d[squareTarget f g M,n] (squareForward f g M n x)) at e
    rw [← e, squareBackward_forward]
    exact (LinearMap.congr_fun (squareBackward_forward f g M (n+1)) _).symm)
    (by
      intro i j n h x a
      apply (squareBackward_bijective f g M n).1
      have e := (squareBackwardHom f g M).comm_act (a := ()) (b := ()) i j n h (squareForward f g M i x) a
      change squareBackward f g M n (act (squareTarget f g M) i j n h (squareForward f g M i x) a) =
        act (restrict (algebraInr f g) (squareSource f g M)) i j n h
          (((squareBackward f g M i).comp (squareForward f g M i)) x) a at e
      rw [e, squareBackward_forward]
      exact LinearMap.congr_fun (squareBackward_forward f g M n) _)
  inv := squareBackwardHom f g M
  hom_inv_id := by
    apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    exact squareBackward_forward f g M n
  inv_hom_id := by
    apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    exact squareForward_backward f g M n

theorem baseChangeSquare_pure (i p q m n : ℤ) (h : p+q=m) (e : i+m=n)
    (x : term M i) (b : B.complex.X p) (c : C.complex.X q) :
    ((baseChangeSquare f g M).hom.app ()).f n
        (pure (algebraInl f g) (M := M) (N := regular (algebraTensor f g)) i m n e x
          (algebraPure f g p q m h b c)) =
      pure g (M := restrict f M) (N := regular C) (i+p) q n (by omega) (act M i p (i+p) rfl x b) c :=
  squareForward_pure f g M i p q m n (i+p) e h rfl x b c

theorem baseChangeSquare_natural {M' : B.Module} (a : M ⟶ M') :
    (restrictFunctor (algebraInr f g)).map ((baseChange (algebraInl f g)).map a) ≫
      (baseChangeSquare f g M').hom =
    (baseChangeSquare f g M).hom ≫ (baseChange g).map ((restrictFunctor f).map a) := by
  let b := algebraInl f g
  let c := algebraInr f g
  let P := regular (algebraTensor f g)
  let L := (restrictFunctor c).map ((baseChange b).map a) ≫ (baseChangeSquare f g M').hom
  let R := (baseChangeSquare f g M).hom ≫ (baseChange g).map ((restrictFunctor f).map a)
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply pure_ext (f := b) (M := M) (N := P)
  intro i j h x z
  have e : ((L.app ()).f n).hom.comp (pair b (M := M) (N := P) i j n h x) =
      ((R.app ()).f n).hom.comp (pair b (M := M) (N := P) i j n h x) := by
    apply pure_ext (f := g) (M := restrict f (regular B)) (N := regular C)
    intro p q hp y w
    change ((baseChangeSquare f g M').hom.app ()).f n
        ((((baseChange b).map a).app ()).f n
          (pure b (M := M) (N := P) i j n h x (algebraPure f g p q j hp y w))) =
      (((baseChange g).map ((restrictFunctor f).map a)).app ()).f n
        (((baseChangeSquare f g M).hom.app ()).f n
          (pure b (M := M) (N := P) i j n h x (algebraPure f g p q j hp y w)))
    rw [map_first_pure b, baseChangeSquare_pure, baseChangeSquare_pure,
      map_first_pure g (M := restrict f M) (M' := restrict f M') (N := regular C)]
    change pure g (M := restrict f M') (N := regular C) (i+p) q n _
        (act M' i p (i+p) rfl ((a.app ()).f i x) y) w =
      pure g (M := restrict f M') (N := regular C) (i+p) q n _
        ((a.app ()).f (i+p) (act M i p (i+p) rfl x y)) w
    rw [a.comm_act]
  exact LinearMap.congr_fun e z

/-- The module comparison around a tensor pushout is natural in the module. -/
def baseChangeSquareIso :
    baseChange (algebraInl f g) ⋙ restrictFunctor (algebraInr f g) ≅
      restrictFunctor f ⋙ baseChange g :=
  NatIso.ofComponents (baseChangeSquare f g) (fun _ => baseChangeSquare_natural f g _ _)

end BaseChangeSquare

section Models

open Specs.DerivedFormalization.DG.HomComplex (HomotopyEquation)

theorem moduleTensor_formulas (f : A ⟶ B) (N : B.Module) :
    (moduleTensorModel.{u,v} k).Formulas f N :=
  ⟨fun M => d_pure f (M := M) (N := N),
    fun M => act_pure f (M := M) (N := N),
    map_first_pure f,
    fun g g' w h => ⟨mapFirstGraded f N w, map_first_homotopy f N g g' w h,
      map_first_graded_pure f N w⟩,
    fun g => ⟨tensorConeIso g f N⟩⟩

theorem moduleTensor_second (f : A ⟶ B) (M : A.Module) :
    (moduleTensorModel.{u,v} k).SecondVariable f M := by
  refine ⟨secondFunctor f M, fun _ => Iso.refl _, ?_, ?_⟩
  · intro N N' g i j n h x y
    exact map_second_pure f M g i j n h x y
  · intro N N' g g' w h
    refine ⟨mapSecondGraded f M w, ?_, ?_⟩
    · change HomotopyEquation ((𝟙 (tensor f M N)) ≫ mapSecond f M g ≫ 𝟙 (tensor f M N'))
        ((𝟙 (tensor f M N)) ≫ mapSecond f M g' ≫ 𝟙 (tensor f M N')) (mapSecondGraded f M w)
      simpa only [Category.id_comp, Category.comp_id] using map_second_homotopy f M g g' w h
    · intro i j n p q hi hj hq x y
      change component (mapSecondGraded f M w) () n q hq (pure f i j n hi x y) =
        i.negOnePow • pure f i p q (by omega) x (component w () j p hj y)
      rw [map_second_graded_pure f M w i j n p q hi hj hq x y,
        show i*(-1) = -i by ring, Int.negOnePow_neg]

theorem moduleTensor_preserves (N : A.Module) :
    (moduleTensorModel.{u,v} k).PreservesQuasiIsomorphisms N :=
  by
    intro hN M M' g h
    exact KFlat.map_quasiIso hN g h

theorem module_tensor_construction : ModuleTensorConstruction.{u,v} := by
  intro k _ _
  exact ⟨moduleTensorModel k, moduleTensor_formulas, moduleTensor_second, moduleTensor_preserves⟩

/-- Restrict the module of the tensor coproduct to the common base. -/
def baseAlgebraModuleIso (f : A ⟶ B) (g : A ⟶ C) :
    over (restrict f (regular B)) (restrict g (regular C)) ≅
      restrict (g ≫ algebraInr f g) (regular (algebraTensor f g)) :=
  (restrictTensorIso (𝟙 A) g (restrict f (regular B)) (regular C)).symm ≪≫
    (restrictFunctor g).mapIso (algebraModuleIso f g)

theorem baseAlgebraModuleIso_pure (f : A ⟶ B) (g : A ⟶ C)
    (i j n : ℤ) (h : i+j=n) (x : B.complex.X i) (y : C.complex.X j) :
    (((baseAlgebraModuleIso f g).hom.app ()).f n)
      (pure (𝟙 A) (M := restrict f (regular B)) (N := restrict g (regular C)) i j n h x y) =
      algebraPure f g i j n h x y := rfl

/-- The coproduct together with its comparison to the balanced module construction. -/
def algebraTensorModel (f : A ⟶ B) (g : A ⟶ C) : (moduleTensorModel.{u,v} k).AlgebraCoproduct f g where
  obj := algebraTensor f g
  inl := algebraInl f g
  inr := algebraInr f g
  comparison := algebraModuleIso f g

theorem algebraTensorModel_formulas (f : A ⟶ B) (g : A ⟶ C) :
    (algebraTensorModel f g).Formulas where
  unit := rfl
  mul i j p q m m' n h h' hn x y z w :=
    algebraMul_pure f g i j p q m m' (i+p) (j+q) n h h' hn rfl rfl x y z w
  inl _ _ := rfl
  inr _ _ := rfl
  base := algebraInl_comp f g
  coproduct r s := algebraTensor_coproduct f g r s
  nonpositive := algebraTensor_nonpositive f g
  underlying := ⟨baseAlgebraModuleIso f g, baseAlgebraModuleIso_pure f g⟩
  scalarExtension := ⟨baseChangeSquareIso f g, baseChangeSquare_pure f g⟩

theorem moduleTensor_comparisons : (moduleTensorModel.{u,v} k).Comparisons where
  associate f g M N P := ⟨associate f g M N P, associate_pure f g M N P⟩
  symmetry M N := ⟨swap M N, swap_pure M N⟩
  leftUnit f N := ⟨leftUnit f N, leftUnit_pure f N⟩
  compose f g M := ⟨baseChangeComp f g M, baseChangeComp_pure f g M⟩
  identity M := ⟨baseChangeId M, baseChangeId_pure M⟩
  regularFlat := regular_kFlat
  secondQuasiIso a hM ha := ⟨mapSecond _ _ a, KFlat.map_quasiIso_second _ hM a ha, map_second_pure _ _ a⟩
  restrict f g M P := ⟨restrictTensorIso f g M P, restrictTensorIso_pure f g M P⟩

theorem algebra_tensor_construction : (moduleTensorModel.{u,v} k).AlgebraCoproducts := by
  refine ⟨algebraTensorModel, algebraTensorModel_formulas, ?_⟩
  intro A B C A' B' C' f g f' g' a b c hb hc
  exact ⟨algebraMap f g f' g' b c hb hc, algebraMap_inl f g f' g' b c hb hc,
    algebraMap_inr f g f' g' b c hb hc, algebraMap_pure f g f' g' b c hb hc⟩

/-- One balanced tensor model satisfies the module, base-change and coproduct laws. -/
theorem signed_tensor_construction : SignedTensorConstruction.{u,v} := by
  intro k _ _
  exact ⟨moduleTensorModel k, moduleTensor_formulas, moduleTensor_second, moduleTensor_preserves,
    moduleTensor_comparisons, algebra_tensor_construction⟩

end Models

end

end DerivedFormalization.Affine.Tensor
