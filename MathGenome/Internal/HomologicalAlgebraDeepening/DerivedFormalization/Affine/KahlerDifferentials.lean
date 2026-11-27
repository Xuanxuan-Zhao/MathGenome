import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.KahlerDifferentials
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.Tensor

open CategoryTheory
open CochainComplex.HomComplex
open scoped Classical

universe u v

namespace DerivedFormalization.Affine.Kahler

open Specs.DerivedFormalization.Affine.Tensor
open Specs.DerivedFormalization.DG.HomComplex (Family gradedHom component homComplex RightLinear)

open QuotientModel

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {A Q Q' A' : CommDGAlgebra.{u,v} k}
variable {f : A ⟶ Q} {M : Q.Module} {r : ℤ}

private theorem negOnePow_left (i j r : ℤ) :
    (r*i).negOnePow * (i*(j+r)).negOnePow = (i*j).negOnePow := by
  rw [← Int.negOnePow_add, show r*i+i*(j+r)=i*j+2*(i*r) by ring,
    Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

theorem koszulRule : KoszulRule.{u,v} := by
  intro k _ _ A Q f M r D
  have signRule (i j jr : ℤ) (hj : j+r=jr) (n : ℤ) (h : i+jr=n)
      (x : Q.complex.X i) (y : term M jr) :
      (r*i).negOnePow • signedLeft M i jr n h x y =
        (i*j).negOnePow • act M jr i n (by omega) y x := by
    subst jr
    rw [signedLeft_apply, smul_smul, negOnePow_left]
  constructor
  · intro h
    refine ⟨h.relative, ?_⟩
    intro i j n ir jr nr e hi hj hn x y
    rw [signRule i j jr hj]
    exact h.leibniz i j n ir jr nr e hi hj hn x y
  · rintro ⟨relative, rule⟩
    refine ⟨relative, ?_⟩
    intro i j n ir jr nr e hi hj hn x y
    rw [← signRule i j jr hj]
    exact rule i j n ir jr nr e hi hj hn x y

theorem koszulLinearity : KoszulLinearity.{u,v} := by
  intro k _ _ Q M N r F
  have laws (i j n ir nr : ℤ) (h : i+j=n) (hi : i+r=ir) (hn : n+r=nr)
      (x : term M i) (a : Q.complex.X j) :
      ((F ()).v n nr hn (signedLeft M j i n (by omega) a x) =
        (r*j).negOnePow • signedLeft N j ir nr (by omega) a ((F ()).v i ir hi x)) ↔
      ((F ()).v n nr hn (act M i j n h x a) =
        act N ir j nr (by omega) ((F ()).v i ir hi x) a) := by
    subst ir
    rw [signedLeft_apply, signedLeft_apply, smul_smul, negOnePow_left]
    have hs (t : ℤˣ) (z : term M n) :
        (F ()).v n nr hn (t • z) = t • (F ()).v n nr hn z :=
      map_zsmul ((F ()).v n nr hn).hom (t : ℤ) z
    rw [hs, smul_left_cancel_iff]
  constructor
  · intro h i j n ir nr e hi hn x a
    exact (laws i j n ir nr e hi hn x a).2 (h (a := ()) (b := ()) i j n ir nr e hi hn x a)
  · intro h
    rintro ⟨⟩ ⟨⟩ i j n ir nr e hi hn x a
    exact (laws i j n ir nr e hi hn x a).1 (h i j n ir nr e hi hn x a)

private theorem δ_value (D : Cochain Q.complex (M.complex ()) r)
    (i p : ℤ) (h : i+(r+1)=p) (x : Q.complex.X i) :
    (δ r (r+1) D).v i p h x =
      (M.complex ()).d (i+r) p (D.v i (i+r) rfl x) +
        (r+1).negOnePow • D.v (i+1) p (by omega) (Q.complex.d i (i+1) x) := by
  rw [δ_v r (r+1) rfl D i p h (i+r) (i+1) (by omega) rfl]
  rfl

private theorem act_d_at (M : Q.Module) (i j n i' j' n' : ℤ)
    (e : i+j=n) (ei : i+1=i') (ej : j+1=j') (en : n+1=n')
    (x : term M i) (y : Q.complex.X j) :
    (M.complex ()).d n n' (act M i j n e x y) =
      act M i' j n' (by omega) ((M.complex ()).d i i' x) y +
        i.negOnePow • act M i j' n' (by omega) x (Q.complex.d j j' y) := by
  subst i' j' n'
  exact M.leibniz (a := ()) (b := ()) i j n e x y

theorem commutator_derivation {D : Cochain Q.complex (M.complex ()) r}
    (hD : IsDerivation f D) : IsDerivation f (δ r (r+1) D) := by
  constructor
  · intro i p h a
    have e := CategoryTheory.congr_fun (f.chainMap.comm i (i+1)) a
    simp only [ModuleCat.comp_apply] at e
    rw [δ_value, hD.relative, map_zero, e, hD.relative, smul_zero, add_zero]
  · intro i j n ir jr nr h hi hj hn x y
    subst n ir jr nr
    rw [δ_value, δ_value, δ_value, hD.leibniz i j (i+j) (i+r) (j+r) (i+j+r) rfl rfl rfl rfl]
    rw [Q.toDGAlgebra.leibniz (a := ()) (b := ()) (c := ())]
    simp only [map_add, Units.smul_def, map_zsmul]
    rw [act_d_at M (i+r) j (i+j+r) (i+(r+1)) (j+1) (i+j+(r+1))
          (by omega) (by omega) rfl (by omega),
        act_d_at M (j+r) i (i+j+r) (j+(r+1)) (i+1) (i+j+(r+1))
          (by omega) (by omega) rfl (by omega)]
    rw [hD.leibniz (i+1) j (i+j+1) (i+(r+1)) (j+r) (i+j+(r+1))
          (by omega) (by omega) rfl (by omega),
        hD.leibniz i (j+1) (i+j+1) (i+r) (j+(r+1)) (i+j+(r+1))
          (by omega) rfl (by omega) (by omega)]
    simp only [Units.smul_def, LinearMap.add_apply, LinearMap.smul_apply,
      smul_add, smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
    rw [show r+1+i=(i+r)+1 by ring, Int.negOnePow_succ,
      show r+1+(i+1)*j=(i*j+(j+r))+1 by ring, Int.negOnePow_succ,
      show r+1+(i+i*(j+1))=(i*j+(r+1))+2*i by ring,
      Int.negOnePow_add (i*j+(r+1)) (2*i), Int.negOnePow_two_mul, mul_one]
    simp only [← add_assoc, Int.negOnePow_succ, Units.val_neg, neg_smul]
    abel

private def eval (D : Derivation f M r) (n p : ℤ) (h : n+r=p) :
    Degree f n →ₗ[k] term M p :=
  (relations f n).liftQ (evalRaw D n p h) (by
    subst p
    exact fun _ hz => hz M r D)

@[simp] private theorem eval_mk (D : Derivation f M r) (n p : ℤ) (h : n+r=p)
    (z : Raw Q n) : eval D n p h (mkDegree f n z) = evalRaw D n p h z := rfl

private theorem degree_ext {n : ℤ} {x y : Degree f n}
    (h : ∀ (M : Q.Module) (r : ℤ) (D : Derivation f M r),
      eval D n (n+r) rfl x = eval D n (n+r) rfl y) : x = y := by
  obtain ⟨x,rfl⟩ := (relations f n).mkQ_surjective x
  obtain ⟨y,rfl⟩ := (relations f n).mkQ_surjective y
  have hz : x-y ∈ relations f n := fun M r D => by
    rw [map_sub, ← eval_mk, ← eval_mk, h M r D, sub_self]
  have e : mkDegree f n (x-y) = 0 := (Submodule.Quotient.mk_eq_zero _).2 hz
  rw [map_sub, sub_eq_zero] at e
  exact e

private def rawAction (Q : CommDGAlgebra.{u,v} k) (i j n : ℤ) (h : i+j=n)
    (b : Q.complex.X j) : Raw Q i →ₗ[k] Raw Q n :=
  DirectSum.toModule k (Index Q) _ fun ⟨p,x⟩ =>
    (single Q p (n-p) n (by omega) x).comp
      ((Q.mul (i-p) j (n-p) (by omega)).flip b)

private theorem rawAction_single (i j n p q t : ℤ) (h : i+j=n) (e : p+q=i) (et : q+j=t)
    (x : Q.complex.X p) (y : Q.complex.X q) (b : Q.complex.X j) :
    rawAction Q i j n h b (single Q p q i e x y) =
      single Q p t n (by omega) x (Q.mul q j t et y b) := by
  obtain rfl : q=i-p := by omega
  obtain rfl : j=n-i := by omega
  obtain rfl : t=n-p := by omega
  change (DirectSum.toModule k (Index Q) (Raw Q n) _)
    (DirectSum.lof k (Index Q) (Coeff Q i) ⟨p, x⟩ y) = _
  rw [DirectSum.toModule_lof]
  rfl

private theorem evalRaw_action (D : Derivation f M r)
    (i j n ir nr : ℤ) (h : i+j=n) (hi : i+r=ir) (hn : n+r=nr)
    (z : Raw Q i) (b : Q.complex.X j) :
    evalRaw D n nr hn (rawAction Q i j n h b z) =
      act M ir j nr (by omega) (evalRaw D i ir hi z) b := by
  change ((evalRaw D n nr hn).comp (rawAction Q i j n h b)) z =
    (((act M ir j nr (by omega)).flip b).comp (evalRaw D i ir hi)) z
  congr 1
  apply raw_ext
  intro p q e x y
  simp only [LinearMap.comp_apply, LinearMap.flip_apply, rawAction_single i j n p q (q+j) h e rfl, evalRaw_single]
  exact (act_assoc_at M (p+r) q j ir (q+j) nr (by omega) rfl (by omega) _ _ _).symm

private def actionBy (f : A ⟶ Q) (i j n : ℤ) (h : i+j=n)
    (b : Q.complex.X j) : Degree f i →ₗ[k] Degree f n :=
  (relations f i).liftQ ((mkDegree f n).comp (rawAction Q i j n h b)) (by
    intro z hz
    change mkDegree f n (rawAction Q i j n h b z) = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    intro M r D
    rw [evalRaw_action D i j n (i+r) (n+r) h rfl rfl, hz M r D]
    exact map_zero ((act M (i+r) j (n+r) (by omega)).flip b))

private theorem eval_actionBy (D : Derivation f M r) (i j n ir nr : ℤ)
    (h : i+j=n) (hi : i+r=ir) (hn : n+r=nr) (z : Degree f i) (b : Q.complex.X j) :
    eval D n nr hn (actionBy f i j n h b z) =
      act M ir j nr (by omega) (eval D i ir hi z) b := by
  obtain ⟨w,rfl⟩ := (relations f i).mkQ_surjective z
  exact evalRaw_action D i j n ir nr h hi hn w b

private def action (f : A ⟶ Q) (i j n : ℤ) (h : i+j=n) :
    Degree f i →ₗ[k] Q.complex.X j →ₗ[k] Degree f n :=
  LinearMap.flip
    { toFun := actionBy f i j n h
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        apply degree_ext
        intro M r D
        simp only [LinearMap.add_apply, map_add, eval_actionBy D i j n (i+r) (n+r) h rfl rfl]
      map_smul' := by
        intro c x
        apply LinearMap.ext
        intro z
        apply degree_ext
        intro M r D
        simp only [LinearMap.smul_apply, map_smul,
          eval_actionBy D i j n (i+r) (n+r) h rfl rfl, RingHom.id_apply] }

private theorem eval_action (D : Derivation f M r) (i j n ir nr : ℤ)
    (h : i+j=n) (hi : i+r=ir) (hn : n+r=nr) (z : Degree f i) (b : Q.complex.X j) :
    eval D n nr hn (action f i j n h z b) =
      act M ir j nr (by omega) (eval D i ir hi z) b :=
  eval_actionBy D i j n ir nr h hi hn z b

/-- The commutator on a homogeneous relative derivation. -/
def commutator (D : Derivation f M r) : Derivation f M (r+1) :=
  ⟨δ r (r+1) D.val, commutator_derivation D.property⟩

private theorem commutator_commutator (D : Derivation f M r) :
    commutator (commutator D) = 0 :=
  Subtype.ext (δ_δ r (r+1) ((r+1)+1) D.val)

private def rawD (Q : CommDGAlgebra.{u,v} k) (n : ℤ) :
    Raw Q n →ₗ[k] Raw Q (n+1) :=
  DirectSum.toModule k (Index Q) _ fun ⟨i,x⟩ =>
    single Q (i+1) (n-i) (n+1) (by omega) (Q.complex.d i (i+1) x) +
      i.negOnePow • (single Q i (n-i+1) (n+1) (by omega) x).comp
        (Q.complex.d (n-i) (n-i+1)).hom

private theorem rawD_single (i j n : ℤ) (h : i+j=n) (x : Q.complex.X i)
    (y : Q.complex.X j) :
    rawD Q n (single Q i j n h x y) =
      single Q (i+1) j (n+1) (by omega) (Q.complex.d i (i+1) x) y +
        i.negOnePow • single Q i (j+1) (n+1) (by omega) x (Q.complex.d j (j+1) y) := by
  obtain rfl : j=n-i := by omega
  change (DirectSum.toModule k (Index Q) (Raw Q (n+1)) _)
    (DirectSum.lof k (Index Q) (Coeff Q n) ⟨i, x⟩ y) = _
  rw [DirectSum.toModule_lof]
  rfl

private theorem evalRaw_zero (n p : ℤ) (h : n+r=p) (z : Raw Q n) :
    evalRaw (0 : Derivation f M r) n p h z = 0 := by
  suffices evalRaw (0 : Derivation f M r) n p h = 0 by rw [this, LinearMap.zero_apply]
  apply raw_ext
  intro i j e x y
  rw [evalRaw_single (0 : Derivation f M r) i j n (i+r) p e rfl h]
  change ((act M (i+r) j p (by omega)).flip y) (((0 : Cochain Q.complex (M.complex ()) r).v i (i+r) rfl) x) = 0
  simp

private theorem evalRaw_d_rule (D : Derivation f M r) (n nr p : ℤ)
    (h : n+r=nr) (hp : nr+1=p) (z : Raw Q n) :
    (M.complex ()).d nr p (evalRaw D n nr h z) =
      evalRaw (commutator D) n p (by omega) z +
        r.negOnePow • evalRaw D (n+1) p (by omega) (rawD Q n z) := by
  change (((M.complex ()).d nr p).hom.comp (evalRaw D n nr h)) z =
    (evalRaw (commutator D) n p (by omega) +
      r.negOnePow • (evalRaw D (n+1) p (by omega)).comp (rawD Q n)) z
  congr 1
  apply raw_ext
  intro i j e x y
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, rawD_single,
    Units.smul_def, map_add, map_zsmul]
  rw [evalRaw_single D i j n (i+r) nr e rfl h,
    act_d_at M (i+r) j nr (i+(r+1)) (j+1) p (by omega) (by omega) rfl hp,
    evalRaw_single (commutator D) i j n (i+(r+1)) p e rfl (by omega),
    evalRaw_single D (i+1) j (n+1) (i+(r+1)) p (by omega) (by omega) (by omega),
    evalRaw_single D i (j+1) (n+1) (i+r) p (by omega) rfl (by omega)]
  change _ = act M (i+(r+1)) j p (by omega)
    ((δ r (r+1) D.val).v i (i+(r+1)) rfl x) y + _
  rw [δ_value]
  let L := (act M (i+(r+1)) j p (by omega)).flip y
  change _ = L (_ + _) + _
  have hs (a : ℤˣ) (w : term M (i+(r+1))) : L (a • w) = a • L w :=
    map_zsmul L (a : ℤ) w
  rw [map_add L, hs]
  simp only [L, LinearMap.flip_apply, Units.smul_def, smul_add, smul_smul,
    ← Units.val_mul, ← Int.negOnePow_add, Int.negOnePow_succ, Units.val_neg, neg_smul]
  rw [add_comm r i]
  abel

private theorem evalRaw_d (D : Derivation f M r) (n nr p : ℤ)
    (h : n+r=nr) (hp : nr+1=p) (z : Raw Q n) :
    evalRaw D (n+1) p (by omega) (rawD Q n z) =
      r.negOnePow • ((M.complex ()).d nr p (evalRaw D n nr h z) -
        evalRaw (commutator D) n p (by omega) z) := by
  rw [evalRaw_d_rule D n nr p h hp z, add_sub_cancel_left, smul_smul, Int.units_mul_self, one_smul]

private def differentialAt (f : A ⟶ Q) (n : ℤ) : Degree f n →ₗ[k] Degree f (n+1) :=
  (relations f n).liftQ ((mkDegree f (n+1)).comp (rawD Q n)) (by
    intro z hz
    change mkDegree f (n+1) (rawD Q n z) = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    intro M r D
    rw [evalRaw_d D n (n+r) ((n+1)+r) rfl (by omega), hz M r D]
    have h (p : ℤ) (e : n+(r+1)=p) : evalRaw (commutator D) n p e z = 0 := by
      subst p
      exact hz M (r+1) (commutator D)
    rw [h, map_zero, sub_zero, smul_zero])

private theorem eval_d (D : Derivation f M r) (n nr p : ℤ)
    (h : n+r=nr) (hp : nr+1=p) (x : Degree f n) :
    eval D (n+1) p (by omega) (differentialAt f n x) =
      r.negOnePow • ((M.complex ()).d nr p (eval D n nr h x) -
        eval (commutator D) n p (by omega) x) := by
  obtain ⟨z,rfl⟩ := (relations f n).mkQ_surjective x
  exact evalRaw_d D n nr p h hp z

private theorem eval_zero (n p : ℤ) (h : n+r=p) (z : Degree f n) :
    eval (0 : Derivation f M r) n p h z = 0 := by
  obtain ⟨z,rfl⟩ := (relations f n).mkQ_surjective z
  exact evalRaw_zero n p h z

private theorem d_squared (n : ℤ) (z : Degree f n) :
    differentialAt f (n+1) (differentialAt f n z) = 0 := by
  apply degree_ext
  intro M r D
  rw [map_zero,
    eval_d D (n+1) ((n+1)+r) ((n+1+1)+r) rfl (by omega),
    eval_d D n (n+r) ((n+1)+r) rfl (by omega),
    eval_d (commutator D) n ((n+1)+r) ((n+1+1)+r) (by omega) (by omega),
    commutator_commutator, eval_zero, sub_zero]
  simp only [Units.smul_def, map_zsmul, map_sub]
  have h := CategoryTheory.congr_fun
    ((M.complex ()).d_comp_d (n+r) ((n+1)+r) ((n+1+1)+r)) (eval D n (n+r) rfl z)
  simp only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at h
  rw [h, zero_sub, Int.negOnePow_succ, Units.val_neg, neg_smul, smul_neg, sub_self, smul_zero]

private theorem action_id (n : ℤ) (z : Degree f n) :
    action f n 0 n (add_zero n) z Q.one = z := by
  apply degree_ext
  intro M r D
  rw [eval_action D n 0 n (n+r) (n+r) (add_zero n) rfl rfl]
  exact M.act_id () (n+r) _

private theorem action_assoc (i j l : ℤ) (z : Degree f i)
    (b : Q.complex.X j) (c : Q.complex.X l) :
    action f (i+j) l (i+j+l) rfl (action f i j (i+j) rfl z b) c =
      action f i (j+l) (i+j+l) (by omega) z (Q.mul j l (j+l) rfl b c) := by
  apply degree_ext
  intro M r D
  rw [eval_action D (i+j) l (i+j+l) (i+j+r) (i+j+l+r) rfl rfl rfl,
    eval_action D i j (i+j) (i+r) (i+j+r) rfl rfl rfl,
    eval_action D i (j+l) (i+j+l) (i+r) (i+j+l+r) (by omega) rfl rfl]
  exact act_assoc_at M (i+r) j l (i+j+r) (j+l) (i+j+l+r) (by omega) rfl (by omega) _ b c

private theorem action_d (i j n : ℤ) (e : i+j=n) (z : Degree f i) (b : Q.complex.X j) :
    differentialAt f n (action f i j n e z b) =
      action f (i+1) j (n+1) (by omega) (differentialAt f i z) b +
        i.negOnePow • action f i (j+1) (n+1) (by omega) z (Q.complex.d j (j+1) b) := by
  apply degree_ext
  intro M r D
  rw [eval_d D n (n+r) ((n+1)+r) rfl (by omega),
    eval_action D i j n (i+r) (n+r) e rfl rfl,
    eval_action (commutator D) i j n ((i+1)+r) ((n+1)+r) e (by omega) (by omega), map_add]
  rw [show eval D (n+1) ((n+1)+r) rfl (i.negOnePow •
      action f i (j+1) (n+1) (by omega) z (Q.complex.d j (j+1) b)) =
    i.negOnePow • eval D (n+1) ((n+1)+r) rfl
      (action f i (j+1) (n+1) (by omega) z (Q.complex.d j (j+1) b))
    from map_zsmul (eval D (n+1) ((n+1)+r) rfl) _ _,
    eval_action D (i+1) j (n+1) ((i+1)+r) ((n+1)+r) (by omega) rfl rfl,
    eval_action D i (j+1) (n+1) (i+r) ((n+1)+r) (by omega) rfl rfl,
    eval_d D i (i+r) ((i+1)+r) rfl (by omega),
    act_d_at M (i+r) j (n+r) ((i+1)+r) (j+1) ((n+1)+r)
      (by omega) (by omega) rfl (by omega)]
  let L := (act M ((i+1)+r) j ((n+1)+r) (by omega)).flip b
  change r.negOnePow • (L _ + _ - L _) = L (r.negOnePow • (_ - _)) + _
  simp only [Units.smul_def, map_zsmul, map_sub, smul_sub, smul_add, smul_smul,
    ← Units.val_mul, ← Int.negOnePow_add]
  rw [show r+(i+r)=i+2*r by ring, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
  abel

@[reducible] private def omegaComplex (f : A ⟶ Q) : ModuleCochain.{u,v} k :=
  CochainComplex.of (fun n => ModuleCat.of k (Degree f n))
    (fun n => ModuleCat.ofHom (differentialAt f n)) (fun n => by
      apply ModuleCat.hom_ext
      exact LinearMap.ext (d_squared n))

/-- The relative dg module of Kähler differentials. -/
@[reducible] def omega (f : A ⟶ Q) : Q.Module where
  complex _ := omegaComplex f
  act := action f
  act_id _ := action_id
  act_assoc := fun {_ _ _} => action_assoc
  leibniz := by
    intro a b i j n e z y
    change (omegaComplex f).d n (n+1) (action f i j n e z y) = _
    simp only [omegaComplex, CochainComplex.of_d]
    exact action_d i j n e z y

/-- The homogeneous term of the constructed module is the canonical quotient. -/
abbrev omegaDegree (f : A ⟶ Q) (n : ℤ) : Type v := term (omega f) n

/-- The universal symbol in the degree of its argument. -/
abbrev universalSymbol (f : A ⟶ Q) (n : ℤ) (x : Q.complex.X n) : omegaDegree f n :=
  symbolClass f n x

private theorem eval_symbol (D : Derivation f M r) (n p : ℤ) (h : n+r=p)
    (x : Q.complex.X n) :
    eval D n p h (universalSymbol f n x) = value D n p h x := by
  change eval D n p h (mkDegree f n (single Q n 0 n (add_zero n) x Q.one)) = _
  rw [eval_mk, evalRaw_single D n 0 n p p (add_zero n) h h]
  exact M.act_id () p _

private def symbolLinear (f : A ⟶ Q) (n : ℤ) : Q.complex.X n →ₗ[k] term (omega f) n where
  toFun := universalSymbol f n
  map_add' x y := by
    apply degree_ext
    intro M r D
    rw [map_add, eval_symbol, eval_symbol, eval_symbol, map_add]
  map_smul' c x := by
    apply degree_ext
    intro M r D
    rw [map_smul, eval_symbol, eval_symbol, map_smul, RingHom.id_apply]

private theorem symbol_d (n : ℤ) (x : Q.complex.X n) :
    differentialAt f n (universalSymbol f n x) = universalSymbol f (n+1) (Q.complex.d n (n+1) x) := by
  change mkDegree f (n+1) (rawD Q n (single Q n 0 n (add_zero n) x Q.one)) = _
  rw [rawD_single, show Q.complex.d 0 (0+1) Q.one = 0 from Q.toDGAlgebra.d_id (),
    map_zero, smul_zero, add_zero]
  rfl

private def diagonalCochain {X Y : ModuleCochain.{u,v} k}
    (L : ∀ n, X.X n ⟶ Y.X n) : Cochain X Y 0 :=
  Cochain.mk fun i p h => L i ≫ eqToHom (by rw [← h, add_zero])

omit [CharZero k] in
@[simp] private theorem diagonalCochain_v {X Y : ModuleCochain.{u,v} k}
    (L : ∀ n, X.X n ⟶ Y.X n) (i : ℤ) :
    (diagonalCochain L).v i i (add_zero i) = L i := by
  simp [diagonalCochain, Cochain.mk_v]

/-- The universal homogeneous derivation of degree zero. -/
def universalDerivation (f : A ⟶ Q) : Derivation f (omega f) 0 :=
  ⟨diagonalCochain fun n => ModuleCat.ofHom (symbolLinear f n), by
    constructor
    · intro i p h a
      have ep : i=p := by omega
      cases ep
      rw [diagonalCochain_v]
      change universalSymbol f i (f.chainMap.f i a) = 0
      apply degree_ext
      intro M r D
      rw [eval_symbol, map_zero]
      exact D.property.relative i (i+r) rfl a
    · intro i j n ir jr nr h hi hj hn x y
      have ei : i=ir := by omega
      have ej : j=jr := by omega
      have en : n=nr := by omega
      cases ei
      cases ej
      cases en
      simp only [diagonalCochain_v]
      change universalSymbol f n (Q.mul i j n h x y) =
        action f i j n h (universalSymbol f i x) y +
          (i*j).negOnePow • action f j i n (by omega) (universalSymbol f j y) x
      apply degree_ext
      intro M r D
      simp only [map_add, Units.smul_def, map_zsmul, eval_symbol]
      rw [eval_action D i j n (i+r) (n+r) h rfl rfl,
        eval_action D j i n (j+r) (n+r) (by omega) rfl rfl, eval_symbol, eval_symbol]
      exact D.property.leibniz i j n (i+r) (j+r) (n+r) h rfl rfl rfl x y⟩

@[simp] private theorem partial_apply (f : A ⟶ Q) (n : ℤ) (x : Q.complex.X n) :
    value (universalDerivation f) n n (add_zero n) x = universalSymbol f n x := by
  change (diagonalCochain _).v n n (add_zero n) x = _
  rw [diagonalCochain_v]
  rfl

theorem partial_commutes (f : A ⟶ Q) (n : ℤ) (x : Q.complex.X n) :
    ((omega f).complex ()).d n (n+1) (value (universalDerivation f) n n (add_zero n) x) =
      value (universalDerivation f) (n+1) (n+1) (add_zero (n+1)) (Q.complex.d n (n+1) x) := by
  change (omegaComplex f).d n (n+1) (universalSymbol f n x) =
    universalSymbol f (n+1) (Q.complex.d n (n+1) x)
  simp only [omegaComplex, CochainComplex.of_d]
  exact symbol_d n x

theorem partial_closed (f : A ⟶ Q) : δ 0 1 (universalDerivation f).val = 0 := by
  apply Cochain.ext
  intro i p h
  subst p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (δ 0 1 (universalDerivation f).val).v i (i+1) (by omega) x = 0
  rw [δ_v 0 1 (by decide) _ i (i+1) (by omega) i (i+1) (by omega) rfl]
  change ((omega f).complex ()).d i (i+1) (value (universalDerivation f) i i (add_zero i) x) +
    (1 : ℤ).negOnePow • value (universalDerivation f) (i+1) (i+1) (add_zero (i+1))
      (Q.complex.d i (i+1) x) = 0
  rw [partial_commutes]
  simp only [Int.negOnePow_one, Units.neg_smul, one_smul, add_neg_cancel]

private theorem mk_single (i j n : ℤ) (h : i+j=n) (x : Q.complex.X i) (y : Q.complex.X j) :
    mkDegree f n (single Q i j n h x y) = action f i j n h (universalSymbol f i x) y := by
  apply degree_ext
  intro M r D
  rw [eval_mk, evalRaw_single D i j n (i+r) (n+r) h rfl rfl,
    eval_action D i j n (i+r) (n+r) h rfl rfl, eval_symbol]

/-- Extension of a relative derivation from its values on the universal symbols. -/
def descend (D : Derivation f M r) : gradedHom (omega f) M r :=
  ⟨fun _ => Cochain.mk (fun n p h => ModuleCat.ofHom (eval D n p h)), by
    rintro ⟨⟩ ⟨⟩ i j n ir nr h hi hn x y
    rw [Cochain.mk_v, Cochain.mk_v]
    exact eval_action D i j n ir nr h hi hn x y⟩

@[simp] theorem descend_partial (D : Derivation f M r)
    (i p : ℤ) (h : i+r=p) (x : Q.complex.X i) :
    component (descend D) () i p h (value (universalDerivation f) i i (add_zero i) x) =
      value D i p h x := by
  rw [partial_apply]
  change (Cochain.mk (F := (omega f).complex ()) (G := M.complex ()) (fun n q e =>
    ModuleCat.ofHom (eval D n q e))).v i p h _ = _
  rw [Cochain.mk_v]
  exact eval_symbol D i p h x

/-- A homogeneous map from the differentials is determined by its values on
the universal derivation. -/
theorem gradedHom_ext {F G : gradedHom (omega f) M r}
    (H : ∀ i p (h : i+r=p) (x : Q.complex.X i),
      component F () i p h (value (universalDerivation f) i i (add_zero i) x) =
        component G () i p h (value (universalDerivation f) i i (add_zero i) x)) : F = G := by
  apply Subtype.ext
  funext a
  cases a
  apply Cochain.ext
  intro n p hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨z,rfl⟩ := (relations f n).mkQ_surjective z
  have e : (component F () n p hn).hom.comp (mkDegree f n) =
      (component G () n p hn).hom.comp (mkDegree f n) := by
    apply raw_ext
    intro i j h x y
    simp only [LinearMap.comp_apply, mk_single]
    change component F () n p hn (act (omega f) i j n h (universalSymbol f i x) y) =
      component G () n p hn (act (omega f) i j n h (universalSymbol f i x) y)
    rw [F.property (a := ()) (b := ()) i j n (i+r) p h rfl hn,
      G.property (a := ()) (b := ()) i j n (i+r) p h rfl hn]
    rw [← partial_apply, H i (i+r) rfl x]
  exact LinearMap.congr_fun e z

theorem universal (f : A ⟶ Q) (M : Q.Module) (r : ℤ) (D : Derivation f M r) :
    ∃! F : gradedHom (omega f) M r, ∀ i p (h : i+r=p) (x : Q.complex.X i),
      component F () i p h (value (universalDerivation f) i i (add_zero i) x) = value D i p h x := by
  refine ⟨descend D, descend_partial D, ?_⟩
  intro G h
  exact gradedHom_ext (fun i p e x => (h i p e x).trans (descend_partial D i p e x).symm)

/-- The module, its universal derivation and its full graded universal property. -/
def model (f : A ⟶ Q) : DifferentialModel f :=
  ⟨omega f, universalDerivation f, partial_closed f, universal f⟩

/-- Restrict a homogeneous module map to the universal derivation. -/
def readout (F : gradedHom (omega f) M r) : Derivation f M r :=
  ⟨Cochain.mk (fun i p h =>
      value (universalDerivation f) i i (add_zero i) ≫ component F () i p h), by
    constructor
    · intro i p h a
      rw [Cochain.mk_v, ModuleCat.comp_apply,
        (universalDerivation f).property.relative i i (add_zero i), map_zero]
    · intro i j n ir jr nr h hi hj hn x y
      simp only [Cochain.mk_v, ModuleCat.comp_apply]
      rw [(universalDerivation f).property.leibniz i j n i j n h
        (add_zero i) (add_zero j) (add_zero n) x y]
      simp only [Units.smul_def, map_add, map_zsmul]
      rw [F.property (a := ()) (b := ()) i j n ir nr h hi hn,
        F.property (a := ()) (b := ()) j i n jr nr (by omega) hj hn]⟩

@[simp] theorem readout_apply (F : gradedHom (omega f) M r)
    (i p : ℤ) (h : i+r=p) (x : Q.complex.X i) :
    value (readout F) i p h x =
      component F () i p h (value (universalDerivation f) i i (add_zero i) x) := by
  change (Cochain.mk (F := Q.complex) (G := M.complex ()) (fun n q e =>
    value (universalDerivation f) n n (add_zero n) ≫ component F () n q e)).v i p h x = _
  rw [Cochain.mk_v, ModuleCat.comp_apply]

private theorem derivation_ext {D E : Derivation f M r}
    (h : ∀ i p (e : i+r=p) (x : Q.complex.X i), value D i p e x = value E i p e x) : D = E := by
  apply Subtype.ext
  apply Cochain.ext
  intro i p e
  apply ModuleCat.hom_ext
  exact LinearMap.ext (h i p e)

private def readoutLinear (f : A ⟶ Q) (M : Q.Module) (r : ℤ) :
    gradedHom (omega f) M r →ₗ[k] Derivation f M r where
  toFun := readout
  map_add' F G := by
    apply derivation_ext
    intro i p h x
    simp only [readout_apply, component, Submodule.coe_add, Pi.add_apply, Cochain.add_v,
      ModuleCat.hom_add, LinearMap.add_apply, value]
  map_smul' c F := by
    apply derivation_ext
    intro i p h x
    simp only [readout_apply, RingHom.id_apply, component, Submodule.coe_smul_of_tower,
      Pi.smul_apply, Cochain.smul_v, ModuleCat.hom_smul, LinearMap.smul_apply, value]

private theorem descend_readout (F : gradedHom (omega f) M r) : descend (readout F) = F := by
  apply gradedHom_ext
  intro i p h x
  rw [descend_partial, readout_apply]

private theorem readout_descend (D : Derivation f M r) : readout (descend D) = D := by
  apply derivation_ext
  intro i p h x
  rw [readout_apply, descend_partial]

/-- The representing linear equivalence in every homogeneous degree. -/
def homEquiv (f : A ⟶ Q) (M : Q.Module) (r : ℤ) :
    Derivation f M r ≃ₗ[k] gradedHom (omega f) M r :=
  (LinearEquiv.ofBijective (readoutLinear f M r)
    ⟨Function.LeftInverse.injective descend_readout, fun D => ⟨descend D, readout_descend D⟩⟩).symm

theorem homEquiv_apply (D : Derivation f M r) : homEquiv f M r D = descend D := by
  apply (homEquiv f M r).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (readout_descend D).symm

private def commutatorLinear (f : A ⟶ Q) (M : Q.Module) (r : ℤ) :
    Derivation f M r →ₗ[k] Derivation f M (r+1) where
  toFun := commutator
  map_add' D E := Subtype.ext (δ_add r (r+1) D.val E.val)
  map_smul' c D := Subtype.ext (δ_smul r (r+1) c D.val)

/-- The complex of all relative graded derivations with commutator differential. -/
@[reducible] def derivationComplex (f : A ⟶ Q) (M : Q.Module) : ModuleCochain.{u,v} k :=
  CochainComplex.of (fun r => ModuleCat.of k (Derivation f M r))
    (fun r => ModuleCat.ofHom (commutatorLinear f M r)) (fun r => by
      apply ModuleCat.hom_ext
      exact LinearMap.ext commutator_commutator)

theorem derivationComplex_d (f : A ⟶ Q) (M : Q.Module) (r : ℤ) (D : Derivation f M r) :
    (derivationComplex f M).d r (r+1) D = commutator D := by
  simp only [derivationComplex, CochainComplex.of_d]
  rfl

private theorem descend_d (D : Derivation f M r) :
    (homComplex (omega f) M).d r (r+1) (descend D) = descend (commutator D) := by
  apply gradedHom_ext
  intro i p h x
  rw [descend_partial]
  change (δ r (r+1) ((descend D).val ())).v i p h
      (value (universalDerivation f) i i (add_zero i) x) = _
  rw [δ_v r (r+1) rfl _ i p h (i+r) (i+1) (by omega) rfl]
  change (M.complex ()).d (i+r) p (component (descend D) () i (i+r) rfl
      (value (universalDerivation f) i i (add_zero i) x)) +
    (r+1).negOnePow • component (descend D) () (i+1) p (by omega)
      (((omega f).complex ()).d i (i+1) (value (universalDerivation f) i i (add_zero i) x)) = _
  rw [partial_commutes]
  rw [descend_partial, descend_partial]
  exact (δ_value D.val i p h x).symm

/-- The representing equivalences commute with the cochain differentials. -/
def homComplexIso (f : A ⟶ Q) (M : Q.Module) :
    derivationComplex f M ≅ homComplex (omega f) M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r => (homEquiv f M r).toModuleIso) (by
      intro i j h
      change i+1=j at h
      subst j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro D
      change (homComplex (omega f) M).d i (i+1) (homEquiv f M i D) =
        (homEquiv f M (i+1)) ((derivationComplex f M).d i (i+1) D)
      rw [derivationComplex_d, homEquiv_apply, homEquiv_apply]
      exact descend_d D)

/-- A closed degree-zero relative derivation gives a strict module map. -/
def descendStrict (D : Derivation f M 0) (hD : δ 0 1 D.val = 0) : omega f ⟶ M :=
  Tensor.homOfDegrees (fun n => eval D n n (add_zero n)) (by
    intro n z
    have h : commutator D = 0 := Subtype.ext hD
    change (M.complex ()).d n (n+1) (eval D n n (add_zero n) z) =
      eval D (n+1) (n+1) (add_zero (n+1)) ((omegaComplex f).d n (n+1) z)
    simp only [omegaComplex, CochainComplex.of_d]
    change _ = eval D (n+1) (n+1) (add_zero (n+1)) (differentialAt f n z)
    rw [eval_d D n n (n+1) (add_zero n) rfl, h, eval_zero, sub_zero, Int.negOnePow_zero, one_smul])
    (fun i j n e z y => eval_action D i j n i n e (add_zero i) (add_zero n) z y)

@[simp] theorem descendStrict_symbol (D : Derivation f M 0) (hD : δ 0 1 D.val = 0)
    (i : ℤ) (x : Q.complex.X i) :
    ((descendStrict D hD).app ()).f i (value (universalDerivation f) i i (add_zero i) x) =
      value D i i (add_zero i) x :=
  eval_symbol D i i (add_zero i) x

section Comparison

local notation "tensorPure" => Specs.DerivedFormalization.Affine.Tensor.pure

variable {M' : Q'.Module} (g : Q ⟶ Q')

private theorem signedLeft_regular (i j n : ℤ) (e : i+j=n)
    (a : Q'.complex.X i) (b : Q'.complex.X j) :
    signedLeft (regular Q') i j n e a b = Q'.mul i j n e a b :=
  (Q'.graded_comm i j n e a b).symm

private def extendDegree (L : M ⟶ restrict g M') (n : ℤ) :
    term ((Tensor.baseChange g).obj M) n →ₗ[k] term M' n :=
  Tensor.liftDegree (f := g) (M := M) (N := regular Q')
    (fun i j h => (act M' i j n h).comp ((L.app ()).f i).hom) (by
      intro i l j h x a b
      change act M' (i+l) j n h ((L.app ()).f (i+l) (act M i l (i+l) rfl x a)) b =
        act M' i (l+j) n (by omega) ((L.app ()).f i x)
          (signedLeft (regular Q') l j (l+j) rfl (g.chainMap.f l a) b)
      rw [L.comm_act, signedLeft_regular]
      exact act_assoc_at M' i l j (i+l) (l+j) n rfl rfl h _ _ _)

@[simp] private theorem extendDegree_pure (L : M ⟶ restrict g M') (i j n : ℤ)
    (h : i+j=n) (x : term M i) (y : Q'.complex.X j) :
    extendDegree g L n (tensorPure g (N := regular Q') i j n h x y) =
      act M' i j n h ((L.app ()).f i x) y := by
  unfold extendDegree
  rw [Tensor.liftDegree_pure]
  rfl

/-- The balanced scalar extension of a strict map into a restricted module. -/
def extend (L : M ⟶ restrict g M') : (Tensor.baseChange g).obj M ⟶ M' :=
  Tensor.homOfDegrees (extendDegree g L) (by
    intro n z
    suffices e : ((M'.complex ()).d n (n+1)).hom.comp (extendDegree g L n) =
        (extendDegree g L (n+1)).comp ((((Tensor.baseChange g).obj M).complex ()).d n (n+1)).hom by
      exact LinearMap.congr_fun e z
    apply Tensor.pure_ext
    intro i j h x y
    change (M'.complex ()).d n (n+1)
      (extendDegree g L n (tensorPure g (N := regular Q') i j n h x y)) =
      extendDegree g L (n+1)
        ((((Tensor.baseChange g).obj M).complex ()).d n (n+1)
          (tensorPure g (N := regular Q') i j n h x y))
    rw [extendDegree_pure, Tensor.d_pure_at g i j n (i+1) (j+1) (n+1) h rfl rfl rfl]
    simp only [map_add, Units.smul_def, map_zsmul]
    rw [extendDegree_pure, extendDegree_pure]
    rw [M'.leibniz (a := ()) (b := ()) i j n h]
    have hc := CategoryTheory.congr_fun ((L.app ()).comm i (i+1)) x
    simp only [ModuleCat.comp_apply] at hc
    rw [← hc]
    rfl) (by
      intro n l q h z b
      suffices e : (extendDegree g L q).comp
          ((act ((Tensor.baseChange g).obj M) n l q h).flip b) =
        ((act M' n l q h).flip b).comp (extendDegree g L n) by
        exact LinearMap.congr_fun e z
      apply Tensor.pure_ext
      intro i j hn x y
      change extendDegree g L q
        (act ((Tensor.baseChange g).obj M) n l q h (tensorPure g (N := regular Q') i j n hn x y) b) =
        act M' n l q h (extendDegree g L n (tensorPure g (N := regular Q') i j n hn x y)) b
      rw [Tensor.act_pure, extendDegree_pure, extendDegree_pure]
      exact (act_assoc_at M' i j l n (j+l) q hn rfl h _ y b).symm)

@[simp] theorem extend_pure (L : M ⟶ restrict g M') (i j n : ℤ)
    (h : i+j=n) (x : term M i) (y : Q'.complex.X j) :
    ((extend g L).app ()).f n (tensorPure g (N := regular Q') i j n h x y) =
      act M' i j n h ((L.app ()).f i x) y :=
  extendDegree_pure g L i j n h x y

/-- Scalar-extended differentials are generated by the universal symbols
tensored with homogeneous target scalars. -/
theorem comparison_ext {L K : (Tensor.baseChange g).obj (omega f) ⟶ M'}
    (h : ∀ (i j n : ℤ) (e : i+j=n) (x : Q.complex.X i) (y : Q'.complex.X j),
      (L.app ()).f n (tensorPure g (N := regular Q') i j n e
        (value (universalDerivation f) i i (add_zero i) x) y) =
        (K.app ()).f n (tensorPure g (N := regular Q') i j n e
          (value (universalDerivation f) i i (add_zero i) x) y)) : L = K := by
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Tensor.pure_ext
  intro i j e z y
  obtain ⟨z,rfl⟩ := (relations f i).mkQ_surjective z
  let B := ((Tensor.pair g (M := omega f) (N := regular Q') i j n e).flip y).comp (mkDegree f i)
  have H : ((L.app ()).f n).hom.comp B = ((K.app ()).f n).hom.comp B := by
    apply raw_ext
    intro p q ep x b
    simp only [B, LinearMap.comp_apply, LinearMap.flip_apply, mk_single]
    change (L.app ()).f n (tensorPure g (N := regular Q') i j n e
        (act (omega f) p q i ep (universalSymbol f p x) b) y) =
      (K.app ()).f n (tensorPure g (N := regular Q') i j n e
        (act (omega f) p q i ep (universalSymbol f p x) b) y)
    rw [Tensor.pure_balance g p q j i (q+j) n ep rfl e, ← partial_apply]
    exact h p (q+j) n (by omega) x
      (signedLeft (regular Q') q j (q+j) rfl (g.chainMap.f q b) y)
  exact LinearMap.congr_fun H z

variable (a : A ⟶ A') (f' : A' ⟶ Q') (sq : f ≫ g = a ≫ f')

include sq

/-- The target universal derivation pulled back along the top algebra map. -/
def squareDerivation : Derivation f (restrict g (omega f')) 0 :=
  ⟨diagonalCochain (fun i =>
    g.chainMap.f i ≫ value (universalDerivation f') i i (add_zero i)), by
    constructor
    · intro i p h x
      have ep : i=p := by omega
      cases ep
      rw [diagonalCochain_v, ModuleCat.comp_apply]
      have e := CategoryTheory.congr_fun (congrArg (fun t : A ⟶ Q' => t.chainMap.f i) sq) x
      change g.chainMap.f i (f.chainMap.f i x) = f'.chainMap.f i (a.chainMap.f i x) at e
      rw [e]
      exact (universalDerivation f').property.relative i i (add_zero i) _
    · intro i j n ir jr nr e hi hj hn x y
      have ei : i=ir := by omega
      have ej : j=jr := by omega
      have en : n=nr := by omega
      cases ei
      cases ej
      cases en
      simp only [diagonalCochain_v]
      change value (universalDerivation f') n n (add_zero n) (g.chainMap.f n (Q.mul i j n e x y)) =
        act (omega f') i j n e
          (value (universalDerivation f') i i (add_zero i) (g.chainMap.f i x)) (g.chainMap.f j y) +
        (i*j).negOnePow • act (omega f') j i n (by omega)
          (value (universalDerivation f') j j (add_zero j) (g.chainMap.f j y)) (g.chainMap.f i x)
      rw [g.map_mul]
      exact (universalDerivation f').property.leibniz i j n i j n e
        (add_zero i) (add_zero j) (add_zero n) (g.chainMap.f i x) (g.chainMap.f j y)⟩

@[simp] theorem squareDerivation_apply (i : ℤ) (x : Q.complex.X i) :
    value (squareDerivation g a f' sq) i i (add_zero i) x =
      value (universalDerivation f') i i (add_zero i) (g.chainMap.f i x) := by
  change (diagonalCochain _).v i i (add_zero i) x = _
  rw [diagonalCochain_v, ModuleCat.comp_apply]

theorem squareDerivation_closed : δ 0 1 (squareDerivation g a f' sq).val = 0 := by
  apply Cochain.ext
  intro i p h
  subst p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (δ 0 1 (squareDerivation g a f' sq).val).v i (i+1) (by omega) x = 0
  rw [δ_v 0 1 (by decide) _ i (i+1) (by omega) i (i+1) (by omega) rfl]
  change ((omega f').complex ()).d i (i+1)
      (value (squareDerivation g a f' sq) i i (add_zero i) x) +
    (1 : ℤ).negOnePow • value (squareDerivation g a f' sq) (i+1) (i+1) (add_zero (i+1))
      (Q.complex.d i (i+1) x) = 0
  rw [squareDerivation_apply, squareDerivation_apply, partial_commutes]
  have hc := CategoryTheory.congr_fun (g.chainMap.comm i (i+1)) x
  simp only [ModuleCat.comp_apply] at hc
  rw [hc]
  simp only [Int.negOnePow_one, Units.neg_smul, one_smul, add_neg_cancel]

/-- The scalar extension comparison for a commutative square of cdgas. -/
def comparison : (Tensor.baseChange g).obj (omega f) ⟶ omega f' :=
  extend g (descendStrict (squareDerivation g a f' sq) (squareDerivation_closed g a f' sq))

@[simp] theorem comparison_symbol (i j n : ℤ) (h : i+j=n)
    (x : Q.complex.X i) (y : Q'.complex.X j) :
    ((comparison g a f' sq).app ()).f n
        (tensorPure g (N := regular Q') i j n h
          (value (universalDerivation f) i i (add_zero i) x) y) =
      act (omega f') i j n h (value (universalDerivation f') i i (add_zero i) (g.chainMap.f i x)) y := by
  unfold comparison
  rw [extend_pure, descendStrict_symbol, squareDerivation_apply]

omit sq

/-- The comparison over the same base algebra. -/
def mapOver {f'' : A ⟶ Q'} (hf : f ≫ g = f'') : (Tensor.baseChange g).obj (omega f) ⟶ omega f'' :=
  comparison g (𝟙 A) f'' (by simpa using hf)

end Comparison


/-- The construction realizes the graded and dg universal properties on the
same module and yields the specified, uniquely determined base comparisons. -/
theorem differentials_construction : DifferentialsConstruction.{u,v} := by
  intro k _ _
  refine ⟨Tensor.moduleTensorModel k, fun f => model f, ?_, ?_, ?_, ?_⟩
  · intro Q Q' g
    exact Tensor.moduleTensor_formulas g (regular Q')
  · intro A Q f i x
    exact partial_commutes f i x
  · intro A Q f M
    refine ⟨derivationComplex f M, fun _ => LinearEquiv.refl k _, homComplexIso f M, ?_, ?_⟩
    · intro r D
      change ((derivationComplex f M).d r (r+1) D).val = _
      rw [derivationComplex_d]
      rfl
    · intro r i p h D x
      change component (homEquiv f M r D) () i p h
        (value (universalDerivation f) i i (add_zero i) x) = value D i p h x
      rw [homEquiv_apply, descend_partial]
  · intro A Q A' Q' f f' a g sq
    refine ⟨comparison g a f' sq, comparison_symbol g a f' sq, ?_⟩
    intro L hL
    apply comparison_ext g
    intro i j n e x y
    exact (hL i j n e x y).trans (comparison_symbol g a f' sq i j n e x y).symm

end
end DerivedFormalization.Affine.Kahler
