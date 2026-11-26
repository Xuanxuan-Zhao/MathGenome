import Specs.LinearAlgebraicGroups.Classification.IntegralLinkedRoots
import LinearAlgebraicGroups.Classification.Pinning
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.Derivative

open WithConv
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Classification.IntegralLinkedRoots

open _root_.LinearAlgebraicGroups.Specs.IntegralLinkedRoots
open _root_.LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum)

noncomputable section

attribute [local instance] pointGroup

section WeylWords

variable {D E : BasedRootDatum.{u}}

/-- An ordinary lattice map intertwines the reflections on root indices. -/
theorem mapReflection (h : LatticeMap D E) (j i : D.I) :
    h.roots (D.datum.reflectionPerm j i) = E.datum.reflectionPerm (h.roots j) (h.roots i) := by
  let f : E.X →+ D.X := h.characters.toAdditive
  have rootMap (i : D.I) : f (E.datum.root (h.roots i)) = D.datum.root i :=
    congrArg Multiplicative.toAdd (h.root_eq i)
  have pairing (i j : D.I) : D.datum.pairing i j = E.datum.pairing (h.roots i) (h.roots j) := by
    have e := h.coroot_eq j (E.datum.root (h.roots i))
    change (D.datum.toLinearMap (f (E.datum.root (h.roots i)))) (D.datum.coroot j) = _ at e
    rw [rootMap] at e
    exact e
  apply E.datum.root.injective
  apply h.injective
  change Multiplicative.ofAdd (f (E.datum.root (h.roots (D.datum.reflectionPerm j i)))) =
    Multiplicative.ofAdd (f (E.datum.root (E.datum.reflectionPerm (h.roots j) (h.roots i))))
  congr 1
  rw [rootMap, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, map_sub, map_zsmul,
    rootMap, rootMap, pairing]

/-- Every root is obtained by simple reflections from some simple root. -/
theorem existsSimpleWord (i : D.I) :
    ∃ (j : ↥D.base.support) (w : List ↥D.base.support), reflectWord w j.val = i := by
  let := D.finiteRoots
  let := D.reduced
  have pos (j : D.I) (hj : D.base.IsPos j) :
      ∃ (s : ↥D.base.support) (w : List ↥D.base.support), reflectWord w s.val = j := by
    apply hj.induction_on_reflect
    · exact fun l hl => ⟨⟨l, hl⟩, [], rfl⟩
    · rintro l k ⟨s, w, rfl⟩ hk
      exact ⟨s, ⟨k, hk⟩ :: w, rfl⟩
  let := D.datum.indexNeg
  rcases RootPairing.Base.IsPos.or_neg D.base i with hi | hi
  · exact pos i hi
  · obtain ⟨j, w, hw⟩ := pos (-i) hi
    have rootNeg (j : D.I) : D.datum.root (-j) = -D.datum.root j := by
      simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
    have hneg (w : List ↥D.base.support) (j : D.I) :
        reflectWord w (-j) = -(reflectWord w j) := by
      induction w with
      | nil => rfl
      | cons k w ih =>
        change D.datum.reflectionPerm k.val (reflectWord w (-j)) =
          -(D.datum.reflectionPerm k.val (reflectWord w j))
        rw [ih]
        apply D.datum.root.injective
        simp only [rootNeg, RootPairing.root_reflectionPerm, map_neg]
    refine ⟨j, w ++ [j], ?_⟩
    change List.foldr _ j.val (w ++ [j]) = i
    rw [List.foldr_append]
    have e : D.datum.reflectionPerm j.val j.val = -(j.val : D.I) := by
      apply D.datum.root.injective
      simp only [rootNeg, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
    change reflectWord w (D.datum.reflectionPerm j.val j.val) = i
    rw [e, hneg, hw, neg_neg]

/-- Corresponding words give corresponding root indices. -/
theorem mapReflectWord (h : LatticeMap D E) (w : List ↥D.base.support) (i : D.I) :
    h.roots (reflectWord w i) = reflectWord (w.map h.simple) (h.roots i) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    change h.roots (D.datum.reflectionPerm j.val (reflectWord w i)) =
      E.datum.reflectionPerm (h.roots j.val) (reflectWord (w.map h.simple) (h.roots i))
    rw [mapReflection, ih]

private theorem mapRootWordStart (h : LatticeMap D E) (w : RootWord D) :
    h.roots w.start = (w.map h).start := by
  cases w with
  | mk simple negative word =>
    cases negative
    · rfl
    · exact mapReflection h simple.val simple.val

/-- The choices on simple roots and their opposites keep both prescribed seed coordinates. -/
private theorem chooseRootWords (D : BasedRootDatum.{u}) :
    ∃ w : D.I → RootWord D,
      (∀ i, reflectWord (w i).word (w i).start = i) ∧
      (∀ i ∈ D.base.support, (w i).word = []) ∧
      (∀ i ∈ D.base.support, (w (D.datum.reflectionPerm i i)).word = []) := by
  classical
  have seed (i : D.I) :
      ∃ v : RootWord D, reflectWord v.word v.start = i ∧
        ((i ∈ D.base.support ∨ ∃ j ∈ D.base.support, D.datum.reflectionPerm j j = i) → v.word = []) := by
    by_cases hp : i ∈ D.base.support
    · exact ⟨⟨⟨i, hp⟩, false, []⟩, rfl, fun _ => rfl⟩
    by_cases hq : ∃ j ∈ D.base.support, D.datum.reflectionPerm j j = i
    · obtain ⟨j, hj, hj'⟩ := hq
      exact ⟨⟨⟨j, hj⟩, true, []⟩, hj', fun _ => rfl⟩
    · obtain ⟨j, w, hw⟩ := existsSimpleWord i
      exact ⟨⟨j, false, w⟩, hw, fun e => (e.elim hp hq).elim⟩
  choose words hw hseed using seed
  exact ⟨words, hw, fun i hi => hseed i (.inl hi), fun i hi => hseed _ (.inr ⟨i, hi, rfl⟩)⟩

end WeylWords

section HopfPoints

variable {R A B S T : Type u} [CommRing R] [CommRing A] [CommRing B]
  [HopfAlgebra R A] [HopfAlgebra R B] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- Change the test algebra of a convolution point. -/
private def mapPoint (g : S →ₐ[R] T) : HopfPoints R A S →* HopfPoints R A T where
  toFun p := toConv (g.comp p.ofConv)
  map_one' := by
    apply WithConv.ext
    ext a
    simp only [AlgHom.convOne_def, WithConv.ofConv_toConv, AlgHom.comp_apply, Algebra.ofId_apply,
      AlgHom.commutes]
  map_mul' p q := WithConv.ext (AlgHom.comp_convMul_distrib g p q)

/-- Apply a homomorphism of affine groups to a test point. -/
private def mapGroup (f : B →ₐc[R] A) : HopfPoints R A S →* HopfPoints R B S where
  toFun p := toConv (p.ofConv.comp f.toAlgHom)
  map_one' := by
    apply WithConv.ext
    ext a
    simp only [AlgHom.convOne_def, WithConv.ofConv_toConv, AlgHom.comp_apply, Algebra.ofId_apply]
    congr 1
    exact DFunLike.congr_fun (BialgHom.counitAlgHom_comp f) a
  map_mul' p q := WithConv.ext (AlgHom.convMul_comp_bialgHom_distrib p q f)

private theorem evaluate_natural (x : A →ₐ[R] Polynomial R) (g : S →ₐ[R] T) (a : S) :
    mapPoint g (evaluate x a) = evaluate x (g a) := by
  apply WithConv.ext
  have e : g.comp (Polynomial.aeval a : Polynomial R →ₐ[R] S) = Polynomial.aeval (g a) := by
    ext
    simp
  exact congrArg (fun p : Polynomial R →ₐ[R] T => p.comp x) e

private def additiveHom {x : A →ₐ[R] Polynomial R} (hx : IsAdditive x) :
    Multiplicative S →* HopfPoints R A S where
  toFun a := evaluate x a.toAdd
  map_one' := (hx (CommAlgCat.of R S)).1
  map_mul' a b := (hx (CommAlgCat.of R S)).2 a.toAdd b.toAdd

variable {D E : BasedRootDatum.{u}}

private theorem matchRankOneWord (h : LatticeMap D E)
    (x : D.I → A →ₐ[R] Polynomial R) (y : E.I → B →ₐ[R] Polynomial R)
    (g : HopfPoints R A S →* HopfPoints R B S)
    (positive : ∀ (i : ↥D.base.support) (a : S), g (evaluate (x i.val) a) =
      evaluate (y (h.roots i.val)) a)
    (negative : ∀ (i : ↥D.base.support) (a : S),
      g (evaluate (x (D.datum.reflectionPerm i.val i.val)) a) =
        evaluate (y (E.datum.reflectionPerm (h.roots i.val) (h.roots i.val))) a)
    (i : ↥D.base.support) (a : Sˣ) :
    g (rankOneWord (x i.val) (x (D.datum.reflectionPerm i.val i.val)) a) =
      rankOneWord (y (h.roots i.val)) (y (E.datum.reflectionPerm (h.roots i.val) (h.roots i.val))) a := by
  simp only [rankOneWord, map_mul, positive, negative]

/-- For coordinates chosen by the same words, preserving the linked simple
pairs suffices to preserve every coordinate on the test algebra. -/
theorem matchTransportedCoordinates (h : LatticeMap D E) (S : CommAlgCat.{u} R)
    (x : D.I → A →ₐ[R] Polynomial R) (y : E.I → B →ₐ[R] Polynomial R)
    (w : D.I → RootWord D) (hx : UsesWords x w)
    (hy : UsesWords y (fun j => (w (h.roots.symm j)).map h))
    (g : HopfPoints R A S →* HopfPoints R B S)
    (positive : ∀ (i : ↥D.base.support) (a : S), g (evaluate (x i.val) a) =
      evaluate (y (h.roots i.val)) a)
    (negative : ∀ (i : ↥D.base.support) (a : S),
      g (evaluate (x (D.datum.reflectionPerm i.val i.val)) a) =
        evaluate (y (E.datum.reflectionPerm (h.roots i.val) (h.roots i.val))) a)
    (i : D.I) (a : S) : g (evaluate (x i) a) = evaluate (y (h.roots i)) a := by
  have wordMap (word : List ↥D.base.support) :
      g (evaluateWord x word S) = evaluateWord y (word.map h.simple) S := by
    induction word with
    | nil => exact g.map_one
    | cons j l ih =>
      change g (rankOneWord (x j.val) (x (D.datum.reflectionPerm j.val j.val)) (1 : Sˣ) *
        evaluateWord x l S) =
        rankOneWord (y (h.roots j.val)) (y (E.datum.reflectionPerm (h.roots j.val) (h.roots j.val)))
          (1 : Sˣ) * evaluateWord y (l.map h.simple) S
      rw [map_mul, matchRankOneWord h x y g positive negative, ih]
  have seedMap (v : RootWord D) : g (evaluate (x v.start) a) = evaluate (y (v.map h).start) a := by
    cases v with
    | mk j n l =>
      cases n
      · exact positive j a
      · exact negative j a
  have hx' := (hx i).2 S a
  have hy' := (hy (h.roots i)).2 S a
  simp only [Equiv.symm_apply_apply] at hy'
  rw [hx', hy', map_mul, map_mul, map_inv, wordMap, seedMap]
  rfl

end HopfPoints

section Gauss

variable {S H : Type u} [CommRing S] [Group H]

local notation "⟨+" a "+⟩" => Multiplicative.ofAdd a

private def weylElement (x y : Multiplicative S →* H) (a : Sˣ) : H :=
  x ⟨+ (a : S) +⟩ * y ⟨+ (-(↑a⁻¹ : S)) +⟩ * x ⟨+ (a : S) +⟩

/-- The open rank-one Gauss formula follows from the coroot word and the
two torus weights. This version takes both denominators to be units. -/
private theorem gaussWithUnits (x y : Multiplicative S →* H) (t : Sˣ →* H)
    (ht : ∀ a, weylElement x y a = t a * weylElement x y 1)
    (hx : ∀ a : Sˣ, ∀ b : S, t a * x ⟨+ b +⟩ * (t a)⁻¹ = x ⟨+ (a : S)^2 * b +⟩)
    (hy : ∀ a : Sˣ, ∀ b : S, t a * y ⟨+ b +⟩ * (t a)⁻¹ = y ⟨+ (↑a⁻¹ : S)^2 * b +⟩)
    (u : S) (v c : Sˣ) (hc : (c : S) = 1 + u * (v : S)) :
    x ⟨+ u +⟩ * y ⟨+ (v : S) +⟩ =
      y ⟨+ (v : S) * (↑c⁻¹ : S) +⟩ * t c * x ⟨+ u * (↑c⁻¹ : S) +⟩ := by
  let n := weylElement x y 1
  have addx (a b : S) : x ⟨+ (a + b) +⟩ = x ⟨+ a +⟩ * x ⟨+ b +⟩ :=
    x.map_mul ⟨+ a +⟩ ⟨+ b +⟩
  have tz (a : Sˣ) : t a * n * (t a)⁻¹ = t a * (t a * n) := by
    change t a * weylElement x y 1 * (t a)⁻¹ = t a * (t a * n)
    calc
      _ = (t a * x ⟨+ (1 : Sˣ) +⟩ * (t a)⁻¹) *
        (t a * y ⟨+ (-(↑(1 : Sˣ)⁻¹ : S)) +⟩ * (t a)⁻¹) *
        (t a * x ⟨+ (1 : Sˣ) +⟩ * (t a)⁻¹) := by
          unfold weylElement
          group
      _ = weylElement x y (a^2) := by
        rw [hx, hy]
        simp [weylElement]
      _ = t a * (t a * n) := by rw [ht, map_pow, pow_two, mul_assoc]
  have nt (a : Sˣ) : n * t a = (t a)⁻¹ * n := by
    have e := tz a⁻¹
    simp only [map_inv, inv_inv] at e
    calc
      n * t a = t a * ((t a)⁻¹ * n * t a) := by group
      _ = (t a)⁻¹ * n := by rw [e]; group
  let z := -v⁻¹
  let b := c * v⁻¹
  have hu : (b : S) + (z : S) = u := by
    change (c : S) * (↑v⁻¹ : S) + -(↑v⁻¹ : S) = u
    rw [hc, add_mul, one_mul, mul_assoc, v.mul_inv, mul_one]
    ring
  have hzero : (z : S) + (↑v⁻¹ : S) = 0 := by simp [z]
  have hv : -(↑z⁻¹ : S) = (v : S) := by simp [z]
  have hv' : -(↑(-b)⁻¹ : S) = (v : S) * (↑c⁻¹ : S) := by simp [b]
  have hdecomp :
      x ⟨+ (b : S) +⟩ * weylElement x y z * x ⟨+ (↑v⁻¹ : S) +⟩ =
        x ⟨+ u +⟩ * y ⟨+ (v : S) +⟩ := by
    unfold weylElement
    rw [← mul_assoc, ← mul_assoc, ← addx, hu, hv, mul_assoc _ (x _) (x _), ← addx, hzero]
    simp
  have hcancel : x ⟨+ (b : S) +⟩ * weylElement x y (-b) =
      y ⟨+ (v : S) * (↑c⁻¹ : S) +⟩ * x ⟨+ (-(b : S)) +⟩ := by
    unfold weylElement
    simp only [Units.val_neg, hv', ← mul_assoc]
    rw [← addx, add_neg_cancel]
    simp
  have hw : weylElement x y z = weylElement x y (-b) * t c := by
    have hb : -b = z * c := by
      dsimp [b, z]
      rw [neg_mul, mul_comm c]
    rw [ht z, ht (-b), hb, map_mul, mul_assoc, nt]
    change t z * n = _
    group
  have hparam' : -((↑c⁻¹ : S)^2 * (b : S)) + (↑v⁻¹ : S) = u * (↑c⁻¹ : S) := by
    have hb : (↑c⁻¹ : S) * (b : S) = (↑v⁻¹ : S) := by
      change (↑c⁻¹ : S) * ((c : S) * (↑v⁻¹ : S)) = _
      rw [← mul_assoc, c.inv_mul, one_mul]
    rw [pow_two, mul_assoc, hb]
    calc
      _ = (↑c⁻¹ : S) * (((c : S) - 1) * (↑v⁻¹ : S)) := by
        rw [← mul_assoc, mul_sub, c.inv_mul, mul_one, sub_mul, one_mul]
        ring
      _ = _ := by
        rw [hc, add_sub_cancel_left, mul_assoc, v.mul_inv, mul_one, mul_comm]
  rw [← hdecomp, hw, ← mul_assoc _ (weylElement x y (-b)) (t c), hcancel]
  have hmove : x ⟨+ (-(b : S)) +⟩ * t c =
      t c * x ⟨+ (↑c⁻¹ : S)^2 * (-(b : S)) +⟩ := by
    have e := hx c⁻¹ (-(b : S))
    rw [map_inv, inv_inv] at e
    rw [← e]
    group
  rw [mul_assoc _ (x _) (t c), hmove, ← mul_assoc _ (t c) (x _),
    mul_assoc _ (x _) (x _), ← addx, mul_neg, hparam']

end Gauss

section GaussDescent

variable {R A : Type u} [CommRing R] [IsDomain R] [CommRing A] [HopfAlgebra R A]

set_option maxHeartbeats 700000 in
/-- The Gauss formula requires only the main denominator to be invertible.
Use an indeterminate for each parameter, then remove the extra localization
by injectivity and specialize the resulting universal equality. -/
private theorem gauss (x y : A →ₐ[R] Polynomial R) (hx : IsAdditive x) (hy : IsAdditive y)
    (t : (S : CommAlgCat.{u} R) → Sˣ →* HopfPoints R A S)
    (htNat : ∀ {S T : CommAlgCat.{u} R} (g : S →ₐ[R] T) (a : Sˣ),
      mapPoint g (t S a) = t T (Units.map g.toMonoidHom a))
    (ht : ∀ (S : CommAlgCat.{u} R) (a : Sˣ), rankOneWord x y a = t S a * rankOneWord x y 1)
    (hp : ∀ (S : CommAlgCat.{u} R) (a : Sˣ) (b : S),
      t S a * evaluate x b * (t S a)⁻¹ = evaluate x ((a : S)^2 * b))
    (hm : ∀ (S : CommAlgCat.{u} R) (a : Sˣ) (b : S),
      t S a * evaluate y b * (t S a)⁻¹ = evaluate y ((↑a⁻¹ : S)^2 * b))
    (S : CommAlgCat.{u} R) (u v : S) (c : Sˣ) (hc : (c : S) = 1 + u * v) :
    evaluate x u * evaluate y v =
      evaluate y (v * (↑c⁻¹ : S)) * t S c * evaluate x (u * (↑c⁻¹ : S)) := by
  let P := Polynomial (Polynomial R)
  let U : P := Polynomial.C Polynomial.X
  let V : P := Polynomial.X
  let d : P := 1 + U * V
  have hd : d ≠ 0 := by
    intro e
    have h := congrArg (fun p : P => p.coeff 0) e
    change (1 + U * Polynomial.X : P).coeff 0 = (0 : P).coeff 0 at h
    rw [Polynomial.coeff_add, Polynomial.coeff_mul_X_zero] at h
    simp at h
  let L := Localization.Away d
  letI : IsDomain L := IsLocalization.Away.isDomain L hd
  let Lc := CommAlgCat.of R L
  obtain ⟨C, hC⟩ := IsLocalization.Away.algebraMap_isUnit (S := L) d
  let l := algebraMap P L
  let F := FractionRing L
  let Fc := CommAlgCat.of R F
  let j := IsScalarTower.toAlgHom R L F
  have hj : Function.Injective j := IsFractionRing.injective L F
  have hV : j (l V) ≠ 0 := by
    apply fun e => Polynomial.X_ne_zero ((IsLocalization.injective L
      (powers_le_nonZeroDivisors_of_noZeroDivisors hd)) (by
        apply hj
        simpa [l, V] using e))
  let Vf : Fˣ := Units.mk0 _ hV
  let Cf := Units.map j.toMonoidHom C
  have hfc : (Cf : F) = 1 + j (l U) * (Vf : F) := by
    change j (C : L) = 1 + j (l U) * j (l V)
    rw [hC]
    simp [l, d]
  have eg := gaussWithUnits (additiveHom (S := F) hx) (additiveHom (S := F) hy) (t Fc)
    (fun a => ht Fc a) (fun a b => hp Fc a b) (fun a b => hm Fc a b) (j (l U)) Vf Cf hfc
  have eg' : evaluate x (l U) * evaluate y (l V) =
      evaluate y (l V * (↑C⁻¹ : L)) * t Lc C * evaluate x (l U * (↑C⁻¹ : L)) := by
    apply (show Function.Injective (mapPoint (A := A) j) from fun p q e => by
      apply WithConv.ext
      ext a
      exact hj (congrArg (fun z : HopfPoints R A F => z.ofConv a) e))
    rw [map_mul, map_mul, map_mul, evaluate_natural, evaluate_natural, evaluate_natural,
      evaluate_natural, htNat (S := Lc) (T := Fc), map_mul, map_mul]
    exact eg
  let φ : P →ₐ[R] S :=
    Polynomial.eval₂AlgHom (Polynomial.aeval u : Polynomial R →ₐ[R] S) v (fun _ => Commute.all _ _)
  have hφU : φ U = u := by
    change Polynomial.eval₂ (Polynomial.aeval u).toRingHom v (Polynomial.C Polynomial.X) = u
    simp
  have hφV : φ V = v := by
    change Polynomial.eval₂ (Polynomial.aeval u).toRingHom v Polynomial.X = v
    simp
  have hφd : φ d = (c : S) := by rw [show d = 1 + U * V by rfl, map_add, map_one, map_mul, hφU, hφV, hc]
  have hdunit : IsUnit (φ d) := hφd ▸ c.isUnit
  let g : L →ₐ[R] S := IsLocalization.Away.liftAlgHom d hdunit
  have hg (a : P) : g (l a) = φ a := IsLocalization.Away.lift_eq d hdunit a
  have hCg : Units.map g.toMonoidHom C = c := by
    apply Units.ext
    change g (C : L) = (c : S)
    rw [hC, hg, hφd]
  have e := congrArg (mapPoint (A := A) g) eg'
  rw [map_mul, map_mul, map_mul, evaluate_natural, evaluate_natural, evaluate_natural,
    evaluate_natural, htNat (S := Lc) (T := S), hCg, map_mul, map_mul, hg, hg, hφU, hφV] at e
  have hCi : g (↑C⁻¹ : L) = (↑c⁻¹ : S) :=
    congrArg (fun z : Sˣ => (↑z⁻¹ : S)) hCg
  rwa [hCi] at e

end GaussDescent

section Coefficients

variable {R A S : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
    [CommRing S] [Algebra R S]

private def dual (a b : S) : DualNumber S := (a, b)

@[simp] private theorem dual_fst (a b : S) : (dual a b).fst = a := rfl

@[simp] private theorem dual_snd (a b : S) : (dual a b).snd = b := rfl

/-- First order polynomial evaluation at a point of the affine line. -/
private def firstOrderEvaluation (a b : S) : Polynomial R →ₐ[R] DualNumber S where
  toFun p := dual (p.aeval a) (p.derivative.aeval a * b)
  map_one' := by
    apply TrivSqZeroExt.ext <;> simp
  map_zero' := by
    apply TrivSqZeroExt.ext <;> simp
  map_add' p q := by
    apply TrivSqZeroExt.ext
    · rw [TrivSqZeroExt.fst_add]
      exact map_add (Polynomial.aeval a : Polynomial R →ₐ[R] S) p q
    · rw [TrivSqZeroExt.snd_add]
      change (Polynomial.aeval a) ((p + q).derivative) * b =
        (Polynomial.aeval a) p.derivative * b + (Polynomial.aeval a) q.derivative * b
      rw [Polynomial.derivative_add, map_add, add_mul]
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · rw [TrivSqZeroExt.fst_mul]
      exact map_mul (Polynomial.aeval a : Polynomial R →ₐ[R] S) p q
    · rw [DualNumber.snd_mul]
      change (Polynomial.aeval a) ((p * q).derivative) * b =
        (Polynomial.aeval a) p * ((Polynomial.aeval a) q.derivative * b) +
        ((Polynomial.aeval a) p.derivative * b) * (Polynomial.aeval a) q
      rw [Polynomial.derivative_mul, map_add, map_mul, map_mul]
      ring
  commutes' r := by
    apply TrivSqZeroExt.ext
    · change (Polynomial.aeval a) (algebraMap R (Polynomial R) r) = algebraMap R S r
      exact AlgHom.commutes _ _
    · change (Polynomial.aeval a) ((Polynomial.C r).derivative) * b = 0
      simp

private theorem polynomialEval_dual (a b : S) :
    (Polynomial.aeval (dual a b) : Polynomial R →ₐ[R] DualNumber S) =
      firstOrderEvaluation a b := by
  apply Polynomial.algHom_ext
  rw [Polynomial.aeval_X]
  apply TrivSqZeroExt.ext <;> simp [firstOrderEvaluation]

private theorem polynomialEval_dual_snd (a b : S) (p : Polynomial R) :
    TrivSqZeroExt.snd (p.aeval (dual a b)) = p.derivative.aeval a * b := by
  exact DFunLike.congr_fun (polynomialEval_dual (R := R) a b) p |> congrArg TrivSqZeroExt.snd

private theorem polynomialEval_dual_fst (a b : S) (p : Polynomial R) :
    TrivSqZeroExt.fst (p.aeval (dual a b)) = p.aeval a := by
  exact DFunLike.congr_fun (polynomialEval_dual (R := R) a b) p |> congrArg TrivSqZeroExt.fst

/-- Nonvanishing in every geometric residue field detects units. -/
theorem isUnit_of_geometricNonzero (r : R)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K], algebraMap R K r ≠ 0) :
    IsUnit r := by
  by_contra hr
  obtain ⟨I, hI, hrI⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hr)
  letI := hI
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  let K := AlgebraicClosure (R ⧸ I)
  letI : Algebra R K := ((algebraMap (R ⧸ I) K).comp (Ideal.Quotient.mk I)).toAlgebra
  apply h K
  change algebraMap (R ⧸ I) K (Ideal.Quotient.mk I r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hrI, map_zero]

/-- A dilation of a chosen additive coordinate. -/
private def rescaleCoordinate (r : R) (x : A →ₐ[R] Polynomial R) : A →ₐ[R] Polynomial R :=
  (Polynomial.aeval (Polynomial.C r * Polynomial.X)).comp x

private theorem evaluate_rescale (r : R) (x : A →ₐ[R] Polynomial R) (a : S) :
    evaluate (rescaleCoordinate r x) a = evaluate x (algebraMap R S r * a) := by
  apply WithConv.ext
  have h : (Polynomial.aeval a : Polynomial R →ₐ[R] S).comp
      (Polynomial.aeval (Polynomial.C r * Polynomial.X)) =
      Polynomial.aeval (algebraMap R S r * a) := by
    ext
    simp
  exact congrArg (fun p : Polynomial R →ₐ[R] S => p.comp x) h

private theorem rescale_additive (r : R) {x : A →ₐ[R] Polynomial R} (hx : IsAdditive x) :
    IsAdditive (rescaleCoordinate r x) := by
  intro T
  refine ⟨by rw [evaluate_rescale, mul_zero]; exact (hx T).1, fun a b => ?_⟩
  simp only [evaluate_rescale, mul_add]
  exact (hx T).2 _ _

private theorem rescale_surjective (r : Rˣ) {x : A →ₐ[R] Polynomial R} (hx : Function.Surjective x) :
    Function.Surjective (rescaleCoordinate (r : R) x) := by
  have h :
      (Polynomial.aeval (Polynomial.C (r : R) * Polynomial.X) : Polynomial R →ₐ[R] Polynomial R).comp
        (Polynomial.aeval (Polynomial.C (↑r⁻¹ : R) * Polynomial.X)) = AlgHom.id R (Polynomial R) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, AlgHom.id_apply, Polynomial.aeval_X, map_mul, Polynomial.aeval_C]
    change Polynomial.C (↑r⁻¹ : R) * (Polynomial.C (r : R) * Polynomial.X) = Polynomial.X
    rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  intro v
  obtain ⟨a, ha⟩ := hx ((Polynomial.aeval (Polynomial.C (↑r⁻¹ : R) * Polynomial.X)) v)
  refine ⟨a, ?_⟩
  change (Polynomial.aeval (Polynomial.C (r : R) * Polynomial.X) : Polynomial R →ₐ[R] Polynomial R)
    (x a) = v
  rw [ha]
  exact DFunLike.congr_fun h v

private theorem conv_apply_repr {S : Type u} [CommRing S] [Algebra R S]
    {a : A} {ι : Type u} (repr : Coalgebra.Repr R a ι) (p q : HopfPoints R A S) :
    (p * q).ofConv a = ∑ j ∈ repr.index, p.ofConv (repr.left j) * q.ofConv (repr.right j) := by
  change (p * q) a = _
  rw [AlgHom.convMul_apply, ← repr.eq, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

private theorem coefficient_succ (x : A →ₐ[R] Polynomial R) (hx : IsAdditive x)
    (a : A) (n : ℕ) {ι : Type u} (repr : Coalgebra.Repr R a ι) :
    (x a).coeff (n + 1) * (n + 1 : R) =
      ∑ j ∈ repr.index, (x (repr.left j)).coeff n * (x (repr.right j)).coeff 1 := by
  let P := Polynomial R
  let U : DualNumber P := dual Polynomial.X 0
  let V : DualNumber P := dual 0 1
  have h := (hx (CommAlgCat.of R (DualNumber P))).2 U V
  have hs := congrArg (fun g : HopfPoints R A (DualNumber P) => (g.ofConv a).snd) h
  rw [conv_apply_repr repr] at hs
  have duv : U + V = dual (Polynomial.X : P) 1 := by
    apply TrivSqZeroExt.ext <;> simp [U, V, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add]
  have hcoeff (p : Polynomial R) : (Polynomial.aeval (0 : P)) p.derivative = Polynomial.C (p.coeff 1) := by
    rw [← Polynomial.coeff_zero_eq_aeval_zero', Polynomial.coeff_derivative]
    simp [P, Polynomial.algebraMap_eq]
  have hs' :
      (x a).derivative =
        ∑ j ∈ repr.index, x (repr.left j) * Polynomial.C ((x (repr.right j)).coeff 1) := by
    change TrivSqZeroExt.snd (Polynomial.aeval (U + V) (x a)) =
      TrivSqZeroExt.snd (∑ j ∈ repr.index,
        (Polynomial.aeval U (x (repr.left j))) * (Polynomial.aeval V (x (repr.right j)))) at hs
    rw [duv, polynomialEval_dual_snd, Polynomial.aeval_X_left_apply, mul_one] at hs
    rw [hs]
    change (TrivSqZeroExt.sndHom (R := P) (M := P)) _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    change TrivSqZeroExt.snd
      (Polynomial.aeval U (x (repr.left j)) * Polynomial.aeval V (x (repr.right j))) = _
    simp only [U, V, DualNumber.snd_mul, polynomialEval_dual_snd, polynomialEval_dual_fst,
      hcoeff, mul_zero, zero_mul, add_zero, mul_one]
    change Polynomial.aeval (Polynomial.X : Polynomial R) (x (repr.left j)) * _ = _
    rw [Polynomial.aeval_X_left_apply]
  have h := congrArg (fun p : Polynomial R => p.coeff n) hs'
  simpa only [Polynomial.coeff_derivative, Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C,
    Nat.cast_add, Nat.cast_one] using h

/-- In characteristic zero the differential determines a homomorphism from
the additive group to an affine group. Evaluate the group law in dual numbers
over the polynomial ring to obtain the recursion for every coefficient. -/
theorem additiveCoordinates_eq_of_tangent [IsDomain R] [CharZero R]
    {x y : A →ₐ[R] Polynomial R} (hx : IsAdditive x) (hy : IsAdditive y)
    (h : evaluate x (DualNumber.eps : DualNumber R) = evaluate y (DualNumber.eps : DualNumber R)) :
    x = y := by
  have hfirst (a : A) : (x a).coeff 1 = (y a).coeff 1 := by
    have e := congrArg (fun v : HopfPoints R A (DualNumber R) => (v.ofConv a).snd) h
    change TrivSqZeroExt.snd (Polynomial.aeval (dual (0 : R) 1) (x a)) =
      TrivSqZeroExt.snd (Polynomial.aeval (dual (0 : R) 1) (y a)) at e
    simpa only [polynomialEval_dual_snd, mul_one, ← Polynomial.coeff_zero_eq_aeval_zero,
      Polynomial.coeff_derivative, zero_add, Nat.cast_zero, Nat.cast_one, mul_one] using e
  apply AlgHom.ext
  intro a
  apply Polynomial.ext
  intro n
  induction n generalizing a with
  | zero =>
    have hzero := (hx (CommAlgCat.of R R)).1.trans (hy (CommAlgCat.of R R)).1.symm
    exact (Polynomial.coeff_zero_eq_aeval_zero (x a)).trans
      ((congrArg (fun v : HopfPoints R A R => v.ofConv a) hzero).trans
        (Polynomial.coeff_zero_eq_aeval_zero (y a)).symm)
  | succ n ih =>
    have hn : (n + 1 : R) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    apply mul_right_cancel₀ hn
    let repr := Coalgebra.Repr.arbitrary R a
    rw [coefficient_succ x hx a n repr, coefficient_succ y hy a n repr]
    exact Finset.sum_congr rfl (fun j _ => by rw [ih, hfirst])

private theorem evaluate_tangent_snd (x : A →ₐ[R] Polynomial R) (b : S) (a : A) :
    ((evaluate x (dual 0 b)).ofConv a).snd = algebraMap R S ((x a).coeff 1) * b := by
  change TrivSqZeroExt.snd (Polynomial.aeval (dual (0 : S) b) (x a)) = _
  simp only [polynomialEval_dual_snd, ← Polynomial.coeff_zero_eq_aeval_zero',
    Polynomial.coeff_derivative, zero_add, Nat.cast_zero, Nat.cast_one, mul_one]

private theorem tangent_reduces (x : A →ₐ[R] Polynomial R) (hx : IsAdditive x) (b : S) :
    mapPoint (TrivSqZeroExt.fstHom R S S) (evaluate x (dual 0 b)) = 1 := by
  rw [evaluate_natural]
  exact (hx (CommAlgCat.of R S)).1

/-- Multiplication of two dual-number lifts of the identity adds the tangent coefficients. -/
private theorem tangentProduct_snd (p q : HopfPoints R A (DualNumber S))
    (hp : mapPoint (TrivSqZeroExt.fstHom R S S) p = 1)
    (hq : mapPoint (TrivSqZeroExt.fstHom R S S) q = 1) (a : A) :
    ((p * q).ofConv a).snd = (p.ofConv a).snd + (q.ofConv a).snd := by
  let repr := Coalgebra.Repr.arbitrary R a
  let d := (TrivSqZeroExt.sndHom (R := S) (M := S)).restrictScalars R
  let dp := d.comp p.ofConv.toLinearMap
  let dq := d.comp q.ofConv.toLinearMap
  have hl : ∑ j ∈ repr.index, Bialgebra.counitAlgHom R A (repr.left j) • repr.right j = a :=
    Coalgebra.sum_counit_smul repr
  have hr : ∑ j ∈ repr.index, Bialgebra.counitAlgHom R A (repr.right j) • repr.left j = a := by
    have h := congrArg (TensorProduct.rid R A) (Coalgebra.sum_tmul_counit_eq repr)
    simpa only [map_sum, TensorProduct.rid_tmul, one_smul, Bialgebra.counitAlgHom_apply] using h
  have hp' (a : A) : (p.ofConv a).fst = algebraMap R S (Bialgebra.counitAlgHom R A a) :=
    congrArg (fun g : HopfPoints R A S => g.ofConv a) hp
  have hq' (a : A) : (q.ofConv a).fst = algebraMap R S (Bialgebra.counitAlgHom R A a) :=
    congrArg (fun g : HopfPoints R A S => g.ofConv a) hq
  have el := congrArg dq hl
  have er := congrArg dp hr
  simp only [map_sum, map_smul] at el er
  rw [conv_apply_repr repr]
  change d (∑ j ∈ repr.index, p.ofConv (repr.left j) * q.ofConv (repr.right j)) = dp a + dq a
  rw [map_sum, ← el, ← er, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change (p.ofConv (repr.left j) * q.ofConv (repr.right j)).snd = _
  rw [DualNumber.snd_mul, hp', hq']
  simp only [dp, dq, d, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    TrivSqZeroExt.sndHom_apply, AlgHom.toLinearMap_apply, Algebra.smul_def]
  ring

/-- Change the scalar ring of dual numbers and multiply the infinitesimal coordinate. -/
private def mapDual {T : Type u} [CommRing T] [Algebra R T] (g : S →ₐ[R] T) (b : T) :
    DualNumber S →ₐ[R] DualNumber T where
  toFun p := dual (g p.fst) (g p.snd * b)
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_add' p q := by
    apply TrivSqZeroExt.ext <;>
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, dual_fst, dual_snd, map_add, add_mul]
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_mul, dual_fst, map_mul]
    · simp only [DualNumber.snd_mul, dual_fst, dual_snd, map_add, map_mul]
      ring
  commutes' r := by
    apply TrivSqZeroExt.ext
    · change g (algebraMap R S r) = algebraMap R T r
      exact g.commutes r
    · change g 0 * b = 0
      rw [map_zero, zero_mul]

private def tangentUnit (c : S) : (DualNumber S)ˣ where
  val := dual 1 c
  inv := dual 1 (-c)
  val_inv := by
    apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.fst_mul, DualNumber.snd_mul]
  inv_val := by
    apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.fst_mul, DualNumber.snd_mul]

private theorem map_tangentUnit {T : Type u} [CommRing T] [Algebra R T]
    (g : S →ₐ[R] T) (b : T) (c : S) :
    Units.map (mapDual g b).toMonoidHom (tangentUnit c) = tangentUnit (g c * b) := by
  apply Units.ext
  change dual (g 1) (g c * b) = dual 1 (g c * b)
  rw [map_one]

/-- The quadratic adjoint coefficient, evaluated on one function of the affine group. -/
private def adjointQuadratic (x y : A →ₐ[R] Polynomial R) (c : R) (a : A) : R :=
  let U : DualNumber (Polynomial R) := dual Polynomial.X 0
  let V : DualNumber (Polynomial R) := dual 0 (Polynomial.C c)
  (((evaluate x U * evaluate y V * (evaluate x U)⁻¹).ofConv a).snd).coeff 2

set_option maxHeartbeats 700000 in
/-- Substituting an infinitesimal negative parameter in the Gauss formula
computes the quadratic coefficient without division by two. -/
private theorem adjointQuadratic_of_linked [IsDomain R]
    (x y : A →ₐ[R] Polynomial R) (hx : IsAdditive x) (hy : IsAdditive y)
    (t : (S : CommAlgCat.{u} R) → Sˣ →* HopfPoints R A S)
    (htNat : ∀ {S T : CommAlgCat.{u} R} (g : S →ₐ[R] T) (a : Sˣ),
      mapPoint g (t S a) = t T (Units.map g.toMonoidHom a))
    (ht : ∀ (S : CommAlgCat.{u} R) (a : Sˣ), rankOneWord x y a = t S a * rankOneWord x y 1)
    (hp : ∀ (S : CommAlgCat.{u} R) (a : Sˣ) (b : S),
      t S a * evaluate x b * (t S a)⁻¹ = evaluate x ((a : S)^2 * b))
    (hm : ∀ (S : CommAlgCat.{u} R) (a : Sˣ) (b : S),
      t S a * evaluate y b * (t S a)⁻¹ = evaluate y ((↑a⁻¹ : S)^2 * b))
    (c : R) (a : A) :
    adjointQuadratic x y c a = -c * (x a).coeff 1 := by
  let P := Polynomial R
  let S := CommAlgCat.of R (DualNumber P)
  let U : DualNumber P := dual Polynomial.X 0
  let V : DualNumber P := dual 0 (Polynomial.C c)
  let C := tangentUnit ((Polynomial.X : P) * Polynomial.C c)
  have hC : (C : DualNumber P) = 1 + U * V := by
    apply TrivSqZeroExt.ext <;> simp [C, tangentUnit, U, V,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_mul, DualNumber.snd_mul]
  have hV : V * (↑C⁻¹ : DualNumber P) = V := by
    apply TrivSqZeroExt.ext <;> simp [C, tangentUnit, V, TrivSqZeroExt.fst_mul, DualNumber.snd_mul]
  have hU : U * (↑C⁻¹ : DualNumber P) + -U =
      dual (0 : P) (-((Polynomial.X : P)^2) * Polynomial.C c) := by
    apply TrivSqZeroExt.ext
    · simp [C, tangentUnit, U, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_neg]
      exact add_neg_cancel _
    · simp [C, tangentUnit, U, TrivSqZeroExt.snd_add, DualNumber.snd_mul, TrivSqZeroExt.snd_neg]
      ring
  have e := gauss x y hx hy t (fun g a => htNat g a) ht hp hm S U V C hC
  have hInv : (evaluate x U)⁻¹ = evaluate x (-U) :=
    ((additiveHom (S := DualNumber P) hx).map_inv (Multiplicative.ofAdd U)).symm
  have e' :
      evaluate x U * evaluate y V * (evaluate x U)⁻¹ =
        evaluate y V * t S C * evaluate x (dual (0 : P) (-((Polynomial.X : P)^2) * Polynomial.C c)) := by
    rw [e, hV, hInv, mul_assoc _ (evaluate x _) (evaluate x _), ← (hx S).2, hU]
  let f := TrivSqZeroExt.fstHom R P P
  have hT : mapPoint f (t S C) = 1 := by
    have h := htNat (S := S) (T := CommAlgCat.of R P) f C
    have e : Units.map f.toMonoidHom C = 1 := by
      apply Units.ext
      rfl
    rw [h, e, map_one]
  let L := CommAlgCat.of R (DualNumber R)
  let g := mapDual (Algebra.ofId R P) ((Polynomial.X : P) * Polynomial.C c)
  have hbase : ∃ d : R, ((t S C).ofConv a).snd = Polynomial.C d *
      (Polynomial.X * Polynomial.C c) := by
    have h := htNat (S := L) (T := S) g (tangentUnit (1 : R))
    have hg : Units.map g.toMonoidHom (tangentUnit (1 : R)) = C := by
      simp only [g, map_tangentUnit, map_one, one_mul, C]
    rw [hg] at h
    refine ⟨((t L (tangentUnit (1 : R))).ofConv a).snd, ?_⟩
    rw [← h]
    rfl
  obtain ⟨d, hd⟩ := hbase
  have hNeg := tangent_reduces y hy (Polynomial.C c : P)
  have hPos := tangent_reduces x hx (-((Polynomial.X : P)^2) * Polynomial.C c)
  have hLeft : mapPoint f (evaluate y V * t S C) = 1 := by
    rw [map_mul, hNeg, hT, one_mul]
  change (((evaluate x U * evaluate y V * (evaluate x U)⁻¹).ofConv a).snd).coeff 2 = _
  rw [e', tangentProduct_snd _ _ hLeft hPos, tangentProduct_snd _ _ hNeg hT, hd]
  rw [evaluate_tangent_snd, evaluate_tangent_snd]
  change (Polynomial.C ((y a).coeff 1) * Polynomial.C c + Polynomial.C d *
    (Polynomial.X * Polynomial.C c) + Polynomial.C ((x a).coeff 1) *
      (-((Polynomial.X : P)^2) * Polynomial.C c)).coeff 2 = _
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C,
    Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_neg, Polynomial.coeff_X_pow_self,
    OfNat.ofNat_ne_zero, show (1 : ℕ) ≠ 2 by decide, ite_false, zero_mul, zero_add]
  ring

private theorem adjointQuadratic_rescale (x y : A →ₐ[R] Polynomial R) (r c : R) (a : A) :
    adjointQuadratic x (rescaleCoordinate r y) c a = adjointQuadratic x y (r * c) a := by
  simp only [adjointQuadratic, evaluate_rescale]
  have e : algebraMap R (DualNumber (Polynomial R)) r * dual 0 (Polynomial.C c) =
      dual 0 (Polynomial.C (r * c)) := by
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_mul, dual_fst, mul_zero]
    · rw [DualNumber.snd_mul, dual_fst, dual_snd, mul_zero, add_zero, map_mul]
      rfl
  rw [e]

end Coefficients

section BaseChange

variable {R K A S : Type u} [CommRing R] [Field K] [CommRing A] [HopfAlgebra R A]
  [Algebra R K] [CommRing S] [Algebra R S] [Algebra K S] [IsScalarTower R K S]

/-- Restrict points of a scalar extension to the original Hopf algebra. -/
private def restrictPoint : HopfPoints K (K ⊗[R] A) S →* HopfPoints R A S where
  toFun p := toConv ((AlgHom.liftEquiv R K A S).symm p.ofConv)
  map_one' := by
    apply WithConv.ext
    ext a
    change algebraMap K S (Bialgebra.counitAlgHom K (K ⊗[R] A) ((1 : K) ⊗ₜ[R] a)) = _
    have e := DFunLike.congr_fun
      (Bialgebra.counitAlgHom_comp_includeRight (R := R) (A := K) (B := A)) a
    change Bialgebra.counitAlgHom K (K ⊗[R] A) ((1 : K) ⊗ₜ[R] a) =
      algebraMap R K (Bialgebra.counitAlgHom R A a) at e
    rw [e, ← IsScalarTower.algebraMap_apply R K S]
    rfl
  map_mul' p q := by
    apply WithConv.ext
    ext a
    change (p * q).ofConv ((1 : K) ⊗ₜ[R] a) =
      (toConv ((AlgHom.liftEquiv R K A S).symm p.ofConv) *
        toConv ((AlgHom.liftEquiv R K A S).symm q.ofConv)).ofConv a
    let repr := Coalgebra.Repr.arbitrary R a
    let incl : A →ₐ[R] K ⊗[R] A := Algebra.TensorProduct.includeRight
    let f := Algebra.TensorProduct.mapRingHom (algebraMap R K) incl.toRingHom incl.toRingHom
      (by simp [incl, ← IsScalarTower.algebraMap_eq])
      (by simp [incl, ← IsScalarTower.algebraMap_eq])
    have e := DFunLike.congr_fun (Bialgebra.comul_includeRight (R := R) (A := K) (B := A)) a
    change Coalgebra.comul ((1 : K) ⊗ₜ[R] a) = f (Coalgebra.comul (R := R) a) at e
    let repK : Coalgebra.Repr K ((1 : K) ⊗ₜ[R] a) (A × A) :=
      { index := repr.index
        left := fun j => incl (repr.left j)
        right := fun j => incl (repr.right j)
        eq := by
          rw [e, ← repr.eq, map_sum]
          exact Finset.sum_congr rfl (fun j _ => by simp [f]) }
    rw [conv_apply_repr repK, conv_apply_repr repr]
    rfl

private theorem restrict_evaluate (x : A →ₐ[R] Polynomial R) (a : S) :
    restrictPoint (R := R) (K := K) (evaluate (extendRoot (K := K) x) a) = evaluate x a := by
  apply WithConv.ext
  ext b
  change (Polynomial.aeval a : Polynomial K →ₐ[K] S)
    ((extendRoot (K := K) x) ((1 : K) ⊗ₜ[R] b)) = (Polynomial.aeval a : Polynomial R →ₐ[R] S) (x b)
  rw [show (extendRoot (K := K) x) ((1 : K) ⊗ₜ[R] b) = (x b).map (algebraMap R K) by
    simp [extendRoot]]
  exact (Polynomial.aeval_eq_aeval_map (φ := algebraMap R K) (by
    ext r
    exact (IsScalarTower.algebraMap_apply R K S r).symm) (x b) a).symm

/-- Additivity is preserved by base change of the polynomial coordinate. -/
private theorem extendRoot_additive {x : A →ₐ[R] Polynomial R} (hx : IsAdditive x) :
    IsAdditive (extendRoot (K := K) x) := by
  intro T
  letI : Algebra R T := ((algebraMap K T).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K T := IsScalarTower.of_algebraMap_eq' rfl
  let U := CommAlgCat.of R T
  have hinj : Function.Injective (restrictPoint (R := R) (K := K) (A := A) (S := T)) :=
    fun p q e => WithConv.ext ((AlgHom.liftEquiv R K A T).symm.injective
      (congrArg WithConv.ofConv e))
  refine ⟨hinj ?_, fun a b => hinj ?_⟩
  · rw [restrict_evaluate, map_one]
    exact (hx U).1
  · rw [map_mul, restrict_evaluate, restrict_evaluate, restrict_evaluate]
    exact (hx U).2 a b

set_option maxHeartbeats 700000 in
/-- The quadratic adjoint coefficient reduces by applying the base-ring map. -/
private theorem adjointQuadratic_extend (x y : A →ₐ[R] Polynomial R) (c : R) (a : A) :
    algebraMap R K (adjointQuadratic x y c a) =
      adjointQuadratic (extendRoot (K := K) x) (extendRoot (K := K) y) (algebraMap R K c) (1 ⊗ₜ[R] a) := by
  let f := Polynomial.mapAlgHom (Algebra.ofId R K)
  let g := mapDual f 1
  let e := restrictPoint (R := R) (K := K) (A := A) (S := DualNumber (Polynomial K))
  let U : DualNumber (Polynomial R) := dual Polynomial.X 0
  let V : DualNumber (Polynomial R) := dual 0 (Polynomial.C c)
  let U' : DualNumber (Polynomial K) := dual Polynomial.X 0
  let V' : DualNumber (Polynomial K) := dual 0 (Polynomial.C (algebraMap R K c))
  have hU : g U = U' := by
    apply TrivSqZeroExt.ext <;> simp [g, mapDual, U, U', f]
  have hV : g V = V' := by
    apply TrivSqZeroExt.ext <;> simp [g, mapDual, V, V', f]
  have eq :
      mapPoint g (evaluate x U * evaluate y V * (evaluate x U)⁻¹) =
        e (evaluate (extendRoot (K := K) x) U' * evaluate (extendRoot (K := K) y) V' *
          (evaluate (extendRoot (K := K) x) U')⁻¹) := by
    change mapPoint g _ = restrictPoint (R := R) _
    simp only [map_mul, map_inv, evaluate_natural, restrict_evaluate, hU, hV]
  have h := congrArg (fun p : HopfPoints R A (DualNumber (Polynomial K)) => (p.ofConv a).snd.coeff 2) eq
  change (f _ * 1).coeff 2 = _ at h
  rw [mul_one, Polynomial.coeff_mapAlgHom_apply] at h
  exact h

end BaseChange

section TorusWords

open _root_.LinearAlgebraicGroups.Specs.IntegralCentralQuotient (cocharacterEval RootScalarAction)

variable {R A X : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommGroup X]

private theorem conv_monomial {S : Type u} [CommRing S] [Algebra R S]
    (p q : HopfPoints R (MonoidAlgebra R X) S) (χ : X) :
    (p * q).ofConv (MonoidAlgebra.of R X χ) =
      p.ofConv (MonoidAlgebra.of R X χ) * q.ofConv (MonoidAlgebra.of R X χ) := by
  change (p * q) (MonoidAlgebra.of R X χ) = _
  rw [AlgHom.convMul_apply]
  simp only [MonoidAlgebra.of_apply]
  rw [(MonoidAlgebra.isGroupLikeElem_single_one (R := R) (A := R) χ).comul_eq_tmul_self]
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

private theorem torusPoint_ext {S : Type u} [CommRing S] [Algebra R S]
    {p q : HopfPoints R (MonoidAlgebra R X) S}
    (h : ∀ χ, p.ofConv (MonoidAlgebra.of R X χ) = q.ofConv (MonoidAlgebra.of R X χ)) :
    p = q := by
  apply WithConv.ext
  apply MonoidAlgebra.algHom_ext h
  exact Subsingleton.elim _ _

private theorem cocharacterEval_monomial (ν : X →* Multiplicative ℤ)
    (S : CommAlgCat.{u} R) (a : Sˣ) (χ : X) :
    cocharacterEval ν S a (MonoidAlgebra.of R X χ) = (↑(a ^ (ν χ).toAdd) : S) := by
  simp only [cocharacterEval, MonoidAlgebra.lift_of]
  rfl

private def cocharacterPoint (t : A →ₐc[R] MonoidAlgebra R X) (ν : X →* Multiplicative ℤ)
    (S : CommAlgCat.{u} R) : Sˣ →* HopfPoints R A S :=
  (mapGroup t).comp
    { toFun a := toConv (cocharacterEval ν S a)
      map_one' := by
        apply torusPoint_ext
        intro χ
        rw [show (toConv (cocharacterEval ν S 1)).ofConv _ =
          cocharacterEval ν S 1 (MonoidAlgebra.of R X χ) by rfl]
        rw [cocharacterEval_monomial, one_zpow]
        change (1 : S) = algebraMap R S (Bialgebra.counitAlgHom R _ (MonoidAlgebra.of R X χ))
        rw [show Bialgebra.counitAlgHom R _ (MonoidAlgebra.of R X χ) = 1 from
          (MonoidAlgebra.isGroupLikeElem_single_one (R := R) (A := R) χ).counit_eq_one, map_one]
      map_mul' a b := by
        apply torusPoint_ext
        intro χ
        rw [conv_monomial]
        change cocharacterEval ν S (a * b) _ = cocharacterEval ν S a _ * cocharacterEval ν S b _
        simp only [cocharacterEval_monomial, mul_zpow, Units.val_mul] }

private theorem cocharacterPoint_natural (t : A →ₐc[R] MonoidAlgebra R X)
    (ν : X →* Multiplicative ℤ)
    {S T : CommAlgCat.{u} R} (g : S →ₐ[R] T) (a : Sˣ) :
    mapPoint g (cocharacterPoint t ν S a) = cocharacterPoint t ν T (Units.map g.toMonoidHom a) := by
  have e :
      mapPoint g (toConv (cocharacterEval ν S a)) = toConv (cocharacterEval ν T (Units.map g.toMonoidHom a)) := by
    apply torusPoint_ext
    intro χ
    change g (cocharacterEval ν S a (MonoidAlgebra.of R X χ)) =
      cocharacterEval ν T (Units.map g.toMonoidHom a) (MonoidAlgebra.of R X χ)
    rw [cocharacterEval_monomial, cocharacterEval_monomial, ← map_zpow]
    rfl
  exact congrArg (mapGroup (S := T) t) e

private theorem linkedWord {D : BasedRootDatum.{u}} (t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X))
    (i : D.I) {x y : A →ₐ[R] Polynomial R} (h : IsLinked t i x y)
    (S : CommAlgCat.{u} R) (a : Sˣ) :
    rankOneWord x y a = cocharacterPoint t (coroot i) S a * rankOneWord x y (1 : Sˣ) := by
  exact mul_inv_eq_iff_eq_mul.mp (h S a)

private theorem corootPositiveWeight {D : BasedRootDatum.{u}} (i : D.I) :
    (coroot i (Multiplicative.ofAdd (D.datum.root i))).toAdd = 2 := by
  change D.datum.toLinearMap (D.datum.root i) (D.datum.coroot i) = 2
  simp

private theorem corootNegativeWeight {D : BasedRootDatum.{u}} (i : D.I) :
    (coroot i (Multiplicative.ofAdd (D.datum.root (D.datum.reflectionPerm i i)))).toAdd = -2 := by
  change D.datum.toLinearMap (D.datum.root (D.datum.reflectionPerm i i)) (D.datum.coroot i) = -2
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, map_neg, LinearMap.neg_apply,
    RootPairing.root_coroot_eq_pairing, RootPairing.pairing_same]

private theorem linkedPositiveScalar {D : BasedRootDatum.{u}}
    (t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X))
    (i : D.I) {x : A →ₐ[R] Polynomial R}
    (hx : RootScalarAction t x (Multiplicative.ofAdd (D.datum.root i)))
    (S : CommAlgCat.{u} R) (a : Sˣ) (b : S) :
    cocharacterPoint t (coroot i) S a * evaluate x b *
      (cocharacterPoint t (coroot i) S a)⁻¹ = evaluate x ((a : S)^2 * b) := by
  have h := hx S b (cocharacterEval (coroot i) S a)
  change cocharacterPoint t (coroot i) S a * evaluate x b *
    (cocharacterPoint t (coroot i) S a)⁻¹ =
    evaluate x (cocharacterEval (coroot i) S a (MonoidAlgebra.of R _
      (Multiplicative.ofAdd (D.datum.root i))) * b) at h
  rw [cocharacterEval_monomial, corootPositiveWeight] at h
  simpa only [zpow_ofNat, Units.val_pow_eq_pow_val] using h

private theorem linkedNegativeScalar {D : BasedRootDatum.{u}}
    (t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X))
    (i : D.I) {y : A →ₐ[R] Polynomial R}
    (hy : RootScalarAction t y (Multiplicative.ofAdd (D.datum.root (D.datum.reflectionPerm i i))))
    (S : CommAlgCat.{u} R) (a : Sˣ) (b : S) :
    cocharacterPoint t (coroot i) S a * evaluate y b *
      (cocharacterPoint t (coroot i) S a)⁻¹ = evaluate y ((↑a⁻¹ : S)^2 * b) := by
  have h := hy S b (cocharacterEval (coroot i) S a)
  change cocharacterPoint t (coroot i) S a * evaluate y b *
    (cocharacterPoint t (coroot i) S a)⁻¹ =
    evaluate y (cocharacterEval (coroot i) S a (MonoidAlgebra.of R _
      (Multiplicative.ofAdd (D.datum.root (D.datum.reflectionPerm i i)))) * b) at h
  rw [cocharacterEval_monomial, corootNegativeWeight] at h
  simpa only [zpow_neg, zpow_ofNat, ← inv_pow, Units.val_pow_eq_pow_val] using h

variable {D : BasedRootDatum.{u}}

/-- The rank-one representative acts on the marked torus by the simple reflection formula. -/
theorem linkedWord_conjugatesTorus
    (t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X)) (i : D.I)
    {x y : A →ₐ[R] Polynomial R} (h : IsLinked t i x y)
    (hx : RootScalarAction t x (Multiplicative.ofAdd (D.datum.root i)))
    (hy : RootScalarAction t y (Multiplicative.ofAdd (D.datum.root (D.datum.reflectionPerm i i))))
    (S : CommAlgCat.{u} R) (s : MonoidAlgebra R (Multiplicative D.X) →ₐ[R] S) :
    let χ := Multiplicative.ofAdd (D.datum.root i)
    let a := (s.toMonoidHom.comp (MonoidAlgebra.of R _)).toHomUnits χ
    let g := toConv (s.comp t.toAlgHom)
    let w := rankOneWord x y (1 : Sˣ)
    w * g * w⁻¹ = (cocharacterPoint t (coroot i) S a)⁻¹ * g := by
  dsimp only
  let χ := Multiplicative.ofAdd (D.datum.root i)
  let a := (s.toMonoidHom.comp (MonoidAlgebra.of R _)).toHomUnits χ
  let g := toConv (s.comp t.toAlgHom)
  let w := rankOneWord x y (1 : Sˣ)
  change w * g * w⁻¹ = (cocharacterPoint t (coroot i) S a)⁻¹ * g
  have hχ : Multiplicative.ofAdd (D.datum.root (D.datum.reflectionPerm i i)) = χ⁻¹ := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
    rfl
  have hxp : g * evaluate x (1 : S) * g⁻¹ = evaluate x (a : S) := by
    have e := hx S 1 s
    change g * evaluate x (1 : S) * g⁻¹ = evaluate x ((a : S) * 1) at e
    rwa [mul_one] at e
  have hxm : g * evaluate y (-1 : S) * g⁻¹ = evaluate y (-(↑a⁻¹ : S)) := by
    have e := hy S (-1) s
    rw [hχ] at e
    change g * evaluate y (-1 : S) * g⁻¹ =
      evaluate y (((s.toMonoidHom.comp (MonoidAlgebra.of R _)).toHomUnits χ⁻¹ : Sˣ).val * (-1)) at e
    simpa only [map_inv, mul_neg, mul_one] using e
  have hw : g * w * g⁻¹ = cocharacterPoint t (coroot i) S a * w := calc
    _ = (g * evaluate x (1 : S) * g⁻¹) * (g * evaluate y (-1 : S) * g⁻¹) *
        (g * evaluate x (1 : S) * g⁻¹) := by
          simp only [w, rankOneWord, Units.val_one, inv_one]
          group
    _ = rankOneWord x y a := by rw [hxp, hxm]; rfl
    _ = _ := linkedWord t i h S a
  calc
    w * g * w⁻¹ = (cocharacterPoint t (coroot i) S a)⁻¹ * (g * w * g⁻¹) * g * w⁻¹ := by rw [hw]; group
    _ = _ := by group

/-- Read the relative negative scale as the image of a single integral coefficient. -/
private theorem integral_opposite_scale {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
    (x y : A →ₐ[R] Polynomial R) (a : A) (ha : x a = Polynomial.X)
    (hF : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
      ∃ (z : (K ⊗[R] A) →ₐ[K] Polynomial K) (b : Kˣ),
        extendRoot (K := K) y = rescaleCoordinate (b : K) z ∧
        adjointQuadratic (extendRoot (K := K) x) z (b : K) ((1 : K) ⊗ₜ[R] a) =
          -(b : K) * ((extendRoot (K := K) x) ((1 : K) ⊗ₜ[R] a)).coeff 1) :
    ∃ r : Rˣ, ∀ (K : Type u) [Field K] [Algebra R K]
      (z : (K ⊗[R] A) →ₐ[K] Polynomial K) (b : K),
      extendRoot (K := K) y = rescaleCoordinate b z →
      adjointQuadratic (extendRoot (K := K) x) z b ((1 : K) ⊗ₜ[R] a) =
        -b * ((extendRoot (K := K) x) ((1 : K) ⊗ₜ[R] a)).coeff 1 →
      algebraMap R K (r : R) = b := by
  let r := -(adjointQuadratic x y 1 a)
  have comparison (K : Type u) [Field K] [Algebra R K]
      (z : (K ⊗[R] A) →ₐ[K] Polynomial K) (b : K)
      (h : extendRoot (K := K) y = rescaleCoordinate b z)
      (hb : adjointQuadratic (extendRoot (K := K) x) z b ((1 : K) ⊗ₜ[R] a) =
        -b * ((extendRoot (K := K) x) ((1 : K) ⊗ₜ[R] a)).coeff 1) :
      algebraMap R K r = b := by
    dsimp only [r]
    rw [map_neg, adjointQuadratic_extend, map_one, h, adjointQuadratic_rescale, mul_one, hb]
    simp [extendRoot, ha]
  have unit_r : IsUnit r := by
    apply isUnit_of_geometricNonzero
    intro K _ _ _
    obtain ⟨z, b, h, hb⟩ := hF K
    rw [comparison K z (b : K) h hb]
    exact Units.ne_zero b
  obtain ⟨r', hr'⟩ := unit_r
  refine ⟨r', fun K _ _ z b h hb => ?_⟩
  rw [hr']
  exact comparison K z b h hb

end TorusWords

section Conjugation

variable {R A S : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing S] [Algebra R S]

/-- The pullback of conjugation by a rational point, constructed on the universal point. -/
private def conjugationPullback (g : HopfPoints R A R) : A →ₐ[R] A :=
  let a := mapPoint (Algebra.ofId R A) g
  (a * toConv (AlgHom.id R A) * a⁻¹).ofConv

private theorem mapPoint_comp_one (f : A →ₐ[R] S) (g : HopfPoints R A R) :
    mapPoint f (mapPoint (Algebra.ofId R A) g) = mapPoint (Algebra.ofId R S) g := by
  apply WithConv.ext
  ext a
  exact f.commutes _

private theorem conjugationPullback_point (g : HopfPoints R A R) (f : A →ₐ[R] S) :
    toConv (f.comp (conjugationPullback g)) =
      mapPoint (Algebra.ofId R S) g * toConv f * (mapPoint (Algebra.ofId R S) g)⁻¹ := by
  change mapPoint f (mapPoint (Algebra.ofId R A) g * toConv (AlgHom.id R A) *
    (mapPoint (Algebra.ofId R A) g)⁻¹) = _
  rw [map_mul, map_mul, map_inv, mapPoint_comp_one]
  rfl

private theorem conjugationPullback_surjective (g : HopfPoints R A R) :
    Function.Surjective (conjugationPullback g) := by
  intro a
  refine ⟨conjugationPullback g⁻¹ a, ?_⟩
  have h := conjugationPullback_point g⁻¹ (conjugationPullback g)
  have e := conjugationPullback_point g (AlgHom.id R A)
  change toConv (conjugationPullback g) = _ at e
  rw [e, map_inv, inv_inv] at h
  have eq : toConv ((conjugationPullback g).comp (conjugationPullback g⁻¹)) =
    toConv (AlgHom.id R A) := h.trans (by group)
  exact congrArg (fun p : HopfPoints R A A => p.ofConv a) eq

private def conjugateCoordinate (g : HopfPoints R A R) (x : A →ₐ[R] Polynomial R) :
    A →ₐ[R] Polynomial R := x.comp (conjugationPullback g)

private theorem evaluate_conjugate (g : HopfPoints R A R) (x : A →ₐ[R] Polynomial R) (b : S) :
    evaluate (conjugateCoordinate g x) b =
      mapPoint (Algebra.ofId R S) g * evaluate x b * (mapPoint (Algebra.ofId R S) g)⁻¹ :=
  conjugationPullback_point g ((Polynomial.aeval b).comp x)

private theorem conjugate_additive (g : HopfPoints R A R) {x : A →ₐ[R] Polynomial R}
    (hx : IsAdditive x) : IsAdditive (conjugateCoordinate g x) := by
  intro T
  refine ⟨?_, fun a b => ?_⟩
  · rw [evaluate_conjugate, (hx T).1, mul_one, mul_inv_cancel]
  · rw [evaluate_conjugate, evaluate_conjugate, evaluate_conjugate, (hx T).2]
    group

private theorem conjugate_surjective (g : HopfPoints R A R) {x : A →ₐ[R] Polynomial R}
    (hx : Function.Surjective x) : Function.Surjective (conjugateCoordinate g x) :=
  hx.comp (conjugationPullback_surjective g)

end Conjugation

section CompareLinkedPairs

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [HopfAlgebra R A] [HopfAlgebra R B]

private theorem evaluate_compGroup {S : Type u} [CommRing S] [Algebra R S]
    (f : B →ₐc[R] A) (x : A →ₐ[R] Polynomial R) (b : S) :
    mapGroup f (evaluate x b) = evaluate (x.comp f.toAlgHom) b := rfl

private theorem adjointQuadratic_compGroup (f : B →ₐc[R] A) (x y : A →ₐ[R] Polynomial R)
    (c : R) (b : B) :
    adjointQuadratic (x.comp f.toAlgHom) (y.comp f.toAlgHom) c b =
      adjointQuadratic x y c (f b) := by
  simp only [adjointQuadratic, ← evaluate_compGroup f, ← map_mul, ← map_inv]
  rfl

/-- After matching the positive coordinate, a map carrying the linked
negative coordinate into the corresponding negative root line has scale one. -/
private theorem matchNegative_of_quadratic (f : B →ₐc[R] A)
    (x y : A →ₐ[R] Polynomial R) (x' y' : B →ₐ[R] Polynomial R)
    (hp : x.comp f.toAlgHom = x') (hs : Function.Surjective x')
    (c : R) (hn : y.comp f.toAlgHom = rescaleCoordinate c y')
    (h₁ : ∀ a, adjointQuadratic x y 1 a = -(x a).coeff 1)
    (h₂ : ∀ b, adjointQuadratic x' y' c b = -c * (x' b).coeff 1) :
    y.comp f.toAlgHom = y' := by
  obtain ⟨b, hb⟩ := hs Polynomial.X
  have e := adjointQuadratic_compGroup f x y 1 b
  have hpb : x (f b) = x' b :=
    DFunLike.congr_fun hp b
  rw [hp, hn, adjointQuadratic_rescale, mul_one, h₁, h₂, hpb, hb,
    Polynomial.coeff_X_one, mul_one] at e
  have hc : c = 1 := neg_injective e
  rw [hn, hc]
  simp only [rescaleCoordinate, map_one, one_mul, Polynomial.aeval_X_left]
  rfl

end CompareLinkedPairs

section PolynomialComparison

set_option maxHeartbeats 1500000
set_option maxRecDepth 1200
set_option linter.style.haveILetI false

variable {R A S : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing S] [Algebra R S]

private theorem coordinate_ext {x y : A →ₐ[R] Polynomial R}
    (h : evaluate x (Polynomial.X : Polynomial R) = evaluate y Polynomial.X) : x = y := by
  have e := congrArg WithConv.ofConv h
  simpa only [evaluate, WithConv.ofConv_toConv, Polynomial.aeval_X_left, AlgHom.id_comp] using e

/-- Conjugation by the indicated torus point multiplies the additive parameter by a character. -/
private def ActsBy {C : Type u} [CommRing C] [HopfAlgebra R C]
    (t : A →ₐc[R] C) (m : C) (x : A →ₐ[R] Polynomial R) : Prop :=
  ∀ (S : CommAlgCat.{u} R) (a : S) (s : C →ₐ[R] S),
    let g := mapGroup t (toConv s)
    g * evaluate x a * g⁻¹ = evaluate x (s m * a)

private theorem rescale_scalar {C : Type u} [CommRing C] [HopfAlgebra R C]
    {t : A →ₐc[R] C} {m : C} {x : A →ₐ[R] Polynomial R}
    (r : R) (hx : ActsBy t m x) : ActsBy t m (rescaleCoordinate r x) := by
  intro S a s
  simp only [evaluate_rescale]
  rw [mul_left_comm (algebraMap R S r)]
  exact hx S _ s

private theorem rescale_rescale (r s : R) (x : A →ₐ[R] Polynomial R) :
    rescaleCoordinate r (rescaleCoordinate s x) = rescaleCoordinate (r * s) x := by
  apply coordinate_ext
  simp only [evaluate_rescale, map_mul]
  rw [mul_left_comm (algebraMap R (Polynomial R) s), ← mul_assoc]

private theorem rescale_one (x : A →ₐ[R] Polynomial R) : rescaleCoordinate 1 x = x := by
  apply coordinate_ext
  rw [evaluate_rescale, map_one, one_mul]

variable {K : Type u} [CommRing K] [Algebra R K]

private abbrev extendBialg {B : Type u} [CommRing B] [Bialgebra R B]
    (f : A →ₐc[R] B) : K ⊗[R] A →ₐc[K] K ⊗[R] B :=
  Bialgebra.TensorProduct.map (BialgHom.id K K) f

end PolynomialComparison

section FieldCoordinates

set_option maxHeartbeats 1800000
set_option maxRecDepth 1500
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Opposite
open _root_.LinearAlgebraicGroups.Specs (GroupScheme ClosedSubgroup Lie)
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs.IntegralCentralQuotient
  (RootScalarAction HopfSpectrum spectrumOfAlgHom spectrumOfHopfHom cocharacterEval)
open LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.Specs.AbstractPairing (Root)
open LinearAlgebraicGroups.Specs.CharacterDescent (Character Cocharacter)
open LinearAlgebraicGroups.Specs.DiagonalizableGroups (IntegerCharacters integerGenerator)
open LinearAlgebraicGroups.Specs.RootGroups (AdditiveLine IsRootSubgroup rootPoint)

open private additiveLine_tangent_point rootPoint_comp rootPoint_eq
  from LinearAlgebraicGroups.RootData.RootGroups
open private additiveIso_linear scaleIso scaleIso_point
  from LinearAlgebraicGroups.Classification.Pinning
open private subgroupOf_mutual_iso
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

set_option backward.isDefEq.respectTransparency false

variable {R K A : Type u} [CommRing R] [Field K] [CommRing A] [Algebra R K] [HopfAlgebra R A]

private theorem restrictPoint_injective {S : Type u} [CommRing S] [Algebra R S]
    [Algebra K S] [IsScalarTower R K S] :
    Function.Injective (restrictPoint (R := R) (K := K) (A := A) (S := S)) :=
  fun _ _ e => WithConv.ext ((AlgHom.liftEquiv R K A S).symm.injective
    (congrArg WithConv.ofConv e))

private theorem restrict_mapGroup {C S : Type u} [CommRing C] [HopfAlgebra R C] [CommRing S]
    [Algebra R S] [Algebra K S] [IsScalarTower R K S] (f : A →ₐc[R] C)
    (p : HopfPoints K (K ⊗[R] C) S) :
    restrictPoint (mapGroup (extendBialg (K := K) f) p) =
      mapGroup f (restrictPoint p) := by
  apply WithConv.ext
  ext a
  change p.ofConv (extendBialg (K := K) f (1 ⊗ₜ[R] a)) = p.ofConv (1 ⊗ₜ[R] f a)
  simp

private theorem extendRoot_surjective {x : A →ₐ[R] Polynomial R}
    (hx : Function.Surjective x) : Function.Surjective (extendRoot (K := K) x) := by
  obtain ⟨a, ha⟩ := hx Polynomial.X
  let z : Polynomial K →ₐ[K] K ⊗[R] A := Polynomial.aeval (1 ⊗ₜ[R] a)
  have h : (extendRoot (K := K) x).comp z = AlgHom.id K (Polynomial K) := by
    apply Polynomial.algHom_ext
    simp [z, extendRoot, ha]
  intro p
  exact ⟨z p, DFunLike.congr_fun h p⟩

private theorem extendRoot_rescale (r : R) (x : A →ₐ[R] Polynomial R) :
    extendRoot (K := K) (rescaleCoordinate r x) =
      rescaleCoordinate (algebraMap R K r) (extendRoot (K := K) x) := by
  let S := Polynomial K
  letI : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq' rfl
  apply coordinate_ext
  apply restrictPoint_injective (R := R)
  rw [evaluate_rescale, restrict_evaluate, restrict_evaluate, evaluate_rescale,
    ← IsScalarTower.algebraMap_apply]

private def FibreActsBy {X : Type u} [CommGroup X]
    (t : A →ₐc[R] MonoidAlgebra R X) (χ : X)
    (x : K ⊗[R] A →ₐ[K] Polynomial K) : Prop :=
  ActsBy (R := K) (A := K ⊗[R] A) (C := K ⊗[R] MonoidAlgebra R X)
    (extendBialg (K := K) (B := MonoidAlgebra R X) t)
    ((1 : K) ⊗ₜ[R] MonoidAlgebra.of R X χ) x

private theorem extendRoot_scalar {X : Type u} [CommGroup X]
    {t : A →ₐc[R] MonoidAlgebra R X} {m : X} {x : A →ₐ[R] Polynomial R}
    (hx : RootScalarAction t x m) :
    FibreActsBy t m (extendRoot (K := K) x) := by
  intro S a s
  letI : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq' rfl
  apply restrictPoint_injective (R := R)
  simp only [map_mul, map_inv, restrict_mapGroup, restrict_evaluate]
  exact hx (CommAlgCat.of R S) a ((restrictPoint (toConv s)).ofConv)

private def fieldPointIso {C : Type u} [CommRing C] [HopfAlgebra K C]
    {G : GroupScheme K} (e : HopfSpectrum K C ≅ G) (S : TestAlgebra K) :
    HopfPoints K C S ≃* GroupPoints G S :=
  Spec.mapMulEquiv.trans ((((groupPointsFunctor K).mapIso e).app S).groupIsoToMulEquiv)

private theorem fieldPoint_natural {C S T : Type u} [CommRing C] [HopfAlgebra K C]
    [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]
    {G : GroupScheme K} (e : HopfSpectrum K C ≅ G)
    (g : S →ₐ[K] T) (p : HopfPoints K C S) :
    fieldPointIso e (CommAlgCat.of K T) (mapPoint g p) =
      mapPoints (CommAlgCat.ofHom g) (fieldPointIso e (CommAlgCat.of K S) p) := by
  change spectrumOfAlgHom (g.comp p.ofConv) ≫ e.hom.hom.hom =
    spectrumOfAlgHom g ≫ (spectrumOfAlgHom p.ofConv ≫ e.hom.hom.hom)
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

private def pullbackCoordinate {C : Type u} [CommRing C] [HopfAlgebra K C]
    {G : GroupScheme K} (e : HopfSpectrum K C ≅ G) {L : AdditiveLine K}
    (f : L.group ⟶ G) : C →ₐ[K] Polynomial K :=
  ((algSpec.fullyFaithful (R := CommRingCat.of K)).preimage
    (f.hom.hom ≫ e.inv.hom.hom)).unop.hom

private theorem pullbackCoordinate_point {C : Type u} [CommRing C] [HopfAlgebra K C]
    {G : GroupScheme K} (e : HopfSpectrum K C ≅ G) {L : AdditiveLine K}
    (f : L.group ⟶ G) (S : TestAlgebra K) (b : S) :
    fieldPointIso e S (evaluate (pullbackCoordinate e f) b) = rootPoint f S b := by
  let F := algSpec (CommRingCat.of K)
  change F.map ((CommAlgCat.ofHom (Polynomial.aeval b)).op ≫
      (algSpec.fullyFaithful (R := CommRingCat.of K)).preimage
        (f.hom.hom ≫ e.inv.hom.hom)) ≫ e.hom.hom.hom = _
  rw [F.map_comp, Functor.FullyFaithful.map_preimage]
  unfold rootPoint
  rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id]

private def restrictPointEquiv {S : Type u} [CommRing S] [Algebra R S]
    [Algebra K S] [IsScalarTower R K S] :
    HopfPoints K (K ⊗[R] A) S ≃* HopfPoints R A S :=
  MulEquiv.ofBijective restrictPoint
    ⟨restrictPoint_injective, fun p =>
      ⟨toConv (AlgHom.liftEquiv R K A S p.ofConv),
        WithConv.ext ((AlgHom.liftEquiv R K A S).symm_apply_apply _)⟩⟩

private def fibreCocharacter {X : Type u} [CommGroup X]
    (t : A →ₐc[R] MonoidAlgebra R X) (ν : X →* Multiplicative ℤ)
    (S : CommAlgCat.{u} K) : Sˣ →* HopfPoints K (K ⊗[R] A) S :=
  letI : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq' rfl
  restrictPointEquiv.symm.toMonoidHom.comp (cocharacterPoint t ν (CommAlgCat.of R S))

private theorem restrict_fibreCocharacter {X : Type u} [CommGroup X]
    (t : A →ₐc[R] MonoidAlgebra R X) (ν : X →* Multiplicative ℤ)
    (S : CommAlgCat.{u} K) (a : Sˣ) :
    letI : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
    letI : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq' rfl
    restrictPoint (fibreCocharacter t ν S a) = cocharacterPoint t ν (CommAlgCat.of R S) a := by
  letI : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq' rfl
  exact (restrictPointEquiv (R := R) (K := K) (A := A) (S := S)).apply_symm_apply _

private theorem restrict_mapPoint {S T : Type u} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra K S] [Algebra K T]
    [IsScalarTower R K S] [IsScalarTower R K T]
    (g : S →ₐ[K] T) (p : HopfPoints K (K ⊗[R] A) S) :
    restrictPoint (mapPoint g p) = mapPoint (g.restrictScalars R) (restrictPoint p) := rfl

private theorem fibreCocharacter_natural {X : Type u} [CommGroup X]
    (t : A →ₐc[R] MonoidAlgebra R X) (ν : X →* Multiplicative ℤ)
    {S T : CommAlgCat.{u} K} (g : S →ₐ[K] T) (a : Sˣ) :
    mapPoint g (fibreCocharacter t ν S a) =
      fibreCocharacter t ν T (Units.map g.toMonoidHom a) := by
  letI : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra R T := ((algebraMap K T).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K T := IsScalarTower.of_algebraMap_eq' rfl
  apply restrictPoint_injective (R := R)
  rw [restrict_mapPoint, restrict_fibreCocharacter, restrict_fibreCocharacter]
  exact cocharacterPoint_natural t ν (S := CommAlgCat.of R S) (T := CommAlgCat.of R T)
    (g.restrictScalars R) a

private theorem fibrePositiveScalar {D : BasedRootDatum.{u}}
    {t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X)} (i : D.I)
    {x : A →ₐ[R] Polynomial R} (hx : RootScalarAction t x (Multiplicative.ofAdd (D.datum.root i)))
    (S : CommAlgCat.{u} K) (a : Sˣ) (b : S) :
    fibreCocharacter t (coroot i) S a * evaluate (extendRoot (K := K) x) b *
      (fibreCocharacter t (coroot i) S a)⁻¹ =
      evaluate (extendRoot (K := K) x) ((a : S)^2 * b) := by
  letI : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq' rfl
  apply restrictPoint_injective (R := R)
  simp only [map_mul, map_inv, restrict_fibreCocharacter, restrict_evaluate]
  exact linkedPositiveScalar t i hx (CommAlgCat.of R S) a b

private theorem fibreNegativeScalar {D : BasedRootDatum.{u}}
    {t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X)} (i : D.I)
    {x : A →ₐ[R] Polynomial R}
    (hx : RootScalarAction t x (Multiplicative.ofAdd (D.datum.root (D.datum.reflectionPerm i i))))
    (S : CommAlgCat.{u} K) (a : Sˣ) (b : S) :
    fibreCocharacter t (coroot i) S a * evaluate (extendRoot (K := K) x) b *
      (fibreCocharacter t (coroot i) S a)⁻¹ =
      evaluate (extendRoot (K := K) x) ((↑a⁻¹ : S)^2 * b) := by
  letI : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq' rfl
  apply restrictPoint_injective (R := R)
  simp only [map_mul, map_inv, restrict_fibreCocharacter, restrict_evaluate]
  exact linkedNegativeScalar t i hx (CommAlgCat.of R S) a b

variable {D : BasedRootDatum.{u}} {t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X)}

private def markedCharacter (F : FibreFrame D t K) (χ : D.X) : Character F.pair.T.group :=
  letI := F.datum.comm
  Additive.toMul (F.marking.val.weightEquiv χ)

private theorem markedCharacter_root (F : FibreFrame D t K) (i : D.I) :
    markedCharacter F (D.datum.root i) = (F.marking.val.indexEquiv i).val := by
  letI := F.datum.comm
  have h := RootPairing.Hom.root_weightMap_apply D.datum F.datum.toBased.datum i F.marking.val.toHom
  change F.marking.val.weightEquiv (D.datum.root i) =
    F.datum.datum.rootDatum.root (F.marking.val.indexEquiv i) at h
  exact congrArg Additive.toMul (h.trans (F.datum.datum.root_eq _))

private theorem markedCharacter_opposite (F : FibreFrame D t K) (i : D.I) :
    (F.marking.val.indexEquiv (D.datum.reflectionPerm i i)).val =
      ((F.marking.val.indexEquiv i).val)⁻¹ := by
  letI := F.datum.comm
  rw [← markedCharacter_root, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  change Additive.toMul (F.marking.val.weightEquiv (-D.datum.root i)) = _
  rw [map_neg]
  exact congrArg Inv.inv (markedCharacter_root F i)

private theorem fieldPoint_inclusion {C B : Type u} [CommRing C] [CommRing B]
    [HopfAlgebra K C] [HopfAlgebra K B] {G T : GroupScheme K}
    (e : HopfSpectrum K C ≅ G) (s : HopfSpectrum K B ≅ T) (f : C →ₐc[K] B)
    (j : T ⟶ G) (h : spectrumOfHopfHom f ≫ e.hom = s.hom ≫ j)
    (S : TestAlgebra K) (p : HopfPoints K B S) :
    fieldPointIso e S (mapGroup f p) = fieldPointIso s S p ≫ j.hom.hom := by
  change spectrumOfAlgHom (p.ofConv.comp f.toAlgHom) ≫ e.hom.hom.hom =
    (spectrumOfAlgHom p.ofConv ≫ s.hom.hom.hom) ≫ j.hom.hom
  have he : (spectrumOfHopfHom f ≫ e.hom).hom.hom = (s.hom ≫ j).hom.hom :=
    congrArg (fun a : HopfSpectrum K B ⟶ G => a.hom.hom) h
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom] at he
  have hc : spectrumOfAlgHom (p.ofConv.comp f.toAlgHom) =
      spectrumOfAlgHom p.ofConv ≫ spectrumOfAlgHom f.toAlgHom :=
    (algSpec (CommRingCat.of K)).map_comp (CommAlgCat.ofHom p.ofConv).op
      (CommAlgCat.ofHom f.toAlgHom).op
  rw [hc]
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun a => spectrumOfAlgHom p.ofConv ≫ a) he

private abbrev fibreTorusInclusion {X : Type u} [CommGroup X]
    (t : A →ₐc[R] MonoidAlgebra R X) : K ⊗[R] A →ₐc[K] K ⊗[R] MonoidAlgebra R X :=
  Bialgebra.TensorProduct.map (BialgHom.id K K) t

private def frameTorusPoint {X : Type u} [CommGroup X]
    (t : A →ₐc[R] MonoidAlgebra R X) (S : TestAlgebra K) :
    HopfPoints K (K ⊗[R] MonoidAlgebra R X) S →* HopfPoints K (K ⊗[R] A) S :=
  mapGroup (R := K) (A := K ⊗[R] MonoidAlgebra R X) (B := K ⊗[R] A) (S := S)
    (fibreTorusInclusion (R := R) (K := K) (A := A) (X := X) t)

private theorem fieldTorusPoint_inclusion (F : FibreFrame D t K) (S : TestAlgebra K)
    (p : HopfPoints K (K ⊗[R] MonoidAlgebra R (Multiplicative D.X)) S) :
    fieldPointIso F.groupIso S (frameTorusPoint (X := Multiplicative D.X) t S p) =
      fieldPointIso F.torusIso S p ≫ F.pair.T.inclusion.hom.hom := by
  exact fieldPoint_inclusion (C := K ⊗[R] A) (B := K ⊗[R] MonoidAlgebra R (Multiplicative D.X))
    F.groupIso F.torusIso (fibreTorusInclusion (R := R) (K := K) (A := A) (X := Multiplicative D.X) t)
    F.pair.T.inclusion F.torus_eq S p

private theorem fieldTorusPoint_value (F : FibreFrame D t K) (S : TestAlgebra K)
    (p : HopfPoints K (K ⊗[R] MonoidAlgebra R (Multiplicative D.X)) S) (χ : D.X) :
    Specs.CharacterPairing.characterValue (markedCharacter F χ) S
        (fieldPointIso F.torusIso S p) =
      p.ofConv ((1 : K) ⊗ₜ[R] MonoidAlgebra.of R _ (Multiplicative.ofAdd χ)) := by
  let ff := algSpec.fullyFaithful (R := CommRingCat.of K)
  let α := markedCharacter F χ
  change ((ff.preimage
    ((spectrumOfAlgHom p.ofConv ≫ F.torusIso.hom.hom.hom) ≫ α.hom.hom)).unop).hom
    (MonoidAlgebra.of K IntegerCharacters integerGenerator) = _
  rw [Category.assoc, ← Grp.comp_hom_hom, ff.preimage_comp, ff.preimage_map]
  change p.ofConv (((ff.preimage (F.torusIso.hom ≫ α).hom.hom).unop).hom
    (MonoidAlgebra.of K IntegerCharacters integerGenerator)) = _
  exact congrArg p.ofConv (F.character_eq χ)

private def markedCoroot (F : FibreFrame D t K) (i : D.I) : Cocharacter F.pair.T.group :=
  letI := F.datum.comm
  Additive.toMul (F.datum.datum.rootDatum.coroot (F.marking.val.indexEquiv i))

private theorem fibreCocharacter_point (F : FibreFrame D t K) (i : D.I)
    (S : TestAlgebra K) (a : Sˣ) :
    fieldPointIso F.groupIso S (fibreCocharacter t (coroot i) S a) =
      LinearAlgebraicGroups.CocharacterDynamics.cocharacterPoint (markedCoroot F i) S a ≫
        F.pair.T.inclusion.hom.hom := by
  letI : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq' rfl
  letI := F.datum.comm
  let g := LinearAlgebraicGroups.CocharacterDynamics.cocharacterPoint (markedCoroot F i) S a
  let q := (fieldPointIso F.torusIso S).symm g
  have hq : fieldPointIso F.torusIso S q = g := (fieldPointIso F.torusIso S).apply_symm_apply g
  change fieldPointIso F.groupIso S _ = g ≫ _
  rw [← hq, ← fieldTorusPoint_inclusion]
  refine congrArg (fieldPointIso F.groupIso S) ?_
  apply restrictPoint_injective (R := R)
  have hmap : restrictPoint (frameTorusPoint (X := Multiplicative D.X) t S q) =
      mapGroup t (restrictPoint q) :=
    restrict_mapGroup (C := MonoidAlgebra R (Multiplicative D.X)) t q
  rw [restrict_fibreCocharacter, hmap]
  change mapGroup t (toConv (cocharacterEval (coroot i) (CommAlgCat.of R S) a)) =
    mapGroup t (restrictPoint q)
  congr 1
  apply torusPoint_ext
  intro χ
  change cocharacterEval (coroot i) (CommAlgCat.of R S) a (MonoidAlgebra.of R _ χ) =
    q.ofConv (1 ⊗ₜ[R] MonoidAlgebra.of R _ χ)
  have he : Specs.CharacterPairing.characterValue (markedCharacter F χ.toAdd) S
      (fieldPointIso F.torusIso S q) = q.ofConv ((1 : K) ⊗ₜ[R] MonoidAlgebra.of R _ χ) :=
    fieldTorusPoint_value F S q χ.toAdd
  rw [← he, hq, cocharacterEval_monomial]
  change ((a ^ (coroot i χ).toAdd : Sˣ) : S) =
    Specs.CharacterPairing.characterValue (markedCharacter F χ.toAdd) S
      (LinearAlgebraicGroups.CocharacterDynamics.cocharacterPoint (markedCoroot F i) S a)
  have h := (LinearAlgebraicGroups.RootData.CharacterPairing.characterPairingComposition
    F.pair.T.group (markedCharacter F χ.toAdd) (markedCoroot F i)).2 S a
  change _ = _ at h
  rw [h]
  have hp : (coroot i χ).toAdd =
      Specs.CharacterPairing.pairing F.pair.T.group (markedCharacter F χ.toAdd) (markedCoroot F i) := by
    rw [← F.datum.datum.pairing_eq]
    exact (F.marking.val.coroot'_weightEquiv i χ.toAdd).symm
  rw [hp]

private theorem rootSubgroups_same (F : FibreFrame D t K) (i : D.I)
    {U V : ClosedSubgroup F.pair.G.val}
    (hU : IsRootSubgroup F.pair.T U (F.marking.val.indexEquiv i).val)
    (hV : IsRootSubgroup F.pair.T V (F.marking.val.indexEquiv i).val) :
    ∃ e : U.group ≅ V.group, e.hom ≫ V.inclusion = U.inclusion := by
  let P := F.pair
  let α := F.marking.val.indexEquiv i
  obtain ⟨W, _, _, _, _, hw⟩ :=
    ((LinearAlgebraicGroups.RootData.RootGroups.rootSubgroups P.G P.reductive P.T P.split
      P.maximal).2 α.val α.property).2.2
  obtain ⟨g, hg⟩ := subgroupOf_mutual_iso (hw U hU).2 (hw U hU).1
  obtain ⟨h, hh⟩ := subgroupOf_mutual_iso (hw V hV).1 (hw V hV).2
  refine ⟨g ≪≫ h, ?_⟩
  change (g.hom ≫ h.hom) ≫ V.inclusion = _
  rw [Category.assoc, hh, hg]

private theorem fibreCoordinate_scaleTo {x : A →ₐ[R] Polynomial R}
    (F : FibreFrame D t K) (i : D.I) (hx : FibreCoordinate F i x)
    {U : ClosedSubgroup F.pair.G.val} {L : AdditiveLine K}
    (j : L.group ≅ U.group)
    (hU : IsRootSubgroup F.pair.T U (F.marking.val.indexEquiv i).val) :
    ∃ c : Kˣ, extendRoot (K := K) x =
      rescaleCoordinate (c : K) (pullbackCoordinate F.groupIso (j.hom ≫ U.inclusion)) := by
  obtain ⟨V, M, k, hV, hk⟩ := hx
  obtain ⟨e, he⟩ := rootSubgroups_same F i hV hU
  let l := k ≪≫ e ≪≫ j.symm
  obtain ⟨c, hc⟩ := additiveIso_linear M L l
  refine ⟨c, coordinate_ext ?_⟩
  let S := CommAlgCat.of K (Polynomial K)
  apply (fieldPointIso F.groupIso S).injective
  rw [evaluate_rescale, pullbackCoordinate_point]
  have h := rootPoint_comp l.hom (j.hom ≫ U.inclusion) S Polynomial.X
  rw [hc, ← rootPoint_eq] at h
  have hl : l.hom ≫ (j.hom ≫ U.inclusion) = k.hom ≫ V.inclusion := by
    change (k.hom ≫ e.hom ≫ j.inv) ≫ (j.hom ≫ U.inclusion) = _
    simp [he]
  rw [hl] at h
  exact (hk S Polynomial.X).trans h

private theorem fibreCoordinate_rescale {x : A →ₐ[R] Polynomial R}
    (F : FibreFrame D t K) (i : D.I) (hx : FibreCoordinate F i x) (c : Rˣ) :
    FibreCoordinate F i (rescaleCoordinate (c : R) x) := by
  obtain ⟨U, L, j, hj, hx⟩ := hx
  let cK := Units.map (algebraMap R K).toMonoidHom c
  refine ⟨U, L, scaleIso L L cK ≪≫ j, hj, fun S a => ?_⟩
  change fieldPointIso F.groupIso S (evaluate (extendRoot (K := K) (rescaleCoordinate (c : R) x)) a) =
    rootPoint (((scaleIso L L cK).hom ≫ j.hom) ≫ U.inclusion) S a
  rw [extendRoot_rescale, evaluate_rescale, Category.assoc, rootPoint_comp, scaleIso_point,
    ← rootPoint_eq]
  exact hx S _

private theorem fibreWord_restrict {x y : A →ₐ[R] Polynomial R}
    (i : D.I) (h : IsLinked t i x y) (S : CommAlgCat.{u} K) (a : Sˣ) :
    rankOneWord (extendRoot (K := K) x) (extendRoot (K := K) y) a =
      fibreCocharacter t (coroot i) S a *
        rankOneWord (extendRoot (K := K) x) (extendRoot (K := K) y) 1 := by
  letI : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq' rfl
  apply restrictPoint_injective (R := R)
  simp only [rankOneWord, map_mul, restrict_evaluate, restrict_fibreCocharacter]
  exact linkedWord t i h (CommAlgCat.of R S) a

private theorem fibreLinkExists (F : FibreFrame D t K) (i : D.I)
    {x y : A →ₐ[R] Polynomial R} (hx : FibreCoordinate F i x)
    (hy : FibreCoordinate F (D.datum.reflectionPerm i i) y) :
    ∃ (z : K ⊗[R] A →ₐ[K] Polynomial K) (b : Kˣ),
      extendRoot (K := K) y = rescaleCoordinate (b : K) z ∧
      ∀ (S : CommAlgCat.{u} K) (a : Sˣ),
        rankOneWord (extendRoot (K := K) x) z a =
          fibreCocharacter t (coroot i) S a * rankOneWord (extendRoot (K := K) x) z 1 := by
  let α := F.marking.val.indexEquiv i
  letI := F.datum.comm
  obtain ⟨C, ν, _, _, H, J, _, Q, flag, P, L, p, n, hp, hn, _, _, r, hr⟩ :=
    F.datum.datum.attached α
  let U := Specs.GeometricBorelConjugacy.subgroupOfSubgroup C.subgroup H.contracting
  let V := Specs.GeometricBorelConjugacy.subgroupOfSubgroup C.subgroup J.contracting
  let p0 := p.root.hom ≫ U.inclusion
  let n0 := n.root.hom ≫ V.inclusion
  let X := pullbackCoordinate F.groupIso p0
  let Y := pullbackCoordinate F.groupIso n0
  obtain ⟨a, ha⟩ := fibreCoordinate_scaleTo F i hx p.root hp
  have hn' : IsRootSubgroup F.pair.T V (F.marking.val.indexEquiv (D.datum.reflectionPerm i i)).val := by
    rw [markedCharacter_opposite]
    exact hn
  obtain ⟨b, hb⟩ := fibreCoordinate_scaleTo F _ hy n.root hn'
  let z := rescaleCoordinate (↑a⁻¹ : K) Y
  refine ⟨z, a * b, ?_, fun S v => ?_⟩
  · rw [hb, rescale_rescale, Units.val_mul, mul_comm (a : K) (b : K), mul_assoc,
      Units.mul_inv, mul_one]
  have word (w : Sˣ) : rankOneWord (extendRoot (K := K) x) z w =
      rankOneWord X Y (Units.map (algebraMap K S).toMonoidHom a * w) := by
    rw [ha]
    simp only [z, rankOneWord, evaluate_rescale, Units.val_mul, Units.coe_map,
      mul_inv_rev, Units.coe_map_inv, mul_neg, mul_comm (↑w⁻¹ : S), X] <;> rfl
  have w0 (w : Sˣ) : rankOneWord X Y w =
      fibreCocharacter t (coroot i) S w * rankOneWord X Y 1 := by
    apply (fieldPointIso F.groupIso S).injective
    simp only [rankOneWord, map_mul, X, Y, pullbackCoordinate_point]
    have hw := r.coroot_word S w
    change LinearAlgebraicGroups.CocharacterDynamics.cocharacterPoint r.coroot S w ≫
      F.pair.T.inclusion.hom.hom =
      Specs.RootGroups.rankOneWord p0 n0 S w * (Specs.RootGroups.rankOneWord p0 n0 S 1)⁻¹ at hw
    rw [fibreCocharacter_point, ← show r.coroot = markedCoroot F i from hr]
    exact mul_inv_eq_iff_eq_mul.mp hw.symm
  rw [word v, word 1, mul_one, w0 (_ * v), w0 (Units.map _ _), map_mul]
  have hcomm := congrArg (fibreCocharacter t (coroot i) S)
    (mul_comm (Units.map (algebraMap K S).toMonoidHom a) v)
  rw [map_mul, map_mul] at hcomm
  rw [hcomm, mul_assoc]

open Specs.AdjointRepresentation (constants dualMap scale)
open Specs.CharacterPairing (adjointWeightVectors characterValue)

private def fibreTangent (F : FibreFrame D t K) {x : K ⊗[R] A →ₐ[K] Polynomial K}
    (hx : IsAdditive x) : Lie K F.pair.G.val := by
  refine ⟨fieldPointIso F.groupIso (CommAlgCat.of K (DualNumber K))
    (evaluate x DualNumber.eps), ?_⟩
  change mapPoints (dualReduction K) (fieldPointIso F.groupIso _ (evaluate x DualNumber.eps)) = 1
  change mapPoints (CommAlgCat.ofHom (TrivSqZeroExt.fstHom K K K))
    (fieldPointIso F.groupIso _ (evaluate x (dual 0 (1 : K)))) = 1
  rw [← fieldPoint_natural, tangent_reduces x hx, map_one]

private theorem fibreTangent_weight (F : FibreFrame D t K) (i : D.I)
    {x : K ⊗[R] A →ₐ[K] Polynomial K} (hx : IsAdditive x)
    (hw : FibreActsBy (X := Multiplicative D.X) t (Multiplicative.ofAdd (D.datum.root i)) x) :
    fibreTangent F hx ∈ adjointWeightVectors F.pair.T (F.marking.val.indexEquiv i).val := by
  rw [← markedCharacter_root]
  intro S a
  let q := (fieldPointIso F.torusIso S).symm a
  have hq : fieldPointIso F.torusIso S q = a := (fieldPointIso F.torusIso S).apply_symm_apply a
  let m := (1 : K) ⊗ₜ[R] MonoidAlgebra.of R _ (Multiplicative.ofAdd (D.datum.root i))
  let c := q.ofConv m
  let W := CommAlgCat.of K (DualNumber S)
  let k := (constants S).hom
  let Fp := fieldPointIso F.groupIso W
  have hg :
      Fp (frameTorusPoint (X := Multiplicative D.X) t W (toConv (k.comp q.ofConv))) =
        mapPoints (constants S) (a ≫ F.pair.T.inclusion.hom.hom) := by
    change _ = mapPoints (CommAlgCat.ofHom k) _
    rw [← hq, ← fieldTorusPoint_inclusion, ← fieldPoint_natural]
    rfl
  have hp :
      Fp (evaluate x (DualNumber.eps : DualNumber S)) =
        mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId K S))) (fibreTangent F hx).toMul.val := by
    let f := (dualMap (CommAlgCat.ofHom (Algebra.ofId K S))).hom
    have he : f (DualNumber.eps : DualNumber K) = (DualNumber.eps : DualNumber S) := by
      apply TrivSqZeroExt.ext
      · exact map_zero (algebraMap K S)
      · exact map_one (algebraMap K S)
    have h := fieldPoint_natural F.groupIso f (evaluate x (DualNumber.eps : DualNumber K))
    rw [evaluate_natural, he] at h
    exact h
  have hscale :
      Fp (evaluate x (k c * (DualNumber.eps : DualNumber S))) =
        mapPoints (scale S c) (Fp (evaluate x DualNumber.eps)) := by
    have he : (scale S c).hom (DualNumber.eps : DualNumber S) =
        k c * (DualNumber.eps : DualNumber S) := by
      apply TrivSqZeroExt.ext
      · change 0 = c * 0
        exact (mul_zero c).symm
      · change c * 1 = c * 1 + 0 * 0
        rw [zero_mul, add_zero]
    have h := fieldPoint_natural F.groupIso (scale S c).hom (evaluate x (DualNumber.eps : DualNumber S))
    rw [evaluate_natural, he] at h
    exact h
  have hs := congrArg Fp (hw W (DualNumber.eps : DualNumber S) (k.comp q.ofConv))
  simp only [map_mul, map_inv] at hs
  change Fp (frameTorusPoint (X := Multiplicative D.X) t W (toConv (k.comp q.ofConv))) *
    Fp (evaluate x (DualNumber.eps : DualNumber S)) *
    (Fp (frameTorusPoint (X := Multiplicative D.X) t W (toConv (k.comp q.ofConv))))⁻¹ =
    Fp (evaluate x (k c * DualNumber.eps)) at hs
  rw [hg, hscale, hp] at hs
  have hc : characterValue (markedCharacter F (D.datum.root i)) S a = c := by
    rw [← hq, fieldTorusPoint_value]
  change _ * _ * _ = mapPoints (scale S (characterValue _ S a)) _
  rw [hc]
  exact hs

private theorem fibre_eq_rescale [CharZero K] (F : FibreFrame D t K) (i : D.I)
    {y : A →ₐ[R] Polynomial R} (hy : FibreCoordinate F i y) (hya : IsAdditive y)
    {x : K ⊗[R] A →ₐ[K] Polynomial K} (hx : IsAdditive x)
    (hw : FibreActsBy (X := Multiplicative D.X) t (Multiplicative.ofAdd (D.datum.root i)) x) :
    ∃ c : K, x = rescaleCoordinate c (extendRoot (K := K) y) := by
  obtain ⟨U, L, j, hU, hj⟩ := hy
  let P := F.pair
  let α := F.marking.val.indexEquiv i
  obtain ⟨V, hV, _, hVR, _, _⟩ :=
    ((LinearAlgebraicGroups.RootData.RootGroups.rootSubgroups P.G P.reductive P.T P.split
      P.maximal).2 α.val α.property).2.2
  obtain ⟨e, he⟩ := rootSubgroups_same F i hV hU
  have h := fibreTangent_weight F i hx hw
  rw [← hVR] at h
  obtain ⟨p, hp⟩ := h
  let S := CommAlgCat.of K (DualNumber K)
  obtain ⟨b, hb⟩ := additiveLine_tangent_point L j (mapPointKernel e.hom p)
  have eq : fieldPointIso F.groupIso S (evaluate x (DualNumber.eps : DualNumber K)) =
      fieldPointIso F.groupIso S (evaluate (extendRoot (K := K) y) (dual 0 b)) := by
    have hj' : fieldPointIso F.groupIso S (evaluate (extendRoot (K := K) y) (dual 0 b)) =
        rootPoint (j.hom ≫ U.inclusion) S (dual 0 b) := hj S _
    have h := congrArg (fun v : Lie K P.G.val => v.toMul.val) hp
    change p.toMul.val ≫ V.inclusion.hom.hom =
      fieldPointIso F.groupIso S (evaluate x DualNumber.eps) at h
    refine h.symm.trans (Eq.trans ?_ hj'.symm)
    rw [rootPoint_comp]
    change _ = rootPoint j.hom S (dual 0 b) ≫ U.inclusion.hom.hom
    have hbp : rootPoint j.hom S (dual 0 b) = p.toMul.val ≫ e.hom.hom.hom := hb.symm
    rw [hbp, Category.assoc, ← Grp.comp_hom_hom, he]
  refine ⟨b, additiveCoordinates_eq_of_tangent hx (rescale_additive b (extendRoot_additive hya)) ?_⟩
  rw [evaluate_rescale]
  have hb' : algebraMap K (DualNumber K) b * DualNumber.eps = dual 0 b := by
    apply TrivSqZeroExt.ext
    · change b * 0 = 0
      exact mul_zero b
    · change b * 1 + 0 * 0 = b
      rw [mul_one, zero_mul, add_zero]
  rw [hb']
  exact (fieldPointIso F.groupIso S).injective eq

end FieldCoordinates

section IntegralNormalization

open LinearAlgebraicGroups.Specs.IntegralCentralQuotient (cocharacterEval)

set_option maxHeartbeats 1800000
set_option maxRecDepth 1500
set_option linter.style.haveILetI false

open LinearAlgebraicGroups.Specs.IntegralCentralQuotient (RootScalarAction)
open LinearAlgebraicGroups.Specs.DiagonalizableGroups (IntegerCharacters integerGenerator)

variable {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
variable {D : BasedRootDatum.{u}} {t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X)}

private theorem onWord_natural {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) (x y : A →ₐ[R] Polynomial R) (a : Sˣ) :
    mapPoint f (rankOneWord x y a) = rankOneWord x y (Units.map f.toMonoidHom a) := by
  simp only [rankOneWord, map_mul, evaluate_natural, Units.coe_map, Units.coe_map_inv, map_neg]
  rfl

private theorem linked_of_generic {K : Type u} [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) (i : D.I) (x y : A →ₐ[R] Polynomial R)
    (h : ∀ (S : CommAlgCat.{u} K) (a : Sˣ),
      rankOneWord (extendRoot (K := K) x) (extendRoot (K := K) y) a =
        fibreCocharacter t (coroot i) S a *
          rankOneWord (extendRoot (K := K) x) (extendRoot (K := K) y) 1) :
    IsLinked t i x y := by
  let U := CommAlgCat.of R (MonoidAlgebra R IntegerCharacters.{u})
  let V := CommAlgCat.of K (MonoidAlgebra K IntegerCharacters.{u})
  letI : Algebra R V := ((algebraMap K V).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K V := IsScalarTower.of_algebraMap_eq' rfl
  let e : U →ₐ[R] V :=
    { toRingHom := MonoidAlgebra.mapRingHom IntegerCharacters (algebraMap R K)
      commutes' r := MonoidAlgebra.mapRingHom_single (algebraMap R K) 1 r }
  let a₀ : Uˣ := (MonoidAlgebra.of R IntegerCharacters).toHomUnits integerGenerator
  have h₀ : rankOneWord x y a₀ =
      cocharacterPoint t (coroot i) U a₀ * rankOneWord x y 1 := by
    have eq := congrArg (restrictPoint (R := R) (K := K) (A := A) (S := V))
      (h V (Units.map e.toMonoidHom a₀))
    simp only [rankOneWord, map_mul, restrict_evaluate, restrict_fibreCocharacter] at eq
    have u :
        mapPoint e (rankOneWord x y a₀) =
          mapPoint e (cocharacterPoint t (coroot i) U a₀ * rankOneWord x y 1) := by
      rw [map_mul, onWord_natural, onWord_natural, map_one,
        cocharacterPoint_natural t (coroot i) (S := U) (T := CommAlgCat.of R V) e a₀]
      exact eq
    have he : Function.Injective e := by
      intro a b h
      ext m
      apply hinj
      exact congrArg (fun p : V => p.coeff m) h
    exact WithConv.ext (AlgHom.ext fun b => he (congrArg
      (fun p : HopfPoints R A V => p.ofConv b) u))
  intro S a
  let g : U →ₐ[R] S := cocharacterEval MulEquiv.ulift.toMonoidHom S a
  have ha : Units.map g.toMonoidHom a₀ = a := by
    apply Units.ext
    change cocharacterEval MulEquiv.ulift.toMonoidHom S a
      (MonoidAlgebra.of R IntegerCharacters integerGenerator) = (a : S)
    rw [cocharacterEval_monomial]
    exact congrArg Units.val (zpow_one a)
  have eq := congrArg (mapPoint g) h₀
  rw [onWord_natural, map_mul, cocharacterPoint_natural t (coroot i) (S := U) (T := S) g a₀,
    onWord_natural, ha, map_one] at eq
  exact mul_inv_eq_iff_eq_mul.mpr eq

private theorem normalizeOpposite [IsDomain R] {K₀ : Type u} [Field K₀] [IsAlgClosed K₀]
    [Algebra R K₀] (hinj : Function.Injective (algebraMap R K₀))
    (i : D.I) {x y : A →ₐ[R] Polynomial R} (hxs : Function.Surjective x)
    (hxa : IsAdditive x) (hya : IsAdditive y)
    (hxw : RootScalarAction t x (Multiplicative.ofAdd (D.datum.root i)))
    (hyw : RootScalarAction t y (Multiplicative.ofAdd (D.datum.root (D.datum.reflectionPerm i i))))
    (hf : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
      ∃ F : FibreFrame D t K, FibreCoordinate F i x ∧
        FibreCoordinate F (D.datum.reflectionPerm i i) y) :
    ∃ r : Rˣ, IsLinked t i x (rescaleCoordinate (r : R) y) := by
  obtain ⟨a, ha⟩ := hxs Polynomial.X
  have fibre (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K] :
      ∃ (z : K ⊗[R] A →ₐ[K] Polynomial K) (b : Kˣ),
        extendRoot (K := K) y = rescaleCoordinate (b : K) z ∧
        (∀ (S : CommAlgCat.{u} K) (v : Sˣ),
          rankOneWord (extendRoot (K := K) x) z v =
            fibreCocharacter t (coroot i) S v * rankOneWord (extendRoot (K := K) x) z 1) ∧
        adjointQuadratic (extendRoot (K := K) x) z (b : K) ((1 : K) ⊗ₜ[R] a) =
          -(b : K) * ((extendRoot (K := K) x) ((1 : K) ⊗ₜ[R] a)).coeff 1 := by
    obtain ⟨F, hx, hy⟩ := hf K
    obtain ⟨z, b, hb, hw⟩ := fibreLinkExists F i hx hy
    have hz : z = rescaleCoordinate (↑b⁻¹ : K) (extendRoot (K := K) y) := by
      rw [hb, rescale_rescale, Units.inv_mul, rescale_one]
    refine ⟨z, b, hb, hw, adjointQuadratic_of_linked _ _ (extendRoot_additive hxa)
      (by rw [hz]; exact rescale_additive _ (extendRoot_additive hya))
      (fibreCocharacter t (coroot i)) (fun g v => fibreCocharacter_natural t (coroot i) g v)
      hw (fibrePositiveScalar i hxw) (fun S u v => ?_) (b : K) ((1 : K) ⊗ₜ[R] a)⟩
    rw [hz, evaluate_rescale, evaluate_rescale, fibreNegativeScalar i hyw, mul_left_comm]
  obtain ⟨r, hr⟩ := integral_opposite_scale x y a ha (fun K _ _ _ => by
    obtain ⟨z, b, hb, _, hq⟩ := fibre K
    exact ⟨z, b, hb, hq⟩)
  obtain ⟨z, b, hb, hw, hq⟩ := fibre K₀
  refine ⟨r⁻¹, linked_of_generic hinj i _ _ ?_⟩
  have hscale : algebraMap R K₀ (↑r⁻¹ : R) * (b : K₀) = 1 := by
    rw [← hr K₀ z b hb hq, ← map_mul, Units.inv_mul, map_one]
  rw [extendRoot_rescale, hb, rescale_rescale, hscale, rescale_one]
  exact hw

end IntegralNormalization

section WeylTransport

open LinearAlgebraicGroups.Specs.IntegralCentralQuotient (cocharacterEval)

set_option maxHeartbeats 1800000
set_option maxRecDepth 1500
set_option linter.style.haveILetI false

open LinearAlgebraicGroups.Specs.IntegralCentralQuotient (RootScalarAction)

variable {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
variable {D E : BasedRootDatum.{u}} {t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X)}

private def reflectCharacters (j : D.I) : Multiplicative D.X ≃* Multiplicative D.X :=
  (D.datum.reflection j).toAddEquiv.toMultiplicative

private theorem reflectCharacters_formula (j : D.I) (χ : Multiplicative D.X) :
    reflectCharacters j χ =
      (Multiplicative.ofAdd (D.datum.root j)) ^ (-(coroot j χ).toAdd) * χ := by
  apply Multiplicative.toAdd.injective
  change D.datum.reflection j χ.toAdd = -(coroot j χ).toAdd • D.datum.root j + χ.toAdd
  rw [RootPairing.reflection_apply, sub_eq_add_neg, neg_zsmul, add_comm]
  rfl

private def reflectTorusPoint (j : D.I) (S : CommAlgCat.{u} R)
    (s : MonoidAlgebra R (Multiplicative D.X) →ₐ[R] S) :
    MonoidAlgebra R (Multiplicative D.X) →ₐ[R] S :=
  s.comp (MonoidAlgebra.mapDomainBialgHom R (reflectCharacters j).toMonoidHom).toAlgHom

private theorem reflectTorusPoint_monomial (j : D.I) (S : CommAlgCat.{u} R)
    (s : MonoidAlgebra R (Multiplicative D.X) →ₐ[R] S) (χ : Multiplicative D.X) :
    reflectTorusPoint j S s (MonoidAlgebra.of R _ χ) =
      s (MonoidAlgebra.of R _ (reflectCharacters j χ)) := by
  simp [reflectTorusPoint, MonoidAlgebra.of_apply, MonoidAlgebra.mapDomainBialgHom_single]

private theorem reflectTorusPoint_twice (j : D.I) (S : CommAlgCat.{u} R)
    (s : MonoidAlgebra R (Multiplicative D.X) →ₐ[R] S) :
    reflectTorusPoint j S (reflectTorusPoint j S s) = s := by
  apply MonoidAlgebra.algHom_ext
  · intro χ
    change reflectTorusPoint j S (reflectTorusPoint j S s) (MonoidAlgebra.of R _ χ) =
      s (MonoidAlgebra.of R _ χ)
    rw [reflectTorusPoint_monomial, reflectTorusPoint_monomial]
    congr 2
    exact D.datum.reflection_same j χ.toAdd
  · exact Subsingleton.elim _ _

private theorem linkedWord_reflection (j : D.I) {x y : A →ₐ[R] Polynomial R}
    (h : IsLinked t j x y)
    (hx : RootScalarAction t x (Multiplicative.ofAdd (D.datum.root j)))
    (hy : RootScalarAction t y (Multiplicative.ofAdd (D.datum.root (D.datum.reflectionPerm j j))))
    (S : CommAlgCat.{u} R) (s : MonoidAlgebra R (Multiplicative D.X) →ₐ[R] S) :
    let n := rankOneWord x y (1 : Sˣ)
    n * mapGroup t (toConv s) * n⁻¹ = mapGroup t (toConv (reflectTorusPoint j S s)) := by
  dsimp only
  have hn := linkedWord_conjugatesTorus t j h hx hy S s
  dsimp only at hn
  change rankOneWord x y (1 : Sˣ) * toConv (s.comp t.toAlgHom) * (rankOneWord x y (1 : Sˣ))⁻¹ = _
  rw [hn]
  let v := (s.toMonoidHom.comp (MonoidAlgebra.of R _)).toHomUnits
  let a := v (Multiplicative.ofAdd (D.datum.root j))
  change (cocharacterPoint t (coroot j) S a)⁻¹ * mapGroup t (toConv s) = _
  rw [← map_inv]
  change mapGroup t (toConv (cocharacterEval (coroot j) S a⁻¹)) * mapGroup t (toConv s) = _
  rw [← map_mul]
  congr 1
  apply torusPoint_ext
  intro χ
  rw [conv_monomial]
  change cocharacterEval (coroot j) S a⁻¹ (MonoidAlgebra.of R _ χ) * s (MonoidAlgebra.of R _ χ) =
    reflectTorusPoint j S s (MonoidAlgebra.of R _ χ)
  rw [cocharacterEval_monomial, inv_zpow, ← zpow_neg, reflectTorusPoint_monomial,
    reflectCharacters_formula]
  change (↑(a ^ (-(coroot j χ).toAdd)) : S) * (v χ : S) =
    (v ((Multiplicative.ofAdd (D.datum.root j)) ^ (-(coroot j χ).toAdd) * χ) : S)
  rw [map_mul, map_zpow, Units.val_mul]

private theorem conjugate_scalar (j i : D.I) {x y z : A →ₐ[R] Polynomial R}
    (hl : IsLinked t j x y)
    (hx : RootScalarAction t x (Multiplicative.ofAdd (D.datum.root j)))
    (hy : RootScalarAction t y (Multiplicative.ofAdd (D.datum.root (D.datum.reflectionPerm j j))))
    (hz : RootScalarAction t z (Multiplicative.ofAdd (D.datum.root i))) :
    RootScalarAction t (conjugateCoordinate (rankOneWord x y (1 : Rˣ)) z)
      (Multiplicative.ofAdd (D.datum.root (D.datum.reflectionPerm j i))) := by
  intro S a s
  let n := rankOneWord x y (1 : Sˣ)
  let g := mapGroup t (toConv s)
  let s' := reflectTorusPoint j S s
  let g' := mapGroup t (toConv s')
  have he : mapPoint (Algebra.ofId R S) (rankOneWord x y (1 : Rˣ)) = n := by
    rw [onWord_natural, map_one]
  have hg : n * g' * n⁻¹ = g := by
    have h := linkedWord_reflection j hl hx hy S s'
    dsimp only at h
    rwa [show reflectTorusPoint j S s' = s from reflectTorusPoint_twice j S s] at h
  have e := hz S a s'
  change g' * evaluate z a * (g')⁻¹ = evaluate z (s' (MonoidAlgebra.of R _
    (Multiplicative.ofAdd (D.datum.root i))) * a) at e
  rw [reflectTorusPoint_monomial] at e
  have er : reflectCharacters j (Multiplicative.ofAdd (D.datum.root i)) =
      Multiplicative.ofAdd (D.datum.root (D.datum.reflectionPerm j i)) :=
    congrArg Multiplicative.ofAdd (D.datum.root_reflectionPerm j i).symm
  rw [er] at e
  change g * evaluate (conjugateCoordinate (rankOneWord x y (1 : Rˣ)) z) a * g⁻¹ =
    evaluate (conjugateCoordinate (rankOneWord x y (1 : Rˣ)) z)
      (s (MonoidAlgebra.of R _ (Multiplicative.ofAdd (D.datum.root (D.datum.reflectionPerm j i)))) * a)
  simp only [evaluate_conjugate, he]
  calc
    _ = n * (g' * evaluate z a * (g')⁻¹) * n⁻¹ := by rw [← hg]; group
    _ = _ := by rw [e]

private def transportCoordinate (x : D.I → A →ₐ[R] Polynomial R)
    (w : List ↥D.base.support) (i : D.I) : A →ₐ[R] Polynomial R :=
  w.foldr (fun j z => conjugateCoordinate
    (rankOneWord (x j.val) (x (D.datum.reflectionPerm j.val j.val)) (1 : Rˣ)) z) (x i)

private theorem transport_evaluate (x : D.I → A →ₐ[R] Polynomial R)
    (w : List ↥D.base.support) (i : D.I) (S : CommAlgCat.{u} R) (a : S) :
    evaluate (transportCoordinate x w i) a =
      evaluateWord x w S * evaluate (x i) a * (evaluateWord x w S)⁻¹ := by
  induction w with
  | nil => simp [transportCoordinate, evaluateWord]
  | cons j w ih =>
    let n := rankOneWord (x j.val) (x (D.datum.reflectionPerm j.val j.val)) (1 : Sˣ)
    change evaluate (conjugateCoordinate
      (rankOneWord (x j.val) (x (D.datum.reflectionPerm j.val j.val)) (1 : Rˣ))
      (transportCoordinate x w i)) a =
      (n * evaluateWord x w S) * evaluate (x i) a * (n * evaluateWord x w S)⁻¹
    rw [evaluate_conjugate, onWord_natural, map_one, ih]
    change n * _ * n⁻¹ = _
    group

private theorem transport_properties {x : D.I → A →ₐ[R] Polynomial R}
    (h : ∀ i, Function.Surjective (x i) ∧ IsAdditive (x i) ∧
      RootScalarAction t (x i) (Multiplicative.ofAdd (D.datum.root i)))
    (hl : ∀ j : ↥D.base.support, IsLinked t j.val (x j.val) (x (D.datum.reflectionPerm j.val j.val)))
    (w : List ↥D.base.support) (i : D.I) :
    Function.Surjective (transportCoordinate x w i) ∧ IsAdditive (transportCoordinate x w i) ∧
      RootScalarAction t (transportCoordinate x w i)
        (Multiplicative.ofAdd (D.datum.root (reflectWord w i))) := by
  induction w with
  | nil => exact h i
  | cons j w ih =>
    exact ⟨conjugate_surjective _ ih.1, conjugate_additive _ ih.2.1,
      conjugate_scalar j.val (reflectWord w i) (hl j) (h j.val).2.2
        (h (D.datum.reflectionPerm j.val j.val)).2.2 ih.2.2⟩

private theorem polynomial_extend_apply {K : Type u} [Field K] [Algebra R K]
    (x : A →ₐ[R] Polynomial R) (a : A) :
    extendRoot (K := K) x ((1 : K) ⊗ₜ[R] a) = (x a).map (algebraMap R K) := by
  simp [extendRoot]

private theorem rescale_coeff_one (r : R) (x : A →ₐ[R] Polynomial R) (a : A) :
    (rescaleCoordinate r x a).coeff 1 = (x a).coeff 1 * r := by
  change (Polynomial.aeval (Polynomial.C r * Polynomial.X) (x a)).coeff 1 = _
  rw [← Polynomial.comp_eq_aeval, Polynomial.comp_C_mul_X_coeff, pow_one]

private theorem integral_eq_unitRescale {K : Type u} [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) {x y : A →ₐ[R] Polynomial R}
    (hx : Function.Surjective x) (hy : Function.Surjective y)
    (c : K) (hc : extendRoot (K := K) x = rescaleCoordinate c (extendRoot (K := K) y)) :
    ∃ r : Rˣ, x = rescaleCoordinate (r : R) y := by
  obtain ⟨a, ha⟩ := hy Polynomial.X
  obtain ⟨b, hb⟩ := hx Polynomial.X
  have coeff (d : A) : algebraMap R K ((x d).coeff 1) = algebraMap R K ((y d).coeff 1) * c := by
    have h := congrArg (fun f : K ⊗[R] A →ₐ[K] Polynomial K => (f ((1 : K) ⊗ₜ[R] d)).coeff 1) hc
    simpa only [rescale_coeff_one, polynomial_extend_apply, Polynomial.coeff_map] using h
  let r := (x a).coeff 1
  have hr : algebraMap R K r = c := by simpa only [r, ha, Polynomial.coeff_X_one, map_one, one_mul] using coeff a
  have hmul : r * (y b).coeff 1 = 1 := by
    apply hinj
    calc
      algebraMap R K (r * (y b).coeff 1) = algebraMap R K ((y b).coeff 1) * c := by
        rw [map_mul, hr, mul_comm]
      _ = algebraMap R K ((x b).coeff 1) := (coeff b).symm
      _ = algebraMap R K 1 := by rw [hb, Polynomial.coeff_X_one]
  let v := Units.mkOfMulEqOne r ((y b).coeff 1) hmul
  refine ⟨v, AlgHom.ext fun d => ?_⟩
  apply Polynomial.map_injective _ hinj
  rw [← polynomial_extend_apply, ← polynomial_extend_apply, extendRoot_rescale]
  exact DFunLike.congr_fun (by rw [hc, show algebraMap R K (v : R) = c from hr]) _

private theorem rootCoordinates_of_rescales {pin : ↥D.base.support → Tangent R A}
    {x y : D.I → A →ₐ[R] Polynomial R} (hx : RootCoordinates t pin x)
    (hs : ∀ i, ∃ c : Rˣ, y i = rescaleCoordinate (c : R) (x i))
    (hp : ∀ i : ↥D.base.support, y i.val = x i.val) :
    RootCoordinates t pin y := by
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · obtain ⟨c, hc⟩ := hs i
    rw [hc]
    exact ⟨rescale_surjective c (hx.1 i).1, rescale_additive _ (hx.1 i).2.1,
      rescale_scalar _ (hx.1 i).2.2⟩
  · rw [hp i]
    exact hx.2.1 i
  · intro K _ _ _
    obtain ⟨F, hF⟩ := hx.2.2 K
    refine ⟨F, fun i => ?_⟩
    obtain ⟨c, hc⟩ := hs i
    rw [hc]
    exact fibreCoordinate_rescale F i (hF i) c

private theorem opposite_injective (D : BasedRootDatum.{u}) :
    Function.Injective (fun i : D.I => D.datum.reflectionPerm i i) := by
  intro i j e
  apply D.datum.root.injective
  exact neg_injective (by simpa only [RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_self] using congrArg D.datum.root e)

private theorem opposite_not_simple {i : D.I} (hi : i ∈ D.base.support) :
    D.datum.reflectionPerm i i ∉ D.base.support := by
  intro h
  have e := D.base.height_reflectionPerm_self i
  change D.base.height (D.datum.reflectionPerm i i) = -D.base.height i at e
  rw [D.base.height_one_of_mem_support hi, D.base.height_one_of_mem_support h] at e
  norm_num at e

private theorem evaluateWord_eq_of_agree
    {x y : D.I → A →ₐ[R] Polynomial R}
    (hp : ∀ j : ↥D.base.support, x j.val = y j.val)
    (hn : ∀ j : ↥D.base.support,
      x (D.datum.reflectionPerm j.val j.val) = y (D.datum.reflectionPerm j.val j.val))
    (S : CommAlgCat.{u} R) (l : List ↥D.base.support) :
    evaluateWord x l S = evaluateWord y l S := by
  have h :
      (fun j : ↥D.base.support => rankOneWord (x j.val)
        (x (D.datum.reflectionPerm j.val j.val)) (1 : Sˣ)) =
      (fun j : ↥D.base.support => rankOneWord (y j.val)
        (y (D.datum.reflectionPerm j.val j.val)) (1 : Sˣ)) := by
    funext j
    rw [hp j, hn j]
  exact congrArg (fun f : ↥D.base.support → HopfPoints R A S => (l.map f).prod) h

private theorem linkedFamily [IsDomain R] {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    [Algebra R K] (hinj : Function.Injective (algebraMap R K))
    {p : ↥D.base.support → Tangent R A} {x : D.I → A →ₐ[R] Polynomial R}
    (hx : RootCoordinates t p x) (w : D.I → RootWord D)
    (hw : ∀ i, reflectWord (w i).word (w i).start = i)
    (hpos : ∀ i ∈ D.base.support, (w i).word = [])
    (hneg : ∀ i ∈ D.base.support, (w (D.datum.reflectionPerm i i)).word = []) :
    ∃ z : D.I → A →ₐ[R] Polynomial R,
      RootCoordinates t p z ∧
      (∀ i : ↥D.base.support, z i.val = x i.val ∧
        IsLinked t i.val (z i.val) (z (D.datum.reflectionPerm i.val i.val))) ∧
      UsesWords z w := by
  classical
  let neg (i : D.I) := D.datum.reflectionPerm i i
  have hscale (i : ↥D.base.support) :
      ∃ c : Rˣ, IsLinked t i.val (x i.val) (rescaleCoordinate (c : R) (x (neg i.val))) :=
    normalizeOpposite hinj i.val (hx.1 i.val).1 (hx.1 i.val).2.1 (hx.1 (neg i.val)).2.1
      (hx.1 i.val).2.2 (hx.1 (neg i.val)).2.2 (fun L _ _ _ => by
        obtain ⟨F, hF⟩ := hx.2.2 L
        exact ⟨F, hF _, hF _⟩)
  choose c hc using hscale
  let seed (i : D.I) := if h : ∃ j : ↥D.base.support, neg j.val = i then
    rescaleCoordinate (c (Classical.choose h) : R) (x i) else x i
  have hseed_pos (i : ↥D.base.support) : seed i.val = x i.val := by
    apply dif_neg
    rintro ⟨j, hj⟩
    apply opposite_not_simple j.property
    change neg j.val ∈ D.base.support
    rw [hj]
    exact i.property
  have hseed_neg (i : ↥D.base.support) :
      seed (neg i.val) = rescaleCoordinate (c i : R) (x (neg i.val)) := by
    have h : ∃ j : ↥D.base.support, neg j.val = neg i.val := ⟨i, rfl⟩
    rw [show seed (neg i.val) = _ from dif_pos h]
    have e : Classical.choose h = i := Subtype.ext (opposite_injective D (Classical.choose_spec h))
    rw [e]
  have hseed : RootCoordinates t p seed := by
    apply rootCoordinates_of_rescales hx _ hseed_pos
    intro i
    by_cases h : ∃ j : ↥D.base.support, neg j.val = i
    · exact ⟨c (Classical.choose h), dif_pos h⟩
    · exact ⟨1, (dif_neg h).trans (rescale_one (x i)).symm⟩
  have hlinked (i : ↥D.base.support) :
      IsLinked t i.val (seed i.val) (seed (neg i.val)) := by
    rw [hseed_pos, hseed_neg]
    exact hc i
  let z (i : D.I) := transportCoordinate seed (w i).word (w i).start
  have hz_props (i : D.I) := transport_properties hseed.1 hlinked (w i).word (w i).start
  have seed_eq (i : D.I) (h : (w i).word = []) : z i = seed i := by
    have e := hw i
    rw [h] at e
    change (w i).start = i at e
    change transportCoordinate seed (w i).word (w i).start = seed i
    rw [h, e]
    rfl
  have hz_pos (i : ↥D.base.support) : z i.val = x i.val :=
    (seed_eq i.val (hpos i.val i.property)).trans (hseed_pos i)
  have hz_neg (i : ↥D.base.support) : z (neg i.val) = seed (neg i.val) :=
    seed_eq _ (hneg i.val i.property)
  have hz : RootCoordinates t p z := by
    obtain ⟨F, hF⟩ := hx.2.2 K
    apply rootCoordinates_of_rescales hx _ hz_pos
    intro i
    have he := (hz_props i).2.2
    rw [hw i] at he
    obtain ⟨b, hb⟩ := fibre_eq_rescale F i (hF i) (hx.1 i).2.1
      (extendRoot_additive (hz_props i).2.1) (extendRoot_scalar he)
    exact integral_eq_unitRescale hinj (hz_props i).1 (hx.1 i).1 b hb
  refine ⟨z, hz, fun i => ⟨hz_pos i, ?_⟩, fun i => ⟨hw i, fun S a => ?_⟩⟩
  · rw [hz_pos, hz_neg, ← hseed_pos i]
    exact hlinked i
  have word_eq (l : List ↥D.base.support) : evaluateWord seed l S = evaluateWord z l S :=
    evaluateWord_eq_of_agree (fun j => (hseed_pos j).trans (hz_pos j).symm)
      (fun j => (hz_neg j).symm) S l
  have start_eq : seed (w i).start = z (w i).start := by
    unfold RootWord.start
    split
    · exact (hz_neg (w i).simple).symm
    · exact (hseed_pos (w i).simple).trans (hz_pos (w i).simple).symm
  exact (transport_evaluate seed (w i).word (w i).start S a).trans (by rw [word_eq, start_eq])

end WeylTransport

section GenericComparison

set_option maxHeartbeats 1800000
set_option maxRecDepth 1500
set_option linter.style.haveILetI false

open LinearAlgebraicGroups.Specs.IntegralCentralQuotient (RootScalarAction)

variable {R K A B : Type u} [CommRing R] [Field K] [Algebra R K]
  [CommRing A] [CommRing B] [HopfAlgebra R A] [HopfAlgebra R B]

private theorem actsBy_comp_of_injective {k C D H J : Type u}
    [CommRing k] [CommRing C] [CommRing D] [CommRing H] [CommRing J]
    [HopfAlgebra k C] [HopfAlgebra k D] [HopfAlgebra k H] [HopfAlgebra k J]
    (t : C →ₐc[k] H) (s : D →ₐc[k] J) (f : D →ₐc[k] C)
    (g : J →ₐc[k] H) (hg : Function.Injective g) (ht : t.comp f = g.comp s)
    {m : H} {m' : J} (hm : g m' = m) {x : C →ₐ[k] Polynomial k} (hx : ActsBy t m x) :
    ActsBy s m' (x.comp f.toAlgHom) := by
  let U := CommAlgCat.of k (Polynomial J)
  let V := CommAlgCat.of k (Polynomial H)
  let c : J →ₐ[k] U := Polynomial.CAlgHom
  let d : H →ₐ[k] V := Polynomial.CAlgHom
  let e : U →ₐ[k] V := Polynomial.mapAlgHom g.toAlgHom
  have hX : e Polynomial.X = Polynomial.X := Polynomial.map_X _
  have he : e.comp c = d.comp g.toAlgHom := by
    apply AlgHom.ext
    intro a
    exact Polynomial.map_C g.toAlgHom.toRingHom
  have ht' {S : Type u} [CommRing S] [Algebra k S] (p : H →ₐ[k] S) :
      mapGroup f (mapGroup t (toConv p)) = mapGroup s (toConv (p.comp g.toAlgHom)) := by
    apply WithConv.ext
    ext b
    exact congrArg p (DFunLike.congr_fun ht b)
  have h := congrArg (mapGroup f) (hx V Polynomial.X d)
  simp only [map_mul, map_inv, ht', evaluate_compGroup] at h
  rw [← he, ← hm, ← hX] at h
  have h₀ : mapGroup s (toConv c) * evaluate (x.comp f.toAlgHom) (Polynomial.X : U) *
      (mapGroup s (toConv c))⁻¹ = evaluate (x.comp f.toAlgHom) (c m' * Polynomial.X) := by
    have h₁ : Function.Injective (mapPoint (A := D) e) := by
      intro p q hpq
      apply WithConv.ext
      apply AlgHom.ext
      intro b
      exact (Polynomial.map_injective _ hg) (congrArg (fun u : HopfPoints k D V => u.ofConv b) hpq)
    apply h₁
    simp only [map_mul, map_inv, evaluate_natural]
    have hu : mapPoint e (mapGroup s (toConv c)) = mapGroup s (toConv (e.comp c)) := rfl
    have hm' : e (c m') = d (g m') := DFunLike.congr_fun he m'
    rw [hu, hm']
    exact h
  intro S b p
  let ψ : U →ₐ[k] S := Polynomial.eval₂AlgHom p b (fun _ => Commute.all _ _)
  have hψ : ψ.comp c = p := by
    ext a
    exact Polynomial.eval₂_C _ _
  have hψX : ψ Polynomial.X = b := Polynomial.eval₂_X _ _
  have h₁ := congrArg (mapPoint ψ) h₀
  have hu : mapPoint ψ (mapGroup s (toConv c)) = mapGroup s (toConv p) := by
    change mapGroup s (toConv (ψ.comp c)) = _
    rw [hψ]
  have hb' : ψ (c m') = p m' := DFunLike.congr_fun hψ m'
  simp only [map_mul, map_inv, evaluate_natural, hψX, hu, hb'] at h₁
  exact h₁

private theorem extendTorusMap_injective
    {X Y : Type u} [CommGroup X] [CommGroup Y] (h : Y →* X)
    (hh : Function.Injective h) :
    Function.Injective (extendBialg (K := K) (MonoidAlgebra.mapDomainBialgHom R h)) := by
  let m := extendBialg (K := K) (MonoidAlgebra.mapDomainBialgHom R h)
  let ex := MonoidAlgebra.scalarTensorEquiv (M := X) R K
  let ey := MonoidAlgebra.scalarTensorEquiv (M := Y) R K
  let g := MonoidAlgebra.mapDomainBialgHom K h
  have e : ex.toAlgHom.comp m.toAlgHom = g.toAlgHom.comp ey.toAlgHom := by
    apply (AlgHom.liftEquiv R K (MonoidAlgebra R Y) (MonoidAlgebra K X)).symm.injective
    apply MonoidAlgebra.algHom_ext
    · intro y
      change ex (m (1 ⊗ₜ[R] MonoidAlgebra.single y 1)) = g (ey (1 ⊗ₜ[R] MonoidAlgebra.single y 1))
      simp [m, ex, ey, g, Bialgebra.TensorProduct.map_tmul, MonoidAlgebra.mapDomainBialgHom_single]
    · exact Subsingleton.elim _ _
  intro a b hab
  apply ey.injective
  apply MonoidAlgebra.mapDomain_injective (R := K) hh
  change g (ey a) = g (ey b)
  exact (DFunLike.congr_fun e a).symm.trans ((congrArg ex hab).trans (DFunLike.congr_fun e b))

private theorem fibreActsBy_comp {X Y : Type u} [CommGroup X] [CommGroup Y]
    (t : A →ₐc[R] MonoidAlgebra R X) (s : B →ₐc[R] MonoidAlgebra R Y)
    (f : K ⊗[R] B →ₐc[K] K ⊗[R] A) (h : Y →* X) (hinj : Function.Injective h)
    (ht : (fibreTorusInclusion (K := K) (X := X) t).comp f =
      (extendBialg (K := K) (MonoidAlgebra.mapDomainBialgHom R h)).comp
        (fibreTorusInclusion (K := K) (X := Y) s))
    {m : X} {m' : Y} (hm : h m' = m) {x : K ⊗[R] A →ₐ[K] Polynomial K}
    (hx : FibreActsBy t m x) : FibreActsBy s m' (x.comp f.toAlgHom) := by
  let tK := fibreTorusInclusion (K := K) (X := X) t
  let sK := fibreTorusInclusion (K := K) (X := Y) s
  let g : K ⊗[R] MonoidAlgebra R Y →ₐc[K] K ⊗[R] MonoidAlgebra R X :=
    Bialgebra.TensorProduct.map (BialgHom.id K K) (MonoidAlgebra.mapDomainBialgHom R h)
  let b := (1 : K) ⊗ₜ[R] MonoidAlgebra.of R X m
  let b' := (1 : K) ⊗ₜ[R] MonoidAlgebra.of R Y m'
  have hmonomial : g b' = b := by
    simp only [g, b, b', extendBialg, Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply,
      MonoidAlgebra.of_apply, MonoidAlgebra.mapDomainBialgHom_single, hm]
  change ActsBy (R := K) (A := K ⊗[R] A) (C := K ⊗[R] MonoidAlgebra R X) tK b x at hx
  change ActsBy (R := K) (A := K ⊗[R] B) (C := K ⊗[R] MonoidAlgebra R Y) sK b' (x.comp f.toAlgHom)
  exact actsBy_comp_of_injective (k := K) (C := K ⊗[R] A) (D := K ⊗[R] B)
    (H := K ⊗[R] MonoidAlgebra R X) (J := K ⊗[R] MonoidAlgebra R Y) tK sK f g
    (extendTorusMap_injective (R := R) h hinj) ht hmonomial hx

private theorem additive_comp {k C D : Type u} [CommRing k] [CommRing C] [CommRing D]
    [HopfAlgebra k C] [HopfAlgebra k D] (f : D →ₐc[k] C)
    {x : C →ₐ[k] Polynomial k} (h : IsAdditive x) : IsAdditive (x.comp f.toAlgHom) := by
  intro S
  refine ⟨?_, fun a b => ?_⟩
  · rw [← evaluate_compGroup, (h S).1, map_one]
  · rw [← evaluate_compGroup, ← evaluate_compGroup, ← evaluate_compGroup, (h S).2, map_mul]

private theorem evaluate_extended_tangent (x : A →ₐ[R] Polynomial R) (a : A) :
    (evaluate (extendRoot (K := K) x) (DualNumber.eps : DualNumber K)).ofConv ((1 : K) ⊗ₜ[R] a) =
      dualCoefficients K ((evaluate x (DualNumber.eps : DualNumber R)).ofConv a) := by
  let m := Polynomial.mapAlgHom (Algebra.ofId R K)
  have e : ((Polynomial.aeval (DualNumber.eps : DualNumber K)).restrictScalars R).comp m =
      (dualCoefficients K).comp (Polynomial.aeval (DualNumber.eps : DualNumber R)) := by
    apply Polynomial.algHom_ext
    change Polynomial.aeval (DualNumber.eps : DualNumber K) (m Polynomial.X) =
      dualCoefficients K (Polynomial.aeval (DualNumber.eps : DualNumber R) Polynomial.X)
    rw [show m Polynomial.X = Polynomial.X from Polynomial.map_X _, Polynomial.aeval_X,
      Polynomial.aeval_X]
    apply TrivSqZeroExt.ext
    · exact (map_zero (algebraMap R K)).symm
    · exact (map_one (algebraMap R K)).symm
  change Polynomial.aeval (DualNumber.eps : DualNumber K) (extendRoot (K := K) x (1 ⊗ₜ[R] a)) =
    dualCoefficients K (Polynomial.aeval (DualNumber.eps : DualNumber R) (x a))
  rw [polynomial_extend_apply]
  exact DFunLike.congr_fun e (x a)

private theorem extend_usesWords {D : BasedRootDatum.{u}}
    {x : D.I → A →ₐ[R] Polynomial R} {w : D.I → RootWord D} (h : UsesWords x w) :
    UsesWords (fun i => extendRoot (K := K) (x i)) w := by
  intro i
  refine ⟨(h i).1, fun S a => ?_⟩
  letI : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq' rfl
  have he (l : List ↥D.base.support) :
      restrictPoint (R := R) (evaluateWord (fun i => extendRoot (K := K) (x i)) l S) =
        evaluateWord x l (CommAlgCat.of R S) := by
    induction l with
    | nil => exact map_one _
    | cons j l ih =>
      simp only [evaluateWord, List.map_cons, List.prod_cons, rankOneWord, map_mul, restrict_evaluate]
      simp only [evaluateWord, rankOneWord, List.map_cons, List.prod_cons] at ih
      rw [ih]
  apply restrictPoint_injective (R := R)
  simp only [map_mul, map_inv, restrict_evaluate, he]
  exact (h i).2 (CommAlgCat.of R S) a

private theorem linkedQuadratic {D : BasedRootDatum.{u}} {t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X)}
    (i : D.I) {x y : A →ₐ[R] Polynomial R} (hx : IsAdditive x) (hy : IsAdditive y)
    (hxw : RootScalarAction t x (Multiplicative.ofAdd (D.datum.root i)))
    (hyw : RootScalarAction t y (Multiplicative.ofAdd (D.datum.root (D.datum.reflectionPerm i i))))
    (hl : IsLinked t i x y) (c : K) (a : K ⊗[R] A) :
    adjointQuadratic (extendRoot (K := K) x) (extendRoot (K := K) y) c a =
      -c * ((extendRoot (K := K) x) a).coeff 1 :=
  adjointQuadratic_of_linked _ _ (extendRoot_additive hx) (extendRoot_additive hy)
    (fibreCocharacter t (coroot i)) (fun g v => fibreCocharacter_natural t (coroot i) g v)
    (fibreWord_restrict i hl) (fibrePositiveScalar i hxw) (fibreNegativeScalar i hyw) c a

private theorem matchLinkedFamily [CharZero K]
    {D E : BasedRootDatum.{u}} {t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X)}
    {s : B →ₐc[R] MonoidAlgebra R (Multiplicative E.X)}
    {p : ↥D.base.support → Tangent R A} {q : ↥E.base.support → Tangent R B}
    (h : LatticeMap D E) {x : D.I → A →ₐ[R] Polynomial R} {y : E.I → B →ₐ[R] Polynomial R}
    (hx : RootCoordinates t p x) (hy : RootCoordinates s q y)
    (hl : ∀ i : ↥D.base.support, IsLinked t i.val (x i.val) (x (D.datum.reflectionPerm i.val i.val)))
    (hm : ∀ j : ↥E.base.support, IsLinked s j.val (y j.val) (y (E.datum.reflectionPerm j.val j.val)))
    (w : D.I → RootWord D) (hw : UsesWords x w)
    (hv : UsesWords y (fun j => (w (h.roots.symm j)).map h))
    [IsAlgClosed K] (f : K ⊗[R] B →ₐc[K] K ⊗[R] A) (hf : GenericMarking t s p q h f) (i : D.I) :
    (extendRoot (K := K) (x i)).comp f.toAlgHom = extendRoot (K := K) (y (h.roots i)) := by
  let X j := extendRoot (K := K) (x j)
  let Y j := extendRoot (K := K) (y j)
  have positive (j : ↥D.base.support) : (X j.val).comp f.toAlgHom = Y (h.roots j.val) := by
    apply additiveCoordinates_eq_of_tangent (additive_comp f (extendRoot_additive (hx.1 j.val).2.1))
      (extendRoot_additive (hy.1 (h.roots j.val)).2.1)
    have he : evaluate (X j.val) (DualNumber.eps : DualNumber K) =
      toConv (extendTangent (K := K) (p j)) := by
      apply WithConv.ext
      apply (AlgHom.liftEquiv R K A (DualNumber K)).symm.injective
      apply AlgHom.ext
      intro a
      simp only [ofConv_toConv, AlgHom.liftEquiv_symm_apply]
      rw [evaluate_extended_tangent, hx.2.1 j]
      simp [extendTangent]
    rw [← evaluate_compGroup, he]
    apply WithConv.ext
    apply (AlgHom.liftEquiv R K B (DualNumber K)).symm.injective
    apply AlgHom.ext
    intro b
    change (extendTangent (K := K) (p j)) (f ((1 : K) ⊗ₜ[R] b)) =
      (evaluate (Y (h.roots j.val)) (DualNumber.eps : DualNumber K)).ofConv ((1 : K) ⊗ₜ[R] b)
    have hp : (evaluate (y (h.roots j.val)) (DualNumber.eps : DualNumber R)).ofConv =
        (q (h.simple j)).val := hy.2.1 (h.simple j)
    rw [evaluate_extended_tangent, hp]
    exact hf.2 j b

  obtain ⟨F, hF⟩ := hy.2.2 K
  have negative (j : ↥D.base.support) :
      (X (D.datum.reflectionPerm j.val j.val)).comp f.toAlgHom =
        Y (E.datum.reflectionPerm (h.roots j.val) (h.roots j.val)) := by
    let a := D.datum.reflectionPerm j.val j.val
    let b := E.datum.reflectionPerm (h.roots j.val) (h.roots j.val)
    have hb : h.roots a = b := mapReflection h j.val j.val
    have hmonomial : h.characters (Multiplicative.ofAdd (E.datum.root b)) =
        Multiplicative.ofAdd (D.datum.root a) := by
      rw [← hb]
      exact h.root_eq a
    have hsrc : FibreActsBy (X := Multiplicative D.X) t
        (Multiplicative.ofAdd (D.datum.root a)) (X a) := extendRoot_scalar (hx.1 a).2.2
    have eq : FibreActsBy (X := Multiplicative E.X) s
        (Multiplicative.ofAdd (E.datum.root b)) ((X a).comp f.toAlgHom) :=
      fibreActsBy_comp (X := Multiplicative D.X) (Y := Multiplicative E.X)
        t s f h.characters h.injective hf.1 hmonomial hsrc
    obtain ⟨c, hc⟩ := fibre_eq_rescale F b (hF b) (hy.1 b).2.1
      (additive_comp f (extendRoot_additive (hx.1 a).2.1)) eq
    exact matchNegative_of_quadratic f (X j.val) (X a) (Y (h.roots j.val)) (Y b)
      (positive j) (extendRoot_surjective (hy.1 (h.roots j.val)).1) c hc
      (fun d => by
        simpa only [neg_one_mul] using linkedQuadratic j.val (hx.1 j.val).2.1 (hx.1 a).2.1
          (hx.1 j.val).2.2 (hx.1 a).2.2 (hl j) (1 : K) d)
      (fun d => linkedQuadratic (h.roots j.val) (hy.1 (h.roots j.val)).2.1 (hy.1 b).2.1
        (hy.1 (h.roots j.val)).2.2 (hy.1 b).2.2 (hm (h.simple j)) c d)
  let S := CommAlgCat.of K (Polynomial K)
  apply coordinate_ext
  rw [← evaluate_compGroup]
  exact matchTransportedCoordinates h S X Y w (extend_usesWords hw) (extend_usesWords hv)
    (mapGroup f) (fun j a => by rw [evaluate_compGroup, positive])
    (fun j a => by rw [evaluate_compGroup, negative]) i Polynomial.X

end GenericComparison

open LinearAlgebraicGroups.Specs.IntegralCentralQuotient (IntegralRing)

/-- Normalize the negative simple coordinates and propagate the linked pairs
by corresponding Weyl words before choosing the generic lift. -/
theorem linkedCoordinates : Statement.{u} := by
  classical
  let R := IntegralRing.{u}
  letI : IsDomain R := (ULift.ringEquiv (R := ℤ)).toMulEquiv.isDomain ℤ
  let K₀ := AlgebraicClosure (FractionRing R)
  letI : Algebra R K₀ := ((algebraMap (FractionRing R) K₀).comp (algebraMap R (FractionRing R))).toAlgebra
  have hK₀ : Function.Injective (algebraMap R K₀) :=
    (algebraMap (FractionRing R) K₀).injective.comp (IsFractionRing.injective R (FractionRing R))
  letI : CharZero R := ⟨fun m n eq => Nat.cast_injective (R := ℤ) (congrArg ULift.down eq)⟩
  letI : CharZero K₀ := charZero_of_injective_algebraMap hK₀
  intro D E A B _ _ _ _ _ _ _ _ t s _ _ p q _ _ h x y hx hy
  obtain ⟨w, hw, hp, hn⟩ := chooseRootWords D
  let v (j : E.I) := (w (h.roots.symm j)).map h
  have hv (j : E.I) : reflectWord (v j).word (v j).start = j := by
    let k := h.roots.symm j
    change reflectWord ((w k).word.map h.simple) ((w k).map h).start = j
    rw [← mapRootWordStart, ← mapReflectWord, hw, Equiv.apply_symm_apply]
  have hvp (j : E.I) (hj : j ∈ E.base.support) : (v j).word = [] := by
    have e := (h.simple_iff (h.roots.symm j)).mp (by rwa [Equiv.apply_symm_apply])
    change (w (h.roots.symm j)).word.map h.simple = []
    rw [hp _ e]
    rfl
  have hvn (j : E.I) (hj : j ∈ E.base.support) :
      (v (E.datum.reflectionPerm j j)).word = [] := by
    let i := h.roots.symm j
    have hi : h.roots i = j := h.roots.apply_symm_apply j
    have e : i ∈ D.base.support := (h.simple_iff i).mp (hi.symm ▸ hj)
    have hidx : h.roots.symm (E.datum.reflectionPerm j j) = D.datum.reflectionPerm i i := by
      apply h.roots.injective
      rw [Equiv.apply_symm_apply, mapReflection, hi]
    change (w (h.roots.symm (E.datum.reflectionPerm j j))).word.map h.simple = []
    rw [hidx, hn _ e]
    rfl
  obtain ⟨x', hx', hxl, hxu⟩ := linkedFamily hK₀ hx w hw hp hn
  obtain ⟨y', hy', hyl, hyu⟩ := linkedFamily hK₀ hy v hv hvp hvn
  refine ⟨x', y', w, hx', hy', hxl, hyl, hxu, hyu, ?_⟩
  intro K _ _ _ _ f _ hf i
  exact matchLinkedFamily h hx' hy' (fun j => (hxl j).2) (fun j => (hyl j).2) w hxu hyu f hf i

end

end LinearAlgebraicGroups.Classification.IntegralLinkedRoots
