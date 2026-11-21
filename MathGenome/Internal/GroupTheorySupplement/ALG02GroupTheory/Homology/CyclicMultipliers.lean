import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Homology.CyclicMultipliers
import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Homology.HopfFormula
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.Ring
import Batteries.Tactic.OpenPrivate

namespace ALG02GroupTheory.CyclicMultipliers

open IntegralBar HopfFormula
open scoped commutatorElement
open private commute_relator_class from MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Homology.HopfFormula

noncomputable section

private abbrev Cyclic (m : ℕ) := Multiplicative (ZMod m)

private def generator (m : ℕ) : Cyclic m := Multiplicative.ofAdd 1

private theorem generator_pow (m k : ℕ) :
    generator m ^ k = Multiplicative.ofAdd (k : ZMod m) := by
  apply Multiplicative.toAdd.injective
  change k • (1 : ZMod m) = _
  simp

private theorem mem_zpowers_generator (m : ℕ) (a : Cyclic m) :
    a ∈ Subgroup.zpowers (generator m) := by
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective a.toAdd
  refine ⟨k, Multiplicative.toAdd.injective ?_⟩
  change k • (1 : ZMod m) = a.toAdd
  simpa using hk

private theorem orderOf_generator (m : ℕ) : orderOf (generator m) = m := by
  have hd (k : ℕ) : generator m ^ k = 1 ↔ m ∣ k := by
    rw [generator_pow]
    change Multiplicative.ofAdd (k : ZMod m) = Multiplicative.ofAdd 0 ↔ _
    rw [Multiplicative.ofAdd.injective.eq_iff, ZMod.natCast_eq_zero_iff]
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ((hd m).mpr dvd_rfl))
    ((hd _).mp (pow_orderOf_eq_one _))

private def kernelExtension {F G : Type} [Group F] [Group G] (p : F →* G)
    (hp : Function.Surjective p) : GroupExtension p.ker F G where
  inl := p.ker.subtype
  rightHom := p
  inl_injective := Subtype.val_injective
  range_inl_eq_ker_rightHom := Subgroup.range_subtype _
  rightHom_surjective := hp

private theorem commutator_le_ker {F G : Type} [Group F] [CommGroup G] (p : F →* G) :
    commutator F ≤ p.ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  exact MonoidHom.mem_ker.mpr (by rw [map_commutatorElement, (Commute.all _ _).commutator_eq])

theorem cyclic_vanishing : Specs.ALG02GroupTheory.CyclicMultipliers.CyclicVanishing := by
  intro m hm
  let p : FreeGroup Unit →* Cyclic m := FreeGroup.lift (fun _ => generator m)
  have hp : Function.Surjective p := by
    intro a
    obtain ⟨k, hk⟩ := mem_zpowers_generator m a
    refine ⟨FreeGroup.of () ^ k, ?_⟩
    rwa [map_zpow, FreeGroup.lift_apply_of]
  let S := kernelExtension p hp
  let : CommGroup (FreeGroup Unit) := IsCyclic.commGroup
  have hn : numerator S.inl.range = ⊥ := by
    rw [numerator, commutator_eq_bot, inf_bot_eq]
  have : Subsingleton (numerator S.inl.range) := by
    rw [hn]
    infer_instance
  have : Subsingleton (PresentationQuotient S.inl.range) :=
    QuotientGroup.mk'_surjective _ |>.subsingleton
  exact (hopfEquiv S).injective.subsingleton

private abbrev F := FreeGroup Bool

private def x : F := FreeGroup.of false
private def y : F := FreeGroup.of true

private def productPresentation (m n : ℕ) : F →* Cyclic m × Cyclic n :=
  FreeGroup.lift (fun b => if b then (1, generator n) else (generator m, 1))

@[simp] private theorem productPresentation_x (m n : ℕ) :
    productPresentation m n x = (generator m, 1) := by
  simp [productPresentation, x]

@[simp] private theorem productPresentation_y (m n : ℕ) :
    productPresentation m n y = (1, generator n) := by
  simp [productPresentation, y]

private theorem productPresentation_surjective (m n : ℕ) :
    Function.Surjective (productPresentation m n) := by
  rintro ⟨a, b⟩
  obtain ⟨i, hi⟩ := mem_zpowers_generator m a
  obtain ⟨j, hj⟩ := mem_zpowers_generator n b
  exact ⟨x ^ i * y ^ j, by simp [hi, hj]⟩

/-- Include the Hopf quotient into the ambient quotient by the same commutators. -/
private def intoAmbient {F : Type} [Group F] (R : Subgroup F) [R.Normal] :
    PresentationQuotient R →* F ⧸ denominator R :=
  let q := QuotientGroup.mk' (denominator R)
  QuotientGroup.lift _ (q.comp (numerator R).subtype) (fun a ha =>
    (QuotientGroup.eq_one_iff (a : F)).2 ha)

private theorem intoAmbient_injective {F : Type} [Group F] (R : Subgroup F) [R.Normal] :
    Function.Injective (intoAmbient R) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a
  induction a using QuotientGroup.induction_on with
  | _ a =>
    intro ha
    exact (QuotientGroup.eq_one_iff a).mpr
      ((QuotientGroup.eq_one_iff (a : F)).mp ha)

private theorem intoAmbient_range {F : Type} [Group F] (R : Subgroup F) [R.Normal]
    (hR : commutator F ≤ R) :
    (intoAmbient R).range = commutator (F ⧸ denominator R) := by
  let q := QuotientGroup.mk' (denominator R)
  have h : (intoAmbient R).range = (numerator R).map q := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      induction b using QuotientGroup.induction_on with
      | _ b => exact ⟨b, b.property, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨QuotientGroup.mk ⟨b, hb⟩, rfl⟩
  rw [h, numerator, inf_eq_right.mpr hR, map_commutator_of_surjective
    (QuotientGroup.mk'_surjective _)]

/-- Killing the central commutator of the two generators makes the quotient abelian. -/
private theorem commutator_eq_zpowers {D : Type} [Group D] (q : F →* D)
    (hq : Function.Surjective q)
    (hz : ⁅q x, q y⁆ ∈ Subgroup.center D) :
    commutator D = Subgroup.zpowers ⁅q x, q y⁆ := by
  let K := Subgroup.zpowers ⁅q x, q y⁆
  have : K.Normal := K.normal_of_le_center (Subgroup.zpowers_le.mpr hz)
  let t := QuotientGroup.mk' K
  have hxy : Commute (t (q x)) (t (q y)) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
  have hq' : t.comp q = FreeGroup.lift (fun b => t (q (FreeGroup.of b))) := by
    apply FreeGroup.ext_hom
    simp
  have hgen : Subgroup.closure (Set.range (fun b => t (q (FreeGroup.of b)))) = ⊤ := by
    rw [← FreeGroup.range_lift_eq_closure, ← hq']
    exact MonoidHom.range_eq_top.mpr ((QuotientGroup.mk'_surjective K).comp hq)
  have hcomm : IsMulCommutative (D ⧸ K) := by
    have hc := Subgroup.isMulCommutative_closure (k := Set.range
      (fun b => t (q (FreeGroup.of b)))) (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _
      cases a <;> cases b
      · exact Commute.refl _
      · exact hxy
      · exact hxy.symm
      · exact Commute.refl _)
    have : IsMulCommutative (⊤ : Subgroup (D ⧸ K)) := hgen ▸ hc
    apply IsMulCommutative.of_comm
    intro a b
    exact congrArg Subtype.val (mul_comm' (⟨a, Subgroup.mem_top a⟩ : (⊤ : Subgroup (D ⧸ K)))
      ⟨b, Subgroup.mem_top b⟩)
  exact le_antisymm (Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm)
    (Subgroup.zpowers_le.mpr (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top _) (Subgroup.mem_top _)))

/-- The three upper off-diagonal entries of a unitriangular matrix. -/
@[ext] private structure Unitriangular (d : ℕ) where
  a : ZMod d
  b : ZMod d
  c : ZMod d

namespace Unitriangular

variable {d : ℕ}

private def mul (u v : Unitriangular d) : Unitriangular d :=
  ⟨u.a + v.a, u.b + v.b, u.c + v.c + u.a * v.b⟩

private def inv (u : Unitriangular d) : Unitriangular d :=
  ⟨-u.a, -u.b, -u.c + u.a * u.b⟩

private instance : Group (Unitriangular d) where
  mul := mul
  one := ⟨0, 0, 0⟩
  inv := inv
  mul_assoc u v w := by
    change mul (mul u v) w = mul u (mul v w)
    ext <;> dsimp [mul] <;> ring
  one_mul u := by
    change mul ⟨0, 0, 0⟩ u = u
    ext <;> simp [mul]
  mul_one u := by
    change mul u ⟨0, 0, 0⟩ = u
    ext <;> simp [mul]
  inv_mul_cancel u := by
    change mul (inv u) u = ⟨0, 0, 0⟩
    ext <;> dsimp [mul, inv] <;> ring

private def projection (d : ℕ) : Unitriangular d →* Cyclic d × Cyclic d where
  toFun u := (Multiplicative.ofAdd u.a, Multiplicative.ofAdd u.b)
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem ker_projection_le_center (d : ℕ) :
    (projection d).ker ≤ Subgroup.center (Unitriangular d) := by
  intro u hu
  have heq : projection d u = 1 := hu
  have ha : u.a = 0 := congrArg (fun p : Cyclic d × Cyclic d => p.1.toAdd) heq
  have hb : u.b = 0 := congrArg (fun p : Cyclic d × Cyclic d => p.2.toAdd) heq
  apply Subgroup.mem_center_iff.mpr
  intro v
  change mul v u = mul u v
  ext <;> simp [mul, ha, hb, add_comm v.c u.c]

/-- The central (1,3) entry gives a copy of the additive coefficient group. -/
private def centralEntry (d : ℕ) : Cyclic d →* Unitriangular d where
  toFun z := ⟨0, 0, z.toAdd⟩
  map_one' := rfl
  map_mul' u v := by
    change (⟨0, 0, u.toAdd + v.toAdd⟩ : Unitriangular d) =
      mul ⟨0, 0, u.toAdd⟩ ⟨0, 0, v.toAdd⟩
    ext <;> simp [mul]

private theorem centralEntry_injective (d : ℕ) : Function.Injective (centralEntry d) :=
  fun _ _ h => Multiplicative.toAdd.injective (congrArg Unitriangular.c h)

private def first (d : ℕ) : Unitriangular d := ⟨1, 0, 0⟩
private def second (d : ℕ) : Unitriangular d := ⟨0, 1, 0⟩

private theorem commutator_first_second (d : ℕ) :
    ⁅first d, second d⁆ = centralEntry d (generator d) := by
  change mul (mul (mul (first d) (second d)) (inv (first d))) (inv (second d)) =
    ⟨0, 0, 1⟩
  ext <;> simp [mul, inv, first, second]

end Unitriangular

private def detector (d : ℕ) : F →* Unitriangular d :=
  FreeGroup.lift (fun b => if b then Unitriangular.second d else Unitriangular.first d)

private def reduceCyclic {d m : ℕ} (h : d ∣ m) : Cyclic m →* Cyclic d :=
  (ZMod.castHom h (ZMod d)).toAddMonoidHom.toMultiplicative

@[simp] private theorem reduceCyclic_generator {d m : ℕ} (h : d ∣ m) :
    reduceCyclic h (generator m) = generator d := by
  change Multiplicative.ofAdd (ZMod.castHom h (ZMod d) 1) = Multiplicative.ofAdd 1
  rw [map_one]

private theorem detector_factor (m n : ℕ) :
    (Unitriangular.projection (Nat.gcd m n)).comp (detector (Nat.gcd m n)) =
      ((reduceCyclic (Nat.gcd_dvd_left m n)).prodMap
        (reduceCyclic (Nat.gcd_dvd_right m n))).comp (productPresentation m n) := by
  apply FreeGroup.ext_hom
  intro b
  cases b <;> simp only [MonoidHom.comp_apply, detector, productPresentation,
    FreeGroup.lift_apply_of, Bool.false_eq_true, ite_false, ite_true, MonoidHom.coe_prodMap,
    Prod.map_apply, reduceCyclic_generator, map_one] <;> rfl

/-- The detector descends through the ambient quotient, because each relator
projects to zero in both first coordinates and therefore maps into the center. -/
private def ambientDetector (m n : ℕ) :
    (F ⧸ denominator (productPresentation m n).ker) →* Unitriangular (Nat.gcd m n) :=
  QuotientGroup.lift _ (detector (Nat.gcd m n)) (by
    rw [Subgroup.commutator_le]
    intro a _ r hr
    have hker : detector (Nat.gcd m n) r ∈ (Unitriangular.projection (Nat.gcd m n)).ker := by
      change ((Unitriangular.projection _).comp (detector _)) r = 1
      rw [detector_factor, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hr, map_one]
    exact MonoidHom.mem_ker.mpr (by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp (Unitriangular.ker_projection_le_center _ hker) _)))

private theorem ambient_commutator_order (m n : ℕ) (R : Subgroup F) [R.Normal]
    (hR : R = (productPresentation m n).ker) :
    let q := QuotientGroup.mk' (denominator R)
    orderOf ⁅q x, q y⁆ = Nat.gcd m n := by
  subst R
  let R := (productPresentation m n).ker
  let q := QuotientGroup.mk' (denominator R)
  change orderOf ⁅q x, q y⁆ = Nat.gcd m n
  have hzR : ⁅x, y⁆ ∈ R :=
    commutator_le_ker (productPresentation m n)
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
  have hz (a : F ⧸ denominator R) : Commute a ⁅q x, q y⁆ := by
    rw [← map_commutatorElement]
    exact commute_relator_class R hzR a
  have hx : x ^ m ∈ R := by
    change productPresentation m n (x ^ m) = 1
    simp [generator_pow]
  have hy : y ^ n ∈ R := by
    change productPresentation m n (y ^ n) = 1
    simp [generator_pow]
  -- The relators x^m and y^n are central in the ambient quotient.
  have hm : ⁅q x, q y⁆ ^ m = 1 := by
    rw [(hz (q x)).commutatorElement_pow_left m, ← map_pow]
    exact (commute_relator_class R hx (q y)).symm.commutator_eq
  have hn : ⁅q x, q y⁆ ^ n = 1 := by
    rw [(hz (q y)).commutatorElement_pow_right n, ← map_pow]
    exact (commute_relator_class R hy (q x)).commutator_eq
  have hdet :
      ambientDetector m n ⁅q x, q y⁆ =
        Unitriangular.centralEntry _ (generator (Nat.gcd m n)) := by
    rw [← map_commutatorElement q]
    change detector (Nat.gcd m n) ⁅x, y⁆ = _
    rw [map_commutatorElement]
    simpa [detector, x, y] using Unitriangular.commutator_first_second (Nat.gcd m n)
  have hdiv := orderOf_map_dvd (ambientDetector m n) ⁅q x, q y⁆
  rw [hdet, orderOf_injective _ (Unitriangular.centralEntry_injective _), orderOf_generator] at hdiv
  exact Nat.dvd_antisymm
    (Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm) (orderOf_dvd_of_pow_eq_one hn)) hdiv

theorem cyclic_product : Specs.ALG02GroupTheory.CyclicMultipliers.CyclicProduct := by
  intro m n hm hn
  let p := productPresentation m n
  let S := kernelExtension p (productPresentation_surjective m n)
  let R := S.inl.range
  have hR : R = p.ker := S.range_inl_eq_ker_rightHom
  let q := QuotientGroup.mk' (denominator R)
  have hle : commutator F ≤ R := hR ▸ commutator_le_ker p
  have hzR : ⁅x, y⁆ ∈ numerator R := by
    have hz : ⁅x, y⁆ ∈ commutator F :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    exact ⟨hle hz, hz⟩
  let z : PresentationQuotient R := QuotientGroup.mk ⟨⁅x, y⁆, hzR⟩
  have hz : intoAmbient R z = ⁅q x, q y⁆ := map_commutatorElement q x y
  have hcomm : commutator (F ⧸ denominator R) = Subgroup.zpowers ⁅q x, q y⁆ := by
    apply commutator_eq_zpowers q (QuotientGroup.mk'_surjective _)
    rw [← map_commutatorElement q]
    exact Subgroup.mem_center_iff.mpr (fun a => (commute_relator_class R hzR.1 a).eq)
  have hgen (a : PresentationQuotient R) : a ∈ Subgroup.zpowers z := by
    have ha : intoAmbient R a ∈ (intoAmbient R).range := ⟨a, rfl⟩
    rw [intoAmbient_range R hle, hcomm, ← hz] at ha
    obtain ⟨k, hk⟩ := ha
    exact ⟨k, intoAmbient_injective R (by rwa [map_zpow])⟩
  have hord : orderOf z = Nat.gcd m n := by
    rw [← orderOf_injective (intoAmbient R) (intoAmbient_injective R), hz]
    exact ambient_commutator_order m n R hR
  have heq : orderOf z = orderOf (generator (Nat.gcd m n)) :=
    hord.trans (orderOf_generator _).symm
  exact ⟨((hopfEquiv S).trans (mulEquivOfOrderOfEq hgen (mem_zpowers_generator _) heq)).toAdditive⟩

end
end ALG02GroupTheory.CyclicMultipliers
