import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.CapProducts
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.CupProduct

/-! Cap products for paper.tex `prop:p202-cap` (2156–2192).
The front/back operation satisfies the chain identities in all ordinary degrees
and descends to both pair homology products with the stated representatives. -/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
open scoped TensorProduct Simplicial
namespace P202.CapProducts
open P202Specs.SingularChains P202Specs.AlexanderWhitney
open P202Specs.CohomologyPairs P202Specs.RelativeSingularChains P202Specs.CupProduct
open P202Specs.CapProducts
universe u w
variable (R : Type u) [CommRing R]

abbrev capAt := P202Specs.CapProducts.capAt R
abbrev cap := P202Specs.CapProducts.cap R

@[simp] theorem capAt_single (X : TopCat.{w}) (p n k : ℕ) (h : p+k=n)
    (a : Cochain R X p) (s : Simplex X n) (r : R) :
    capAt R X p n k h a (Finsupp.single s r) =
      (r * a (Finsupp.single (interval s 0 p (by omega)) 1)) •
        Finsupp.single (interval s p k (by omega)) 1 := by
  simp [capAt, P202Specs.CapProducts.capAt, Finsupp.llift_apply, Finsupp.lift_apply]

theorem cap_pairing (X : TopCat.{w}) (p n k : ℕ) (h : p+k=n)
    (a : Cochain R X p) (b : Cochain R X k) (c : Chains R X n) :
    b (capAt R X p n k h a c) = castCochain R h (cup R X p k a b) c := by
  have he : b.comp (capAt R X p n k h a) = castCochain R h (cup R X p k a b) := by
    apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R X n)).ext
    intro s
    simp only [Finsupp.coe_basisSingleOne, LinearMap.comp_apply, capAt_single,
      one_mul, map_smul, smul_eq_mul]
    exact (P202.CupProduct.cast_cup_single R h a b s).symm
  exact LinearMap.congr_fun he c

lemma chains_ext {X : TopCat.{w}} {k : ℕ} {c d : Chains R X k}
    (h : ∀ b : Cochain R X k, b c = b d) : c=d := by
  ext s
  exact h (Finsupp.lapply s)

theorem cap_boundary (X : TopCat.{w}) (p n k : ℕ) (h : p+k=n)
    (a : Cochain R X p) (c : Chains R X (n+1)) :
    boundary R R X k (capAt R X p (n+1) (k+1) (by omega) a c) =
      (-1 : ℤ)^p • (capAt R X p n k h a (boundary R R X n c) -
        capAt R X (p+1) (n+1) k (by omega) (delta R X p a) c) := by
  subst n
  apply chains_ext R
  intro b
  change delta R X k b (capAt R X p (p+k+1) (k+1) _ a c) = _
  rw [cap_pairing]
  simp only [map_zsmul, map_sub, cap_pairing]
  have hh := LinearMap.congr_fun (P202.CupProduct.cup_leibniz R X p k a b) c
  change cup R X p k a b (boundary R R X (p+k) c) = _ at hh
  simp only [LinearMap.add_apply, LinearMap.smul_apply] at hh
  change _ = (-1 : ℤ)^p • (cup R X p k a b (boundary R R X (p+k) c) - _)
  rw [hh, add_sub_cancel_left, smul_smul, ← mul_pow]
  norm_num

theorem cap_natural {X Y : TopCat.{w}} (f : X ⟶ Y)
    (p n k : ℕ) (h : p+k=n) (a : Cochain R Y p) (c : Chains R X n) :
    ((chainMap R R f).f k).hom (capAt R X p n k h (pullback R f p a) c) =
      capAt R Y p n k h a (((chainMap R R f).f n).hom c) := by
  subst n
  apply chains_ext R
  intro b
  change pullback R f k b (capAt R X p (p+k) k rfl (pullback R f p a) c) = _
  rw [cap_pairing, cap_pairing]
  exact (LinearMap.congr_fun (P202.CupProduct.cup_natural R f p k a b) c).symm

/-- A cap of a subspace chain is a subspace chain. -/
theorem capAt_preserves_subspace (P : Pair.{w}) (p n k : ℕ) (h : p+k=n)
    (a : Cochain R P.space p) (c : Chains R P.space n)
    (hc : c ∈ ((chainMap R R P.inclusion).f n).hom.range) :
    capAt R P.space p n k h a c ∈ ((chainMap R R P.inclusion).f k).hom.range := by
  obtain ⟨d, rfl⟩ := hc
  exact ⟨capAt R P.sub p n k h (pullback R P.inclusion p a) d,
    cap_natural R P.inclusion p n k h a d⟩

/-- A relative cochain kills every subspace chain under cap. -/
theorem capAt_annihilates_subspace (P : Pair.{w}) (p n k : ℕ) (h : p+k=n)
    (a : Cochain R P.space p) (ha : a ∈ vanishingCochains R R P p)
    (c : Chains R P.space n)
    (hc : c ∈ ((chainMap R R P.inclusion).f n).hom.range) :
    capAt R P.space p n k h a c = 0 := by
  obtain ⟨d, rfl⟩ := hc
  have ha' : pullback R P.inclusion p a = 0 := ha
  rw [← cap_natural, ha', map_zero, LinearMap.zero_apply, map_zero]

/-- The vanishing convention uses the genuine negative ordinary chain group. -/
theorem zeroAbove : zeroAbove_type.{u,w} := by
  intro R _ X p q h
  simp [P202Specs.CapProducts.cap, not_le.mpr h]

lemma chainDegreeEquiv_nat (X : TopCat.{w}) (n : ℕ) (h : 0 ≤ (n : ℤ)) :
    chainDegreeEquiv R X (n : ℤ) h = (ordinaryNonnegativeIso R R X n).toLinearEquiv := by
  ext x
  simp [chainDegreeEquiv]

/-- Transport only the degree of a finite chain. -/
def castChains {X : TopCat.{w}} {n m : ℕ} (h : n=m) :
    Chains R X n →ₗ[R] Chains R X m := h ▸ LinearMap.id

lemma cast_chainDegreeEquiv_symm {X : TopCat.{w}} {i j : ℤ}
    (hi : 0 ≤ i) (hj : 0 ≤ j) (h : i=j) (c : Chains R X i.toNat) :
    castOrdinary R h ((chainDegreeEquiv R X i hi).symm c) =
      (chainDegreeEquiv R X j hj).symm (castChains R (congrArg Int.toNat h) c) := by
  subst j
  rfl

lemma cast_capAt {X : TopCat.{w}} {p n k l : ℕ} (h : k=l) (hd : p+k=n)
    (a : Cochain R X p) (c : Chains R X n) :
    castChains R h (capAt R X p n k hd a c) = capAt R X p n l (by omega) a c := by
  subst l
  rfl

/-- The integer-graded cap is exactly the finite-chain cap under the ordinary
nonnegative degree identifications. -/
lemma cap_nonnegative (X : TopCat.{w}) (p n k : ℕ) (h : p+k=n)
    (a : Cochain R X p) (c : (ordinaryComplex R R X).X (n : ℤ)) :
    castOrdinary R (by omega : (n:ℤ)-(p:ℤ)=(k:ℤ)) (cap R X p (n:ℤ) a c) =
      (ordinaryNonnegativeIso R R X k).inv
        (capAt R X p n k h a ((ordinaryNonnegativeIso R R X n).hom c)) := by
  simp only [cap, P202Specs.CapProducts.cap,
    dite_eq_left (show (p:ℤ) ≤ (n:ℤ) by omega)]
  change castOrdinary R _ ((chainDegreeEquiv R X ((n:ℤ)-p) (by omega)).symm _) = _
  rw [cast_chainDegreeEquiv_symm R (by omega) (by omega)]
  simp only [LinearMap.compl₂_apply]
  erw [cast_capAt]
  simp only [Int.toNat_natCast, chainDegreeEquiv_nat]
  rfl

lemma castOrdinary_comp {X : TopCat.{w}} {i j k : ℤ}
    (h : i=j) (h' : j=k) (c : (ordinaryComplex R R X).X i) :
    castOrdinary R h' (castOrdinary R h c) = castOrdinary R (h.trans h') c := by
  subst j
  subst k
  rfl

lemma castOrdinary_d {X : TopCat.{w}} {i j i' j' : ℤ}
    (hi : i=i') (hj : j=j') (c : (ordinaryComplex R R X).X i) :
    castOrdinary R hj ((ordinaryComplex R R X).d i j c) =
      (ordinaryComplex R R X).d i' j' (castOrdinary R hi c) := by
  subst i'
  subst j'
  rfl

lemma ordinary_boundary_inv (X : TopCat.{w}) (n : ℕ) (c : Chains R X (n+1)) :
    (ordinaryComplex R R X).d ((n+1:ℕ):ℤ) (n:ℤ)
      ((ordinaryNonnegativeIso R R X (n+1)).inv c) =
        (ordinaryNonnegativeIso R R X n).inv (boundary R R X n c) := by
  apply (ModuleCat.mono_iff_injective (ordinaryNonnegativeIso R R X n).hom).mp inferInstance
  have hh := congrArg (fun f : (complex R R X).X (n+1) ⟶ (complex R R X).X n => f c)
    (P202.SingularChains.ordinary_boundary R R X n)
  simpa using hh

lemma cap_degree_formula (X : TopCat.{w}) (p : ℕ) (q : ℤ) (n k : ℕ)
    (hi : q=(n:ℤ)) (ho : q-p=(k:ℤ)) (a : Cochain R X p)
    (c : (ordinaryComplex R R X).X q) :
    castOrdinary R ho (cap R X p q a c) =
      (ordinaryNonnegativeIso R R X k).inv
        (capAt R X p n k (by omega) a
          ((ordinaryNonnegativeIso R R X n).hom (castOrdinary R hi c))) := by
  subst q
  exact cap_nonnegative R X p n k (by omega) a c
lemma castOrdinary_injective {X : TopCat.{w}} {i j : ℤ} (h : i=j) :
    Function.Injective (castOrdinary R (X:=X) h) := by
  subst j
  exact Function.injective_id
lemma ordinary_boundary_hom (X : TopCat.{w}) (n : ℕ)
    (c : (ordinaryComplex R R X).X ((n+1:ℕ):ℤ)) :
    (ordinaryNonnegativeIso R R X n).hom ((ordinaryComplex R R X).d ((n+1:ℕ):ℤ) n c) =
      boundary R R X n ((ordinaryNonnegativeIso R R X (n+1)).hom c) := by
  have hh := ordinary_boundary_inv R X n ((ordinaryNonnegativeIso R R X (n+1)).hom c)
  have hh' := congrArg (fun x => (ordinaryNonnegativeIso R R X n).hom x) hh
  simpa using hh'

/-- All terms of the boundary identity at or below the diagonal lie in a zero
ordinary chain module. This includes q=p, not just q<p. -/
theorem cap_boundary_low (X : TopCat.{w}) (p : ℕ) (q : ℤ) (hq : q ≤ p)
    (a : Cochain R X p) (c : (ordinaryComplex R R X).X q) :
    (ordinaryComplex R R X).d (q-p) (q-p-1) (cap R X p q a c) =
      (-1 : ℤ)^p •
        (castOrdinary R (by omega : (q-1)-(p : ℤ)=q-p-1)
          (cap R X p (q-1) a ((ordinaryComplex R R X).d q (q-1) c)) -
         castOrdinary R (by omega : q-((p+1 : ℕ) : ℤ)=q-p-1)
          (cap R X (p+1) q (delta R X p a) c)) := by
  letI := ModuleCat.subsingleton_of_isZero
    (P202.SingularChains.ordinary_negative_chains R R X (q-p-1) (by omega))
  exact Subsingleton.elim _ _

theorem ordinaryBoundary : ordinaryBoundary_type.{u,w} := by
  intro R _ X p q a c
  by_cases hq : q ≤ p
  · exact cap_boundary_low R X p q hq a c
  · have hpos : (p:ℤ) < q := by omega
    let n := (q-1).toNat
    let k := (q-p-1).toNat
    have hn : q-1=(n:ℤ) := by dsimp [n]; omega
    have hk : q-p-1=(k:ℤ) := by dsimp [k]; omega
    have hpn : p+k=n := by omega
    have hq' : q=((n+1:ℕ):ℤ) := by omega
    have hkp : q-p=((k+1:ℕ):ℤ) := by omega
    apply castOrdinary_injective R hk
    rw [castOrdinary_d R hkp hk]
    rw [cap_degree_formula R X p q (n+1) (k+1) hq' hkp]
    rw [ordinary_boundary_inv, P202.CapProducts.cap_boundary]
    simp only [map_zsmul, map_sub]
    rw [castOrdinary_comp, castOrdinary_comp]
    rw [cap_degree_formula R X p (q-1) n k hn (by omega)]
    rw [cap_degree_formula R X (p+1) q (n+1) k hq' (by omega)]
    rw [castOrdinary_d R hq' hn, ordinary_boundary_hom]

lemma castOrdinary_map {X Y : TopCat.{w}} (f : X ⟶ Y) {i j : ℤ}
    (h : i=j) (c : (ordinaryComplex R R X).X i) :
    castOrdinary R h (((ordinaryFunctor R R).map f).f i c) =
      ((ordinaryFunctor R R).map f).f j (castOrdinary R h c) := by
  subst j
  rfl
lemma ordinary_chainMap_inv {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (c : Chains R X n) :
    ((ordinaryFunctor R R).map f).f (n:ℤ) ((ordinaryNonnegativeIso R R X n).inv c) =
      (ordinaryNonnegativeIso R R Y n).inv (((chainMap R R f).f n).hom c) :=
  congrArg (fun ff => ff c) (P202.CupProduct.ordinary_chainMap_degree R f n)
lemma ordinary_chainMap_hom {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (c : (ordinaryComplex R R X).X (n:ℤ)) :
    (ordinaryNonnegativeIso R R Y n).hom (((ordinaryFunctor R R).map f).f (n:ℤ) c) =
      ((chainMap R R f).f n).hom ((ordinaryNonnegativeIso R R X n).hom c) := by
  have hh := congrArg (fun x => (ordinaryNonnegativeIso R R Y n).hom x)
    (ordinary_chainMap_inv R f n ((ordinaryNonnegativeIso R R X n).hom c))
  simpa using hh

theorem ordinaryNatural {X Y : TopCat.{w}} (f : X ⟶ Y)
    (p : ℕ) (q : ℤ) (a : Cochain R Y p) (c : (ordinaryComplex R R X).X q) :
    ((ordinaryFunctor R R).map f).f (q-p)
      (P202Specs.CapProducts.cap R X p q (pullback R f p a) c) =
    P202Specs.CapProducts.cap R Y p q a (((ordinaryFunctor R R).map f).f q c) := by
  by_cases h : q < p
  · erw [zeroAbove R X p q h, zeroAbove R Y p q h]
    simp
  · let n := q.toNat
    let k := (q-p).toNat
    have hn : q=(n:ℤ) := by dsimp [n]; omega
    have hk : q-p=(k:ℤ) := by dsimp [k]; omega
    apply castOrdinary_injective R hk
    rw [castOrdinary_map R f hk]
    rw [cap_degree_formula R X p q n k hn hk]
    rw [ordinary_chainMap_inv]
    rw [cap_degree_formula R Y p q n k hn hk]
    rw [castOrdinary_map R f hn, ordinary_chainMap_hom, cap_natural]

/-- Integer-graded cap preserves the ordinary subspace-chain image. -/
theorem cap_preserves_subspace (P : Pair.{w}) (p : ℕ) (q : ℤ)
    (a : Cochain R P.space p) (c : (ordinaryComplex R R P.space).X q)
    (hc : c ∈ ((inclusion (ordinaryFunctor R R) P).f q).hom.range) :
    cap R P.space p q a c ∈ ((inclusion (ordinaryFunctor R R) P).f (q-p)).hom.range := by
  obtain ⟨d, rfl⟩ := hc
  exact ⟨cap R P.sub p q (pullback R P.inclusion p a) d,
    ordinaryNatural R P.inclusion p q a d⟩

/-- Integer-graded cap by a cochain vanishing on B annihilates chains of B. -/
theorem cap_annihilates_subspace (P : Pair.{w}) (p : ℕ) (q : ℤ)
    (a : Cochain R P.space p) (ha : a ∈ vanishingCochains R R P p)
    (c : (ordinaryComplex R R P.space).X q)
    (hc : c ∈ ((inclusion (ordinaryFunctor R R) P).f q).hom.range) :
    cap R P.space p q a c = 0 := by
  obtain ⟨d, rfl⟩ := hc
  have ha' : pullback R P.inclusion p a = 0 := ha
  rw [← ordinaryNatural R P.inclusion p q a d, ha', map_zero, LinearMap.zero_apply, map_zero]

theorem ordinaryNaturality : ordinaryNaturality_type.{u,w} := ordinaryNatural

/-- Complete nonnegative chain laws. -/
theorem formula : P202Specs.CapProducts.formula_type.{u,w} := capAt_single

theorem pairing : pairing_type.{u,w} := cap_pairing

theorem boundary : boundary_type.{u,w} := cap_boundary

theorem naturality : P202Specs.CapProducts.naturality_type.{u,w} := cap_natural

/-! A bilinear differential operation descends through both homology quotients. -/
section AlgebraicDescent
universe v
variable {R}
variable (C : CochainComplex (ModuleCat.{v} R) ℤ)
  (D E : ChainComplex (ModuleCat.{v} R) ℤ)

/-- Explicit degree parameters keep arithmetic transports out of the descent. -/
structure CapSystem where
  op : ∀ (p : ℕ) (q k : ℤ), q-(p:ℤ)=k →
    C.X (p:ℤ) →ₗ[R] D.X q →ₗ[R] E.X k
  boundary : ∀ (p : ℕ) (q n k : ℤ) (hn : q-(p:ℤ)=n) (hk : n-1=k)
    (a : C.X (p:ℤ)) (c : D.X q),
    E.d n k (op p q n hn a c) = (-1:ℤ)^p •
      (op p (q-1) k (by omega) a (D.d q (q-1) c) -
       op (p+1) q k (by push_cast; omega) (C.d (p:ℤ) ((p+1:ℕ):ℤ) a) c)
  negative : IsZero (C.X (-1))

variable {C D E}

lemma cycles_injective (K : HomologicalComplex (ModuleCat.{v} R) (ComplexShape.down ℤ))
    (q : ℤ) : Function.Injective (K.iCycles q) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

lemma chain_cycle_closed (K : ChainComplex (ModuleCat.{v} R) ℤ) (q : ℤ)
    (z : K.cycles q) : K.d q (q-1) (K.iCycles q z) = 0 := by
  exact congrArg (fun f => f z) (K.iCycles_d q (q-1))

lemma cochain_cycle_closed (K : CochainComplex (ModuleCat.{v} R) ℤ) (p : ℕ)
    (a : K.cycles (p:ℤ)) : K.d (p:ℤ) ((p+1:ℕ):ℤ) (K.iCycles (p:ℤ) a) = 0 := by
  exact congrArg (fun f => f a) (K.iCycles_d (p:ℤ) ((p+1:ℕ):ℤ))

/-- A literal closed element as a categorical cycle. -/
def chainCycle (K : ChainComplex (ModuleCat.{v} R) ℤ) (q : ℤ)
    (x : K.X q) (hx : K.d q (q-1) x = 0) : K.cycles q :=
  (K.sc q).moduleCatCyclesIso.inv ⟨x, by
    change K.d q ((ComplexShape.down ℤ).next q) x = 0
    rw [(ComplexShape.down ℤ).next_eq' (show (ComplexShape.down ℤ).Rel q (q-1) by change q-1+1=q; omega)]
    exact hx⟩

@[simp] lemma chainCycle_i (K : ChainComplex (ModuleCat.{v} R) ℤ) (q : ℤ)
    (x : K.X q) (hx : K.d q (q-1) x = 0) :
    K.iCycles q (chainCycle K q x hx) = x := by
  exact congrArg (fun f => f ⟨x, by change K.d q _ x=0; rw [(ComplexShape.down ℤ).next_eq' (show (ComplexShape.down ℤ).Rel q (q-1) by change q-1+1=q; omega)]; exact hx⟩)
    (K.sc q).moduleCatCyclesIso_inv_iCycles

lemma chain_class_zero_iff (K : ChainComplex (ModuleCat.{v} R) ℤ) (q : ℤ)
    (z : K.cycles q) : K.homologyπ q z = 0 ↔
      ∃ x : K.X (q+1), K.d (q+1) q x = K.iCycles q z := by
  change (K.sc q).homologyπ z = 0 ↔ _
  rw [P202.CupProduct.shortComplex_homologyπ_eq_zero_iff]
  change (∃ x : K.X ((ComplexShape.down ℤ).prev q), K.d _ q x = K.iCycles q z) ↔ _
  rw [(ComplexShape.down ℤ).prev_eq' (show (ComplexShape.down ℤ).Rel (q+1) q by rfl)]

lemma cochain_class_zero_positive (K : CochainComplex (ModuleCat.{v} R) ℤ) (p : ℕ)
    (z : K.cycles ((p+1:ℕ):ℤ)) : K.homologyπ ((p+1:ℕ):ℤ) z = 0 ↔
      ∃ x : K.X (p:ℤ), K.d (p:ℤ) ((p+1:ℕ):ℤ) x = K.iCycles ((p+1:ℕ):ℤ) z := by
  change (K.sc ((p+1:ℕ):ℤ)).homologyπ z = 0 ↔ _
  rw [P202.CupProduct.shortComplex_homologyπ_eq_zero_iff]
  change (∃ x : K.X ((ComplexShape.up ℤ).prev ((p+1:ℕ):ℤ)), K.d _ _ x = K.iCycles _ z) ↔ _
  rw [(ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (p:ℤ) ((p+1:ℕ):ℤ) by simp)]

variable (S : CapSystem C D E)

lemma CapSystem.closed (p : ℕ) (q : ℤ) (a : C.cycles (p:ℤ)) (z : D.cycles q) :
    E.d (q-p) (q-p-1)
      (S.op p q (q-p) rfl (C.iCycles (p:ℤ) a) (D.iCycles q z)) = 0 := by
  rw [S.boundary p q (q-p) (q-p-1) rfl rfl]
  simp only [chain_cycle_closed, cochain_cycle_closed, map_zero, LinearMap.zero_apply,
    sub_zero, smul_zero]

def CapSystem.cycleOp (p : ℕ) (q : ℤ) :
    C.cycles (p:ℤ) →ₗ[R] D.cycles q →ₗ[R] E.cycles (q-p) where
  toFun a :=
    { toFun := fun z => chainCycle E (q-p)
        (S.op p q (q-p) rfl (C.iCycles (p:ℤ) a) (D.iCycles q z)) (S.closed p q a z)
      map_add' := by
        intro z z'
        apply cycles_injective E
        simp only [chainCycle_i, map_add]
      map_smul' := by
        intro r z
        apply cycles_injective E
        simp only [chainCycle_i, map_smul, RingHom.id_apply] }
  map_add' := by
    intro a b
    ext z
    apply cycles_injective E
    simp only [LinearMap.coe_mk, AddHom.coe_mk, chainCycle_i, map_add, LinearMap.add_apply]
  map_smul' := by
    intro r a
    ext z
    apply cycles_injective E
    simp only [LinearMap.coe_mk, AddHom.coe_mk, chainCycle_i, map_smul, LinearMap.smul_apply,
      RingHom.id_apply]

@[simp] lemma CapSystem.cycleOp_i (p : ℕ) (q : ℤ)
    (a : C.cycles (p:ℤ)) (z : D.cycles q) :
    E.iCycles (q-p) (S.cycleOp p q a z) =
      S.op p q (q-p) rfl (C.iCycles (p:ℤ) a) (D.iCycles q z) := chainCycle_i _ _ _ (S.closed p q a z)

lemma CapSystem.boundary_right (p : ℕ) (q : ℤ)
    (a : C.cycles (p:ℤ)) (z : D.cycles q) (hz : D.homologyπ q z = 0) :
    E.homologyπ (q-p) (S.cycleOp p q a z) = 0 := by
  obtain ⟨c, hc⟩ := (chain_class_zero_iff D q z).mp hz
  apply (chain_class_zero_iff E (q-p) _).mpr
  refine ⟨(-1:ℤ)^p • S.op p (q+1) (q-p+1) (by omega) (C.iCycles (p:ℤ) a) c, ?_⟩
  rw [map_zsmul, S.boundary p (q+1) (q-p+1) (q-p) (by omega) (by omega),
    cochain_cycle_closed, map_zero, LinearMap.zero_apply, sub_zero,
    smul_smul, ← mul_pow]
  norm_num
  have hq : q+1-1=q := by omega
  have hop (r : ℤ) (h : r=q) (hp : r-(p:ℤ)=q-p) :
      S.op p r (q-p) hp (C.iCycles (p:ℤ) a) (D.d (q+1) r c) =
      S.op p q (q-p) rfl (C.iCycles (p:ℤ) a) (D.d (q+1) q c) := by
    subst r
    rfl
  exact (hop _ hq _).trans
    (congrArg (S.op p q (q-p) rfl (C.iCycles (p:ℤ) a)) hc)

lemma CapSystem.boundary_left (p : ℕ) (q : ℤ)
    (a : C.cycles (p:ℤ)) (z : D.cycles q) (ha : C.homologyπ (p:ℤ) a = 0) :
    E.homologyπ (q-p) (S.cycleOp p q a z) = 0 := by
  cases p with
  | zero =>
    obtain ⟨x, hx⟩ := (P202.CupProduct.shortComplex_homologyπ_eq_zero_iff R (C.sc 0) a).mp ha
    haveI : Subsingleton ((C.sc 0).X₁) := by
      change Subsingleton (C.X ((ComplexShape.up ℤ).prev 0))
      rw [(ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)]
      exact ModuleCat.subsingleton_of_isZero S.negative
    have hx0 : x=0 := Subsingleton.elim _ _
    rw [hx0, map_zero] at hx
    have ha0 : a=0 := (ModuleCat.mono_iff_injective (C.iCycles 0)).mp inferInstance
      (hx.symm.trans (map_zero _).symm)
    rw [ha0, map_zero, LinearMap.zero_apply, map_zero]
  | succ p =>
    obtain ⟨b, hb⟩ := (cochain_class_zero_positive C p a).mp ha
    apply (chain_class_zero_iff E (q-(p+1:ℕ)) _).mpr
    refine ⟨-((-1:ℤ)^p • S.op p q (q-(p+1:ℕ)+1) (by push_cast; omega) b (D.iCycles q z)), ?_⟩
    rw [map_neg, map_zsmul, S.boundary p q (q-(p+1:ℕ)+1) (q-(p+1:ℕ)) (by push_cast; omega) (by omega),
      chain_cycle_closed, map_zero, zero_sub]
    simp only [smul_neg, neg_neg, smul_smul, ← mul_pow]
    norm_num
    rw [hb]

def CapSystem.homologyOp (p : ℕ) (q : ℤ) :
    C.homology (p:ℤ) →ₗ[R] D.homology q →ₗ[R] E.homology (q-p) :=
  P202.CupProduct.descendBilinear (C.homologyπ (p:ℤ)).hom (D.homologyπ q).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)
    ((LinearMap.llcomp R _ _ _ (E.homologyπ (q-p)).hom).comp (S.cycleOp p q))
    (fun a ha => by ext z; exact S.boundary_left p q a z ha)
    (fun a z hz => S.boundary_right p q a z hz)

@[simp] lemma CapSystem.homologyOp_rep (p : ℕ) (q : ℤ)
    (a : C.cycles (p:ℤ)) (z : D.cycles q) :
    S.homologyOp p q (C.homologyπ (p:ℤ) a) (D.homologyπ q z) =
      E.homologyπ (q-p) (S.cycleOp p q a z) :=
  P202.CupProduct.descendBilinear_apply _ _ _ _ _ _ _ a z

end AlgebraicDescent

/-! Degreewise quotient operations for the two pairs of complexes. -/

lemma projection_surjective (P : Pair.{w}) (q : ℤ) :
    Function.Surjective ((projection (ordinaryFunctor R R) P).f q) :=
  (P202.RelativeSingularChains.ordinary_short_exact R R P q).moduleCat_surjective_g

lemma projection_kernel (P : Pair.{w}) (q : ℤ)
    (c : (ordinaryComplex R R P.space).X q) :
    (projection (ordinaryFunctor R R) P).f q c = 0 ↔
      c ∈ ((inclusion (ordinaryFunctor R R) P).f q).hom.range := by
  constructor
  · exact (ShortComplex.moduleCat_exact_iff _).mp
      (P202.RelativeSingularChains.ordinary_short_exact R R P q).exact c
  · rintro ⟨d, rfl⟩
    exact ((sequence (ordinaryFunctor R R) P).map (HomologicalComplex.eval _ _ q)).zero_apply d

/-- The actual absolute cochain underlying a relative cochain. -/
def relativeValue (P : Pair.{w}) (p : ℕ) :
    (relativeCochains R R P).X (p:ℤ) →ₗ[R] Cochain R P.space p :=
  (ordinaryCochainsEquiv R R P.space p).toLinearMap.comp
    ((relativeToAbsolute R R P).f (p:ℤ)).hom

lemma relativeValue_vanishing (P : Pair.{w}) (p : ℕ)
    (a : (relativeCochains R R P).X (p:ℤ)) :
    relativeValue R P p a ∈ vanishingCochains R R P p := by
  change pullback R P.inclusion p (relativeValue R P p a) = 0
  change pullback R P.inclusion p (ordinaryCochainsEquiv R R P.space p
    ((relativeToAbsolute R R P).f (p:ℤ) a)) = 0
  rw [← P202.CupProduct.ordinaryCochainsEquiv_pullback]
  have h := congrArg (fun f => f a)
    ((cochainSequence R R P).map (HomologicalComplex.eval _ _ (p:ℤ))).zero
  change (restriction R R P).f (p:ℤ) ((relativeToAbsolute R R P).f (p:ℤ) a) = 0 at h
  change ordinaryCochainsEquiv R R P.sub p
    ((restriction R R P).f (p:ℤ) ((relativeToAbsolute R R P).f (p:ℤ) a)) = 0
  rw [h, map_zero]

lemma relativeValue_d (P : Pair.{w}) (p : ℕ)
    (a : (relativeCochains R R P).X (p:ℤ)) :
    relativeValue R P (p+1) ((relativeCochains R R P).d (p:ℤ) ((p+1:ℕ):ℤ) a) =
      delta R P.space p (relativeValue R P p a) := by
  change ordinaryCochainsEquiv R R P.space (p+1)
    ((relativeToAbsolute R R P).f ((p+1:ℕ):ℤ)
      ((relativeCochains R R P).d (p:ℤ) ((p+1:ℕ):ℤ) a)) =
    delta R P.space p (ordinaryCochainsEquiv R R P.space p
      ((relativeToAbsolute R R P).f (p:ℤ) a))
  rw [← P202.CupProduct.ordinaryCochainsEquiv_d]
  exact congrArg (fun x => ordinaryCochainsEquiv R R P.space (p+1) x)
    (congrArg (fun f => f a) ((relativeToAbsolute R R P).comm (p:ℤ) ((p+1:ℕ):ℤ))).symm

/-- Cap of absolute cochains with relative chains, before homology. -/
def absoluteChainCap (P : Pair.{w}) (p : ℕ) (q : ℤ) :
    (ordinaryCochains R R P.space).X (p:ℤ) →ₗ[R]
      (ordinary R R P).X q →ₗ[R] (ordinary R R P).X (q-p) :=
  P202.CupProduct.descendBilinear LinearMap.id ((projection (ordinaryFunctor R R) P).f q).hom
    Function.surjective_id (projection_surjective R P q)
    ((LinearMap.llcomp R _ _ _ ((projection (ordinaryFunctor R R) P).f (q-p)).hom).comp
      ((cap R P.space p q).comp (ordinaryCochainsEquiv R R P.space p).toLinearMap))
    (by intro a ha; change a=0 at ha; subst a; exact map_zero _)
    (by
      intro a c hc
      exact (projection_kernel R P (q-p) _).mpr
        (cap_preserves_subspace R P p q _ c ((projection_kernel R P q c).mp hc)))

@[simp] lemma absoluteChainCap_lift (P : Pair.{w}) (p : ℕ) (q : ℤ)
    (a : (ordinaryCochains R R P.space).X (p:ℤ))
    (c : (ordinaryComplex R R P.space).X q) :
    absoluteChainCap R P p q a ((projection (ordinaryFunctor R R) P).f q c) =
      (projection (ordinaryFunctor R R) P).f (q-p)
        (cap R P.space p q (ordinaryCochainsEquiv R R P.space p a) c) :=
  P202.CupProduct.descendBilinear_apply _ _ _ _ _ _ _ a c

/-- Cap of relative cochains with relative chains, with absolute output. -/
def relativeChainCap (P : Pair.{w}) (p : ℕ) (q : ℤ) :
    (relativeCochains R R P).X (p:ℤ) →ₗ[R]
      (ordinary R R P).X q →ₗ[R] (ordinaryComplex R R P.space).X (q-p) :=
  P202.CupProduct.descendBilinear LinearMap.id ((projection (ordinaryFunctor R R) P).f q).hom
    Function.surjective_id (projection_surjective R P q)
    ((cap R P.space p q).comp (relativeValue R P p))
    (by intro a ha; change a=0 at ha; subst a; exact map_zero _)
    (fun a c hc => cap_annihilates_subspace R P p q _
      (relativeValue_vanishing R P p a) c ((projection_kernel R P q c).mp hc))

@[simp] lemma relativeChainCap_lift (P : Pair.{w}) (p : ℕ) (q : ℤ)
    (a : (relativeCochains R R P).X (p:ℤ))
    (c : (ordinaryComplex R R P.space).X q) :
    relativeChainCap R P p q a ((projection (ordinaryFunctor R R) P).f q c) =
      cap R P.space p q (relativeValue R P p a) c :=
  P202.CupProduct.descendBilinear_apply _ _ _ _ _ _ _ a c

universe v
/-- Degree transport for any complex of modules. -/
def complexCast {shape : ComplexShape ℤ}
    (K : HomologicalComplex (ModuleCat.{v} R) shape) {i j : ℤ} (h : i=j) :
    K.X i →ₗ[R] K.X j := h ▸ LinearMap.id

lemma complexCast_d (K : ChainComplex (ModuleCat.{v} R) ℤ)
    {i j i' j' : ℤ} (hi : i=i') (hj : j=j') (c : K.X i) :
    complexCast R K hj (K.d i j c) = K.d i' j' (complexCast R K hi c) := by
  subst i'; subst j'; rfl

lemma complexCast_map {K L : ChainComplex (ModuleCat.{v} R) ℤ}
    (f : K ⟶ L) {i j : ℤ} (h : i=j) (c : K.X i) :
    complexCast R L h (f.f i c) = f.f j (complexCast R K h c) := by
  subst j; rfl

lemma complexCast_comp {shape : ComplexShape ℤ}
    (K : HomologicalComplex (ModuleCat.{v} R) shape) {i j k : ℤ}
    (h : i=j) (h' : j=k) (c : K.X i) :
    complexCast R K h' (complexCast R K h c) = complexCast R K (h.trans h') c := by
  subst j; subst k; rfl

lemma complexCast_ordinary {X : TopCat.{w}} {i j : ℤ} (h : i=j)
    (c : (ordinaryComplex R R X).X i) :
    complexCast R (ordinaryComplex R R X) h c = castOrdinary R h c := by
  subst j; rfl

/-- The full boundary identity transported to arbitrary named output degrees. -/
lemma cap_boundary_degrees (X : TopCat.{w}) (p : ℕ) (q n k : ℤ)
    (hn : q-(p:ℤ)=n) (hk : n-1=k)
    (a : Cochain R X p) (c : (ordinaryComplex R R X).X q) :
    (ordinaryComplex R R X).d n k (castOrdinary R hn (cap R X p q a c)) =
      (-1:ℤ)^p •
        (castOrdinary R (by omega : (q-1)-(p:ℤ)=k)
          (cap R X p (q-1) a ((ordinaryComplex R R X).d q (q-1) c)) -
         castOrdinary R (by push_cast; omega : q-((p+1:ℕ):ℤ)=k)
          (cap R X (p+1) q (delta R X p a) c)) := by
  rw [← castOrdinary_d R hn (by omega : q-p-1=k), ordinaryBoundary]
  simp only [map_zsmul, map_sub, castOrdinary_comp]

/-- The first quotient operation is a differential cap system. -/
def absoluteSystem (P : Pair.{w}) :
    CapSystem (ordinaryCochains R R P.space) (ordinary R R P) (ordinary R R P) where
  op p q k h := (LinearMap.llcomp R _ _ _ (complexCast R (ordinary R R P) h)).comp
    (absoluteChainCap R P p q)
  boundary := by
    intro p q n k hn hk a z
    obtain ⟨c, rfl⟩ := projection_surjective R P q z
    change (ordinaryComplex R R P.space).X q at c
    simp only [LinearMap.comp_apply, LinearMap.llcomp_apply, absoluteChainCap_lift]
    rw [complexCast_map]
    rw [← ModuleCat.comp_apply, Hom.comm, ModuleCat.comp_apply]
    change (projection (ordinaryFunctor R R) P).f k
      ((ordinaryComplex R R P.space).d n k
        (complexCast R (ordinaryComplex R R P.space) hn
          (cap R P.space p q (ordinaryCochainsEquiv R R P.space p a) c))) = _
    rw [complexCast_ordinary, cap_boundary_degrees R P.space p q n k hn hk]
    simp only [map_zsmul, map_sub]
    erw [← complexCast_ordinary, ← complexCast_ordinary, ← complexCast_map, ← complexCast_map]
    congr 2
    · rw [← ModuleCat.comp_apply, Hom.comm, ModuleCat.comp_apply, absoluteChainCap_lift]
      rfl
    · simp only [P202.CupProduct.ordinaryCochainsEquiv_d]
  negative := (P202.CohomologyPairs.negative R R).1 P.space (-1) (by omega) |>.1

/-- The second quotient operation is a differential cap system. -/
def relativeSystem (P : Pair.{w}) :
    CapSystem (relativeCochains R R P) (ordinary R R P) (ordinaryComplex R R P.space) where
  op p q k h := (LinearMap.llcomp R _ _ _ (complexCast R (ordinaryComplex R R P.space) h)).comp
    (relativeChainCap R P p q)
  boundary := by
    intro p q n k hn hk a z
    obtain ⟨c, rfl⟩ := projection_surjective R P q z
    change (ordinaryComplex R R P.space).X q at c
    simp only [LinearMap.comp_apply, LinearMap.llcomp_apply, relativeChainCap_lift]
    simp only [complexCast_ordinary]
    rw [cap_boundary_degrees R P.space p q n k hn hk]
    congr 2
    · rw [← ModuleCat.comp_apply, Hom.comm, ModuleCat.comp_apply, relativeChainCap_lift]
      rfl
    · simp only [relativeValue_d]
  negative := (P202.CohomologyPairs.negative R R).2 P (-1) (by omega) |>.1

/-- The two tensor products, with the universal representative formulas. -/
def pairProductsData : PairProducts.{u,w} R where
  absolute P p q := TensorProduct.lift ((absoluteSystem R P).homologyOp p q)
  relative P p q := TensorProduct.lift ((relativeSystem R P).homologyOp p q)
  absolute_represents := by
    intro P p q a z c hc
    refine ⟨(absoluteSystem R P).cycleOp p q a z, ?_, ?_⟩
    · rw [CapSystem.cycleOp_i]
      change absoluteChainCap R P p q ((ordinaryCochains R R P.space).iCycles (p:ℤ) a)
        ((ordinary R R P).iCycles q z) = _
      rw [← hc, absoluteChainCap_lift]
      rfl
    · exact (absoluteSystem R P).homologyOp_rep p q a z
  relative_represents := by
    intro P p q a z c hc
    refine ⟨(relativeSystem R P).cycleOp p q a z, ?_, ?_⟩
    · rw [CapSystem.cycleOp_i]
      change relativeChainCap R P p q ((relativeCochains R R P).iCycles (p:ℤ) a)
        ((ordinary R R P).iCycles q z) = _
      rw [← hc, relativeChainCap_lift]
      rfl
    · exact (relativeSystem R P).homologyOp_rep p q a z
  absolute_zero_above := by
    intro P p q h
    haveI := ModuleCat.subsingleton_of_isZero
      ((P202.RelativeSingularChains.ordinary_negative R R P (q-p) (by omega)).2)
    exact Subsingleton.elim _ _
  relative_zero_above := by
    intro P p q h
    haveI := ModuleCat.subsingleton_of_isZero
      (P202.SingularChains.ordinary_negative_homology R R P.space (q-p) (by omega))
    exact Subsingleton.elim _ _

theorem pairProducts : pairProducts_type.{u,w} := fun R _ => ⟨pairProductsData R⟩

end P202.CapProducts
