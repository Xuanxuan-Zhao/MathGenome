import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.SelfDuality
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Resolution

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
universe u v
namespace AdvCommAlg.Koszul.SelfDuality
variable {R : Type u} [CommRing R]

abbrev koszulCochainComplex := @cochainComplex
abbrev koszulCohomology := @cohomology

theorem cochain_differential : Specs.AdvCommAlg.Koszul.SelfDuality.cochainDifferential.{u,v} := by
  intro R _ M _ _ x q f
  change f.comp ((listComplex x).d (q+1) q).hom = _
  congr 1
  simp [listComplex, complex]

theorem cochain_bounded : Specs.AdvCommAlg.Koszul.SelfDuality.cochainBounded.{u,v} := by
  intro R _ M _ _ x q hq
  have : Subsingleton ((listComplex x).X q) := listComplex_vanish x q hq
  change Subsingleton (((listComplex x).X q) →ₗ[R] M)
  infer_instance

/-- Computing Ext by the actual canonical Koszul projective resolution. -/
def cohomologyExtIso (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (hx : RegularSequence.RingRegular x) (q : ℕ) :
    cohomology M x q ≅ quotientExt M (listIdeal x) q :=
  (HomologicalComplex.homologyUnop _ q) ≪≫
    ((koszulResolution x hx).isoLeftDerivedObj (homCoefficient M).rightOp q).unop

theorem cohomology_ext : Specs.AdvCommAlg.Koszul.SelfDuality.cohomologyExt.{u,v} := by
  intro R _ M _ _ x hx q
  exact ⟨cohomologyExtIso M x hx q⟩

/-- Our size-polymorphic Hom functor is the usual linear Yoneda functor
when its coefficient module belongs to the source category. -/
def homCoefficientYonedaIso (M : Type u) [AddCommGroup M] [Module R M] :
    homCoefficient M ≅ (linearYoneda R (ModuleCat.{u} R)).obj (ModuleCat.of R M) :=
  NatIso.ofComponents (fun N => (ModuleCat.homLinearEquiv (S := R) (M := N.unop)
      (N := ModuleCat.of R M)).symm.toModuleIso)
    (by intros; ext; rfl)

/-- Thus the derived-Hom interface is the standard Mathlib Ext. -/
def quotientExtOrdinaryIso (M : Type u) [AddCommGroup M] [Module R M]
    (I : Ideal R) (q : ℕ) :
    quotientExt M I q ≅
      ((Ext R (ModuleCat.{u} R) q).obj (op (ModuleCat.of R (R ⧸ I)))).obj
        (ModuleCat.of R M) :=
  Iso.unop
    { hom := (NatTrans.leftDerived (homCoefficientYonedaIso M).hom.rightOp q).app _
      inv := (NatTrans.leftDerived (homCoefficientYonedaIso M).inv.rightOp q).app _
      hom_inv_id := by
        rw [← NatTrans.comp_app, ← NatTrans.leftDerived_comp,
          ← NatTrans.rightOp_comp]
        simp
        rfl
      inv_hom_id := by
        rw [← NatTrans.comp_app, ← NatTrans.leftDerived_comp,
          ← NatTrans.rightOp_comp]
        simp }

theorem ordinary_ext_comparison : Specs.AdvCommAlg.Koszul.SelfDuality.ordinaryExtComparison.{u} := by
  intro R _ M _ _ I q
  exact ⟨quotientExtOrdinaryIso M I q⟩

@[simp] theorem orientation_top_basis (x : List R) :
    orientation x (listBasis x x.length (topSubset x)) = 1 := by
  simp [orientation, LinearEquiv.funUnique, show (default : Set.powersetCard (Fin x.length) x.length) = topSubset x from rfl]

@[simp] theorem topWedge_coe (x : List R) (q p : ℕ) (h : q+p=x.length)
    (a : ⋀[R]^q (Fin x.length → R)) (b : ⋀[R]^p (Fin x.length → R)) :
    (topWedge x q p h a b : ExteriorAlgebra R (Fin x.length → R)) = a * b := by
  simp [topWedge, DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul]

/-- Complementary exterior degrees pair perfectly over every commutative ring,
including the zero ring. -/
instance scalarWedge_isPerfPair (x : List R) (q p : ℕ) (h : q+p=x.length) :
    (scalarWedge x q p h).IsPerfPair := by
  nontriviality R
  have hr : Module.finrank R (Fin x.length → R) = x.length := by simp
  let vol : (⋀[R]^(Module.finrank R (Fin x.length → R)) (Fin x.length → R)) ≃ₗ[R] R :=
    (LinearEquiv.ofEq _ _ (congrArg (fun n => ⋀[R]^n (Fin x.length → R)) hr)).trans
      (orientation x)
  have transport : ∀ (n r : ℕ) (hr : n=r)
      (vol : (⋀[R]^r (Fin x.length → R)) ≃ₗ[R] R) (h : q+p=r),
      ((exteriorPower.wedge R _ q p).compr₂
        ((LinearEquiv.ofEq _ _ (congrArg (fun n => ⋀[R]^n (Fin x.length → R)) h)).trans vol).toLinearMap) =
      (exteriorPower.wedge R _ q p).compr₂
        (h.trans hr.symm ▸ ((LinearEquiv.ofEq _ _
          (congrArg (fun n => ⋀[R]^n (Fin x.length → R)) hr)).trans vol).toLinearMap) := by
    intro n r hr vol h
    subst r
    subst n
    rfl
  have he : scalarWedge x q p h = exteriorPower.wedgePairing vol (h.trans hr.symm) :=
    transport _ _ hr (orientation x) h
  rw [he]
  infer_instance

/-- The complementary pairing transposes contraction with precisely the sign
which is cancelled by `dualitySign`. -/
theorem topWedge_differential (x : List R) (q p : ℕ) (h : q+(p+1)=x.length)
    (w : ⋀[R]^(q+1) (Fin x.length → R))
    (a : ⋀[R]^(p+1) (Fin x.length → R)) :
    topWedge x q (p+1) h (differential (listForm x) q w) a =
      (-1 : R)^q • topWedge x (q+1) p (by omega) w
        (differential (listForm x) p a) := by
  have hz : (w : ExteriorAlgebra R (Fin x.length → R)) * a = 0 := by
    have hm : (w : ExteriorAlgebra R (Fin x.length → R)) * a ∈
        ⋀[R]^(x.length+1) (Fin x.length → R) := by
      have hm := SetLike.mul_mem_graded w.property a.property
      have hh : (q+1)+(p+1)=x.length+1 := by omega
      exact hh ▸ hm
    have hs := listComplex_vanish x (x.length+1) (by omega)
    exact congrArg Subtype.val (@Subsingleton.elim _ hs ⟨_, hm⟩ 0)
  have hl := contraction_leibniz (listForm x) (q+1) w a w.property
  rw [hz, map_zero, pow_succ, mul_neg_one, neg_smul, ← sub_eq_add_neg] at hl
  apply Subtype.ext
  simpa only [topWedge_coe, SetLike.val_smul, differential_coe] using
    (sub_eq_zero.mp hl.symm)

/-- The signed perfect pairing with ordinary, oriented coefficients. -/
def orientedDegreeEquiv (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (q p : ℕ) (h : q+p=x.length) :
    ((⋀[R]^p (Fin x.length → R)) ⊗[R] M) ≃ₗ[R]
      ((⋀[R]^q (Fin x.length → R)) →ₗ[R] M) :=
  ((TensorProduct.congr (scalarWedge x q p h).flip.toPerfPair
    (LinearEquiv.refl R M)).trans
      (dualTensorHomEquivOfBasis (listBasis x q))).trans
        (LinearEquiv.smulOfUnit ((-1 : Rˣ) ^ (q*(q-1)/2)))

@[simp] theorem orientedDegreeEquiv_tmul (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (q p : ℕ) (h : q+p=x.length)
    (a : ⋀[R]^p (Fin x.length → R)) (m : M)
    (w : ⋀[R]^q (Fin x.length → R)) :
    orientedDegreeEquiv M x q p h (a ⊗ₜ[R] m) w =
      dualitySign R q • (scalarWedge x q p h w a • m) := by
  change (((-1 : Rˣ) ^ (q*(q-1)/2) : R) •
    ((scalarWedge x q p h) w a • m)) = _
  simp [dualitySign]

theorem dualitySign_succ (q : ℕ) :
    dualitySign R (q+1) = dualitySign R q * (-1 : R)^q := by
  simp only [dualitySign, ← Nat.choose_two_right]
  rw [Nat.choose_succ_succ]
  simp [pow_add, mul_comm]

/-- Oriented degree maps commute with the two actual differentials. -/
theorem orientedDegreeEquiv_comm (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (q p : ℕ) (h : q+(p+1)=x.length)
    (z : (⋀[R]^(p+1) (Fin x.length → R)) ⊗[R] M)
    (w : ⋀[R]^(q+1) (Fin x.length → R)) :
    orientedDegreeEquiv M x (q+1) p (by omega)
        (coefficientDifferential M x p z) w =
      orientedDegreeEquiv M x q (p+1) h z (differential (listForm x) q w) := by
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
    change orientedDegreeEquiv M x (q+1) p _
      (differential (listForm x) p a ⊗ₜ[R] m) w = _
    rw [orientedDegreeEquiv_tmul, orientedDegreeEquiv_tmul]
    have hl := congrArg (orientation x) (topWedge_differential x q p h w a)
    change scalarWedge x q (p+1) h (differential (listForm x) q w) a = _ at hl
    rw [map_smul] at hl
    change _ = dualitySign R q • (scalarWedge x q (p+1) h _ a • m)
    rw [hl, dualitySign_succ]
    simp only [scalarWedge, LinearMap.compr₂_apply, LinearEquiv.coe_coe, smul_eq_mul, mul_smul]
  | add z z' hz hz' =>
    simp only [map_add, LinearMap.add_apply, hz, hz']

/-- Dual orientation of the determinant line, obtained by evaluation on its
oriented generator. -/
def determinantDualOrientation (x : List R) : Module.Dual R (determinantLine x) ≃ₗ[R] R :=
  (orientation x).symm.dualMap.trans (LinearMap.ringLmapEquivSelf R R R)

/-- Trivialize the determinant twist using the specified ordered basis. -/
def untwistCoefficients (M : Type v) [AddCommGroup M] [Module R M] (x : List R) :
    (M ⊗[R] Module.Dual R (determinantLine x)) ≃ₗ[R] M :=
  (TensorProduct.congr (LinearEquiv.refl R M) (determinantDualOrientation x)).trans
    (TensorProduct.rid R M)

@[simp] theorem untwistCoefficients_tmul (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (m : M) (φ : Module.Dual R (determinantLine x)) :
    untwistCoefficients M x (m ⊗ₜ[R] φ) = φ ((orientation x).symm 1) • m := rfl

/-- The un-oriented determinant-twisted degree maps. Their formula below shows
that the temporary choice of orientation cancels completely. -/
def twistedDegreeEquiv (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (q p : ℕ) (h : q+p=x.length) :
    ((⋀[R]^p (Fin x.length → R)) ⊗[R] (M ⊗[R] Module.Dual R (determinantLine x))) ≃ₗ[R]
      ((⋀[R]^q (Fin x.length → R)) →ₗ[R] M) :=
  (TensorProduct.congr (LinearEquiv.refl R _) (untwistCoefficients M x)).trans
    (orientedDegreeEquiv M x q p h)

theorem determinant_eval (x : List R) (φ : Module.Dual R (determinantLine x))
    (d : determinantLine x) :
    φ d = orientation x d * φ ((orientation x).symm 1) := by
  have hd : d = orientation x d • (orientation x).symm 1 := by
    apply (orientation x).injective
    simp
  conv_lhs => rw [hd]
  rw [map_smul, smul_eq_mul]

@[simp] theorem twistedDegreeEquiv_tmul (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (q p : ℕ) (h : q+p=x.length)
    (a : ⋀[R]^p (Fin x.length → R)) (m : M)
    (φ : Module.Dual R (determinantLine x)) (w : ⋀[R]^q (Fin x.length → R)) :
    twistedDegreeEquiv M x q p h (a ⊗ₜ[R] (m ⊗ₜ[R] φ)) w =
      dualitySign R q • (φ (topWedge x q p h w a) • m) := by
  change orientedDegreeEquiv M x q p h
    (a ⊗ₜ[R] untwistCoefficients M x (m ⊗ₜ[R] φ)) w = _
  rw [untwistCoefficients_tmul, orientedDegreeEquiv_tmul,
    determinant_eval x φ (topWedge x q p h w a)]
  simp only [scalarWedge, LinearMap.compr₂_apply, LinearEquiv.coe_coe, mul_smul]

/-- Naturality of tensoring the chain differential with the coefficient
orientation. -/
theorem untwist_differential (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (p : ℕ)
    (z : (⋀[R]^(p+1) (Fin x.length → R)) ⊗[R]
      (M ⊗[R] Module.Dual R (determinantLine x))) :
    TensorProduct.map LinearMap.id (untwistCoefficients M x).toLinearMap
        (coefficientDifferential (M ⊗[R] Module.Dual R (determinantLine x)) x p z) =
      coefficientDifferential M x p
        (TensorProduct.map LinearMap.id (untwistCoefficients M x).toLinearMap z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a m => rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

/-- The complete signed, determinant-twisted exterior cochain pairing. -/
def signedDualityData (M : Type v) [AddCommGroup M] [Module R M] (x : List R) :
    SignedDualityData M x where
  equiv := twistedDegreeEquiv M x
  formula := twistedDegreeEquiv_tmul M x
  comm q p h z w := by
    change orientedDegreeEquiv M x (q+1) p _
      (TensorProduct.map LinearMap.id (untwistCoefficients M x).toLinearMap
        (coefficientDifferential _ x p z)) w = _
    rw [untwist_differential, orientedDegreeEquiv_comm]
    rfl

theorem signed_self_duality : Specs.AdvCommAlg.Koszul.SelfDuality.signedSelfDuality.{u,v} := by
  intro R _ M _ _ x
  exact ⟨signedDualityData M x⟩

/-- A cycle belongs to the boundary submodule precisely when its underlying
vector is a boundary in the middle term. -/
private theorem mem_boundaries_iff (S : ShortComplex (ModuleCat.{v} R))
    (z : LinearMap.ker S.g.hom) :
    z ∈ LinearMap.range S.moduleCatToCycles ↔ (z : S.X₂) ∈ LinearMap.range S.f.hom := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

/-- An equivalence preserving cycles and boundaries descends to homology.
This form handles the two ends of a bounded complex without identifying
irrelevant outer terms of short complexes. -/
def homologyEquivOfCyclesBoundaries (S T : ShortComplex (ModuleCat.{v} R))
    (e : S.X₂ ≃ₗ[R] T.X₂)
    (hc : ∀ a, S.g.hom a = 0 ↔ T.g.hom (e a) = 0)
    (hb : ∀ a, a ∈ LinearMap.range S.f.hom ↔ e a ∈ LinearMap.range T.f.hom) :
    S.homology ≃ₗ[R] T.homology := by
  have hk : (LinearMap.ker S.g.hom).map e.toLinearMap = LinearMap.ker T.g.hom := by
    ext y
    rw [Submodule.mem_map_equiv]
    change S.g.hom (e.symm y) = 0 ↔ T.g.hom y = 0
    simpa using hc (e.symm y)
  let ek := e.ofSubmodules (LinearMap.ker S.g.hom) (LinearMap.ker T.g.hom) hk
  have hr : (LinearMap.range S.moduleCatToCycles).map ek.toLinearMap =
      LinearMap.range T.moduleCatToCycles := by
    ext z
    rw [Submodule.mem_map_equiv, mem_boundaries_iff, mem_boundaries_iff]
    change (e.symm (z : T.X₂)) ∈ LinearMap.range S.f.hom ↔
      (z : T.X₂) ∈ LinearMap.range T.f.hom
    simpa using hb (e.symm (z : T.X₂))
  exact S.moduleCatHomologyIso.toLinearEquiv.trans
    ((Submodule.Quotient.equiv _ _ ek hr).trans T.moduleCatHomologyIso.toLinearEquiv.symm)

private abbrev cochainWindow (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (q : ℕ) := (cochainComplex M x).sc' (q-1) q (q+1)

private abbrev chainWindow (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (p : ℕ) := (coefficientComplex M x).sc' (p+1) p (p-1)

private theorem up_prev (q : ℕ) : (ComplexShape.up ℕ).prev q = q-1 := by
  cases q with
  | zero => exact ComplexShape.prev_eq_self' _ _ (by intro i h; change i+1=0 at h; omega)
  | succ q => exact ComplexShape.prev_eq' _ rfl

private theorem down_next (p : ℕ) : (ComplexShape.down ℕ).next p = p-1 := by
  cases p with
  | zero => exact ComplexShape.next_eq_self' _ _ (by intro i h; change i+1=0 at h; omega)
  | succ p => exact ComplexShape.next_eq' _ rfl

private theorem cochain_sc_g (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (q : ℕ) (f : (⋀[R]^q (Fin x.length → R)) →ₗ[R] M) :
    (cochainWindow M x q).g.hom f = f.comp (differential (listForm x) q) :=
  cochain_differential M x q f

private theorem cochain_sc_f_succ (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (q : ℕ) :
    (cochainWindow M x (q+1)).f = (cochainComplex M x).d q (q+1) := rfl

private theorem cochain_sc_f_zero (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) : (cochainWindow M x 0).f = 0 := by
  change (cochainComplex M x).d 0 0 = 0
  exact HomologicalComplex.shape _ _ _ (by intro h; change 0+1=0 at h; omega)

private theorem chain_sc_f (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (p : ℕ) :
    (chainWindow M x p).f.hom = coefficientDifferential M x p := by
  change ((coefficientComplex M x).d (p+1) p).hom = _
  simp [coefficientComplex]

private theorem chain_sc_g_succ (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (p : ℕ) :
    (chainWindow M x (p+1)).g.hom = coefficientDifferential M x p := by
  change ((coefficientComplex M x).d (p+1) p).hom = _
  simp [coefficientComplex]

private theorem chain_sc_g_zero (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) : (chainWindow M x 0).g = 0 := by
  change (coefficientComplex M x).d 0 0 = 0
  exact HomologicalComplex.shape _ _ _ (by intro h; change 0+1=0 at h; omega)

private theorem oriented_cycles_iff (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (q p : ℕ) (h : q+p=x.length)
    (a : (coefficientComplex M x).X p) :
    (chainWindow M x p).g.hom a = 0 ↔
      (cochainWindow M x q).g.hom (orientedDegreeEquiv M x q p h a) = 0 := by
  rw [cochain_sc_g]
  cases p with
  | zero =>
    rw [chain_sc_g_zero]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, true_iff]
    have hs : Subsingleton (⋀[R]^(q+1) (Fin x.length → R)) :=
      listComplex_vanish x (q+1) (by omega)
    exact @Subsingleton.elim
      ((⋀[R]^(q+1) (Fin x.length → R)) →ₗ[R] M) (by infer_instance) _ _
  | succ p =>
    rw [chain_sc_g_succ]
    have he : orientedDegreeEquiv M x (q+1) p (by omega)
        (coefficientDifferential M x p a) =
        (orientedDegreeEquiv M x q (p+1) h a).comp (differential (listForm x) q) := by
      apply LinearMap.ext
      intro w
      exact orientedDegreeEquiv_comm M x q p h a w
    rw [← he]
    constructor
    · intro ha
      exact (congrArg (orientedDegreeEquiv M x (q+1) p (by omega)) ha).trans (map_zero _)
    · intro ha
      exact (orientedDegreeEquiv M x (q+1) p (by omega)).injective
        (ha.trans (map_zero _).symm)

private theorem oriented_boundaries_iff (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (q p : ℕ) (h : q+p=x.length)
    (a : (coefficientComplex M x).X p) :
    a ∈ LinearMap.range (chainWindow M x p).f.hom ↔
      orientedDegreeEquiv M x q p h a ∈
        LinearMap.range (cochainWindow M x q).f.hom := by
  rw [chain_sc_f]
  cases q with
  | zero =>
    rw [cochain_sc_f_zero]
    have hs : Subsingleton ((⋀[R]^(p+1) (Fin x.length → R)) ⊗[R] M) :=
      coefficientComplex_vanish M x (p+1) (by omega)
    have hd : coefficientDifferential M x p = 0 := Subsingleton.elim _ _
    rw [hd]
    simp
  | succ q =>
    rw [cochain_sc_f_succ]
    let ep := orientedDegreeEquiv M x q (p+1) (by omega)
    have he (z : (⋀[R]^(p+1) (Fin x.length → R)) ⊗[R] M) :
        orientedDegreeEquiv M x (q+1) p h (coefficientDifferential M x p z) =
          ((cochainComplex M x).d q (q+1)).hom (ep z) := by
      rw [cochain_differential]
      apply LinearMap.ext
      intro w
      exact orientedDegreeEquiv_comm M x q p (by omega) z w
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨ep z, (he z).symm⟩
    · rintro ⟨f, hf⟩
      obtain ⟨z, rfl⟩ := ep.surjective f
      exact ⟨z, (orientedDegreeEquiv M x (q+1) p h).injective ((he z).trans hf)⟩

/-- The cohomological form of self-duality, including both ends of the complex. -/
def cohomologyDualityEquiv (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (q p : ℕ) (h : q+p=x.length) :
    cohomology M x q ≃ₗ[R] homology M x p :=
  ((cochainComplex M x).homologyIsoSc' (q-1) q (q+1)
    (up_prev q) (ComplexShape.next_eq' _ rfl)).toLinearEquiv.trans
    ((homologyEquivOfCyclesBoundaries (chainWindow M x p)
      (cochainWindow M x q) (orientedDegreeEquiv M x q p h)
      (oriented_cycles_iff M x q p h) (oriented_boundaries_iff M x q p h)).symm.trans
      ((coefficientComplex M x).homologyIsoSc' (p+1) p (p-1)
        (ComplexShape.prev_eq' _ rfl) (down_next p)).toLinearEquiv.symm)

/-- The Hom complex and its cohomology are both zero above r. -/
theorem cohomology_vanish (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (q : ℕ) (hq : x.length < q) : Subsingleton (cohomology M x q) := by
  apply ModuleCat.isZero_iff_subsingleton.mp
  exact HomologicalComplex.ExactAt.isZero_homology
    (HomologicalComplex.ExactAt.of_isZero
      (ModuleCat.isZero_iff_subsingleton.mpr (cochain_bounded M x q hq)))

theorem cohomology_duality : Specs.AdvCommAlg.Koszul.SelfDuality.cohomologyDuality.{u,v} := by
  intro R _ M _ _ x q
  exact ⟨fun hq => ⟨cohomologyDualityEquiv M x q (x.length-q) (by omega)⟩,
    cohomology_vanish M x q⟩

/-- The ring coefficient quotient is canonically R/(x). -/
def ringCoefficientQuotientEquiv (x : List R) :
    (R ⧸ listSubmodule R x) ≃ₗ[R] (R ⧸ listIdeal x) :=
  Submodule.quotEquivOfEq _ _ (by
    simp only [listSubmodule, Ideal.smul_eq_mul, Ideal.mul_top])

/-- Ext is concentrated in degree r, with the oriented top Ext equal to R/(x). -/
theorem ext_concentration : Specs.AdvCommAlg.Koszul.SelfDuality.extConcentration.{u} := by
  intro R _ x hx
  constructor
  · intro q hq
    apply IsZero.of_iso _ (cohomologyExtIso R x hx q).symm
    by_cases h : q ≤ x.length
    · have hp : 0 < x.length-q := by omega
      have hz : IsZero (homology R x (x.length-q)) :=
        ModuleCat.isZero_iff_subsingleton.mpr
          (weaklyRegular_acyclic R x hx.toIsWeaklyRegular _ hp)
      exact hz.of_iso (cohomologyDualityEquiv R x q (x.length-q) (by omega)).toModuleIso
    · exact ModuleCat.isZero_iff_subsingleton.mpr (cohomology_vanish R x q (by omega))
  · exact ⟨(cohomologyExtIso R x hx x.length).symm.toLinearEquiv.trans
      ((cohomologyDualityEquiv R x x.length 0 (by omega)).trans
        ((homologyZeroEquiv R x).trans (ringCoefficientQuotientEquiv x)))⟩

end AdvCommAlg.Koszul.SelfDuality
