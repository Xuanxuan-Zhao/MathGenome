import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.RegularQuotientComputation
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtTorDefinitions

namespace P103.Ch11.RegularQuotientComputation
open CategoryTheory
open P103.Specs.Ch10.ProjectiveResolutions
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions hiding extModule torModule
open P103.Specs.Ch11.RegularQuotientComputation
noncomputable section
set_option maxHeartbeats 1000000
universe u v

section Resolution
variable {S : Type u} [Ring S] {M : Type u} [AddCommGroup M] [Module S M]

/-- Exact augmentation of the two-term complex of an injective endomorphism. -/
def twoTermResolution (d : M →ₗ[S] M) (hd : Function.Injective d) :
    Resolution S (M ⧸ LinearMap.range d) where
  complex := twoTerm d
  ε := (LinearMap.range d).mkQ
  surjective := Submodule.mkQ_surjective (LinearMap.range d)
  exact_zero := by
    rw [twoTerm_d]
    exact (Submodule.ker_mkQ _).symm
  exact_succ n := by
    cases n with
    | zero =>
      rw [twoTerm_d, twoTerm_d]
      change LinearMap.range (0 : PUnit →ₗ[S] M) = LinearMap.ker d
      rw [LinearMap.range_zero, LinearMap.ker_eq_bot.mpr hd]
    | succ n =>
      rw [twoTerm_d, twoTerm_d]
      change LinearMap.range (0 : PUnit.{u+1} →ₗ[S] PUnit.{u+1}) = LinearMap.ker (0 : PUnit.{u+1} →ₗ[S] term (S := S) M (n+1))
      ext x
      constructor
      · intro _; rfl
      · intro _; exact ⟨0, Subsingleton.elim _ _⟩

theorem twoTermResolution_free (d : M →ₗ[S] M) (hd : Function.Injective d)
    [Module.Free S M] : (twoTermResolution d hd).IsFree := by
  intro n
  match n with
  | 0 => change Module.Free S M; infer_instance
  | 1 => change Module.Free S M; infer_instance
  | n + 2 => change Module.Free S PUnit; infer_instance

end Resolution

variable {R : Type u} [CommRing R]

/-- The right regular module is rank-one free over the opposite ring. -/
def rightRegularEquiv : Rᵐᵒᵖ ≃ₗ[Rᵐᵒᵖ] R where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem free_resolution : free_resolutionType.{u} := by
  intro R _ r hr
  letI : Module.Free Rᵐᵒᵖ R := Module.Free.of_equiv (rightRegularEquiv (R := R))
  constructor
  · exact ⟨twoTermResolution (multiply r) hr, rfl, HEq.rfl,
      twoTermResolution_free _ _⟩
  · have hr' : Function.Injective (rightMultiply r) := hr
    exact ⟨twoTermResolution (rightMultiply r) hr', rfl, HEq.rfl,
      twoTermResolution_free _ _⟩

theorem not_resolution : not_resolutionType.{u} := by
  intro R _ r ⟨a, ha, hra⟩ ⟨P, hP⟩
  have hex := P.exact_succ 0
  rw [hP, twoTerm_d, twoTerm_d] at hex
  change LinearMap.range (0 : PUnit →ₗ[R] R) = LinearMap.ker (multiply r) at hex
  have ha' : a ∈ LinearMap.ker (multiply r) := hra
  rw [← hex] at ha'
  obtain ⟨x, hx⟩ := ha'
  exact ha hx.symm

/-- Descent of a surjection on cycles whose kernel is exactly the boundaries. -/
def homologyEquiv {S : Type*} [Ring S] {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} S) c) (n : ι)
    {T : Type*} [AddCommGroup T] [Module S T] (f : cycles C n →ₗ[S] T)
    (hf : Function.Surjective f) (hk : cycleBoundaries C n = LinearMap.ker f) :
    Homology C n ≃ₗ[S] T :=
  (Submodule.quotEquivOfEq _ _ hk).trans (f.quotKerEquivOfSurjective hf)

theorem homologyEquiv_class {S : Type*} [Ring S] {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} S) c) (n : ι)
    {T : Type*} [AddCommGroup T] [Module S T] (f : cycles C n →ₗ[S] T)
    (hf : Function.Surjective f) (hk : cycleBoundaries C n = LinearMap.ker f)
    (z : cycles C n) : homologyEquiv C n f hf hk (homologyClass C n z) = f z :=
  LinearMap.quotKerEquivOfSurjective_apply_mk f hf z

theorem ext_higher (r : R) (B : Type v) [AddCommGroup B] [Module R B] (n : ℕ) :
    Subsingleton (Ext r B (n+2)) := by
  letI : Subsingleton ((homComplex (leftComplex r) B).X (n+2)) := by
    change Subsingleton (PUnit.{u+1} →ₗ[R] B)
    infer_instance
  infer_instance

theorem tor_higher (r : R) (B : Type v) [AddCommGroup B] [Module R B] (n : ℕ) :
    Subsingleton (Tor r B (n+2)) := by
  letI : Subsingleton ((tensorComplex (rightComplex r) B).X (n+2)) := by
    change Subsingleton (P103.BalancedTensor.Tensor R PUnit.{u+1} B)
    exact ⟨fun x y => (P103.BalancedTensor.eq_zero_of_subsingleton_left x).trans
      (P103.BalancedTensor.eq_zero_of_subsingleton_left y).symm⟩
  infer_instance

section ExtComputation
variable (r : R) (B : Type v) [AddCommGroup B] [Module R B]

/-- Evaluation of an R-linear map R → B is its value at one. -/
abbrev evaluate := LinearMap.ringLmapEquivSelf R ℤ B

/-- The cocycle condition in degree zero is r times the value at one equals zero. -/
def extZeroCycle : cycles (homComplex (leftComplex r) B) 0 →ₗ[ℤ] Torsion r B :=
  ((evaluate (R := R) B).toLinearMap.comp (cycles (homComplex (leftComplex r) B) 0).subtype).codRestrict ((Torsion r B).restrictScalars ℤ) (by
    intro z
    let h : R →ₗ[R] B := z.val
    have hz := z.property
    change ((homComplex (leftComplex r) B).d 0 ((ComplexShape.up ℕ).next 0)).hom z.val = 0 at hz
    rw [CochainComplex.next] at hz
    change h.comp ((leftComplex r).d 1 0).hom = 0 at hz
    rw [twoTerm_d] at hz
    change h.comp (multiply r) = 0 at hz
    change r • h 1 = 0
    have he := LinearMap.congr_fun hz 1
    change h (r * 1) = 0 at he
    simpa only [mul_one, ← h.map_smul, smul_eq_mul] using he)

/-- The cochain taking a to a • b. -/
abbrev cochainOf (b : B) : R →ₗ[R] B := (evaluate (R := R) B).symm b

theorem cochainOf_mul (b : B) :
    (cochainOf (R := R) B b).comp (multiply r) = cochainOf (R := R) B (r • b) := by
  apply (evaluate (R := R) B).injective
  change (r * (1 : R)) • b = (1 : R) • (r • b)
  simp

theorem extZeroCycle_surjective : Function.Surjective (extZeroCycle r B) := by
  intro b
  refine ⟨⟨cochainOf (R := R) B b.val, ?_⟩, Subtype.ext ?_⟩
  · change ((homComplex (leftComplex r) B).d 0 ((ComplexShape.up ℕ).next 0)).hom _ = 0
    rw [CochainComplex.next]
    change (cochainOf (R := R) B b.val).comp (multiply r) = 0
    rw [cochainOf_mul]
    have hb : r • b.val = 0 := b.property
    rw [hb]
    exact (evaluate (R := R) B).symm.map_zero
  · exact (evaluate (R := R) B).apply_symm_apply b.val

theorem extZeroCycle_kernel :
    cycleBoundaries (homComplex (leftComplex r) B) 0 = LinearMap.ker (extZeroCycle r B) := by
  rw [P103.Ch11.ExtTorDefinitions.cochain_zero_boundaries]
  symm
  apply LinearMap.ker_eq_bot.mpr
  intro z z' h
  apply Subtype.ext
  apply (evaluate (R := R) B).injective
  change (evaluate (R := R) B) z.val = (evaluate (R := R) B) z'.val
  exact congrArg Subtype.val h

def extZeroAdd : Ext r B 0 ≃+ Torsion r B :=
  (homologyEquiv _ 0 (extZeroCycle r B) (extZeroCycle_surjective r B) (extZeroCycle_kernel r B)).toAddEquiv

@[simp] theorem extZeroAdd_class (z : cycles (homComplex (leftComplex r) B) 0) :
    extZeroAdd r B (homologyClass _ 0 z) = extZeroCycle r B z :=
  homologyEquiv_class (homComplex (leftComplex r) B) 0 (extZeroCycle r B)
    (extZeroCycle_surjective r B) (extZeroCycle_kernel r B) z

/-- Every degree-one cochain is a cocycle, since the next resolution term is zero. -/
def oneCocycle (h : R →ₗ[R] B) : cycles (homComplex (leftComplex r) B) 1 := by
  refine ⟨h, ?_⟩
  change ((homComplex (leftComplex r) B).d 1 ((ComplexShape.up ℕ).next 1)).hom h = 0
  rw [CochainComplex.next]
  change h.comp ((leftComplex r).d 2 1).hom = 0
  rw [twoTerm_d]
  exact LinearMap.comp_zero _

def extOneCycle : cycles (homComplex (leftComplex r) B) 1 →ₗ[ℤ] Modulo r B :=
  (LinearMap.range (scalar r B)).mkQ.toAddMonoidHom.toIntLinearMap.comp
    ((evaluate (R := R) B).toLinearMap.comp (cycles (homComplex (leftComplex r) B) 1).subtype)

theorem extOneCycle_surjective : Function.Surjective (extOneCycle r B) := by
  intro x
  obtain ⟨b, rfl⟩ := (LinearMap.range (scalar r B)).mkQ_surjective x
  refine ⟨oneCocycle r B (cochainOf (R := R) B b), ?_⟩
  change (LinearMap.range (scalar r B)).mkQ ((evaluate (R := R) B) ((evaluate (R := R) B).symm b)) = _
  rw [LinearEquiv.apply_symm_apply]

theorem modulo_eq_zero (b : B) :
    (LinearMap.range (scalar r B)).mkQ b = 0 ↔ ∃ c : B, r • c = b := by
  change b ∈ LinearMap.ker (LinearMap.range (scalar r B)).mkQ ↔ _
  rw [Submodule.ker_mkQ]
  rfl

theorem eval_precomp (h : R →ₗ[R] B) : (h.comp (multiply r)) 1 = r • h 1 := by
  change h (r * 1) = r • h 1
  rw [mul_one]
  simpa only [smul_eq_mul, mul_one] using h.map_smul r 1

theorem extOneCycle_kernel :
    cycleBoundaries (homComplex (leftComplex r) B) 1 = LinearMap.ker (extOneCycle r B) := by
  ext z
  change (∃ h, ((homComplex (leftComplex r) B).d ((ComplexShape.up ℕ).prev 1) 1).hom h = z.val) ↔
    (LinearMap.range (scalar r B)).mkQ ((evaluate (R := R) B) z.val) = 0
  rw [CochainComplex.prev_nat_succ, modulo_eq_zero]
  change (∃ h : R →ₗ[R] B, h.comp ((leftComplex r).d 1 0).hom = z.val) ↔ _
  rw [twoTerm_d]
  change (∃ h : R →ₗ[R] B, h.comp (multiply r) = z.val) ↔ _
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h 1, ?_⟩
    rw [← hh]
    exact (eval_precomp r B h).symm
  · rintro ⟨b, hb⟩
    refine ⟨cochainOf (R := R) B b, ?_⟩
    apply (evaluate (R := R) B).injective
    change ((cochainOf (R := R) B b).comp (multiply r)) 1 = (evaluate (R := R) B) z.val
    rw [eval_precomp]
    change r • ((evaluate (R := R) B) ((evaluate (R := R) B).symm b)) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hb

def extOneAdd : Ext r B 1 ≃+ Modulo r B :=
  (homologyEquiv _ 1 (extOneCycle r B) (extOneCycle_surjective r B) (extOneCycle_kernel r B)).toAddEquiv

@[simp] theorem extOneAdd_class (z : cycles (homComplex (leftComplex r) B) 1) :
    extOneAdd r B (homologyClass _ 1 z) = extOneCycle r B z :=
  homologyEquiv_class (homComplex (leftComplex r) B) 1 (extOneCycle r B)
    (extOneCycle_surjective r B) (extOneCycle_kernel r B) z

variable {B}
theorem extZeroAdd_natural {B' : Type v} [AddCommGroup B'] [Module R B']
    (g : B →ₗ[R] B') (x : Ext r B 0) :
    extZeroAdd r B' (homologyMap (homPostMap (leftComplex r) g) 0 x) =
      torsionMap r g (extZeroAdd r B x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ z =>
    change extZeroAdd r B' (homologyClass _ 0 (cyclesMap (homPostMap (leftComplex r) g) 0 z)) =
      torsionMap r g (extZeroAdd r B (homologyClass _ 0 z))
    rw [extZeroAdd_class, extZeroAdd_class]
    rfl

theorem extOneAdd_natural {B' : Type v} [AddCommGroup B'] [Module R B']
    (g : B →ₗ[R] B') (x : Ext r B 1) :
    extOneAdd r B' (homologyMap (homPostMap (leftComplex r) g) 1 x) =
      moduloMap r g (extOneAdd r B x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ z =>
    change extOneAdd r B' (homologyClass _ 1 (cyclesMap (homPostMap (leftComplex r) g) 1 z)) =
      moduloMap r g (extOneAdd r B (homologyClass _ 1 z))
    rw [extOneAdd_class, extOneAdd_class]
    rfl

variable (B)
def extZeroLinear : Ext r B 0 ≃ₗ[R] Torsion r B where
  __ := extZeroAdd r B
  map_smul' s x := extZeroAdd_natural r (scalarMap (ModuleCat.of R B) s).hom x

theorem moduloMap_scalar (s : R) (x : Modulo r B) :
    moduloMap r (scalarMap (ModuleCat.of R B) s).hom x = s • x := by
  induction x using Submodule.Quotient.induction_on with
  | _ b => rfl

def extOneLinear : Ext r B 1 ≃ₗ[R] Modulo r B where
  __ := extOneAdd r B
  map_smul' s x := by
    change extOneAdd r B (homologyMap
      (homPostMap (leftComplex r) (scalarMap (ModuleCat.of R B) s).hom) 1 x) = _
    rw [extOneAdd_natural, moduloMap_scalar]
    rfl

end ExtComputation

theorem ext_computation : ext_computationType.{u,v} := by
  intro R _ r _hr
  exact ⟨{
    zero := fun B => extZeroLinear r B
    one := fun B => extOneLinear r B
    zero_natural := fun g x => extZeroAdd_natural r g.hom x
    one_natural := fun g x => extOneAdd_natural r g.hom x
    higher := fun B n => ext_higher r B n }⟩


section TorComputation
open P103.BalancedTensor (Tensor tmul leftUnit)
variable (r : R) (B : Type v) [AddCommGroup B] [Module R B]

/-- The differential tensored with B is multiplication by r under R ⊗ B ≃ B. -/
theorem tensor_multiply (z : Tensor R R B) :
    (leftUnit (R := R) (B := B)) (tensorMap (rightMultiply r) (LinearMap.id : B →ₗ[R] B) z) =
      r • ((leftUnit (R := R) (B := B)) z : B) := by
  induction z using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ht a b =>
    change (r * a) • b = r • (a • b)
    exact mul_smul _ _ _
  | ha z z' hz hz' => simp [hz, hz', smul_add]

/-- Cycles in tensor degree one are the elements killed by r. -/
def torOneCycle : cycles (tensorComplex (rightComplex r) B) 1 →ₗ[ℤ] Torsion r B :=
  ((leftUnit (R := R) (B := B)).toAddMonoidHom.toIntLinearMap.comp
    (cycles (tensorComplex (rightComplex r) B) 1).subtype).codRestrict
      ((Torsion r B).restrictScalars ℤ) (by
    intro z
    have hz := z.property
    change ((tensorComplex (rightComplex r) B).d 1 ((ComplexShape.down ℕ).next 1)).hom z.val = 0 at hz
    rw [ChainComplex.next_nat_succ] at hz
    change tensorMap ((rightComplex r).d 1 0).hom (LinearMap.id : B →ₗ[R] B) z.val = 0 at hz
    rw [twoTerm_d] at hz
    change tensorMap (rightMultiply r) (LinearMap.id : B →ₗ[R] B) z.val = 0 at hz
    change r • ((leftUnit (R := R) (B := B)) z.val : B) = 0
    exact (tensor_multiply r B z.val).symm.trans
      ((congrArg (leftUnit (R := R) (B := B)) hz).trans (map_zero _)))

theorem torOneCycle_surjective : Function.Surjective (torOneCycle r B) := by
  intro b
  refine ⟨⟨(leftUnit (R := R) (B := B)).symm b.val, ?_⟩, Subtype.ext ?_⟩
  · change ((tensorComplex (rightComplex r) B).d 1 ((ComplexShape.down ℕ).next 1)).hom _ = 0
    rw [ChainComplex.next_nat_succ]
    change tensorMap ((rightComplex r).d 1 0).hom (LinearMap.id : B →ₗ[R] B) _ = 0
    rw [twoTerm_d]
    change tensorMap (rightMultiply r) (LinearMap.id : B →ₗ[R] B) _ = 0
    apply (leftUnit (R := R) (B := B)).injective
    rw [map_zero, tensor_multiply, AddEquiv.apply_symm_apply]
    exact b.property
  · exact (leftUnit (R := R) (B := B)).apply_symm_apply b.val

theorem torOneCycle_kernel :
    cycleBoundaries (tensorComplex (rightComplex r) B) 1 = LinearMap.ker (torOneCycle r B) := by
  have hb : cycleBoundaries (tensorComplex (rightComplex r) B) 1 = ⊥ := by
    ext z
    change (∃ y, ((tensorComplex (rightComplex r) B).d ((ComplexShape.down ℕ).prev 1) 1).hom y = z.val) ↔ z = 0
    rw [ChainComplex.prev]
    constructor
    · rintro ⟨y, hy⟩
      change Tensor R PUnit.{u+1} B at y
      have hy0 : y = 0 := P103.BalancedTensor.eq_zero_of_subsingleton_left y
      apply Subtype.ext
      exact hy.symm.trans ((congrArg
        ((tensorComplex (rightComplex r) B).d (1+1) 1).hom hy0).trans (map_zero _))
    · rintro rfl
      exact ⟨0, map_zero _⟩
  rw [hb]
  symm
  apply LinearMap.ker_eq_bot.mpr
  intro z z' h
  apply Subtype.ext
  apply (leftUnit (R := R) (B := B)).injective
  exact congrArg Subtype.val h

def torOneAdd : Tor r B 1 ≃+ Torsion r B :=
  (homologyEquiv _ 1 (torOneCycle r B) (torOneCycle_surjective r B) (torOneCycle_kernel r B)).toAddEquiv

@[simp] theorem torOneAdd_class (z : cycles (tensorComplex (rightComplex r) B) 1) :
    torOneAdd r B (homologyClass _ 1 z) = torOneCycle r B z :=
  homologyEquiv_class (tensorComplex (rightComplex r) B) 1 (torOneCycle r B)
    (torOneCycle_surjective r B) (torOneCycle_kernel r B) z

/-- Degree-zero tensor homology is the cokernel of multiplication by r. -/
def torZeroCycle : cycles (tensorComplex (rightComplex r) B) 0 →ₗ[ℤ] Modulo r B :=
  (LinearMap.range (scalar r B)).mkQ.toAddMonoidHom.toIntLinearMap.comp
    ((leftUnit (R := R) (B := B)).toAddMonoidHom.toIntLinearMap.comp
      (cycles (tensorComplex (rightComplex r) B) 0).subtype)

theorem torZeroCycle_surjective : Function.Surjective (torZeroCycle r B) := by
  intro x
  obtain ⟨b, rfl⟩ := (LinearMap.range (scalar r B)).mkQ_surjective x
  refine ⟨⟨(leftUnit (R := R) (B := B)).symm b, P103.Ch11.ExtTorDefinitions.chain_mem_zero_cycles _ _⟩, ?_⟩
  change (LinearMap.range (scalar r B)).mkQ ((leftUnit (R := R) (B := B)) ((leftUnit (R := R) (B := B)).symm b)) = _
  rw [AddEquiv.apply_symm_apply]

theorem torZeroCycle_kernel :
    cycleBoundaries (tensorComplex (rightComplex r) B) 0 = LinearMap.ker (torZeroCycle r B) := by
  ext z
  change (∃ y, ((tensorComplex (rightComplex r) B).d ((ComplexShape.down ℕ).prev 0) 0).hom y = z.val) ↔
    (LinearMap.range (scalar r B)).mkQ ((leftUnit (R := R) (B := B)) z.val) = 0
  rw [ChainComplex.prev, modulo_eq_zero]
  change (∃ y, tensorMap ((rightComplex r).d 1 0).hom (LinearMap.id : B →ₗ[R] B) y = z.val) ↔ _
  rw [twoTerm_d]
  change (∃ y : Tensor R R B, tensorMap (rightMultiply r) (LinearMap.id : B →ₗ[R] B) y = z.val) ↔ _
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(leftUnit (R := R) (B := B)) y, ?_⟩
    rw [← hy, tensor_multiply]
  · rintro ⟨b, hb⟩
    refine ⟨(leftUnit (R := R) (B := B)).symm b, ?_⟩
    apply (leftUnit (R := R) (B := B)).injective
    rw [tensor_multiply, AddEquiv.apply_symm_apply]
    exact hb

def torZeroAdd : Tor r B 0 ≃+ Modulo r B :=
  (homologyEquiv _ 0 (torZeroCycle r B) (torZeroCycle_surjective r B) (torZeroCycle_kernel r B)).toAddEquiv

@[simp] theorem torZeroAdd_class (z : cycles (tensorComplex (rightComplex r) B) 0) :
    torZeroAdd r B (homologyClass _ 0 z) = torZeroCycle r B z :=
  homologyEquiv_class (tensorComplex (rightComplex r) B) 0 (torZeroCycle r B)
    (torZeroCycle_surjective r B) (torZeroCycle_kernel r B) z

variable {B}
theorem tensorUnit_natural {B' : Type v} [AddCommGroup B'] [Module R B']
    (g : B →ₗ[R] B') (z : Tensor R R B) :
    (leftUnit (R := R) (B := B'))
      (tensorMap (LinearMap.id : R →ₗ[Rᵐᵒᵖ] R) g z) =
      g ((leftUnit (R := R) (B := B)) z) := by
  induction z using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ht a b =>
    change a • g b = g (a • b)
    exact (g.map_smul a b).symm
  | ha z z' hz hz' => simp [hz, hz']

theorem torOneAdd_natural {B' : Type v} [AddCommGroup B'] [Module R B']
    (g : B →ₗ[R] B') (x : Tor r B 1) :
    torOneAdd r B' (homologyMap (tensorSecondMap (rightComplex r) g) 1 x) =
      torsionMap r g (torOneAdd r B x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ z =>
    change torOneAdd r B' (homologyClass _ 1 (cyclesMap (tensorSecondMap (rightComplex r) g) 1 z)) =
      torsionMap r g (torOneAdd r B (homologyClass _ 1 z))
    rw [torOneAdd_class, torOneAdd_class]
    apply Subtype.ext
    exact tensorUnit_natural g z.val

theorem torZeroAdd_natural {B' : Type v} [AddCommGroup B'] [Module R B']
    (g : B →ₗ[R] B') (x : Tor r B 0) :
    torZeroAdd r B' (homologyMap (tensorSecondMap (rightComplex r) g) 0 x) =
      moduloMap r g (torZeroAdd r B x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ z =>
    change torZeroAdd r B' (homologyClass _ 0 (cyclesMap (tensorSecondMap (rightComplex r) g) 0 z)) =
      moduloMap r g (torZeroAdd r B (homologyClass _ 0 z))
    rw [torZeroAdd_class, torZeroAdd_class]
    exact congrArg (LinearMap.range (scalar r B')).mkQ (tensorUnit_natural g z.val)

variable (B)
def torOneLinear : Tor r B 1 ≃ₗ[R] Torsion r B where
  __ := torOneAdd r B
  map_smul' s x := torOneAdd_natural r (scalarMap (ModuleCat.of R B) s).hom x

def torZeroLinear : Tor r B 0 ≃ₗ[R] Modulo r B where
  __ := torZeroAdd r B
  map_smul' s x := by
    change torZeroAdd r B (homologyMap
      (tensorSecondMap (rightComplex r) (scalarMap (ModuleCat.of R B) s).hom) 0 x) = _
    rw [torZeroAdd_natural, moduloMap_scalar]
    rfl

end TorComputation

theorem tor_computation : tor_computationType.{u,v} := by
  intro R _ r _hr
  exact ⟨{
    zero := fun B => torZeroLinear r B
    one := fun B => torOneLinear r B
    zero_natural := fun g x => torZeroAdd_natural r g.hom x
    one_natural := fun g x => torOneAdd_natural r g.hom x
    higher := fun B n => tor_higher r B n }⟩


/-- The full calculation, including the bridge to the shared ExtWith/TorWith
objects, uses the displayed free resolutions of the same quotient R/(r). -/
theorem regular_computation : regular_computationType.{u,v} := by
  intro R _ r hr
  obtain ⟨⟨P, hP, hεP, hfP⟩, ⟨Q, hQ, hεQ, hfQ⟩⟩ := free_resolution R r hr
  obtain ⟨e⟩ := ext_computation.{u,v} R r hr
  obtain ⟨t⟩ := tor_computation.{u,v} R r hr
  exact ⟨{
    left := P
    left_shape := hP
    left_augmentation := hεP
    left_free := hfP
    left_model := fun B n => by
      change Homology (homComplex P.complex B) n = _
      rw [hP]
    right := Q
    right_shape := hQ
    right_augmentation := hεQ
    right_free := hfQ
    right_model := fun B n => by
      change Homology (tensorComplex Q.complex B) n = _
      rw [hQ]
    ext := e
    tor := t }⟩

end
end P103.Ch11.RegularQuotientComputation
