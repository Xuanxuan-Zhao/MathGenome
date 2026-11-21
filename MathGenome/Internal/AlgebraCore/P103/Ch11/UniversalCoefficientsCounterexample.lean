import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.UniversalCoefficientsCounterexample
import MathGenome.Internal.AlgebraCore.P103.Ch10.Complexes
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtTorDefinitions
import MathGenome.Internal.AlgebraCore.P103.Ch01.BalancedTensor

namespace P103.Ch11.UniversalCoefficientsCounterexample
open CategoryTheory
open P103.Specs.Ch11.UniversalCoefficientsCounterexample
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.BalancedTensor
noncomputable section
universe u v w
variable (k : Type u) [Field k]

@[simp] theorem C_d (n : ℕ) : ((C k).d (n+1) n).hom = epsilonLeft k := by
  simp only [C, ChainComplex.of_d]
  rfl
@[simp] theorem Cright_d (n : ℕ) : ((Cright k).d (n+1) n).hom = epsilonRight k := by
  simp only [Cright, ChainComplex.of_d]
  rfl
@[simp] theorem C_d_zero (j : ℕ) : (C k).d 0 j = 0 := by
  apply HomologicalComplex.shape
  simp
@[simp] theorem Cright_d_zero (j : ℕ) : (Cright k).d 0 j = 0 := by
  apply HomologicalComplex.shape
  simp

/-- Multiplication by ε forgets the ε-coordinate and shifts the constant
coordinate into it.  This is the key computation in all positive degrees. -/
theorem mul_epsilon (x : R k) : x * epsilon k = TrivSqZeroExt.inr x.fst := by
  ext <;> simp [epsilon]

theorem mul_epsilon_eq_zero (x : R k) : x * epsilon k = 0 ↔ x.fst = 0 := by
  rw [mul_epsilon]
  constructor
  · intro h
    exact congrArg TrivSqZeroExt.snd h
  · intro h
    simp [h]

theorem range_epsilonLeft : LinearMap.range (epsilonLeft k) =
    LinearMap.ker (epsilonLeft k) := by
  ext x
  change (∃ y : R k, y * epsilon k = x) ↔ x * epsilon k = 0
  rw [mul_epsilon_eq_zero]
  constructor
  · rintro ⟨y, rfl⟩
    simp [mul_epsilon]
  · intro hx
    refine ⟨TrivSqZeroExt.inl x.snd, ?_⟩
    rw [mul_epsilon]
    ext <;> simp [hx]

theorem range_epsilonRight : LinearMap.range (epsilonRight k) =
    LinearMap.ker (epsilonRight k) := by
  ext x
  change (∃ y : R k, y * epsilon k = x) ↔ x * epsilon k = 0
  exact SetLike.ext_iff.mp (range_epsilonLeft k) x

/-- A quotient by all cycles is the zero module. -/
theorem positive_homology (n : ℕ) :
    Subsingleton (H k (n+1)) ∧ Subsingleton (Hr k (n+1)) := by
  constructor <;> apply Submodule.Quotient.subsingleton_iff.mpr <;> apply top_unique
  · intro z _
    change z.val ∈ boundaries (C k) (n+1)
    have hz := z.property
    change ((C k).d (n+1) ((ComplexShape.down ℕ).next (n+1))).hom z.val = 0 at hz
    rw [ChainComplex.next_nat_succ, C_d] at hz
    change ∃ y : R k, ((C k).d ((ComplexShape.down ℕ).prev (n+1)) (n+1)).hom y = z.val
    rw [ChainComplex.prev, C_d]
    change z.val ∈ LinearMap.range (epsilonLeft k)
    rw [range_epsilonLeft]
    exact hz
  · intro z _
    change z.val ∈ boundaries (Cright k) (n+1)
    have hz := z.property
    change ((Cright k).d (n+1) ((ComplexShape.down ℕ).next (n+1))).hom z.val = 0 at hz
    rw [ChainComplex.next_nat_succ, Cright_d] at hz
    change ∃ y : R k, ((Cright k).d ((ComplexShape.down ℕ).prev (n+1)) (n+1)).hom y = z.val
    rw [ChainComplex.prev, Cright_d]
    change z.val ∈ LinearMap.range (epsilonRight k)
    rw [range_epsilonRight]
    exact hz

/-- Quotient homology computed by a surjective map on cycles with precisely
its boundaries as kernel. -/
def homologyOfAugmentation {S : Type*} [Ring S] {ι : Type*} {c : ComplexShape ι}
    (D : HomologicalComplex (ModuleCat.{v} S) c) (n : ι)
    {M : Type*} [AddCommGroup M] [Module S M]
    (f : cycles D n →ₗ[S] M) (hf : Function.Surjective f)
    (hker : LinearMap.ker f = cycleBoundaries D n) : Homology D n ≃ₗ[S] M :=
  (Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hf)

/-- For any zero differential complex, the quotient homology is its term. -/
def homologyOfZero {S : Type*} [Ring S] {ι : Type*} {c : ComplexShape ι}
    (D : HomologicalComplex (ModuleCat.{v} S) c)
    (hd : ∀ i j, D.d i j = 0) (n : ι) : Homology D n ≃ₗ[S] D.X n :=
  homologyOfAugmentation D n (cycles D n).subtype
    (by intro x; exact ⟨⟨x, by simp [cycles, hd]⟩, rfl⟩)
    (by ext z; simp [cycleBoundaries, boundaries, hd])

def residueLeft : R k →ₗ[R k] k where
  toFun x := x.fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def residueRight : R k →ₗ[(R k)ᵐᵒᵖ] k where
  toFun x := x.fst
  map_add' _ _ := rfl
  map_smul' r x := by
    change (x * r.unop).fst = r.unop.fst * x.fst
    simp [mul_comm]

def hZeroLeft : H k 0 ≃ₗ[R k] k :=
  homologyOfAugmentation (C k) 0 ((residueLeft k).comp (cycles (C k) 0).subtype)
    (by intro x; exact ⟨⟨TrivSqZeroExt.inl x, by
      change ((C k).d 0 0).hom _ = 0
      rw [C_d_zero]
      rfl⟩, rfl⟩)
    (by
      ext z
      change z.val.fst = 0 ↔ z.val ∈ boundaries (C k) 0
      change z.val.fst = 0 ↔ ∃ y : R k, ((C k).d ((ComplexShape.down ℕ).prev 0) 0).hom y = z.val
      rw [ChainComplex.prev, C_d]
      change z.val.fst = 0 ↔ z.val ∈ LinearMap.range (epsilonLeft k)
      rw [range_epsilonLeft]
      exact (mul_epsilon_eq_zero k z.val).symm)

def hZeroRight : Hr k 0 ≃ₗ[(R k)ᵐᵒᵖ] k :=
  homologyOfAugmentation (Cright k) 0 ((residueRight k).comp (cycles (Cright k) 0).subtype)
    (by intro x; exact ⟨⟨TrivSqZeroExt.inl x, by
      change ((Cright k).d 0 0).hom _ = 0
      rw [Cright_d_zero]
      rfl⟩, rfl⟩)
    (by
      ext z
      change z.val.fst = 0 ↔ z.val ∈ boundaries (Cright k) 0
      change z.val.fst = 0 ↔ ∃ y : R k, ((Cright k).d ((ComplexShape.down ℕ).prev 0) 0).hom y = z.val
      rw [ChainComplex.prev, Cright_d]
      change z.val.fst = 0 ↔ z.val ∈ LinearMap.range (epsilonRight k)
      rw [range_epsilonRight]
      exact (mul_epsilon_eq_zero k z.val).symm)

theorem tensor_d_zero (i j : ℕ) : (tensorC k).d i j = 0 := by
  by_cases h : i = j+1
  · subst i
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    change R k at a
    change k at b
    change tmul (R k) (((Cright k).d (j+1) j).hom a) b = 0
    rw [Cright_d]
    change tmul (R k) (a * epsilon k) b = 0
    change tmul (R k) (MulOpposite.op (epsilon k) • a) b = 0
    rw [balance]
    change tmul (R k) a ((epsilon k).fst * b) = 0
    simp [epsilon]
  · exact (tensorC k).shape i j (by simpa [ComplexShape.down_Rel] using Ne.symm h)

theorem hom_d_zero (i j : ℕ) : (homC k).d i j = 0 := by
  by_cases h : i+1 = j
  · subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change R k →ₗ[R k] k at f
    change f.comp ((C k).d (i+1) i).hom = 0
    rw [C_d]
    apply LinearMap.ext
    intro x
    change R k at x
    change f (x * epsilon k) = 0
    rw [mul_comm x, ← smul_eq_mul, map_smul]
    change (epsilon k).fst * f x = 0
    simp [epsilon]
  · exact (homC k).shape i j (by simpa [ComplexShape.up_Rel] using h)

def tensorHomology (n : ℕ) : Homology (tensorC k) n ≃+ k :=
  (homologyOfZero (tensorC k) (tensor_d_zero k) n).toAddEquiv.trans leftUnit

/-- Evaluation at 1 is the usual Hom(R,k) = k identification. -/
def homTerm : ((R k) →ₗ[R k] k) ≃+ k where
  toFun f := f 1
  invFun b :=
    { toFun := fun x => x • b
      map_add' := fun x y => add_smul x y b
      map_smul' := fun r x => mul_smul r x b }
  left_inv f := by
    apply LinearMap.ext
    intro x
    change x • f 1 = f x
    calc
      x • f 1 = f (x • (1 : R k)) := (f.map_smul x 1).symm
      _ = f x := by rw [smul_eq_mul, mul_one]
  right_inv b := by change (1 : R k) • b = b; exact one_smul (R k) b
  map_add' _ _ := rfl

def homHomology (n : ℕ) : Homology (homC k) n ≃+ k :=
  (homologyOfZero (homC k) (hom_d_zero k) n).toAddEquiv.trans (homTerm k)

open Polynomial
abbrev Q := Polynomial k ⧸ Ideal.span ({(X : Polynomial k)^2} : Set (Polynomial k))
private def toDual : Q k →ₐ[k] R k :=
  Ideal.Quotient.liftₐ _ (aeval (epsilon k)) (by
    intro p hp
    have hle : Ideal.span ({(X : Polynomial k)^2} : Set (Polynomial k)) ≤
        RingHom.ker (aeval (epsilon k)).toRingHom := by
      rw [Ideal.span_singleton_le_iff_mem]
      change aeval (epsilon k) (X^2) = 0
      simp [epsilon]
    exact hle hp)
@[simp] private theorem toDual_X : toDual k (Ideal.Quotient.mk _ X) = epsilon k := by
  have h : (toDual k).comp (Ideal.Quotient.mkₐ k _) = aeval (epsilon k) :=
    Ideal.Quotient.liftₐ_comp _ _ _
  exact (DFunLike.congr_fun h X).trans (aeval_X _)

private def fromDual : R k →ₐ[k] Q k :=
  DualNumber.lift ⟨(Algebra.ofId k (Q k), Ideal.Quotient.mk _ X), by
    constructor
    · rw [← map_mul, ← pow_two]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    · intro a; exact Commute.all _ _⟩
@[simp] private theorem fromDual_eps : fromDual k (epsilon k) = Ideal.Quotient.mk _ X := by
  simp [fromDual, epsilon]
theorem ringPresentation : ∃ e : Q k ≃ₐ[k] R k, e (Ideal.Quotient.mk _ X) = epsilon k := by
  have h1 : (toDual k).comp (fromDual k) = AlgHom.id k (R k) := by
    apply DualNumber.algHom_ext
    change toDual k (fromDual k (epsilon k)) = epsilon k
    rw [fromDual_eps, toDual_X]
  have h2 : (fromDual k).comp (toDual k) = AlgHom.id k (Q k) := by
    apply Ideal.Quotient.algHom_ext k
    apply Polynomial.algHom_ext
    change fromDual k (toDual k (Ideal.Quotient.mk _ X)) = Ideal.Quotient.mk _ X
    rw [toDual_X, fromDual_eps]
  exact ⟨AlgEquiv.ofAlgHom (toDual k) (fromDual k) h1 h2, toDual_X k⟩

theorem residue_kernel : RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom =
    Ideal.span ({epsilon k} : Set (R k)) := by
  ext x
  change x.fst = 0 ↔ x ∈ Ideal.span ({epsilon k} : Set (R k))
  rw [Ideal.mem_span_singleton]
  constructor
  · intro hx
    refine ⟨TrivSqZeroExt.inl x.snd, ?_⟩
    ext <;> simp [epsilon, hx]
  · rintro ⟨y, rfl⟩
    simp [epsilon]

def residueQuotient : (R k ⧸ Ideal.span ({epsilon k} : Set (R k))) ≃+* k :=
  (Ideal.quotEquivOfEq (residue_kernel k).symm).trans
    ((TrivSqZeroExt.fstHom k k k).toRingHom.quotientKerEquivOfSurjective
      (fun x => ⟨TrivSqZeroExt.inl x, rfl⟩))

@[simp] theorem residueQuotient_mk (x : R k) :
    residueQuotient k (Ideal.Quotient.mk _ x) = x.fst := rfl

theorem free_terms (n : ℕ) : Module.Free (R k) ((C k).X n) ∧
    Module.Free (R k)ᵐᵒᵖ ((Cright k).X n) := by
  constructor
  · change Module.Free (R k) (R k)
    infer_instance
  · change Module.Free (R k)ᵐᵒᵖ (R k)
    let e : (R k)ᵐᵒᵖ ≃ₗ[(R k)ᵐᵒᵖ] R k :=
      { MulOpposite.opAddEquiv.symm with map_smul' := fun _ _ => rfl }
    exact Module.Free.of_equiv e


section ZeroDerived
variable {S : Type u} [Ring S] {A : Type v} [AddCommGroup A]
  {B : Type w} [AddCommGroup B] [Module S B]
theorem ext_subsingleton [Module S A] [Subsingleton A] (P : LeftResolution S A) (hP : P.IsProjective) (n : ℕ) :
    Subsingleton (ExtWith P B n) := by
  let E := P103.Ch11.ExtTorDefinitions.extMaps.{u,v,w} (R := S) n
  let p : ProjectiveChoice S (ModuleCat.of S A) := ⟨P, hP⟩
  have hz : E.map p p (0 : ModuleCat.of S A ⟶ _) (𝟙 (ModuleCat.of S B)) = 0 := by
    have h := E.add_first p p (0 : ModuleCat.of S A ⟶ _) 0 (𝟙 (ModuleCat.of S B))
    apply add_left_cancel (a := E.map p p 0 (𝟙 (ModuleCat.of S B)))
    simpa only [zero_add, add_zero] using h.symm
  have hid : (𝟙 (ModuleCat.of S A)) = (0 : ModuleCat.of S A ⟶ _) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  rw [← hid, E.id] at hz
  exact ⟨fun x y => by
    have hx : x = 0 := LinearMap.congr_fun hz x
    have hy : y = 0 := LinearMap.congr_fun hz y
    exact hx.trans hy.symm⟩

theorem tor_subsingleton [Module Sᵐᵒᵖ A] [Subsingleton A] (P : LeftResolution Sᵐᵒᵖ A) (hP : P.IsProjective) (n : ℕ) :
    Subsingleton (TorWith P B n) := by
  let E := P103.Ch11.ExtTorDefinitions.torMaps.{u,v,w} (R := S) n
  let p : ProjectiveChoice Sᵐᵒᵖ (ModuleCat.of Sᵐᵒᵖ A) := ⟨P, hP⟩
  have hz : E.map p p (0 : ModuleCat.of Sᵐᵒᵖ A ⟶ _) (𝟙 (ModuleCat.of S B)) = 0 := by
    have h := E.add_first p p (0 : ModuleCat.of Sᵐᵒᵖ A ⟶ _) 0 (𝟙 (ModuleCat.of S B))
    apply add_left_cancel (a := E.map p p 0 (𝟙 (ModuleCat.of S B)))
    simpa only [zero_add, add_zero] using h.symm
  have hid : (𝟙 (ModuleCat.of Sᵐᵒᵖ A)) = (0 : ModuleCat.of Sᵐᵒᵖ A ⟶ _) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  rw [← hid, E.id] at hz
  exact ⟨fun x y => by
    have hx : x = 0 := LinearMap.congr_fun hz x
    have hy : y = 0 := LinearMap.congr_fun hz y
    exact hx.trans hy.symm⟩

end ZeroDerived

/-- A nonzero middle group cannot be exact between zero outer groups. -/
theorem not_exact_of_outer_zero {A B M : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup M]
    [Subsingleton A] [Subsingleton B] [Nontrivial M]
    (f : A →+ M) (g : M →+ B) : ¬ Function.Exact f g := by
  intro h
  have hz (x : M) : x = 0 := by
    obtain ⟨a, ha⟩ := (h x).mp (Subsingleton.elim _ _)
    rw [Subsingleton.elim a 0, map_zero] at ha
    exact ha.symm
  exact not_subsingleton M ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- The dual-number complex disproves both coefficient sequences under
degreewise freeness alone, over every field. -/
theorem counterexample : counterexampleType.{u} := by
  intro k _
  refine ⟨ringPresentation k, ⟨residueQuotient k, residueQuotient_mk k⟩,
    ?_, ?_, ?_, free_terms k, ⟨hZeroLeft k⟩, ⟨hZeroRight k⟩,
    positive_homology k, ?_, ?_, ?_⟩
  · intro i j l
    exact P103.Ch10.Complexes.differential_squared (C k) i j l
  · intro n
    exact ⟨C_d k n, Cright_d k n⟩
  · intro j
    exact ⟨C_d_zero k j, Cright_d_zero k j⟩
  · intro i j
    exact ⟨tensor_d_zero k i j, hom_d_zero k i j⟩
  · intro n
    exact ⟨⟨tensorHomology k n⟩, ⟨homHomology k n⟩,
      (tensorHomology k n).surjective.nontrivial, (homHomology k n).surjective.nontrivial⟩
  · intro n hn
    have hpos (m : ℕ) (hm : 0 < m) : Subsingleton (H k m) ∧ Subsingleton (Hr k m) := by
      obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
      exact positive_homology k l
    let :=  (hpos n (by omega)).1
    let :=  (hpos n (by omega)).2
    let :=  (hpos (n-1) (by omega)).1
    let :=  (hpos (n-1) (by omega)).2
    have hT : Subsingleton (Tensor (R k) (Hr k n) k) :=
      ⟨fun x y => (eq_zero_of_subsingleton_left x).trans (eq_zero_of_subsingleton_left y).symm⟩
    have htor (P : LeftResolution (R k)ᵐᵒᵖ (Hr k (n-1))) (hP : P.IsProjective) :
        Subsingleton (TorWith P k 1) := tor_subsingleton P hP 1
    have hext (P : LeftResolution (R k) (H k (n-1))) (hP : P.IsProjective) :
        Subsingleton (ExtWith P k 1) := ext_subsingleton P hP 1
    refine ⟨hT, htor, hext, inferInstance, ?_, ?_⟩
    · intro P hP f g
      let :=  hT
      let :=  htor P hP
      let :=  (tensorHomology k n).surjective.nontrivial
      exact not_exact_of_outer_zero f g
    · intro P hP f g
      let :=  hext P hP
      let :=  (homHomology k n).surjective.nontrivial
      exact not_exact_of_outer_zero f g

end
end P103.Ch11.UniversalCoefficientsCounterexample
