import MathGenome.Internal.Specs.D05.M15.Symmetric
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Isomorphisms
import MathGenome.Internal.D05.M15.TensorAlgebra
import MathGenome.Internal.D05.M15.Multilinear
import MathGenome.Internal.D05.M06.QuotientLift

/-! Symmetric algebra and adjacent-relation symmetric powers.

The canonical Mathlib congruence quotient is proved to be the quotient by the
paper's two-sided commutator ideal. Its universal property also allows a
noncommutative target when the generator images commute pairwise.

For grading, `homogeneousRelations` is the linear span of the images of all
adjacent-relation spaces. Tensor concatenation makes it a two-sided ideal;
it equals the commutator ideal. Projection to one component therefore proves
`homogeneous_kernel`, identifying our degreewise quotient with the corresponding
homogeneous image in the algebra quotient. No averaging or dimension argument
is used. The nullary normalization is fixed by the empty tensor mapping to 1.
-/
namespace D05.M15.Symmetric
open scoped TensorProduct

abbrev commutatorIdeal := Specs.D05.M15.Symmetric.commutatorIdeal
abbrev symmetricAlgebra := Specs.D05.M15.Symmetric.symmetricAlgebra
abbrev adjacentRelations := Specs.D05.M15.Symmetric.adjacentRelations
abbrev symmetricPower := Specs.D05.M15.Symmetric.symmetricPower
abbrev elementary := Specs.D05.M15.Symmetric.elementary
abbrev homogeneousMap := Specs.D05.M15.Symmetric.homogeneousMap

theorem ideal_congruence : Specs.D05.M15.Symmetric.ideal_congruence := by
  intro K V _ _ _
  apply le_antisymm
  · apply RingCon.ringConGen_le.mpr
    intro x y h
    obtain ⟨⟨u,v⟩, huv⟩ := h
    have hc : (_root_.TensorAlgebra.symRingCon K V)
        (_root_.TensorAlgebra.ι K u * _root_.TensorAlgebra.ι K v)
        (_root_.TensorAlgebra.ι K v * _root_.TensorAlgebra.ι K u) :=
      RingCon.le_ringConGen _ _ (_root_.TensorAlgebra.SymRel.mul_comm u v)
    have hm := (TwoSidedIdeal.rel_iff
      (TwoSidedIdeal.ofRingCon (_root_.TensorAlgebra.symRingCon K V)) _ _).mp hc
    apply (TwoSidedIdeal.rel_iff
      (TwoSidedIdeal.ofRingCon (_root_.TensorAlgebra.symRingCon K V)) x y).mpr
    rwa [← huv]
  · apply RingCon.ringConGen_le.mpr
    intro x y h
    cases h with
    | mul_comm u v =>
      apply (TwoSidedIdeal.rel_iff (commutatorIdeal K V) _ _).mpr
      exact TwoSidedIdeal.subset_span ⟨(u,v), rfl⟩

theorem quotient_eq_iff : Specs.D05.M15.Symmetric.quotient_eq_iff := by
  intro K V _ _ _ x y
  change (_root_.TensorAlgebra.symRingCon K V).mk' x =
    (_root_.TensorAlgebra.symRingCon K V).mk' y ↔ _
  rw [show (TensorAlgebra.symRingCon K V).mk' x =
      (TensorAlgebra.symRingCon K V).mk' y ↔
      (TensorAlgebra.symRingCon K V) x y from Quotient.eq, ← ideal_congruence]
  exact TwoSidedIdeal.rel_iff _ _ _

theorem commutative : Specs.D05.M15.Symmetric.commutative := by
  intro K V _ _ _ x y
  exact mul_comm x y

/-- Extensionality remains valid even for a noncommutative target algebra. -/
theorem hom_ext {K V A : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Ring A] [Algebra K A] (F G : symmetricAlgebra K V →ₐ[K] A)
    (h : ∀ v, F (_root_.SymmetricAlgebra.ι K V v) =
      G (_root_.SymmetricAlgebra.ι K V v)) : F = G := by
  have ht : F.comp (_root_.SymmetricAlgebra.algHom K V) =
      G.comp (_root_.SymmetricAlgebra.algHom K V) := by
    apply _root_.TensorAlgebra.hom_ext
    exact LinearMap.ext h
  apply AlgHom.ext
  intro x
  obtain ⟨t, rfl⟩ := _root_.SymmetricAlgebra.algHom_surjective K V x
  exact DFunLike.congr_fun ht t

/-- Linear maps with pairwise commuting images descend without requiring a
commutative target. -/
def extend {K V A : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Ring A] [Algebra K A] (f : V →ₗ[K] A) (h : ∀ u v, Commute (f u) (f v)) :
    symmetricAlgebra K V →ₐ[K] A :=
  (_root_.TensorAlgebra.symRingCon K V).liftₐ (_root_.TensorAlgebra.lift K f) (by
    apply RingCon.ringConGen_le.mpr
    intro x y hxy
    cases hxy with
    | mul_comm u v =>
      change _root_.TensorAlgebra.lift K f _ = _root_.TensorAlgebra.lift K f _
      simpa only [map_mul, _root_.TensorAlgebra.lift_ι_apply] using (h u v).eq)

@[simp] theorem extend_generator {K V A : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Ring A] [Algebra K A] (f : V →ₗ[K] A)
    (h : ∀ u v, Commute (f u) (f v)) (v : V) :
    extend f h (_root_.SymmetricAlgebra.ι K V v) = f v := by
  change (_root_.TensorAlgebra.symRingCon K V).liftₐ _ _
    ((_root_.TensorAlgebra.symRingCon K V).mk' (_root_.TensorAlgebra.ι K v)) = _
  exact _root_.TensorAlgebra.lift_ι_apply f v

theorem universal_property : Specs.D05.M15.Symmetric.universal_property := by
  intro K V A _ _ _ _ _ f
  constructor
  · intro h
    refine ⟨extend f h, extend_generator f h, ?_⟩
    intro F hF
    exact hom_ext F (extend f h) (fun v => (hF v).trans (extend_generator f h v).symm)
  · rintro ⟨F, hF, _⟩ u v
    change f u * f v = f v * f u
    calc
      f u * f v = F (_root_.SymmetricAlgebra.ι K V u * _root_.SymmetricAlgebra.ι K V v) := by rw [map_mul, hF, hF]
      _ = F (_root_.SymmetricAlgebra.ι K V v * _root_.SymmetricAlgebra.ι K V u) := congrArg F (mul_comm _ _)
      _ = f v * f u := by rw [map_mul, hF, hF]

theorem commutative_universal : Specs.D05.M15.Symmetric.commutative_universal := by
  intro K V A _ _ _ _ _ f
  exact (universal_property f).mp (fun _ _ => Commute.all _ _)

theorem tensor_lift_kills_ideal : Specs.D05.M15.Symmetric.tensor_lift_kills_ideal := by
  intro K V A _ _ _ _ _ f h t ht
  have hc : (TensorAlgebra.symRingCon K V) t 0 := by
    rw [← ideal_congruence]
    exact ht
  have hf : (TensorAlgebra.symRingCon K V) ≤
      RingCon.ker (TensorAlgebra.lift K f).toRingHom := by
    apply RingCon.ringConGen_le.mpr
    intro x y hxy
    cases hxy with
    | mul_comm u v =>
      change TensorAlgebra.lift K f _ = TensorAlgebra.lift K f _
      simpa only [map_mul, TensorAlgebra.lift_ι_apply] using (h u v).eq
  exact (hf hc).trans (map_zero (TensorAlgebra.lift K f))

/-- A function on finite tuples invariant under consecutive transpositions
is invariant under all permutations. This also handles zero slots. -/
theorem invariant_of_adjacent {V W : Type*} (p : ℕ) (b : (Fin p → V) → W)
    (h : ∀ (x : Fin p → V) (i j : Fin p), j.val = i.val + 1 →
      b (x ∘ Equiv.swap i j) = b x) :
    ∀ (x : Fin p → V) (σ : Equiv.Perm (Fin p)), b (x ∘ σ) = b x := by
  cases p with
  | zero =>
    intro x σ
    congr 1
    exact funext (fun i => Fin.elim0 i)
  | succ n =>
    let S : Submonoid (Equiv.Perm (Fin (n+1))) := {
      carrier := {σ | ∀ x : Fin (n+1) → V, b (x ∘ σ) = b x}
      one_mem' := fun _ => rfl
      mul_mem' := by
        intro σ τ hσ hτ x
        change b ((x ∘ σ) ∘ τ) = b x
        exact (hτ (x ∘ σ)).trans (hσ x) }
    have hs : Submonoid.closure
        (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) ≤ S := by
      apply Submonoid.closure_le.mpr
      rintro _ ⟨i, rfl⟩ x
      exact h x i.castSucc i.succ rfl
    rw [Equiv.Perm.mclosure_swap_castSucc_succ] at hs
    intro x σ
    exact hs (Submonoid.mem_top σ) x

theorem symmetry_iff_adjacent : Specs.D05.M15.Symmetric.symmetry_iff_adjacent := by
  intro K V W _ _ _ _ _ p b
  exact ⟨invariant_of_adjacent p b, fun h x i j _ => h x (Equiv.swap i j)⟩

/-- Equality of elementary classes under a single defining adjacent swap. -/
theorem elementary_adjacent {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (x : Fin p → V) (i j : Fin p) (hij : j.val = i.val + 1) :
    elementary K V p (x ∘ Equiv.swap i j) = elementary K V p x := by
  apply Eq.symm
  apply sub_eq_zero.mp
  change (adjacentRelations K V p).mkQ (PiTensorProduct.tprod K x) -
    (adjacentRelations K V p).mkQ (PiTensorProduct.tprod K (x ∘ Equiv.swap i j)) = 0
  rw [← map_sub]
  apply LinearMap.mem_ker.mp
  rw [Submodule.ker_mkQ]
  exact Submodule.subset_span ⟨x, i, j, hij, rfl⟩

theorem elementary_symmetric : Specs.D05.M15.Symmetric.elementary_symmetric := by
  intro K V _ _ _ p
  exact invariant_of_adjacent p (elementary K V p) (elementary_adjacent p)

theorem permutation_relation : Specs.D05.M15.Symmetric.permutation_relation := by
  intro K V _ _ _ p x σ
  change _ ∈ adjacentRelations K V p
  rw [← Submodule.ker_mkQ (adjacentRelations K V p)]
  apply LinearMap.mem_ker.mpr
  change (adjacentRelations K V p).mkQ (_ - _) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (elementary_symmetric p x σ).symm

theorem annihilates_relations : Specs.D05.M15.Symmetric.annihilates_relations := by
  intro K V W _ _ _ _ _ p b
  constructor
  · intro h
    apply (symmetry_iff_adjacent p b).mp
    intro x i j hij
    have hz := h (Submodule.subset_span ⟨x, i, j, hij, rfl⟩)
    change PiTensorProduct.lift b (_ - _) = 0 at hz
    rw [map_sub, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod] at hz
    exact (sub_eq_zero.mp hz).symm
  · intro h
    apply Submodule.span_le.mpr
    rintro t ⟨x, i, j, _, rfl⟩
    change PiTensorProduct.lift b (_ - _) = 0
    rw [map_sub, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod,
      h x (Equiv.swap i j), sub_self]

theorem power_universal : Specs.D05.M15.Symmetric.power_universal := by
  intro K V W _ _ _ _ _ p b
  constructor
  · intro h
    have hk := (annihilates_relations p b).mpr h
    refine ⟨(adjacentRelations K V p).liftQ (PiTensorProduct.lift b) hk, ?_, ?_⟩
    · intro x
      exact PiTensorProduct.lift.tprod x
    · intro L hL
      have heq : L.comp (adjacentRelations K V p).mkQ = PiTensorProduct.lift b := by
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro x
        exact (hL x).trans (PiTensorProduct.lift.tprod x).symm
      apply LinearMap.ext
      intro t
      obtain ⟨t, rfl⟩ := (adjacentRelations K V p).mkQ_surjective t
      exact LinearMap.congr_fun heq t
  · rintro ⟨L, hL, _⟩ x σ
    rw [← hL, ← hL, elementary_symmetric]

section Grading
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Extend permutations separately on the two consecutive blocks of slots. -/
def blockPerm {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (m+n)) :=
  finSumFinEquiv.symm.trans ((σ.sumCongr τ).trans finSumFinEquiv)

theorem append_blockPerm {m n : ℕ} (x : Fin m → V) (y : Fin n → V)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    Fin.append (x ∘ σ) (y ∘ τ) = Fin.append x y ∘ blockPerm σ τ := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp [blockPerm, Function.comp_def]
  · intro j; simp [blockPerm, Function.comp_def]

def tensorLeft {m n : ℕ} (x : Fin m → V) :
    TensorPower K n V →ₗ[K] TensorPower K (m+n) V :=
  ((TensorProduct.mk K _ _).compr₂ (TensorPower.mulEquiv (R := K) (M := V) (n := m) (m := n)).toLinearMap) (PiTensorProduct.tprod K x)

def tensorRight {m n : ℕ} (y : Fin n → V) :
    TensorPower K m V →ₗ[K] TensorPower K (m+n) V :=
  ((TensorProduct.mk K _ _).compr₂ (TensorPower.mulEquiv (R := K) (M := V) (n := m) (m := n)).toLinearMap).flip (PiTensorProduct.tprod K y)

@[simp] theorem tensorLeft_tprod {m n : ℕ} (x : Fin m → V) (y : Fin n → V) :
    tensorLeft (K := K) x (PiTensorProduct.tprod K y) =
      PiTensorProduct.tprod K (Fin.append x y) := TensorPower.tprod_mul_tprod K x y

@[simp] theorem tensorRight_tprod {m n : ℕ} (x : Fin m → V) (y : Fin n → V) :
    tensorRight (K := K) y (PiTensorProduct.tprod K x) =
      PiTensorProduct.tprod K (Fin.append x y) := TensorPower.tprod_mul_tprod K x y

theorem tensorLeft_relation {m n : ℕ} (x : Fin m → V) (r : TensorPower K n V)
    (hr : r ∈ adjacentRelations K V n) :
    tensorLeft x r ∈ adjacentRelations K V (m+n) := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨y,i,j,_,rfl⟩ := hr
    rw [map_sub, tensorLeft_tprod, tensorLeft_tprod]
    rw [show Fin.append x (y ∘ Equiv.swap i j) =
        Fin.append x y ∘ blockPerm (Equiv.refl _) (Equiv.swap i j) from
      append_blockPerm x y (Equiv.refl _) (Equiv.swap i j)]
    exact permutation_relation (m+n) _ _
  | zero => simp
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul a r _ hr => simpa only [map_smul] using Submodule.smul_mem _ a hr

theorem tensorRight_relation {m n : ℕ} (y : Fin n → V) (r : TensorPower K m V)
    (hr : r ∈ adjacentRelations K V m) :
    tensorRight y r ∈ adjacentRelations K V (m+n) := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨x,i,j,_,rfl⟩ := hr
    rw [map_sub, tensorRight_tprod, tensorRight_tprod]
    rw [show Fin.append (x ∘ Equiv.swap i j) y =
        Fin.append x y ∘ blockPerm (Equiv.swap i j) (Equiv.refl _) from
      append_blockPerm x y (Equiv.swap i j) (Equiv.refl _)]
    exact permutation_relation (m+n) _ _
  | zero => simp
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul a r _ hr => simpa only [map_smul] using Submodule.smul_mem _ a hr

/-- The global submodule generated by all homogeneous adjacent relations. -/
def homogeneousRelations : Submodule K (TensorAlgebra K V) :=
  Submodule.span K {t | ∃ (p : ℕ) (r : TensorPower K p V),
    r ∈ adjacentRelations K V p ∧ t = TensorPower.toTensorAlgebra r}

theorem homogeneousRelation_mem (p : ℕ) (r : TensorPower K p V)
    (hr : r ∈ adjacentRelations K V p) :
    TensorPower.toTensorAlgebra r ∈ homogeneousRelations (K := K) (V := V) :=
  Submodule.subset_span ⟨p,r,hr,rfl⟩

/-- Every tensor algebra element is a finite linear combination of pure words. -/
theorem word_induction {P : TensorAlgebra K V → Prop}
    (word : ∀ p (x : Fin p → V), P (TensorPower.toTensorAlgebra (PiTensorProduct.tprod K x)))
    (zero : P 0) (add : ∀ a b, P a → P b → P (a+b))
    (smul : ∀ (c : K) a, P a → P (c • a)) (a : TensorAlgebra K V) : P a := by
  obtain ⟨s, _, hs⟩ := D05.M15.TensorAlgebra.reconstruction a
  rw [hs]
  apply Finset.sum_induction
  · exact add
  · exact zero
  · intro p _
    induction TensorAlgebra.equivDirectSum a p using PiTensorProduct.induction_on with
    | smul_tprod c x => rw [map_smul]; exact smul c _ (word p x)
    | add x y hx hy => rw [map_add]; exact add _ _ hx hy

theorem homogeneousRelations_mul_left (a t : TensorAlgebra K V)
    (ht : t ∈ homogeneousRelations (K := K) (V := V)) :
    a * t ∈ homogeneousRelations (K := K) (V := V) := by
  induction a using word_induction with
  | word m x =>
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨n,r,hr,rfl⟩ := ht
      rw [← TensorPower.toTensorAlgebra_gMul]
      exact homogeneousRelation_mem (m+n) _ (tensorLeft_relation x r hr)
    | zero => simp
    | add t u _ _ ht hu => simpa only [mul_add] using Submodule.add_mem _ ht hu
    | smul c t _ ht => simpa only [mul_smul_comm] using Submodule.smul_mem _ c ht
  | zero => simp
  | add a b ha hb => simpa only [add_mul] using Submodule.add_mem _ ha hb
  | smul c a ha => simpa only [smul_mul_assoc] using Submodule.smul_mem _ c ha

theorem homogeneousRelations_mul_right (a t : TensorAlgebra K V)
    (ht : t ∈ homogeneousRelations (K := K) (V := V)) :
    t * a ∈ homogeneousRelations (K := K) (V := V) := by
  induction a using word_induction with
  | word n y =>
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨m,r,hr,rfl⟩ := ht
      rw [← TensorPower.toTensorAlgebra_gMul]
      exact homogeneousRelation_mem (m+n) _ (tensorRight_relation y r hr)
    | zero => simp
    | add t u _ _ ht hu => simpa only [add_mul] using Submodule.add_mem _ ht hu
    | smul c t _ ht => simpa only [smul_mul_assoc] using Submodule.smul_mem _ c ht
  | zero => simp
  | add a b ha hb => simpa only [mul_add] using Submodule.add_mem _ ha hb
  | smul c a ha => simpa only [mul_smul_comm] using Submodule.smul_mem _ c ha

@[simp] theorem homogeneousMap_tprod (p : ℕ) (x : Fin p → V) :
    homogeneousMap K V p (PiTensorProduct.tprod K x) =
      ∏ i, _root_.SymmetricAlgebra.ι K V (x i) := by
  change _root_.SymmetricAlgebra.algHom K V
    (TensorPower.toTensorAlgebra (PiTensorProduct.tprod K x)) = _
  rw [D05.M15.TensorAlgebra.elementary_word, map_list_prod, List.map_ofFn, Fin.prod_ofFn]
  rfl

theorem relations_killed (p : ℕ) :
    adjacentRelations K V p ≤ LinearMap.ker (homogeneousMap K V p) := by
  apply Submodule.span_le.mpr
  rintro t ⟨x,i,j,_,rfl⟩
  change homogeneousMap K V p (_ - _) = 0
  rw [map_sub, homogeneousMap_tprod, homogeneousMap_tprod]
  apply sub_eq_zero.mpr
  exact (Equiv.prod_comp (Equiv.swap i j) (fun i => _root_.SymmetricAlgebra.ι K V (x i))).symm

theorem homogeneousRelations_le_ideal (t : TensorAlgebra K V)
    (ht : t ∈ homogeneousRelations (K := K) (V := V)) : t ∈ commutatorIdeal K V := by
  have hker : homogeneousRelations (K := K) (V := V) ≤
      LinearMap.ker (_root_.SymmetricAlgebra.algHom K V).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro t ⟨p,r,hr,rfl⟩
    exact relations_killed p hr
  have hz := hker ht
  have heq := (quotient_eq_iff t 0).mp (by simpa using hz)
  simpa using heq

/-- The span of homogeneous swap relations is already a two-sided ideal. -/
def homogeneousRelationsIdeal : TwoSidedIdeal (TensorAlgebra K V) :=
  TwoSidedIdeal.mk' (homogeneousRelations (K := K) (V := V))
    (Submodule.zero_mem _) (Submodule.add_mem _) (Submodule.neg_mem _)
    (fun {_ _} ht => homogeneousRelations_mul_left _ _ ht)
    (fun {_ _} ht => homogeneousRelations_mul_right _ _ ht)

theorem ideal_le_homogeneousRelations (t : TensorAlgebra K V)
    (ht : t ∈ commutatorIdeal K V) :
    t ∈ homogeneousRelations (K := K) (V := V) := by
  have hle : commutatorIdeal K V ≤ homogeneousRelationsIdeal (K := K) (V := V) := by
    apply TwoSidedIdeal.span_le.mpr
    rintro t ⟨⟨u,v⟩,rfl⟩
    let x : Fin 2 → V := Fin.cons u (Fin.cons v Fin.elim0)
    have hr : PiTensorProduct.tprod K x -
        PiTensorProduct.tprod K (x ∘ Equiv.swap 0 1) ∈ adjacentRelations K V 2 :=
      Submodule.subset_span ⟨x,0,1,rfl,rfl⟩
    have hh := homogeneousRelation_mem 2 _ hr
    have hs : x ∘ Equiv.swap 0 1 = Fin.cons v (Fin.cons u Fin.elim0) := by
      funext i
      fin_cases i <;> simp [x]
    rw [map_sub, D05.M15.TensorAlgebra.elementary_word,
      D05.M15.TensorAlgebra.elementary_word, hs] at hh
    simpa [x, List.ofFn_succ, homogeneousRelationsIdeal] using hh
  have hh := hle ht
  change t - 0 ∈ homogeneousRelations (K := K) (V := V) at hh
  simpa only [sub_zero] using hh

/-- Projection of the global homogeneous relation submodule lands in the
corresponding adjacent-relation subspace. -/
theorem relation_component (t : TensorAlgebra K V)
    (ht : t ∈ homogeneousRelations (K := K) (V := V)) (p : ℕ) :
    TensorAlgebra.equivDirectSum t p ∈ adjacentRelations K V p := by
  let π : TensorAlgebra K V →ₗ[K] TensorPower K p V :=
    (DirectSum.component K ℕ (fun n => TensorPower K n V) p).comp
      TensorAlgebra.equivDirectSum.toLinearMap
  change π t ∈ adjacentRelations K V p
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨q,r,hr,rfl⟩ := ht
    change TensorAlgebra.equivDirectSum (TensorPower.toTensorAlgebra r) p ∈ _
    rw [D05.M15.TensorAlgebra.direct_sum_inclusion]
    by_cases h : q = p
    · subst q; simpa only [DirectSum.lof_eq_of, DirectSum.of_eq_same] using hr
    · simpa only [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)] using
        (adjacentRelations K V p).zero_mem
  | zero => simp
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul c r _ hr => simpa only [map_smul] using Submodule.smul_mem _ c hr

end Grading

theorem ideal_homogeneous : Specs.D05.M15.Symmetric.ideal_homogeneous := by
  intro K V _ _ _ t ht p
  exact homogeneousRelations_le_ideal _
    (homogeneousRelation_mem p _ (relation_component t (ideal_le_homogeneousRelations t ht) p))

theorem homogeneous_kernel : Specs.D05.M15.Symmetric.homogeneous_kernel := by
  intro K V _ _ _ p
  apply le_antisymm
  · intro t ht
    have hi : TensorPower.toTensorAlgebra t ∈ commutatorIdeal K V := by
      have heq := (quotient_eq_iff (TensorPower.toTensorAlgebra t) 0).mp (by
        exact (LinearMap.mem_ker.mp ht).trans (map_zero _).symm)
      simpa only [sub_zero] using heq
    have hc := relation_component _ (ideal_le_homogeneousRelations _ hi) p
    rw [D05.M15.TensorAlgebra.direct_sum_inclusion] at hc
    simpa only [DirectSum.lof_eq_of, DirectSum.of_eq_same] using hc
  · exact relations_killed p

theorem power_equiv_homogeneous : Specs.D05.M15.Symmetric.power_equiv_homogeneous := by
  intro K V _ _ _ p
  let E := (Submodule.quotEquivOfEq _ _ (homogeneous_kernel p).symm).trans
    (homogeneousMap K V p).quotKerEquivRange
  refine ⟨E, ?_⟩
  intro x
  exact (homogeneousMap K V p).quotKerEquivRange_apply_mk (PiTensorProduct.tprod K x)

theorem degree_zero : Specs.D05.M15.Symmetric.degree_zero := by
  intro K V _ _ _
  have hbot : adjacentRelations K V 0 = ⊥ := by
    apply le_bot_iff.mp
    apply Submodule.span_le.mpr
    rintro t ⟨x,i,j,_,_⟩
    exact Fin.elim0 i
  refine ⟨((adjacentRelations K V 0).quotEquivOfEqBot hbot).trans
    (PiTensorProduct.isEmptyEquiv (Fin 0)), ?_⟩
  intro x
  exact PiTensorProduct.isEmptyEquiv_apply_tprod (Fin 0) x

end D05.M15.Symmetric
