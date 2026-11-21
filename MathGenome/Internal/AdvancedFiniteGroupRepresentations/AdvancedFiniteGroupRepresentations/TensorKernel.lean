import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.IsotypicMatrixBlocks
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.LengthBound
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.TensorKernel
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.TwoSidedIdeal.BigOperators
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct
universe u
namespace AdvancedFiniteGroupRepresentations
abbrev tensorSlotAction := @Specs.AdvancedFiniteGroupRepresentations.tensorSlotAction
abbrev omittedMatrixBlocks := Specs.AdvancedFiniteGroupRepresentations.omittedMatrixBlocks
abbrev initialPositionSubgroup := Specs.AdvancedFiniteGroupRepresentations.initialPositionSubgroup
abbrev initialAlternator := Specs.AdvancedFiniteGroupRepresentations.initialAlternator

variable (V : Type u) [AddCommGroup V] [Module ℂ V]

theorem tensorSlotAction_eq (n : ℕ) : tensorSlotAction V n = slotAlgebraMap V n := rfl

/-- Equivariance extends from permutations to their group algebra. -/
theorem tensorMultiplicity_algebra_action {n : ℕ} (p : Partition n)
    (f : TensorMultiplicity V p) (a : GroupAlgebra n) (v : SpechtModule p) :
    f.val ((canonicalSpechtRepresentation p).asAlgebraHom a v) =
      tensorSlotAction V n a (f.val v) := by
  rw [tensorSlotAction_eq]
  exact intertwining_algebra_action _ _ (tensorMultiplicityEquivIntertwining V p f) a v

theorem tensorKernel_blocks [FiniteDimensional ℂ V] (n : ℕ)
    (σ : ∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (hσ : ∀ p, InheritedSpechtAction p (σ p)) :
    LinearMap.ker (tensorSlotAction V n).toLinearMap =
      (omittedMatrixBlocks n (Module.finrank ℂ V)).comap
        (spechtFamilyAlgebraMap σ).toLinearMap := by
  have he : σ = canonicalSpechtRepresentation := by
    funext p
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    exact Subtype.ext (hσ p g v)
  subst σ
  ext a
  change tensorSlotAction V n a = 0 ↔
    ∀ p : Partition n, length p ≤ Module.finrank ℂ V →
      (canonicalSpechtRepresentation p).asAlgebraHom a = 0
  constructor
  · intro ha p hp
    let f := LengthBound.spechtTensorEmbedding (Module.finBasis ℂ V) hp
    apply LinearMap.ext
    intro v
    apply LengthBound.spechtTensorEmbedding_injective (Module.finBasis ℂ V) hp
    change f.val ((canonicalSpechtRepresentation p).asAlgebraHom a v) = f.val 0
    rw [tensorMultiplicity_algebra_action, ha]
    simp
  · intro ha
    apply tensorEvaluation_end_ext V
    intro p v f
    by_cases hp : length p ≤ Module.finrank ℂ V
    · rw [← tensorMultiplicity_algebra_action, ha p hp]
      simp
    · have hf := LengthBound.tensorMultiplicity_eq_zero_of_length_gt (Nat.lt_of_not_ge hp) f
      rw [hf]
      simp

/-- A partition has no more nonempty rows than cells. -/
theorem partition_length_le {n : ℕ} (p : Partition n) : length p ≤ n := by
  have h := List.length_le_sum_of_one_le (parts p) (fun i hi => parts_positive p i hi)
  change (parts p).length ≤ n
  simpa only [parts_sum] using h

theorem tensorSlotAction_injective [FiniteDimensional ℂ V] (n : ℕ)
    (hn : n ≤ Module.finrank ℂ V) : Function.Injective (tensorSlotAction V n) := by
  change Function.Injective (tensorSlotAction V n).toLinearMap
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro a ha
  have hb := congrArg (fun S : Submodule ℂ (GroupAlgebra n) => a ∈ S)
    (tensorKernel_blocks V n canonicalSpechtRepresentation (fun _ _ _ => rfl))
  have hc : ∀ p : Partition n, (canonicalSpechtRepresentation p).asAlgebraHom a = 0 := by
    intro p
    exact (Iff.mp (eq_iff_iff.mp hb) ha) p ((partition_length_le p).trans hn)
  have he : spechtFamilyAlgebraMap canonicalSpechtRepresentation a = 0 := funext hc
  exact (canonicalSpechtFamilyAlgebraMap_injective n) (by simpa using he)

namespace TensorKernel

variable {n k : ℕ}

/-- A permutation supported on the first k positions preserves that set. -/
theorem initial_lt (s : initialPositionSubgroup n k) (a : Fin n) (ha : a.val < k) :
    (s.val a).val < k := by
  by_contra h
  have he := s.property (s.val a) (Nat.le_of_not_gt h)
  have hi : s.val a = a := s.val.injective he
  exact (Nat.not_le_of_gt ha) (hi ▸ Nat.le_of_not_gt h)

/-- The signed averaging operator transforms on the right by the sign. -/
theorem alternator_right {X : Type*} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (SymmetricGroup n) X) (c : initialPositionSubgroup n k) (x : X) :
    ρ.asAlgebraHom (initialAlternator n k) (ρ c.val x) =
      permutationSign c.val • ρ.asAlgebraHom (initialAlternator n k) x := by
  classical
  simp only [initialAlternator, Specs.AdvancedFiniteGroupRepresentations.initialAlternator,
    map_sum, LinearMap.sum_apply, Representation.asAlgebraHom_single, Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.mulRight c)
  intro d
  change permutationSign d.val • (ρ d.val (ρ c.val x)) =
    permutationSign c.val • (permutationSign (d.val * c.val) • ρ (d.val * c.val) x)
  rw [permutationSign_mul, smul_smul]
  have hs : permutationSign c.val * (permutationSign d.val * permutationSign c.val) =
      permutationSign d.val := by
    rw [mul_left_comm, permutationSign_sq, mul_one]
  rw [hs, map_mul, Module.End.mul_apply]

/-- The pairing cancellation, for any k larger than the dimension. -/
theorem alternator_tensor_zero [FiniteDimensional ℂ V]
    (hn : k ≤ n) (hk : Module.finrank ℂ V < k) :
    tensorSlotAction V n (initialAlternator n k) = 0 := by
  classical
  let b := Module.finBasis ℂ V
  apply (Basis.piTensorProduct (fun _ : Fin n => b)).ext
  intro w
  obtain ⟨i, j, hij, hw⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin k => w (Fin.castLE hn i)) (by simpa using hk)
  let a : Fin n := Fin.castLE hn i
  let a' : Fin n := Fin.castLE hn j
  have haa' : a ≠ a' := (Fin.castLE_injective hn).ne hij
  have hal : a.val < k := i.isLt
  have ha'l : a'.val < k := j.isLt
  let c : initialPositionSubgroup n k := ⟨Equiv.swap a a', by
    intro x hx
    exact Equiv.swap_apply_of_ne_of_ne
      (by intro he; subst x; omega) (by intro he; subst x; omega)⟩
  have hs : permutationSign c.val = -1 := by
    simp [c, permutationSign, Specs.AdvancedFiniteGroupRepresentations.permutationSign,
      Equiv.Perm.sign_swap haa']
  have hfix : slotRepresentation V n c.val (pureTensor V n (fun x => b (w x))) =
      pureTensor V n (fun x => b (w x)) := by
    change slotOperator V n (Equiv.swap a a') _ = _
    rw [slot_pureTensor]
    congr 1
    funext x
    exact congrArg b (Equiv.apply_swap_eq_self hw x)
  have he := alternator_right (slotRepresentation V n) c
    (pureTensor V n (fun x => b (w x)))
  rw [hfix, hs, neg_one_smul] at he
  have hz : (2 : ℂ) • (Representation.asAlgebraHom (slotRepresentation V n) (initialAlternator n k))
      (pureTensor V n (fun x => b (w x))) = 0 := by
    simpa only [two_smul] using eq_neg_iff_add_eq_zero.mp he
  have hz' := (smul_eq_zero.mp hz).resolve_left (by norm_num)
  rw [Basis.piTensorProduct_apply]
  change tensorSlotAction V n (initialAlternator n k)
    (pureTensor V n (fun x => b (w x))) = 0
  exact hz'

/-- The first k labels can be placed in the first column of every shape
with at least k rows. No standardness requirement is imposed on tableaux. -/
theorem exists_firstColumn_tableau {p : Partition n} (hk : k ≤ length p) :
    ∃ t : Tableau p, ∀ a : Fin n, a.val < k → labelColumn t a = 0 := by
  classical
  have hn : k ≤ n := hk.trans (partition_length_le p)
  let t₀ := canonicalTableau p
  let f : Fin k → Fin n := fun i => LengthBound.firstColumnLabel t₀ (Fin.castLE hk i)
  let g : Fin k → Fin n := Fin.castLE hn
  have hf : Function.Injective f :=
    (LengthBound.firstColumnLabel_injective t₀).comp (Fin.castLE_injective hk)
  obtain ⟨s, hs⟩ := Equiv.Perm.exists_extending_pair f g hf (Fin.castLE_injective hn)
  refine ⟨s • t₀, ?_⟩
  intro a ha
  let i : Fin k := ⟨a.val, ha⟩
  have hgi : g i = a := rfl
  have hsa : s⁻¹ a = f i := by
    rw [← hgi, ← hs i]
    exact s.symm_apply_apply _
  rw [labelColumn_smul, hsa]
  exact LengthBound.labelColumn_firstColumnLabel t₀ _

/-- Each omitted matrix coordinate of the generator is nonzero. -/
theorem alternator_specht_ne_zero {p : Partition n} (hk : k ≤ length p) :
    (canonicalSpechtRepresentation p).asAlgebraHom (initialAlternator n k) ≠ 0 := by
  classical
  obtain ⟨t, ht⟩ := exists_firstColumn_tableau hk
  have hc (s : initialPositionSubgroup n k) : s.val ∈ columnSubgroup t := by
    intro a
    change labelColumn t (s.val a) = labelColumn t a
    by_cases ha : a.val < k
    · rw [ht _ (initial_lt s a ha), ht a ha]
    · rw [s.property a (Nat.le_of_not_gt ha)]
  have he : (canonicalSpechtRepresentation p).asAlgebraHom (initialAlternator n k)
      (spechtPolytabloid t) =
      (Fintype.card (initialPositionSubgroup n k) : ℂ) • spechtPolytabloid t := by
    apply Subtype.ext
    simp only [initialAlternator, Specs.AdvancedFiniteGroupRepresentations.initialAlternator,
      map_sum, LinearMap.sum_apply, Representation.asAlgebraHom_single,
      Submodule.coe_sum, Submodule.coe_smul_of_tower]
    change (∑ s : initialPositionSubgroup n k,
      permutationSign s.val • permutationRepresentation p s.val (polytabloid t)) =
        (Fintype.card (initialPositionSubgroup n k) : ℂ) • polytabloid t
    simp only [column_action_polytabloid t ⟨_, hc _⟩, smul_smul,
      permutationSign_sq, one_smul, Finset.sum_const, Finset.card_univ]
    exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm
  intro hz
  rw [hz, LinearMap.zero_apply] at he
  have hnz : (Fintype.card (initialPositionSubgroup n k) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hv := (smul_eq_zero.mp he.symm).resolve_left hnz
  exact polytabloid_ne_zero t (congrArg Subtype.val hv)

/-- Injection of a single factor into a product, without a unitality claim. -/
private def coordinateInjection {ι : Type*} [DecidableEq ι] (R : ι → Type*)
    [∀ i, Ring (R i)] (i : ι) : R i →ₙ+* ∀ j, R j where
  toFun := Pi.single i
  map_zero' := Pi.single_zero i
  map_add' := Pi.single_add i
  map_mul' := Pi.single_mul i

/-- Central coordinate projectors isolate each simple matrix factor. -/
theorem single_mem_of_nonzero_coordinate {ι : Type*} [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, IsSimpleRing (R i)]
    (I : TwoSidedIdeal (∀ i, R i)) {F : ∀ i, R i} (hF : F ∈ I)
    (i : ι) (hi : F i ≠ 0) (x : R i) : Pi.single i x ∈ I := by
  let J := I.comap (coordinateInjection R i)
  have hj : F i ∈ J := by
    apply (TwoSidedIdeal.mem_comap (coordinateInjection R i)).mpr
    change Pi.single i (F i) ∈ I
    simpa only [← Pi.single_mul_left, one_mul] using
      I.mul_mem_left (Pi.single i 1) F hF
  have hone : Pi.single i (1 : R i) ∈ I :=
    (TwoSidedIdeal.mem_comap (coordinateInjection R i)).mp (IsSimpleRing.one_mem_of_ne_zero_mem J hi hj)
  simpa only [← Pi.single_mul, mul_one] using
    I.mul_mem_left (Pi.single i x) (Pi.single i 1) hone

/-- The full endomorphism ring of each nonzero finite Specht space is simple. -/
theorem spechtEnd_isSimpleRing (p : Partition n) : IsSimpleRing (Module.End ℂ (SpechtModule p)) := by
  let v := spechtPolytabloid (canonicalTableau p)
  have hv : v ≠ 0 := by
    intro he
    exact polytabloid_ne_zero _ (congrArg Subtype.val he)
  haveI : Nontrivial (SpechtModule p) := nontrivial_of_ne v 0 hv
  haveI : Nonempty (Fin (Module.finrank ℂ (SpechtModule p))) :=
    ⟨⟨0, Module.finrank_pos⟩⟩
  exact IsSimpleRing.of_ringEquiv
    (LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ (SpechtModule p))).symm.toRingEquiv
    inferInstance

end TensorKernel

/-- FR-D06: the unnormalized alternating sum generates the entire kernel. -/
theorem tensorKernel_generated [FiniteDimensional ℂ V] (n : ℕ)
    (hn : Module.finrank ℂ V < n) :
    TwoSidedIdeal.ker (tensorSlotAction V n).toRingHom =
      TwoSidedIdeal.span {initialAlternator n (Module.finrank ℂ V + 1)} := by
  classical
  let b := initialAlternator n (Module.finrank ℂ V + 1)
  let I : TwoSidedIdeal (GroupAlgebra n) := TwoSidedIdeal.span {b}
  have hb : b ∈ I := TwoSidedIdeal.subset_span (Set.mem_singleton b)
  have hI : I ≤ TwoSidedIdeal.ker (tensorSlotAction V n).toRingHom := by
    apply TwoSidedIdeal.span_le.mpr
    rintro a (rfl : a = b)
    exact TensorKernel.alternator_tensor_zero V (Nat.succ_le_of_lt hn) (Nat.lt_succ_self _)
  apply le_antisymm
  · intro a ha
    let e := AlgEquiv.ofBijective (spechtFamilyAlgebraMap (n := n) canonicalSpechtRepresentation)
      (spechtFamilyAlgebraMap_bijective _ (fun _ _ _ => rfl))
    let J : TwoSidedIdeal (∀ p : Partition n, Module.End ℂ (SpechtModule p)) := I.comap e.symm.toAlgHom.toRingHom.toNonUnitalRingHom
    have hJ : e b ∈ J := by
      dsimp only [J]
      rw [TwoSidedIdeal.mem_comap]
      change e.symm (e b) ∈ I
      simpa using hb
    have hblocks : ∀ p : Partition n, length p ≤ Module.finrank ℂ V → e a p = 0 := by
      have hh : a ∈ LinearMap.ker (tensorSlotAction V n).toLinearMap := ha
      rw [tensorKernel_blocks V n canonicalSpechtRepresentation (fun _ _ _ => rfl)] at hh
      exact hh
    haveI (p : Partition n) : IsSimpleRing (Module.End ℂ (SpechtModule p)) :=
      TensorKernel.spechtEnd_isSimpleRing p
    have hsingle (p : Partition n) : Pi.single p (e a p) ∈ J := by
      by_cases hp : length p ≤ Module.finrank ℂ V
      · simp only [hblocks p hp, Pi.single_zero]
        exact J.zero_mem
      · exact TensorKernel.single_mem_of_nonzero_coordinate J hJ p
          (TensorKernel.alternator_specht_ne_zero (Nat.succ_le_of_lt (Nat.lt_of_not_ge hp))) (e a p)
    have he : e a ∈ J := by
      have hh := J.finsetSum_mem Finset.univ (fun p => Pi.single p (e a p)) (fun p _ => hsingle p)
      have hsum : (∑ p, Pi.single p (e a p)) = e a := by
        funext q
        simp only [Finset.sum_apply, Finset.sum_pi_single, Finset.mem_univ, ite_true]
      rwa [hsum] at hh
    change e a ∈ I.comap e.symm.toAlgHom.toRingHom.toNonUnitalRingHom at he
    rw [TwoSidedIdeal.mem_comap] at he
    change e.symm (e a) ∈ I at he
    change a ∈ I
    simpa only [AlgEquiv.symm_apply_apply] using he
  · exact hI

/-- A permutation fixing all but at most one point fixes that point too. -/
theorem initialAlternator_one (n : ℕ) : initialAlternator n 1 = 1 := by
  classical
  have hs (s : initialPositionSubgroup n 1) : s = 1 := by
    apply Subtype.ext
    apply Equiv.ext
    intro a
    change s.val a = a
    by_cases ha : 1 ≤ a.val
    · exact s.property a ha
    · by_contra h
      have hsa : 1 ≤ (s.val a).val := by
        by_contra h'
        exact h (Fin.ext (by omega))
      have he := s.property (s.val a) hsa
      exact h (s.val.injective he)
  haveI : Unique (initialPositionSubgroup n 1) := { default := 1, uniq := hs }
  change (∑ s : initialPositionSubgroup n 1,
    MonoidAlgebra.single s.val (permutationSign s.val)) = 1
  rw [Fintype.sum_unique, hs default]
  change MonoidAlgebra.single (1 : SymmetricGroup n) (permutationSign 1) = 1
  rw [permutationSign_one]
  rfl

theorem tensorKernel_zero_dimension [FiniteDimensional ℂ V] (n : ℕ)
    (hn : 0 < n) (hd : Module.finrank ℂ V = 0) :
    TwoSidedIdeal.ker (tensorSlotAction V n).toRingHom = ⊤ := by
  rw [tensorKernel_generated V n (by omega), hd, zero_add, initialAlternator_one]
  apply TwoSidedIdeal.eq_top
  exact TwoSidedIdeal.subset_span (Set.mem_singleton _)

end AdvancedFiniteGroupRepresentations
