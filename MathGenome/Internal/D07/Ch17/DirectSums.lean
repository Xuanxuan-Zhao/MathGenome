import MathGenome.Internal.D07.Ch17.IntertwinersEquivalence
import MathGenome.Internal.Specs.D07.Ch17.DirectSums

/-! Direct sums, invariant complements and simultaneous block forms.
No finiteness or characteristic restriction on the group or field is used. -/
namespace D07.Ch17.DirectSums

universe u v w x t z

noncomputable section
open Specs.D07.Ch17.DirectSums
open DirectSum

theorem product_laws : ProductLaws.{u,v,w,x} := by
  intro K G V W _ _ _ _ _ _ ρ σ
  exact ⟨fun _ _ => rfl, (ρ.prod σ).map_one, (ρ.prod σ).map_mul⟩

theorem product_intertwiners : ProductIntertwiners.{u,v,w,x} := by
  intro K G V W _ _ _ _ _ _ ρ σ
  refine ⟨⟨?_⟩, ⟨?_⟩, ⟨fun _ _ => rfl⟩, ⟨fun _ _ => rfl⟩⟩
  · intro g v
    ext <;> simp [Representation.prod]
  · intro g w
    ext <;> simp [Representation.prod]

theorem internal_equivalence : InternalEquivalence.{u,v,w} := by
  intro K G E _ _ _ _ ρ U W h
  refine ⟨Representation.Equiv.mk (U.toSubmodule.prodEquivOfIsCompl W.toSubmodule h) ?_,
    fun _ => rfl⟩
  intro g
  apply LinearMap.ext
  intro p
  exact (map_add (ρ g) (p.1 : E) (p.2 : E)).symm

section Blocks
variable {K : Type u} {G : Type v} {E : Type w} {ι : Type t} {κ : Type z}
  [Field K] [Group G] [AddCommGroup E] [Module K E]

lemma mem_leftSpan (b : Module.Basis (ι ⊕ κ) K E) (x : E) :
    x ∈ leftSpan b ↔ ∀ j, b.repr x (Sum.inr j) = 0 := by
  classical
  rw [leftSpan, b.mem_span_image]
  constructor
  · intro h j
    by_contra hn
    obtain ⟨i, hi⟩ := h (Finsupp.mem_support_iff.mpr hn)
    cases hi
  · intro h i hi
    cases i with
    | inl i => exact ⟨i, rfl⟩
    | inr j => exact False.elim ((Finsupp.mem_support_iff.mp hi) (h j))

lemma mem_rightSpan (b : Module.Basis (ι ⊕ κ) K E) (x : E) :
    x ∈ rightSpan b ↔ ∀ i, b.repr x (Sum.inl i) = 0 := by
  classical
  rw [rightSpan, b.mem_span_image]
  constructor
  · intro h i
    by_contra hn
    obtain ⟨j, hj⟩ := h (Finsupp.mem_support_iff.mpr hn)
    cases hj
  · intro h j hj
    cases j with
    | inr j => exact ⟨j, rfl⟩
    | inl i => exact False.elim ((Finsupp.mem_support_iff.mp hj) (h i))

lemma block_spans_complementary (b : Module.Basis (ι ⊕ κ) K E) :
    IsCompl (leftSpan b) (rightSpan b) :=
  b.linearIndependent.isCompl_span_image b.span_eq Set.isCompl_range_inl_range_inr

lemma invariant_span_iff (ρ : Representation K G E) (s : Set E) :
    Invariant ρ (Submodule.span K s) ↔ ∀ g x, x ∈ s → ρ g x ∈ Submodule.span K s := by
  constructor
  · intro h g x hx
    exact h g x (Submodule.subset_span hx)
  · intro h g x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact h g x hx
    | zero => simp
    | add x y hx hy hx' hy' => simpa using (Submodule.span K s).add_mem hx' hy'
    | smul a x hx hx' => simpa using (Submodule.span K s).smul_mem a hx'

lemma invariant_left_iff (ρ : Representation K G E) (b : Module.Basis (ι ⊕ κ) K E) :
    Invariant ρ (leftSpan b) ↔ ∀ g i j, b.repr (ρ g (b (Sum.inl i))) (Sum.inr j) = 0 := by
  rw [leftSpan, invariant_span_iff]
  constructor
  · intro h g i
    exact (mem_leftSpan b _).mp (h g _ ⟨_, ⟨i, rfl⟩, rfl⟩)
  · intro h g x hx
    rcases hx with ⟨_, ⟨i, rfl⟩, rfl⟩
    exact (mem_leftSpan b _).mpr (h g i)

lemma invariant_right_iff (ρ : Representation K G E) (b : Module.Basis (ι ⊕ κ) K E) :
    Invariant ρ (rightSpan b) ↔ ∀ g j i, b.repr (ρ g (b (Sum.inr j))) (Sum.inl i) = 0 := by
  rw [rightSpan, invariant_span_iff]
  constructor
  · intro h g j
    exact (mem_rightSpan b _).mp (h g _ ⟨_, ⟨j, rfl⟩, rfl⟩)
  · intro h g x hx
    rcases hx with ⟨_, ⟨j, rfl⟩, rfl⟩
    exact (mem_rightSpan b _).mpr (h g j)

end Blocks

theorem triangular_criterion : TriangularCriterion.{u,v,w,t,z} := by
  intro K G E ι κ _ _ _ _ _ _ _ _ ρ b
  simpa only [LinearMap.toMatrix_apply, forall_comm (α := κ) (β := ι)] using invariant_left_iff ρ b

theorem common_block_criterion : CommonBlockCriterion.{u,v,w,t,z} := by
  intro K G E ι κ _ _ _ _ _ _ _ _ ρ b
  refine ⟨block_spans_complementary b, ?_⟩
  rw [invariant_left_iff, invariant_right_iff]
  simp only [LinearMap.toMatrix_apply]
  constructor
  · rintro ⟨hL, hR⟩ g
    exact ⟨fun i j => hR g j i, fun j i => hL g i j⟩
  · intro h
    exact ⟨fun g i j => (h g).2 j i, fun g j i => (h g).1 i j⟩

section Concatenation
variable {K : Type u} {E : Type w} {ι : Type t} {κ : Type z}
  [Field K] [AddCommGroup E] [Module K E]
  (U W : Submodule K E) (h : IsCompl U W)
  (bU : Module.Basis ι K U) (bW : Module.Basis κ K W)

/-- The concatenated basis is the product basis transported by addition. -/
def concatenatedBasis : Module.Basis (ι ⊕ κ) K E :=
  (bU.prod bW).map (U.prodEquivOfIsCompl W h)

@[simp] lemma concatenatedBasis_inl (i : ι) :
    concatenatedBasis U W h bU bW (Sum.inl i) = (bU i : E) := by
  simp [concatenatedBasis, Submodule.coe_prodEquivOfIsCompl']

@[simp] lemma concatenatedBasis_inr (j : κ) :
    concatenatedBasis U W h bU bW (Sum.inr j) = (bW j : E) := by
  simp [concatenatedBasis, Submodule.coe_prodEquivOfIsCompl']

lemma leftSpan_concatenatedBasis : leftSpan (concatenatedBasis U W h bU bW) = U := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp
  · intro x hx
    apply (mem_leftSpan _ _).mpr
    intro j
    change (bU.prod bW).repr ((U.prodEquivOfIsCompl W h).symm x) (Sum.inr j) = 0
    have he : (U.prodEquivOfIsCompl W h).symm x = (⟨x, hx⟩, 0) := by
      apply (U.prodEquivOfIsCompl W h).symm_apply_eq.mpr
      simp [Submodule.coe_prodEquivOfIsCompl']
    simp [he]

end Concatenation

theorem concatenated_block_basis : ConcatenatedBlockBasis.{u,v,w,t,z} := by
  intro K G E ι κ _ _ _ _ _ _ _ _ ρ U W h bU bW
  let b := concatenatedBasis U.toSubmodule W.toSubmodule h bU bW
  refine ⟨b, concatenatedBasis_inl _ _ _ _ _, concatenatedBasis_inr _ _ _ _ _, ?_⟩
  intro g
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₁]
      change (bU.prod bW).repr
        ((U.toSubmodule.prodEquivOfIsCompl W.toSubmodule h).symm
          (ρ g (b (Sum.inl j)))) (Sum.inl i) = _
      rw [show b (Sum.inl j) = (bU j : E) from concatenatedBasis_inl _ _ _ _ _ j]
      change (bU.prod bW).repr
        ((U.toSubmodule.prodEquivOfIsCompl W.toSubmodule h).symm
          ((U.toRepresentation g (bU j) : U.toSubmodule) : E)) _ = _
      rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
      simp
    | inr j =>
      simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      change (bU.prod bW).repr
        ((U.toSubmodule.prodEquivOfIsCompl W.toSubmodule h).symm
          (ρ g (b (Sum.inr j)))) (Sum.inl i) = 0
      rw [show b (Sum.inr j) = (bW j : E) from concatenatedBasis_inr _ _ _ _ _ j]
      change (bU.prod bW).repr
        ((U.toSubmodule.prodEquivOfIsCompl W.toSubmodule h).symm
          ((W.toRepresentation g (bW j) : W.toSubmodule) : E)) _ = _
      rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
      simp
  | inr i =>
    cases j with
    | inl j =>
      simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      change (bU.prod bW).repr
        ((U.toSubmodule.prodEquivOfIsCompl W.toSubmodule h).symm
          (ρ g (b (Sum.inl j)))) (Sum.inr i) = 0
      rw [show b (Sum.inl j) = (bU j : E) from concatenatedBasis_inl _ _ _ _ _ j]
      change (bU.prod bW).repr
        ((U.toSubmodule.prodEquivOfIsCompl W.toSubmodule h).symm
          ((U.toRepresentation g (bU j) : U.toSubmodule) : E)) _ = _
      rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
      simp
    | inr j =>
      simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₂₂]
      change (bU.prod bW).repr
        ((U.toSubmodule.prodEquivOfIsCompl W.toSubmodule h).symm
          (ρ g (b (Sum.inr j)))) (Sum.inr i) = _
      rw [show b (Sum.inr j) = (bW j : E) from concatenatedBasis_inr _ _ _ _ _ j]
      change (bU.prod bW).repr
        ((U.toSubmodule.prodEquivOfIsCompl W.toSubmodule h).symm
          ((W.toRepresentation g (bW j) : W.toSubmodule) : E)) _ = _
      rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
      simp

theorem extended_triangular_basis : ExtendedTriangularBasis.{u,v,w,t} := by
  intro K G E ι _ _ _ _ _ _ _ ρ U bU
  obtain ⟨W, h⟩ := U.toSubmodule.exists_isCompl
  let bW := Module.finBasis K W
  let b := concatenatedBasis U.toSubmodule W h bU bW
  have hb : leftSpan b = U.toSubmodule := leftSpan_concatenatedBasis _ _ _ _ _
  refine ⟨Module.finrank K W, b, concatenatedBasis_inl _ _ _ _ _, hb, ?_⟩
  apply (triangular_criterion K G E ι (Fin (Module.finrank K W)) ρ b).mp
  rw [hb]
  exact fun g _ hx => U.apply_mem_toSubmodule g hx

theorem arbitrary_direct_sum : ArbitraryDirectSum.{u,v,t,w} := by
  classical
  intro K G ι V _ _ _ _ ρ
  refine ⟨fun _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro i
    constructor
    intro g x
    exact (DirectSum.lmap_lof (fun i => ρ i g) i x).symm
  · intro i
    exact ⟨fun _ _ => rfl⟩
  · intro f
    constructor
    · rintro ⟨x, hx⟩
      have he : (fun i => x i) = f := funext hx
      exact he ▸ x.finite_support
    · intro hf
      refine ⟨DFinsupp.mk hf.toFinset (fun i => f i), ?_⟩
      intro i
      by_cases hi : f i = 0 <;> simp [DFinsupp.mk_apply, hi]

theorem infinite_product_boundary : InfiniteProductBoundary := by
  rintro ⟨x, hx⟩
  have hf := x.finite_support
  have hs : {i | x i ≠ 0} = (Set.univ : Set ℕ) := by
    ext i
    simp [hx i]
  rw [hs] at hf
  exact Set.infinite_univ hf

/-- A rational shear action. Its first axis is invariant and its second axis
is a vector-space complement but is not invariant. -/
theorem nonInvariant_complement : NonInvariantComplement := by
  let ρ : Representation ℚ (Multiplicative ℚ) (ℚ × ℚ) := {
    toFun := fun g =>
      ((LinearMap.fst ℚ ℚ ℚ) + g.toAdd • LinearMap.snd ℚ ℚ ℚ).prod (LinearMap.snd ℚ ℚ ℚ)
    map_one' := by
      apply LinearMap.ext
      intro p
      apply Prod.ext <;> simp
    map_mul' := by
      intro g h
      apply LinearMap.ext
      intro p
      apply Prod.ext <;> simp [add_smul, add_comm, add_left_comm]
  }
  let U := LinearMap.ker (LinearMap.snd ℚ ℚ ℚ)
  let W := LinearMap.ker (LinearMap.fst ℚ ℚ ℚ)
  refine ⟨Multiplicative ℚ, inferInstance, ρ, U, W, ?_, ?_, ?_⟩
  · dsimp [U, W]
    rw [LinearMap.ker_snd, LinearMap.ker_fst]
    exact LinearMap.isCompl_range_inl_inr
  · intro g p hp
    exact hp
  · intro h
    have hh := h (Multiplicative.ofAdd 1) (0, 1) (by simp [W])
    change (0 : ℚ) + 1 • 1 = 0 at hh
    simp at hh

end
end D07.Ch17.DirectSums
