import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.ProfiniteIntegers.ProjectionKernels
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.ProfiniteIntegers.IntegerDensity

noncomputable section
namespace AdvancedFieldTheory.ProfiniteIntegers

/-- Integer representatives already make every residue projection surjective. -/
theorem π_surjective : Specs.AdvancedFieldTheory.ProjectionKernels.ProjectionSurjective := by
  intro n b
  refine ⟨ι (ZMod.cast b), ?_⟩
  exact ZMod.intCast_zmod_cast b

/-- Multiplication by n lands in the kernel of the n-th projection. -/
theorem nsmul_mem_ker_π (n : ℕ+) (a : Zhat) : (n : ℕ) • a ∈ (π n).ker := by
  change π n ((n : ℕ) • a) = 0
  rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- Every kernel is clopen because its target is finite discrete. -/
theorem clopen_ker_π : Specs.AdvancedFieldTheory.ProjectionKernels.KernelClopen := by
  intro n
  exact (isClopen_discrete ({0} : Set (ZMod (n : ℕ)))).preimage (continuous_π n)

/-- Integer multiples approximate every point of the kernel simultaneously at
any finite list of coordinates, including the n-th coordinate. -/
theorem closure_integer_multiples :
    Specs.AdvancedFieldTheory.ProjectionKernels.IntegerMultiplesClosure := by
  intro n
  apply Set.Subset.antisymm
  · apply closure_minimal ?_ (clopen_ker_π n).isClosed
    rintro _ ⟨z, rfl⟩
    change ι ((n : ℕ) • z) ∈ (π n).ker
    rw [map_nsmul]
    exact nsmul_mem_ker_π n (ι z)
  · intro a ha
    apply mem_closure_iff.mpr
    intro U hU haU
    obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
    have haV : a.val ∈ V := by rw [← hVU] at haU; exact haU
    obtain ⟨s, W, hW, hWV⟩ := isOpen_pi_iff.mp hV a.val haV
    obtain ⟨z, hz⟩ := finite_coordinate_matching a (insert n s)
    have hzn : (z : ZMod (n : ℕ)) = 0 := by
      calc
        (z : ZMod (n : ℕ)) = π n a := hz n (Finset.mem_insert_self _ _)
        _ = 0 := ha
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z (n : ℕ)).mp hzn
    have hzk : (n : ℕ) • k = z := by simpa using hk.symm
    refine ⟨ι ((n : ℕ) • k), ?_, ⟨k, rfl⟩⟩
    rw [hzk, ← hVU]
    apply hWV
    intro m hm
    have he : (ι z).val m = a.val m := hz m (Finset.mem_insert_of_mem hm)
    rw [he]
    exact (hW m hm).2

/-- Compactness makes the continuous multiplication image closed. It contains
all integer multiples and is itself contained in the projection kernel. -/
theorem nsmul_range_eq_closure :
    Specs.AdvancedFieldTheory.ProjectionKernels.MultiplicationImageClosure := by
  intro n
  apply Set.Subset.antisymm
  · rw [closure_integer_multiples n]
    rintro _ ⟨a, rfl⟩
    exact nsmul_mem_ker_π n a
  · apply closure_minimal ?_ (isCompact_range (continuous_id.nsmul (n : ℕ))).isClosed
    rintro _ ⟨z, rfl⟩
    exact ⟨ι z, (map_nsmul ι (n : ℕ) z).symm⟩

/-- The kernel is the image of multiplication on the entire profinite group. -/
theorem ker_π : Specs.AdvancedFieldTheory.ProjectionKernels.KernelMultiples := by
  intro n
  apply SetLike.coe_injective
  change ((π n).ker : Set Zhat) = Set.range (fun a : Zhat => (n : ℕ) • a)
  rw [nsmul_range_eq_closure n, closure_integer_multiples n]
  rfl

/-- The quotient by the kernel has exactly n elements. -/
theorem index_ker_π : Specs.AdvancedFieldTheory.ProjectionKernels.KernelIndex := by
  intro n
  rw [AddSubgroup.index_eq_card]
  calc
    Nat.card (Zhat ⧸ (π n).ker) = Nat.card (ZMod (n : ℕ)) :=
      Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective (π n) (π_surjective n)).toEquiv
    _ = (n : ℕ) := by simp [Nat.card_eq_fintype_card]

end AdvancedFieldTheory.ProfiniteIntegers
