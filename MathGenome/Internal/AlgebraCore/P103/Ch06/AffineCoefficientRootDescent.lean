import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.AffineCoefficientRootDescent

namespace P103.Ch06.CoefficientRootDescent

universe u v

variable {k : Type u} {Ω : Type v} [Field k] [Field Ω] [Algebra k Ω]

/-- Applying a field homomorphism to finitely many rational expressions uses
only finitely many images of base-field constants. -/
theorem finite_constant_support (r : Ω →+* Ω) {d : ℕ} (t : Fin d → Ω)
    (S : Finset (IntermediateField.adjoin k (Set.range t))) :
    ∃ C : Finset Ω, (∀ x ∈ C, x ∈ Set.range (r ∘ algebraMap k Ω)) ∧
      ∀ a ∈ S, r (a : Ω) ∈
        (IntermediateField.adjoin (IntermediateField.adjoin k (C : Set Ω))
          (Set.range (r ∘ t))).restrictScalars k := by
  classical
  let R : Set Ω := Set.range (r ∘ algebraMap k Ω)
  let Z : Set Ω := Set.range (r ∘ t)
  let G := IntermediateField.adjoin k (R ∪ Z)
  have hroot (x : Ω) (hx : x ∈ IntermediateField.adjoin k (Set.range t)) : r x ∈ G := by
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact IntermediateField.subset_adjoin k (R ∪ Z) (Or.inr ⟨i, rfl⟩)
    | algebraMap x =>
        exact IntermediateField.subset_adjoin k (R ∪ Z) (Or.inl ⟨x, rfl⟩)
    | add x y hx hy ihx ihy => simpa only [map_add] using G.add_mem ihx ihy
    | inv x hx ih => simpa only [map_inv₀] using G.inv_mem ih
    | mul x y hx hy ihx ihy => simpa only [map_mul] using G.mul_mem ihx ihy
  choose T hT hmem using fun (a : IntermediateField.adjoin k (Set.range t)) => IntermediateField.exists_finset_of_mem_adjoin (hroot (a : Ω) a.property)
  let U : Finset Ω := S.biUnion T
  let C : Finset Ω := U.filter (· ∈ R)
  let c := IntermediateField.adjoin k (C : Set Ω)
  let P := (IntermediateField.adjoin c Z).restrictScalars k
  have hU (x : Ω) (hx : x ∈ U) : x ∈ R ∪ Z := by
    obtain ⟨a, ha, hx⟩ := Finset.mem_biUnion.mp hx
    exact hT a hx
  have hUP : (U : Set Ω) ⊆ P := by
    intro x hx
    rcases hU x hx with hR | hZ
    · have hxC : x ∈ c := IntermediateField.subset_adjoin k _ (Finset.mem_filter.mpr ⟨hx, hR⟩)
      exact (IntermediateField.adjoin c Z).algebraMap_mem ⟨x, hxC⟩
    · exact IntermediateField.subset_adjoin c Z hZ
  refine ⟨C, ?_, ?_⟩
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro a ha
    exact (IntermediateField.adjoin_le_iff.mpr hUP)
      ((IntermediateField.adjoin.mono k _ _ (by
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨a, ha, hx⟩)) (hmem a))

/-- The common bounded-exponent root field, realized in the ambient field. -/
def boundedRootField (p e : ℕ) [Fact p.Prime] [CharP Ω p] : IntermediateField k Ω :=
  { (algebraMap k Ω).fieldRange.comap (iterateFrobenius Ω p e) with
    algebraMap_mem' := fun x => by
      change (algebraMap k Ω x) ^ (p ^ e) ∈ (algebraMap k Ω).fieldRange
      exact ⟨x ^ (p ^ e), map_pow _ _ _⟩ }

@[simp] theorem mem_boundedRootField (p e : ℕ) [Fact p.Prime] [CharP Ω p] (x : Ω) :
    x ∈ boundedRootField (k := k) p e ↔ x ^ (p ^ e) ∈ (algebraMap k Ω).range := Iff.rfl

/-- The finite purely inseparable constant extension and rational coefficient roots. -/
theorem coefficientRootDescent : coefficientRootDescentType.{u,v} := by
  intro k Ω _ _ _ _ p _ _ d t _ht e S
  have : CharP Ω p := charP_of_injective_algebraMap (algebraMap k Ω).injective p
  let f := iterateFrobeniusEquiv Ω p e
  let r := f.symm
  have hr (x : Ω) : r x ^ (p ^ e) = x := f.apply_symm_apply x
  obtain ⟨C, hC, hS⟩ := finite_constant_support r.toRingHom t S
  let c := IntermediateField.adjoin k (C : Set Ω)
  let z : Fin d → Ω := r ∘ t
  let P := (IntermediateField.adjoin c (Set.range z)).restrictScalars k
  have hCpow (x : Ω) (hx : x ∈ C) : x ^ (p ^ e) ∈ (algebraMap k Ω).range := by
    obtain ⟨a, rfl⟩ := hC x hx
    exact ⟨a, (hr _).symm⟩
  have hc : c ≤ boundedRootField (k := k) p e := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    exact hCpow x hx
  have hcpow (a : c) : (a : Ω) ^ (p ^ e) ∈ (algebraMap k Ω).range := hc a.property
  have hfin : Module.Finite k c := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    obtain ⟨a, ha⟩ := hCpow x hx
    apply IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos e)
    rw [← ha]
    exact isIntegral_algebraMap
  have hpure : IsPurelyInseparable k c := by
    apply (isPurelyInseparable_iff_pow_mem k p).mpr
    intro a
    obtain ⟨x, hx⟩ := hcpow a
    refine ⟨e, x, ?_⟩
    apply Subtype.ext
    exact hx
  have hKP : IntermediateField.adjoin k (Set.range t) ≤ P := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨i, rfl⟩
    have hzP : z i ∈ P := IntermediateField.subset_adjoin c (Set.range z) ⟨i, rfl⟩
    have hm : z i ^ (p ^ e) ∈ P := pow_mem hzP _
    change t i ∈ P
    simpa only [z, Function.comp_apply, hr] using hm
  refine ⟨C, c, z, rfl, hCpow, hfin, hpure, hcpow, (fun i => hr (t i)), hKP, ?_⟩
  intro a ha
  exact ⟨⟨r (a : Ω), hS a ha⟩, hr (a : Ω)⟩

end P103.Ch06.CoefficientRootDescent
