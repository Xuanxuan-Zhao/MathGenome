import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SplitPlaces
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.FiniteKummerSplitting
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

namespace LinearAlgebraicGroups.Arithmetic

universe u v w

open IntermediateField

/-- If the inverse of the exponent is integral at a finite place, the exponent
is a unit in the valuation ring and has nonzero reduction. -/
private theorem natCast_residue_ne_zero {K : Type u} [Field K]
    (D : GlobalFieldData.{u, v} K) (v : D.FinitePlace) (n : ℕ) (hn : (n : K) ≠ 0)
    (h : D.embedding (.inl v) (n : K)⁻¹ ∈ D.integers v) :
    (n : IsLocalRing.ResidueField (D.integers v)) ≠ 0 := by
  let emb : K →+* D.FiniteCompletion v := D.embedding (.inl v)
  let a : D.integers v := ⟨emb (n : K)⁻¹, h⟩
  have ha : (n : D.integers v) * a = 1 := by
    apply Subtype.ext
    change (n : D.FiniteCompletion v) * emb (n : K)⁻¹ = 1
    rw [← map_natCast emb, ← map_mul, mul_inv_cancel₀ hn, map_one]
  have hr := congrArg (IsLocalRing.residue (D.integers v)) ha
  intro hz
  simp only [map_mul, map_natCast, map_one, hz, zero_mul] at hr
  exact zero_ne_one hr

theorem exists_finiteKummerSplittingPlace : FiniteKummerSplittingSpec.ExistsPlace.{u, v, w} := by
  classical
  intro K E _ _ _ _ _ D S n hn hnK P hP
  let C := SeparableClosure K
  have : NeZero (n : C) :=
    ⟨by simpa only [map_natCast, map_zero] using (algebraMap K C).injective.ne hnK⟩
  let i : E →ₐ[K] C := IsSepClosed.lift
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot C n
  have hrep (c : P) : ∃ a : Eˣ, Kummer.classOf n a = c.val :=
    QuotientGroup.mk'_surjective _ c.val
  choose a ha using hrep
  have hroot (c : P) : ∃ b : C, b ^ n = i (a c : E) :=
    IsSepClosed.exists_pow_nat_eq _ _
  choose b hb using hroot

  -- Adjoin all the selected roots together with the embedded copy of E,
  -- then take the normal closure over K.
  let T : Set C := insert ζ (Set.range b)
  have : Finite P := hP
  have : Finite T := (Set.finite_range b).insert ζ
  let A := adjoin K T
  have : FiniteDimensional K A :=
    finiteDimensional_adjoin (fun x _ ↦ Algebra.IsSeparable.isIntegral K x)
  have : FiniteDimensional K i.fieldRange := i.toLinearMap.finiteDimensional_range
  let B := i.fieldRange ⊔ A
  let L := normalClosure K B C
  have hBL : B ≤ L := le_normalClosure B
  have hAL : A ≤ L := le_sup_right.trans hBL
  have hTL : T ⊆ (L : Set C) := fun _ hx ↦ hAL (subset_adjoin K T hx)
  have hIL : i.fieldRange ≤ L := le_sup_left.trans hBL
  let j : E →ₐ[K] L := i.codRestrict L.toSubalgebra fun x ↦
    hIL (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
  let ζL : L := ⟨ζ, hTL (Set.mem_insert _ _)⟩
  have hζL : IsPrimitiveRoot ζL n := IsPrimitiveRoot.of_map_of_injective
    (f := L.val) hζ L.val.injective

  let U := (D.finite_nonintegral ((n : K)⁻¹)).toFinset
  obtain ⟨v, hv, hsplit⟩ := exists_splitPlace_outside (L := L) D (S ∪ U)
  obtain ⟨f, hf⟩ := (splitsCompletelyAt_iff_embedding (L := L) D v).mp hsplit
  let e := f.comp j.toRingHom
  have he : e.comp (algebraMap K E) = D.embedding (.inl v) := by
    apply RingHom.ext
    intro x
    exact (congrArg f (j.commutes x)).trans (DFunLike.congr_fun hf x)
  have hvU : v ∉ U := fun h ↦ hv (Finset.mem_union_right S h)
  have hinv : D.embedding (.inl v) (n : K)⁻¹ ∈ D.integers v := by
    by_contra h
    exact hvU ((D.finite_nonintegral ((n : K)⁻¹)).mem_toFinset.mpr h)
  refine ⟨v, fun h ↦ hv (Finset.mem_union_left U h), e, he, ?_,
    ⟨f ζL, hζL.map_of_injective f.injective⟩, natCast_residue_ne_zero D v n hnK hinv⟩
  intro c hc
  let d : P := ⟨c, hc⟩
  let bL : L := ⟨b d, hTL (Set.mem_insert_of_mem _ ⟨d, rfl⟩)⟩
  have hbL : bL ^ n = j (a d : E) := Subtype.ext (hb d)
  have hpow : f bL ^ n = e (a d : E) := by
    rw [← map_pow, hbL]
    rfl
  have hbne : f bL ≠ 0 := by
    intro hz
    rw [hz, zero_pow (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn))] at hpow
    exact (e.injective.ne (Units.ne_zero (a d))) (hpow.symm.trans (map_zero e).symm)
  have hd : Kummer.classOf n (a d) = c := ha d
  rw [← hd]
  change Kummer.classOf n (Units.map e.toMonoidHom (a d)) = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨Units.mk0 (f bL) hbne, Units.ext hpow⟩

end LinearAlgebraicGroups.Arithmetic
