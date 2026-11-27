import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.PrimaryCohomologyVanishing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.CohomologyExactSequence
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.ArtinSchreierTensorAcyclic

namespace GaloisFormalization.GH.PrimaryCohomologyVanishing

open Model
open KrullLayers (AbsoluteGaloisGroup)
open ArtinSchreierTensor (Tensor primeFieldModule diagonalAction tensorInclusion tensorWp)

universe u v w

noncomputable section

section StableSubgroup

variable {G : Type v} [Group G] {M : Type w} [AddCommGroup M] [DistribMulAction G M]

@[instance_reducible]
private def subgroupAction (A : AddSubgroup M)
    (hA : ∀ (g : G) (a : M), a ∈ A → g • a ∈ A) : DistribMulAction G A where
  smul g a := ⟨g • (a : M), hA g a a.property⟩
  one_smul a := Subtype.ext (one_smul G (a : M))
  mul_smul g h a := Subtype.ext (mul_smul g h (a : M))
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g a b := Subtype.ext (smul_add g (a : M) (b : M))

private theorem subgroupContinuousSMul
    [TopologicalSpace G] [TopologicalSpace M] [ContinuousSMul G M] (A : AddSubgroup M)
    (hA : ∀ (g : G) (a : M), a ∈ A → g • a ∈ A) :
    let := subgroupAction A hA
    ContinuousSMul G A := by
  let : DistribMulAction G A := subgroupAction A hA
  exact Topology.IsInducing.subtypeVal.continuousSMul continuous_id rfl

private theorem nsmul_ker_stable (n : ℕ) (g : G) (a : M)
    (ha : a ∈ (nsmulAddMonoidHom (α := M) n).ker) :
    g • a ∈ (nsmulAddMonoidHom (α := M) n).ker := by
  change n • (DistribSMul.toAddMonoidHom M g) a = 0
  change n • a = 0 at ha
  rw [← map_nsmul (DistribSMul.toAddMonoidHom M g), ha, map_zero]

private theorem nsmul_range_stable (n : ℕ) (g : G) (a : M)
    (ha : a ∈ (nsmulAddMonoidHom (α := M) n).range) :
    g • a ∈ (nsmulAddMonoidHom (α := M) n).range := by
  obtain ⟨b, rfl⟩ := ha
  exact ⟨g • b, (map_nsmul (DistribSMul.toAddMonoidHom M g) n b).symm⟩

end StableSubgroup

section Vanishing

variable (p : ℕ) (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]
  [Fact p.Prime] [CharP k p] [IsSepClosure k S]
  (M : Type w) [AddCommGroup M] [DistribMulAction (AbsoluteGaloisGroup k S) M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (AbsoluteGaloisGroup k S) M]

local notation "Γ" => AbsoluteGaloisGroup k S

/-- Use the two adjacent positive-degree cohomology groups of the diagonal tensor. -/
private theorem vanishing_of_killed_by_prime (h : ∀ m : M, p • m = 0)
    (n : ℕ) (hn : 0 < n) : Subsingleton (ContinuousH Γ M (n + 1)) := by
  let : CharP S p := charP_of_injective_algebraMap' k p
  let : Module (ZMod p) M := primeFieldModule p M h
  let W := Tensor p S M
  let : DistribMulAction Γ W := diagonalAction p S M
  let : TopologicalSpace W := ⊥
  let : DiscreteTopology W := ⟨rfl⟩
  obtain ⟨hW, hacyclic⟩ := ArtinSchreierTensorAcyclic.tensorAcyclic p k S M h
  let : ContinuousSMul Γ W := hW
  obtain ⟨hi, hexact, hp⟩ := ArtinSchreierTensor.shortExact p k S M h
  obtain ⟨hiEquiv, hpEquiv⟩ := ArtinSchreierTensor.equivariant p k S M h
  let seq : ShortExactCoefficients Γ M W W :=
    ⟨(tensorInclusion p S M).toAddMonoidHom, (tensorWp p S M).toAddMonoidHom,
      hiEquiv, hpEquiv, hi, hexact, hp⟩
  obtain ⟨δ, hseq⟩ := continuousCohomology_longExact seq
  have : Subsingleton (ContinuousH Γ W n) := hacyclic n hn
  have : Subsingleton (ContinuousH Γ W (n + 1)) := hacyclic (n + 1) (Nat.succ_pos n)
  refine subsingleton_of_forall_eq 0 fun a => ?_
  obtain ⟨b, hb⟩ := (hseq.exact_left n a).mp (Subsingleton.elim _ _)
  rw [← hb, Subsingleton.elim b 0, map_zero]

/-- Induct on the exponent using the kernel and image of multiplication by p. -/
private theorem vanishing_of_killed_by_pow (r n : ℕ) (hn : 0 < n)
    (h : ∀ m : M, p ^ r • m = 0) : Subsingleton (ContinuousH Γ M (n + 1)) := by
  induction r generalizing M with
  | zero =>
    refine subsingleton_of_forall_eq 0 fun a => ?_
    obtain ⟨c, rfl⟩ := continuousClass_surjective (G := Γ) (M := M) (n + 1) a
    have hc : c = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      funext x
      change c.val.val x = 0
      simpa only [pow_zero, one_nsmul] using h (c.val.val x)
    rw [hc, map_zero]
  | succ r ih =>
    let mult : M →+ M := nsmulAddMonoidHom p
    let : DistribMulAction Γ mult.ker := subgroupAction mult.ker (nsmul_ker_stable p)
    let : ContinuousSMul Γ mult.ker := subgroupContinuousSMul mult.ker (nsmul_ker_stable p)
    let : DistribMulAction Γ mult.range := subgroupAction mult.range (nsmul_range_stable p)
    let : ContinuousSMul Γ mult.range := subgroupContinuousSMul mult.range (nsmul_range_stable p)
    let seq : ShortExactCoefficients Γ mult.ker M mult.range :=
      { i := mult.ker.subtype
        p := mult.rangeRestrict
        i_equivariant := fun _ _ => rfl
        p_equivariant := fun g m =>
          Subtype.ext (map_nsmul (DistribSMul.toAddMonoidHom M g) p m).symm
        i_injective := Subtype.val_injective
        exact := by
          intro m
          constructor
          · intro hm
            exact ⟨⟨m, congrArg Subtype.val hm⟩, rfl⟩
          · rintro ⟨a, rfl⟩
            exact Subtype.ext a.property
        p_surjective := mult.rangeRestrict_surjective }
    have hker (a : mult.ker) : p • a = 0 := Subtype.ext a.property
    have hrange (a : mult.range) : p ^ r • a = 0 := by
      obtain ⟨m, hm⟩ := a.property
      apply Subtype.ext
      change p ^ r • (a : M) = 0
      rw [← hm]
      change p ^ r • (p • m) = 0
      rw [← mul_nsmul, ← pow_succ']
      exact h m
    have : Subsingleton (ContinuousH Γ mult.ker (n + 1)) :=
      vanishing_of_killed_by_prime p k S mult.ker hker n hn
    have : Subsingleton (ContinuousH Γ mult.range (n + 1)) := ih mult.range hrange
    obtain ⟨_, hseq⟩ := continuousCohomology_longExact seq
    refine subsingleton_of_forall_eq 0 fun a => ?_
    obtain ⟨b, hb⟩ := (hseq.exact_middle (n + 1) a).mp (Subsingleton.elim _ _)
    rw [← hb, Subsingleton.elim b 0, map_zero]

omit [Fact p.Prime] [CharP k p] [DistribMulAction Γ M] [ContinuousSMul Γ M] in
/-- A continuous cochain has finite image, so the annihilating exponents can be bounded
uniformly on its values. -/
private theorem cochain_killed_by_pow {n : ℕ} (c : continuousCochains Γ M n)
    (h : ∀ m : M, ∃ r : ℕ, p ^ r • m = 0) :
    ∃ r : ℕ, ∀ x : Fin n → Γ, p ^ r • c.val x = 0 := by
  classical
  choose e he using h
  have hfin : (Set.range c.val).Finite := (isCompact_range c.property).finite_of_discrete
  let r := (hfin.toFinset).sup e
  refine ⟨r, fun x => ?_⟩
  have hle : e (c.val x) ≤ r := Finset.le_sup (f := e) (hfin.mem_toFinset.mpr ⟨x, rfl⟩)
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
  rw [hj, pow_add, mul_nsmul, he, nsmul_zero]

end Vanishing

/-- For a field of characteristic p, the continuous cohomology of its absolute Galois
group with discrete p-primary coefficients vanishes in degrees at least two. -/
theorem vanishing :
    Specs.GaloisFormalization.GH.PrimaryCohomologyVanishing.vanishing_type.{u, v, w} := by
  intro p k S _ _ _ _ _ hp M _ _ _ _ _ h q hq
  have : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero k hp.ne'⟩
  cases q with
  | zero => omega
  | succ n =>
    have hn : 0 < n := by omega
    let G := AbsoluteGaloisGroup k S
    refine subsingleton_of_forall_eq 0 fun a => ?_
    obtain ⟨c, rfl⟩ := continuousClass_surjective (G := G) (M := M) (n + 1) a
    obtain ⟨r, hr⟩ := cochain_killed_by_pow p k S M c.val h
    let A := (nsmulAddMonoidHom (α := M) (p ^ r)).ker
    let : DistribMulAction G A := subgroupAction A (nsmul_ker_stable (p ^ r))
    let : ContinuousSMul G A := subgroupContinuousSMul A (nsmul_ker_stable (p ^ r))
    let i : A →+ M := A.subtype
    have hi : ∀ (g : G) (a : A), i (g • a) = g • i a := fun _ _ => rfl
    let cA : continuousCochains G A (n + 1) :=
      ⟨fun x => ⟨c.val.val x, hr x⟩, c.val.property.subtype_mk _⟩
    have hmap : continuousCochainMap (MonoidHom.id G) continuous_id i (n + 1) cA = c.val :=
      Subtype.ext rfl
    have hcA : continuousDifferential G A (n + 1) cA = 0 := by
      have hc : continuousDifferential G M (n + 1) c.val = 0 := c.property
      have e := continuousCochainMap_d (MonoidHom.id G) continuous_id i hi (n + 1) cA
      rw [hmap, hc] at e
      apply Subtype.ext
      funext x
      exact Subtype.ext (congrArg (fun f : continuousCochains G M (n + 2) => f.val x) e)
    let z : continuousCocycles G A (n + 1) := ⟨cA, hcA⟩
    have hA (a : A) : p ^ r • a = 0 := Subtype.ext a.property
    have : Subsingleton (ContinuousH G A (n + 1)) :=
      vanishing_of_killed_by_pow p k S A r n hn hA
    have hz : continuousClass G A (n + 1) z = 0 := Subsingleton.elim _ _
    -- The inclusion sends the class of the lifted cocycle to the original class.
    have he := congrArg (continuousCohomologyMap (MonoidHom.id G) continuous_id i hi (n + 1)) hz
    rw [map_zero] at he
    exact he

end

end GaloisFormalization.GH.PrimaryCohomologyVanishing
