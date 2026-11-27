import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.Cochains
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.TraceOne
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.TraceContraction

namespace GaloisFormalization.GH

universe u v w

open scoped BigOperators

section Homogeneous

variable {G V : Type*} [Group G] [AddCommGroup V] [DistribMulAction G V]

private def IsEquivariant {n : ℕ} (f : (Fin (n + 1) → G) → V) : Prop :=
  ∀ (g : G) (x : Fin (n + 1) → G), f (g • x) = g • f x

private def homogeneousExtension {n : ℕ} (f : (Fin n → G) → V)
    (x : Fin (n + 1) → G) : V :=
  x 0 • f (fun i => (x i.castSucc)⁻¹ * x i.succ)

private theorem homogeneousExtension_equivariant {n : ℕ} (f : (Fin n → G) → V) :
    IsEquivariant (homogeneousExtension f) := by
  intro g x
  simp [homogeneousExtension, Pi.smul_apply, smul_eq_mul, mul_inv_rev, mul_assoc, mul_smul]

private theorem homogeneousExtension_partialProd {n : ℕ} (f : (Fin n → G) → V)
    (x : Fin n → G) : homogeneousExtension f (Fin.partialProd x) = f x := by
  simp [homogeneousExtension, Fin.partialProd_right_inv]

private def homogeneousDifferential {n : ℕ} (f : (Fin (n + 1) → G) → V)
    (x : Fin (n + 2) → G) : V :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • f (x ∘ i.succAbove)

private theorem homogeneousDifferential_equivariant {n : ℕ}
    {f : (Fin (n + 1) → G) → V} (hf : IsEquivariant f) :
    IsEquivariant (homogeneousDifferential f) := by
  intro g x
  simp only [homogeneousDifferential, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (-1 : ℤ) ^ i.val • f (g • (x ∘ i.succAbove)) =
    g • ((-1 : ℤ) ^ i.val • f (x ∘ i.succAbove))
  rw [hf, smul_comm]

private theorem homogeneousDifferential_partialProd {n : ℕ}
    {f : (Fin (n + 1) → G) → V} (hf : IsEquivariant f) (x : Fin (n + 1) → G) :
    homogeneousDifferential f (Fin.partialProd x) =
      differentialFormula G V n (f ∘ Fin.partialProd) x := by
  have htail : Fin.partialProd x ∘ Fin.succ = x 0 • Fin.partialProd (Fin.tail x) :=
    funext (Fin.partialProd_succ' x)
  rw [homogeneousDifferential, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.val_succ]
  rw [htail, hf]
  simp only [Model.differentialFormula, Function.comp_apply, Fin.tail_def, Fin.partialProd_contractNth]

private theorem homogeneousExtension_closed {n : ℕ} {f : (Fin n → G) → V}
    (hf : differentialFormula G V n f = 0) :
    homogeneousDifferential (homogeneousExtension f) = 0 := by
  funext x
  let y : Fin (n + 1) → G := fun i => (x i.castSucc)⁻¹ * x i.succ
  have hcoord : x 0 • Fin.partialProd y = x := Fin.partialProd_left_inv x
  have he := homogeneousExtension_equivariant f
  calc
    homogeneousDifferential (homogeneousExtension f) x =
        x 0 • homogeneousDifferential (homogeneousExtension f) (Fin.partialProd y) := by
      rw [← homogeneousDifferential_equivariant he, hcoord]
    _ = 0 := by
      rw [homogeneousDifferential_partialProd he]
      have hrestrict : homogeneousExtension f ∘ Fin.partialProd = f :=
        funext (homogeneousExtension_partialProd f)
      rw [hrestrict, hf]
      simp

end Homogeneous

private theorem homogeneousDifferential_cons {G V : Type*} [AddCommGroup V] {n : ℕ}
    (f : (Fin (n + 2) → G) → V) (h : G) (x : Fin (n + 2) → G) :
    homogeneousDifferential f (Fin.cons h x) =
      f x - ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • f (Fin.cons h (x ∘ i.succAbove)) := by
  have htuple (i : Fin (n + 2)) :
      Fin.cons h x ∘ i.succ.succAbove = Fin.cons h (x ∘ i.succAbove) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp
    · simp
  rw [homogeneousDifferential, Fin.sum_univ_succ]
  simp [htuple, Function.comp_def, pow_succ, Finset.sum_neg_distrib, sub_eq_add_neg]

section Averaging

variable {G V R : Type*} [Fintype G] [AddCommGroup V] [Ring R] [Module R V]

private def averageCochain {n : ℕ} (weight : G → R) (f : (Fin (n + 2) → G) → V)
    (x : Fin (n + 1) → G) : V :=
  ∑ h : G, weight h • f (Fin.cons h x)

private theorem averageCochain_equivariant [Group G] [DistribMulAction G V] {n : ℕ}
    {weight : G → R} (hweight : ∀ (g h : G) (b : V),
      g • (weight h • b) = weight (g * h) • (g • b))
    {f : (Fin (n + 2) → G) → V} (hf : IsEquivariant f) :
    IsEquivariant (averageCochain weight f) := by
  intro g x
  simp only [averageCochain, Finset.smul_sum]
  symm
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_
  rw [hweight, ← hf]
  apply congrArg (fun y => weight (g * h) • f y)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Pi.smul_apply, smul_eq_mul]
  · simp [Pi.smul_apply]

private theorem averageCochain_differential {n : ℕ} {weight : G → R}
    (hweight : ∑ h, weight h = 1) (f : (Fin (n + 2) → G) → V) (x : Fin (n + 2) → G) :
    averageCochain weight (homogeneousDifferential f) x =
      f x - homogeneousDifferential (averageCochain weight f) x := by
  simp only [averageCochain, homogeneousDifferential_cons, smul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_smul, hweight, one_smul]
  congr 1
  unfold homogeneousDifferential
  simp only [averageCochain, Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun h _ => smul_comm _ _ _

end Averaging

/-- In the finite discrete model, every positive-degree cocycle with semilinear coefficients
is a coboundary, by averaging with a trace-one element. -/
theorem discrete_semilinear_cohomology_subsingleton :
    Specification.DiscreteSemilinearVanishing.{u,v,w} := by
  intro k E V _ _ _ _ _ _ _ _ _ _ _ _ hsemi q hq
  cases q with
  | zero => exact (Nat.not_lt_zero _ hq).elim
  | succ n =>
    obtain ⟨t, ht⟩ := exists_trace_one k E
    let weight : Gal(E/k) → E := fun h => h t
    have hweight (g h : Gal(E/k)) (b : V) :
        g • (weight h • b) = weight (g * h) • (g • b) := hsemi g (h t) b
    have vanishes (c : ContinuousH Gal(E/k) V (n + 1)) : c = 0 := by
      obtain ⟨z, rfl⟩ := continuousClass_surjective (G := Gal(E/k)) (M := V) (n + 1) c
      rw [← (continuousClass Gal(E/k) V (n + 1)).map_zero]
      apply (continuousClass_succ_eq_iff z 0).2
      let f := homogeneousExtension z.val.val
      have hz : differentialFormula Gal(E/k) V (n + 1) z.val.val = 0 :=
        congrArg Subtype.val (LinearMap.mem_ker.mp z.property)
      have hf : homogeneousDifferential f = 0 := homogeneousExtension_closed hz
      let b := averageCochain weight f
      have hb : IsEquivariant b := averageCochain_equivariant hweight
        (homogeneousExtension_equivariant z.val.val)
      have hdb (x : Fin (n + 2) → Gal(E/k)) : homogeneousDifferential b x = f x := by
        have h := averageCochain_differential ht f x
        rw [hf] at h
        have hzero : averageCochain weight 0 x = (0 : V) := by simp [averageCochain]
        rw [hzero] at h
        exact (sub_eq_zero.mp h.symm).symm
      let primitive : continuousCochains Gal(E/k) V n :=
        ⟨b ∘ Fin.partialProd, continuous_of_discreteTopology⟩
      refine ⟨primitive, ?_⟩
      change continuousDifferential Gal(E/k) V n primitive = z.val - 0
      rw [sub_zero]
      apply Subtype.ext
      funext x
      change differentialFormula Gal(E/k) V n (b ∘ Fin.partialProd) x = z.val.val x
      rw [← homogeneousDifferential_partialProd hb, hdb]
      exact homogeneousExtension_partialProd z.val.val x
    exact ⟨fun a b => (vanishes a).trans (vanishes b).symm⟩

private theorem ordinary_of_discrete_semilinear_vanishing
    (h : Specification.DiscreteSemilinearVanishing.{u,v,w}) :
    Specification.SemilinearVanishing.{u,v,w} := by
  intro k E V _ _ _ _ _ _ _ _ hsemi q hq
  let : TopologicalSpace Gal(E/k) := ⊥
  let : DiscreteTopology Gal(E/k) := discreteTopology_bot _
  let : TopologicalSpace V := ⊥
  let : DiscreteTopology V := discreteTopology_bot _
  have := h k E V hsemi q hq
  let e := ordinaryCohomologyEquiv.{v,w,0} Gal(E/k) V q
  exact ⟨fun x y => e.symm.injective (Subsingleton.elim (e.symm x) (e.symm y))⟩

/-- Finite Galois groups have zero positive-degree integral cohomology with coefficients
in the additive group of any semilinear vector space. -/
theorem semilinear_cohomology_subsingleton : Specification.SemilinearVanishing.{u,v,w} :=
  ordinary_of_discrete_semilinear_vanishing discrete_semilinear_cohomology_subsingleton

end GaloisFormalization.GH
