import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianCliffordInvariants
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TrialitarianMarkedSpin
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RankEightSpinStructure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.FunctionFieldForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuadraticIsotropy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CliffordModel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.FrameParameters
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Central.End
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.Group
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.CentralizerDimension
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SkolemNoether

/-! Clifford invariants of the vector form over the trialitarian cubic field in F12. -/

namespace LinearAlgebraicGroups.Arithmetic.TrialitarianCliffordInvariants

open LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianCliffordInvariants
open LinearAlgebraicGroups.Specs.Arithmetic.IsotropicSpinGeneration (HyperbolicPair IsIsotropic)

universe u v w

set_option autoImplicit false

open scoped BigOperators

private theorem quadraticPolynomial {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] (q : QuadraticForm K V) {n : ℕ}
    (b : Fin n → V) (s : Finset (Fin n)) :
    ∃ p : MvPolynomial (Fin n) K, p.IsHomogeneous 2 ∧
      ∀ x : Fin n → K, MvPolynomial.eval x p = q (∑ i ∈ s, x i • b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨p, hp, hpe⟩ := ih
    let cross (j : Fin n) : MvPolynomial (Fin n) K :=
      (MvPolynomial.C (q.polarBilin (b i) (b j)) * MvPolynomial.X i) * MvPolynomial.X j
    have hc (j : Fin n) : (cross j).IsHomogeneous 2 := by
      change (MvPolynomial.C (q.polarBilin (b i) (b j)) * MvPolynomial.X i *
        MvPolynomial.X j).IsHomogeneous (1 + 1)
      exact (MvPolynomial.isHomogeneous_C_mul_X _ _).mul (MvPolynomial.isHomogeneous_X _ _)
    refine ⟨MvPolynomial.C (q (b i)) * MvPolynomial.X i ^ 2 + p + ∑ j ∈ s, cross j,
      ((MvPolynomial.isHomogeneous_C_mul_X_pow _ _ _).add hp).add
        (MvPolynomial.IsHomogeneous.sum s cross 2 fun j _ => hc j), ?_⟩
    intro x
    rw [Finset.sum_insert hi, QuadraticMap.map_add q, q.map_smul, ← QuadraticMap.polarBilin_apply_apply,
      LinearMap.map_smul₂, map_sum (q.polarBilin (b i))]
    simp only [map_add, map_mul, map_pow, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X,
      hpe, cross, LinearMap.map_smul, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _
      ring

private theorem localIsotropy {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (q : QuadraticForm K V) (hq : IsRegular q)
    (hd : 4 < Module.finrank K V) : IsIsotropic q := by
  by_cases h : (2 : K) = 0
  · have hchar : ringChar K = 2 :=
      CharP.ringChar_of_prime_eq_zero Nat.prime_two (by exact h)
    let : CharP K 2 := hchar ▸ ringChar.charP K
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let b := Module.finBasis K V
    obtain ⟨p, hp, hpe⟩ := quadraticPolynomial q b Finset.univ
    obtain ⟨x, hx, hpx⟩ := FunctionFieldForms.local_quadratic_bound K 2 _ hd p hp
    refine ⟨b.equivFun.symm x, fun hzero => hx (b.equivFun.symm.injective (hzero.trans (map_zero _).symm)), ?_⟩
    rw [b.equivFun_symm_apply, ← hpe]
    exact hpx
  · exact LocalQuadraticIsotropy.local_isotropy h q hq hd

private def plane {K : Type u} [Field K] : QuadraticForm K (K × K) :=
  LinearMap.BilinMap.toQuadraticMap (LinearMap.mk₂ K (fun s t : K × K => s.1 * t.2)
    (fun _ _ _ => add_mul _ _ _) (fun _ _ _ => mul_assoc _ _ _)
    (fun _ _ _ => mul_add _ _ _) (fun _ _ _ => mul_left_comm _ _ _))

@[simp] private theorem plane_apply {K : Type u} [Field K] (x : K × K) :
    plane x = x.1 * x.2 := rfl

private theorem polarSymm {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticForm K V) (x y : V) : q.polarBilin x y = q.polarBilin y x := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, add_comm x y]
  abel

private noncomputable def splitPlane {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] {q : QuadraticForm K V}
    (h : HyperbolicPair q) :
    (plane.prod (q.comp h.perpendicular.subtype)).IsometryEquiv q := by
  let B := q.polarBilin
  have hee : B h.e h.e = 0 := by
    simp [B, QuadraticMap.polar_self, h.q_e]
  have hff : B h.f h.f = 0 := by
    simp [B, QuadraticMap.polar_self, h.q_f]
  have hef : B h.e h.f = 1 := h.polar_ef
  have hfe : B h.f h.e = 1 := (polarSymm q _ _).trans hef
  let f : (K × K) × h.perpendicular →ₗ[K] V :=
    ((LinearMap.fst K K K).smulRight h.e + (LinearMap.snd K K K).smulRight h.f).comp
      (LinearMap.fst K (K × K) h.perpendicular) +
      h.perpendicular.subtype.comp (LinearMap.snd K (K × K) h.perpendicular)
  have hf (x : (K × K) × h.perpendicular) : f x = (x.1.1 • h.e + x.1.2 • h.f) + x.2.val := rfl
  have hperp (x : h.perpendicular) : B h.e x.val = 0 ∧ B h.f x.val = 0 := x.property
  have hpair (x : (K × K) × h.perpendicular) :
      B h.f (f x) = x.1.1 ∧ B h.e (f x) = x.1.2 := by
    simp [hf, hperp x.2, hee, hff, hef, hfe]
  have hinj : Function.Injective f := by
    intro x y hxy
    have h₁ : x.1.1 = y.1.1 := by rw [← (hpair x).1, ← (hpair y).1, hxy]
    have h₂ : x.1.2 = y.1.2 := by rw [← (hpair x).2, ← (hpair y).2, hxy]
    refine Prod.ext (Prod.ext h₁ h₂) (Subtype.ext ?_)
    rw [hf, hf, h₁, h₂] at hxy
    exact add_left_cancel hxy
  have hsurj : Function.Surjective f := by
    intro x
    let a := B h.f x
    let b := B h.e x
    let p := a • h.e + b • h.f
    have hp : x - p ∈ h.perpendicular := by
      change B h.e (x - p) = 0 ∧ B h.f (x - p) = 0
      simp [p, a, b, hee, hff, hef, hfe]
    exact ⟨((a, b), ⟨x - p, hp⟩), by rw [hf]; change p + (x - p) = x; abel⟩
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  intro x
  change q (f x) = _
  rw [hf, QuadraticMap.map_add q, ← QuadraticMap.polarBilin_apply_apply, LinearMap.map_add₂,
    LinearMap.map_smul₂, LinearMap.map_smul₂, (hperp x.2).1, (hperp x.2).2,
    QuadraticMap.map_add q, ← QuadraticMap.polarBilin_apply_apply, LinearMap.map_smul₂,
    LinearMap.map_smul, h.polar_ef]
  simp [q.map_smul, h.q_e, h.q_f, QuadraticMap.prod_apply, QuadraticMap.comp_apply]

private theorem regularComp {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] {W : Type w} [AddCommGroup W] [Module K W]
    (q : QuadraticForm K V) (e : W ≃ₗ[K] V) (h : IsRegular q) :
    IsRegular (q.comp e.toLinearMap) := by
  change LinearMap.ker q.polarBilin = ⊥ at h
  change LinearMap.ker (q.comp e.toLinearMap).polarBilin = ⊥
  rw [LinearMap.ker_eq_bot'] at h ⊢
  intro x hx
  apply e.injective
  rw [map_zero]
  apply h
  ext y
  obtain ⟨z, rfl⟩ := e.surjective y
  have hz := LinearMap.congr_fun hx z
  simpa [QuadraticMap.polarBilin_comp] using hz

private theorem regularPerpendicular {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] {q : QuadraticForm K V}
    (h : HyperbolicPair q) (hq : IsRegular q) :
    IsRegular (q.comp h.perpendicular.subtype) := by
  have hprod := regularComp q (splitPlane h).toLinearEquiv hq
  have heq : q.comp (splitPlane h).toLinearEquiv.toLinearMap =
      plane.prod (q.comp h.perpendicular.subtype) :=
    QuadraticMap.ext fun x => (splitPlane h).map_app x
  rw [heq] at hprod
  change LinearMap.ker (plane.prod (q.comp h.perpendicular.subtype)).polarBilin = ⊥ at hprod
  change LinearMap.ker (q.comp h.perpendicular.subtype).polarBilin = ⊥
  rw [LinearMap.ker_eq_bot'] at hprod
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have hz : (0, x) = (0 : (K × K) × h.perpendicular) := by
    apply hprod
    apply LinearMap.ext
    intro y
    simp [QuadraticMap.polarBilin_prod, hx]
  exact congrArg Prod.snd hz

open LinearAlgebraicGroups.Specs.SymplecticMatrixStructure (Indices)

private noncomputable def hyperbolicSucc {K : Type u} [Field K] (m : ℕ) :
    (plane.prod (hyperbolic K m)).IsometryEquiv (hyperbolic K (m + 1)) := by
  let W (n : ℕ) := Indices (ULift.{u} (Fin n)) → K
  let f : (K × K) × W m → W (m + 1) := fun x =>
    Sum.elim (fun i => Fin.cases x.1.1 (fun j => x.2 (.inl ⟨j⟩)) i.down)
      (fun i => Fin.cases x.1.2 (fun j => x.2 (.inr ⟨j⟩)) i.down)
  let g : W (m + 1) → (K × K) × W m := fun y =>
    ((y (.inl ⟨0⟩), y (.inr ⟨0⟩)),
      Sum.elim (fun i => y (.inl ⟨i.down.succ⟩)) (fun i => y (.inr ⟨i.down.succ⟩)))
  refine ⟨{ toFun := f
            invFun := g
            left_inv := ?_
            right_inv := ?_
            map_add' := ?_
            map_smul' := ?_ }, ?_⟩
  · intro x y
    funext i
    rcases i with i | i <;> cases i with
    | up i => cases i using Fin.cases <;> rfl
  · intro r x
    funext i
    rcases i with i | i <;> cases i with
    | up i => cases i using Fin.cases <;> rfl
  · intro x
    apply Prod.ext
    · simp [f, g]
    · funext i
      cases i <;> simp [f, g]
  · intro y
    funext i
    rcases i with i | i <;> cases i with
    | up i => cases i using Fin.cases <;> simp [f, g]
  · intro x
    change hyperbolic K (m + 1) (f x) = (plane.prod (hyperbolic K m)) x
    simp only [QuadraticMap.prod_apply, plane_apply, OddSpinModels.hyperbolicForm_apply]
    rw [← (Equiv.ulift : ULift.{u} (Fin (m + 1)) ≃ Fin (m + 1)).symm.sum_comp]
    rw [← (Equiv.ulift : ULift.{u} (Fin m) ≃ Fin m).symm.sum_comp]
    rw [Fin.sum_univ_succ]
    rfl

private theorem wittDecomposition {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    ∀ {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (q : QuadraticForm K V), IsRegular q → Module.finrank K V = 2 * n →
      ∃ (m r : ℕ) (q₀ : QuadraticForm K (Fin (2 * r) → K)),
        m + r = n ∧ r ≤ 2 ∧ IsRegular q₀ ∧ ¬ IsIsotropic q₀ ∧
          q.Equivalent ((hyperbolic K m).prod q₀) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ q hq hd
    by_cases h : IsIsotropic q
    · obtain ⟨x, hx, hqx⟩ := h
      obtain ⟨p, _⟩ := IsotropicSpinGeneration.hyperbolicPairExistence q (Or.inl hq) x hx hqx
      let Q := q.comp p.perpendicular.subtype
      let e := splitPlane p
      have hd' := e.toLinearEquiv.finrank_eq
      rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self,
        hd] at hd'
      have hsmall : n - 1 < n := by omega
      have hdim : Module.finrank K p.perpendicular = 2 * (n - 1) := by omega
      obtain ⟨m, r, q₀, hmr, hr, hq₀, ha, ⟨d⟩⟩ :=
        ih (n - 1) hsmall Q (regularPerpendicular p hq) hdim
      let reassoc : (plane.prod ((hyperbolic K m).prod q₀)).IsometryEquiv
          ((plane.prod (hyperbolic K m)).prod q₀) :=
        ⟨(LinearEquiv.prodAssoc K _ _ _).symm, fun x => add_assoc _ _ _⟩
      exact ⟨m + 1, r, q₀, by omega, hr, hq₀, ha,
        ⟨e.symm.trans (((QuadraticMap.IsometryEquiv.refl plane).prod d).trans
          (reassoc.trans ((hyperbolicSucc m).prod (QuadraticMap.IsometryEquiv.refl q₀))))⟩⟩
    · have hn : n ≤ 2 := by
        by_contra! hn
        exact h (localIsotropy q hq (by omega))
      let e : (Fin (2 * n) → K) ≃ₗ[K] V :=
        (LinearEquiv.funCongrLeft K K (finCongr hd)).trans (Module.finBasis K V).equivFun.symm
      let Q := q.comp e.toLinearMap
      have hQ : ¬ IsIsotropic Q := by
        rintro ⟨x, hx, hqx⟩
        exact h ⟨e x, fun hz => hx (e.injective (hz.trans (map_zero e).symm)), hqx⟩
      let insertZero : Q.IsometryEquiv ((hyperbolic K 0).prod Q) :=
        ⟨{ toFun := fun x => (0, x), invFun := Prod.snd, left_inv := fun _ => rfl,
           right_inv := fun x => Prod.ext (Subsingleton.elim _ _) rfl,
           map_add' := fun _ _ => Prod.ext (by simp) rfl,
           map_smul' := fun _ _ => Prod.ext (by simp) rfl },
          fun x => by simp [QuadraticMap.prod_apply]⟩
      let qToQ : q.IsometryEquiv Q := ⟨e.symm, fun x => by simp [Q, QuadraticMap.comp_apply]⟩
      exact ⟨0, n, Q, Nat.zero_add n, hn, regularComp q e hq, hQ, ⟨qToQ.trans insertZero⟩⟩

private theorem localWitt : LocalWittDecomposition.{u, v} := by
  intro K _ _ _ _ V _ _ _ q n hq hd
  exact wittDecomposition n q hq hd

private theorem binaryNorm : CharTwoBinaryNorm.{u, v} := by
  classical
  intro K _ _ V _ _ q b hb hq
  let l := b (.inl 0)
  let r := b (.inr 0)
  let a := q l
  let d := arf q b
  have hpol : q.polarBilin l r = 1 := by
    simpa [l, r] using hb.2.2 0 0
  have hd : d = a * q r := by
    simp [d, arf, a, l, r]
  have hnonzero : ∀ x : V, q x = 0 → x = 0 := by
    intro x hx
    by_contra hn
    exact hq ⟨x, hn, hx⟩
  have ha : a ≠ 0 := fun h => b.ne_zero (.inl 0) (hnonzero l h)
  have hcoordinate (s t : K) :
      q (s • l + t • r) = a * s ^ 2 + s * t + q r * t ^ 2 := by
    rw [QuadraticMap.map_add q (s • l) (t • r), ← QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.map_smul, QuadraticMap.map_smul,
      LinearMap.map_smul₂, LinearMap.map_smul, hpol]
    simp only [smul_eq_mul]
    change s * s * a + t * t * q r + s * (t * 1) = _
    ring
  have hAS : ¬ IsArtinSchreier d := by
    rintro ⟨s, hs⟩
    have hx : q (s • l + a • r) = 0 := by
      rw [hcoordinate]
      calc
        _ = a * (s ^ 2 + s + d) := by rw [hd]; ring
        _ = 0 := by rw [hs, CharTwo.add_self_eq_zero, mul_zero]
    have hrepr := congrArg (fun x => b.repr x (.inr 0)) (hnonzero _ hx)
    exact ha (by simpa [l, r] using hrepr)
  let : Fact (∀ s : K, s ^ 2 ≠ d + (1 : K) * s) :=
    ⟨fun s hs => hAS ⟨s, by rw [hs, one_mul, add_assoc, CharTwo.add_self_eq_zero, add_zero]⟩⟩
  let index : Fin 1 ⊕ Fin 1 ≃ Fin 2 := finSumFinEquiv
  let changeIndex : (Fin 1 ⊕ Fin 1 → K) ≃ₗ[K] (Fin 2 → K) :=
    LinearEquiv.funCongrLeft K K index.symm
  let scaleSecond : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) :=
    LinearEquiv.piCongrRight (fun i =>
      if i = 0 then LinearEquiv.refl K K else LinearEquiv.smulOfUnit (Units.mk0 a ha)⁻¹)
  let e := ((b.equivFun.trans changeIndex).trans scaleSecond).trans
    (QuadraticAlgebra.linearEquivTuple d 1).symm
  refine ⟨ha, hAS, Field.toIsField _, e, ?_⟩
  intro x
  have hx : x = b.repr x (.inl 0) • l + b.repr x (.inr 0) • r := by
    calc
      x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
      _ = _ := by rw [Fintype.sum_sum_type]; simp [l, r]
  have hindex₀ : index.symm 0 = Sum.inl 0 := by decide
  have hindex₁ : index.symm 1 = Sum.inr 0 := by decide
  have he : e x = ⟨b.repr x (.inl 0), a⁻¹ * b.repr x (.inr 0)⟩ := by
    simp [e, changeIndex, scaleSecond, LinearEquiv.funCongrLeft_apply,
      LinearEquiv.smulOfUnit, hindex₀, hindex₁, Units.smul_def, smul_eq_mul]
  calc
    q x = a * (b.repr x (.inl 0)) ^ 2 +
        b.repr x (.inl 0) * b.repr x (.inr 0) + q r * (b.repr x (.inr 0)) ^ 2 := by
      conv_lhs => rw [hx]
      exact hcoordinate _ _
    _ = a * QuadraticAlgebra.norm (e x) := by
      rw [he, QuadraticAlgebra.norm_def, CharTwo.sub_eq_add, hd]
      dsimp only
      field_simp

section CliffordCenter

open CliffordAlgebra Module
open _root_.LinearAlgebraicGroups.Albert

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
variable {I : Type w} [LinearOrder I]

private theorem orderedWord_eq_sort (q : QuadraticForm K V) (b : Basis I K V) (s : Finset I) :
    CliffordSpecification.orderedWord q b s = (s.sort.map (ι q ∘ b)).prod := by
  change (List.ofFn (fun i : Fin s.card => (ι q ∘ b) (s.orderEmbOfFin rfl i))).prod = _
  rw [List.ofFn_eq_map]
  change ((List.finRange s.card).map ((ι q ∘ b) ∘ ⇑(s.orderEmbOfFin rfl))).prod = _
  rw [← List.map_map (f := ⇑(s.orderEmbOfFin rfl)), Finset.listMap_orderEmbOfFin_finRange]

set_option maxHeartbeats 800000 in
private theorem contraction_word (q : QuadraticForm K V) (b : Basis I K V)
    (i : I) (s : Finset I) :
    (i ∉ s → CliffordAlgebra.contractLeft (b.coord i) (CliffordSpecification.orderedWord q b s) = 0) ∧
    (i ∈ s → ∃ c : K, c ≠ 0 ∧
      CliffordAlgebra.contractLeft (b.coord i) (CliffordSpecification.orderedWord q b s) =
        c • CliffordSpecification.orderedWord q b (s.erase i)) := by
  classical
  let word (l : List I) := (l.map (ι q ∘ b)).prod
  have hcons (j : I) (l : List I) : word (j :: l) = ι q (b j) * word l := rfl
  have coord (j : I) : b.coord i (b j) = if j = i then 1 else 0 := by
    rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  have hzero (l : List I) (hi : i ∉ l) : CliffordAlgebra.contractLeft (b.coord i) (word l) = 0 := by
    induction l with
    | nil => exact contractLeft_one q _
    | cons j l ih =>
      have hj : j ≠ i := fun h => hi (by simp [h])
      have hl : i ∉ l := fun h => hi (by simp [h])
      simp [hcons, contractLeft_ι_mul, coord, hj, ih hl]
  let keep (j : I) : Bool := decide (j ≠ i)
  have hdel (l : List I) (hl : l.Nodup) (hi : i ∈ l) :
      ∃ c : K, c ≠ 0 ∧ CliffordAlgebra.contractLeft (b.coord i) (word l) =
        c • word (l.filter keep) := by
    induction l with
    | nil => simp at hi
    | cons j l ih =>
      rw [List.nodup_cons] at hl
      by_cases hij : j = i
      · subst j
        refine ⟨1, one_ne_zero, ?_⟩
        have hfilter : l.filter keep = l :=
          List.filter_eq_self.mpr fun j hj => decide_eq_true (fun he => hl.1 (he ▸ hj))
        have hk : keep i = false := by simp [keep]
        simp [hk, hfilter, hcons, contractLeft_ι_mul, coord, hzero l hl.1]
      · have hit : i ∈ l := by simpa [Ne.symm hij] using hi
        obtain ⟨c, hc, he⟩ := ih hl.2 hit
        refine ⟨-c, neg_ne_zero.mpr hc, ?_⟩
        have hk : keep j = true := decide_eq_true hij
        simp [hk, hcons, contractLeft_ι_mul, coord, hij, he]
  have hsort (l : List I) (hl : l.Pairwise (· ≤ ·)) (hn : l.Nodup) :
      word l = CliffordSpecification.orderedWord q b l.toFinset := by
    rw [orderedWord_eq_sort, (List.toFinset_sort (· ≤ ·) hn).mpr hl]
  rw [orderedWord_eq_sort]
  refine ⟨fun h => hzero s.sort (by simpa using h), fun h => ?_⟩
  obtain ⟨c, hc, he⟩ := hdel s.sort (Finset.sort_nodup _ _) (by simpa using h)
  refine ⟨c, hc, he.trans ?_⟩
  let l := s.sort.filter keep
  have hl : l.toFinset = s.erase i := by
    ext j
    change j ∈ (s.sort.filter keep).toFinset ↔ j ∈ s.erase i
    rw [List.mem_toFinset, List.mem_filter, Finset.mem_sort, Finset.mem_erase]
    change (j ∈ s ∧ decide (j ≠ i) = true) ↔ j ≠ i ∧ j ∈ s
    simp only [decide_eq_true_eq, and_comm]
  have hsorted : l.Pairwise (· ≤ ·) := (Finset.pairwise_sort s (· ≤ ·)).filter keep
  have hnodup : l.Nodup := (Finset.sort_nodup s (· ≤ ·)).filter keep
  have hfinal := hsort l hsorted hnodup
  rw [hl] at hfinal
  exact congrArg (fun a : CliffordAlgebra q => c • a) hfinal

private theorem contraction_eq_commutator (q : QuadraticForm K V) (x : V)
    (z : CliffordAlgebra q) :
    CliffordAlgebra.contractLeft (q.polarBilin x) z = ι q x * z - involute z * ι q x := by
  induction z using CliffordAlgebra.left_induction with
  | algebraMap a => simp [Algebra.commutes]
  | add z y hz hy => simp only [map_add, hz, hy, mul_add, add_mul]; abel
  | ι_mul z y hz =>
    have hxy := CliffordAlgebra.ι_mul_ι_add_swap (Q := q) x y
    rw [← QuadraticMap.polarBilin_apply_apply] at hxy
    rw [contractLeft_ι_mul, hz, map_mul, involute_ι, Algebra.smul_def, ← hxy]
    noncomm_ring

private theorem even_scalar_of_commutes (q : QuadraticForm K V) (b : Basis I K V) [Fintype I]
    (hq : IsRegular q) (z : CliffordAlgebra q) (hz : z ∈ evenOdd q 0)
    (h : ∀ x : V, Commute (ι q x) z) : ∃ a : K, z = algebraMap K _ a := by
  classical
  let := Module.Finite.of_basis b
  let f := q.polarBilin.linearEquivOfInjective
    (LinearMap.ker_eq_bot.mp hq) Subspace.dual_finrank_eq.symm
  obtain ⟨B, hB⟩ := CliffordModel.ordered_basis q b
  have hword (i : I) : CliffordAlgebra.contractLeft (b.coord i) z = 0 := by
    obtain ⟨x, hx⟩ := f.surjective (b.coord i)
    change q.polarBilin x = b.coord i at hx
    rw [← hx, contraction_eq_commutator, involute_eq_of_mem_even hz, (h x).eq, sub_self]
  have hrepr (s : Finset I) (hs : s ≠ ∅) : B.repr z s = 0 := by
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    obtain ⟨c, hc, he⟩ := (contraction_word q b i s).2 hi
    have hsummand (t : Finset I) (ht : t ≠ s) :
        B.coord (s.erase i) (CliffordAlgebra.contractLeft (b.coord i) (B t)) = 0 := by
      rw [hB]
      by_cases hit : i ∈ t
      · obtain ⟨a, _, ha⟩ := (contraction_word q b i t).2 hit
        rw [ha, ← hB, map_smul, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
        have hne : t.erase i ≠ s.erase i := fun ht' =>
          ht (by rw [← Finset.insert_erase hit, ← Finset.insert_erase hi, ht'])
        simp [hne]
      · rw [(contraction_word q b i t).1 hit, map_zero]
    have hcprod : B.repr z s * c = 0 := by
      calc
        _ = B.coord (s.erase i) (CliffordAlgebra.contractLeft (b.coord i) z) := by
          conv_rhs => rw [← B.sum_repr z]
          simp only [map_sum, map_smul, smul_eq_mul]
          rw [Finset.sum_eq_single s (fun t _ ht => by simp [hsummand t ht])
            (fun hs' => (hs' (Finset.mem_univ _)).elim)]
          rw [hB, he, ← hB]
          simp [Basis.coord_apply, Basis.repr_self]
        _ = 0 := by rw [hword, map_zero]
    exact (mul_eq_zero.mp hcprod).resolve_right hc
  refine ⟨B.repr z ∅, ?_⟩
  calc
    z = ∑ s, B.repr z s • B s := (B.sum_repr _).symm
    _ = _ := by
      rw [Finset.sum_eq_single ∅ (fun s _ hs => by simp [hrepr s hs])
        (fun hs => (hs (Finset.mem_univ _)).elim), hB, orderedWord_eq_sort]
      simp [Algebra.algebraMap_eq_smul_one]

private def conjugation {A : Type v} [Ring A] [Algebra K A] (a : Aˣ) : A →ₐ[K] A where
  toFun x := ↑a⁻¹ * x * ↑a
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp [mul_add, add_mul]
  map_mul' x y := by simp [mul_assoc]
  commutes' r := by rw [← Algebra.commutes, mul_assoc, Units.inv_mul, mul_one]

private theorem even_center_of_root (q : QuadraticForm K V) (b : Basis I K V) [Fintype I]
    (hq : IsRegular q) {x : V} (hx : q x ≠ 0) {z : CliffordAlgebra q}
    (hz : z ∈ evenOdd q 0) (d t : K) (hsep : t ^ 2 + 4 * d ≠ 0)
    (hsq : z * z = d • 1 + t • z)
    (hmove : ∀ y : V, z * ι q y = ι q y * (t • 1 - z)) :
    ∃ e : QuadraticAlgebra K d t ≃ₐ[K] Subalgebra.center K (even q),
      ((e QuadraticAlgebra.omega).val : CliffordAlgebra q) = z := by
  classical
  let C := CliffordAlgebra q
  obtain ⟨B, _⟩ := CliffordModel.ordered_basis q b
  let : Nontrivial C := nontrivial_of_ne (B ∅) 0 (B.ne_zero ∅)
  have hreverse (y : V) : (t • (1 : C) - z) * ι q y = ι q y * z := by
    rw [sub_mul, hmove, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
    abel
  let Central (a : C) := ∀ y : C, y ∈ evenOdd q 0 → Commute y a
  have hzcentral : Central z := by
    intro y hy
    induction y, hy using CliffordAlgebra.even_induction with
    | algebraMap r => exact Algebra.commutes r z
    | add a b ha hb iha ihb => exact iha.add_left ihb
    | ι_mul_ι_mul a b c hc ih =>
      show (ι q a * ι q b * c) * z = z * (ι q a * ι q b * c)
      have hab : z * (ι q a * ι q b) = (ι q a * ι q b) * z := by
        rw [← mul_assoc, hmove, mul_assoc, hreverse, ← mul_assoc]
      rw [mul_assoc, ih.eq, ← mul_assoc, ← hab, mul_assoc]
  let u : Cˣ := (isUnit_ι_of_isUnit q hx.isUnit).unit
  have hu : (u : C) = ι q x := (isUnit_ι_of_isUnit q hx.isUnit).unit_spec
  have hu' : (↑u⁻¹ : C) = (q x)⁻¹ • ι q x := by
    apply u.isUnit.mul_right_cancel
    rw [Units.inv_mul, hu, smul_mul_assoc, ι_sq_scalar, Algebra.smul_def, ← map_mul,
      inv_mul_cancel₀ hx, map_one]
  let T := conjugation (K := K) u
  have hT (a : C) : (u : C) * T a = a * u := by
    change (u : C) * ((↑u⁻¹ : C) * a * ↑u) = _
    simp only [← mul_assoc, Units.mul_inv, one_mul]
  have hT₂ (a : C) : T (T a) = a := by
    apply u.isUnit.mul_left_cancel
    apply u.isUnit.mul_left_cancel
    rw [hT, ← mul_assoc, hT, mul_assoc, ← mul_assoc (u : C), hu, ι_sq_scalar]
    exact (Algebra.commutes _ _).symm
  have hTeven (a : C) (ha : a ∈ evenOdd q 0) : T a ∈ evenOdd q 0 := by
    change (↑u⁻¹ : C) * a * ↑u ∈ evenOdd q 0
    rw [hu', hu]
    have h := SetLike.mul_mem_graded
      (Submodule.smul_mem (evenOdd q 1) (q x)⁻¹ (ι_mem_evenOdd_one q x)) ha
    simpa only [add_zero, show (1 + 1 : ZMod 2) = 0 by decide] using
      SetLike.mul_mem_graded h (ι_mem_evenOdd_one q x)
  have hTcentral (a : C) (ha : Central a) : Central (T a) := by
    intro y hy
    have he := congrArg T (ha (T y) (hTeven y hy)).eq
    show y * T a = T a * y
    simpa only [map_mul, hT₂] using he
  have hFixed (a : C) (ae : a ∈ evenOdd q 0) (ac : Central a) (at' : T a = a) :
      ∃ r : K, a = algebraMap K C r := by
    have hac : Commute (u : C) a := by
      change (u : C) * a = a * u
      rw [← hT a, at']
    apply even_scalar_of_commutes q b hq a ae
    intro y
    apply u.isUnit.mul_right_cancel
    rw [mul_assoc, ← hac.eq, ← mul_assoc, hu]
    have he := (ac (ι q y * ι q x) (ι_mul_ι_mem_evenOdd_zero q y x)).eq
    rw [he, ← mul_assoc]
  have hTz : T z = t • 1 - z := by
    apply u.isUnit.mul_left_cancel
    rw [hT, hu, hmove]
  let D := T z - z
  have hD₂ : D * D = algebraMap K C (t ^ 2 + 4 * d) := by
    change (T z - z) * (T z - z) = _
    rw [hTz]
    calc
      _ = (t ^ 2) • (1 : C) + (4 : K) • (z * z - t • z) := by
        simp only [sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc,
          one_mul, mul_one, pow_two]
        module
      _ = _ := by rw [hsq, add_sub_cancel_right, smul_smul, ← add_smul, ← Algebra.algebraMap_eq_smul_one]
  have hDunit : IsUnit D := isUnit_mul_self_iff.mp
    (hD₂.symm ▸ hsep.isUnit.map (algebraMap K C))
  have hTd (a : C) : T (T a - a) = -(T a - a) := by
    simp [hT₂, neg_sub]
  have hde (a : C) (ha : a ∈ evenOdd q 0) : T a - a ∈ evenOdd q 0 :=
    Submodule.sub_mem _ (hTeven a ha) ha
  have hdc (a : C) (ha : Central a) : Central (T a - a) :=
    fun y hy => (hTcentral a ha y hy).sub_right (ha y hy)
  let H := Subalgebra.center K (even q)
  let root : H := ⟨⟨z, hz⟩, Subalgebra.mem_center_iff.mpr fun y =>
    Subtype.ext (hzcentral y.val y.property).eq⟩
  have hp : root * root = d • (1 : H) + t • root :=
    Subtype.ext (Subtype.ext hsq)
  let f : QuadraticAlgebra K d t →ₐ[K] H := QuadraticAlgebra.lift ⟨root, hp⟩
  have hf (a : QuadraticAlgebra K d t) : ((f a).val.val : C) = a.re • 1 + a.im • z := rfl
  have hinj : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro a ha
    have h₀ : a.re • (1 : C) + a.im • z = 0 := by
      rw [← hf, ha]
      rfl
    have h₁ := congrArg T h₀
    simp only [map_add, map_smul, map_one, map_zero] at h₁
    have h₂ : a.im • D = 0 := by
      change a.im • (T z - z) = 0
      rw [smul_sub, (show a.im • T z = a.im • z from add_left_cancel (h₁.trans h₀.symm)), sub_self]
    have him := (smul_eq_zero.mp h₂).resolve_right hDunit.ne_zero
    rw [him, zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one,
      map_eq_zero_iff _ (algebraMap K C).injective] at h₀
    ext <;> assumption
  have hsurj : Function.Surjective f := by
    intro a
    let y : C := a.val.val
    have ye : y ∈ evenOdd q 0 := a.val.property
    have yc : Central y := fun w hw =>
      congrArg Subtype.val ((Subalgebra.mem_center_iff.mp a.property) ⟨w, hw⟩)
    let k := T y - y
    have hk (a b : C) (ha : a ∈ evenOdd q 0) (hb : b ∈ evenOdd q 0) :
        a * b ∈ evenOdd q 0 := by
      simpa only [add_zero] using SetLike.mul_mem_graded ha hb
    obtain ⟨r, hr⟩ := hFixed (k * D) (hk _ _ (hde y ye) (hde z hz))
      (fun w hw => (hdc y yc w hw).mul_right (hdc z hzcentral w hw))
      (by rw [map_mul, show T k = -k from hTd y, show T D = -D from hTd z, neg_mul_neg])
    let c := r / (t ^ 2 + 4 * d)
    have hkc : k = c • D := by
      apply hDunit.mul_right_cancel
      rw [hr, smul_mul_assoc, hD₂, Algebra.smul_def, ← map_mul, div_mul_cancel₀ _ hsep]
    have hscalar : T (y - c • z) = y - c • z := by
      change T y - y = c • (T z - z) at hkc
      rw [smul_sub] at hkc
      rw [map_sub, map_smul]
      calc
        _ = (T y - y) - (c • T z - c • z) + (y - c • z) := by abel
        _ = _ := by rw [hkc, sub_self, zero_add]
    obtain ⟨s, hs⟩ := hFixed (y - c • z)
      (Submodule.sub_mem _ ye (Submodule.smul_mem _ _ hz))
      (fun w hw => (yc w hw).sub_right ((hzcentral w hw).smul_right c)) hscalar
    refine ⟨⟨s, c⟩, Subtype.ext (Subtype.ext ?_)⟩
    rw [hf]
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (sub_eq_iff_eq_add.mp hs).symm
  refine ⟨AlgEquiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  change ((f QuadraticAlgebra.omega).val.val : C) = z
  simp [hf]

private theorem symplectic_coordinates (q : QuadraticForm K V) {n : ℕ}
    (b : Basis (Fin n ⊕ Fin n) K V) (hb : IsSymplecticBasis q b) (x : V) :
    (∑ i, (q.polarBilin x (b (.inl i)) • b (.inr i) +
      q.polarBilin x (b (.inr i)) • b (.inl i))) = x := by
  classical
  let P : V →ₗ[K] V := ∑ i : Fin n,
    (((q.polarBilin.flip (b (.inl i))).smulRight (b (.inr i))) +
      ((q.polarBilin.flip (b (.inr i))).smulRight (b (.inl i))))
  have hP : P = LinearMap.id := by
    apply b.ext
    rintro (j | j)
    · simp only [P, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
        LinearMap.flip_apply, LinearMap.id_apply, hb.1, hb.2.2, zero_smul, zero_add, ite_smul,
        one_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    · have hrev (i : Fin n) : q.polarBilin (b (.inr j)) (b (.inl i)) =
          if i = j then 1 else 0 := (polarSymm q _ _).trans (hb.2.2 i j)
      simp only [P, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
        LinearMap.flip_apply, LinearMap.id_apply, hb.2.1, hrev, zero_smul, add_zero, ite_smul,
        one_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simpa only [P, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.flip_apply, LinearMap.id_apply] using LinearMap.congr_fun hP x

private theorem arf_center : ArfCenter.{u, v} := by
  classical
  intro K _ _ V _ _ q n b hn hb
  let ba := b.reindex finSumFinEquiv
  obtain ⟨B, _⟩ := CliffordModel.ordered_basis q ba
  let C := CliffordAlgebra q
  let : Nontrivial C := nontrivial_of_ne (B ∅) 0 (B.ne_zero ∅)
  let : CharP C 2 := charP_of_injective_algebraMap (algebraMap K C).injective 2
  let s (i : Fin n) := b (.inl i)
  let t (i : Fin n) := b (.inr i)
  let p (i : Fin n) : C := ι q (s i) * ι q (t i)
  let z : C := arfElement q b
  have hz : z ∈ evenOdd q 0 :=
    (evenOdd q 0).sum_mem fun i _ => ι_mul_ι_mem_evenOdd_zero q (s i) (t i)
  have hq : IsRegular q := by
    change q.polarBilin.ker = ⊥
    rw [LinearMap.ker_eq_bot']
    intro x hx
    simpa [hx] using (symplectic_coordinates q b hb x).symm
  have hc (a a' : V) (h : q.polarBilin a a' = 0) : Commute (ι q a) (ι q a') := by
    have he := ι_mul_ι_add_swap (Q := q) a a'
    rw [← QuadraticMap.polarBilin_apply_apply, h, map_zero] at he
    exact (eq_neg_of_add_eq_zero_left he).trans (CharTwo.neg_eq _)
  have hps (i j : Fin n) (hij : i ≠ j) : Commute (p i) (p j) := by
    have hst : q.polarBilin (s i) (t j) = 0 := by simp [s, t, hb.2.2, hij]
    have hts : q.polarBilin (t i) (s j) = 0 := by
      rw [polarSymm q]
      simp [s, t, hb.2.2, hij.symm]
    exact ((hc _ _ (hb.1 i j)).mul_right (hc _ _ hst)).mul_left
      ((hc _ _ hts).mul_right (hc _ _ (hb.2.1 i j)))
  have hp (i : Fin n) : p i * p i = algebraMap K C (q (s i) * q (t i)) + p i := by
    have h := ι_mul_ι_add_swap (Q := q) (t i) (s i)
    rw [← QuadraticMap.polarBilin_apply_apply, polarSymm q (t i) (s i),
      show q.polarBilin (s i) (t i) = 1 by simp [s, t, hb.2.2], map_one] at h
    have hts : ι q (t i) * ι q (s i) = 1 + p i := CharTwo.add_eq_iff_eq_add.mp h
    calc
      p i * p i = ι q (s i) * (ι q (t i) * ι q (s i)) * ι q (t i) := by
        dsimp only [p]
        simp only [mul_assoc]
      _ = p i + (ι q (s i) * ι q (s i)) * (ι q (t i) * ι q (t i)) := by
        rw [hts]
        simp only [p, mul_add, mul_one, add_mul, mul_assoc]
      _ = _ := by rw [ι_sq_scalar, ι_sq_scalar, map_mul, add_comm]
  have hsum (J : Finset (Fin n)) :
      (∑ i ∈ J, p i) * (∑ i ∈ J, p i) = ∑ i ∈ J, p i * p i := by
    induction J using Finset.induction_on with
    | empty => simp
    | @insert i J hi ih =>
      have hm : Commute (p i) (∑ j ∈ J, p j) :=
        Commute.sum_right _ _ _ fun j hj => hps i j (fun hij => hi (hij ▸ hj))
      simp only [Finset.sum_insert hi]
      let a := ∑ j ∈ J, p j
      change (p i + a) * (p i + a) = p i * p i + ∑ j ∈ J, p j * p j
      calc
        _ = p i * p i + (p i * a + p i * a) + a * a := by
          simp only [add_mul, mul_add]
          rw [show a * p i = p i * a from hm.eq.symm]
          abel
        _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero, ih]
  have hzsq : z * z = arf q b • 1 + (1 : K) • z := by
    change (∑ i, p i) * (∑ i, p i) = _
    rw [hsum, one_smul]
    simp only [hp, Finset.sum_add_distrib]
    rw [← map_sum (algebraMap K C), Algebra.algebraMap_eq_smul_one]
    rfl
  have hcontract (x : V) : CliffordAlgebra.contractLeft (q.polarBilin x) z = ι q x := by
    have hcoord := congrArg (ι q) (symplectic_coordinates q b hb x)
    rw [← hcoord]
    change CliffordAlgebra.contractLeft (q.polarBilin x) (∑ i, p i) = _
    simp only [p, s, t, map_sum, map_add, map_smul, contractLeft_ι_mul, contractLeft_ι,
      CharTwo.sub_eq_add]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Algebra.commutes, ← Algebra.smul_def]
  have hmove (x : V) : z * ι q x = ι q x * (z + 1) := by
    have h := hcontract x
    rw [contraction_eq_commutator, involute_eq_of_mem_even hz, CharTwo.sub_eq_add] at h
    rw [add_comm] at h
    rw [mul_add, mul_one, add_comm]
    exact CharTwo.add_eq_iff_eq_add.mp h
  have hnonzero : ∃ x : V, q x ≠ 0 := by
    by_contra! h
    let i : Fin n := ⟨0, hn⟩
    have hh := hb.2.2 i i
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      h, sub_zero] at hh
    exact zero_ne_one hh
  obtain ⟨x, hx⟩ := hnonzero
  have hsep : (1 : K) ^ 2 + 4 * arf q b ≠ 0 := by
    have hfour : (4 : K) = 0 := by
      rw [show (4 : K) = 2 * 2 by norm_num, CharTwo.two_eq_zero, zero_mul]
    simp [hfour]
  obtain ⟨e, he⟩ := even_center_of_root q ba hq hx hz (arf q b) 1 hsep hzsq
    (by simpa [CharTwo.sub_eq_add, add_comm] using hmove)
  exact ⟨e, he, hmove⟩

private theorem signed_discriminant_diagonal (q : QuadraticForm K V) {n : ℕ}
    (b : Basis (Fin (2 * n)) K V) (h₂ : (2 : K) ≠ 0)
    (ho : ∀ i j, i ≠ j → q.polarBilin (b i) (b j) = 0) :
    signedDiscriminant q b = (-1) ^ n * ∏ i, q (b i) := by
  classical
  have hm : (Matrix.of fun i j => q.polarBilin (b i) (b j) / 2) =
      Matrix.diagonal (fun i => q (b i)) := by
    ext i j
    change q.polarBilin (b i) (b j) / 2 = Matrix.diagonal (fun i => q (b i)) i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self,
        two_nsmul, ← two_mul, mul_div_cancel_left₀ _ h₂]
    · rw [ho i j hij, zero_div, Matrix.diagonal_apply_ne _ hij]
  rw [signedDiscriminant, hm, Matrix.det_diagonal]

private def cliffordWord (q : QuadraticForm K V) (b : I → V) (l : List I) :
    CliffordAlgebra q := (l.map (ι q ∘ b)).prod

omit [LinearOrder I] in
private theorem cliffordWord_cons (q : QuadraticForm K V) (b : I → V) (i : I) (l : List I) :
    cliffordWord q b (i :: l) = ι q (b i) * cliffordWord q b l := rfl

omit [LinearOrder I] in
private theorem cliffordWord_append (q : QuadraticForm K V) (b : I → V) (l l' : List I) :
    cliffordWord q b (l ++ l') = cliffordWord q b l * cliffordWord q b l' := by
  simp [cliffordWord, List.prod_append]

omit [LinearOrder I] in
private theorem orthogonal_word_move (q : QuadraticForm K V) (b : I → V)
    (ho : ∀ i j, i ≠ j → q.polarBilin (b i) (b j) = 0) (j : I)
    (l : List I) (hl : j ∉ l) :
    cliffordWord q b l * ι q (b j) =
      (-1 : K) ^ l.length • (ι q (b j) * cliffordWord q b l) := by
  induction l with
  | nil => simp [cliffordWord]
  | cons i l ih =>
    rw [List.mem_cons, not_or] at hl
    have hi := ι_mul_ι_comm (Q := q) (b i) (b j)
    rw [← QuadraticMap.polarBilin_apply_apply, ho i j (Ne.symm hl.1), map_zero, zero_sub] at hi
    rw [cliffordWord_cons, mul_assoc, ih hl.2, mul_smul_comm, ← mul_assoc (ι q (b i)),
      hi, neg_mul, mul_assoc, List.length_cons, pow_succ, mul_neg_one, neg_smul, smul_neg]

omit [LinearOrder I] in
private theorem orthogonal_word_square (q : QuadraticForm K V) (b : I → V)
    (ho : ∀ i j, i ≠ j → q.polarBilin (b i) (b j) = 0) (l : List I) (hl : l.Nodup) :
    cliffordWord q b l * cliffordWord q b l =
      (-1 : K) ^ l.length.choose 2 • algebraMap K _ (l.map (q ∘ b)).prod := by
  induction l with
  | nil => simp [cliffordWord]
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    rw [cliffordWord_cons]
    calc
      _ = (ι q (b i) * (cliffordWord q b l * ι q (b i))) * cliffordWord q b l := by
        simp only [mul_assoc]
      _ = (-1 : K) ^ l.length •
          (ι q (b i) * ι q (b i) * (cliffordWord q b l * cliffordWord q b l)) := by
        rw [orthogonal_word_move q b ho i l hl.1, mul_smul_comm, smul_mul_assoc]
        simp only [mul_assoc]
      _ = _ := by
        rw [ι_sq_scalar, ih hl.2, mul_smul_comm, smul_smul, ← pow_add, ← map_mul,
          List.map_cons, List.prod_cons, Function.comp_apply, List.length_cons,
          Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm l.length]

private theorem sign_choose_even (n : ℕ) : (-1 : K) ^ (2 * n).choose 2 = (-1 : K) ^ n := by
  cases n with
  | zero => simp
  | succ n =>
    have hs : (((-1 : K) ^ (n + 1)) ^ 2) = 1 := by
      rw [← pow_mul, Nat.mul_comm (n + 1) 2, pow_mul]
      simp
    rw [Nat.choose_two_right, show 2 * (n + 1) - 1 = 2 * n + 1 by omega, Nat.mul_assoc,
      Nat.mul_div_cancel_left _ (by decide : 0 < 2), pow_mul, pow_succ,
      pow_mul ((-1 : K) ^ (n + 1)) 2 n, hs, one_pow, one_mul]

private theorem discriminant_center : DiscriminantCenter.{u, v} := by
  classical
  intro K _ V _ _ q n b h₂ hn hq ho
  let l := List.ofFn (id : Fin (2 * n) → Fin (2 * n))
  let C := CliffordAlgebra q
  let z := volumeElement q b
  have hword : cliffordWord q b l = z := by
    simp [cliffordWord, l, z, volumeElement, List.map_ofFn, Function.comp_def]
  have hnodup : l.Nodup := List.nodup_ofFn.mpr (fun _ _ h => h)
  have hlen : l.length = 2 * n := List.length_ofFn
  have hnorm (i : Fin (2 * n)) : q (b i) ≠ 0 := by
    intro hbi
    have hp : q.polarBilin (b i) = 0 := by
      apply b.ext
      intro j
      by_cases hij : i = j
      · subst j
        simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, hbi]
      · exact ho i j hij
    exact b.ne_zero i (LinearMap.ker_eq_bot'.mp hq _ hp)
  have hdiag := signed_discriminant_diagonal q b h₂ ho
  have hd : signedDiscriminant q b ≠ 0 :=
    hdiag ▸ mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (Finset.prod_ne_zero_iff.mpr fun i _ => hnorm i)
  have hzsq : z * z = signedDiscriminant q b • (1 : C) + (0 : K) • z := by
    rw [← hword, orthogonal_word_square q b ho l hnodup,
      hlen, sign_choose_even, hdiag, mul_smul, Algebra.algebraMap_eq_smul_one, zero_smul, add_zero]
    congr 2
  have hset : l.toFinset = Finset.univ := by
    ext i
    simp [l]
  have hsort : (Finset.univ : Finset (Fin (2 * n))).sort = l := by
    rw [← hset]
    exact (List.toFinset_sort (· ≤ ·) hnodup).mpr (List.pairwise_ofFn.mpr fun _ _ h => le_of_lt h)
  have hz : z ∈ evenOdd q 0 := by
    rw [← hword, cliffordWord, ← hsort, ← orderedWord_eq_sort]
    convert CliffordModel.ordered_word_parity q b Finset.univ using 2
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_mul]
    exact (zero_mul (n : ZMod 2)).symm
  have hmove_basis (j : Fin (2 * n)) : z * ι q (b j) = ι q (b j) * (-z) := by
    let a := ι q (b j)
    have ha : IsUnit a := isUnit_ι_of_isUnit q (hnorm j).isUnit
    let T := conjugation (K := K) ha.unit
    have hT (c : C) : a * T c = c * a := by
      have he : ↑ha.unit * T c = c * (↑ha.unit : C) := by
        change ↑ha.unit * ((↑ha.unit⁻¹ : C) * c * ha.unit) = _
        simp only [← mul_assoc, Units.mul_inv, one_mul]
      exact (congrArg (· * T c) ha.unit_spec).symm.trans
        (he.trans (congrArg (c * ·) ha.unit_spec))
    have hTj : T a = a := ha.mul_left_cancel (hT a)
    have hTi (i : Fin (2 * n)) (hi : i ≠ j) : T (ι q (b i)) = -ι q (b i) := by
      apply ha.mul_left_cancel
      rw [hT, mul_neg, ι_mul_ι_comm, ← QuadraticMap.polarBilin_apply_apply,
        ho i j hi, map_zero, zero_sub]
    have hTl (p : List (Fin (2 * n))) (hp : j ∉ p) :
        T (cliffordWord q b p) = (-1 : K) ^ p.length • cliffordWord q b p := by
      induction p with
      | nil => simp [cliffordWord]
      | cons i p ih =>
        rw [List.mem_cons, not_or] at hp
        rw [cliffordWord_cons, map_mul, hTi i (Ne.symm hp.1), ih hp.2, List.length_cons,
          pow_succ, mul_neg_one, neg_smul, mul_smul_comm, neg_mul, smul_neg]
    obtain ⟨p, r, hp⟩ := List.append_of_mem (show j ∈ l by simp [l])
    have hdpr := List.nodup_append'.mp (hp ▸ hnodup)
    have hpj : j ∉ p := fun hj => hdpr.2.2 hj (by simp)
    have hrj : j ∉ r := (List.nodup_cons.mp hdpr.2.1).1
    have hpr : p.length + r.length = 2 * (n - 1) + 1 := by
      rw [hp, List.length_append, List.length_cons] at hlen
      omega
    have hsign : (-1 : K) ^ p.length * (-1 : K) ^ r.length = -1 := by
      rw [← pow_add, hpr, pow_succ, pow_mul]
      simp
    have hTz : T z = -z := by
      rw [← hword, hp, cliffordWord_append, cliffordWord_cons, map_mul, map_mul,
        hTl p hpj, hTj, hTl r hrj, mul_smul_comm, smul_mul_smul, hsign, neg_one_smul]
    exact (hTz ▸ hT z).symm
  have hmove (x : V) : z * ι q x = ι q x * ((0 : K) • (1 : C) - z) := by
    let L := (LinearMap.mul K C z).comp (ι q)
    let R := ((LinearMap.mul K C).flip (-z)).comp (ι q)
    have h : L = R := b.ext hmove_basis
    rw [zero_smul, zero_sub]
    exact LinearMap.congr_fun h x
  have hsep : (0 : K) ^ 2 + 4 * signedDiscriminant q b ≠ 0 := by
    simpa using mul_ne_zero (show (4 : K) ≠ 0 by
      rw [show (4 : K) = 2 * 2 by norm_num]
      exact mul_ne_zero h₂ h₂) hd
  exact even_center_of_root q b hq (hnorm ⟨0, by omega⟩) hz _ _ hsep hzsq hmove

end CliffordCenter

section Symbols

open scoped TensorProduct
open Module

variable {K : Type u} [Field K] [CharP K 2]

private abbrev firstGenerator (d c : K) : Symbol K d c := ⟨0, 1, 0, 0⟩

private abbrev secondGenerator (d c : K) : Symbol K d c := ⟨0, 0, 1, 0⟩

private theorem firstGenerator_commutator {d c : K} (a : Symbol K d c) :
    firstGenerator d c * a - a * firstGenerator d c = ⟨0, 0, a.imJ, a.imK⟩ := by
  ext <;> simp [firstGenerator, CharTwo.sub_eq_add,
    add_left_comm, add_comm, CharTwo.add_self_eq_zero]
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

private theorem secondGenerator_commutator {d c : K} (x y : K) :
    secondGenerator d c * (⟨x, y, 0, 0⟩ : Symbol K d c) -
      (⟨x, y, 0, 0⟩ : Symbol K d c) * secondGenerator d c = y • secondGenerator d c := by
  ext <;> simp [secondGenerator, CharTwo.sub_eq_add, ← add_assoc,
    add_comm, CharTwo.add_self_eq_zero]

private theorem symbol_central_simple (d : K) (c : Kˣ) :
    _root_.Specs.RM03.CSA.isCentralSimple K (Symbol K d c) := by
  classical
  let Q := Symbol K d c
  let i : Q := firstGenerator d c
  let j : Q := secondGenerator d c
  have hcc : (c : K) ≠ 0 := Units.ne_zero _
  have hj : j * j = algebraMap K Q c := by
    change secondGenerator d (c : K) * secondGenerator d (c : K) =
      algebraMap K (Symbol K d c) c
    ext <;> simp [secondGenerator, QuaternionAlgebra.algebraMap_eq]
  have hju : IsUnit j := isUnit_mul_self_iff.mp (hj.symm ▸ c.isUnit.map (algebraMap K Q))
  refine ⟨IsSimpleRing.of_eq_bot_or_eq_top (fun J => ?_), ⟨fun a ha => ?_⟩, inferInstance⟩
  · by_cases hbot : J = ⊥
    · exact Or.inl hbot
    · right
      obtain ⟨a, ha, hane⟩ : ∃ a : Q, a ∈ J ∧ a ≠ 0 := by
        by_contra! h
        exact hbot (eq_bot_iff.mpr fun a ha => (TwoSidedIdeal.mem_bot Q).mpr (h a ha))
      have hunit (b : Q) (hb : b ∈ J) (hu : IsUnit b) : J = ⊤ := by
        obtain ⟨r, rfl⟩ := hu
        exact J.eq_top (by simpa using J.mul_mem_left (↑r⁻¹) ↑r hb)
      have hpair (x y : K) (h : (⟨x, y, 0, 0⟩ : Q) ∈ J) (hnz : x ≠ 0 ∨ y ≠ 0) : J = ⊤ := by
        by_cases hy : y = 0
        · subst y
          exact hunit _ h ((hnz.resolve_right (not_not_intro rfl)).isUnit.map (algebraMap K Q))
        · have hm := J.sub_mem (J.mul_mem_left j _ h) (J.mul_mem_right _ j h)
          change j * _ - _ * j ∈ J at hm
          rw [secondGenerator_commutator] at hm
          exact hunit _ hm (by
            rw [Algebra.smul_def]
            exact ((isUnit_iff_ne_zero.mpr hy).map (algebraMap K Q)).mul hju)
      have hc := J.sub_mem (J.mul_mem_left i a ha) (J.mul_mem_right a i ha)
      change firstGenerator d c * a - a * firstGenerator d c ∈ J at hc
      rw [firstGenerator_commutator] at hc
      by_cases hz : a.imJ = 0 ∧ a.imK = 0
      · have he : (⟨a.re, a.imI, 0, 0⟩ : Q) = a :=
          QuaternionAlgebra.ext rfl rfl hz.1.symm hz.2.symm
        apply hpair a.re a.imI (he.symm ▸ ha)
        by_contra! h
        exact hane (QuaternionAlgebra.ext h.1 h.2 hz.1 hz.2)
      · have hm := J.mul_mem_right _ j hc
        have he : (⟨0, 0, a.imJ, a.imK⟩ : Q) * j =
            ⟨(c : K) * a.imJ, (c : K) * a.imK, 0, 0⟩ := by
          change ((⟨0, 0, a.imJ, a.imK⟩ : Symbol K d c) * secondGenerator d (c : K)) = _
          ext <;> simp [secondGenerator, mul_comm]
        rw [he] at hm
        refine hpair _ _ hm ?_
        by_contra! h
        exact hz ⟨(mul_eq_zero.mp h.1).resolve_left hcc, (mul_eq_zero.mp h.2).resolve_left hcc⟩
  · rw [Algebra.mem_bot]
    have h := Subalgebra.mem_center_iff.mp ha
    have hi : (⟨0, 0, a.imJ, a.imK⟩ : Q) = 0 := by
      rw [← firstGenerator_commutator, (h i : firstGenerator d c * a = a * firstGenerator d c), sub_self]
    have hJ := congrArg QuaternionAlgebra.imJ hi
    have hK := congrArg QuaternionAlgebra.imK hi
    have he : a = (⟨a.re, a.imI, 0, 0⟩ : Q) := QuaternionAlgebra.ext rfl rfl hJ hK
    have hjc : a.imI • j = 0 := by
      have hj' := sub_eq_zero.mpr (h j)
      conv_lhs at hj' => rw [he]
      exact (secondGenerator_commutator a.re a.imI).symm.trans hj'
    have hI : a.imI = 0 := by
      simpa [Q, j, secondGenerator] using congrArg QuaternionAlgebra.imJ hjc
    exact ⟨a.re, QuaternionAlgebra.ext rfl hI.symm hJ.symm hK.symm⟩

omit [CharP K 2] in
private theorem symbol_norm (d c : K) (a : Symbol K d c) :
    (a * star a).re =
      QuadraticAlgebra.norm (⟨a.re, a.imI⟩ : QuadraticAlgebra K d 1) -
      c * QuadraticAlgebra.norm (⟨a.imJ, a.imK⟩ : QuadraticAlgebra K d 1) := by
  simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, QuadraticAlgebra.norm_def]
  ring

open private quaternion_isUnit_of_norm_ne_zero from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting

open private matrix2_of_nonunit from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.QuaternionNorm

private theorem split_symbol_iff_zero_norm (d : K) (c : Kˣ) :
    _root_.Specs.RM03.CSA.isSplit K (Symbol K d c) ↔
      ∃ a : Symbol K d c, a ≠ 0 ∧ (a * star a).re = 0 := by
  let Q := Symbol K d c
  constructor
  · rintro ⟨n, hn, ⟨e⟩⟩
    have hf := e.toLinearEquiv.finrank_eq
    rw [QuaternionAlgebra.finrank_eq_four, Module.finrank_matrix, Fintype.card_fin,
      Module.finrank_self, mul_one] at hf
    have h2 : n = 2 := by nlinarith
    subst n
    let x : Matrix (Fin 2) (Fin 2) K := Matrix.single 0 0 1
    have hx : x ≠ 0 := by
      intro h
      have he := congrFun (congrFun h 0) 0
      simp [x] at he
    have hx1 : x ≠ 1 := by
      intro h
      have he := congrFun (congrFun h 1) 1
      simp [x] at he
    have hxx : x * x = x := by simp [x, Matrix.single_mul_single_same]
    have hxu : ¬ IsUnit x :=
      fun hu => hx1 (hu.mul_left_cancel (hxx.trans (mul_one _).symm))
    refine ⟨e.symm x, fun he => hx ((map_eq_zero_iff e.symm e.symm.injective).mp he), ?_⟩
    by_contra hz
    exact hxu (by simpa using (quaternion_isUnit_of_norm_ne_zero hz).map e.toMonoidHom)
  · rintro ⟨a, ha, hz⟩
    have hp : a * star a = 0 := by rw [QuaternionAlgebra.mul_star_eq_coe, hz, QuaternionAlgebra.coe_zero]
    have hu : ¬ IsUnit a := by
      intro h
      exact ha (star_eq_zero.mp (h.mul_left_cancel (hp.trans (mul_zero _).symm)))
    exact ⟨2, by decide, matrix2_of_nonunit (symbol_central_simple d c)
      (QuaternionAlgebra.finrank_eq_four _ _ _) ha hu⟩

private theorem artin_schreier_norm_surjective {d : K} (hd : IsArtinSchreier d) :
    normSubgroup d = ⊤ := by
  obtain ⟨r, hr⟩ := hd
  apply top_unique
  intro c _
  let y : K := c + 1
  let x : K := c + r * y
  let a : QuadraticAlgebra K d 1 := ⟨x, y⟩
  have hn : QuadraticAlgebra.norm a = (c : K) := by
    calc
      _ = (x + r * y) * (x + (r + 1) * y) := by
        rw [QuadraticAlgebra.norm_def]
        change x * x + 1 * x * y - d * y * y = _
        rw [← hr, CharTwo.sub_eq_add]
        ring_nf
        simp [CharTwo.two_eq_zero]
      _ = _ := by
        have hx : x + r * y = (c : K) := by
          dsimp [x]
          rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
        have hx' : x + (r + 1) * y = 1 := by
          rw [add_mul, one_mul, ← add_assoc, hx]
          change (c : K) + (c + 1) = 1
          rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
        rw [hx, hx', mul_one]
  have hau : IsUnit a :=
    QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (hn.symm ▸ c.isUnit)
  exact ⟨hau.unit, Units.ext (by
    change QuadraticAlgebra.norm (↑hau.unit : QuadraticAlgebra K d 1) = (c : K)
    rw [hau.unit_spec, hn])⟩

private theorem symbol_split_iff_norm (d : K) (c : Kˣ) :
    _root_.Specs.RM03.CSA.isSplit K (Symbol K d c) ↔ c ∈ normSubgroup d := by
  rw [split_symbol_iff_zero_norm]
  constructor
  · rintro ⟨a, ha, hna⟩
    by_cases hd : IsArtinSchreier d
    · rw [artin_schreier_norm_surjective hd]
      exact Subgroup.mem_top _
    · let : Fact (∀ r : K, r ^ 2 ≠ d + (1 : K) * r) :=
        ⟨fun s h => hd ⟨s, by rw [h, one_mul, add_assoc, CharTwo.add_self_eq_zero, add_zero]⟩⟩
      let L := QuadraticAlgebra K d 1
      let x : L := ⟨a.re, a.imI⟩
      let y : L := ⟨a.imJ, a.imK⟩
      have hxy : QuadraticAlgebra.norm x = (c : K) * QuadraticAlgebra.norm y :=
        sub_eq_zero.mp ((symbol_norm d c a).symm.trans hna)
      have hy : y ≠ 0 := by
        intro hy0
        have hx0 : x = 0 := QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp (by simp [hxy, hy0])
        exact ha (QuaternionAlgebra.ext (congrArg QuadraticAlgebra.re hx0)
          (congrArg QuadraticAlgebra.im hx0) (congrArg QuadraticAlgebra.re hy0)
          (congrArg QuadraticAlgebra.im hy0))
      have hn (z : L) : QuadraticAlgebra.norm z = 0 ↔ z = 0 :=
        QuadraticAlgebra.norm_eq_zero_iff_eq_zero
      have hyN := (hn y).not.mpr hy
      have hr : QuadraticAlgebra.norm (x / y) = (c : K) := by
        apply mul_right_cancel₀ hyN
        rw [← map_mul, div_mul_cancel₀ _ hy, hxy]
      have hu : IsUnit (x / y) :=
        QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (hr.symm ▸ c.isUnit)
      exact ⟨hu.unit, Units.ext (by
        change QuadraticAlgebra.norm (↑hu.unit : L) = (c : K)
        rw [hu.unit_spec, hr])⟩
  · intro hc
    obtain ⟨x, hx⟩ := hc
    have h : QuadraticAlgebra.norm (↑x : QuadraticAlgebra K d 1) = (c : K) :=
      congrArg Units.val hx
    let a : Symbol K d c := ⟨(x : QuadraticAlgebra K d 1).re, (x : QuadraticAlgebra K d 1).im, 1, 0⟩
    refine ⟨a, fun he => one_ne_zero (congrArg QuaternionAlgebra.imJ he), ?_⟩
    rw [symbol_norm]
    change QuadraticAlgebra.norm (↑x : QuadraticAlgebra K d 1) -
      (c : K) * QuadraticAlgebra.norm (1 : QuadraticAlgebra K d 1) = 0
    rw [h, map_one, mul_one, sub_self]

omit [CharP K 2] in
private theorem tensor_quaternion_generators_commute {A : Type v} [Ring A] [Algebra K A]
    {d c e t : K} (p : QuaternionAlgebra.Basis A d 1 c)
    (r : QuaternionAlgebra.Basis A e 1 t)
    (hii : Commute p.i r.i) (hij : Commute p.i r.j)
    (hji : Commute p.j r.i) (hjj : Commute p.j r.j)
    (x : Symbol K d c) (y : Symbol K e t) : Commute (p.liftHom x) (r.liftHom y) := by
  have hc (a : A) (hi : Commute a r.i) (hj : Commute a r.j) :
      Commute a (r.liftHom y) := by
    change Commute a (algebraMap K A y.re + y.imI • r.i + y.imJ • r.j + y.imK • r.k)
    rw [← r.i_mul_j]
    have ha : Commute (algebraMap K A y.re) a := Algebra.commutes _ _
    exact ((ha.symm.add_right (hi.smul_right _)).add_right
      (hj.smul_right _)).add_right ((hi.mul_right hj).smul_right _)
  have hi := hc _ hii hij
  have hj := hc _ hji hjj
  change Commute (algebraMap K A x.re + x.imI • p.i + x.imJ • p.j + x.imK • p.k) _
  rw [← p.i_mul_j]
  have ha : Commute (algebraMap K A x.re) (r.liftHom y) := Algebra.commutes _ _
  exact ((ha.add_left (hi.smul_left _)).add_left
    (hj.smul_left _)).add_left ((hi.mul_left hj).smul_left _)

private theorem combine_symbols (d e : K) (c t : Kˣ) :
    Nonempty ((Symbol K (d + e) c ⊗[K] Symbol K e (c * t : Kˣ)) ≃ₐ[K]
      (Symbol K d c ⊗[K] Symbol K e t)) := by
  let X := Symbol K d c
  let Y := Symbol K e t
  let A := X ⊗[K] Y
  let : IsSimpleRing A := (RM03.CSA.isCentralSimple_tensor
    (symbol_central_simple d c) (symbol_central_simple e t)).1
  let : CharP A 2 := charP_of_injective_algebraMap (algebraMap K A).injective 2
  let l : X →ₐ[K] A := Algebra.TensorProduct.includeLeft
  let r : Y →ₐ[K] A := Algebra.TensorProduct.includeRight
  let p := (QuaternionAlgebra.Basis.self K).compHom l
  let q := (QuaternionAlgebra.Basis.self K).compHom r
  have hcross (a : X) (b : Y) : Commute (l a) (r b) := by
    change (a ⊗ₜ[K] (1 : Y)) * ((1 : X) ⊗ₜ[K] b) =
      ((1 : X) ⊗ₜ[K] b) * (a ⊗ₜ[K] (1 : Y))
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul, one_mul, mul_one]
  have hii : Commute p.i q.i := hcross _ _
  have hij : Commute p.i q.j := hcross _ _
  have hji : Commute p.j q.i := hcross _ _
  have hjj : Commute p.j q.j := hcross _ _
  have hpji : p.j * p.i = p.j + p.i * p.j := by
    rw [p.j_mul_i, one_smul, ← p.i_mul_j, CharTwo.sub_eq_add]
  have hqji : q.j * q.i = q.j + q.i * q.j := by
    rw [q.j_mul_i, one_smul, ← q.i_mul_j, CharTwo.sub_eq_add]
  let a := p.i + q.i
  let b := p.j * q.j
  have hai : a * a = (d + e) • (1 : A) + a := by
    change (p.i + q.i) * (p.i + q.i) = _
    calc
      _ = p.i * p.i + (p.i * q.i + p.i * q.i) + q.i * q.i := by
        rw [add_mul, mul_add, mul_add, ← hii.eq]
        abel
      _ = _ := by
        rw [CharTwo.add_self_eq_zero, add_zero, p.i_mul_i, q.i_mul_i, one_smul, one_smul,
          add_smul]
        change d • (1 : A) + p.i + (e • (1 : A) + q.i) =
          d • (1 : A) + e • (1 : A) + (p.i + q.i)
        abel
  have hbb : b * b = (↑(c * t) : K) • (1 : A) := by
    change (p.j * q.j) * (p.j * q.j) = _
    rw [hjj.symm.mul_mul_mul_comm, p.j_mul_j, q.j_mul_j, smul_mul_smul, mul_one]
    rfl
  have hbia : b * p.i = b + p.i * b := by
    change (p.j * q.j) * p.i = _
    rw [mul_assoc, ← hij.eq, ← mul_assoc, hpji, add_mul]
    simp only [b, mul_assoc]
  have hbiq : b * q.i = b + q.i * b := by
    change (p.j * q.j) * q.i = _
    rw [mul_assoc, hqji, mul_add, ← mul_assoc, hji.eq, mul_assoc]
  have hba : Commute a b := by
    change (p.i + q.i) * b = b * (p.i + q.i)
    rw [add_mul, mul_add, hbia, hbiq]
    calc
      _ = (b + p.i * b + (b + q.i * b)) - (b + b) := by
        abel
      _ = _ := by rw [CharTwo.add_self_eq_zero, sub_zero]
  let P : QuaternionAlgebra.Basis A (d + e) 1 (c : K) :=
    ⟨a, p.j, a * p.j, by simpa only [one_smul] using hai, p.j_mul_j, rfl, by
      change p.j * (p.i + q.i) = (1 : K) • p.j - (p.i + q.i) * p.j
      rw [mul_add, hpji, hji.eq, one_smul, CharTwo.sub_eq_add, add_mul, add_assoc]⟩
  let Q : QuaternionAlgebra.Basis A e 1 (↑(c * t) : K) :=
    ⟨q.i, b, q.i * b, q.i_mul_i, hbb, rfl, by
      rw [hbiq, one_smul, CharTwo.sub_eq_add]⟩
  have hPQi : Commute P.i Q.i := hii.add_left (Commute.refl _)
  have hPQj : Commute P.i Q.j := hba
  have hPjQi : Commute P.j Q.i := hji
  have hPjQj : Commute P.j Q.j := (Commute.refl _).mul_right hjj
  let f := Algebra.TensorProduct.lift P.liftHom Q.liftHom
    (tensor_quaternion_generators_commute P Q hPQi hPQj hPjQi hPjQj)
  let : IsSimpleRing (Symbol K (d + e) c ⊗[K] Symbol K e (c * t : Kˣ)) :=
    (RM03.CSA.isCentralSimple_tensor (symbol_central_simple (d + e) c)
      (symbol_central_simple e (c * t))).1
  have hf : Function.Injective f := f.toRingHom.injective
  have hdim : finrank K (Symbol K (d + e) c ⊗[K] Symbol K e (c * t : Kˣ)) = finrank K A := by
    simp only [A, X, Y, Module.finrank_tensorProduct, QuaternionAlgebra.finrank_eq_four]
  exact ⟨AlgEquiv.ofBijective f ⟨hf, (f.toLinearMap.linearEquivOfInjective hf hdim).surjective⟩⟩

private theorem symbol_matrix_equiv {d : K} {c : Kˣ} (hs : c ∈ normSubgroup d) :
    Nonempty (Symbol K d c ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := (symbol_split_iff_norm d c).mpr hs
  have hf := e.toLinearEquiv.finrank_eq
  rw [QuaternionAlgebra.finrank_eq_four, Module.finrank_matrix, Fintype.card_fin,
    Module.finrank_self, mul_one] at hf
  have hn2 : n = 2 := by nlinarith
  exact ⟨hn2 ▸ e⟩

omit [CharP K 2] in
private theorem square_mem_norm (d : K) (c : Kˣ) : c * c ∈ normSubgroup d := by
  refine ⟨Units.map (algebraMap K (QuadraticAlgebra K d 1)) c, Units.ext ?_⟩
  change QuadraticAlgebra.norm (algebraMap K (QuadraticAlgebra K d 1) c) = (c : K) * c
  rw [QuadraticAlgebra.norm_algebraMap, pow_two]

open private equivalent_of_matrix_presentation from
  MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.Equivalence

private theorem symbol_identities : SymbolIdentities.{u} := by
  intro K _ _ d e c t
  refine ⟨symbol_central_simple d c, symbol_split_iff_norm d c, ?_, ?_⟩
  · obtain ⟨f⟩ := combine_symbols d e c c
    obtain ⟨g⟩ := symbol_matrix_equiv (square_mem_norm e c)
    exact equivalent_of_matrix_presentation (by decide : 0 < 2)
      (f.symm.trans ((Algebra.TensorProduct.congr (AlgEquiv.refl) g).trans
        (matrixEquivTensor (Fin 2) K (Symbol K (d + e) c)).symm))
  · obtain ⟨f⟩ := combine_symbols d d c t
    have h0 : IsArtinSchreier (d + d) := ⟨0, by simp [CharTwo.add_self_eq_zero]⟩
    have hc : c ∈ normSubgroup (d + d) := by
      rw [artin_schreier_norm_surjective h0]
      exact Subgroup.mem_top _
    obtain ⟨g⟩ := symbol_matrix_equiv hc
    exact equivalent_of_matrix_presentation (by decide : 0 < 2)
      (f.symm.trans ((Algebra.TensorProduct.comm K _ _).trans
        ((Algebra.TensorProduct.congr (AlgEquiv.refl) g).trans
          (matrixEquivTensor (Fin 2) K (Symbol K d (c * t : Kˣ))).symm)))

private theorem artin_schreier_separable (d : K)
    [Fact (∀ s : K, s ^ 2 ≠ d + (1 : K) * s)] :
    Algebra.IsSeparable K (QuadraticAlgebra K d 1) := by
  open Polynomial in
  let p : K[X] := X ^ 2 + X + C d
  let L := QuadraticAlgebra K d 1
  let a : L := QuadraticAlgebra.omega
  have hs : p.Separable := by
    rw [Polynomial.separable_def]
    have hp : p.derivative = 1 := by
      simp [p, CharTwo.add_self_eq_zero]
    rw [hp]
    exact isCoprime_one_right
  have ha : Polynomial.aeval a p = 0 := by
    simp only [p, map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    change a ^ 2 + a + algebraMap K L d = 0
    rw [QuadraticAlgebra.omega_pow_two_eq_add, one_smul, ← Algebra.algebraMap_eq_smul_one]
    calc
      _ = (algebraMap K L d + algebraMap K L d) + (a + a) := by abel
      _ = _ := by
        have h₀ : a + a = 0 := by
          apply QuadraticAlgebra.ext
          · change (0 : K) + 0 = 0
            exact zero_add _
          · change (1 : K) + 1 = 0
            exact CharTwo.add_self_eq_zero _
        rw [h₀, add_zero, ← map_add, CharTwo.add_self_eq_zero, map_zero]
  have hasep : IsSeparable K a := hs.of_dvd (minpoly.dvd K a ha)
  have hamem : a ∈ separableClosure K L := hasep
  constructor
  intro x
  change x ∈ separableClosure K L
  have hx : x = algebraMap K L x.re + x.im • a := by ext <;> simp [a, L]
  rw [hx]
  exact (separableClosure K L).add_mem (IntermediateField.algebraMap_mem _ _)
    ((separableClosure K L).toSubalgebra.smul_mem hamem _)

private theorem symbol_presentation [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (d : K) (hd : ¬ IsArtinSchreier d) :
    ∃ c : Kˣ, ¬ _root_.Specs.RM03.CSA.isSplit K (Symbol K d c) ∧
      ∀ x : Symbol K d c, x ≠ 0 → IsUnit x := by
  classical
  let : Fact (∀ s : K, s ^ 2 ≠ d + (1 : K) * s) :=
    ⟨fun s h => hd ⟨s, by rw [h, one_mul, add_assoc, CharTwo.add_self_eq_zero, add_zero]⟩⟩
  let L := QuadraticAlgebra K d 1
  let : Algebra.IsSeparable K L := artin_schreier_separable d
  have hL : finrank K L = 2 := QuadraticAlgebra.finrank_eq_two _ _
  obtain ⟨B, _, _, hB, hb⟩ := LocalQuadraticSplitting.local_division_exists (F := K)
  obtain ⟨g⟩ := LocalQuadraticSplitting.quadratic_embedding hB hb hL
  have hCSA := RM03.CSA.isCentralSimple_of_isCentralDivision K B hB
  let : FiniteDimensional K B := hB.2
  change RM03.CSA.degree K B = 2 at hb
  have hdim : Module.finrank K B = 4 := by
    rw [RM03.CSA.finrank_eq_degree_sq hCSA, hb]
    rfl
  let σ : L →ₐ[K] L :=
    { toFun := star
      map_zero' := star_zero L
      map_one' := star_one L
      map_add' := star_add
      map_mul' := fun x y => (star_mul x y).trans (mul_comm _ _)
      commutes' := fun k => by
        change star (⟨k, 0⟩ : QuadraticAlgebra K d 1) = ⟨k, 0⟩
        rw [QuadraticAlgebra.star_mk, mul_zero, add_zero, neg_zero] }
  have hσ (a : L) : σ (σ a) = a := star_star _
  have hσfixed (a : L) (ha : σ a = a) : a = algebraMap K L a.re := by
    have h := congrArg QuadraticAlgebra.re ha
    change a.re + (1 : K) * a.im = a.re at h
    rw [one_mul] at h
    have h' := add_left_cancel (h.trans (add_zero a.re).symm)
    change a = (⟨a.re, 0⟩ : QuadraticAlgebra K d 1)
    exact QuadraticAlgebra.ext rfl h'
  obtain ⟨j, hj⟩ := RM03.CSA.skolem_noether hCSA (inferInstance : IsSimpleRing L)
    (g.comp σ) g (g.comp σ).toRingHom.injective g.injective
  have hj' (a : L) : (j : B) * g a = g (σ a) * j := (hj a).symm
  let R := g.range
  let C := Subalgebra.centralizer K (R : Set B)
  have hR : IsSimpleRing R :=
    IsSimpleRing.of_ringEquiv (AlgEquiv.ofInjective g g.injective).toRingEquiv inferInstance
  have hRdim : finrank K R = 2 :=
    (AlgEquiv.ofInjective g g.injective).toLinearEquiv.finrank_eq.symm.trans hL
  have hCdim := (RM03.CSA.centralizer_simple_and_finrank hCSA R hR).2
  change finrank K R * finrank K C = finrank K B at hCdim
  rw [hRdim, hdim] at hCdim
  have hRC : R.toSubmodule = C.toSubmodule := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro x ⟨a, rfl⟩
      apply (Subalgebra.mem_centralizer_iff K).mpr
      rintro y ⟨b, rfl⟩
      rw [← map_mul, ← map_mul, mul_comm a b]
    · change finrank K R = finrank K C
      rw [hRdim]
      omega
  have hjj : (j : B) * j ∈ R := by
    change (j : B) * j ∈ R.toSubmodule
    rw [hRC]
    apply (Subalgebra.mem_centralizer_iff K).mpr
    rintro a ⟨b, rfl⟩
    have he := hj' (σ b)
    rw [hσ] at he
    change g b * ((j : B) * j) = ((j : B) * j) * g b
    calc
      _ = (g b * (j : B)) * j := by rw [mul_assoc]
      _ = (j : B) * (g (σ b) * j) := by rw [← he, mul_assoc]
      _ = _ := by rw [← hj' b, ← mul_assoc]
  obtain ⟨a, ha⟩ := hjj
  change g a = (j : B) * j at ha
  have hfix : σ a = a := by
    apply g.injective
    apply j.isUnit.mul_right_cancel
    change g (σ a) * (j : B) = g a * j
    rw [← hj' a, ha, mul_assoc]
  have hScalar : (j : B) * j = algebraMap K B a.re := by
    exact ha.symm.trans ((congrArg g (hσfixed a hfix)).trans (g.commutes _))
  have ha0 : a.re ≠ 0 := fun hz =>
    (j.isUnit.mul j.isUnit).ne_zero (by rw [hScalar, hz, map_zero])
  let c := Units.mk0 a.re ha0
  let i : B := g QuadraticAlgebra.omega
  have hii : i * i = d • (1 : B) + (1 : K) • i := by
    dsimp [i]
    rw [← map_mul, QuadraticAlgebra.omega_mul_omega_eq_add, map_add, map_smul, map_smul, map_one]
  have hji : (j : B) * i = (1 : K) • (j : B) - i * j := by
    change (j : B) * g (QuadraticAlgebra.omega : L) = _
    have h' : σ QuadraticAlgebra.omega = 1 - QuadraticAlgebra.omega := by
      change star (QuadraticAlgebra.omega : QuadraticAlgebra K d 1) =
        1 - QuadraticAlgebra.omega
      apply QuadraticAlgebra.ext
      · change (0 : K) + 1 * 1 = 1 - 0
        simp
      · change -(1 : K) = 0 - 1
        rw [zero_sub]
    rw [hj', h', map_sub, map_one, sub_mul, one_mul, one_smul]
  let q : QuaternionAlgebra.Basis B d 1 (c : K) :=
    ⟨i, j, i * (j : B), hii, hScalar.trans (Algebra.algebraMap_eq_smul_one _), rfl, hji⟩
  let f := q.liftHom
  let : IsSimpleRing (Symbol K d c) := (symbol_central_simple d c).1
  have hf : Function.Injective f := f.toRingHom.injective
  have hunit (x : Symbol K d c) (hx : x ≠ 0) : IsUnit x := by
    let e := AlgEquiv.ofBijective f ⟨hf,
      (f.toLinearMap.linearEquivOfInjective hf ((QuaternionAlgebra.finrank_eq_four _ _ _).trans
        hdim.symm)).surjective⟩
    have he : e x ≠ 0 := fun hz => hx (e.injective (hz.trans (map_zero e).symm))
    simpa using he.isUnit.map e.symm.toMonoidHom
  refine ⟨c, ?_, hunit⟩
  rintro hs
  obtain ⟨x, hx, hnorm⟩ := (split_symbol_iff_zero_norm d c).mp hs
  have hp : x * star x = 0 := by
    rw [QuaternionAlgebra.mul_star_eq_coe, hnorm, QuaternionAlgebra.coe_zero]
  exact hx (star_eq_zero.mp ((hunit x hx).mul_left_cancel (hp.trans (mul_zero _).symm)))

private noncomputable def symbolCSA (d : K) (c : Kˣ) : _root_.CSA.{u, u} K :=
  RM03.CSA.toCSA (symbol_central_simple d c)

private noncomputable def symbolClass (d : K) (c : Kˣ) : BrauerGroup.{u, u} K :=
  RM03.Brauer.classOf (symbolCSA d c)

private theorem symbol_class_eq_zero (d : K) (c : Kˣ) :
    symbolClass d c = 0 ↔ c ∈ normSubgroup d :=
  (RM03.Brauer.classOf_eq_zero_iff_split (symbolCSA d c)).trans (symbol_split_iff_norm d c)

private theorem symbol_class_eq (d e : K) (c t : Kˣ) :
    symbolClass d c = symbolClass e t ↔
      _root_.Specs.RM03.Brauer.equivalent K (Symbol K d c) (Symbol K e t) :=
  RM03.Brauer.classOf_eq_iff K (symbolCSA d c) (symbolCSA e t)

private theorem symbol_class_add (d e : K) (c : Kˣ) :
    symbolClass d c + symbolClass e c = symbolClass (d + e) c := by
  rw [symbolClass, symbolClass, symbolClass, RM03.Brauer.classOf_add]
  exact (RM03.Brauer.classOf_eq_iff K _ _).mpr (symbol_identities d e c 1).2.2.1

private theorem symbol_class_mul (d : K) (c t : Kˣ) :
    symbolClass d c + symbolClass d t = symbolClass d (c * t) := by
  rw [symbolClass, symbolClass, symbolClass, RM03.Brauer.classOf_add]
  exact (RM03.Brauer.classOf_eq_iff K _ _).mpr (symbol_identities d 0 c t).2.2.2

private theorem symbol_class_double (d : K) (c : Kˣ) :
    symbolClass d c + symbolClass d c = 0 :=
  (symbol_class_mul d c c).trans ((symbol_class_eq_zero d _).mpr (square_mem_norm d c))

private theorem nonsplit_symbols_same_class [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (d e : K) (c t : Kˣ)
    (hd : symbolClass d c ≠ 0) (he : symbolClass e t ≠ 0) :
    symbolClass d c = symbolClass e t := by
  have unit_or_zero (b : K) (s : Kˣ) (h : symbolClass b s ≠ 0) (x : Symbol K b s) :
      IsUnit x ∨ x = 0 := by
    by_cases hx : x = 0
    · exact Or.inr hx
    · refine Or.inl (quaternion_isUnit_of_norm_ne_zero ?_)
      intro hz
      exact h ((symbol_class_eq_zero _ _).mpr ((symbol_split_iff_norm _ _).mp
        ((split_symbol_iff_zero_norm _ _).mpr ⟨x, hx, hz⟩)))
  let : DivisionRing (Symbol K d c) := DivisionRing.ofIsUnitOrEqZero (unit_or_zero d c hd)
  let : DivisionRing (Symbol K e t) := DivisionRing.ofIsUnitOrEqZero (unit_or_zero e t he)
  have hdeg (b : K) (s : Kˣ) : _root_.Specs.RM03.CSA.degree K (Symbol K b s) = 2 := by
    change Nat.sqrt (finrank K (Symbol K b s)) = 2
    rw [QuaternionAlgebra.finrank_eq_four]
    exact Nat.sqrt_eq' 2
  obtain ⟨f⟩ := LocalQuadraticSplitting.local_division_unique
    ⟨(symbol_central_simple d c).2.1, inferInstance⟩ (hdeg d c)
    ⟨(symbol_central_simple e t).2.1, inferInstance⟩ (hdeg e t)
  exact RM03.Brauer.classOf_eq_of_algEquiv (A := symbolCSA d c) (B := symbolCSA e t) f

private theorem norm_character [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (d : K) (c : Kˣ) (hc : ¬ _root_.Specs.RM03.CSA.isSplit K (Symbol K d c)) :
    ∃ χ : Kˣ →* Multiplicative (ZMod 2),
      Function.Surjective χ ∧ χ.ker = normSubgroup d ∧ (normSubgroup d).index = 2 ∧
      (∀ a b : Kˣ, χ a = χ b ↔
        _root_.Specs.RM03.Brauer.equivalent K (Symbol K d a) (Symbol K d b)) := by
  classical
  let T := Multiplicative (ZMod 2)
  let m : T := Multiplicative.ofAdd 1
  have hm : m ≠ 1 := by decide
  have hm₂ : m * m = 1 := by decide
  let β := symbolClass d c
  have hβ : β ≠ 0 := fun hz => hc ((symbol_split_iff_norm d c).mpr ((symbol_class_eq_zero _ _).mp hz))
  have hβ₂ : β + β = 0 := symbol_class_double d c
  have hcases (a : Kˣ) : symbolClass d a = 0 ∨ symbolClass d a = β := by
    by_cases ha : symbolClass d a = 0
    · exact Or.inl ha
    · exact Or.inr (nonsplit_symbols_same_class _ _ _ _ ha hβ)
  let f (a : Kˣ) : T := if symbolClass d a = 0 then 1 else m
  let χ : Kˣ →* T :=
    { toFun := f
      map_one' := by
        change f 1 = 1
        simp [f, (symbol_class_eq_zero d 1).mpr (one_mem _)]
      map_mul' := by
        intro a b
        change f (a * b) = f a * f b
        rcases hcases a with h₁ | h₁ <;> rcases hcases b with h₂ | h₂ <;>
          simp [f, ← symbol_class_mul, h₁, h₂, hβ, hβ₂, hm₂] }
  have hsurj : Function.Surjective χ := by
    intro x
    have hx : x = (1 : T) ∨ x = m := by
      change x = Multiplicative.ofAdd (0 : ZMod 2) ∨ x = Multiplicative.ofAdd (1 : ZMod 2)
      fin_cases x <;> decide
    rcases hx with rfl | rfl
    · exact ⟨1, map_one χ⟩
    · exact ⟨c, by
        change f c = m
        exact ite_eq_right hβ⟩
  have hk : χ.ker = normSubgroup d := by
    ext a
    change f a = 1 ↔ a ∈ normSubgroup d
    rw [← symbol_class_eq_zero]
    by_cases ha : symbolClass d a = 0 <;> simp [f, ha, hm]
  have hidx : (normSubgroup d).index = 2 := by
    rw [← hk, Subgroup.index, Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective χ hsurj).toEquiv]
    change Nat.card (Multiplicative (ZMod 2)) = 2
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2), Nat.card_zmod]
  refine ⟨χ, hsurj, hk, hidx, fun a b => ?_⟩
  rw [← symbol_class_eq]
  change f a = f b ↔ _
  rcases hcases a with h₁ | h₁ <;> rcases hcases b with h₂ | h₂ <;>
    simp [f, h₁, h₂, hβ, hβ.symm, hm, hm.symm]

private theorem local_norm_groups : LocalNormGroups.{u} := by
  classical
  intro K _ _ _ _ _ d hd
  obtain ⟨c, hc, hu⟩ := symbol_presentation d hd
  obtain ⟨χ, hsurj, hker, hidx, hsym⟩ := norm_character d c hc
  refine ⟨⟨c, hc, hu⟩, χ, hsurj, hker, hidx, hsym, fun e he hde => ?_⟩
  have hne : normSubgroup d ≠ normSubgroup e := by
    intro heq
    obtain ⟨s, hs, _⟩ := symbol_presentation (d + e) hde
    have heqClass : symbolClass d s = symbolClass e s := by
      by_cases hn : s ∈ normSubgroup d
      · exact ((symbol_class_eq_zero d s).mpr hn).trans
          (((symbol_class_eq_zero e s).mpr (heq ▸ hn)).symm)
      · exact nonsplit_symbols_same_class _ _ _ _
          ((symbol_class_eq_zero d s).not.mpr hn)
          ((symbol_class_eq_zero e s).not.mpr (heq ▸ hn))
    apply hs
    apply (symbol_split_iff_norm _ _).mpr
    apply (symbol_class_eq_zero _ _).mp
    rw [← symbol_class_add, ← heqClass, symbol_class_double]
  refine ⟨hne, ?_⟩
  let J := normSubgroup d ⊔ normSubgroup e
  have hdJ : normSubgroup d ≤ J := le_sup_left
  have heJ : normSubgroup e ≤ J := le_sup_right
  change J = ⊤
  have hDvd : J.index ∣ 2 := hidx ▸ Subgroup.index_dvd_of_le hdJ
  rcases (Nat.dvd_prime Nat.prime_two).mp hDvd with hj | hj
  · exact Subgroup.index_eq_one.mp hj
  · let : J.FiniteIndex := ⟨hj ▸ (by decide : (2 : ℕ) ≠ 0)⟩
    have hd' : normSubgroup d = J := Subgroup.eq_of_index_dvd_index hdJ (by rw [hidx, hj])
    obtain ⟨t, ht, _⟩ := symbol_presentation e he
    obtain ⟨_, _, _, hidxE, _⟩ := norm_character e t ht
    have he' : normSubgroup e = J := Subgroup.eq_of_index_dvd_index heJ (by rw [hidxE, hj])
    exact (hne (hd'.trans he'.symm)).elim

end Symbols

section QuaternionKernels

open CliffordAlgebra Module
open _root_.LinearAlgebraicGroups.Albert

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

private theorem even_finrank_four (q : QuadraticForm K V) (b : Basis (Fin 4) K V) :
    finrank K (even q) = 8 := by
  have hc : Fintype.card {s : Finset (Fin 4) // (s.card : ZMod 2) = 0} = 8 := by decide
  obtain ⟨B, hB⟩ := CliffordModel.ordered_basis q b
  let I := {s : Finset (Fin 4) // (s.card : ZMod 2) = 0}
  have hspan : Submodule.span K (Set.range (fun s : I => B s.val)) =
      (even q).toSubmodule := by
    rw [even_toSubmodule, CliffordModel.parity_span q b 0]
    congr 1
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s.val, s.property, (hB s.val).symm⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, hB s⟩
  change finrank K (even q).toSubmodule = 8
  have hl : LinearIndependent K (fun i : I => B i.val) :=
    B.linearIndependent.comp _ Subtype.val_injective
  rw [← hspan, finrank_span_eq_card hl]
  exact hc

private theorem quaternion_even_factors (q : QuadraticForm K V) (b : Basis (Fin 4) K V)
    {a β c scale : K}
    (hD : _root_.Specs.RM03.CSA.isCentralSimple K (QuaternionAlgebra K a β c))
    (hscale : scale ≠ 0) (hu : ∀ z : QuaternionAlgebra K a β c, z ≠ 0 → IsUnit z)
    (e : V ≃ₗ[K] QuaternionAlgebra K a β c)
    (he : ∀ x, q x = scale * (e x * star (e x)).re) :
    HasEvenDivisionClass (D := QuaternionAlgebra K a β c) q := by
  let A := QuaternionAlgebra K a β c
  have hnorm (x : A) : x * star x = algebraMap K A (x * star x).re :=
    QuaternionAlgebra.mul_star_eq_coe x
  have hnorm' (x : A) : star x * x = algebraMap K A (x * star x).re :=
    (star_comm_self' x).trans (hnorm x)
  let f₂ : EvenHom q (A × A) :=
    { bilin := LinearMap.mk₂ K (fun x y : V =>
        (scale • (e x * star (e y)), scale • (star (e x) * e y)))
        (by intros; apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add, star_add, add_mul, smul_add])
        (by intros; apply Prod.ext <;>
          simp only [Prod.smul_fst, Prod.smul_snd, map_smul, QuaternionAlgebra.star_smul,
            smul_mul_assoc, smul_comm scale _])
        (by intros; apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add, star_add, mul_add, smul_add])
        (by intros; apply Prod.ext <;>
          simp only [Prod.smul_fst, Prod.smul_snd, map_smul, QuaternionAlgebra.star_smul,
            mul_smul_comm, smul_comm scale _])
      contract := by
        intro x
        apply Prod.ext
        · change scale • (e x * star (e x)) = algebraMap K A (q x)
          rw [he, hnorm, Algebra.smul_def, ← map_mul]
          rfl
        · change scale • (star (e x) * e x) = algebraMap K A (q x)
          rw [he, hnorm', Algebra.smul_def, ← map_mul]
      contract_mid := by
        intro x y z
        have hmul (i j : A) (p : K) :
            (scale * scale) • (i * (algebraMap K A p * j)) = (scale * p) • (scale • (i * j)) := by
          rw [← Algebra.smul_def, mul_smul_comm, smul_smul, smul_smul]
          congr 1
          ring
        apply Prod.ext
        · change (scale • (e x * star (e y))) * (scale • (e y * star (e z))) =
            q y • (scale • (e x * star (e z)))
          rw [smul_mul_smul, he y, mul_assoc, ← mul_assoc (star (e y)), hnorm', hmul]
        · change (scale • (star (e x) * e y)) * (scale • (star (e y) * e z)) =
            q y • (scale • (star (e x) * e z))
          rw [smul_mul_smul, he y, mul_assoc, ← mul_assoc (e y),
            hnorm (e y), hmul]
          rfl }
  let f := even.lift q f₂
  have hdiag (p : A) : (p, star p) ∈ f.range := by
    refine ⟨(even.ι q).bilin (e.symm (scale⁻¹ • p)) (e.symm 1), ?_⟩
    change (even.lift q f₂) ((even.ι q).bilin _ _) = _
    rw [even.lift_ι]
    change (scale • (e (e.symm (scale⁻¹ • p)) * star (e (e.symm 1))),
      scale • (star (e (e.symm (scale⁻¹ • p))) * e (e.symm 1))) = (p, star p)
    simp only [e.apply_symm_apply, star_one, mul_one, smul_smul, mul_inv_cancel₀ hscale, one_smul]
    rw [show star (scale⁻¹ • p) = scale⁻¹ • star p from QuaternionAlgebra.star_smul _ _,
      smul_smul, mul_inv_cancel₀ hscale, one_smul]
  have hd : RM03.CSA.degree K A = 2 := by
    change Nat.sqrt (finrank K A) = 2
    rw [QuaternionAlgebra.finrank_eq_four]
    exact Nat.sqrt_eq' 2
  obtain ⟨x, y, hxy⟩ := Composition.quaternion_noncommutative hD hd
  let r : A := star x * star y - star (x * y)
  have hr : r ≠ 0 := by
    intro heq
    apply hxy
    have hs := sub_eq_zero.mp heq
    change star x * star y = star (x * y) at hs
    rw [star_mul] at hs
    simpa using (congrArg star hs).symm
  have hzero : ((0 : A), r) ∈ f.range := by
    have hp := f.range.sub_mem (f.range.mul_mem (hdiag x) (hdiag y)) (hdiag (x * y))
    change ((x * y - x * y), r) ∈ f.range at hp
    rwa [sub_self] at hp
  let u := (hu r hr).unit
  have hU : (↑u : A) = r := (hu r hr).unit_spec
  have h01 : ((0 : A), (1 : A)) ∈ f.range := by
    have hp := f.range.mul_mem hzero (hdiag (star (↑u⁻¹ : A)))
    change ((0 : A) * star (↑u⁻¹ : A), r * star (star (↑u⁻¹ : A))) ∈ f.range at hp
    rw [zero_mul, star_star, ← hU, Units.mul_inv] at hp
    exact hp
  have hsurj : Function.Surjective f := by
    rintro ⟨x, y⟩
    have h0 (z : A) : ((0 : A), z) ∈ f.range := by
      have hz := f.range.mul_mem h01 (hdiag (star z))
      change ((0 : A) * star z, 1 * star (star z)) ∈ f.range at hz
      rwa [zero_mul, one_mul, show star (star z) = z from star_star z] at hz
    have hx := f.range.add_mem (hdiag x) (h0 (y - star x))
    change (x + 0, star x + (y - star x)) ∈ f.range at hx
    simpa [add_comm, sub_add_cancel] using hx
  have hdim : finrank K (even q) = finrank K (A × A) := by
    rw [even_finrank_four q b, Module.finrank_prod, QuaternionAlgebra.finrank_eq_four]
  have hinj : Function.Injective f := by
    obtain ⟨B, _⟩ := CliffordModel.ordered_basis q b
    let : FiniteDimensional K (CliffordAlgebra q) := Module.Finite.of_basis B
    let : FiniteDimensional K (even q) :=
      FiniteDimensional.of_injective (even q).val.toLinearMap Subtype.val_injective
    have htop : f.toLinearMap.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
    have hr : finrank K f.toLinearMap.range = finrank K (A × A) := by
      rw [htop, finrank_top]
    have hfin : finrank K (LinearMap.ker f.toLinearMap) = 0 := by
      have heq := f.toLinearMap.finrank_range_add_finrank_ker
      omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hfin)
  let iso := AlgEquiv.ofBijective f ⟨hinj, hsurj⟩
  let : Small.{v} A := Small.mk' e.symm.toEquiv
  let S := Shrink.{v} A
  let g : S ≃ₐ[K] A := Shrink.algEquiv K A
  let : Algebra.IsCentral K A := hD.2.1
  have hCentral : Algebra.IsCentral K S := by
    constructor
    intro x hx
    have hgx : g x ∈ Subalgebra.center K A :=
      (MulEquivClass.apply_mem_center_iff g).mpr hx
    obtain ⟨k, hk⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hgx)
    exact Algebra.mem_bot.mpr ⟨k, g.injective ((g.commutes k).trans hk)⟩
  have hS : _root_.Specs.RM03.CSA.isCentralSimple K S :=
    ⟨IsSimpleRing.of_ringEquiv g.symm.toRingEquiv hD.1,
      hCentral,
      FiniteDimensional.of_injective g.toLinearMap g.injective⟩
  let P := _root_.Specs.RM03.CSA.toCSA hS
  let h : A ≃ₐ[K] P := g.symm
  have hEq : _root_.Specs.RM03.Brauer.equivalent K P A :=
    ⟨1, 1, Nat.one_pos, Nat.one_pos, ⟨g.mapMatrix⟩⟩
  exact ⟨P, P, ⟨iso.trans (AlgEquiv.prodCongr h h)⟩, hEq, hEq⟩

private theorem square_discriminant_change_basis {n : ℕ} (q : QuadraticForm K V)
    (b b' : Basis (Fin (2 * n)) K V) (h : IsSquare (signedDiscriminant q b)) :
    IsSquare (signedDiscriminant q b') := by
  classical
  let B : LinearMap.BilinForm K V := (2 : K)⁻¹ • q.polarBilin
  have hmat (c : Basis (Fin (2 * n)) K V) :
      B.toMatrix c = (Matrix.of fun i j => q.polarBilin (c i) (c j) / 2) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    change (2 : K)⁻¹ * q.polarBilin (c i) (c j) = q.polarBilin (c i) (c j) / 2
    rw [div_eq_mul_inv, mul_comm]
  have he := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b b' B
  have hdet := congrArg Matrix.det he
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hmat, hmat] at hdet
  obtain ⟨s, hs⟩ := h
  refine ⟨(b.toMatrix b').det * s, ?_⟩
  calc
    signedDiscriminant q b' = (b.toMatrix b').det ^ 2 * signedDiscriminant q b := by
      unfold signedDiscriminant
      rw [← hdet]
      ring
    _ = _ := by rw [hs]; ring

open private quaternion_isUnit_or_zero quaternion_central quaternion_reduced_norm
  quaternion_norm_formula from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuadraticIsotropy

set_option maxHeartbeats 1200000 in
private theorem anisotropic_diagonal_quaternion [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (q : QuadraticForm K V)
    (w : Fin 4 → K) (e : q.IsometryEquiv (QuadraticMap.weightedSumSquares K w))
    (h₂ : (2 : K) ≠ 0) (hani : ¬ IsIsotropic q) :
    ∃ (scale A C : K), scale ≠ 0 ∧ A ≠ 0 ∧ C ≠ 0 ∧
      let D := QuaternionAlgebra K A 0 C
      ∃ _hD : _root_.Specs.RM03.CSA.isCentralSimple K D,
        (∀ x : D, x ≠ 0 → IsUnit x) ∧
        (∃ f : V ≃ₗ[K] D, ∀ x, q x = scale * (f x * star (f x)).re) ∧
        IsSquare (∏ i, w i) := by
  classical
  let p := w 0
  let a := w 1
  let c := w 2
  let d := w 3
  have hform (x : Fin 4 → K) :
      q (e.symm x) = p * x 0 ^ 2 + a * x 1 ^ 2 + c * x 2 ^ 2 + d * x 3 ^ 2 := by
    rw [e.symm.map_app, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_four]
    dsimp [p, a, c, d]
    ring
  have hz (x : Fin 4 → K) (hx : q (e.symm x) = 0) : x = 0 := by
    by_contra h
    exact hani ⟨e.symm x, fun h0 => h (e.symm.toLinearEquiv.injective (by simpa using h0)), hx⟩
  have hweight (i : Fin 4) : w i ≠ 0 := by
    intro hi
    let x : Fin 4 → K := Pi.single i 1
    have hx : q (e.symm x) = 0 := by
      rw [e.symm.map_app, QuadraticMap.weightedSumSquares_apply]
      rw [Finset.sum_eq_single i]
      · simp [x, hi]
      · intro j _ hj; simp [x, Pi.single_eq_of_ne hj]
      · simp
    have h := congrFun (hz x hx) i
    simp [x] at h
  have hp : p ≠ 0 := hweight 0
  have ha : a ≠ 0 := hweight 1
  have hc : c ≠ 0 := hweight 2
  have hd : d ≠ 0 := hweight 3
  have ht (x y z : K) (h : a * x ^ 2 + c * y ^ 2 + d * z ^ 2 = 0) :
      x = 0 ∧ y = 0 ∧ z = 0 := by
    let X : Fin 4 → K := ![0, x, y, z]
    have heX := hz X (by simpa [hform, X] using h)
    exact ⟨congrFun heX 1, congrFun heX 2, congrFun heX 3⟩
  let scale := a * c / d
  have hscale : scale ≠ 0 := div_ne_zero (mul_ne_zero ha hc) hd
  have hsq : IsSquare (p / scale) := by
    by_contra h
    obtain ⟨x, y, z, he'⟩ :=
      (LocalQuadraticIsotropy.ternary_values h₂ a c d ha hc hd ht (-p) (neg_ne_zero.mpr hp)).mpr
        (by simpa [scale, neg_div] using h)
    let X : Fin 4 → K := ![1, x, y, z]
    have hX : q (e.symm X) = 0 := by
      rw [hform]
      change p * 1 ^ 2 + a * x ^ 2 + c * y ^ 2 + d * z ^ 2 = 0
      linear_combination he'
    exact one_ne_zero (congrFun (hz X hX) 0)
  obtain ⟨r, hr⟩ := hsq
  have hpr : p = scale * (r * r) := by
    apply (div_eq_iff hscale).mp at hr
    rwa [mul_comm] at hr
  have hr0 : r ≠ 0 := by
    intro h
    exact hp (by simp [hpr, h])
  let A := -(a / scale)
  let C := -(c / scale)
  have hA : A ≠ 0 := neg_ne_zero.mpr (div_ne_zero ha hscale)
  have hC : C ≠ 0 := neg_ne_zero.mpr (div_ne_zero hc hscale)
  have hcoeffA : scale * -A = a := by simp [A, div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ hscale]
  have hcoeffC : scale * -C = c := by simp [C, div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ hscale]
  have hcoeffAC : scale * (A * C) = d := by
    dsimp only [A, C]
    rw [neg_mul_neg, ← mul_div_mul_comm, ← div_div, mul_comm scale, div_mul_cancel₀ _ hscale]
    dsimp only [scale]
    field_simp
  let D := QuaternionAlgebra K A 0 C
  have hPure (x y z : K) :
      scale * LinearAlgebraicGroups.Specs.Arithmetic.LocalQuadraticIsotropy.pureNorm A C x y z =
        a * x^2 + c * y^2 + d * z^2 := by
    unfold LinearAlgebraicGroups.Specs.Arithmetic.LocalQuadraticIsotropy.pureNorm
    calc
      _ = (scale * -A) * x ^ 2 + (scale * -C) * y ^ 2 + (scale * (A * C)) * z ^ 2 := by
        ring
      _ = _ := by rw [hcoeffA, hcoeffC, hcoeffAC]
  have hu₀ := quaternion_isUnit_or_zero (F := K) (a := A) (b := C) (fun x y z h =>
    ht x y z (by rw [← hPure, h, mul_zero]))
  have hSimple : IsSimpleRing D := by
    let : DivisionRing D := DivisionRing.ofIsUnitOrEqZero hu₀
    infer_instance
  have hD : _root_.Specs.RM03.CSA.isCentralSimple K D :=
    ⟨hSimple, quaternion_central h₂ hA, inferInstance⟩
  have hu (x : D) (hx : x ≠ 0) : IsUnit x := (hu₀ x).resolve_right hx
  let s : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) :=
    LinearEquiv.piCongrRight (fun i =>
      if i = 0 then LinearEquiv.smulOfUnit (Units.mk0 r hr0) else LinearEquiv.refl K K)
  let qeq := (e.toLinearEquiv.trans s).trans (QuaternionAlgebra.linearEquivTuple A 0 C).symm
  have hNorm (x : V) : q x = scale * (qeq x * star (qeq x)).re := by
    have hx : q x = p * e x 0 ^ 2 + a * e x 1 ^ 2 +
        c * e x 2 ^ 2 + d * e x 3 ^ 2 := by
      simpa only [e.symm_apply_apply] using hform (e x)
    have hqe : qeq x = ⟨r * e x 0, e x 1, e x 2, e x 3⟩ := by
      simp [qeq, s, LinearEquiv.smulOfUnit, Units.smul_def, QuaternionAlgebra.coe_linearEquivTuple_symm,
        smul_eq_mul]
    rw [hqe, quaternion_norm_formula, mul_add, hPure, hx, hpr]
    dsimp only
    ring
  have hdet : IsSquare (∏ i, w i) := by
    refine ⟨r * a * c, ?_⟩
    rw [Fin.prod_univ_four]
    change p * a * c * d = _
    rw [hpr]
    dsimp only [scale]
    field_simp
  exact ⟨scale, A, C, hscale, hA, hC, hD, hu, ⟨qeq, hNorm⟩, hdet⟩

private theorem odd_quaternion_kernel : OddQuaternionKernel.{u, v} := by
  classical
  intro K _ _ _ _ V _ _ q b h₂ _ hani
  let : FiniteDimensional K V := Module.Finite.of_basis b
  let : Invertible (2 : K) := (isUnit_iff_ne_zero.mpr h₂).invertible
  have hdim : finrank K V = 4 :=
    (Module.finrank_eq_card_basis b).trans (Fintype.card_fin _)
  obtain ⟨b₀, hO₀⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := QuadraticMap.associated (R := K) q)
    ⟨QuadraticMap.associated_isSymm K q⟩
  let c : Basis (Fin 4) K V := b₀.reindex (finCongr hdim)
  have hO : (QuadraticMap.associated (R := K) q).IsOrthoᵢ c := by
    intro i j hij
    change QuadraticMap.associated (R := K) q (c i) (c j) = 0
    dsimp only [c]
    rw [Basis.reindex_apply, Basis.reindex_apply]
    exact hO₀ ((finCongr hdim).symm.injective.ne hij)
  let w : Fin 4 → K := fun i => q (c i)
  have e : q.IsometryEquiv (QuadraticMap.weightedSumSquares K w) := by
    rw [← QuadraticMap.basisRepr_eq_of_iIsOrtho q c hO]
    exact q.isometryEquivBasisRepr c
  obtain ⟨scale, A, C, hscale, hA, hC, hD, hu, ⟨f, hf⟩, hd⟩ :=
    anisotropic_diagonal_quaternion q w e h₂ hani
  have hNR (x : V) : q x = scale * _root_.Specs.RM03.CSA.reducedNorm hD (f x) :=
    (hf x).trans (congrArg (scale * ·) (quaternion_reduced_norm h₂ hA hC hD (f x)).symm)
  have hpol (i j : Fin 4) (hij : i ≠ j) : q.polarBilin (c i) (c j) = 0 := by
    rw [← QuadraticMap.two_nsmul_associated (S := K)]
    change 2 • QuadraticMap.associated (R := K) q (c i) (c j) = 0
    rw [hO hij, nsmul_zero]
  have hdisc : IsSquare (signedDiscriminant q (n := 2) c) := by
    rw [signed_discriminant_diagonal q (n := 2) c h₂ hpol, neg_one_sq, one_mul]
    exact hd
  exact ⟨scale, A, C, hscale, hA, hC, hD, hu, ⟨f, hNR⟩,
    square_discriminant_change_basis q (n := 2) c b hdisc,
    quaternion_even_factors q b hD hscale hu f hf⟩

private def artinSchreierConjugation [CharP K 2] (d : K) :
    QuadraticAlgebra K d 1 ≃ₐ[K] QuadraticAlgebra K d 1 := by
  let L := QuadraticAlgebra K d 1
  let f : L →ₐ[K] L :=
    { toFun := star
      map_zero' := star_zero L
      map_one' := star_one L
      map_add' := star_add
      map_mul' := fun x y => (star_mul x y).trans (mul_comm _ _)
      commutes' := fun k => by
        change star (⟨k, 0⟩ : QuadraticAlgebra K d 1) = ⟨k, 0⟩
        rw [QuadraticAlgebra.star_mk, mul_zero, add_zero, neg_zero] }
  have h : f.comp f = AlgHom.id K L := AlgHom.ext fun x => star_star x
  exact AlgEquiv.ofAlgHom f f h h

open private cyclicPairEquiv cyclic_pair_one from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.QuaternionNorm

private theorem symbol_reduced_norm [CharP K 2] (d c : K) (hd : ¬ IsArtinSchreier d)
    (hc : c ≠ 0) (hD : _root_.Specs.RM03.CSA.isCentralSimple K (Symbol K d c))
    (x : Symbol K d c) :
    _root_.Specs.RM03.CSA.reducedNorm hD x = (x * star x).re := by
  let : Fact (∀ s : K, s ^ 2 ≠ d + (1 : K) * s) :=
    ⟨fun s h => hd ⟨s, by rw [h, one_mul, add_assoc, CharTwo.add_self_eq_zero, add_zero]⟩⟩
  let L := QuadraticAlgebra K d 1
  let D := Symbol K d c
  let : Algebra.IsSeparable K L := artin_schreier_separable d
  let σ := artinSchreierConjugation d
  have hσ (x : L) : σ x = ⟨x.re + x.im, -x.im⟩ := by
    change star (⟨x.re, x.im⟩ : QuadraticAlgebra K d 1) = _
    rw [QuadraticAlgebra.star_mk, one_mul]
  have hσne : σ ≠ AlgEquiv.refl := by
    intro h
    have hr := congrArg (fun f : L ≃ₐ[K] L => (f QuadraticAlgebra.omega).re) h
    change (σ QuadraticAlgebra.omega).re = (0 : K) at hr
    rw [hσ] at hr
    change (0 : K) + 1 = 0 at hr
    exact one_ne_zero ((zero_add 1).symm.trans hr)
  obtain ⟨hInv, hred⟩ := Composition.local_quadratic_field_cyclic_reduced_norm
    (B := D) (QuadraticAlgebra.finrank_eq_two d 1) σ hσne c hc
  let p := Composition.QuaternionSpecification.cyclicPair σ hInv c
  let f := cyclicPairEquiv σ hInv c
  let coords : (L × L) ≃ₗ[K] D :=
    { toFun := fun xy => ⟨xy.1.re, xy.1.im, xy.2.re, xy.2.im⟩
      invFun := fun q => (⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let g := f.symm.trans coords
  have hg (x y : L) : g (p x y) = ⟨x.re, x.im, y.re, y.im⟩ := by
    change coords (f.symm (f (x, y))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have h1 : g 1 = 1 := by
    rw [← cyclic_pair_one σ hInv c]
    change g (p 1 0) = 1
    rw [hg]
    rfl
  have hm (a b : Composition.QuaternionSpecification.cyclicAlgebra σ hInv c) :
      g (a * b) = g a * g b := by
    obtain ⟨⟨x, y⟩, rfl⟩ := f.surjective a
    obtain ⟨⟨z, t⟩, rfl⟩ := f.surjective b
    change g (p x y * p z t) = g (p x y) * g (p z t)
    rw [show p x y * p z t = p (x * z + c • (σ t * y)) (t * x + y * σ z) from
      Composition.cyclic_pair_mul σ hInv c x y z t, hg, hg, hg]
    change (_ : QuaternionAlgebra K d 1 c) =
      (⟨x.re, x.im, y.re, y.im⟩ : QuaternionAlgebra K d 1 c) * ⟨z.re, z.im, t.re, t.im⟩
    apply QuaternionAlgebra.ext <;>
      simp [hσ, QuaternionAlgebra.mk_mul_mk, smul_eq_mul] <;> ring
  let e := AlgEquiv.ofLinearEquiv g h1 hm
  have e_apply (a b : L) : e (p a b) = ⟨a.re, a.im, b.re, b.im⟩ := hg a b
  have he := (hred e hD).1 ⟨x.re, x.imI⟩ ⟨x.imJ, x.imK⟩
  change _root_.Specs.RM03.CSA.reducedNorm hD (e (p _ _)) = _ at he
  rw [e_apply] at he
  have hnorm (a : L) : Algebra.norm K a = QuadraticAlgebra.norm a := by
    rw [Algebra.norm_apply]
    exact QuadraticAlgebra.det_toLinearMap_eq_norm a
  rw [symbol_norm]
  simpa only [hnorm] using he

private theorem symplectic4_norm_coordinates [CharP K 2] (q : QuadraticForm K V)
    (b : Basis (Fin 2 ⊕ Fin 2) K V) (hb : IsSymplecticBasis q b)
    (h0 : q (b (.inl 0)) ≠ 0) (h1 : q (b (.inl 1)) ≠ 0) :
    let a := q (b (.inl 0))
    let c := q (b (.inl 1))
    let d := a * q (b (.inr 0))
    let e := c * q (b (.inr 1))
    ∃ f : V ≃ₗ[K] (QuadraticAlgebra K d 1 × QuadraticAlgebra K e 1),
      ∀ x, q x = a * QuadraticAlgebra.norm (f x).1 + c * QuadraticAlgebra.norm (f x).2 := by
  classical
  dsimp only
  let a := q (b (.inl 0))
  let c := q (b (.inl 1))
  let d := a * q (b (.inr 0))
  let e := c * q (b (.inr 1))
  have ha : a ≠ 0 := h0
  have hc : c ≠ 0 := h1
  let L := QuadraticAlgebra K d 1
  let M := QuadraticAlgebra K e 1
  let f : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (L × M) :=
    { toFun := fun x => (⟨x (.inl 0), x (.inr 0) / a⟩, ⟨x (.inl 1), x (.inr 1) / c⟩)
      invFun := fun y => Sum.elim ![y.1.re, y.2.re] ![a * y.1.im, c * y.2.im]
      left_inv := by
        intro x
        funext i
        rcases i with i | i
        · fin_cases i <;> rfl
        · fin_cases i
          · change a * (x (.inr 0) / a) = x (.inr 0)
            rw [← mul_div_assoc, mul_div_cancel_left₀ _ ha]
          · change c * (x (.inr 1) / c) = x (.inr 1)
            rw [← mul_div_assoc, mul_div_cancel_left₀ _ hc]
      right_inv := by
        intro y
        exact Prod.ext (QuadraticAlgebra.ext rfl (mul_div_cancel_left₀ _ ha))
          (QuadraticAlgebra.ext rfl (mul_div_cancel_left₀ _ hc))
      map_add' := by
        intro x y
        exact Prod.ext (QuadraticAlgebra.ext rfl (add_div _ _ _))
          (QuadraticAlgebra.ext rfl (add_div _ _ _))
      map_smul' := by
        intro k x
        exact Prod.ext (QuadraticAlgebra.ext rfl (mul_div_assoc _ _ _))
          (QuadraticAlgebra.ext rfl (mul_div_assoc _ _ _)) }
  let v (i : Fin 2) (s t : K) := s • b (.inl i) + t • b (.inr i)
  have hv (i : Fin 2) (s t : K) :
      q (v i s t) = q (b (.inl i)) * s ^ 2 + s * t + q (b (.inr i)) * t ^ 2 := by
    have hp : q.polarBilin (b (.inl i)) (b (.inr i)) = 1 := by simp [hb.2.2]
    change q (s • b (.inl i) + t • b (.inr i)) = _
    rw [QuadraticMap.map_add q, ← QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.map_smul, QuadraticMap.map_smul, LinearMap.map_smul₂, map_smul, hp]
    simp only [smul_eq_mul]
    ring
  have hcross (s t u v' : K) : q.polarBilin (v 0 s t) (v 1 u v') = 0 := by
    have hp : q.polarBilin (b (.inl 0)) (b (.inr 1)) = 0 := by simp [hb.2.2]
    have hp' : q.polarBilin (b (.inr 0)) (b (.inl 1)) = 0 := by
      rw [polarSymm q]
      simp [hb.2.2]
    simp only [v, LinearMap.add_apply,
      LinearMap.smul_apply, map_add, map_smul, hb.1, hb.2.1, hp, hp',
      add_zero, smul_zero]
  have hdecomp (x : V) : x =
      v 0 (b.repr x (.inl 0)) (b.repr x (.inr 0)) + v 1 (b.repr x (.inl 1)) (b.repr x (.inr 1)) := by
    calc
      x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
      _ = _ := by rw [Fintype.sum_sum_type]; simp only [Fin.sum_univ_two, v]; abel
  have hN (i : Fin 2) (s t : K) (h : q (b (.inl i)) ≠ 0) :
      q (v i s t) = q (b (.inl i)) * QuadraticAlgebra.norm
        (⟨s, t / q (b (.inl i))⟩ : QuadraticAlgebra K (q (b (.inl i)) * q (b (.inr i))) 1) := by
    rw [hv, QuadraticAlgebra.norm_def, CharTwo.sub_eq_add]
    dsimp only
    field_simp
  refine ⟨b.equivFun.trans f, fun x => ?_⟩
  change q x = a * QuadraticAlgebra.norm
    (⟨b.repr x (.inl 0), b.repr x (.inr 0) / a⟩ : L) +
    c * QuadraticAlgebra.norm (⟨b.repr x (.inl 1), b.repr x (.inr 1) / c⟩ : M)
  conv_lhs => rw [hdecomp x]
  rw [QuadraticMap.map_add q, ← QuadraticMap.polarBilin_apply_apply,
    hcross, add_zero, hN 0 _ _ h0, hN 1 _ _ h1]

open private quaternion_isUnit_of_norm_ne_zero from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting

private theorem char_two_quaternion_kernel : CharTwoQuaternionKernel.{u, v} := by
  classical
  intro K _ _ _ _ _ V _ _ q b hb hani
  let a := q (b (.inl 0))
  let t := q (b (.inl 1))
  let d := a * q (b (.inr 0))
  let d' := t * q (b (.inr 1))
  let c := t / a
  let D := Symbol K d c
  let L := QuadraticAlgebra K d 1
  let L' := QuadraticAlgebra K d' 1
  have hnonzero (x : V) (hx : x ≠ 0) : q x ≠ 0 :=
    fun h => hani ⟨x, hx, h⟩
  have ha : a ≠ 0 := hnonzero _ (b.ne_zero _)
  have ht : t ≠ 0 := hnonzero _ (b.ne_zero _)
  have hc : c ≠ 0 := div_ne_zero ht ha
  have hat : a * c = t := by
    change a * (t / a) = t
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ ha]
  obtain ⟨f, hf⟩ := symplectic4_norm_coordinates q b hb ha ht
  have hAn (x : L × L') (hx : x ≠ 0) :
      a * QuadraticAlgebra.norm x.1 + t * QuadraticAlgebra.norm x.2 ≠ 0 := by
    have hx' : f.symm x ≠ 0 := fun h => hx (f.symm.injective (h.trans (map_zero f.symm).symm))
    have hn := hnonzero (f.symm x) hx'
    rw [hf, LinearEquiv.apply_symm_apply] at hn
    exact hn
  have hZeroNorm {z : K} (r : K) (hr : r ^ 2 + r = z) :
      QuadraticAlgebra.norm (⟨r, 1⟩ : QuadraticAlgebra K z 1) = 0 := by
    rw [QuadraticAlgebra.norm_def]
    change r * r + 1 * r * 1 - z * 1 * 1 = 0
    rw [mul_one, one_mul, mul_one, mul_one, ← pow_two, hr, sub_self]
  have hd : ¬ IsArtinSchreier d := by
    rintro ⟨r, hr⟩
    have hx : ((⟨r, 1⟩ : L), (0 : L')) ≠ 0 :=
      fun h => one_ne_zero (congrArg (fun x : L × L' => x.1.im) h)
    exact hAn _ hx (by simp [hZeroNorm r hr])
  have hd' : ¬ IsArtinSchreier d' := by
    rintro ⟨r, hr⟩
    have hx : ((0 : L), (⟨r, 1⟩ : L')) ≠ 0 :=
      fun h => one_ne_zero (congrArg (fun x : L × L' => x.2.im) h)
    exact hAn _ hx (by simp [hZeroNorm r hr])
  have hArf : IsArtinSchreier (d + d') := by
    by_contra hn
    obtain ⟨_, χ, _, _, _, _, hh⟩ := local_norm_groups d hd
    have hj := (hh d' hd' hn).2
    let s := Units.mk0 c hc
    have hs : s ∈ normSubgroup d ⊔ normSubgroup d' := hj.symm ▸ Subgroup.mem_top _
    obtain ⟨x, hx, y, hy, he⟩ := Subgroup.mem_sup.mp hs
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := (normSubgroup d').inv_mem hy
    have hU : QuadraticAlgebra.norm (↑u : L) = (x : K) := congrArg Units.val hu
    have hV : QuadraticAlgebra.norm (↑v : L') = ↑y⁻¹ := congrArg Units.val hv
    have hxy : (x : K) * y = c := congrArg Units.val he
    have huv : a * (x : K) = t * (↑y⁻¹ : K) := by
      apply y.isUnit.mul_right_cancel
      rw [mul_assoc, hxy]
      rw [hat, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
    have huvne : ((↑u : L), (↑v : L')) ≠ 0 := fun h =>
      u.ne_zero (congrArg Prod.fst h)
    exact hAn _ huvne (by rw [hU, hV, huv, CharTwo.add_self_eq_zero])
  obtain ⟨r, hr⟩ := hArf
  have hd'rel : d' = d + (r ^ 2 + r) := by
    rw [hr, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  let shift : L' ≃ₗ[K] L :=
    { toFun := fun x => ⟨x.re + r * x.im, x.im⟩
      invFun := fun x => ⟨x.re - r * x.im, x.im⟩
      left_inv := fun x => QuadraticAlgebra.ext (add_sub_cancel_right _ _) rfl
      right_inv := fun x => QuadraticAlgebra.ext (sub_add_cancel _ _) rfl
      map_add' := fun x y => QuadraticAlgebra.ext (by
        change x.re + y.re + r * (x.im + y.im) =
          x.re + r * x.im + (y.re + r * y.im)
        ring) rfl
      map_smul' := fun k x => QuadraticAlgebra.ext (by
        change k * x.re + r * (k * x.im) = k * (x.re + r * x.im)
        ring) rfl }
  have hshift (x : L') : QuadraticAlgebra.norm (shift x) = QuadraticAlgebra.norm x := by
    rw [QuadraticAlgebra.norm_def, QuadraticAlgebra.norm_def]
    change (x.re + r * x.im) * (x.re + r * x.im) + 1 * (x.re + r * x.im) * x.im -
      d * x.im * x.im = x.re * x.re + 1 * x.re * x.im - d' * x.im * x.im
    simp only [CharTwo.sub_eq_add, hd'rel]
    ring_nf
    simp [CharTwo.two_eq_zero]
  let coords : (L × L) ≃ₗ[K] D :=
    { toFun := fun x => ⟨x.1.re, x.1.im, x.2.re, x.2.im⟩
      invFun := fun x => (⟨x.re, x.imI⟩, ⟨x.imJ, x.imK⟩)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e := (f.trans ((LinearEquiv.refl K L).prodCongr shift)).trans coords
  have hNorm (x : V) : q x = a * (e x * star (e x)).re := by
    rw [hf, symbol_norm]
    change a * QuadraticAlgebra.norm (f x).1 + t * QuadraticAlgebra.norm (f x).2 =
      a * (QuadraticAlgebra.norm (f x).1 - c * QuadraticAlgebra.norm (shift (f x).2))
    rw [hshift, CharTwo.sub_eq_add, mul_add, ← mul_assoc, hat]
  have hD : _root_.Specs.RM03.CSA.isCentralSimple K D :=
    symbol_central_simple d (Units.mk0 c hc)
  have hunit (x : D) (hx : x ≠ 0) : IsUnit x := by
    apply quaternion_isUnit_of_norm_ne_zero
    intro hn
    have hx' : e.symm x ≠ 0 := fun h => hx (e.symm.injective (h.trans (map_zero e.symm).symm))
    have h := hnonzero (e.symm x) hx'
    rw [hNorm, e.apply_symm_apply, hn, mul_zero] at h
    exact h rfl
  have hArf' : IsArtinSchreier (arf q b) := ⟨r, by simpa [arf, Fin.sum_univ_two, d, d', a, t] using hr⟩
  refine ⟨ha, hc, hd, hArf', hD, hunit, ⟨e, fun x => ?_⟩, ?_⟩
  · rw [symbol_reduced_norm d c hd hc hD]
    exact hNorm x
  · exact quaternion_even_factors q (b.reindex finSumFinEquiv) hD ha hunit e hNorm

end QuaternionKernels

section HyperbolicStabilization

open CliffordAlgebra Module
open _root_.LinearAlgebraicGroups.Albert
open scoped Matrix

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

private abbrev HyperbolicPlane (K : Type u) :=
  Indices (ULift.{u} (Fin 1)) → K

private def planeLeft : HyperbolicPlane K := Sum.elim (fun _ => 1) (fun _ => 0)
private def planeRight : HyperbolicPlane K := Sum.elim (fun _ => 0) (fun _ => 1)

private theorem hyperbolic_one_apply (x : HyperbolicPlane K) :
    hyperbolic K 1 x = x (.inl ⟨0⟩) * x (.inr ⟨0⟩) := by
  rw [OddSpinModels.hyperbolicForm_apply, Fintype.sum_unique]
  congr

private theorem clifford_finrank [FiniteDimensional K V] (q : QuadraticForm K V) :
    finrank K (CliffordAlgebra q) = 2 ^ finrank K V := by
  obtain ⟨B, _⟩ := CliffordModel.ordered_basis q (Module.finBasis K V)
  rw [Module.finrank_eq_card_basis B, Fintype.card_finset, Fintype.card_fin]

private theorem plane_matrix [FiniteDimensional K V] (q : QuadraticForm K V) :
    ∃ e : CliffordAlgebra (q.prod (hyperbolic K 1)) ≃ₐ[K]
        Matrix (Fin 2) (Fin 2) (CliffordAlgebra q),
      ∀ x : V × HyperbolicPlane K, e (ι _ x) =
        !![ι q x.1, algebraMap K _ (x.2 (.inl ⟨0⟩));
          algebraMap K _ (x.2 (.inr ⟨0⟩)), -ι q x.1] := by
  let C := CliffordAlgebra q
  let Q := q.prod (hyperbolic K 1)
  let op : V × HyperbolicPlane K →ₗ[K] Matrix (Fin 2) (Fin 2) C :=
    { toFun := fun x =>
        !![ι q x.1, algebraMap K C (x.2 (.inl ⟨0⟩));
          algebraMap K C (x.2 (.inr ⟨0⟩)), -ι q x.1]
      map_add' := by
        intro x y
        ext i j
        fin_cases i <;> fin_cases j <;> simp [add_comm]
      map_smul' := by
        intro k x
        ext i j
        fin_cases i <;> fin_cases j <;> simp [C, Algebra.smul_def] }
  have hsq (x : V × HyperbolicPlane K) : op x * op x = algebraMap K _ (Q x) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [op, C, Q, QuadraticMap.prod_apply, hyperbolic_one_apply, Matrix.mul_apply,
        Matrix.algebraMap_matrix_apply, Fin.sum_univ_two, neg_mul,
        Algebra.commutes, mul_comm (x.2 (.inl ⟨0⟩)), ← map_mul, add_comm]
  let f := CliffordAlgebra.lift Q ⟨op, hsq⟩
  have hf (x : V × HyperbolicPlane K) : f (ι Q x) = op x :=
    CliffordAlgebra.lift_ι_apply _ _ _
  let inc : CliffordAlgebra q →ₐ[K] CliffordAlgebra Q :=
    CliffordAlgebra.map (QuadraticMap.Isometry.inl q (hyperbolic K 1))
  have hentry (z : C) :
      f (inc z) 0 0 = z ∧ f (inc z) 0 1 = 0 ∧ f (inc z) 1 0 = 0 := by
    induction z using CliffordAlgebra.induction with
    | algebraMap r => simp [C, AlgHom.commutes, Matrix.algebraMap_matrix_apply]
    | ι x =>
      change f (CliffordAlgebra.map (QuadraticMap.Isometry.inl q (hyperbolic K 1))
        (ι q x)) 0 0 = ι q x ∧ _ ∧ _
      have he : inc (ι q x) = ι Q (x, 0) :=
        CliffordAlgebra.map_apply_ι _ _
      rw [← show inc = CliffordAlgebra.map (QuadraticMap.Isometry.inl q (hyperbolic K 1)) from rfl,
        he, hf]
      simp [op]
    | mul x y hx hy =>
      simp [map_mul, Matrix.mul_apply, Fin.sum_univ_two, hx.1, hx.2.1, hx.2.2,
        hy.1, hy.2.1, hy.2.2]
    | add x y hx hy => simp [hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2]
  have h01 : Matrix.single 0 1 (1 : C) ∈ f.range := by
    refine ⟨ι Q (0, planeLeft), ?_⟩
    change f (ι Q (0, planeLeft)) = _
    rw [hf]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [op, Matrix.single, planeLeft]
  have h10 : Matrix.single 1 0 (1 : C) ∈ f.range := by
    refine ⟨ι Q (0, planeRight), ?_⟩
    change f (ι Q (0, planeRight)) = _
    rw [hf]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [op, Matrix.single, planeRight]
  have h00 : Matrix.single 0 0 (1 : C) ∈ f.range := by
    simpa only [Matrix.single_mul_single_same, mul_one] using f.range.mul_mem h01 h10
  have hsingle (i j : Fin 2) (z : C) : Matrix.single i j z ∈ f.range := by
    have h_i : Matrix.single i 0 (1 : C) ∈ f.range := by fin_cases i <;> assumption
    have h_j : Matrix.single 0 j (1 : C) ∈ f.range := by fin_cases j <;> assumption
    have h := f.range.mul_mem (f.range.mul_mem h_i (show f (inc z) ∈ f.range from ⟨inc z, rfl⟩)) h_j
    rwa [Matrix.single_mul_mul_single, one_mul, mul_one, (hentry z).1] at h
  have hsurj : Function.Surjective f := by
    intro m
    change m ∈ f.range
    exact (Matrix.matrix_eq_sum_single m).symm ▸
      f.range.sum_mem (fun i _ => f.range.sum_mem fun j _ => hsingle i j (m i j))
  obtain ⟨B, _⟩ := CliffordModel.ordered_basis Q (Module.finBasis K (V × HyperbolicPlane K))
  let : FiniteDimensional K (CliffordAlgebra Q) := Module.Finite.of_basis B
  have hdim : finrank K (CliffordAlgebra Q) =
      finrank K (Matrix (Fin 2) (Fin 2) C) := by
    have hp : finrank K (HyperbolicPlane K) = 2 := by
      simp [HyperbolicPlane, Module.finrank_fintype_fun_eq_card]
    rw [clifford_finrank, Module.finrank_prod, hp, pow_add, Module.finrank_matrix, Fintype.card_fin]
    change 2 ^ finrank K V * 2 ^ 2 = 2 * 2 * finrank K (CliffordAlgebra q)
    rw [clifford_finrank, mul_comm]
    rfl
  have htop : f.toLinearMap.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdim' := f.toLinearMap.finrank_range_add_finrank_ker
  rw [htop, finrank_top, ← hdim] at hdim'
  have hker : finrank K f.toLinearMap.ker = 0 := by omega
  have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)
  exact ⟨AlgEquiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

private def MatrixHasGrade (q : QuadraticForm K V) (k : ZMod 2)
    (m : Matrix (Fin 2) (Fin 2) (CliffordAlgebra q)) : Prop :=
  ∀ i j, m i j ∈ evenOdd q (k + (i.val : ZMod 2) + (j.val : ZMod 2))

private theorem matrix_grade_mul {q : QuadraticForm K V} {k l : ZMod 2}
    {a b : Matrix (Fin 2) (Fin 2) (CliffordAlgebra q)}
    (ha : MatrixHasGrade q k a) (hb : MatrixHasGrade q l b) :
    MatrixHasGrade q (k + l) (a * b) := by
  intro i j
  rw [Matrix.mul_apply]
  apply Submodule.sum_mem
  intro t _
  have h := SetLike.mul_mem_graded (ha i t) (hb t j)
  have hg : (k + (i.val : ZMod 2) + (t.val : ZMod 2)) +
      (l + (t.val : ZMod 2) + (j.val : ZMod 2)) =
      (k + l) + (i.val : ZMod 2) + (j.val : ZMod 2) := by
    calc
      _ = ((k + l) + (i.val : ZMod 2) + (j.val : ZMod 2)) +
          ((t.val : ZMod 2) + (t.val : ZMod 2)) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
  rwa [hg] at h

private theorem plane_matrix_grade (q : QuadraticForm K V)
    (E : CliffordAlgebra (q.prod (hyperbolic K 1)) ≃ₐ[K] Matrix (Fin 2) (Fin 2) (CliffordAlgebra q))
    (hE : ∀ x : V × HyperbolicPlane K, E (ι _ x) =
      !![ι q x.1, algebraMap K _ (x.2 (.inl ⟨0⟩));
        algebraMap K _ (x.2 (.inr ⟨0⟩)), -ι q x.1])
    {k : ZMod 2} {z : CliffordAlgebra (q.prod (hyperbolic K 1))}
    (hz : z ∈ evenOdd (q.prod (hyperbolic K 1)) k) : MatrixHasGrade q k (E z) := by
  have h0 (r : K) : MatrixHasGrade q 0 (algebraMap K _ r) := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [zero_add, CharTwo.add_self_eq_zero, Matrix.algebraMap_matrix_apply, ite_eq_left rfl]
      exact SetLike.algebraMap_mem_graded _ _
    · rw [Matrix.algebraMap_matrix_apply, ite_eq_right hij]
      exact Submodule.zero_mem _
  have h1 (x : V × HyperbolicPlane K) : MatrixHasGrade q 1 (E (ι _ x)) := by
    intro i j
    rw [hE]
    fin_cases i <;> fin_cases j
    · exact ι_mem_evenOdd_one q x.1
    · change algebraMap K (CliffordAlgebra q) (x.2 (.inl ⟨0⟩)) ∈ evenOdd q (1 + 0 + 1)
      rw [show (1 + 0 + 1 : ZMod 2) = 0 by decide]
      exact SetLike.algebraMap_mem_graded _ _
    · change algebraMap K (CliffordAlgebra q) (x.2 (.inr ⟨0⟩)) ∈ evenOdd q (1 + 1 + 0)
      rw [show (1 + 1 + 0 : ZMod 2) = 0 by decide]
      exact SetLike.algebraMap_mem_graded _ _
    · exact Submodule.neg_mem _ (ι_mem_evenOdd_one q x.1)
  have hadd {j : ZMod 2} {x y : CliffordAlgebra (q.prod (hyperbolic K 1))}
      (hx : MatrixHasGrade q j (E x)) (hy : MatrixHasGrade q j (E y)) :
      MatrixHasGrade q j (E (x + y)) := by
    intro i t
    rw [map_add, Matrix.add_apply]
    exact Submodule.add_mem _ (hx i t) (hy i t)
  have hpair {j : ZMod 2} (a b : V × HyperbolicPlane K)
      {w : CliffordAlgebra (q.prod (hyperbolic K 1))}
      (hw : MatrixHasGrade q j (E w)) : MatrixHasGrade q j (E (ι _ a * ι _ b * w)) := by
    rw [map_mul, map_mul]
    have h := matrix_grade_mul (matrix_grade_mul (h1 a) (h1 b)) hw
    simpa only [show (1 + 1 : ZMod 2) = 0 by decide, zero_add] using h
  fin_cases k
  · induction z, hz using CliffordAlgebra.even_induction with
    | algebraMap r => exact (E.commutes r).symm ▸ h0 r
    | add _ _ _ _ hx hy => exact hadd hx hy
    | ι_mul_ι_mul a b _ _ ih => exact hpair a b ih
  · induction z, hz using CliffordAlgebra.odd_induction with
    | ι a => exact h1 a
    | add _ _ _ _ hx hy => exact hadd hx hy
    | ι_mul_ι_mul a b _ _ ih => exact hpair a b ih

private theorem plane_matrix_even_mem (q : QuadraticForm K V)
    (E : CliffordAlgebra (q.prod (hyperbolic K 1)) ≃ₐ[K] Matrix (Fin 2) (Fin 2) (CliffordAlgebra q))
    (hE : ∀ x : V × HyperbolicPlane K, E (ι _ x) =
      !![ι q x.1, algebraMap K _ (x.2 (.inl ⟨0⟩));
        algebraMap K _ (x.2 (.inr ⟨0⟩)), -ι q x.1])
    {m : Matrix (Fin 2) (Fin 2) (CliffordAlgebra q)}
    (hm : MatrixHasGrade q 0 m) :
    E.symm m ∈ evenOdd (q.prod (hyperbolic K 1)) 0 := by
  let Q := q.prod (hyperbolic K 1)
  have hs := (evenOdd_isCompl Q).sup_eq_top
  have hmem : E.symm m ∈ evenOdd Q 0 ⊔ evenOdd Q 1 := hs.symm ▸ Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hmem
  have hxy' : E x + E y = m := by rw [← map_add, hxy, E.apply_symm_apply]
  have hx' := plane_matrix_grade q E hE hx
  have hy' := plane_matrix_grade q E hE hy
  have hy0 (i j : Fin 2) : E y i j = 0 := by
    have he : E y i j = m i j - E x i j := by
      have h := congrArg (fun n : Matrix (Fin 2) (Fin 2) (CliffordAlgebra q) => n i j) hxy'
      exact eq_sub_of_add_eq ((add_comm (E y i j) _).trans h)
    have hy'' := he.symm ▸ (evenOdd q _).sub_mem (hm i j) (hx' i j)
    have hneg {a : ZMod 2} {z : CliffordAlgebra q}
        (h : z ∈ evenOdd q a) (h' : z ∈ evenOdd q (1 + a)) : z = 0 := by
      fin_cases a
      · exact Submodule.disjoint_def.mp (evenOdd_isCompl q).disjoint z h h'
      · exact Submodule.disjoint_def.mp (evenOdd_isCompl q).disjoint z h' h
    apply hneg hy''
    simpa only [zero_add, add_assoc] using hy' i j
  have h := E.injective (show E y = E 0 from by
    ext i j
    rw [hy0, map_zero, Matrix.zero_apply])
  rwa [← hxy, h, add_zero]

private theorem even_plane_matrix [FiniteDimensional K V] (q : QuadraticForm K V)
    {x : V} (hx : q x ≠ 0) :
    Nonempty (CliffordAlgebra.even (q.prod (hyperbolic K 1)) ≃ₐ[K]
      Matrix (Fin 2) (Fin 2) (CliffordAlgebra.even q)) := by
  let C := CliffordAlgebra q
  let Q := q.prod (hyperbolic K 1)
  let M := Matrix (Fin 2) (Fin 2) C
  obtain ⟨E, hE⟩ := plane_matrix q
  let a : Cˣ := (isUnit_ι_of_isUnit q hx.isUnit).unit
  have ha : (a : C) = ι q x := (isUnit_ι_of_isUnit q hx.isUnit).unit_spec
  have hai : (↑a⁻¹ : C) = (q x)⁻¹ • ι q x := by
    apply a.isUnit.mul_right_cancel
    rw [Units.inv_mul, ha, smul_mul_assoc, ι_sq_scalar, Algebra.smul_def, ← map_mul,
      inv_mul_cancel₀ hx, map_one]
  let r : Fin 2 → Cˣ := ![1, a]
  have hr (i : Fin 2) : (r i : C) ∈ evenOdd q (i.val : ZMod 2) := by
    fin_cases i
    · change (1 : C) ∈ evenOdd q 0
      exact SetLike.one_mem_graded _
    · change (a : C) ∈ evenOdd q 1
      rw [ha]
      exact ι_mem_evenOdd_one q x
  have hri (i : Fin 2) : (↑(r i)⁻¹ : C) ∈ evenOdd q (i.val : ZMod 2) := by
    fin_cases i
    · change (1 : C) ∈ evenOdd q 0
      exact SetLike.one_mem_graded _
    · change (↑a⁻¹ : C) ∈ evenOdd q 1
      rw [hai]
      exact Submodule.smul_mem _ _ (ι_mem_evenOdd_one q x)
  let u : (Fin 2 → C)ˣ :=
    ⟨fun i => r i, fun i => (↑(r i)⁻¹ : C),
      funext fun i => (r i).mul_inv, funext fun i => (r i).inv_mul⟩
  let U : Mˣ := Units.map (Matrix.diagonalAlgHom K).toMonoidHom u
  let T := conjugation (K := K) U
  let Ti := conjugation (K := K) U⁻¹
  have hT (m : M) (i j : Fin 2) :
      T m i j = (↑(r i)⁻¹ : C) * m i j * ↑(r j) := by
    change ((Matrix.diagonal (fun i => (↑(r i)⁻¹ : C)) * m) *
        Matrix.diagonal (fun i => (r i : C))) i j = _
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hTi (m : M) (i j : Fin 2) :
      Ti m i j = ↑(r i) * m i j * (↑(r j)⁻¹ : C) := by
    change (((↑(U⁻¹)⁻¹ : M) * m) * (↑U⁻¹ : M)) i j = _
    rw [inv_inv]
    change ((Matrix.diagonal (fun i => (r i : C)) * m) *
        Matrix.diagonal (fun i => (↑(r i)⁻¹ : C))) i j = _
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hTTi (m : M) : T (Ti m) = m := by
    change (↑U⁻¹ : M) * ((U : M) * m * ↑U⁻¹) * U = _
    simp only [mul_assoc, U.inv_mul_cancel_left, Units.inv_mul, mul_one]
  have hTiT (m : M) : Ti (T m) = m := by
    change (↑(U⁻¹)⁻¹ : M) * ((↑U⁻¹ : M) * m * ↑U) * ↑U⁻¹ = _
    rw [inv_inv]
    simp only [mul_assoc, U.mul_inv_cancel_left, Units.mul_inv, mul_one]
  let enc : Matrix (Fin 2) (Fin 2) (even q) →ₐ[K] M := (even q).val.mapMatrix
  have henc (m : Matrix (Fin 2) (Fin 2) (even q)) (i j : Fin 2) :
      enc m i j = (m i j).val := rfl
  have henc_inj : Function.Injective enc := by
    intro m n h
    apply Matrix.ext
    intro i j
    exact Subtype.ext (congrArg (fun x : M => x i j) h)
  have hTeven (m : M) (hm : MatrixHasGrade q 0 m) (i j : Fin 2) : T m i j ∈ evenOdd q 0 := by
    rw [hT]
    have he := SetLike.mul_mem_graded (SetLike.mul_mem_graded (hri i) (hm i j)) (hr j)
    have h₂ : ((i.val : ZMod 2) + (0 + (i.val : ZMod 2) + (j.val : ZMod 2))) +
        (j.val : ZMod 2) = 0 := by
      have h₃ : ((i.val : ZMod 2) + (0 + (i.val : ZMod 2) + (j.val : ZMod 2))) +
        (j.val : ZMod 2) = ((i.val : ZMod 2) + (i.val : ZMod 2)) +
        ((j.val : ZMod 2) + (j.val : ZMod 2)) := by abel
      rw [h₃, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
    rwa [h₂] at he
  have hTif (m : Matrix (Fin 2) (Fin 2) (even q)) : MatrixHasGrade q 0 (Ti (enc m)) := by
    intro i j
    rw [hTi, henc]
    simpa only [add_zero, zero_add] using
      SetLike.mul_mem_graded (SetLike.mul_mem_graded (hr i) (m i j).property) (hri j)
  let f : even Q →ₐ[K] M := T.comp (E.toAlgHom.comp (even Q).val)
  have hf (m : even Q) : f m ∈ enc.range := by
    have h := plane_matrix_grade q E hE m.property
    exact ⟨Matrix.of fun i j => ⟨f m i j, hTeven _ h i j⟩, rfl⟩
  let G := AlgEquiv.ofInjective enc henc_inj
  let g := G.symm.toAlgHom.comp (f.codRestrict enc.range hf)
  have hg (m : even Q) : enc (g m) = f m := by
    have h := congrArg Subtype.val (G.apply_symm_apply (f.codRestrict enc.range hf m))
    exact h
  have hgi : Function.Injective g := by
    intro m n h
    apply Subtype.ext
    apply E.injective
    have h' := congrArg enc h
    rw [hg, hg] at h'
    have h'' := congrArg Ti h'
    change Ti (T (E m.val)) = Ti (T (E n.val)) at h''
    simpa only [hTiT] using h''
  have hgs : Function.Surjective g := by
    intro m
    let n := E.symm (Ti (enc m))
    have hn : n ∈ evenOdd Q 0 := plane_matrix_even_mem q E hE (hTif m)
    refine ⟨⟨n, hn⟩, henc_inj ?_⟩
    rw [hg]
    change T (E (E.symm (Ti (enc m)))) = enc m
    rw [E.apply_symm_apply, hTTi]
  exact ⟨AlgEquiv.ofBijective g ⟨hgi, hgs⟩⟩

private noncomputable def matrixCSA (A : _root_.CSA.{u, v} K) : _root_.CSA.{u, max u v} K := by
  let R := Matrix (Fin 2) (Fin 2) A
  let S := ULift.{u} R
  let e : S ≃ₐ[K] R := ULift.algEquiv
  have h : _root_.Specs.RM03.CSA.isCentralSimple K S := by
    refine ⟨IsSimpleRing.of_ringEquiv e.symm.toRingEquiv inferInstance, ⟨fun x hx => ?_⟩,
      FiniteDimensional.of_injective e.toLinearMap e.injective⟩
    have hxe : e x ∈ Subalgebra.center K R := (MulEquivClass.apply_mem_center_iff e).mpr hx
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hxe)
    exact Algebra.mem_bot.mpr ⟨c, e.injective ((e.commutes c).trans hc)⟩
  exact _root_.Specs.RM03.CSA.toCSA h

private noncomputable def matrixProd {A B : Type v} [Ring A] [Ring B] [Algebra K A] [Algebra K B] :
    Matrix (Fin 2) (Fin 2) (A × B) ≃ₐ[K] Matrix (Fin 2) (Fin 2) A × Matrix (Fin 2) (Fin 2) B := by
  let f := (AlgHom.fst K A B).mapMatrix (m := Fin 2)
  let g := (AlgHom.snd K A B).mapMatrix (m := Fin 2)
  apply AlgEquiv.ofBijective (f.prod g)
  constructor
  · intro a b h
    apply Matrix.ext
    intro i j
    exact Prod.ext (congrArg (fun x => x.1 i j) h) (congrArg (fun x => x.2 i j) h)
  · rintro ⟨a, b⟩
    exact ⟨Matrix.of fun i j => (a i j, b i j), rfl⟩

open private equivalent_of_matrix_presentation from
  MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.Equivalence

private theorem hyperbolic_clifford_factors : HyperbolicCliffordFactors.{u, v} := by
  intro K _ V _ _ _ q hq _ A B ⟨f⟩
  have hx : ∃ x : V, q x ≠ 0 := by
    by_contra hn
    have hz : q = 0 := QuadraticMap.ext fun x => not_not.mp (fun h => hn ⟨x, h⟩)
    have hv (x : V) : x = 0 := by
      apply LinearMap.ker_eq_bot'.mp hq
      ext y
      simp [hz, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
    let z : even q := f.symm (1, 0)
    obtain ⟨a, ha⟩ := even_scalar_of_commutes q (Module.finBasis K V) hq z.val z.property
      (fun x => by rw [hv x, map_zero]; exact Commute.zero_left _)
    have ha' : z = algebraMap K (even q) a := Subtype.ext ha
    have h : ((1 : A), (0 : B)) = algebraMap K (A × B) a :=
      (f.apply_symm_apply _).symm.trans ((congrArg f ha').trans (f.commutes a))
    have hb : a = 0 := (algebraMap K B).injective (by simpa using (congrArg Prod.snd h).symm)
    rw [hb, map_zero] at h
    exact one_ne_zero (congrArg Prod.fst h)
  obtain ⟨x, hx⟩ := hx
  obtain ⟨e⟩ := even_plane_matrix q hx
  let A' := matrixCSA A
  let B' := matrixCSA B
  let a : A' ≃ₐ[K] Matrix (Fin 2) (Fin 2) A := ULift.algEquiv
  let b : B' ≃ₐ[K] Matrix (Fin 2) (Fin 2) B := ULift.algEquiv
  refine ⟨A', B', ⟨e.trans (f.mapMatrix.trans (matrixProd.trans (AlgEquiv.prodCongr a.symm b.symm)))⟩, ?_, ?_⟩
  · exact equivalent_of_matrix_presentation (by decide : 0 < 2) a
  · exact equivalent_of_matrix_presentation (by decide : 0 < 2) b

end HyperbolicStabilization

private theorem galois_of_trivial_residual_action
    {F E S : Type u} [Field F] [Field E] [Field S] [Algebra F E] [Algebra F S]
    [Algebra E S] [IsScalarTower F E S] [Algebra.IsSeparable F E] [IsSepClosure F S]
    (h : ResidualActionTrivial F E S) : IsGalois F E := by
  let : Algebra.IsSeparable E S := Algebra.isSeparable_tower_top_of_isSeparable F E S
  let : IsSepClosure E S := ⟨IsSepClosure.sep_closed F, inferInstance⟩
  let i : E →ₐ[F] S := vectorEmbedding
  let E' := i.fieldRange
  let e : E ≃ₐ[F] E' := i.equivFieldRange
  let : Normal F E' := IntermediateField.normal_iff_forall_fieldRange_le.mpr (by
    intro f s hs
    obtain ⟨x, rfl⟩ := hs
    obtain ⟨y, rfl⟩ := e.surjective x
    change f (e y) ∈ E'
    have hfix (σ : Gal(S/E)) : σ (f (e y)) = f (e y) :=
      DFunLike.congr_fun (h σ (f.comp e.toAlgHom)) y
    have hem := (InfiniteGalois.mem_range_algebraMap_iff_fixed (f (e y))).mpr hfix
    obtain ⟨z, hz⟩ := hem
    exact ⟨z, hz⟩)
  exact isGalois_iff.mpr ⟨inferInstance, Normal.of_algEquiv e.symm⟩


section PeirceDescent

open LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescentSpecification
open LinearAlgebraicGroups.Albert LinearAlgebraicGroups.Composition
open scoped TensorProduct

variable {F E S : Type u} [Field F] [Field E] [Field S]
  [Algebra F E] [Algebra F S]
variable (numbering : (E →ₐ[F] S) ≃ Fin 3)

private noncomputable def diagonalEvaluation : S ⊗[F] E →ₐ[S] (Fin 3 → S) :=
  AlgHom.pi (fun i => Algebra.TensorProduct.lift (AlgHom.id S S) (numbering.symm i)
    (fun _ _ => Commute.all _ _))

private theorem diagonalEvaluation_tmul (s : S) (a : E) (i : Fin 3) :
    diagonalEvaluation numbering (s ⊗ₜ[F] a) i = s * (numbering.symm i) a := by
  rw [diagonalEvaluation, AlgHom.pi_apply, Algebra.TensorProduct.lift_tmul]
  rfl

private theorem diagonalEvaluation_surjective : Function.Surjective (diagonalEvaluation numbering) := by
  classical
  let d := diagonalEvaluation numbering
  have axis (i : Fin 3) : Pi.single i (1 : S) ∈ d.toLinearMap.range := by
    have hsep (j : {j : Fin 3 // j ≠ i}) :
        ∃ a : E, (numbering.symm i) a ≠ (numbering.symm j.val) a := by
      by_contra! h
      exact j.property ((numbering.symm.injective (AlgHom.ext h)).symm)
    choose a ha using hsep
    let b (j : {j : Fin 3 // j ≠ i}) : S ⊗[F] E :=
      (((numbering.symm i) (a j) - (numbering.symm j.val) (a j))⁻¹ ⊗ₜ[F] (1 : E)) *
        ((1 : S) ⊗ₜ[F] a j - (numbering.symm j.val) (a j) ⊗ₜ[F] (1 : E))
    have hb (j : {j : Fin 3 // j ≠ i}) (k : Fin 3) :
        d (b j) k = ((numbering.symm i) (a j) - (numbering.symm j.val) (a j))⁻¹ *
          ((numbering.symm k) (a j) - (numbering.symm j.val) (a j)) := by
      dsimp only [d, b]
      rw [map_mul, Pi.mul_apply, diagonalEvaluation_tmul, map_sub, Pi.sub_apply,
        diagonalEvaluation_tmul, diagonalEvaluation_tmul]
      simp
    refine ⟨∏ j, b j, ?_⟩
    change d (∏ j, b j) = _
    funext k
    rw [map_prod, Finset.prod_apply]
    by_cases hki : k = i
    · subst k
      rw [Pi.single_eq_same]
      exact Finset.prod_eq_one (fun j _ => by rw [hb, inv_mul_cancel₀ (sub_ne_zero.mpr (ha j))])
    · rw [Pi.single_eq_of_ne hki]
      exact Finset.prod_eq_zero (Finset.mem_univ (⟨k, hki⟩ : {j : Fin 3 // j ≠ i}))
        (by rw [hb, sub_self, mul_zero])
  intro x
  have hx : x ∈ d.toLinearMap.range := by
    rw [← (Module.Basis.sum_repr (Pi.basisFun S (Fin 3)) x)]
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)
    rw [Pi.basisFun_apply]
    exact axis i
  exact hx

variable {numbering}
variable {J : AlbertModel F} (B : CubicStabilizer J E)
  (t : S ⊗[F] J.V ≃ₗ[S] TrialitySpecification.Model S)

private theorem diagonalCoordinates_baseChange
    (ht : ∀ e : E, t (1 ⊗ₜ[F] B.diagonal e) = (fun i => numbering.symm i e, 0))
    (x : S ⊗[F] E) :
    t (B.diagonal.baseChange S x) = (diagonalEvaluation numbering x, 0) := by
  induction x using TensorProduct.inductionOn
  case tmul s e =>
    rw [LinearMap.baseChange_tmul, show s ⊗ₜ[F] B.diagonal e = s • ((1 : S) ⊗ₜ[F] B.diagonal e) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      map_smul, ht]
    apply Prod.ext
    · funext i
      exact (diagonalEvaluation_tmul numbering s e i).symm
    · simp
  case add x y hx hy => simp [hx, hy]

private theorem diagonalEvaluation_galois (σ : Gal(S/F)) (x : S ⊗[F] E) (e : E →ₐ[F] S) :
    diagonalEvaluation numbering (σ.toAlgHom.toLinearMap.rTensor E x)
      (numbering (σ.toAlgHom.comp e)) =
        σ (diagonalEvaluation numbering x (numbering e)) := by
  induction x using TensorProduct.inductionOn
  case tmul s b =>
    rw [LinearMap.rTensor_tmul, diagonalEvaluation_tmul, diagonalEvaluation_tmul,
      numbering.symm_apply_apply, numbering.symm_apply_apply, map_mul]
    rfl
  case add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]


private def embeddingPermutation (σ : Gal(S/F)) : Equiv.Perm (E →ₐ[F] S) where
  toFun e := σ.toAlgHom.comp e
  invFun e := σ.symm.toAlgHom.comp e
  left_inv e := AlgHom.ext fun x => σ.symm_apply_apply (e x)
  right_inv e := AlgHom.ext fun x => σ.apply_symm_apply (e x)

private def vertexPermutation (σ : Gal(S/F)) : Equiv.Perm (Fin 3) :=
  (numbering.symm.trans (embeddingPermutation σ)).trans numbering

private def modelCoefficientAction (σ : Gal(S/F)) (x : TrialitySpecification.Model S) :
    TrialitySpecification.Model S :=
  t (σ.toAlgHom.toLinearMap.rTensor J.V (t.symm x))

private theorem modelCoefficientAction_injective (σ : Gal(S/F)) :
    Function.Injective (modelCoefficientAction t σ) :=
  t.injective.comp ((TensorProduct.congr σ.toLinearEquiv (LinearEquiv.refl F J.V)).injective.comp
    t.symm.injective)

open QuadraticOperatorSpecification (triple)
open TrialitySpecification (Model modelOp)
open Composition.ZornSpecification (norm)

private theorem modelCoefficientAction_axis (σ : Gal(S/F))
    (hdiag : ∀ e : E, t (1 ⊗ₜ[F] B.diagonal e) = (fun i => numbering.symm i e, 0))
    (i : Fin 3) :
    modelCoefficientAction t σ (frameAxis i) =
      frameAxis (vertexPermutation (numbering := numbering) σ i) := by
  obtain ⟨x, hx⟩ := diagonalEvaluation_surjective numbering (Pi.single i 1)
  have hframe : t (B.diagonal.baseChange S x) = frameAxis i := by
    rw [diagonalCoordinates_baseChange B t hdiag, hx]
    rfl
  have hcomm (y : S ⊗[F] E) : σ.toAlgHom.toLinearMap.rTensor J.V (B.diagonal.baseChange S y) =
      B.diagonal.baseChange S (σ.toAlgHom.toLinearMap.rTensor E y) := by
    induction y using TensorProduct.inductionOn with
    | tmul s e => simp only [LinearMap.rTensor_tmul, LinearMap.baseChange_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [← hframe]
  change t (σ.toAlgHom.toLinearMap.rTensor J.V (t.symm (t (B.diagonal.baseChange S x)))) = _
  rw [LinearEquiv.symm_apply_apply, hcomm, diagonalCoordinates_baseChange B t hdiag]
  refine Prod.ext ?_ rfl
  funext k
  let π := vertexPermutation (numbering := numbering) σ
  obtain ⟨j, rfl⟩ := π.surjective k
  have h := diagonalEvaluation_galois (numbering := numbering) σ x (numbering.symm j)
  rw [numbering.apply_symm_apply, hx] at h
  change diagonalEvaluation numbering (σ.toAlgHom.toLinearMap.rTensor E x) (π j) =
    (Pi.single (π i) 1 : Fin 3 → S) (π j)
  change diagonalEvaluation numbering (σ.toAlgHom.toLinearMap.rTensor E x) (π j) = _ at h
  rw [h]
  by_cases hji : j = i
  · subst j
    simp
  · simp [Pi.single_eq_of_ne hji, Pi.single_eq_of_ne (π.injective.ne hji)]

private theorem modelCoefficientAction_op (σ : Gal(S/F))
    (hlaw : ∀ x y, t (J.law.op S x y) = modelOp (t x) (t y))
    (x y : Model S) :
    modelCoefficientAction t σ (modelOp x y) =
      modelOp (modelCoefficientAction t σ x) (modelCoefficientAction t σ y) := by
  obtain ⟨x, rfl⟩ := t.surjective x
  obtain ⟨y, rfl⟩ := t.surjective y
  rw [← hlaw]
  change t (σ.toAlgHom.toLinearMap.rTensor J.V (t.symm (t (J.law.op S x y)))) =
    modelOp (t (σ.toAlgHom.toLinearMap.rTensor J.V (t.symm (t x))))
      (t (σ.toAlgHom.toLinearMap.rTensor J.V (t.symm (t y))))
  simp only [LinearEquiv.symm_apply_apply]
  exact (congrArg t (J.law.natural σ.toAlgHom x y)).trans (hlaw _ _)

private theorem peirceProjection_fixed (i : Fin 3) (x : Model S) :
    x ∈ geometricPeirceBlock i ↔ singleBlockCoordinates i (x.2 i) = x := by
  classical
  change (x ∈ LinearMap.ker (LinearMap.fst S (Fin 3 → S) (Fin 3 → Zorn S)) ⊓
    ⨅ j : {j : Fin 3 // j ≠ i}, LinearMap.ker ((LinearMap.proj j.val).comp
      (LinearMap.snd S (Fin 3 → S) (Fin 3 → Zorn S)))) ↔ _
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.fst_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.snd_apply]
  constructor
  · rintro ⟨h₁, h₂⟩
    apply Prod.ext
    · exact h₁.symm
    · funext j
      by_cases hj : j = i
      · subst j
        simp [CubicSpecification.singleBlockCoordinates]
      · rw [h₂ ⟨j, hj⟩]
        simp [CubicSpecification.singleBlockCoordinates, Pi.single_eq_of_ne hj]
  · intro h
    refine ⟨(congrArg Prod.fst h).symm, ?_⟩
    intro j
    simpa [CubicSpecification.singleBlockCoordinates, Pi.single_eq_of_ne j.property] using
      (congrArg (fun z : Model S => z.2 j.val) h).symm

private theorem perm_cyclic_complement (π : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (π (cyclicNext i) = cyclicNext (π i) ∧ π (cyclicPrev i) = cyclicPrev (π i)) ∨
      (π (cyclicNext i) = cyclicPrev (π i) ∧ π (cyclicPrev i) = cyclicNext (π i)) := by
  revert π i
  decide

private theorem peirceProjector_eq (i : Fin 3) (x : Model S) :
    geometricPeirceProjector i x = singleBlockCoordinates i (x.2 i) :=
  (LinearAlgebraicGroups.Albert.hermitian_frame (norm S) (fun _ => 1)).2.2.2.1 i x

private theorem modelCoefficientAction_projector (σ : Gal(S/F))
    (hdiag : ∀ e : E, t (1 ⊗ₜ[F] B.diagonal e) = (fun i => numbering.symm i e, 0))
    (hlaw : ∀ x y, t (J.law.op S x y) = modelOp (t x) (t y))
    (i : Fin 3) (x : Model S) :
    modelCoefficientAction t σ (geometricPeirceProjector i x) =
      geometricPeirceProjector (vertexPermutation (numbering := numbering) σ i)
        (modelCoefficientAction t σ x) := by
  let π := vertexPermutation (numbering := numbering) σ
  let g := modelCoefficientAction t σ
  let T := triple (norm S) (fun _ => 1)
  have hadd (a b : Model S) : g (a + b) = g a + g b := by
    simp only [g, modelCoefficientAction, map_add]
  have hsub (a b : Model S) : g (a - b) = g a - g b := by
    simp only [g, modelCoefficientAction, map_sub]
  have hop (a b : Model S) : g (modelOp a b) = modelOp (g a) (g b) :=
    modelCoefficientAction_op t σ hlaw a b
  have hT (a b c : Model S) : g (T a b c) = T (g a) (g b) (g c) := by
    change g (modelOp (a + c) b - modelOp a b - modelOp c b) = _
    rw [hsub, hsub, hop, hop, hop, hadd]
    rfl
  have hsym (a b c : Model S) : T a b c = T c b a := by
    dsimp only [T, triple]
    rw [add_comm a c]
    abel
  have haxis (j : Fin 3) : g (frameAxis j) = frameAxis (π j) :=
    modelCoefficientAction_axis B t σ hdiag j
  change g (T (frameAxis (cyclicNext i)) x (frameAxis (cyclicPrev i))) =
    T (frameAxis (cyclicNext (π i))) (g x) (frameAxis (cyclicPrev (π i)))
  rw [hT, haxis, haxis]
  rcases perm_cyclic_complement π i with ⟨a, b⟩ | ⟨a, b⟩
  · rw [a, b]
  · rw [a, b, hsym]

private theorem modelCoefficientAction_mem_block (σ : Gal(S/F))
    (hdiag : ∀ e : E, t (1 ⊗ₜ[F] B.diagonal e) = (fun i => numbering.symm i e, 0))
    (hlaw : ∀ x y, t (J.law.op S x y) = modelOp (t x) (t y))
    (i : Fin 3) (x : Model S) :
    x ∈ geometricPeirceBlock i ↔ modelCoefficientAction t σ x ∈
      geometricPeirceBlock (vertexPermutation (numbering := numbering) σ i) := by
  rw [peirceProjection_fixed, peirceProjection_fixed, ← peirceProjector_eq,
    ← peirceProjector_eq, ← modelCoefficientAction_projector B t σ hdiag hlaw,
    (modelCoefficientAction_injective t σ).eq_iff]


open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)

variable [Algebra E S] [IsScalarTower F E S]

private theorem extendAlbertVector_injective (J : AlbertModel F) :
    Function.Injective (extendAlbertVector (E := E) (S := S) J) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := J.V)
    (vectorEmbedding (F := F) (E := E) (S := S)).toLinearMap
    (vectorEmbedding (F := F) (E := E) (S := S)).injective

private theorem mem_peirceSpace_iff (i : Fin 3) (x : E ⊗[F] J.V) :
    x ∈ peirceSpace (E := E) t i ↔ t (extendAlbertVector J x) ∈ geometricPeirceBlock i := Iff.rfl

private theorem extendAlbertVector_map (J : AlbertModel F) (σ : Gal(E/F)) (γ : Gal(S/F))
    (hγ : γ.toAlgHom.comp vectorEmbedding = vectorEmbedding.comp σ.toAlgHom)
    (x : E ⊗[F] J.V) :
    extendAlbertVector J (TensorProduct.map σ.toLinearMap LinearMap.id x) =
      γ.toAlgHom.toLinearMap.rTensor J.V (extendAlbertVector J x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    change vectorEmbedding (F := F) (S := S) (σ a) ⊗ₜ[F] b =
      γ (vectorEmbedding (F := F) (S := S) a) ⊗ₜ[F] b
    exact congrArg (fun s : S => s ⊗ₜ[F] b) (DFunLike.congr_fun hγ a).symm
  | add x y hx hy => simp only [extendAlbertVector, map_add] at hx hy ⊢; rw [hx, hy]

private theorem peirce_transport [Normal F E]
    (hdiag : ∀ e : E, t (1 ⊗ₜ[F] B.diagonal e) = (fun i => numbering.symm i e, 0))
    (hlaw : ∀ x y, t (J.law.op S x y) = modelOp (t x) (t y))
    (σ : Gal(E/F)) (γ : Gal(S/F)) (hγ : γ.restrictNormal E = σ)
    (e : E →ₐ[F] S) (x : E ⊗[F] J.V) :
    x ∈ peirceSpace (E := E) t (numbering e) ↔
      TensorProduct.map σ.toLinearMap LinearMap.id x ∈
        peirceSpace (E := E) t (numbering (γ.toAlgHom.comp e)) := by
  have hcomp : γ.toAlgHom.comp vectorEmbedding = vectorEmbedding.comp σ.toAlgHom :=
    AlgHom.ext fun a => hγ ▸ (γ.restrictNormal_commutes E a).symm
  rw [mem_peirceSpace_iff, mem_peirceSpace_iff, extendAlbertVector_map J σ γ hcomp]
  have hv : vertexPermutation (numbering := numbering) γ (numbering e) =
      numbering (γ.toAlgHom.comp e) := by
    change numbering (γ.toAlgHom.comp (numbering.symm (numbering e))) = _
    rw [numbering.symm_apply_apply]
  rw [← hv]
  simpa only [modelCoefficientAction, LinearEquiv.symm_apply_apply] using
    modelCoefficientAction_mem_block B t γ hdiag hlaw (numbering e) (t (extendAlbertVector J x))

private theorem cyclicEmbeddingTransport [Module.Finite F E] [IsGalois F E]
    (hdeg : Module.finrank F E = 3) (σ : Gal(E/F)) (γ : Gal(S/F))
    (hγ : γ.toAlgHom.comp vectorEmbedding = vectorEmbedding.comp σ.toAlgHom)
    (e : E →ₐ[F] S) : γ.toAlgHom.comp e = e.comp σ.toAlgHom := by
  have hn : Nat.card (Gal(E/F)) = 3 := (IsGalois.card_aut_eq_finrank F E).trans hdeg
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsCyclic (Gal(E/F)) := isCyclic_of_prime_card hn
  let τ := e.restrictNormal' E
  let e₀ : E →ₐ[F] S := vectorEmbedding
  have he (a : E) : e₀ (τ a) = e a := e.restrictNormal_commutes E a
  have hσ (a : E) : γ (e₀ a) = e₀ (σ a) := DFunLike.congr_fun hγ a
  have hcomm (a : E) : σ (τ a) = τ (σ a) :=
    DFunLike.congr_fun ((IsCyclic.commGroup (α := Gal(E/F))).mul_comm σ τ) a
  apply AlgHom.ext
  intro a
  change γ (e a) = e (σ a)
  rw [← he a, hσ, hcomm, he]

/-- Applying a cubic Galois automorphism to the coefficients transports the
block of the embedding `e` to the block of `e.comp σ.toAlgHom`. -/
theorem cubicPeirceTransport [Module.Finite F E] [IsGalois F E] [Normal F S]
    {G : AffineAlgebraicGroup F} {D : DiagramPresentation G E S}
    (M : CubicPeirceModel G D) (hdeg : Module.finrank F E = 3)
    (σ : Gal(E/F)) (e : E →ₐ[F] S) (x : E ⊗[F] M.albert.V) :
    x ∈ peirceSpace (E := E) M.coordinates (D.numbering e) ↔
      TensorProduct.map σ.toLinearMap LinearMap.id x ∈
        peirceSpace (E := E) M.coordinates (D.numbering (e.comp σ.toAlgHom)) := by
  obtain ⟨γ, hγ⟩ := AlgEquiv.restrictNormalHom_surjective S σ
  have hcomp : γ.toAlgHom.comp vectorEmbedding = vectorEmbedding.comp σ.toAlgHom :=
    AlgHom.ext fun a => hγ ▸ (γ.restrictNormal_commutes E a).symm
  rw [← cyclicEmbeddingTransport hdeg σ γ hcomp e]
  exact peirce_transport M.cubic M.coordinates M.diagonal M.law σ γ hγ e x

private theorem diagonalCoordinate_eq {G : AffineAlgebraicGroup F}
    {D : DiagramPresentation G E S} (M : CubicPeirceModel G D) (e : E →ₐ[F] S)
    (x : E ⊗[F] E) :
    diagonalCoordinate M e x = diagonalEvaluation D.numbering
      (TensorProduct.map (vectorEmbedding (F := F) (E := E) (S := S)).toLinearMap
        LinearMap.id x) (D.numbering e) := by
  have h (y : E ⊗[F] E) :
      extendAlbertVector M.albert (M.cubic.diagonal.baseChange E y) =
        M.cubic.diagonal.baseChange S
          (TensorProduct.map (vectorEmbedding (F := F) (E := E) (S := S)).toLinearMap
            LinearMap.id y) := by
    induction y using TensorProduct.inductionOn with
    | tmul a b => simp [extendAlbertVector, LinearMap.baseChange_tmul]
    | add y z hy hz => simp only [map_add, extendAlbertVector] at hy hz ⊢; rw [hy, hz]
  rw [diagonalCoordinate, h, diagonalCoordinates_baseChange M.cubic M.coordinates M.diagonal]

private theorem cyclicLabelTransport [Module.Finite F E] [IsGalois F E]
    {G : AffineAlgebraicGroup F} {D : DiagramPresentation G E S}
    (M : CubicPeirceModel G D) (hdeg : Module.finrank F E = 3) : CyclicLabelTransport M := by
  constructor
  · intro e a b
    rw [diagonalCoordinate_eq, TensorProduct.map_tmul, LinearMap.id_apply,
      diagonalEvaluation_tmul, Equiv.symm_apply_apply]
    rfl
  · intro σ γ hγ e
    refine ⟨cyclicEmbeddingTransport hdeg σ γ hγ e, ?_, ?_⟩
    · intro x
      rw [diagonalCoordinate_eq, diagonalCoordinate_eq, ← diagonalEvaluation_galois γ]
      have hc (y : E ⊗[F] E) :
          TensorProduct.map (vectorEmbedding (F := F) (E := E) (S := S)).toLinearMap
            LinearMap.id (TensorProduct.map σ.toLinearMap LinearMap.id y) =
          γ.toAlgHom.toLinearMap.rTensor E
            (TensorProduct.map (vectorEmbedding (F := F) (E := E) (S := S)).toLinearMap
              LinearMap.id y) := by
        induction y using TensorProduct.inductionOn with
        | tmul a b =>
          exact congrArg (fun s : S => s ⊗ₜ[F] b) (DFunLike.congr_fun hγ a).symm
        | add y z hy hz => simp only [map_add, hy, hz]
      rw [hc]
    · intro x
      have h := modelCoefficientAction_projector M.cubic M.coordinates γ M.diagonal M.law
        (D.numbering e) x
      simpa only [geometricCoefficientAction, modelCoefficientAction, vertexPermutation,
        Equiv.trans_apply, Equiv.symm_apply_apply, embeddingPermutation, Equiv.coe_fn_mk] using h

private theorem cubicPeirceEndConjugacy [Module.Finite F E] [IsGalois F E] [Normal F S]
    {G : AffineAlgebraicGroup F} {D : DiagramPresentation G E S}
    (M : CubicPeirceModel G D) (hdeg : Module.finrank F E = 3)
    (σ : Gal(E/F)) (e : E →ₐ[F] S) :
    let W := peirceSpace (E := E) M.coordinates (D.numbering e)
    let W' := peirceSpace (E := E) M.coordinates (D.numbering (e.comp σ.toAlgHom))
    ∃ c : Module.End E W ≃+* Module.End E W',
      (∀ a : E, c (algebraMap E _ a) = algebraMap E _ (σ a)) ∧
      ∀ (a : Module.End E W) (x : W) (y : W'),
        TensorProduct.map σ.toLinearMap LinearMap.id x.val = y.val →
        (c a y).val = TensorProduct.map σ.toLinearMap LinearMap.id (a x).val := by
  let W := peirceSpace (E := E) M.coordinates (D.numbering e)
  let W' := peirceSpace (E := E) M.coordinates (D.numbering (e.comp σ.toAlgHom))
  let f := TensorProduct.congr σ.toLinearEquiv (LinearEquiv.refl F M.albert.V)
  have hf (x) : x ∈ W ↔ f x ∈ W' := cubicPeirceTransport M hdeg σ e x
  let ρ := σ.toRingEquiv
  let : RingHomInvPair ρ.toRingHom ρ.symm.toRingHom := RingHomInvPair.of_ringEquiv ρ
  let : RingHomInvPair ρ.symm.toRingHom ρ.toRingHom := RingHomInvPair.of_ringEquiv_symm ρ
  let g : W ≃ₛₗ[ρ.toRingHom] W' :=
    { toFun := fun x => ⟨f x.val, (hf x.val).mp x.property⟩
      invFun := fun y => ⟨f.symm y.val, (hf (f.symm y.val)).mpr
        ((f.apply_symm_apply y.val).symm ▸ y.property)⟩
      left_inv := fun x => Subtype.ext (f.symm_apply_apply x.val)
      right_inv := fun y => Subtype.ext (f.apply_symm_apply y.val)
      map_add' := fun x y => Subtype.ext (f.map_add x.val y.val)
      map_smul' := fun a x => Subtype.ext (by
        change f (a • x.val) = σ a • f x.val
        generalize x.val = z
        induction z using TensorProduct.inductionOn with
        | tmul b v =>
          simp only [TensorProduct.smul_tmul', smul_eq_mul, f, TensorProduct.congr_tmul,
            AlgEquiv.toLinearEquiv_apply, LinearEquiv.refl_apply, map_mul]
        | add y z hy hz => simp only [smul_add, map_add, hy, hz]) }
  refine ⟨g.conjRingEquiv, ?_, ?_⟩
  · intro a
    apply LinearMap.ext
    intro y
    rw [LinearEquiv.conjRingEquiv_apply_apply]
    change g (a • g.symm y) = σ a • y
    rw [map_smulₛₗ, LinearEquiv.apply_symm_apply]
    rfl
  · intro a x y h
    have hy : g x = y := Subtype.ext h
    rw [LinearEquiv.conjRingEquiv_apply_apply, ← hy, g.symm_apply_apply]
    rfl

private theorem eq_zero_of_mem_peirceSpaces {i j : Fin 3} (hij : i ≠ j) (x : E ⊗[F] J.V)
    (hi : x ∈ peirceSpace (E := E) t i) (hj : x ∈ peirceSpace (E := E) t j) : x = 0 := by
  let z := t (extendAlbertVector J (S := S) x)
  have hi' : singleBlockCoordinates i (z.2 i) = z :=
    (peirceProjection_fixed i z).mp ((mem_peirceSpace_iff t i x).mp hi)
  have hj' : singleBlockCoordinates j (z.2 j) = z :=
    (peirceProjection_fixed j z).mp ((mem_peirceSpace_iff t j x).mp hj)
  have hzi : z.2 i = 0 := by
    rw [← hj']
    change (Pi.single j (z.2 j) : Fin 3 → Zorn S) i = 0
    exact Pi.single_eq_of_ne hij _
  have hz : z = 0 := by
    rw [← hi', hzi]
    exact Prod.ext rfl (funext fun k => by simp [CubicSpecification.singleBlockCoordinates])
  apply extendAlbertVector_injective (J := J) (S := S)
  apply t.injective
  simpa only [z, map_zero, extendAlbertVector] using hz

private theorem invariantAlbertVector [IsGalois E S] [FiniteDimensional F J.V]
    (x : S ⊗[F] J.V)
    (hx : ∀ τ : Gal(S/E), (τ.restrictScalars F).toAlgHom.toLinearMap.rTensor J.V x = x) :
    ∃ y : E ⊗[F] J.V, extendAlbertVector J y = x := by
  classical
  let b := Module.finBasis F J.V
  let c := b.baseChange S
  have hmap (τ : Gal(S/E)) (z : S ⊗[F] J.V) (a : Fin (Module.finrank F J.V)) :
      c.repr ((τ.restrictScalars F).toAlgHom.toLinearMap.rTensor J.V z) a = τ (c.repr z a) := by
    induction z using TensorProduct.inductionOn with
    | tmul s v =>
      simp only [LinearMap.rTensor_tmul, c, Module.Basis.baseChange_repr_tmul, Algebra.smul_def]
      change algebraMap F S (b.repr v a) * τ s = τ (algebraMap F S (b.repr v a) * s)
      rw [map_mul]
      rw [IsScalarTower.algebraMap_apply F E S, τ.commutes]
    | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]
  have hcoeff (a : Fin (Module.finrank F J.V)) :
      ∃ d : E, algebraMap E S d = c.repr x a :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (c.repr x a)).mpr fun τ =>
      (hmap τ x a).symm.trans (congrArg (fun z => c.repr z a) (hx τ))
  choose d hd using hcoeff
  let extend : (E ⊗[F] J.V) →ₗ[E] (S ⊗[F] J.V) :=
    TensorProduct.AlgebraTensorModule.map (Algebra.ofId E S).toLinearMap LinearMap.id
  use ∑ a, d a • b.baseChange E a
  change extend _ = x
  rw [map_sum, ← c.sum_repr x]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul, Module.Basis.baseChange_apply, Module.Basis.baseChange_apply]
  simp only [extend, TensorProduct.AlgebraTensorModule.map_tmul, AlgHom.toLinearMap_apply, map_one,
    LinearMap.id_apply]
  change d a • ((1 : S) ⊗ₜ[F] b a) = c.repr x a • ((1 : S) ⊗ₜ[F] b a)
  rw [← algebraMap_smul S (d a), hd]

private theorem modelCoefficientAction_fix_extend (τ : Gal(S/E)) (x : E ⊗[F] J.V) :
    modelCoefficientAction t (τ.restrictScalars F) (t (extendAlbertVector J x)) =
      t (extendAlbertVector J x) := by
  rw [modelCoefficientAction, LinearEquiv.symm_apply_apply]
  apply congrArg t
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    change τ (algebraMap E S a) ⊗ₜ[F] b = _
    rw [τ.commutes]
    rfl
  | add x y hx hy =>
    simp only [extendAlbertVector, map_add] at hx hy ⊢
    rw [hx, hy]

private theorem residual_vertex_transport (τ : Gal(S/E)) (e : E →ₐ[F] S) :
    vertexPermutation (numbering := numbering) (τ.restrictScalars F) (numbering e) =
      numbering (τ.restrictScalars F |>.toAlgHom.comp e) := by
  change numbering ((τ.restrictScalars F).toAlgHom.comp (numbering.symm (numbering e))) = _
  rw [Equiv.symm_apply_apply]

private theorem residual_fixes_marked (τ : Gal(S/E)) :
    (τ.restrictScalars F).toAlgHom.comp (vectorEmbedding (F := F) (E := E) (S := S)) =
      vectorEmbedding :=
  AlgHom.ext fun a => τ.commutes a

private theorem peirceProjector_descends [IsGalois E S] [FiniteDimensional F J.V]
    (hdiag : ∀ e : E, t (1 ⊗ₜ[F] B.diagonal e) = (fun i => numbering.symm i e, 0))
    (hlaw : ∀ x y, t (J.law.op S x y) = modelOp (t x) (t y))
    (i : Fin 3) (hi : ∀ τ : Gal(S/E), vertexPermutation (numbering := numbering)
      (τ.restrictScalars F) i = i) (x : E ⊗[F] J.V) :
    ∃ y : peirceSpace (E := E) t i,
      t (extendAlbertVector J y.val) = geometricPeirceProjector i (t (extendAlbertVector J x)) := by
  let z := geometricPeirceProjector i (t (extendAlbertVector J x))
  obtain ⟨y, hy⟩ := invariantAlbertVector (E := E) (J := J) (t.symm z) (fun τ => by
    apply t.injective
    change modelCoefficientAction t (τ.restrictScalars F) z = t (t.symm z)
    rw [t.apply_symm_apply, modelCoefficientAction_projector B t _ hdiag hlaw, hi,
      modelCoefficientAction_fix_extend])
  have h : t (extendAlbertVector J y) = z := (congrArg t hy).trans (t.apply_symm_apply z)
  refine ⟨⟨y, (mem_peirceSpace_iff t i y).mpr ?_⟩, h⟩
  rw [h, peirceProjection_fixed]
  simp [z, peirceProjector_eq, CubicSpecification.singleBlockCoordinates]

local instance peirceRestrictedModule : Module E (Zorn S) :=
  Module.compHom (Zorn S) (algebraMap E S)

local instance peirceRestrictedTower : IsScalarTower E S (Zorn S) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

private def peirceCoordinate (i : Fin 3) : peirceSpace (E := E) t i →ₗ[E] Zorn S :=
  (((LinearMap.proj i).comp (LinearMap.snd S (Fin 3 → S) (Fin 3 → Zorn S))).comp
    t.toLinearMap).restrictScalars E ∘ₗ
    TensorProduct.AlgebraTensorModule.map (Algebra.ofId E S).toLinearMap LinearMap.id ∘ₗ
    (peirceSpace (E := E) t i).subtype

private def peirceInclusion (i : Fin 3) : Zorn S →ₗ[S] Model S :=
  (0 : Zorn S →ₗ[S] (Fin 3 → S)).prod (LinearMap.single S (fun _ : Fin 3 => Zorn S) i)

private theorem peirceCoordinate_apply (i : Fin 3) (x : peirceSpace (E := E) t i) :
    peirceCoordinate t i x = (t (extendAlbertVector J x.val)).2 i := rfl

private theorem peirceInclusion_coordinate (i : Fin 3) (x : peirceSpace (E := E) t i) :
    peirceInclusion (S := S) i (peirceCoordinate t i x) = t (extendAlbertVector J x.val) :=
  (peirceProjection_fixed i _).mp ((mem_peirceSpace_iff t i x.val).mp x.property)

private theorem peirceCoordinate_baseChange_injective (i : Fin 3) :
    Function.Injective ((peirceCoordinate (E := E) t i).liftBaseChange S) := by
  let P := peirceSpace (E := E) t i
  let cancel := TensorProduct.AlgebraTensorModule.cancelBaseChange F E S S J.V
  let j : S ⊗[E] P →ₗ[S] S ⊗[E] (E ⊗[F] J.V) := P.subtype.baseChange S
  have hj : Function.Injective j :=
    Module.Flat.lTensor_preserves_injective_linearMap P.subtype Subtype.val_injective
  have h (z : S ⊗[E] P) :
      peirceInclusion i ((peirceCoordinate t i).liftBaseChange S z) = t (cancel (j z)) := by
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      rw [LinearMap.liftBaseChange_tmul, map_smul, peirceInclusion_coordinate]
      have hc : cancel (j ((1 : S) ⊗ₜ[E] x)) = extendAlbertVector J x.val := by
        rw [show j (1 ⊗ₜ[E] x) = (1 : S) ⊗ₜ[E] x.val from rfl]
        induction x.val using TensorProduct.inductionOn with
        | tmul b v =>
          rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
          simp only [Algebra.smul_def, mul_one]
          rfl
        | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, extendAlbertVector] at hy hz ⊢; rw [hy, hz]
      rw [← hc, ← map_smul, ← map_smul, ← j.map_smul,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y heq
  exact hj (cancel.injective (t.injective ((h x).symm.trans (congrArg (peirceInclusion i) heq |>.trans (h y)))))

private theorem peirceCoordinate_baseChange_surjective [IsGalois E S] [FiniteDimensional F J.V]
    (hdiag : ∀ e : E, t (1 ⊗ₜ[F] B.diagonal e) = (fun i => numbering.symm i e, 0))
    (hlaw : ∀ x y, t (J.law.op S x y) = modelOp (t x) (t y))
    (i : Fin 3) (hi : ∀ τ : Gal(S/E), vertexPermutation (numbering := numbering)
      (τ.restrictScalars F) i = i) :
    Function.Surjective ((peirceCoordinate (E := E) t i).liftBaseChange S) := by
  classical
  let b := Module.finBasis F J.V
  let c := b.baseChange S
  let p : (S ⊗[F] J.V) →ₗ[S] Zorn S :=
    (LinearMap.proj i).comp ((LinearMap.snd S (Fin 3 → S) (Fin 3 → Zorn S)).comp t.toLinearMap)
  let f := (peirceCoordinate (E := E) t i).liftBaseChange S
  have step (a : Fin (Module.finrank F J.V)) : p (c a) ∈ LinearMap.range f := by
    obtain ⟨y, hy⟩ := peirceProjector_descends B t hdiag hlaw i hi ((1 : E) ⊗ₜ[F] b a)
    refine ⟨(1 : S) ⊗ₜ[E] y, ?_⟩
    rw [LinearMap.liftBaseChange_one_tmul, peirceCoordinate_apply, hy, peirceProjector_eq]
    rw [show (singleBlockCoordinates i ((t (extendAlbertVector J (1 ⊗ₜ[F] b a))).2 i)).2 i =
      (t (extendAlbertVector J (1 ⊗ₜ[F] b a))).2 i from Pi.single_eq_same (M := fun _ => Zorn S) i _]
    rw [show c a = (1 : S) ⊗ₜ[F] b a from Module.Basis.baseChange_apply S b a]
    change (t ((algebraMap E S 1) ⊗ₜ[F] b a)).2 i = _
    rw [map_one]
    rfl
  intro z
  let x := t.symm (peirceInclusion i z)
  have hx : p x = z := by
    change (t (t.symm (peirceInclusion i z))).2 i = z
    rw [t.apply_symm_apply]
    exact Pi.single_eq_same (M := fun _ => Zorn S) i z
  change z ∈ LinearMap.range f
  rw [← hx, ← c.sum_repr x, map_sum]
  simp only [map_smul]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (step a)

private theorem peirceSpace_finrank [IsGalois E S] [FiniteDimensional F J.V]
    (hdiag : ∀ e : E, t (1 ⊗ₜ[F] B.diagonal e) = (fun i => numbering.symm i e, 0))
    (hlaw : ∀ x y, t (J.law.op S x y) = modelOp (t x) (t y))
    (i : Fin 3) (hi : ∀ τ : Gal(S/E), vertexPermutation (numbering := numbering)
      (τ.restrictScalars F) i = i) :
    Module.finrank E (peirceSpace (E := E) t i) = 8 := by
  let e := LinearEquiv.ofBijective ((peirceCoordinate (E := E) t i).liftBaseChange S)
    ⟨peirceCoordinate_baseChange_injective t i,
      peirceCoordinate_baseChange_surjective B t hdiag hlaw i hi⟩
  let : Module.Free E ↥(peirceSpace (E := E) t i) :=
    Module.Free.of_divisionRing E ↥(peirceSpace (E := E) t i)
  rw [← Module.finrank_baseChange (R := S) (M' := ↥(peirceSpace (E := E) t i)), e.finrank_eq]
  simpa using Module.finrank_eq_card_basis (Zorn.coordinateBasis S)

private theorem modelCoefficientAction_smul (τ : Gal(S/F)) (a : S) (x : Model S) :
    modelCoefficientAction t τ (a • x) = τ a • modelCoefficientAction t τ x := by
  obtain ⟨z, rfl⟩ := t.surjective x
  obtain h : τ.toAlgHom.toLinearMap.rTensor J.V (a • z) =
      τ a • τ.toAlgHom.toLinearMap.rTensor J.V z := by
    induction z using TensorProduct.inductionOn with
    | tmul b v => simp [TensorProduct.smul_tmul', smul_eq_mul]
    | add y z hy hz => simp only [smul_add, map_add, hy, hz]
  rw [← map_smul, modelCoefficientAction, modelCoefficientAction, t.symm_apply_apply,
    t.symm_apply_apply, h, map_smul]

open private opSquare from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.QuadraticOperators

private theorem singleBlock_square (i : Fin 3) (x : Zorn S) :
    modelOp (singleBlockCoordinates i x) CubicSpecification.cubicUnit =
      norm S x • (CubicSpecification.cubicUnit - frameAxis i) := by
  have hs := opSquare (n := norm S) (fun _ => 1) (singleBlockCoordinates i x)
  change modelOp (singleBlockCoordinates i x) CubicSpecification.cubicUnit = _ at hs
  rw [hs]
  change CubicSpecification.cubicAdjoint (norm S) (fun _ => 1) (CubicSpecification.singleBlockCoordinates i x) +
      CubicSpecification.linearTrace (norm S) (fun _ => 1) (CubicSpecification.singleBlockCoordinates i x) •
        CubicSpecification.singleBlockCoordinates i x -
      CubicSpecification.quadraticTrace (norm S) (fun _ => 1) (CubicSpecification.singleBlockCoordinates i x) •
        CubicSpecification.cubicUnit = _
  have ha := (cubic_single_block_formulas (n := norm S) (fun _ => 1) i x).2.1
  unfold CubicSpecification.quadraticTrace
  rw [ha]
  apply Prod.ext
  · funext j
    by_cases hj : j = i
    · subst j
      simp [linearTrace_apply,
        CubicSpecification.singleBlockCoordinates, CubicSpecification.diagonalCoordinates,
        CubicSpecification.cubicUnit, FrameSpecification.frameAxis, CubicSpecification.blockWeight]
    · simp [linearTrace_apply,
        CubicSpecification.singleBlockCoordinates, CubicSpecification.diagonalCoordinates,
        CubicSpecification.cubicUnit, FrameSpecification.frameAxis, CubicSpecification.blockWeight,
        Pi.single_eq_of_ne hj]
  · funext j
    simp [linearTrace_apply, CubicSpecification.singleBlockCoordinates,
      CubicSpecification.diagonalCoordinates, CubicSpecification.cubicUnit, FrameSpecification.frameAxis]

private theorem coordinateNorm_descends [IsGalois E S]
    (hunit : t (1 ⊗ₜ[F] J.law.unit) = CubicSpecification.cubicUnit)
    (hdiag : ∀ e : E, t (1 ⊗ₜ[F] B.diagonal e) = (fun i => numbering.symm i e, 0))
    (hlaw : ∀ x y, t (J.law.op S x y) = modelOp (t x) (t y))
    (i : Fin 3) (hi : ∀ τ : Gal(S/E), vertexPermutation (numbering := numbering)
      (τ.restrictScalars F) i = i) (x : peirceSpace (E := E) t i) :
    norm S (peirceCoordinate t i x) ∈ Set.range (algebraMap E S) := by
  let a := norm S (peirceCoordinate t i x)
  let y := t (extendAlbertVector J (S := S) x.val)
  let c : Model S := CubicSpecification.cubicUnit
  let p : Model S := frameAxis i
  have hy : y = singleBlockCoordinates i (peirceCoordinate t i x) :=
    (peirceInclusion_coordinate t i x).symm
  have hsq : modelOp y c = a • (c - p) := by rw [hy]; exact singleBlock_square i _
  apply (InfiniteGalois.mem_range_algebraMap_iff_fixed a).mpr
  intro τ
  let γ := τ.restrictScalars F
  have hf : modelCoefficientAction t γ y = y := modelCoefficientAction_fix_extend t τ x.val
  have hc : modelCoefficientAction t γ c = c := by
    change modelCoefficientAction t γ CubicSpecification.cubicUnit = CubicSpecification.cubicUnit
    rw [← hunit, modelCoefficientAction, t.symm_apply_apply, LinearMap.rTensor_tmul]
    simp only [AlgHom.toLinearMap_apply, map_one]
  have hp : modelCoefficientAction t γ p = p := by
    dsimp only [p]
    rw [modelCoefficientAction_axis B t γ hdiag i, hi τ]
  have h := modelCoefficientAction_op t γ hlaw y c
  rw [hf, hc, hsq, modelCoefficientAction_smul] at h
  have hcp : modelCoefficientAction t γ (c - p) = c - p := by
    simp only [modelCoefficientAction, map_sub] at hc hp ⊢
    rw [hc, hp]
  rw [hcp] at h
  have hj : cyclicNext i ≠ i := by fin_cases i <;> decide
  have ha := congrArg (fun z : Model S => z.1 (cyclicNext i)) h
  change γ a = a
  simpa [c, p, CubicSpecification.cubicUnit, FrameSpecification.frameAxis,
    CubicSpecification.diagonalCoordinates, Pi.single_eq_of_ne hj] using ha

private theorem exists_peirceNorm [IsGalois E S] [FiniteDimensional F J.V]
    (hunit : t (1 ⊗ₜ[F] J.law.unit) = CubicSpecification.cubicUnit)
    (hdiag : ∀ e : E, t (1 ⊗ₜ[F] B.diagonal e) = (fun i => numbering.symm i e, 0))
    (hlaw : ∀ x y, t (J.law.op S x y) = modelOp (t x) (t y))
    (i : Fin 3) (hi : ∀ τ : Gal(S/E), vertexPermutation (numbering := numbering)
      (τ.restrictScalars F) i = i) :
    ∃ q : QuadraticForm E (peirceSpace (E := E) t i),
      IsRegular (K := E) (V := ↥(peirceSpace (E := E) t i)) q ∧
        ∀ x, algebraMap E S (q x) = norm S (peirceCoordinate t i x) := by
  let L := peirceCoordinate (E := E) t i
  let incl : E →ₗ[E] S := Algebra.linearMap E S
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective incl
    (LinearMap.ker_eq_bot.mpr (algebraMap E S).injective)
  let q := g.compQuadraticMap (((norm S).restrictScalars (S := E)).comp L)
  have hq (x : peirceSpace (E := E) t i) : algebraMap E S (q x) = norm S (L x) := by
    obtain ⟨a, ha⟩ := coordinateNorm_descends B t hunit hdiag hlaw i hi x
    change incl (g (norm S (L x))) = norm S (L x)
    rw [← show incl a = norm S (L x) from ha]
    exact congrArg incl (DFunLike.congr_fun hg a)
  refine ⟨q, LinearMap.ker_eq_bot'.mpr ?_, hq⟩
  intro x hx
  have hp (z : peirceSpace (E := E) t i) : (norm S).polarBilin (L x) (L z) = 0 := by
    rw [show (norm S).polarBilin (L x) (L z) = algebraMap E S (q.polarBilin x z) by
      simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, map_sub, hq, map_add],
      DFunLike.congr_fun hx z, LinearMap.zero_apply, map_zero]
  have hs (u : S ⊗[E] peirceSpace (E := E) t i) :
      (norm S).polarBilin (L x) (L.liftBaseChange S u) = 0 := by
    induction u using TensorProduct.inductionOn with
    | tmul a z => rw [LinearMap.liftBaseChange_tmul, map_smul, hp, smul_zero]
    | add y z hy hz => simp only [map_add, hy, hz, add_zero]
  have hpol : (norm S).polarBilin (L x) = 0 := by
    ext z
    obtain ⟨z, rfl⟩ := peirceCoordinate_baseChange_surjective B t hdiag hlaw i hi z
    exact hs z
  let : (norm S).polarBilin.IsPerfPair := Zorn.perfect S
  have hL := (LinearMap.IsPerfPair.bijective_left (norm S).polarBilin).injective
    (hpol.trans (map_zero _).symm)
  apply Subtype.ext
  apply extendAlbertVector_injective (J := J) (S := S)
  apply t.injective
  rw [← peirceInclusion_coordinate t i x, show peirceCoordinate t i x = 0 from hL]
  simp [extendAlbertVector]

private theorem exists_markedVectorForm [IsGalois E S] [FiniteDimensional F J.V]
    (hunit : t (1 ⊗ₜ[F] J.law.unit) = CubicSpecification.cubicUnit)
    (hdiag : ∀ e : E, t (1 ⊗ₜ[F] B.diagonal e) = (fun i => numbering.symm i e, 0))
    (hlaw : ∀ x y, t (J.law.op S x y) = modelOp (t x) (t y)) :
    let i := numbering (vectorEmbedding (F := F) (E := E) (S := S))
    ∃ (q : QuadraticForm E (Fin 8 → E)), IsRegular q ∧
      ∃ d : (Fin 8 → E) ≃ₗ[E] peirceSpace (E := E) t i,
        ∀ x, algebraMap E S (q x) = norm S ((t (extendAlbertVector J (d x).val)).2 i) := by
  let e : E →ₐ[F] S := vectorEmbedding
  let i := numbering e
  have hi (τ : Gal(S/E)) : vertexPermutation (numbering := numbering) (τ.restrictScalars F) i = i :=
    (residual_vertex_transport (numbering := numbering) τ e).trans
      (congrArg numbering (residual_fixes_marked τ))
  obtain ⟨q, hq, hn⟩ := exists_peirceNorm B t hunit hdiag hlaw i hi
  let P := peirceSpace (E := E) t i
  have hdim : Module.finrank E P = 8 := peirceSpace_finrank B t hdiag hlaw i hi
  let : Module.Free E ↥P := Module.Free.of_divisionRing E ↥P
  let a : Module.Basis (Fin 8) E P := Module.finBasisOfFinrankEq E P hdim
  let d := a.equivFun.symm
  refine ⟨q.comp d.toLinearMap, ?_, d, fun x => hn (d x)⟩
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  apply d.injective
  rw [map_zero]
  apply LinearMap.ker_eq_bot'.mp hq
  ext y
  obtain ⟨z, rfl⟩ := d.surjective y
  simpa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar] using DFunLike.congr_fun hx z

end PeirceDescent

section ActualVectorForm

open CategoryTheory
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescentSpecification
open LinearAlgebraicGroups.Albert LinearAlgebraicGroups.Composition
open TrialitySpecification (Model modelOp)
open Composition.ZornSpecification (norm)
open scoped TensorProduct

private theorem actualMarkedVectorForm
    (F E S : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field E] [Field S] [Algebra F E] [Algebra F S]
    [Algebra E S] [IsScalarTower F E S] [Module.Finite F E] [Algebra.IsSeparable F E] [IsSepClosure F S]
    (degree : Module.finrank F E = 3) (G : AffineAlgebraicGroup F) (D : DiagramPresentation G E S) :
    Nonempty (CubicPeirceModel G D) := by
  obtain ⟨_, _, _, _, J, B, ⟨realization⟩, hsplit, hdiag⟩ :=
    TrialitarianAlbertDescent.trialitarianRealization F E S degree G D
  obtain ⟨t, hunit, hlaw, hdiag⟩ := hdiag
  let : Algebra.IsSeparable E S := Algebra.isSeparable_tower_top_of_isSeparable F E S
  let : IsSepClosure E S := ⟨IsSepClosure.sep_closed F, inferInstance⟩
  let : FiniteDimensional F J.V :=
    (SplitSpecification.freudenthal_finite_projective J.law J.albert.1).1
  obtain ⟨q, hq, d, hn⟩ := exists_markedVectorForm B t hunit hdiag hlaw
  exact ⟨{ albert := J, splitAlbert := hsplit, cubic := B, realization := realization
           coordinates := t, unit := hunit, law := hlaw, diagonal := hdiag
           q := q, regular := hq, vector := d, norm := hn }⟩

end ActualVectorForm

section CliffordPeirceProducts

open LinearAlgebraicGroups.Albert LinearAlgebraicGroups.Composition
open QuadraticOperatorSpecification (triple)
open Composition.ZornSpecification (norm)
open private triple_formula from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.QuadraticOperators
open private adjointCross_diagonal adjointCross_block adjointCross_comm
  next_zero next_one next_two prev_zero prev_one prev_two
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CubicIdentities

variable {S : Type u} [Field S]

private theorem peircePolar_next (i : Fin 3) (x y : Zorn S) :
    triple (norm S) (fun _ => 1) (singleBlockCoordinates i x) cubicUnit
      (singleBlockCoordinates (cyclicNext i) y) =
      singleBlockCoordinates (cyclicPrev i) (conjugate (norm S) (x * y)) := by
  let X := singleBlockCoordinates (R := S) i x
  let Y := singleBlockCoordinates (R := S) (cyclicNext i) y
  let Z := singleBlockCoordinates (R := S) (cyclicPrev i) (conjugate (norm S) (x * y))
  let γ : Fin 3 → Sˣ := fun _ => 1
  have htrace (j : Fin 3) (z : Zorn S) :
      tracePairing (norm S) γ (singleBlockCoordinates j z) cubicUnit = 0 := by
    change linearTrace (norm S) γ (singleBlockCoordinates j z) = 0
    simp [linearTrace_apply, CubicSpecification.singleBlockCoordinates]
  have hcross : adjointCross (norm S) γ X Y = Z := by
    apply Prod.ext
    · funext j
      rw [adjointCross_diagonal]
      fin_cases i <;> fin_cases j <;>
        simp [X, Y, Z, CubicSpecification.singleBlockCoordinates,
          next_zero, next_one, next_two]
    · funext j
      rw [adjointCross_block]
      fin_cases i <;> fin_cases j <;>
        simp [X, Y, Z, γ, CubicSpecification.singleBlockCoordinates,
          next_zero, next_one, next_two, prev_zero, prev_one, prev_two]
  have hunit : adjointCross (norm S) γ Z cubicUnit = -Z := by
    rw [adjointCross_comm]
    have h := (cubic_unit_identities (n := norm S) γ).2.2 Z
    change adjointCross (norm S) γ cubicUnit Z = linearTrace (norm S) γ Z • cubicUnit - Z at h
    rw [h]
    have hZ : linearTrace (norm S) γ Z = 0 := htrace _ _
    rw [hZ, zero_smul, zero_sub]
  change triple (norm S) γ X cubicUnit Y = Z
  rw [triple_formula, hcross, hunit]
  have hx : tracePairing (norm S) γ X cubicUnit = 0 := htrace _ _
  have hy : tracePairing (norm S) γ Y cubicUnit = 0 := htrace _ _
  rw [hx, hy, zero_smul, zero_smul, add_zero, zero_sub, neg_neg]

private theorem peircePolar_prev (i : Fin 3) (x y : Zorn S) :
    triple (norm S) (fun _ => 1) (singleBlockCoordinates i x) cubicUnit
      (singleBlockCoordinates (cyclicPrev i) y) =
      singleBlockCoordinates (cyclicNext i) (conjugate (norm S) (y * x)) := by
  have h₁ : cyclicNext (cyclicPrev i) = i := by fin_cases i <;> decide
  have h₂ : cyclicPrev (cyclicPrev i) = cyclicNext i := by fin_cases i <;> decide
  have hs : triple (norm S) (fun _ => 1) (singleBlockCoordinates i x) cubicUnit
      (singleBlockCoordinates (cyclicPrev i) y) =
      triple (norm S) (fun _ => 1) (singleBlockCoordinates (cyclicPrev i) y) cubicUnit
        (singleBlockCoordinates i x) := by
    unfold triple
    rw [add_comm]
    abel
  rw [hs]
  simpa only [h₁, h₂] using peircePolar_next (cyclicPrev i) y x

end CliffordPeirceProducts

section GeometricCliffordAlgebra

open LinearAlgebraicGroups.Albert LinearAlgebraicGroups.Composition
open CliffordAlgebra CliffordModel
open Composition.ZornSpecification (norm)
open scoped TensorProduct
open private isometry_grade from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinInnerDescent

variable {K S V : Type u} [Field K] [Field S] [Algebra K S] [AddCommGroup V] [Module K V]

private def diagonalEnd (S : Type u) [Field S] :
    Module.End S (Zorn S) × Module.End S (Zorn S) →ₐ[S] Module.End S (Zorn S × Zorn S) where
  toFun a := (a.1.comp (LinearMap.fst S _ _)).prod (a.2.comp (LinearMap.snd S _ _))
  map_one' := LinearMap.ext fun _ => rfl
  map_zero' := LinearMap.ext fun _ => rfl
  map_add' _ _ := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl
  commutes' _ := LinearMap.ext fun _ => rfl

private theorem diagonalEnd_injective (S : Type u) [Field S] :
    Function.Injective (diagonalEnd S) := by
  intro a b h
  apply Prod.ext <;> apply LinearMap.ext <;> intro x
  · exact congrArg (fun f : Module.End S (Zorn S × Zorn S) => (f (x, 0)).1) h
  · exact congrArg (fun f : Module.End S (Zorn S × Zorn S) => (f (0, x)).2) h

private theorem mem_diagonalEnd_range (a : Module.End S (Zorn S × Zorn S)) :
    a ∈ (diagonalEnd S).range ↔
      (∀ x, (a (x, 0)).2 = 0) ∧ (∀ y, (a (0, y)).1 = 0) := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨fun x => f.2.map_zero, fun y => f.1.map_zero⟩
  · intro ⟨hx, hy⟩
    let f := (LinearMap.fst S _ _).comp (a.comp (LinearMap.inl S _ _))
    let g := (LinearMap.snd S _ _).comp (a.comp (LinearMap.inr S _ _))
    refine ⟨(f, g), LinearMap.ext fun x => ?_⟩
    change ((a (x.1, 0)).1, (a (0, x.2)).2) = a x
    have h₁ : a (x.1, 0) = ((a (x.1, 0)).1, 0) := Prod.ext rfl (hx x.1)
    have h₂ : a (0, x.2) = (0, (a (0, x.2)).2) := Prod.ext (hy x.2) rfl
    calc
      _ = a (x.1, 0) + a (0, x.2) := by rw [h₁, h₂]; simp
      _ = a x := by rw [← map_add]; simp

private theorem geometricEvenClifford (q : QuadraticForm K V) {I : Type v} [LinearOrder I]
    (b : Module.Basis I K V) (d : S ⊗[K] V ≃ₗ[S] Zorn S)
    (hd : ∀ v, norm S (d (1 ⊗ₜ[K] v)) = algebraMap K S (q v)) :
    ∃ f : (S ⊗[K] even q) ≃ₐ[S] (Module.End S (Zorn S) × Module.End S (Zorn S)),
      ∀ v w x,
        diagonalEnd S (f (1 ⊗ₜ[K] (even.ι q).bilin v w)) x =
          CliffordSpecification.octonionOperator (d (1 ⊗ₜ[K] v))
            (CliffordSpecification.octonionOperator (d (1 ⊗ₜ[K] w)) x) := by
  let Q := CliffordSpecification.coefficientForm S q b
  let iso : Q.IsometryEquiv (norm S) :=
    { toLinearEquiv := d
      map_app' := fun x => QuadraticMap.congr_fun
        ((coefficient_form_unique S q b ((norm S).comp d.toLinearMap)).2 hd) x }
  obtain ⟨c, hc, _, hcg, _⟩ := base_change_model S q b
  let a := c.trans (equivOfIsometry iso)
  let o : CliffordAlgebra (norm S) ≃ₐ[S] Module.End S (Zorn S × Zorn S) := octonionEquiv
  let inc : S ⊗[K] even q →ₐ[S] S ⊗[K] CliffordAlgebra q :=
    Algebra.TensorProduct.map (AlgHom.id S S) (even q).val
  let g := o.toAlgHom.comp (a.toAlgHom.comp inc)
  have hinc : Function.Injective inc :=
    Module.Flat.lTensor_preserves_injective_linearMap (even q).val.toLinearMap Subtype.val_injective
  have hra : ((evenOdd q 0).baseChange S).map a.toLinearMap = evenOdd (norm S) 0 := by
    change (((evenOdd q 0).baseChange S).map
      ((equivOfIsometry iso).toLinearMap.comp c.toLinearMap)) = _
    rw [Submodule.map_comp, hcg, isometry_grade]
  have hmem (p : CliffordAlgebra (norm S)) : p ∈ evenOdd (norm S) 0 ↔ o p ∈ (diagonalEnd S).range :=
    (octonionEquiv_even p).trans (mem_diagonalEnd_range (o p)).symm
  have hrg : g.range = (diagonalEnd S).range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      apply (hmem (a (inc y))).mp
      rw [← hra]
      exact Submodule.mem_map.mpr ⟨inc y, ⟨y, rfl⟩, rfl⟩
    · intro hx
      have hm := (hmem (o.symm x)).mpr (by simpa using hx)
      rw [← hra] at hm
      obtain ⟨y, ⟨z, hz⟩, hy⟩ := Submodule.mem_map.mp hm
      exact ⟨z, (congrArg (o ∘ a) hz).trans ((congrArg o hy).trans (o.apply_symm_apply x))⟩
  let f := (AlgEquiv.ofInjective g (o.injective.comp (a.injective.comp hinc))).trans
    ((g.range.equivOfEq (diagonalEnd S).range hrg).trans
      (AlgEquiv.ofInjective (diagonalEnd S) (diagonalEnd_injective S)).symm)
  refine ⟨f, fun v w x => ?_⟩
  have hf (y : S ⊗[K] even q) : diagonalEnd S (f y) = g y := by
    change ((AlgEquiv.ofInjective (diagonalEnd S) (diagonalEnd_injective S))
      ((AlgEquiv.ofInjective (diagonalEnd S) (diagonalEnd_injective S)).symm _)).val = g y
    rw [AlgEquiv.apply_symm_apply]
    rfl
  rw [hf]
  have hv (v : V) : o (a (1 ⊗ₜ[K] ι q v)) =
      CliffordSpecification.octonionOperator (d (1 ⊗ₜ[K] v)) := by
    change o (equivOfIsometry iso (c (1 ⊗ₜ[K] ι q v))) = _
    rw [hc]
    change o (CliffordAlgebra.map iso.toIsometry (ι Q (1 ⊗ₜ[K] v))) = _
    rw [CliffordAlgebra.map_apply_ι]
    exact octonionEquiv_ι _
  change o (a ((1 : S) ⊗ₜ[K] (ι q v * ι q w))) x = _
  rw [show (1 : S) ⊗ₜ[K] (ι q v * ι q w) = (1 ⊗ₜ[K] ι q v) * (1 ⊗ₜ[K] ι q w) by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul], map_mul, map_mul, hv, hv]
  rfl

end GeometricCliffordAlgebra

section GeometricPeirceAction

open LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescentSpecification
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Albert LinearAlgebraicGroups.Composition
open QuadraticOperatorSpecification (triple)
open Composition.ZornSpecification (norm)
open scoped TensorProduct

attribute [local instance] peirceRestrictedModule peirceRestrictedTower

variable {F E S : Type u} [Field F] [Field E] [Field S]
  [Algebra F E] [Algebra F S] [Algebra E S] [IsScalarTower F E S]
  {G : AffineAlgebraicGroup F} {D : DiagramPresentation G E S}

private theorem next_ne_self (i : Fin 3) : cyclicNext i ≠ i := by fin_cases i <;> decide

private theorem prev_ne_self (i : Fin 3) : cyclicPrev i ≠ i := by fin_cases i <;> decide

private theorem next_ne_prev (i : Fin 3) : cyclicNext i ≠ cyclicPrev i := by
  fin_cases i <;> decide

private theorem complement_indices (i j : Fin 3) (h : j ≠ i) :
    j = cyclicPrev i ∨ j = cyclicNext i := by
  fin_cases i <;> fin_cases j <;> first | contradiction | decide

private theorem markedFormIsometry [IsGalois E S] (M : CubicPeirceModel G D)
    [FiniteDimensional F M.albert.V] :
    ∃ e : (CliffordSpecification.coefficientForm S M.q (Pi.basisFun E (Fin 8))).IsometryEquiv (norm S),
      ∀ v : Fin 8 → E,
        M.coordinates (extendAlbertVector M.albert (M.vector v).val) =
          singleBlockCoordinates (D.numbering vectorEmbedding) (e (1 ⊗ₜ[E] v)) := by
  classical
  let i := D.numbering (vectorEmbedding (F := F) (E := E) (S := S))
  have hi (τ : Gal(S/E)) : vertexPermutation (numbering := D.numbering) (τ.restrictScalars F) i = i :=
    (residual_vertex_transport (numbering := D.numbering) τ vectorEmbedding).trans
      (congrArg D.numbering (residual_fixes_marked τ))
  let e := LinearEquiv.ofBijective ((peirceCoordinate (E := E) M.coordinates i).liftBaseChange S)
    ⟨peirceCoordinate_baseChange_injective M.coordinates i,
      peirceCoordinate_baseChange_surjective M.cubic M.coordinates M.diagonal M.law i hi⟩
  let d := (LinearEquiv.baseChange E S _ _ M.vector).trans e
  have hd (v : Fin 8 → E) : d (1 ⊗ₜ[E] v) = peirceCoordinate M.coordinates i (M.vector v) := by
    simp only [d, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul]
    change ((peirceCoordinate (E := E) M.coordinates i).liftBaseChange S)
      (1 ⊗ₜ[E] M.vector v) = _
    rw [LinearMap.liftBaseChange_one_tmul]
  have hn (v : Fin 8 → E) : norm S (d (1 ⊗ₜ[E] v)) = algebraMap E S (M.q v) := by
    rw [hd]
    exact (M.norm v).symm
  refine ⟨⟨d, fun x => QuadraticMap.congr_fun
    ((CliffordModel.coefficient_form_unique S M.q (Pi.basisFun E (Fin 8))
      ((norm S).comp d.toLinearMap)).2 hn) x⟩, ?_⟩
  intro v
  change M.coordinates (extendAlbertVector M.albert (M.vector v).val) =
    singleBlockCoordinates i (d (1 ⊗ₜ[E] v))
  rw [hd]
  exact (peirceInclusion_coordinate M.coordinates i (M.vector v)).symm

set_option maxHeartbeats 1600000 in
private theorem exists_geometricPeirceAction [IsGalois E S] (M : CubicPeirceModel G D)
    [FiniteDimensional F M.albert.V] :
    ∃ f : (S ⊗[E] CliffordAlgebra.even M.q) ≃ₐ[S]
        (∀ _ : HalfSpinVertices F E S, Module.End S (Zorn S)),
      ∀ j v w x, f (1 ⊗ₜ[E] (CliffordAlgebra.even.ι M.q).bilin v w) j x =
        halfSpinVectorProduct M j v w x := by
  classical
  let i := D.numbering (vectorEmbedding (F := F) (E := E) (S := S))
  obtain ⟨iso, hvec⟩ := markedFormIsometry M
  let d := iso.toLinearEquiv
  have hn (v : Fin 8 → E) : norm S (d (1 ⊗ₜ[E] v)) = algebraMap E S (M.q v) :=
    (iso.map_app _).trans (CliffordModel.coefficientForm_tmul S M.q (Pi.basisFun E (Fin 8)) 1 v |>.trans (by simp))
  obtain ⟨f, hf⟩ := geometricEvenClifford (K := E) (S := S) (V := Fin 8 → E)
    M.q (Pi.basisFun E (Fin 8)) d hn
  let a : HalfSpinVertices F E S :=
    ⟨D.numbering.symm (cyclicPrev i), fun h =>
      prev_ne_self i (by simpa only [Equiv.apply_symm_apply] using congrArg D.numbering h)⟩
  let b : HalfSpinVertices F E S :=
    ⟨D.numbering.symm (cyclicNext i), fun h =>
      next_ne_self i (by simpa only [Equiv.apply_symm_apply] using congrArg D.numbering h)⟩
  have ha : D.numbering a.val = cyclicPrev i := D.numbering.apply_symm_apply _
  have hb : D.numbering b.val = cyclicNext i := D.numbering.apply_symm_apply _
  have hj (j : HalfSpinVertices F E S) : j = a ∨ j = b := by
    exact (complement_indices i (D.numbering j.val) (fun h => j.property (D.numbering.injective h))).imp
      (fun h => Subtype.ext (D.numbering.injective (h.trans ha.symm)))
      (fun h => Subtype.ext (D.numbering.injective (h.trans hb.symm)))
  have hab : a ≠ b := fun h => next_ne_prev i (hb.symm.trans ((congrArg (fun j : HalfSpinVertices F E S =>
    D.numbering j.val) h).symm.trans ha))
  let A := Module.End S (Zorn S)
  let route : A × A →ₐ[S] (∀ _ : HalfSpinVertices F E S, A) :=
    AlgHom.pi fun j => if j = a then AlgHom.fst S A A else AlgHom.snd S A A
  have hra (x : A × A) : route x a = x.1 := by simp [route]
  have hrb (x : A × A) : route x b = x.2 := by simp [route, hab.symm]
  let r := AlgEquiv.ofBijective route ⟨fun x y h =>
    Prod.ext ((hra x).symm.trans ((congrFun h a).trans (hra y)))
      ((hrb x).symm.trans ((congrFun h b).trans (hrb y))),
    fun g => ⟨(g a, g b), funext fun j => by
      rcases hj j with rfl | rfl
      · exact hra _
      · exact hrb _⟩⟩
  let bar := conjugate (norm S)
  have hinv : Function.Involutive bar :=
    conjugate_involutive (Zorn.isOctonion S).toNormLaws
  let c : Zorn S ≃ₗ[S] Zorn S :=
    { toFun := bar, invFun := bar, left_inv := hinv, right_inv := hinv
      map_add' := map_add bar, map_smul' := map_smul bar }
  let g := f.trans ((AlgEquiv.prodCongr (c.conjAlgEquiv S) (AlgEquiv.refl : A ≃ₐ[S] A)).trans r)
  refine ⟨g, fun j v w x => ?_⟩
  have hv (y : Fin 8 → E) :
      M.coordinates (extendAlbertVector M.albert (M.vector y).val) =
        singleBlockCoordinates i (d (1 ⊗ₜ[E] y)) := hvec y
  let v' := d (1 ⊗ₜ[E] v)
  let w' := d (1 ⊗ₜ[E] w)
  let y := (1 : S) ⊗ₜ[E] (CliffordAlgebra.even.ι M.q).bilin v w
  have hbar (p q : Zorn S) : bar (p * q) = bar q * bar p :=
    conjugate_mul (Zorn.isOctonion S).toNormLaws p q
  change g y j x = halfSpinVectorProduct M j v w x
  rcases hj j with rfl | rfl
  · have h₁ : g y a x = bar ((f y).1 (bar x)) := by
      change route _ a x = _
      rw [hra]
      rfl
    have h₂ : (f y).1 (bar x) = v' * (bar w' * bar x) :=
      congrArg Prod.fst (hf v w (bar x, 0))
    rw [h₁, h₂, ← hbar x w']
    unfold halfSpinVectorProduct
    dsimp only
    rw [ha, hv v, hv w, peircePolar_prev, peircePolar_next]
    exact (Pi.single_eq_same (M := fun _ => Zorn S) (cyclicPrev i) _).symm
  · have h₁ : g y b x = (f y).2 x := by
      change route _ b x = _
      rw [hrb]
      rfl
    have h₂ : (f y).2 x = bar v' * (w' * x) := congrArg Prod.snd (hf v w (0, x))
    rw [h₁, h₂]
    unfold halfSpinVectorProduct
    dsimp only
    rw [hb, hv v, hv w, peircePolar_next, peircePolar_prev]
    change bar v' * (w' * x) =
      (Pi.single (cyclicNext i) (bar (bar (w' * x) * v')) : Fin 3 → Zorn S) (cyclicNext i)
    rw [Pi.single_eq_same, hbar, hinv]

end GeometricPeirceAction

section HalfSpinTransport

open LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescentSpecification
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Albert LinearAlgebraicGroups.Composition
open TrialitySpecification (Model modelOp)
open QuadraticOperatorSpecification (triple)
open Composition.ZornSpecification (norm)
open scoped TensorProduct

variable {F E S : Type u} [Field F] [Field E] [Field S]
  [Algebra F E] [Algebra F S] [Algebra E S] [IsScalarTower F E S]
  {G : AffineAlgebraicGroup F} {D : DiagramPresentation G E S}

private def residualHalfSpin (τ : Gal(S/E)) (j : HalfSpinVertices F E S) :
    HalfSpinVertices F E S :=
  ⟨(τ.restrictScalars F).toAlgHom.comp j.val,
    fun h => j.property ((embeddingPermutation (τ.restrictScalars F)).injective
      (h.trans (residual_fixes_marked τ).symm))⟩

set_option maxHeartbeats 3600000 in
private theorem halfSpinCoefficient_intertwines (M : CubicPeirceModel G D)
    (f : (S ⊗[E] CliffordAlgebra.even M.q) ≃ₐ[S]
      (∀ _ : HalfSpinVertices F E S, Module.End S (Zorn S)))
    (hf : ∀ j v w x, f (1 ⊗ₜ[E] (CliffordAlgebra.even.ι M.q).bilin v w) j x =
      halfSpinVectorProduct M j v w x)
    (τ : Gal(S/E)) (j : HalfSpinVertices F E S) (a : CliffordAlgebra.even M.q) (x : Zorn S) :
    let j' := residualHalfSpin τ j
    let A := modelCoefficientAction M.coordinates (τ.restrictScalars F)
    A (singleBlockCoordinates (D.numbering j.val) (f (1 ⊗ₜ[E] a) j x)) =
      singleBlockCoordinates (D.numbering j'.val)
        (f (1 ⊗ₜ[E] a) j' ((A (singleBlockCoordinates (D.numbering j.val) x)).2 (D.numbering j'.val))) := by
  let j' := residualHalfSpin τ j
  let i := D.numbering j.val
  let i' := D.numbering j'.val
  let γ := τ.restrictScalars F
  let A := modelCoefficientAction M.coordinates γ
  let b : Zorn S → Model S := singleBlockCoordinates (R := S) i
  let b' : Zorn S → Model S := singleBlockCoordinates (R := S) i'
  have hb (y : Zorn S) : (b y).2 i = y := Pi.single_eq_same (M := fun _ => Zorn S) _ _
  have hb' (y : Zorn S) : (b' y).2 i' = y := Pi.single_eq_same (M := fun _ => Zorn S) _ _
  have hblock (z : Model S) : z ∈ geometricPeirceBlock i ↔ A z ∈ geometricPeirceBlock i' := by
    have h := modelCoefficientAction_mem_block M.cubic M.coordinates γ M.diagonal M.law i z
    rw [show vertexPermutation (numbering := D.numbering) γ i = i' from
      residual_vertex_transport τ j.val] at h
    exact h
  let T : Zorn S → Zorn S := fun y => (A (b y)).2 i'
  have hT (y : Zorn S) : A (b y) = b' (T y) := by
    symm
    apply (peirceProjection_fixed i' _).mp
    apply (hblock _).mp
    exact (peirceProjection_fixed i _).mpr (congrArg b (hb y))
  have hAi : Function.Injective A := modelCoefficientAction_injective M.coordinates γ
  have hAs : Function.Surjective A := M.coordinates.surjective.comp
    ((TensorProduct.congr γ.toLinearEquiv (LinearEquiv.refl F M.albert.V)).surjective.comp
      M.coordinates.symm.surjective)
  have hTi : Function.Injective T := by
    intro p q h
    have hp : b p = b q := hAi ((hT p).trans (h ▸ (hT q).symm))
    exact (hb p).symm.trans ((congrArg (fun z : Model S => z.2 i) hp).trans (hb q))
  have hTs : Function.Surjective T := by
    intro y
    obtain ⟨z, hz⟩ := hAs (b' y)
    have hz' : b (z.2 i) = z := (peirceProjection_fixed i z).mp ((hblock z).mpr
      (hz ▸ (peirceProjection_fixed i' (b' y)).mpr (congrArg b' (hb' y))))
    exact ⟨z.2 i, by change (A (b (z.2 i))).2 i' = y; rw [hz', hz, hb']⟩
  let ρ := τ.toRingEquiv
  let : RingHomInvPair ρ.toRingHom ρ.symm.toRingHom := RingHomInvPair.of_ringEquiv ρ
  let : RingHomInvPair ρ.symm.toRingHom ρ.toRingHom := RingHomInvPair.of_ringEquiv_symm ρ
  let L : Zorn S →ₛₗ[ρ.toRingHom] Zorn S :=
    { toFun := T
      map_add' := fun y z => by
        change (A (peirceInclusion i (y + z))).2 i' = _
        simp only [A, modelCoefficientAction, map_add, Prod.snd_add, Pi.add_apply]
        rfl
      map_smul' := fun c y => by
        change (A (peirceInclusion i (c • y))).2 i' = _
        rw [map_smul]
        change (modelCoefficientAction M.coordinates γ (c • peirceInclusion i y)).2 i' = _
        rw [modelCoefficientAction_smul]
        rfl }
  let e := LinearEquiv.ofBijective L ⟨hTi, hTs⟩
  let N := Module.End S (Zorn S)
  let : Algebra E (Module.End S (Zorn S)) := Algebra.compHom N (algebraMap E S)
  let : IsScalarTower E S (Module.End S (Zorn S)) := IsScalarTower.of_algebraMap_eq' rfl
  let C : N →ₐ[E] N :=
    { e.conjRingEquiv.toRingHom with
      commutes' := fun r => by
        apply LinearMap.ext
        intro y
        change (e.conjRingEquiv (algebraMap S N (algebraMap E S r))) y =
          (algebraMap E S r) • y
        rw [LinearEquiv.conjRingEquiv_apply_apply]
        change e ((algebraMap E S r) • e.symm y) = _
        rw [map_smulₛₗ, e.apply_symm_apply]
        change τ (algebraMap E S r) • y = _
        rw [τ.commutes] }
  let ι := (Algebra.TensorProduct.includeRight (R := E) (A := S) :
    CliffordAlgebra.even M.q →ₐ[E] S ⊗[E] CliffordAlgebra.even M.q)
  let g (k : HalfSpinVertices F E S) : CliffordAlgebra.even M.q →ₐ[E] N :=
    (((Pi.evalAlgHom S _ k).comp f.toAlgHom).restrictScalars E).comp ι
  have hunit : A (CubicSpecification.cubicUnit : Model S) = CubicSpecification.cubicUnit := by
    rw [← M.unit]
    change M.coordinates (γ.toAlgHom.toLinearMap.rTensor M.albert.V
      (M.coordinates.symm (M.coordinates (1 ⊗ₜ[F] M.albert.law.unit)))) = _
    simp only [LinearEquiv.symm_apply_apply, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]
  let vec (v : Fin 8 → E) :=
    M.coordinates (extendAlbertVector M.albert (M.vector v).val)
  let act (v : Fin 8 → E) (z : Model S) :=
    triple (norm S) (fun _ => 1) (vec v) CubicSpecification.cubicUnit z
  have hv (v : Fin 8 → E) : A (vec v) = vec v :=
    modelCoefficientAction_fix_extend M.coordinates τ (M.vector v).val
  have hadd (p q : Model S) : A (p + q) = A p + A q := by
    simp only [A, modelCoefficientAction, map_add]
  have hsub (p q : Model S) : A (p - q) = A p - A q := by
    simp only [A, modelCoefficientAction, map_sub]
  have hop (p q : Model S) : A (modelOp p q) = modelOp (A p) (A q) :=
    modelCoefficientAction_op M.coordinates γ M.law p q
  have hact (v : Fin 8 → E) (z : Model S) : A (act v z) = act v (A z) := by
    change A (modelOp (vec v + z) CubicSpecification.cubicUnit -
      modelOp (vec v) CubicSpecification.cubicUnit - modelOp z CubicSpecification.cubicUnit) = _
    rw [hsub, hsub, hop, hop, hop, hadd, hv, hunit]
    rfl
  have hgen (v w : Fin 8 → E) (y : Zorn S) :
      T (g j ((CliffordAlgebra.even.ι M.q).bilin v w) y) =
        g j' ((CliffordAlgebra.even.ι M.q).bilin v w) (T y) := by
    let p := act v (act w (b y))
    have hs : p ∈ geometricPeirceBlock i := by
      let k := D.numbering vectorEmbedding
      have hki : i ≠ k := fun h => j.property (D.numbering.injective h)
      rcases complement_indices k i hki with h | h
      · change triple (norm S) (fun _ => 1) (vec v) CubicSpecification.cubicUnit
          (triple (norm S) (fun _ => 1) (vec w) CubicSpecification.cubicUnit (b y)) ∈
            geometricPeirceBlock i
        rw [show vec v = singleBlockCoordinates k ((vec v).2 k) from
          (peirceInclusion_coordinate M.coordinates k (M.vector v)).symm,
          show vec w = singleBlockCoordinates k ((vec w).2 k) from
          (peirceInclusion_coordinate M.coordinates k (M.vector w)).symm]
        change triple (norm S) (fun _ => 1) _ CubicSpecification.cubicUnit
          (triple (norm S) (fun _ => 1) _ CubicSpecification.cubicUnit (singleBlockCoordinates i y)) ∈ _
        rw [h, peircePolar_prev, peircePolar_next, peirceProjection_fixed]
        simp [CubicSpecification.singleBlockCoordinates]
      · change triple (norm S) (fun _ => 1) (vec v) CubicSpecification.cubicUnit
          (triple (norm S) (fun _ => 1) (vec w) CubicSpecification.cubicUnit (b y)) ∈
            geometricPeirceBlock i
        rw [show vec v = singleBlockCoordinates k ((vec v).2 k) from
          (peirceInclusion_coordinate M.coordinates k (M.vector v)).symm,
          show vec w = singleBlockCoordinates k ((vec w).2 k) from
          (peirceInclusion_coordinate M.coordinates k (M.vector w)).symm]
        change triple (norm S) (fun _ => 1) _ CubicSpecification.cubicUnit
          (triple (norm S) (fun _ => 1) _ CubicSpecification.cubicUnit (singleBlockCoordinates i y)) ∈ _
        rw [h, peircePolar_next, peircePolar_prev, peirceProjection_fixed]
        simp [CubicSpecification.singleBlockCoordinates]
    change T (f (1 ⊗ₜ[E] (CliffordAlgebra.even.ι M.q).bilin v w) j y) =
      f (1 ⊗ₜ[E] (CliffordAlgebra.even.ι M.q).bilin v w) j' (T y)
    rw [hf, hf]
    have hp₀ : b (p.2 i) = p := (peirceProjection_fixed i p).mp hs
    have hp : A (b (p.2 i)) = act v (act w (b' (T y))) := by
      rw [hp₀, ← hT y, ← hact, ← hact]
    have hprod (k : HalfSpinVertices F E S) (z : Zorn S) :
        halfSpinVectorProduct M k v w z =
          (act v (act w (singleBlockCoordinates (D.numbering k.val) z))).2 (D.numbering k.val) := by
      simp only [halfSpinVectorProduct, act, vec]
    rw [hprod, hprod]
    have hcoord : (A (b (p.2 i))).2 i' = (act v (act w (b' (T y)))).2 i' :=
      congrArg (fun z : Model S => z.2 i') hp
    simpa only [T, p, b, b', i, i'] using hcoord
  have hg : C.comp (g j) = g j' := by
    apply CliffordAlgebra.even.algHom_ext
    apply CliffordAlgebra.EvenHom.ext
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro y
    change (e.conjRingEquiv (g j ((CliffordAlgebra.even.ι M.q).bilin v w))) y =
      g j' ((CliffordAlgebra.even.ι M.q).bilin v w) y
    rw [LinearEquiv.conjRingEquiv_apply_apply]
    have h := hgen v w (e.symm y)
    change e (g j ((CliffordAlgebra.even.ι M.q).bilin v w) (e.symm y)) =
      g j' ((CliffordAlgebra.even.ι M.q).bilin v w) (e (e.symm y)) at h
    simpa only [LinearEquiv.apply_symm_apply] using h
  have ha := DFunLike.congr_fun hg a
  have hax := DFunLike.congr_fun ha (e x)
  change (e.conjRingEquiv (g j a)) (e x) = g j' a (e x) at hax
  rw [LinearEquiv.conjRingEquiv_apply_apply, LinearEquiv.symm_apply_apply] at hax
  change T (f (1 ⊗ₜ[E] a) j x) = f (1 ⊗ₜ[E] a) j' (T x) at hax
  change A (b (f (1 ⊗ₜ[E] a) j x)) = b' (f (1 ⊗ₜ[E] a) j' (T x))
  rw [hT, hax]

end HalfSpinTransport

section GeometricCliffordCenter

open LinearAlgebraicGroups.Albert LinearAlgebraicGroups.Composition
open scoped TensorProduct

variable {K S A : Type u} [Field K] [Field S] [Algebra K S] [Ring A] [Algebra K A]

private theorem centralTensor (z : Subalgebra.center K A) :
    (1 ⊗ₜ[K] z.val : S ⊗[K] A) ∈ Subalgebra.center S (S ⊗[K] A) := by
  rw [Subalgebra.mem_center_iff]
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s a =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul, (Subalgebra.mem_center_iff.mp z.property) a]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]

private theorem tensorCenter_surjective (x : S ⊗[K] A)
    (hx : x ∈ Subalgebra.center S (S ⊗[K] A)) :
    ∃ z : S ⊗[K] Subalgebra.center K A,
      Algebra.TensorProduct.map (AlgHom.id S S) (Subalgebra.center K A).val z = x := by
  classical
  let b := Module.Basis.ofVectorSpace K S
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := A) b
  have hleft (a : A) (y : S ⊗[K] A) (i : Module.Basis.ofVectorSpaceIndex K S) :
      e ((1 ⊗ₜ[K] a) * y) i = a * e y i := by
    induction y using TensorProduct.inductionOn with
    | tmul s c =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      simp only [e, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, mul_smul_comm]
    | add y z hy hz => simp only [mul_add, map_add, Finsupp.add_apply, hy, hz]
  have hright (a : A) (y : S ⊗[K] A) (i : Module.Basis.ofVectorSpaceIndex K S) :
      e (y * (1 ⊗ₜ[K] a)) i = e y i * a := by
    induction y using TensorProduct.inductionOn with
    | tmul s c =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      simp only [e, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, smul_mul_assoc]
    | add y z hy hz => simp only [add_mul, map_add, Finsupp.add_apply, hy, hz]
  have hc (i : Module.Basis.ofVectorSpaceIndex K S) : e x i ∈ Subalgebra.center K A := by
    rw [Subalgebra.mem_center_iff]
    intro a
    rw [← hleft, ← hright, (Subalgebra.mem_center_iff.mp hx) (1 ⊗ₜ[K] a)]
  refine ⟨∑ i ∈ (e x).support, b i ⊗ₜ[K] ⟨e x i, hc i⟩, ?_⟩
  have hrepr : (∑ i ∈ (e x).support, b i ⊗ₜ[K] e x i) = x := by
    have h := e.symm_apply_apply x
    change (TensorProduct.equivFinsuppOfBasisLeft b).symm (e x) = x at h
    rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply] at h
    exact h
  refine Eq.trans ?_ hrepr
  rw [map_sum]
  exact Finset.sum_congr rfl (fun _ _ => rfl)

private theorem characterOfProduct {L : Type v} [Fintype L] (g : (L → S) →ₐ[S] S) :
    ∃ j : L, ∀ x, g x = x j := by
  classical
  have hsum : (∑ j : L, (Pi.single j (1 : S) : L → S)) = 1 := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hex : ∃ j : L, g (Pi.single j (1 : S)) ≠ 0 := by
    by_contra! h
    have h' := congrArg g hsum
    exact zero_ne_one (by simpa only [map_one, map_sum, h, Finset.sum_const_zero] using h')
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, fun x => ?_⟩
  let e : L → S := Pi.single j 1
  have h : x * e = x j • e := by
    funext k
    by_cases hk : k = j
    · subst k
      simp [e]
    · simp [e, Pi.single_eq_of_ne hk]
  have he := congrArg g h
  rw [map_mul, map_smul, smul_eq_mul] at he
  exact mul_right_cancel₀ hj he

private theorem zorn_one_ne_zero (S : Type u) [Field S] : (1 : Zorn S) ≠ 0 := by
  intro h
  apply (one_ne_zero : (1 : S) ≠ 0)
  simpa using congrArg (ZornSpecification.norm S) h

private theorem geometricCenterEvaluations {L : Type v} [Fintype L]
    (f : (S ⊗[K] A) ≃ₐ[S] (L → Module.End S (Zorn S))) :
    ∃ χ : L ≃ (Subalgebra.center K A →ₐ[K] S),
      ∀ j z, f (1 ⊗ₜ[K] z.val) j = algebraMap S _ (χ j z) := by
  classical
  let C := Subalgebra.center K A
  let N := Module.End S (Zorn S)
  let : Nontrivial (Zorn S) := ⟨⟨1, 0, zorn_one_ne_zero S⟩⟩
  let : Algebra K (Module.End S (Zorn S)) := Algebra.compHom N (algebraMap K S)
  let : IsScalarTower K S (Module.End S (Zorn S)) := IsScalarTower.of_algebraMap_eq' rfl
  let inc : S ⊗[K] C →ₐ[S] S ⊗[K] A :=
    Algebra.TensorProduct.map (AlgHom.id S S) C.val
  have hinc : Function.Injective inc :=
    Module.Flat.lTensor_preserves_injective_linearMap C.val.toLinearMap Subtype.val_injective
  let α : S →ₐ[S] N := Algebra.ofId S N
  let α' := (AlgEquiv.ofInjective α (algebraMap S N).injective).symm
  let f₀ (j : L) : C →ₐ[K] N :=
    (((Pi.evalAlgHom S _ j).comp f.toAlgHom).restrictScalars K).comp
      ((Algebra.TensorProduct.includeRight (R := K) (A := S)).comp C.val)
  have hc (j : L) (z : C) : f₀ j z ∈ α.range := by
    apply Algebra.mem_bot.mp
    apply (Algebra.IsCentral.out (K := S))
    rw [Subalgebra.mem_center_iff]
    intro a
    let w := f.symm (fun _ => a)
    have h := (Subalgebra.mem_center_iff.mp (centralTensor (S := S) z)) w
    have hl := congrArg (fun y => f y j) h
    change a * f (1 ⊗ₜ[K] z.val) j = f (1 ⊗ₜ[K] z.val) j * a
    simpa only [map_mul, Pi.mul_apply, w, AlgEquiv.apply_symm_apply] using hl
  let χ (j : L) : C →ₐ[K] S :=
    (α'.toAlgHom.restrictScalars K).comp ((f₀ j).codRestrict (α.range.restrictScalars K) (hc j))
  have hχ (j : L) (z : C) : f (1 ⊗ₜ[K] z.val) j = algebraMap S N (χ j z) := by
    exact congrArg Subtype.val
      ((AlgEquiv.ofInjective α (algebraMap S N).injective).apply_symm_apply ⟨f₀ j z, hc j z⟩).symm
  let F : S ⊗[K] C →ₐ[S] (L → S) :=
    AlgHom.pi (fun j => Algebra.TensorProduct.lift (AlgHom.id S S) (χ j) fun _ _ => Commute.all _ _)
  have hF (s : S) (z : C) (j : L) : F (s ⊗ₜ[K] z) j = s * χ j z := by
    change Algebra.TensorProduct.lift (AlgHom.id S S) (χ j) (fun _ _ => Commute.all _ _)
      (s ⊗ₜ[K] z) = _
    rw [Algebra.TensorProduct.lift_tmul]
    rfl
  have hcomp (z : S ⊗[K] C) (j : L) : f (inc z) j = algebraMap S N (F z j) := by
    induction z using TensorProduct.inductionOn with
    | tmul s z =>
      change f (s ⊗ₜ[K] z.val) j = _
      rw [hF, show s ⊗ₜ[K] z.val = s • ((1 : S) ⊗ₜ[K] z.val) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, Pi.smul_apply, hχ,
        map_mul, Algebra.smul_def]
    | add y z hy hz => simp only [map_add, Pi.add_apply, hy, hz]
  have hFi : Function.Injective F := fun x y h => hinc (f.injective (funext fun j =>
    (hcomp x j).trans ((congrArg (algebraMap S N) (congrFun h j)).trans (hcomp y j).symm)))
  have hFs : Function.Surjective F := by
    intro c
    let x := f.symm (fun j => algebraMap S N (c j))
    have hx : x ∈ Subalgebra.center S (S ⊗[K] A) := by
      rw [Subalgebra.mem_center_iff]
      intro y
      apply f.injective
      simp only [map_mul, x, f.apply_symm_apply]
      exact funext fun j => (Algebra.commutes (c j) (f y j)).symm
    obtain ⟨z, hz⟩ := tensorCenter_surjective x hx
    refine ⟨z, funext fun j => (algebraMap S N).injective ?_⟩
    rw [← hcomp, show inc z = x from hz]
    exact congrFun (f.apply_symm_apply _) j
  let e := AlgEquiv.ofBijective F ⟨hFi, hFs⟩
  have hχi : Function.Injective χ := by
    intro j l hjl
    by_contra hne
    obtain ⟨z, hz⟩ := hFs (Pi.single j 1)
    have hF' (y : S ⊗[K] C) : F y j = F y l := by
      induction y using TensorProduct.inductionOn with
      | tmul s z => rw [hF, hF, hjl]
      | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
    have h := hF' z
    rw [hz, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm (show j ≠ l from hne))] at h
    exact one_ne_zero h
  have hχs : Function.Surjective χ := by
    intro φ
    let T := Algebra.TensorProduct.lift (AlgHom.id S S) φ (fun _ _ => Commute.all _ _)
    obtain ⟨j, hj⟩ := characterOfProduct (T.comp e.symm.toAlgHom)
    refine ⟨j, AlgHom.ext fun z => ?_⟩
    have h := hj (e (1 ⊗ₜ[K] z))
    change T (e.symm (e (1 ⊗ₜ[K] z))) = F (1 ⊗ₜ[K] z) j at h
    rw [e.symm_apply_apply, hF, one_mul] at h
    dsimp only [T] at h
    rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, one_mul] at h
    exact h.symm
  exact ⟨Equiv.ofBijective χ ⟨hχi, hχs⟩, hχ⟩

end GeometricCliffordCenter

section LabelledClifford

open LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescentSpecification
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Albert LinearAlgebraicGroups.Composition
open TrialitySpecification (Model)
open scoped TensorProduct

variable {F E S : Type u} [Field F] [Field E] [Field S]
  [Algebra F E] [Algebra F S] [Algebra E S] [IsScalarTower F E S]
  {G : AffineAlgebraicGroup F} {D : DiagramPresentation G E S}

set_option maxHeartbeats 1000000 in
private theorem labelledGeometricClifford [IsGalois E S] (M : CubicPeirceModel G D)
    [FiniteDimensional F M.albert.V] :
    ∃ labels : (Subalgebra.center E (CliffordAlgebra.even M.q) →ₐ[E] S) ≃ HalfSpinVertices F E S,
      LabelsAgree M labels ∧ GeometricCliffordComparison M labels := by
  classical
  let H := HalfSpinVertices F E S
  let : Finite H := Finite.of_injective (fun j : H => D.numbering j.val)
    (fun _ _ h => Subtype.ext (D.numbering.injective h))
  let : Fintype H := Fintype.ofFinite H
  obtain ⟨f, hf⟩ := exists_geometricPeirceAction M
  obtain ⟨χ, hχ⟩ := geometricCenterEvaluations (K := E) (S := S) f
  refine ⟨χ.symm, ?_, f, hf, hχ⟩
  intro τ c
  let j := χ.symm c
  let j' := residualHalfSpin τ j
  have he : τ.toAlgHom.comp (χ j) = χ j' := by
    apply AlgHom.ext
    intro z
    let γ := τ.restrictScalars F
    let A := modelCoefficientAction M.coordinates γ
    let i := D.numbering j.val
    let i' := D.numbering j'.val
    let b := peirceInclusion (S := S) i
    let b' := peirceInclusion (S := S) i'
    let x := (1 : Zorn S)
    let y := (A (b x)).2 i'
    have hy : A (b x) = b' y := by
      symm
      apply (peirceProjection_fixed i' _).mp
      rw [← show vertexPermutation (numbering := D.numbering) γ i = i' from
        residual_vertex_transport τ j.val]
      apply (modelCoefficientAction_mem_block M.cubic M.coordinates γ M.diagonal M.law i _).mp
      apply (peirceProjection_fixed i _).mpr
      exact congrArg b (Pi.single_eq_same (M := fun _ => Zorn S) _ _)
    have hy₀ : y ≠ 0 := by
      intro h
      have hzero : A (b x) = A 0 := by
        rw [hy, h, map_zero]
        simp only [A, modelCoefficientAction, map_zero]
      have hx := congrArg (fun w : Model S => w.2 i)
        ((modelCoefficientAction_injective M.coordinates γ) hzero)
      exact zorn_one_ne_zero S ((Pi.single_eq_same (M := fun _ => Zorn S) i x).symm.trans hx)
    have h := halfSpinCoefficient_intertwines M f hf τ j z.val x
    change A (b (f (1 ⊗ₜ[E] z.val) j x)) = b' (f (1 ⊗ₜ[E] z.val) j' y) at h
    rw [hχ, hχ] at h
    change A (b (χ j z • x)) = b' (χ j' z • y) at h
    rw [map_smul, map_smul] at h
    change modelCoefficientAction M.coordinates γ (χ j z • b x) = _ at h
    rw [modelCoefficientAction_smul] at h
    change (τ (χ j z)) • A (b x) = _ at h
    rw [hy] at h
    have h' : τ (χ j z) • y = χ j' z • y := by
      have h' := congrArg (fun w : Model S => w.2 i') h
      simpa [b', peirceInclusion] using h'
    have hz : (τ (χ j z) - χ j' z) • y = 0 := by rw [sub_smul, h', sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hy₀)
  have hj : χ (residualHalfSpin τ (χ.symm c)) = τ.toAlgHom.comp c := by
    rw [← he]
    change τ.toAlgHom.comp (χ (χ.symm c)) = _
    rw [χ.apply_symm_apply]
  have h := congrArg Subtype.val (χ.symm_apply_eq.mpr hj.symm)
  exact h

end LabelledClifford

section CyclicCliffordDescent

open LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescentSpecification
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Albert LinearAlgebraicGroups.Composition
open TrialitySpecification (Model)
open scoped TensorProduct

attribute [local instance] peirceRestrictedModule peirceRestrictedTower

variable {F E S : Type u} [Field F] [Field E] [Field S]
  [Algebra F E] [Algebra F S] [Algebra E S] [IsScalarTower F E S]
  {G : AffineAlgebraicGroup F} {D : DiagramPresentation G E S}

private theorem peirceCoordinate_injective (M : CubicPeirceModel G D) (i : Fin 3) :
    Function.Injective (peirceCoordinate (E := E) M.coordinates i) := by
  intro x y h
  apply Subtype.ext
  apply extendAlbertVector_injective (J := M.albert) (S := S)
  apply M.coordinates.injective
  rw [← peirceInclusion_coordinate M.coordinates i x, ← peirceInclusion_coordinate M.coordinates i y, h]

set_option maxHeartbeats 1400000 in
private theorem descendedEvenAction [IsGalois E S] (M : CubicPeirceModel G D)
    [FiniteDimensional F M.albert.V] (hres : ResidualActionTrivial F E S)
    (f : (S ⊗[E] CliffordAlgebra.even M.q) ≃ₐ[S]
      (∀ _ : HalfSpinVertices F E S, Module.End S (Zorn S)))
    (hf : ∀ j v w x, f (1 ⊗ₜ[E] (CliffordAlgebra.even.ι M.q).bilin v w) j x =
      halfSpinVectorProduct M j v w x) :
    ∃ g : CliffordAlgebra.even M.q →ₐ[E]
        (∀ j : HalfSpinVertices F E S,
          Module.End E (peirceSpace (E := E) M.coordinates (D.numbering j.val))),
      ∀ a (j : HalfSpinVertices F E S) x,
        peirceCoordinate (E := E) M.coordinates (D.numbering j.val) (g a j x) =
          f (1 ⊗ₜ[E] a) j (peirceCoordinate (E := E) M.coordinates (D.numbering j.val) x) := by
  let H := HalfSpinVertices F E S
  let W (j : H) := ↥(peirceSpace (E := E) M.coordinates (D.numbering j.val))
  let P (j : H) := peirceCoordinate (E := E) M.coordinates (D.numbering j.val)
  have hP (j : H) : Function.Injective (P j) := peirceCoordinate_injective M _
  let N := Module.End S (Zorn S)
  let : Algebra E (Module.End S (Zorn S)) := Algebra.compHom N (algebraMap E S)
  let : IsScalarTower E S (Module.End S (Zorn S)) := IsScalarTower.of_algebraMap_eq' rfl
  let A := CliffordAlgebra.even M.q
  let f₀ (j : H) : A →ₐ[E] N :=
    (((Pi.evalAlgHom S _ j).comp f.toAlgHom).restrictScalars E).comp
      (Algebra.TensorProduct.includeRight (R := E) (A := S))
  have hstab (j : H) (a : A) (x : W j) : f₀ j a (P j x) ∈ LinearMap.range (P j) := by
    let i := D.numbering j.val
    let b := peirceInclusion (S := S) i
    let z := b (f₀ j a (P j x))
    obtain ⟨y, hy⟩ := invariantAlbertVector (E := E) (J := M.albert) (M.coordinates.symm z) (fun τ => by
      apply M.coordinates.injective
      change modelCoefficientAction M.coordinates (τ.restrictScalars F) z = _
      rw [M.coordinates.apply_symm_apply]
      have he : residualHalfSpin τ j = j := Subtype.ext (hres τ j.val)
      have h := halfSpinCoefficient_intertwines M f hf τ j a (P j x)
      dsimp only at h
      rw [he] at h
      change modelCoefficientAction M.coordinates (τ.restrictScalars F) z =
        b (f₀ j a ((modelCoefficientAction M.coordinates (τ.restrictScalars F) (b (P j x))).2 i)) at h
      rw [peirceInclusion_coordinate M.coordinates i x, modelCoefficientAction_fix_extend] at h
      exact h)
    have hz : M.coordinates (extendAlbertVector M.albert y) = z :=
      (congrArg M.coordinates hy).trans (M.coordinates.apply_symm_apply z)
    have hmem : y ∈ peirceSpace (E := E) M.coordinates i := by
      rw [mem_peirceSpace_iff, hz, peirceProjection_fixed]
      exact congrArg b (Pi.single_eq_same (M := fun _ => Zorn S) _ _)
    refine ⟨⟨y, hmem⟩, ?_⟩
    change (M.coordinates (extendAlbertVector M.albert y)).2 i = _
    rw [hz]
    exact Pi.single_eq_same (M := fun _ => Zorn S) _ _
  let e (j : H) := LinearEquiv.ofInjective (P j) (hP j)
  let desc (a : A) (j : H) : Module.End E (W j) :=
    (e j).symm.toLinearMap.comp
      (((f₀ j a).restrictScalars E).comp (P j) |>.codRestrict (LinearMap.range (P j)) (hstab j a))
  have hdesc (a : A) (j : H) (x : W j) : P j (desc a j x) = f₀ j a (P j x) := by
    exact congrArg Subtype.val ((e j).apply_symm_apply ⟨f₀ j a (P j x), hstab j a x⟩)
  let g : A →ₐ[E] (∀ j : H, Module.End E (W j)) :=
    { toFun := desc
      map_one' := funext fun j => LinearMap.ext fun x => hP j (by
        rw [hdesc, map_one]
        rfl)
      map_zero' := funext fun j => LinearMap.ext fun x => hP j (by
        rw [hdesc, map_zero]
        exact (P j).map_zero.symm)
      map_add' := fun a b => funext fun j => LinearMap.ext fun x => hP j (by
        change P j (desc (a + b) j x) = P j (desc a j x + desc b j x)
        rw [hdesc, map_add (f₀ j), map_add (P j), hdesc, hdesc]
        rfl)
      map_mul' := fun a b => funext fun j => LinearMap.ext fun x => hP j (by
        change P j (desc (a * b) j x) = P j (desc a j (desc b j x))
        rw [hdesc, map_mul, hdesc, hdesc]
        rfl)
      commutes' := fun a => funext fun j => LinearMap.ext fun x => hP j (by
        change P j (desc (algebraMap E A a) j x) = P j (a • x)
        rw [hdesc, (f₀ j).commutes, map_smul]
        rfl) }
  exact ⟨g, hdesc⟩

set_option maxHeartbeats 1400000 in
private theorem cyclicCliffordComparison [Module.Finite F E] [IsGalois F E] [Normal F S]
    [IsGalois E S] (M : CubicPeirceModel G D) [FiniteDimensional F M.albert.V]
    (hdeg : Module.finrank F E = 3) (hres : ResidualActionTrivial F E S)
    (labels : (Subalgebra.center E (CliffordAlgebra.even M.q) →ₐ[E] S) ≃ HalfSpinVertices F E S)
    (hl : LabelsAgree M labels) (hf : GeometricCliffordComparison M labels) :
    CyclicCliffordComparison M labels := by
  classical
  have hi (e : E →ₐ[F] S) (τ : Gal(S/E)) :
      vertexPermutation (numbering := D.numbering) (τ.restrictScalars F) (D.numbering e) =
        D.numbering e := (residual_vertex_transport τ e).trans (congrArg D.numbering (hres τ e))
  have hdim (e : E →ₐ[F] S) :
      Module.finrank E (peirceSpace (E := E) M.coordinates (D.numbering e)) = 8 :=
    peirceSpace_finrank M.cubic M.coordinates M.diagonal M.law (D.numbering e) (hi e)
  obtain ⟨f, hfg, hc⟩ := hf
  obtain ⟨g, hg⟩ := descendedEvenAction M hres f hfg
  let H := HalfSpinVertices F E S
  let : Finite H := Finite.of_injective (fun j : H => D.numbering j.val)
    (fun _ _ h => Subtype.ext (D.numbering.injective h))
  let : Fintype H := Fintype.ofFinite H
  let A := ↥(CliffordAlgebra.even M.q)
  let W (j : H) := ↥(peirceSpace (E := E) M.coordinates (D.numbering j.val))
  let P (j : H) : W j →ₗ[E] Zorn S := peirceCoordinate M.coordinates (D.numbering j.val)
  let : Module.Finite E (CliffordAlgebra M.q) := by
    obtain ⟨b, _⟩ := LinearAlgebraicGroups.Albert.CliffordModel.ordered_basis M.q (Pi.basisFun E (Fin 8))
    exact Module.Finite.of_basis b
  let : Module.Finite E A :=
    Module.Finite.of_injective (CliffordAlgebra.even M.q).val.toLinearMap Subtype.val_injective
  let : Module.Free E A := Module.Free.of_divisionRing E A
  let : ∀ j : H, AddCommGroup (W j) := fun j =>
    inferInstanceAs (AddCommGroup ↥(peirceSpace (E := E) M.coordinates (D.numbering j.val)))
  let : ∀ j : H, Module E (W j) := fun j =>
    inferInstanceAs (Module E ↥(peirceSpace (E := E) M.coordinates (D.numbering j.val)))
  let : ∀ j : H, Module.Finite E (W j) := fun j =>
    Module.Finite.of_injective (peirceSpace (E := E) M.coordinates (D.numbering j.val)).subtype
      Subtype.val_injective
  let : ∀ j, Module.Free E (W j) := fun j => Module.Free.of_divisionRing E (W j)
  let : ∀ j, Module.Free E (Module.End E (W j)) :=
    fun j => Module.Free.of_divisionRing E (Module.End E (W j))
  let : Module.Free S (Module.End S (Zorn S)) :=
    Module.Free.of_divisionRing S (Module.End S (Zorn S))
  have hgi : Function.Injective g := by
    let l : A →ₗ[E] (S ⊗[E] A) := (Algebra.linearMap E S).rTensor A ∘ₗ
      (TensorProduct.lid E A).symm.toLinearMap
    have hli : Function.Injective l :=
      (Module.Flat.rTensor_preserves_injective_linearMap (Algebra.linearMap E S)
        (algebraMap E S).injective).comp (TensorProduct.lid E A).symm.injective
    intro a b h
    apply hli
    have hl (x : A) : l x = (1 : S) ⊗ₜ[E] x := by
      simp only [l, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.lid_symm_apply,
        LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
    rw [hl, hl]
    apply f.injective
    funext j
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := peirceCoordinate_baseChange_surjective M.cubic M.coordinates M.diagonal
      M.law (D.numbering j.val) (hi j.val) z
    change f (1 ⊗ₜ[E] a) j ((P j).liftBaseChange S x) =
      f (1 ⊗ₜ[E] b) j ((P j).liftBaseChange S x)
    induction x using TensorProduct.inductionOn with
    | tmul s y =>
      rw [LinearMap.liftBaseChange_tmul, map_smul, map_smul]
      exact congrArg (s • ·) ((hg a j y).symm.trans
        ((congrArg (fun T => P j (T j y)) h).trans (hg b j y)))
    | add x y hx hy => simp only [map_add, hx, hy]
  have hZ : Module.finrank S (Zorn S) = 8 := by
    simpa using Module.finrank_eq_card_basis (Zorn.coordinateBasis S)
  have hn :
      Module.finrank E A = Module.finrank E (∀ j : H, Module.End E (W j)) := by
    rw [← Module.finrank_baseChange (R := S) (M' := A), f.toLinearEquiv.finrank_eq,
      Module.finrank_pi_fintype, Module.finrank_pi_fintype]
    apply Finset.sum_congr rfl
    intro j _
    change Module.finrank S (Zorn S →ₗ[S] Zorn S) =
      Module.finrank E (W j →ₗ[E] W j)
    rw [Module.finrank_linearMap, Module.finrank_linearMap, hZ, show Module.finrank E (W j) = 8 from hdim j.val]
  have hgs : Function.Surjective g := by
    let g' : A →ₗ[E] (∀ j : H, Module.End E (W j)) := g.toLinearMap
    have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := g') hn).mp hgi
    exact hs
  let t := AlgEquiv.ofBijective g ⟨hgi, hgs⟩
  refine ⟨hdim, ?_, cubicPeirceTransport M hdeg, cyclicLabelTransport M hdeg,
    cubicPeirceEndConjugacy M hdeg, t, ?_, ?_⟩
  · intro e
    let U := ↥(peirceSpace (E := E) M.coordinates (D.numbering e))
    have hU : Module.finrank E U = 8 := hdim e
    let : Module.Free E U := Module.Free.of_divisionRing E U
    let : FiniteDimensional E U := Module.finite_of_finrank_pos (by rw [hU]; decide)
    exact ⟨⟨e.restrictNormal' E, AlgHom.ext fun a => e.restrictNormal_commutes E a⟩,
      ⟨LinearMap.toMatrixAlgEquiv (Module.finBasisOfFinrankEq E U hU)⟩⟩
  · intro j z
    let φ := labels.symm j
    have hfix (τ : Gal(S/E)) : τ (φ z) = φ z := by
      have h := hl τ φ
      rw [labels.apply_symm_apply, hres] at h
      have ht : τ.toAlgHom.comp φ = φ :=
        labels.injective (Subtype.ext (h.trans (congrArg Subtype.val (labels.apply_symm_apply j)).symm))
      exact DFunLike.congr_fun ht z
    obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (φ z)).mpr hfix
    refine ⟨a, ?_, ha.symm⟩
    apply LinearMap.ext
    intro x
    apply peirceCoordinate_injective M (D.numbering j.val)
    change P j (g z.val j x) = P j (a • x)
    rw [hg, hc, ← ha, map_smul]
    rfl
  · intro j v w x
    exact (hg ((CliffordAlgebra.even.ι M.q).bilin v w) j x).trans (hfg j v w (P j x))

private theorem cubicCliffordComparisons [Module.Finite F E] [Algebra.IsSeparable F E]
    [IsSepClosure F S] (M : CubicPeirceModel G D) (hdeg : Module.finrank F E = 3) :
    ∃ labels : (Subalgebra.center E (CliffordAlgebra.even M.q) →ₐ[E] S) ≃ HalfSpinVertices F E S,
      LabelsAgree M labels ∧ GeometricCliffordComparison M labels ∧
      (ResidualActionTrivial F E S → IsGalois F E ∧ CyclicCliffordComparison M labels) := by
  let : Algebra.IsSeparable E S := Algebra.isSeparable_tower_top_of_isSeparable F E S
  let : IsSepClosure E S := ⟨IsSepClosure.sep_closed F, inferInstance⟩
  let : FiniteDimensional F M.albert.V :=
    (SplitSpecification.freudenthal_finite_projective M.albert.law M.albert.albert.1).1
  obtain ⟨labels, hl, hgeom⟩ := labelledGeometricClifford M
  refine ⟨labels, hl, hgeom, fun hres => ?_⟩
  let : IsGalois F E := galois_of_trivial_residual_action hres
  exact ⟨inferInstance, cyclicCliffordComparison M hdeg hres labels hl hgeom⟩

end CyclicCliffordDescent

section WittCliffordCenter

open CliffordAlgebra Module

private theorem isField_of_ringEquiv {A B : Type u} [Ring A] [Ring B]
    (e : A ≃+* B) (h : IsField A) : IsField B := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := h.exists_pair_ne
    exact ⟨e a, e b, e.injective.ne hab⟩
  · intro a b
    apply e.symm.injective
    simpa only [map_mul] using h.mul_comm (e.symm a) (e.symm b)
  · intro a ha
    obtain ⟨b, hb⟩ := h.mul_inv_cancel (fun h₀ => ha (e.symm.injective (h₀.trans (map_zero e.symm).symm)))
    refine ⟨e b, ?_⟩
    rw [← e.apply_symm_apply a, ← map_mul, hb, map_one]

set_option maxHeartbeats 1000000 in
private theorem binaryCliffordCenter_field {K : Type u} [Field K]
    (q : QuadraticForm K (Fin 2 → K)) (hq : IsRegular q) (ha : ¬ IsIsotropic q) :
    IsField (Subalgebra.center K (even q)) := by
  classical
  by_cases h₂ : (2 : K) = 0
  · have hchar : ringChar K = 2 := CharP.ringChar_of_prime_eq_zero Nat.prime_two (by exact h₂)
    let : CharP K 2 := hchar ▸ ringChar.charP K
    let b : Basis (Fin 1 ⊕ Fin 1) K (Fin 2 → K) :=
      (Pi.basisFun K (Fin 2)).reindex (finSumFinEquiv (m := 1) (n := 1)).symm
    let s : Fin 1 ⊕ Fin 1 := Sum.inl 0
    let t : Fin 1 ⊕ Fin 1 := Sum.inr 0
    have hself (x : Fin 2 → K) : q.polarBilin x x = 0 := by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul, ← two_mul, h₂, zero_mul]
    let d := q.polarBilin (b s) (b t)
    have hd : d ≠ 0 := by
      intro h
      have hz : q.polarBilin (b s) = 0 := by
        apply b.ext
        rintro (i | i)
        · have hi : i = 0 := Subsingleton.elim _ _
          subst i
          exact hself _
        · have hi : i = 0 := Subsingleton.elim _ _
          subst i
          exact h
      exact b.ne_zero s (LinearMap.ker_eq_bot'.mp hq _ hz)
    let b' : Basis (Fin 1 ⊕ Fin 1) K (Fin 2 → K) :=
      b.unitsSMul (fun i => i.elim (fun _ => 1) (fun _ => (Units.mk0 d hd)⁻¹))
    have hsymb : IsSymplecticBasis q b' := by
      refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
      all_goals
        have hi : i = 0 := Subsingleton.elim _ _
        have hj : j = 0 := Subsingleton.elim _ _
        subst i
        subst j
      · exact hself _
      · exact hself _
      · simp only [ite_true, b', Basis.unitsSMul_apply, Sum.elim_inl, Sum.elim_inr, one_smul]
        change (q.polarBilin (b s)) ((d⁻¹ : K) • b t) = 1
        rw [map_smul, smul_eq_mul]
        exact inv_mul_cancel₀ hd
    obtain ⟨e, _, _⟩ := arf_center q b' (by decide) hsymb
    obtain ⟨_, _, hF, _⟩ := binaryNorm q b' hsymb ha
    exact isField_of_ringEquiv e.toRingEquiv hF
  · let : Invertible (2 : K) := (isUnit_iff_ne_zero.mpr h₂).invertible
    obtain ⟨b₀, hO₀⟩ := LinearMap.BilinForm.exists_orthogonal_basis
      (B := QuadraticMap.associated (R := K) q) ⟨QuadraticMap.associated_isSymm K q⟩
    have hdim : finrank K (Fin 2 → K) = 2 := by simp
    let b : Basis (Fin 2) K (Fin 2 → K) := b₀.reindex (finCongr hdim)
    have hOB : (QuadraticMap.associated (R := K) q).IsOrthoᵢ b := by
      intro i j hij
      change QuadraticMap.associated (R := K) q (b i) (b j) = 0
      dsimp only [b]
      rw [Basis.reindex_apply, Basis.reindex_apply]
      exact hO₀ ((finCongr hdim).symm.injective.ne hij)
    have hO (i j : Fin 2) (hij : i ≠ j) : q.polarBilin (b i) (b j) = 0 := by
      rw [← QuadraticMap.two_nsmul_associated (S := K)]
      change 2 • QuadraticMap.associated (R := K) q (b i) (b j) = 0
      rw [hOB hij, smul_zero]
    have hd : signedDiscriminant (n := 1) q b = -(q (b 0) * q (b 1)) := by
      rw [signed_discriminant_diagonal (n := 1) q b h₂ hO]
      simp [Fin.prod_univ_two]
    have ha₀ : q (b 0) ≠ 0 := by
      intro h
      apply ha
      exact ⟨(b 0 : Fin 2 → K), b.ne_zero 0, h⟩
    let : Fact (∀ r : K, r ^ 2 ≠ signedDiscriminant (n := 1) q b + 0 * r) := ⟨by
      intro r hr
      rw [zero_mul, add_zero, hd] at hr
      let x := (r / q (b 0)) • b 0 + b 1
      have hx : x ≠ 0 := by
        intro h
        have hc := congrArg (fun z => b.repr z 1) h
        have hn : (0 : Fin 2) ≠ 1 := by decide
        simp [x, Ne.symm hn] at hc
      apply ha
      refine ⟨x, hx, ?_⟩
      have ho : q.polarBilin ((r / q (b 0)) • b 0) (b 1) = 0 := by
        rw [map_smul, LinearMap.smul_apply, hO 0 1 (by decide), smul_zero]
      have hh := QuadraticMap.polarBilin_apply_apply q ((r / q (b 0)) • b 0) (b 1)
      rw [ho, QuadraticMap.polar] at hh
      have hsum : q (((r / q (b 0)) • b 0) + b 1) =
          q ((r / q (b 0)) • b 0) + q (b 1) := by linear_combination -hh
      change q (((r / q (b 0)) • b 0) + b 1) = 0
      rw [hsum, q.map_smul, smul_eq_mul]
      calc
        (r / q (b 0)) * (r / q (b 0)) * q (b 0) + q (b 1) =
            r ^ 2 / q (b 0) + q (b 1) := by field_simp
        _ = 0 := by rw [hr]; field_simp; ring⟩
    obtain ⟨e, _⟩ := discriminant_center q (n := 1) b h₂ (by decide) hq hO
    exact isField_of_ringEquiv e.toRingEquiv (Field.toIsField _)

open private isometry_grade from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinInnerDescent

variable {K : Type u} [Field K]

private noncomputable def centerEquiv {A B : Type v} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (e : A ≃ₐ[K] B) : Subalgebra.center K A ≃ₐ[K] Subalgebra.center K B :=
  { Subring.centerCongr e.toRingEquiv with commutes' := fun x => Subtype.ext (e.commutes x) }

private noncomputable def matrixCenterEquiv {A : Type v} [Ring A] [Algebra K A] :
    Subalgebra.center K (Matrix (Fin 2) (Fin 2) A) ≃ₐ[K] Subalgebra.center K A := by
  let s : A →ₐ[K] Matrix (Fin 2) (Fin 2) A := Matrix.scalarAlgHom (Fin 2) K
  have hs : Function.Injective s := by
    intro a b h
    have hh := congrArg (fun x : Matrix (Fin 2) (Fin 2) A => x 0 0) h
    simpa [s] using hh
  exact ((Subalgebra.center K (Matrix (Fin 2) (Fin 2) A)).equivOfEq _
    Matrix.subalgebraCenter_eq_scalarAlgHom_map).trans
      ((Subalgebra.center K A).equivMapOfInjective s hs).symm

private noncomputable def evenIsometryEquiv {V W : Type u} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {q : QuadraticForm K V} {q' : QuadraticForm K W}
    (e : q.IsometryEquiv q') : even q ≃ₐ[K] even q' := by
  let a := equivOfIsometry e
  have h : (even q).map a.toAlgHom = even q' := by
    apply Subalgebra.toSubmodule_injective
    exact isometry_grade e 0
  exact (a.subalgebraMap (even q)).trans ((even q).map a.toAlgHom |>.equivOfEq (even q') h)

private noncomputable def onePlaneIso :
    (hyperbolic K 1).IsometryEquiv (plane (K := K)) := by
  let I := ULift.{u} (Fin 1)
  let a : (I → K) ≃ₗ[K] K := LinearEquiv.funUnique I K K
  refine ⟨(LinearEquiv.sumArrowLequivProdArrow I I K K).trans (a.prodCongr a), ?_⟩
  intro x
  rw [hyperbolic_one_apply, plane_apply]
  rfl

private noncomputable def hyperbolicProductStep {V : Type u} [AddCommGroup V] [Module K V]
    (q : QuadraticForm K V) (m : ℕ) :
    ((hyperbolic K (m + 1)).prod q).IsometryEquiv (((hyperbolic K m).prod q).prod (hyperbolic K 1)) := by
  let M₁ := K × K
  let M₂ := Indices (ULift.{u} (Fin m)) → K
  let d := (hyperbolicSucc (K := K) m).symm
  let e := (d.toLinearEquiv.prodCongr (LinearEquiv.refl K V)).trans
    ((LinearEquiv.prodAssoc K M₁ M₂ V).trans
      ((LinearEquiv.prodComm K M₁ (M₂ × V)).trans
        ((LinearEquiv.refl K (M₂ × V)).prodCongr (onePlaneIso (K := K)).symm.toLinearEquiv)))
  refine ⟨e, fun x => ?_⟩
  change (((hyperbolic K m) ((d x.1).2) + q x.2) +
    (hyperbolic K 1) ((onePlaneIso (K := K)).symm ((d x.1).1))) =
      (hyperbolic K (m + 1)) x.1 + q x.2
  rw [(onePlaneIso (K := K)).symm.map_app]
  rw [← d.map_app]
  simp only [QuadraticMap.prod_apply]
  abel

set_option maxHeartbeats 600000 in
private theorem center_hyperbolicProduct {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (q : QuadraticForm K V) (hx : ∃ x, q x ≠ 0) (m : ℕ) :
    Nonempty (Subalgebra.center K (even ((hyperbolic K m).prod q)) ≃ₐ[K]
      Subalgebra.center K (even q)) := by
  induction m with
  | zero =>
    let : IsEmpty (Indices (ULift.{u} (Fin 0))) := inferInstance
    let : Unique (Indices (ULift.{u} (Fin 0)) → K) := ⟨⟨0⟩, fun x => funext fun i => isEmptyElim i⟩
    let e : ((hyperbolic K 0).prod q).IsometryEquiv q :=
      ⟨LinearEquiv.uniqueProd, fun x => by
        change q x.2 = (hyperbolic K 0) x.1 + q x.2
        rw [show x.1 = 0 from Subsingleton.elim _ _, map_zero, zero_add]⟩
    exact ⟨centerEquiv (evenIsometryEquiv e)⟩
  | succ m ih =>
    let p := (hyperbolic K m).prod q
    obtain ⟨x, hx⟩ := hx
    have hpx : p (0, x) ≠ 0 := by simpa [p] using hx
    obtain ⟨a⟩ := even_plane_matrix p hpx
    obtain ⟨b⟩ := ih
    let e := centerEquiv (evenIsometryEquiv (hyperbolicProductStep q m))
    let e' := centerEquiv a
    exact ⟨e.trans (e'.trans (matrixCenterEquiv.trans b))⟩

end WittCliffordCenter

section CyclicWittIndex

open LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescentSpecification
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Albert (cyclicNext cyclicPrev)
open CliffordAlgebra

variable {F E S : Type u} [Field F] [Field E] [Field S]
  [Algebra F E] [Algebra F S] [Algebra E S] [IsScalarTower F E S]
  {G : AffineAlgebraicGroup F} {D : DiagramPresentation G E S}

set_option maxHeartbeats 1600000 in
private theorem no_binary_kernel_of_cyclicComparison (M : CubicPeirceModel G D)
    (labels : (Subalgebra.center E (even M.q) →ₐ[E] S) ≃ HalfSpinVertices F E S)
    (hC : CyclicCliffordComparison M labels)
    (q : QuadraticForm E (Fin 2 → E)) (hq : IsRegular q) (ha : ¬ IsIsotropic q) (m : ℕ) :
    ¬ M.q.Equivalent ((hyperbolic E m).prod q) := by
  rintro ⟨p⟩
  obtain ⟨hdim, _, _, _, _, f, _, _⟩ := hC
  have hx : ∃ x, q x ≠ 0 := by
    let x : Fin 2 → E := 1
    have hx : x ≠ 0 := fun h => one_ne_zero (congrFun h 0)
    exact ⟨x, fun h => ha ⟨x, hx, h⟩⟩
  obtain ⟨C⟩ := center_hyperbolicProduct q hx m
  let e := centerEquiv (evenIsometryEquiv p) |>.trans C
  have hF : IsField (Subalgebra.center E (even M.q)) :=
    isField_of_ringEquiv e.symm.toRingEquiv (binaryCliffordCenter_field q hq ha)
  let i := D.numbering (vectorEmbedding (F := F) (E := E) (S := S))
  let a : HalfSpinVertices F E S :=
    ⟨D.numbering.symm (cyclicNext i), fun h =>
      next_ne_self i (by simpa only [Equiv.apply_symm_apply] using congrArg D.numbering h)⟩
  let b : HalfSpinVertices F E S :=
    ⟨D.numbering.symm (cyclicPrev i), fun h =>
      prev_ne_self i (by simpa only [Equiv.apply_symm_apply] using congrArg D.numbering h)⟩
  have hab : a ≠ b := fun h => next_ne_prev i (D.numbering.symm.injective (congrArg Subtype.val h))
  let : ∀ j : HalfSpinVertices F E S,
      Nontrivial ↥(peirceSpace (E := E) M.coordinates (D.numbering j.val)) := fun j => by
    apply Module.nontrivial_of_finrank_pos (R := E)
    rw [hdim]
    decide
  classical
  let A (j : HalfSpinVertices F E S) :=
    Module.End E (peirceSpace (E := E) M.coordinates (D.numbering j.val))
  let y : ∀ j, A j := Pi.single a 1
  have hcentral : f.symm y ∈ Subalgebra.center E (even M.q) := by
    rw [Subalgebra.mem_center_iff]
    intro z
    apply f.injective
    rw [map_mul, map_mul, f.apply_symm_apply]
    funext j
    by_cases hj : j = a
    · subst j
      simp [y]
    · simp [y, Pi.single_eq_of_ne hj]
  let c : Subalgebra.center E (even M.q) := ⟨f.symm y, hcentral⟩
  have hc : f c.val = y := f.apply_symm_apply y
  have hc₀ : c ≠ 0 := by
    intro h
    have h' := congrFun (hc.symm.trans ((congrArg (fun z : Subalgebra.center E (even M.q) =>
      f z.val) h).trans (map_zero f))) a
    let : Nontrivial (A a) := by dsimp [A]; infer_instance
    simp [y] at h'
  have hc₁ : c ≠ 1 := by
    intro h
    have h' := congrFun (hc.symm.trans ((congrArg (fun z : Subalgebra.center E (even M.q) =>
      f z.val) h).trans (map_one f))) b
    let : Nontrivial (A b) := by dsimp [A]; infer_instance
    simp [y, Pi.single_eq_of_ne hab.symm] at h'
  have hcc : c * c = c := by
    apply Subtype.ext
    apply f.injective
    change f (c.val * c.val) = f c.val
    rw [map_mul, hc]
    funext j
    by_cases hj : j = a
    · subst j
      simp [y]
    · simp [y, Pi.single_eq_of_ne hj]
  obtain ⟨d, hd⟩ := hF.mul_inv_cancel hc₀
  have hh := congrArg (fun z => z * d) hcc
  rw [mul_assoc, hd, mul_one] at hh
  exact hc₁ hh

end CyclicWittIndex

theorem localWittDecomposition : LocalWittDecomposition.{u, v} :=
  localWitt

theorem discriminantCenter : DiscriminantCenter.{u, v} :=
  discriminant_center

theorem arfCenter : ArfCenter.{u, v} :=
  arf_center

theorem charTwoBinaryNorm : CharTwoBinaryNorm.{u, v} :=
  binaryNorm

theorem oddQuaternionKernel : OddQuaternionKernel.{u, v} :=
  odd_quaternion_kernel

theorem symbolIdentities : SymbolIdentities.{u} :=
  symbol_identities

theorem localNormGroups : LocalNormGroups.{u} :=
  local_norm_groups

theorem charTwoQuaternionKernel : CharTwoQuaternionKernel.{u, v} :=
  char_two_quaternion_kernel

theorem hyperbolicCliffordFactors : HyperbolicCliffordFactors.{u, v} :=
  hyperbolic_clifford_factors

noncomputable section

open LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescentSpecification
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Albert (cyclicNext)
open CliffordAlgebra Module
open private oneMatrixEquiv from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.Equivalence

section WittAssembly

variable {K : Type u} [Field K]

private theorem exists_polar_pair {V : Type u} [AddCommGroup V] [Module K V]
    (q : QuadraticForm K V) (hr : IsRegular q) {x : V} (hx : x ≠ 0) :
    ∃ y : V, q.polarBilin x y = 1 := by
  have hneq : q.polarBilin x ≠ 0 := fun h => hx (LinearMap.ker_eq_bot'.mp hr x h)
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp hneq
  have hy' : q.polarBilin x y ≠ 0 := hy
  exact ⟨(q.polarBilin x y)⁻¹ • y, by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy']⟩

set_option maxHeartbeats 950000 in
private theorem exists_symplectic_basis_four {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [CharP K 2] (q : QuadraticForm K V)
    (hr : IsRegular q) (hd : finrank K V = 4) :
    ∃ b : Basis (Fin 2 ⊕ Fin 2) K V, IsSymplecticBasis q b := by
  classical
  let B := q.polarBilin
  have hal (x : V) : B x x = 0 := by
    rw [show B = q.polarBilin by rfl, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_self, two_nsmul, ← two_mul, CharTwo.two_eq_zero, zero_mul]
  have hs (x y : V) : B x y = B y x := polarSymm q x y
  obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 := by
    let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    exact exists_ne 0
  obtain ⟨y, hxy⟩ := exists_polar_pair q hr hx
  have hyx : B y x = 1 := (hs y x).trans hxy
  let p : V →ₗ[K] K × K := (B x).prod (B y)
  have hk₀ : p.ker ≠ ⊥ := by
    intro h
    have hle := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp h)
    simp [hd, Module.finrank_prod] at hle
  obtain ⟨z, hz, hzn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk₀
  have hzx : B x z = 0 := congrArg Prod.fst (LinearMap.mem_ker.mp hz)
  have hzy : B y z = 0 := congrArg Prod.snd (LinearMap.mem_ker.mp hz)
  obtain ⟨w, hzw⟩ := exists_polar_pair q hr hzn
  let t : V := w - (B y w • x + B x w • y)
  have hxt : B x t = 0 := by simp [t, hal, show B x y = 1 from hxy]
  have hyt : B y t = 0 := by simp [t, hal, hyx]
  have hzt : B z t = 1 := by
    simp [t, show B z w = 1 from hzw, ← hs x z, ← hs y z, hzx, hzy]
  let a : Fin 2 ⊕ Fin 2 → V := Sum.elim ![x,z] ![y,t]
  have hxx (i j : Fin 2) : B (a (.inl i)) (a (.inl j)) = 0 := by
    fin_cases i <;> fin_cases j <;> simp [a, hal, hzx, ← hs x z]
  have hyy (i j : Fin 2) : B (a (.inr i)) (a (.inr j)) = 0 := by
    fin_cases i <;> fin_cases j <;> simp [a, hal, hyt, ← hs y t]
  have hxy' (i j : Fin 2) : B (a (.inl i)) (a (.inr j)) = if i = j then 1 else 0 := by
    fin_cases i <;> fin_cases j <;>
      simp [a, show B x y = 1 from hxy, hxt, hzt, hzy, ← hs y z]
  have hyx' (i j : Fin 2) : B (a (.inr i)) (a (.inl j)) = if j = i then 1 else 0 :=
    (hs _ _).trans (hxy' j i)
  have ha : LinearIndependent K a := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    cases i with
    | inl i =>
      have hh := congrArg (B (a (.inr i))) hg
      fin_cases i <;> simpa [Fintype.sum_sum_type, map_sum, smul_eq_mul,
        hyx', hyy, mul_ite] using hh
    | inr i =>
      have hh := congrArg (B (a (.inl i))) hg
      fin_cases i <;> simpa [Fintype.sum_sum_type, map_sum, smul_eq_mul, hxx, hxy', mul_ite] using hh
  let b := Basis.mk ha ((ha.span_eq_top_of_card_eq_finrank (by simp [hd])).ge)
  have hb : (b : Fin 2 ⊕ Fin 2 → V) = a := Basis.coe_mk _ _
  refine ⟨b, ?_⟩
  unfold IsSymplecticBasis
  rw [hb]
  exact ⟨hxx, hyy, hxy'⟩

private theorem fourSpaceDivisionFactors [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (q : QuadraticForm K (Fin 4 → K))
    (hr : IsRegular q) (ha : ¬ IsIsotropic q) :
    ∃ (a b c : K) (_h : _root_.Specs.RM03.CSA.isCentralSimple K (QuaternionAlgebra K a b c)),
      (∀ x : QuaternionAlgebra K a b c, x ≠ 0 → IsUnit x) ∧
        HasEvenDivisionClass (D := QuaternionAlgebra K a b c) q := by
  by_cases h₂ : (2 : K) = 0
  · have hc : ringChar K = 2 := CharP.ringChar_of_prime_eq_zero Nat.prime_two h₂
    let : CharP K 2 := hc ▸ ringChar.charP K
    obtain ⟨b, hb⟩ := exists_symplectic_basis_four q hr (by simp)
    obtain ⟨_, _, _, _, h, hu, _, hq⟩ := charTwoQuaternionKernel q b hb ha
    exact ⟨_, 1, _, h, hu, hq⟩
  · obtain ⟨_, a, c, _, _, _, h, hu, _, _, hq⟩ :=
      oddQuaternionKernel q (Pi.basisFun K (Fin 4)) h₂ hr ha
    exact ⟨a, 0, c, h, hu, hq⟩

private noncomputable def hyperbolicZeroKernel (q : QuadraticForm K (Fin 0 → K)) (m : ℕ) :
    ((hyperbolic K m).prod q).IsometryEquiv (hyperbolic K m) := by
  let : Unique (Fin 0 → K) := ⟨⟨0⟩, fun x => funext fun i => Fin.elim0 i⟩
  refine ⟨LinearEquiv.prodUnique, ?_⟩
  intro x
  change hyperbolic K m x.1 = hyperbolic K m x.1 + q x.2
  rw [show x.2 = 0 from Subsingleton.elim _ _, map_zero, add_zero]

private noncomputable def hyperbolicLeftZero {V : Type u} [AddCommGroup V] [Module K V]
    (q : QuadraticForm K V) : ((hyperbolic K 0).prod q).IsometryEquiv q := by
  let : IsEmpty (Indices (ULift.{u} (Fin 0))) := inferInstance
  let : Unique (Indices (ULift.{u} (Fin 0)) → K) := ⟨⟨0⟩, fun x => funext fun i => isEmptyElim i⟩
  refine ⟨LinearEquiv.uniqueProd, ?_⟩
  intro x
  change q x.2 = (hyperbolic K 0) x.1 + q x.2
  rw [show x.1 = 0 from Subsingleton.elim _ _, map_zero, zero_add]

set_option maxHeartbeats 750000 in
private theorem hyperbolicProductDivisionClass {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {D : Type u} [Ring D] [Algebra K D]
    (q : QuadraticForm K V) (hx : ∃ x, q x ≠ 0) (m : ℕ)
    (hD : HasEvenDivisionClass (D := D) q) :
    HasEvenDivisionClass (D := D) ((hyperbolic K m).prod q) := by
  induction m with
  | zero =>
    obtain ⟨A, B, ⟨f⟩, ha, hb⟩ := hD
    exact ⟨A, B, ⟨(evenIsometryEquiv (hyperbolicLeftZero q)).trans f⟩, ha, hb⟩
  | succ m ih =>
    obtain ⟨A, B, ⟨f⟩, ha, hb⟩ := ih
    let p := (hyperbolic K m).prod q
    obtain ⟨x, hx⟩ := hx
    have hp : p (0, x) ≠ 0 := by simpa [p] using hx
    obtain ⟨a⟩ := even_plane_matrix p hp
    let A' := matrixCSA A
    let B' := matrixCSA B
    let a' : A' ≃ₐ[K] Matrix (Fin 2) (Fin 2) A := ULift.algEquiv
    let b' : B' ≃ₐ[K] Matrix (Fin 2) (Fin 2) B := ULift.algEquiv
    let f' := a.trans (f.mapMatrix.trans (matrixProd.trans (AlgEquiv.prodCongr a'.symm b'.symm)))
    -- Flatten the matrix enlargement into the positive size already in the equivalence.
    have step (C : _root_.CSA.{u,u} K) (C' : Type u) [Ring C'] [Algebra K C']
        (e : C' ≃ₐ[K] Matrix (Fin 2) (Fin 2) C)
        (h : _root_.Specs.RM03.Brauer.equivalent K C D) :
        _root_.Specs.RM03.Brauer.equivalent K C' D := by
      obtain ⟨r, s, hr, hs, ⟨g⟩⟩ := h
      let g' := (Matrix.compAlgEquiv (Fin 2) (Fin r) C K).trans
        ((Matrix.reindexAlgEquiv K C (Equiv.prodComm _ _)).trans
          (Matrix.compAlgEquiv (Fin r) (Fin 2) C K).symm)
      let eq := e.mapMatrix (m := Fin r) |>.trans ((g'.symm.trans (g.mapMatrix (m := Fin 2))).trans
        ((Matrix.compAlgEquiv (Fin 2) (Fin s) D K).trans
          (Matrix.reindexAlgEquiv K D finProdFinEquiv)))
      exact ⟨r, 2 * s, hr, Nat.mul_pos (by decide) hs, ⟨eq⟩⟩
    exact ⟨A', B', ⟨(evenIsometryEquiv (hyperbolicProductStep q m)).trans f'⟩,
      step A A' a' ha, step B B' b' hb⟩

private noncomputable def scalarCenterEquiv (A : Type u) [Ring A] [Nontrivial A]
    [Algebra K A] [Algebra.IsCentral K A] : K ≃ₐ[K] Subalgebra.center K A :=
  AlgEquiv.ofBijective (Algebra.ofId K _) ⟨(algebraMap K _).injective, fun x => by
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out x.property)
    exact ⟨a, Subtype.ext ha⟩⟩

private noncomputable def centerProduct (A B : Type u) [Ring A] [Ring B]
    [Nontrivial A] [Nontrivial B] [Algebra K A] [Algebra K B]
    [Algebra.IsCentral K A] [Algebra.IsCentral K B] :
    Subalgebra.center K (A × B) ≃ₐ[K] K × K := by
  let S := Subalgebra.center K A
  let T := Subalgebra.center K B
  let f : S × T →ₐ[K] S.prod T :=
    ((S.val.prodMap T.val).codRestrict (S.prod T) fun x => ⟨x.1.property, x.2.property⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact Prod.ext (Subtype.ext (congrArg (fun z : S.prod T => z.val.1) h))
        (Subtype.ext (congrArg (fun z : S.prod T => z.val.2) h))
    · intro x
      exact ⟨(⟨x.val.1, x.property.1⟩, ⟨x.val.2, x.property.2⟩), Subtype.ext rfl⟩
  exact ((Subalgebra.center K (A × B)).equivOfEq (S.prod T) Subalgebra.center_prod).trans
    ((AlgEquiv.ofBijective f hf).symm.trans (AlgEquiv.prodCongr
      (scalarCenterEquiv A).symm (scalarCenterEquiv B).symm))

private theorem evenDivisionClass_splitCenter {V : Type u} [AddCommGroup V] [Module K V]
    {D : Type u} [Ring D] [Algebra K D] (q : QuadraticForm K V) (h : HasEvenDivisionClass (D := D) q) :
    Nonempty (Subalgebra.center K (even q) ≃ₐ[K] K × K) := by
  obtain ⟨A, B, ⟨f⟩, _, _⟩ := h
  exact ⟨(centerEquiv f).trans (centerProduct A B)⟩

private noncomputable def splitQuadraticAlgebra : QuadraticAlgebra K 0 1 ≃ₐ[K] K × K := by
  let z : K × K := (0, 1)
  let f : QuadraticAlgebra K 0 1 →ₐ[K] K × K := QuadraticAlgebra.lift ⟨z, by simp [z]⟩
  have hf (x : QuadraticAlgebra K 0 1) : f x = (x.re, x.re + x.im) := by
    change x.re • (1 : K × K) + x.im • z = _
    ext <;> simp [z, smul_eq_mul]
  exact AlgEquiv.ofBijective f ⟨fun x y h => QuadraticAlgebra.ext
    (congrArg Prod.fst ((hf x).symm.trans (h.trans (hf y)))) (by
      have h₁ := congrArg Prod.fst ((hf x).symm.trans (h.trans (hf y)))
      have h₂ := congrArg Prod.snd ((hf x).symm.trans (h.trans (hf y)))
      change x.re = y.re at h₁
      change x.re + x.im = y.re + y.im at h₂
      rw [h₁] at h₂
      exact add_left_cancel h₂),
    fun x => ⟨⟨x.1, x.2 - x.1⟩, by simp [hf]⟩⟩

set_option maxHeartbeats 900000 in
private theorem plane_splitCenter : Nonempty (Subalgebra.center K (even (plane (K := K))) ≃ₐ[K]
    K × K) := by
  classical
  let q := plane (K := K)
  let a : K × K := (1, 0)
  let b : K × K := (0, 1)
  have hq (x : K × K) : q x = x.1 * x.2 := plane_apply x
  have hB (x y : K × K) : q.polarBilin x y = x.1 * y.2 + y.1 * x.2 := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hq, Prod.fst_add, Prod.snd_add]
    ring
  have hreg : IsRegular q := by
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    exact Prod.ext (by simpa [hB, b] using LinearMap.congr_fun hx b)
      (by simpa [hB, a] using LinearMap.congr_fun hx a)
  let A := ι q a
  let B := ι q b
  have hA : A * A = 0 := by rw [ι_sq_scalar, hq]; simp [a]
  have h₂ : B * B = 0 := by rw [ι_sq_scalar, hq]; simp [b]
  have hAB : A * B + B * A = 1 := by
    have h := ι_mul_ι_add_swap (Q := q) a b
    rw [← QuadraticMap.polarBilin_apply_apply, hB] at h
    simpa [a, b] using h
  let z := A * B
  have hBA : B * A = 1 - z := by rw [eq_sub_iff_add_eq, add_comm]; exact hAB
  have hzA : z * A = A := by
    change A * B * A = A
    rw [mul_assoc, hBA, mul_sub, mul_one, show A * z = A * A * B from (mul_assoc _ _ _).symm,
      hA, zero_mul, sub_zero]
  have hzB : z * B = 0 := by change A * B * B = 0; rw [mul_assoc, h₂, mul_zero]
  have hAz : A * z = 0 := by change A * (A * B) = 0; rw [← mul_assoc, hA, zero_mul]
  have hBz : B * z = B := by
    change B * (A * B) = B
    rw [← mul_assoc, hBA, sub_mul, one_mul, hzB, sub_zero]
  have hsq : z * z = (0 : K) • 1 + (1 : K) • z := by
    change z * (A * B) = _
    rw [← mul_assoc, hzA, zero_smul, one_smul, zero_add]
  have hmove (y : K × K) : z * ι q y = ι q y * ((1 : K) • 1 - z) := by
    have hy : y = y.1 • a + y.2 • b := by ext <;> simp [a, b]
    nth_rw 1 2 [hy]
    rw [map_add, map_smul, map_smul, mul_add, mul_smul_comm, mul_smul_comm,
      hzA, hzB, one_smul, add_mul, smul_mul_assoc, smul_mul_assoc, mul_sub, mul_one,
      hAz, sub_zero, mul_sub, mul_one, hBz, sub_self]
  let d := (Basis.singleton Unit K).prod (Basis.singleton Unit K)
  let : LinearOrder (Unit ⊕ Unit) := IsWellOrder.linearOrder WellOrderingRel
  obtain ⟨e, _⟩ := even_center_of_root q d
    hreg (x := (1, 1)) (by simp [hq]) (ι_mul_ι_mem_evenOdd_zero q a b)
    0 1 (by simp) hsq hmove
  exact ⟨e.symm.trans splitQuadraticAlgebra⟩

private theorem hyperbolic_splitCenter (m : ℕ) :
    Nonempty (Subalgebra.center K (even (hyperbolic K (m + 1))) ≃ₐ[K] K × K) := by
  let p := plane (K := K)
  let e := onePlaneIso (K := K)
  -- Split off all but one plane on the left.
  have h (n : ℕ) : (hyperbolic K (n + 1)).Equivalent ((hyperbolic K n).prod p) := by
    induction n with
    | zero => exact ⟨e.trans (hyperbolicLeftZero p).symm⟩
    | succ n ih =>
      obtain ⟨d⟩ := ih
      let reassoc : (p.prod ((hyperbolic K n).prod p)).IsometryEquiv
          ((p.prod (hyperbolic K n)).prod p) :=
        ⟨(LinearEquiv.prodAssoc K _ _ _).symm, fun x => add_assoc _ _ _⟩
      exact ⟨(hyperbolicSucc (K := K) (n + 1)).symm.trans
        (((QuadraticMap.IsometryEquiv.refl p).prod d).trans
          (reassoc.trans ((hyperbolicSucc (K := K) n).prod (QuadraticMap.IsometryEquiv.refl p))))⟩
  obtain ⟨d⟩ := h m
  obtain ⟨d'⟩ := center_hyperbolicProduct p ⟨(1, 1), by simp [p, plane_apply]⟩ m
  obtain ⟨d''⟩ := plane_splitCenter (K := K)
  exact ⟨(centerEquiv (evenIsometryEquiv d)).trans (d'.trans d'')⟩

private theorem prodAlgHom_zero_right {A B C : Type u} [Ring A] [Ring B] [Ring C]
    [Algebra K A] [Algebra K B] [Algebra K C] [IsSimpleRing A] [Nontrivial C]
    (f : A × B →ₐ[K] C) (hs : Function.Surjective f) (h : f (0, 1) = 0) :
    Nonempty (A ≃ₐ[K] C) := by
  have hz (b : B) : f (0, b) = 0 := by
    calc
      f (0, b) = f ((0, 1) * (0, b)) := by simp
      _ = 0 := by rw [map_mul, h, zero_mul]
  have hf (a : A) (b : B) : f (a, b) = f (a, 0) := by
    rw [show (a, b) = (a, 0) + (0, b) by simp, map_add, hz, add_zero]
  let g : A →ₐ[K] C :=
    { toFun := fun a => f (a, 0)
      map_one' := (hf 1 1).symm.trans (map_one f)
      map_zero' := map_zero f
      map_mul' := fun x y => by
        rw [← map_mul]
        exact congrArg f (Prod.ext rfl (zero_mul 0).symm)
      map_add' := fun x y => by
        rw [← map_add]
        exact congrArg f (Prod.ext rfl (zero_add 0).symm)
      commutes' := fun a =>
        (hf (algebraMap K A a) (algebraMap K B a)).symm.trans (f.commutes a) }
  exact ⟨AlgEquiv.ofBijective g ⟨g.toRingHom.injective, fun c => by
    obtain ⟨⟨a, b⟩, hab⟩ := hs c
    exact ⟨a, (hf a b).symm.trans hab⟩⟩⟩

private theorem factor_of_prod_surjection {A B C : Type u} [Ring A] [Ring B] [Ring C]
    [Algebra K A] [Algebra K B] [Algebra K C] [IsSimpleRing A] [IsSimpleRing B]
    [Nontrivial C] [Algebra.IsCentral K C] (f : A × B →ₐ[K] C) (hs : Function.Surjective f) :
    Nonempty (A ≃ₐ[K] C) ∨ Nonempty (B ≃ₐ[K] C) := by
  have h (a : C) : a * f (0, 1) = f (0, 1) * a := by
    obtain ⟨⟨x, y⟩, rfl⟩ := hs a
    rw [← map_mul, ← map_mul]
    simp
  obtain ⟨k, hk⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out (Subalgebra.mem_center_iff (R := K).mpr h))
  have hi : IsIdempotentElem k := by
    apply (algebraMap K C).injective
    change algebraMap K C (k * k) = algebraMap K C k
    rw [map_mul, hk, ← map_mul]
    congr 1
    simp
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hi with rfl | rfl
  · exact Or.inl (prodAlgHom_zero_right f hs (by simpa using hk.symm))
  · let e : (B × A) ≃ₐ[K] (A × B) :=
      { (RingEquiv.prodComm : (B × A) ≃+* (A × B)) with commutes' := fun _ => rfl }
    have h01 : f (0, 1) = 1 := by simpa using hk.symm
    have h10 : (f.comp e.toAlgHom) (0, 1) = 0 := by
      change f (1, 0) = 0
      have hh := map_add f ((1 : A), (0 : B)) (0, 1)
      rw [show ((1 : A), (0 : B)) + (0, 1) = 1 by simp, map_one, h01] at hh
      exact add_right_cancel (hh.symm.trans (zero_add 1).symm)
    exact Or.inr (prodAlgHom_zero_right _ (hs.comp e.surjective) h10)

private theorem quaternionClass_ne_split {a b c : K} {A : _root_.CSA.{u,u} K}
    (hD : _root_.Specs.RM03.CSA.isCentralSimple K (QuaternionAlgebra K a b c))
    (hu : ∀ x : QuaternionAlgebra K a b c, x ≠ 0 → IsUnit x)
    (h : _root_.Specs.RM03.Brauer.equivalent K A (QuaternionAlgebra K a b c))
    (n : ℕ) (hn : 0 < n) (e : A ≃ₐ[K] Matrix (Fin n) (Fin n) K) : False := by
  let D := QuaternionAlgebra K a b c
  let : DivisionRing D := DivisionRing.ofIsUnitOrEqZero fun x => by
    by_cases hx : x = 0
    · exact Or.inr hx
    · exact Or.inl (hu x hx)
  have hhA : _root_.Specs.RM03.CSA.isCentralSimple K A := ⟨inferInstance, inferInstance, inferInstance⟩
  have hhK : _root_.Specs.RM03.CSA.isCentralDivision K K := ⟨inferInstance, inferInstance⟩
  have hhD : _root_.Specs.RM03.CSA.isCentralDivision K D := ⟨hD.2.1, hD.2.2⟩
  obtain ⟨f⟩ := (RM03.Brauer.equivalent_iff_division_factors K A D hhA hD K D hhK hhD
    n 1 hn Nat.one_pos e (oneMatrixEquiv K D).symm).mp h
  have hf := f.toLinearEquiv.finrank_eq
  rw [Module.finrank_self, QuaternionAlgebra.finrank_eq_four] at hf
  omega

private theorem algHom_prod_fixed {S : Type u} [Field S] [Algebra K S]
    (τ : Gal(S/K)) (f : K × K →ₐ[K] S) : τ.toAlgHom.comp f = f := by
  have hE := IsIdempotentElem.iff_eq_zero_or_one.mp (show IsIdempotentElem (f (1, 0)) from by
    rw [IsIdempotentElem, ← map_mul]
    congr 1
    simp)
  have hE' : τ (f (1, 0)) = f (1, 0) := by
    rcases hE with h | h <;> simp [h]
  have hsum : f (1, 0) + f (0, 1) = 1 := by
    rw [← map_add, show ((1 : K), (0 : K)) + (0, 1) = 1 by simp, map_one]
  have hF' : τ (f (0, 1)) = f (0, 1) := by
    rw [show f (0, 1) = 1 - f (1, 0) by
      rw [eq_sub_iff_add_eq, add_comm]; exact hsum, map_sub, map_one, hE']
  ext x
  change τ (f x) = f x
  rw [show x = x.1 • ((1 : K), (0 : K)) + x.2 • (0, 1) by simp,
    map_add, map_smul, map_smul, map_add, map_smul, map_smul, hE', hF']

end WittAssembly

section CubicWittAssembly

variable {F E S : Type u} [Field F] [Field E] [Field S]
  [Algebra F E] [Algebra F S] [Algebra E S] [IsScalarTower F E S]
  {G : AffineAlgebraicGroup F} {D : DiagramPresentation G E S}

private theorem residualAction_of_splitCenter (M : CubicPeirceModel G D)
    (labels : (Subalgebra.center E (even M.q) →ₐ[E] S) ≃ HalfSpinVertices F E S)
    (hL : LabelsAgree M labels)
    (e : Subalgebra.center E (even M.q) ≃ₐ[E] E × E) : ResidualActionTrivial F E S := by
  intro τ s
  by_cases hs : s = vectorEmbedding
  · subst s
    ext x
    exact AlgEquiv.commutes τ x
  · let f := labels.symm ⟨s, hs⟩
    have hfix : τ.toAlgHom.comp f = f := by
      apply AlgHom.ext
      intro x
      have h := DFunLike.congr_fun (algHom_prod_fixed τ (f.comp e.symm.toAlgHom)) (e x)
      simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, e.symm_apply_apply] using h
    have h := hL τ f
    rw [hfix] at h
    rw [show labels f = ⟨s, hs⟩ from labels.apply_symm_apply _] at h
    exact h.symm

private theorem evenDivisionClass_excludes_cyclic (M : CubicPeirceModel G D)
    (labels : (Subalgebra.center E (even M.q) →ₐ[E] S) ≃ HalfSpinVertices F E S)
    (hc : CyclicCliffordComparison M labels)
    {a b c : E} (hD : _root_.Specs.RM03.CSA.isCentralSimple E (QuaternionAlgebra E a b c))
    (hu : ∀ x : QuaternionAlgebra E a b c, x ≠ 0 → IsUnit x)
    (h : HasEvenDivisionClass (D := QuaternionAlgebra E a b c) M.q) : False := by
  classical
  obtain ⟨A, B, ⟨f⟩, hA, hB⟩ := h
  obtain ⟨_, hsplit, _, _, _, g, _, _⟩ := hc
  let i := D.numbering (vectorEmbedding (F := F) (E := E) (S := S))
  let j : HalfSpinVertices F E S := ⟨D.numbering.symm (cyclicNext i), fun hj =>
    next_ne_self i (by simpa only [Equiv.apply_symm_apply] using congrArg D.numbering hj)⟩
  let W (j : HalfSpinVertices F E S) := peirceSpace (E := E) M.coordinates (D.numbering j.val)
  let C (j : HalfSpinVertices F E S) := Module.End E (W j)
  obtain ⟨e⟩ := (hsplit j.val).2
  let u : (A × B) →ₐ[E] Matrix (Fin 8) (Fin 8) E :=
    e.toAlgHom.comp ((Pi.evalAlgHom E C j).comp (g.toAlgHom.comp f.symm.toAlgHom))
  have heval : Function.Surjective (Pi.evalAlgHom E C j) :=
    fun c => ⟨Pi.single j c, Pi.single_eq_same j c⟩
  have hs : Function.Surjective u := e.surjective.comp (heval.comp (g.surjective.comp f.symm.surjective))
  rcases factor_of_prod_surjection u hs with h | h
  · obtain ⟨d⟩ := h
    exact quaternionClass_ne_split hD hu hA 8 (by decide) d
  · obtain ⟨d⟩ := h
    exact quaternionClass_ne_split hD hu hB 8 (by decide) d

private theorem cubicWittIndices [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (M : CubicPeirceModel G D)
    (labels : (Subalgebra.center E (even M.q) →ₐ[E] S) ≃ HalfSpinVertices F E S)
    (hL : LabelsAgree M labels)
    (hc : ResidualActionTrivial F E S → CyclicCliffordComparison M labels) :
    (ResidualActionTrivial F E S → M.q.Equivalent (hyperbolic E 4)) ∧
    (¬ ResidualActionTrivial F E S →
      ∃ q₀ : QuadraticForm E (Fin 2 → E), IsRegular q₀ ∧ ¬ IsIsotropic q₀ ∧
        M.q.Equivalent ((hyperbolic E 3).prod q₀)) := by
  classical
  obtain ⟨m, r, q, hmr, hr, hq, ha, ⟨p⟩⟩ := localWitt M.q 4 M.regular (by simp)
  have hr' : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hr' with rfl | rfl | rfl
  · have hm : m = 4 := by omega
    subst m
    let e := p.trans (hyperbolicZeroKernel q 4)
    obtain ⟨z⟩ := hyperbolic_splitCenter (K := E) 3
    have h := residualAction_of_splitCenter M labels hL ((centerEquiv (evenIsometryEquiv e)).trans z)
    exact ⟨fun _ => ⟨e⟩, fun hn => (hn h).elim⟩
  · have hm : m = 3 := by omega
    subst m
    exact ⟨fun h => (no_binary_kernel_of_cyclicComparison M labels (hc h) q hq ha 3 ⟨p⟩).elim,
      fun _ => ⟨q, hq, ha, ⟨p⟩⟩⟩
  · obtain ⟨a, b, c, hD, hu, hQ⟩ := fourSpaceDivisionFactors q hq ha
    have hx : ∃ x, q x ≠ 0 := ⟨1, fun h => ha ⟨1, fun h' => one_ne_zero (congrFun h' 0), h⟩⟩
    obtain ⟨A, B, ⟨f⟩, hA, hB⟩ := hyperbolicProductDivisionClass q hx m hQ
    have h : HasEvenDivisionClass (D := QuaternionAlgebra E a b c) M.q :=
      ⟨A, B, ⟨(evenIsometryEquiv p).trans f⟩, hA, hB⟩
    obtain ⟨z⟩ := evenDivisionClass_splitCenter M.q h
    have ht := residualAction_of_splitCenter M labels hL z
    exact (evenDivisionClass_excludes_cyclic M labels (hc ht) hD hu h).elim

end CubicWittAssembly


set_option maxHeartbeats 900000 in
private theorem wittIndex_of_anisotropic_decomposition {K A : Type u} [Field K] [AddCommGroup A]
    [Module K A] [FiniteDimensional K A] (q : QuadraticForm K A) (ha : ¬ IsIsotropic q) (m : ℕ) :
    let V := (Indices (ULift.{u} (Fin m)) → K) × A
    let Q := (hyperbolic K m).prod q
    (∃ U : Submodule K V, finrank K U = m ∧ ∀ z : U, Q z.val = 0) ∧
      ∀ U : Submodule K V, (∀ z : U, Q z.val = 0) → finrank K U ≤ m := by
  classical
  let I := ULift.{u} (Fin m)
  let L := I → K
  let V := (Indices I → K) × A
  let Q := (hyperbolic K m).prod q
  have Qformula (z : V) : Q z = (∑ i : I, z.1 (.inl i) * z.1 (.inr i)) + q z.2 := by
    rw [QuadraticMap.prod_apply, OddSpinModels.hyperbolicForm_apply]
  have hL : finrank K L = m := by simp [L, I]
  let inl : L →ₗ[K] V :=
    (LinearMap.pi (Sum.elim (LinearMap.proj (R := K)) (fun _ : I => 0))).prod 0
  have hinl (x : L) (i : I) : (inl x).1 (.inl i) = x i := rfl
  have hinr (x : L) (i : I) : (inl x).1 (.inr i) = 0 := rfl
  refine ⟨⟨inl.range, ?_, ?_⟩, ?_⟩
  · rw [(LinearEquiv.ofInjective inl (fun x y h => funext fun i =>
      (hinl x i).symm.trans ((congrArg (fun z : V => z.1 (.inl i)) h).trans (hinl y i)))).finrank_eq.symm, hL]
  · rintro ⟨_, ⟨z, rfl⟩⟩
    rw [Qformula]
    simp only [hinr, mul_zero, Finset.sum_const_zero, zero_add]
    exact q.map_zero
  · intro U hU
    let l : V →ₗ[K] L := (LinearMap.pi fun i : I => LinearMap.proj (.inl i : Indices I)).comp
      (LinearMap.fst K (Indices I → K) A)
    let r : V →ₗ[K] L := (LinearMap.pi fun i : I => LinearMap.proj (.inr i : Indices I)).comp
      (LinearMap.fst K (Indices I → K) A)
    let f := r.comp U.subtype
    let j := U.subtype.comp f.ker.subtype
    have hj (x : f.ker) (i : I) : (j x).1 (.inr i) = 0 := by
      exact congrFun (LinearMap.mem_ker.mp x.property) i
    have hj' (x : f.ker) : (j x).2 = 0 := by
      by_contra hz
      apply ha
      use (j x).2, hz
      have h := hU x.val
      change Q (j x) = 0 at h
      rw [Qformula] at h
      simpa only [hj, mul_zero, Finset.sum_const_zero, zero_add] using h
    let B : L →ₗ[K] Module.Dual K L := dotProductBilin K K
    have hB (x y : L) : B x y = ∑ i : I, x i * y i := rfl
    have hBi : Function.Injective B := by
      intro x y hxy
      funext i
      have h := LinearMap.congr_fun hxy (Pi.single i 1)
      change dotProduct x (Pi.single i 1) = dotProduct y (Pi.single i 1) at h
      simpa only [dotProduct_single_one] using h
    have hmem (x : f.ker) : B (l (j x)) ∈ f.range.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      rintro _ ⟨y, rfl⟩
      have h := hU (x.val + y)
      have hy := hU y
      change Q (j x + y.val) = 0 at h
      rw [Qformula] at h hy
      rw [hB]
      change (∑ i : I, (j x).1 (.inl i) * y.val.1 (.inr i)) = 0
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, hj, hj', zero_add, add_mul,
        Finset.sum_add_distrib] at h
      rw [add_assoc, hy, add_zero] at h
      exact h
    let a := (B.comp (l.comp j)).codRestrict f.range.dualAnnihilator hmem
    have hAi : Function.Injective a := by
      intro x y hxy
      have h := congrArg Subtype.val hxy
      change B (l (j x)) = B (l (j y)) at h
      have h₀ := hBi h
      have hx₀ : j x = j y := by
        apply Prod.ext
        · funext i
          cases i with
          | inl i => exact congrFun h₀ i
          | inr i => exact (hj x i).trans (hj y i).symm
        · exact (hj' x).trans (hj' y).symm
      exact Subtype.ext (Subtype.ext hx₀)
    have hlo := LinearMap.finrank_le_finrank_of_injective hAi
    have hdim := Subspace.finrank_add_finrank_dualAnnihilator_eq f.range
    have hsum := f.finrank_range_add_finrank_ker
    omega

set_option maxHeartbeats 850000 in
private theorem wittIndex_of_isometry {K V W : Type u} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {q : QuadraticForm K V} {p : QuadraticForm K W}
    (e : q.IsometryEquiv p) {m : ℕ} (h : HasWittIndex p m) : HasWittIndex q m := by
  have mapZero {X Y : Type u} [AddCommGroup X] [AddCommGroup Y] [Module K X] [Module K Y]
      {a : QuadraticForm K X} {b : QuadraticForm K Y} (d : a.IsometryEquiv b)
      (U : Submodule K X) (hU : ∀ z : U, a z.val = 0) :
      (finrank K (U.map d.toLinearEquiv.toLinearMap) = finrank K U) ∧
        ∀ z : U.map d.toLinearEquiv.toLinearMap, b z.val = 0 := by
    refine ⟨(Submodule.equivMapOfInjective d.toLinearEquiv.toLinearMap d.toLinearEquiv.injective U).finrank_eq.symm, ?_⟩
    rintro ⟨_, ⟨z, hz, rfl⟩⟩
    exact (d.map_app z).trans (hU ⟨z, hz⟩)
  obtain ⟨⟨U, hd, hu⟩, hmax⟩ := h
  have hl := mapZero e.symm U hu
  refine ⟨⟨_, hl.1.trans hd, hl.2⟩, fun A hA => ?_⟩
  obtain ⟨da, za⟩ := mapZero e A hA
  exact da ▸ hmax _ za

private theorem wittIndex_of_hyperbolic_anisotropic_sum {K V A : Type u} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup A] [Module K A] [FiniteDimensional K A]
    {p : QuadraticForm K V} (q : QuadraticForm K A) (ha : ¬ IsIsotropic q) (m : ℕ)
    (h : p.Equivalent ((hyperbolic K m).prod q)) : HasWittIndex p m := by
  obtain ⟨e⟩ := h
  exact wittIndex_of_isometry e (wittIndex_of_anisotropic_decomposition q ha m)

private theorem wittIndex_of_hyperbolic {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    {q : QuadraticForm K V} (m : ℕ) (h : q.Equivalent (hyperbolic K m)) : HasWittIndex q m := by
  let A := Fin 0 → K
  let p : QuadraticForm K A := 0
  have ha : ¬ IsIsotropic p := fun ⟨v, hv, _⟩ => hv (Subsingleton.elim _ _)
  obtain ⟨e⟩ := h
  exact wittIndex_of_hyperbolic_anisotropic_sum p ha m ⟨e.trans (hyperbolicZeroKernel p m).symm⟩

private theorem cubicPeirceSplitting
    (F E S : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field E] [Field S] [Algebra F E] [Algebra F S]
    [Algebra E S] [IsScalarTower F E S] [Module.Finite F E] [Algebra.IsSeparable F E]
    [IsSepClosure F S] (degree : Module.finrank F E = 3)
    (G : AffineAlgebraicGroup F) (D : DiagramPresentation G E S) :
    ∃ (M : CubicPeirceModel G D)
      (labels : (Subalgebra.center E (even M.q) →ₐ[E] S) ≃ HalfSpinVertices F E S),
      LabelsAgree M labels ∧ GeometricCliffordComparison M labels ∧
      (ResidualActionTrivial F E S →
        IsGalois F E ∧ CyclicCliffordComparison M labels ∧ M.q.Equivalent (hyperbolic E 4) ∧
          HasWittIndex M.q 4) ∧
      (¬ ResidualActionTrivial F E S →
        ∃ q₀ : QuadraticForm E (Fin 2 → E), IsRegular q₀ ∧ ¬ IsIsotropic q₀ ∧
          M.q.Equivalent ((hyperbolic E 3).prod q₀) ∧ HasWittIndex M.q 3) := by
  obtain ⟨M⟩ := actualMarkedVectorForm F E S degree G D
  obtain ⟨labels, hL, hgeom, hcyc⟩ := cubicCliffordComparisons M degree
  obtain ⟨r, T, _, hlocal, _, _, _⟩ := finiteExtension_localField (K := F) (L := E)
  let : ValuativeRel E := r
  let : TopologicalSpace E := T
  let : IsNonarchimedeanLocalField E := hlocal
  obtain ⟨hsplit, hbinary⟩ := cubicWittIndices M labels hL (fun h => (hcyc h).2)
  refine ⟨M, labels, hL, hgeom,
    fun h => ⟨(hcyc h).1, (hcyc h).2, hsplit h, wittIndex_of_hyperbolic 4 (hsplit h)⟩, ?_⟩
  intro h
  obtain ⟨q, hr, ha, hq⟩ := hbinary h
  exact ⟨q, hr, ha, hq, wittIndex_of_hyperbolic_anisotropic_sum q ha 3 hq⟩

end

section CubicSplitting

open LinearAlgebraicGroups.Albert
open LinearAlgebraicGroups.Specs.Unipotent (baseChangedAlgebraicGroup)

/-- The actual cubic scalar extension is quasi-split, and it is split when the
residual diagram action is trivial. -/
theorem trialitarianCubicSplitting : TrialitarianCubicSplitting.{u} := by
  intro F E S _ _ _ _ _ _ _ _ _ _ _ _ _ degree G D
  obtain ⟨M, labels, hlabels, hgeom, hcyclic, hbinary⟩ :=
    cubicPeirceSplitting F E S degree G D
  let : IsSepClosure E S :=
    ⟨IsSepClosure.sep_closed F, Algebra.isSeparable_tower_top_of_isSeparable F E S⟩
  let : FiniteDimensional F M.albert.V :=
    (SplitSpecification.freudenthal_finite_projective M.albert.law M.albert.albert.1).1
  obtain ⟨d, hd⟩ := markedFormIsometry M
  let j₀ := (peirceSpace (E := E) M.coordinates (D.numbering vectorEmbedding)).subtype ∘ₗ
    M.vector.toLinearMap
  have hj₀ : Function.Injective j₀ := Subtype.val_injective.comp M.vector.injective
  obtain ⟨p, hp, hpv⟩ := TrialitarianMarkedSpin.markedSpinComparison F E S degree G D
    M.albert M.cubic M.realization M.coordinates M.unit M.law M.diagonal M.q M.regular j₀ hj₀ d hd
  let N : CubicVectorModel G D := {
    toCubicPeirceModel := M
    spinPoints := p
    spin := hp
    spinVector := hpv }
  let H := baseChangedAlgebraicGroup E G
  have hsplit (h : ResidualActionTrivial F E S) :=
    RankEightSpinStructure.hyperbolicSpinStructure M.q H p M.regular hp (hcyclic h).2.2.1
  refine ⟨N, labels, hlabels, ?_, ?_, hbinary, hgeom⟩
  · by_cases h : ResidualActionTrivial F E S
    · exact (hsplit h).2
    · obtain ⟨q₀, hregular, haniso, hisom, _⟩ := hbinary h
      exact RankEightSpinStructure.binaryKernelSpinStructure M.q H p M.regular hp
        q₀ hregular haniso hisom
  · intro h
    obtain ⟨hgalois, hcomparison, hisom, hindex⟩ := hcyclic h
    exact ⟨hgalois, hcomparison, hisom, hindex, (hsplit h).1⟩

end CubicSplitting

end LinearAlgebraicGroups.Arithmetic.TrialitarianCliffordInvariants
